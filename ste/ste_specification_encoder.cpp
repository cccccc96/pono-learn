#include "ste_specification_encoder.h"

// #include <format>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <sstream>
#include <stack>
#include <string>
#include <unordered_map>
#include <ctime>
#include <iomanip>

#include "core/fts.h"
#include "core/prop.h"
#include "engines/ste.h"
#include "frontends/btor2_encoder.h"
#include "map"
#include "smt/available_solvers.h"
#include "utils/logger.h"
#include "utils/str_util.h"
// #include "printers/vcd_witness_printer.h"
using namespace smt;
using namespace std;
using namespace pono;

// formula compiler helper

bool isOperator(char c)
{
  return c == '&' || c == '|' || c == '!' || c == '=' || c == '+';
}

int getPriority(char c)
{
  if (c == '!') {
    return 100;
  } else if (c == '&') {
    return 90;
  } else if (c == '|') {
    return 80;
  } else if (c == '+') {
    return 70;
  } else if (c == '=') {
    return 40;
  } else {
    return 0;
  }
}

smt::Term performOperation(smt::SmtSolver solver_,
                           smt::Term operand1,
                           smt::Term operand2,
                           char op)
{
  // cout << operand1->to_string() << op << operand2->to_string() << endl;
  if (op == '&') {
    return solver_->make_term(smt::And, operand1, operand2);
  } else if (op == '|') {
    return solver_->make_term(smt::Or, operand1, operand2);
  } else if (op == '!') {
    return solver_->make_term(smt::Not, operand1);
  } else if (op == '+') {
    return solver_->make_term(smt::BVAdd, operand1, operand2);
  } else if (op == '=') {
    // cout << solver_->make_term(smt::Equal, operand1, operand2)->to_string()<< endl;
    return solver_->make_term(smt::Equal, operand1, operand2);
  } else {
    assert("guard error!");
    return solver_->make_term(false);
  }
}

smt::Term parseLogicExpression(const smt::SmtSolver solver_,
                               const std::string & expression)
{
  // cout<<"start parse"<<endl;
  std::stack<smt::Term> operands;
  std::stack<char> operators;

  for (size_t i = 0; i < expression.length(); ++i) {
    char c = expression[i];

    if (c == ' ') {
      continue;  // 忽略空格
    }

    if (isOperator(c)) {
      // 处理运算符
      while (!operators.empty()
             && getPriority(operators.top()) >= getPriority(c)) {
        char op = operators.top();
        operators.pop();

        if (op == '!') {
          smt::Term operand = operands.top();
          operands.pop();
          operands.push(performOperation(
              solver_, operand, solver_->make_term(false), op));
        } else {
          smt::Term operand2 = operands.top();
          operands.pop();
          smt::Term operand1 = operands.top();
          operands.pop();
          operands.push(performOperation(solver_, operand1, operand2, op));
        }
      }

      operators.push(c);
    } else if (c == '(') {
      // 左括号入栈
      operators.push(c);
    } else if (c == ')') {
      // 处理右括号
      while (!operators.empty() && operators.top() != '(') {
        char op = operators.top();
        operators.pop();

        if (op == '!') {
          smt::Term operand = operands.top();
          operands.pop();
          operands.push(performOperation(
              solver_, operand, solver_->make_term(false), op));
        } else {
          smt::Term operand2 = operands.top();
          operands.pop();
          smt::Term operand1 = operands.top();
          operands.pop();
          operands.push(performOperation(solver_, operand1, operand2, op));
        }
      }

      if (!operators.empty() && operators.top() == '(') {
        operators.pop();  // 弹出左括号
      }
    } else {
      // 处理操作数
      std::string variable;
      while (i < expression.length() && !isOperator(expression[i])
             && expression[i] != ' ') {
        variable += expression[i];
        i++;
      }
      i--;  // 退回一个字符，以便下一轮循环继续处理

      // 压入符号变量:res
      // 处理是否有[left:right]
      // 处理是否为整数
      // cout << variable << endl;
      Term res;
      vector<string> tokens = pono::syntax_analysis::Split(variable, "[");
      if (tokens.size() == 1) {
        vector<string> tokens2 = pono::syntax_analysis::Split(variable, "@");
        if (tokens2.size() == 1) {  // 正常的变量
          res = solver_->get_symbol(variable);
        } else {
          // 整数
          res = solver_->make_term(stoi(tokens2[0]),
                                   solver_->make_sort(BV, stoi(tokens2[1])));
        }

      } else {
        Term node = solver_->get_symbol(tokens[0]);
        vector<string> tokens_ = pono::syntax_analysis::Split(tokens[1], ":");
        int left = stoi(tokens_[0]);
        int right = stoi(tokens_[1].erase(tokens_[1].size() - 1));
        res = solver_->make_term(Op(Extract, left, right), node);
      }
      // cout << res << endl;
      operands.push(res);
    }
  }

  // 处理剩余的运算符
  while (!operators.empty()) {
    char op = operators.top();
    operators.pop();

    if (op == '!') {
      smt::Term operand = operands.top();
      operands.pop();
      operands.push(
          performOperation(solver_, operand, solver_->make_term(false), op));
    } else {
      smt::Term operand2 = operands.top();
      operands.pop();
      smt::Term operand1 = operands.top();
      operands.pop();
      operands.push(performOperation(solver_, operand1, operand2, op));
    }
  }

  return operands.top();
}

bool isNumber(const string & str)
{
  for (char const & c : str) {
    if (std::isdigit(c) == 0) return false;
  }
  return true;
}

// SteSpecificationEncoder

SteSpecificationEncoder::SteSpecificationEncoder()
{
  // Ander/BubbleFifo/RWSmem/Stack
  modName = "Risc";
  buildPath = "/root/chisel_with_ste/" + modName + "_build";
  resultPath = buildPath + "/VCD-CEX.vcd";
  btor2Path = buildPath + "/" + modName + ".btor2";
  assertPath = buildPath + "/ste.assert";

  // this->ste = ste;
  convertVerilog2Btor2(buildPath, modName);
  loadSteSpec(assertPath, btor2Path, resultPath, buildPath);
}

SteSpecificationEncoder::SteSpecificationEncoder(string buildPath,
                                                 string modName)
{
  // Ander/BubbleFifo/RWSmem/Stack
  this->modName = modName;
  string resultPath = buildPath + "/VCD-CEX.vcd";
  string btor2Path = buildPath + "/" + modName + ".btor2";
  string assertPath = buildPath + "/ste.assert";

  // this->ste = ste;
  convertVerilog2Btor2(buildPath, modName);
  loadSteSpec(assertPath, btor2Path, resultPath, buildPath);
}

void SteSpecificationEncoder::test() { cout << this->a << endl; }

void SteSpecificationEncoder::convertVerilog2Btor2(string buildPath,
                                                   string modName)
{
  std::string formattedText = R"(
       read_verilog -formal %s/%s.sv
       prep -top %s
       flatten
       memory -nomap
       hierarchy -check
       setundef -undriven -init -expose
       write_btor %s.btor2
     )";
  string ys = "";
  ys += "read_verilog -formal " + buildPath + "/" + modName + ".sv" + "\n";
  ys += "prep -top " + modName + "\n";
  ys += "flatten\n";
  ys += "memory \n";
  ys += "hierarchy -check\n";
  ys += "setundef -undriven -init -expose\n";
  ys += "write_btor " + buildPath + "/" + modName + ".btor2\n";

  // 打开文件以写入模式
  std::ofstream outFile((buildPath + "/gen.ys"));

  // 检查文件是否成功打开
  if (!outFile) {
    std::cerr << "Error opening the file." << std::endl;
    return;
  }
  // 将地址字符串写入文件
  outFile << ys << std::endl;

  // 关闭文件
  outFile.close();
  string ysFile = buildPath + "/gen.ys";
  string command = "yosys -q " + ysFile;  //
  // 这里的命令是列出当前目录下的文件和文件夹
  //  使用 std::system 函数运行中断命令
  std::system(command.c_str());
}

Term SteSpecificationEncoder::nodeStr2BV(FunctionalTransitionSystem fts,
                                         string node_str)
{
  Term res;
  // 如果没有[left:right]：
  vector<string> tokens = pono::syntax_analysis::Split(node_str, "[");
  if (tokens.size() == 1) {
    res = fts.named_terms().at(node_str);
  } else {
    Term node = fts.named_terms().at(tokens[0]);
    vector<string> tokens_ = pono::syntax_analysis::Split(tokens[1], ":");
    int left = stoi(tokens_[0]);
    int right = stoi(tokens_[1].erase(tokens_[1].size() - 1));
    res = s->make_term(Op(Extract, left, right), node);
  }

  return res;
  // 如果有[left:right]：
}

Term SteSpecificationEncoder::valStr2BV(string value_str, Term node)
{
  Term value;
  // boolean/int/formula
  if (value_str == "F") {
    value = s->make_term(false);
  } else if (value_str == "T") {
    value = s->make_term(true);
  } else if (isNumber(value_str)) {
    value = s->make_term(stoi(value_str), node->get_sort());
  } else {
    // 在parseLogicExpression处理[left:right]
    value = parseLogicExpression(s, value_str);
  }
  return value;
}

void SteSpecificationEncoder::loadSteSpec(string assertFilePath,
                                          string btor2FilePath,
                                          string resultPath,
                                          string buildPath)
{
  logger.set_verbosity(4);
  this->s = create_solver(smt::BTOR);
  FunctionalTransitionSystem fts(this->s);
  BTOR2Encoder be(btor2FilePath, fts);
  Property p(fts.solver(), s->make_term(true));
  Ste ste(p, fts, s);

  // 读取assertFilePath
  map<int, smt::Term> ant;             // ant
  map<int, smt::Term> cons;            // cons
  ifstream inputFile(assertFilePath);  // 假设输入文本保存在input.txt文件中
  if (!inputFile.is_open()) {
    cout << "无法打开输入文件" << endl;
    return;
  }
  string flag;
  string line;
  int max_time = 0;

  while (getline(inputFile, line)) {
    cout << line << endl;
    vector<string> tokens = pono::syntax_analysis::Split(line, ",");
    if (tokens[0] == "VARS" || tokens[0] == "ANT" || tokens[0] == "CONS") {
      flag = tokens[0];
    } else if (flag == "VARS") {
      // 1.创建符号变量
      // 符号名  符号size
      string name = tokens[0];
      int bv_size = stoi(tokens[1]);
      s->make_symbol(name, s->make_sort(BV, bv_size));
    } else if (flag == "ANT" || flag == "CONS") {
      // 2.ANT/CONS
      string guard_str, node_str, value_str;
      int idx = 0;
      int clock = -1;
      string token0 = tokens[idx++];

      if (token0 == "GUARD") {
        // 有GUARD的情况
        guard_str = tokens[idx++];
        node_str = tokens[idx++];
        value_str = tokens[idx++];
      } else {
        // 没有GUARD的情况
        node_str = token0;
        value_str = tokens[idx++];
      }

      // 这一行最终的clock
      clock = stoi(tokens[tokens.size() - 1]);
      // 这一行最终的node
      Term node = nodeStr2BV(fts, node_str);
      // 这一行最终的value
      Term value = valStr2BV(value_str, node);
      // 这一行最终的ant/cons
      Term ant_cons_t;
      if (token0 == "GUARD") {
        Term guard = parseLogicExpression(s, guard_str);
        ant_cons_t = s->make_term(
            PrimOp::Implies, guard, s->make_term(PrimOp::Equal, node, value));
      } else {
        ant_cons_t = s->make_term(PrimOp::Equal, node, value);
      }

      // cout << "ant_cons_t" << ant_cons_t->to_string() << endl;

      // 2.1 ant加入map
      if (flag == "ANT") {
        if (ant.find(clock) != ant.end()) {
          ant[clock] = s->make_term(PrimOp::And, ant[clock], ant_cons_t);
        } else {
          ant[clock] = ant_cons_t;
        }
      }
      // 2.2 cons加入map
      if (flag == "CONS") {
        if (cons.find(clock) != cons.end()) {
          cons[clock] = s->make_term(PrimOp::And, cons[clock], ant_cons_t);
        } else {
          cons[clock] = ant_cons_t;
        }
      }

      // 更新max_time
      max_time = max(max_time, clock);
    }
    cout << "over" << endl;
  }

  // cout << "czc:" << endl;

  for (int i = 0; i <= max_time; i++) {
    if (ant.find(i) != ant.end()) {
      ste.antecedent.push_back(ant[i]);
    } else {
      ste.antecedent.push_back(s->make_term(true));
    }
    if (cons.find(i) != cons.end()) {
      ste.consequent.push_back(cons[i]);
    } else {
      ste.consequent.push_back(s->make_term(true));
    }
  }
  cout << "check begin" << endl;
  clock_t start_time = clock();
  ProverResult r = ste.check_until(max_time);
  clock_t end_time = clock();
  double duration_seconds = static_cast<double>(end_time - start_time) / CLOCKS_PER_SEC;
  std::ofstream outfile(buildPath+"/smt_res.txt");
  if (outfile.is_open()) {
      outfile << "runtime: " << std::fixed << std::setprecision(2) << duration_seconds << " 秒" << std::endl;
      outfile << "res: " << to_string(r) <<std::endl;
      std::cerr << buildPath+"smt_res.txt" << std::endl;
      outfile.close();
  } else {
      std::cerr << "res file open error" << std::endl;
  }
  cout << "check end" << endl;
  logger.log(0, "\nSTE RESULT: " + to_string(r));
}