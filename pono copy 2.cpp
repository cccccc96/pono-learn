/*********************                                                        */
/*! \file
** \verbatim
** Top contributors (to current version):
**   Makai Mann, Ahmed Irfan
** This file is part of the pono project.
** Copyright (c) 2019 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief
**
**
**/

#include <csignal>
#include <iostream>
#include <sstream>

#include "assert.h"

#ifdef WITH_PROFILING
#include <gperftools/profiler.h>
#endif

#include "smt-switch/boolector_factory.h"
#ifdef WITH_MSAT
#include "smt-switch/msat_factory.h"
#endif

#include "core/fts.h"
#include "engines/bmc.h"
#include "engines/ste.h"
#include "frontends/btor2_encoder.h"
#include "frontends/smv_encoder.h"
#include "frontends/vmt_encoder.h"
#include "map"
#include "modifiers/control_signals.h"
#include "modifiers/mod_ts_prop.h"
#include "modifiers/prop_monitor.h"
#include "modifiers/static_coi.h"
#include "options/options.h"
#include "printers/btor2_witness_printer.h"
#include "printers/vcd_witness_printer.h"
#include "smt-switch/logging_solver.h"
#include "smt/available_solvers.h"
// #include "ste/formula_compiler.cpp"
#include "ste/ste_specification_encoder.h"
#include "utils/logger.h"
#include "utils/make_provers.h"
#include "utils/str_util.cpp"
#include "utils/timestamp.h"
#include "utils/ts_analysis.h"
// #include <format>
#include <cstdlib>
// #include "printers/vcd_witness_printer.h"
using namespace pono;
using namespace smt;
using namespace std;

void ste_mult()
{
  logger.set_verbosity(4);
  SmtSolver s = create_solver(smt::BTOR);
  s->set_opt("incremental", "true");
  FunctionalTransitionSystem fts(s);
  string filename = ("/root/SteBmcSmt/pono");
  filename += "/stecase/mult.btor2";
  BTOR2Encoder be(filename, fts);
  Property p(fts.solver(), s->make_term(true));
  Ste ste(p, fts, s);

  // function
  auto AND = [s](Term a, Term b) { return s->make_term(And, a, b); };
  auto ANDV = [s](vector<Term> v) { return s->make_term(And, v); };
  auto OR = [s](Term a, Term b) { return s->make_term(Or, a, b); };
  auto NOT = [s](Term a) { return s->make_term(Not, a); };
  auto IMPLY = [s](Term a, Term b) { return s->make_term(Implies, a, b); };
  auto EQUAL = [s](Term a, Term b) { return s->make_term(Equal, a, b); };
  auto EXTRACT = [s](Term a, int left, int right) {
    return s->make_term(Op(Extract, left, right), a);
  };
  auto ZEROEXTEND = [s](Term a, int left) {
    return s->make_term(Op(smt::Zero_Extend, left), a);
  };
  Term data_rdy = fts.named_terms().at("io_data_rdy");
  Term io_mult1 = fts.named_terms().at("io_mult1");
  Term io_mult2 = fts.named_terms().at("io_mult2");
  Term io_rstn = fts.named_terms().at("io_rstn");
  Term reset = fts.named_terms().at("reset");
  Term a = fts.make_statevar("a", io_mult1->get_sort());
  Term b = fts.make_statevar("b", io_mult2->get_sort());
  a = s->make_term(15, io_mult1->get_sort());
  b = s->make_term(15, io_mult1->get_sort());
  Term io_res = fts.named_terms().at("io_res");
  int n = 10;
  int latency = 4;
  int size = 3;
  for (int i = 0; i < n; i++) {
    Term a1;
    if (i == 0) {
      a1 = EQUAL(io_rstn, s->make_term(false));
    } else {
      a1 = EQUAL(io_rstn, s->make_term(true));
    }
    Term a2 = EQUAL(data_rdy, s->make_term(true));
    Term a3 = EQUAL(io_mult1, a);
    Term a4 = EQUAL(io_mult2, b);
    Term a5 = EQUAL(reset, s->make_term(false));
    ste.antecedent.push_back(ANDV(vector<Term>{ a1, a2, a3, a4, a5 }));
  }
  cout << s->make_term(BVMul, ZEROEXTEND(a, 4), ZEROEXTEND(b, 4))->to_string()
       << endl;
  for (int i = 0; i < n; i++) {
    if (i == 5) {
      ste.consequent.push_back(EQUAL(
          io_res, s->make_term(BVMul, ZEROEXTEND(a, 4), ZEROEXTEND(b, 4))));
    } else {
      ste.consequent.push_back(s->make_term(true));
    }
  }
  ProverResult r = ste.check_until(n - 1);

  logger.log(0, to_string(r));
}

// void parseFormulaTest()
// {
//   logger.set_verbosity(4);
//   SmtSolver s = create_solver(smt::BTOR);
//   s->set_opt("incremental", "true");
//   s->make_symbol("a1", s->make_sort(BV, 4));
//   s->make_symbol("a2", s->make_sort(BV, 4));
//   s->make_symbol("a3", s->make_sort(BV, 4));
//   cout << parseLogicExpression(s, "( (!( a1 = a3 ) )&(!( a2 = a3 ) ) )")
//        << endl;
//   cout << parseLogicExpression(s, "( a1 + a2 ) )") << endl;
// }

void convertVerilog2Btor2(string buildPath, string modName)
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
  std::ofstream outFile(buildPath + "/gen.ys");

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

bool isNumber(const string & str)
{
  for (char const & c : str) {
    if (std::isdigit(c) == 0) return false;
  }
  return true;
}

void parseAssertFile(string assertFilePath,
                     string btor2FilePath,
                     string resultPath,
                     string buildPath,
                     int vervosity = 4)
{
  // Solver/电路 预处理
  logger.set_verbosity(vervosity);
  SmtSolver s = create_solver(smt::BTOR);
  s->set_opt("incremental", "true");
  FunctionalTransitionSystem fts(s);
  BTOR2Encoder be(btor2FilePath, fts);
  Property p(fts.solver(), s->make_term(true));
  Ste ste(p, fts, s);

  auto AND = [s](Term a, Term b) { return s->make_term(And, a, b); };
  auto ANDV = [s](vector<Term> v) { return s->make_term(And, v); };
  auto OR = [s](Term a, Term b) { return s->make_term(Or, a, b); };
  auto NOT = [s](Term a) { return s->make_term(Not, a); };
  auto IMPLY = [s](Term a, Term b) { return s->make_term(Implies, a, b); };
  auto EQUAL = [s](Term a, Term b) { return s->make_term(Equal, a, b); };
  auto EXTRACT = [s](Term a, int left, int right) {
    return s->make_term(Op(Extract, left, right), a);
  };

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
    vector<string> tokens = pono::syntax_analysis::Split(line, ",");
    if (tokens[0] == "VARS" || tokens[0] == "ANT" || tokens[0] == "CONS") {
      flag = tokens[0];
    } else if (flag == "VARS") {  // 创建符号变量
      string name = tokens[0];
      int bv_size = stoi(tokens[1]);
      if (bv_size == 1) {
        s->make_symbol(name, s->make_sort(BOOL));
      } else {
        s->make_symbol(name, s->make_sort(BV, bv_size));
      }
    } else if (flag == "ANT") {
      string guard_str, node_str, value_str;
      int left, right;
      int clock;
      string token0 = tokens[0];
      if (token0 == "Imply") {
        guard_str = tokens[1];
        node_str = tokens[2];
        value_str = tokens[3];
        if (tokens.size() > 5) {
          left = stoi(tokens[4]);
          right = stoi(tokens[5]);
        }
      } else {
        node_str = tokens[0];
        value_str = tokens[1];
        if (tokens.size() > 3) {
          left = stoi(tokens[2]);
          right = stoi(tokens[3]);
        }
      }
      std::replace(node_str.begin(),node_str.end(),'.','_');
      clock = stoi(tokens[tokens.size() - 1]);

      // not guard

      Term node = fts.named_terms().at(node_str);
      if(node->get_sort()->get_width()>1){
        node = EXTRACT(node, left, right);
      }
      Term value;
      
      // boolean/int/formula
      if (value_str == "F") {
        value = s->make_term(false);
      } else if (value_str == "T") {
        value = s->make_term(true);
      } else if (isNumber(value_str)) {
        value = s->make_term(stoi(value_str), node->get_sort());
      } else {
        value = parseLogicExpression(s, value_str);
      }

      Term ant_t;

      if (token0 == "Imply") {
        Term guard = parseLogicExpression(s, guard_str);
        ant_t = IMPLY(guard, EQUAL(node, value));
      } else {
        ant_t = EQUAL(node, value);
      }

      if (ant.find(clock) != ant.end()) {
        ant[clock] = AND(ant[clock], ant_t);
      } else {
        ant[clock] = ant_t;
      }
      max_time = max(max_time, clock);
    } else {
      string guard_str, node_str, value_str;
      int left,right;
      int clock;

      string token0 = tokens[0];
      if (token0 == "Imply") {
        guard_str = tokens[1];
        node_str = tokens[2];
        value_str = tokens[3];
        if (tokens.size() > 5) {
          left = stoi(tokens[4]);
          right = stoi(tokens[5]);
        }
      } else {
        node_str = tokens[0];
        value_str = tokens[1];
        if (tokens.size() > 3) {
          left = stoi(tokens[2]);
          right = stoi(tokens[3]);
        }
      }
      clock = stoi(tokens[tokens.size() - 1]);
      std::replace(node_str.begin(),node_str.end(),'.','_');

      // not guard

      Term node = fts.named_terms().at(node_str);
      if(node->get_sort()->get_width()>1){
        node = EXTRACT(node, left, right);
      }
      Term value;
      // boolean/int/formula
      if (value_str == "F") {
        value = s->make_term(false);
      } else if (value_str == "T") {
        value = s->make_term(true);
      } else if (isNumber(value_str)) {
        value = s->make_term(stoi(value_str), node->get_sort());
      } else {
        value = parseLogicExpression(s, value_str);
      }

      Term cons_t;

      if (token0 == "Imply") {
        Term guard = parseLogicExpression(s, guard_str);
        cons_t = IMPLY(guard, EQUAL(node, value));
      } else {
        cons_t = EQUAL(node, value);
      }

      if (cons.find(clock) != cons.end()) {
        cons[clock] = AND(cons[clock], cons_t);
      } else {
        cons[clock] = cons_t;
      }
      max_time = max(max_time, clock);
    }
  }


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
  ProverResult r = ste.check_until(max_time);
  logger.log(0, "\nSTE RESULT: " + to_string(r));
  
  //将r的结果写入buildPath/result文件
  fstream resultFile(buildPath+"/result", ios::out);
  resultFile << to_string(r);

  inputFile.close();
  return;
}

int main(int argc, char * argv[])
{
  //test
  if (argc == 1) {
    string modName = "Ander";
    string buildPath = "/root/chisel_with_ste/" + modName + "_build";
    
    SteSpecificationEncoder *sse = new SteSpecificationEncoder();
    sse->convertVerilog2Btor2(buildPath, modName);

    // parseFormulaTest();
    // string modName = "Ander";
    // string buildPath = "/root/chisel_with_ste/" + modName + "_build";
    // // convertVerilog2Btor2(buildPath,modName);
    // string resultPath = buildPath + "/VCD-CEX.vcd";
    // // convertVerilog2Btor2(buildPath, modName);
    // string btor2Path = buildPath + "/" + modName + ".btor2";
    // string assertPath = buildPath + "/ste.assert";
    // parseAssertFile(assertPath, btor2Path, resultPath,buildPath,1);
    return 0;
  }
  string buildPath = argv[1];
  string modName = argv[2];
  string resultPath = buildPath + "/VCD-CEX.vcd";
  convertVerilog2Btor2(buildPath, modName);
  string btor2Path = buildPath + "/" + modName + ".btor2";
  string assertPath = buildPath + "/ste.assert";
  parseAssertFile(assertPath, btor2Path, resultPath,buildPath);
  return 0;
}
