#ifndef BTOR2_ENCODER_H
#define BTOR2_ENCODER_H

extern "C" {
#include "btor2parser/btor2parser.h"
}

#include <stdio.h>
#include <iostream>
#include <map>
#include <string>
#include <unordered_map>
#include "assert.h"

#include "exceptions.h"
#include "rts.h"
#include "smt-switch/smt.h"

namespace cosa {
class BTOR2Encoder
{
 public:
  BTOR2Encoder(std::string filename, RelationalTransitionSystem & rts)
      : rts_(rts), solver_(rts.solver())
  {
    parse(filename);
  };

  const smt::TermVec & badvec() const { return badvec_; };
  const smt::TermVec & justicevec() const { return justicevec_; };
  const smt::TermVec & fairvec() const { return fairvec_; };
  const smt::TermVec & inputsvec() const { return inputsvec_; }
  const smt::TermVec & statesvec() const { return statesvec_; }
  const std::map<uint64_t, smt::Term> & no_next_states() const
  {
    return no_next_states_;
  }

 protected:
  // converts booleans to bitvector of size one
  smt::Term bool_to_bv(const smt::Term & t) const;
  // converts bitvector of size one to boolean
  smt::Term bv_to_bool(const smt::Term & t) const;
  // lazy conversion
  // takes a list of booleans / bitvectors of size one
  // and lazily converts them to the majority
  smt::TermVec lazy_convert(const smt::TermVec &) const;

  // parse a btor2 file
  void parse(const std::string filename);

  // Important members
  smt::SmtSolver & solver_;
  cosa::RelationalTransitionSystem & rts_;

  // vectors of inputs and states
  // maintains the order from the btor file
  smt::TermVec inputsvec_;
  smt::TermVec statesvec_;
  std::map<uint64_t, smt::Term> no_next_states_;

  // Useful variables
  smt::Sort linesort_;
  smt::TermVec termargs_;
  std::unordered_map<int, smt::Sort> sorts_;
  std::unordered_map<int, smt::Term> terms_;
  std::string symbol_;

  smt::TermVec badvec_;
  smt::TermVec justicevec_;
  smt::TermVec fairvec_;

  Btor2Parser * reader_;
  Btor2LineIterator it_;
  Btor2Line * l_;
  size_t i_;
  int64_t idx_;
  bool negated_;
};
}  // namespace cosa

#endif
