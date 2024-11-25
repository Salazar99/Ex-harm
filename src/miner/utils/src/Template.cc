#include "Template.hh"
#include "EdgeProposition.hh"
#include "colors.hh"
#include "fort.hpp"
#include "globals.hh"
#include "message.hh"
#include "minerUtils.hh"
#include "misc.hh"

#include <algorithm>
#include <deque>
#include <fstream>
#include <sstream>
#include <string>
#include <thread>
#include <utility>
namespace slam {

Template::Template(slam::Trace *trace, DTLimits limits)
    : _max_length(trace->getLength()), _limits(limits), _trace(trace) {

}


Template::~Template() {

  delete _impl;

}

size_t Template::nPermsGenerated() const {
  return _pg._size.first;
  //return _cProps.size();
}

std::string Template::getAssertion() {
  return "G(" + temp2String(*_impl, 1) + ")";
}
std::string Template::getColoredAssertion() {
  return GLOB("G(") + temp2ColoredString(*_impl, 1) + GLOB(")");
}
std::string Template::getTemplate() {
  std::string ant = "";
  if (_dtOp.second == nullptr) {
    ant = temp2String(*_impl->getItems()[0]);
  } else {
    if (dynamic_cast<DTAndF *>(_dtOp.second) != nullptr) {
      ant = "(..F..)";
    } else {
      messageError("Unknown dt operator");
    }
  }

  return "G(" + ant + " -> " + temp2String(*_impl->getItems()[1], 0) + ")";
}
std::string Template::getColoredTemplate() {
  std::string ant = "";
  if (_dtOp.second == nullptr) {
    ant = temp2String(*_impl->getItems()[0]);
  } else {
    if (dynamic_cast<DTAndF *>(_dtOp.second) != nullptr) {
      ant = TEMP("(..F..)");
    } else {
      messageError("Unknow dt operator");
    }
  }

  return GLOB("G(") + ant + TIMPL(" -> ") +
         temp2ColoredString(*_impl->getItems()[1], 0) + GLOB(")");
}

DTOperator *Template::getDT() { return _dtOp.second; }

std::map<std::string, TemporalExp *> &Template::get_aphToProp() {
  return _aphToProp;
}
std::map<std::string, TemporalExp *> &Template::get_cphToProp() {
  return _cphToProp;
}
std::map<std::string, TemporalExp *> &Template::get_acphToProp() {
  return _acphToProp;
}

bool Template::nextPerm() {

  if (_iToProp.size() ==
      (_tokenToProp.size() - (_dtOp.second == nullptr ? 0 : 1))) {
    return false;
  }
  messageErrorIf(_permIndex < 0, "No permutations available!");
  if ((size_t)_permIndex >= _pg._size.first) {
    _permIndex = 0;
    return false;
  }
  //load the next permutation FIXME:  this could be heavily optimised by loading only the propositions changing from the previous permutation
  _conInCache = false;
  _antInCache = false;
  for (auto &e : _pg._phToIndex) {
    slam::Location where = _pg._phToLoc.at(e.first);
    // e.first is the string representation of a placeholder e.second is the column of the permutation's table _permIndex is the row of the permutation's table

    if (where == slam::Location::Ant) {
      //fill the placeholder with the correct proposition _pg._perms[_permIndex][e.second] contains the index of the proposition to be inserted
      //FIXME Completely broken due to Hstring modification
      //  (*_aphToProp.at(e.first)) = _aProps[_pg._perms[_permIndex][e.second]];
      //} else if (where == slam::Location::Con) {
      //  (*_cphToProp.at(e.first)) = _cProps[_pg._perms[_permIndex][e.second]];
      //} else {
      //  (*_acphToProp.at(e.first)) = _acProps[_pg._perms[_permIndex][e.second]];
    }
  }
  //go to the next permutation
  _permIndex++;
  return true;
}

void Template::loadPerm(size_t n) {
  if (getNumPlaceholders() == 0 && n != 0) {
    messageError("Perm not available!");
  }
  messageErrorIf(_permIndex < 0, "No permutations available!");
  if (n >= _pg._size.first) {
    messageError("Perm not available!");
  }

  // load the next permutation
  _conInCache = false;
  _antInCache = false;
  for (auto &e : _pg._phToIndex) {
    slam::Location where = _pg._phToLoc.at(e.first);
    //e.first is the string representation of a placeholder e.second is the column of the permutation's table _permIndex is the row of the permutation's table

    if (where == slam::Location::Ant) {
      //        messageError("");
      //feel the placeholder with the correct proposition _pg._perms[_permIndex][e.second] contains the index of the proposition to be inserted
      //FIXME Completely broken due to Hstring modification
      dynamic_cast<Placeholder *>(_aphToProp.at(e.first))
          ->setProposition(_aProps[_pg._perms[n][e.second]]);
    } else if (where == slam::Location::Con) {
      dynamic_cast<Placeholder *>(_cphToProp.at(e.first))
          ->setProposition(_cProps[_pg._perms[n][e.second]]);
      //      dynamic_cast<Placeholder *>(*_cphToProp.at(e.first)) ->setProposition(_cProps[n]);
    } else {
      //       messageError("");
      dynamic_cast<Placeholder *>(_acphToProp.at(e.first))
          ->setProposition(_acProps[_pg._perms[n][e.second]]);
    }
  }
  // return to the first permutation if we have reached the end of the
  // available permutations
}

size_t Template::getNumPlaceholders(slam::Location where) {
  if (where == slam::Location::Ant) {
    return _aphToProp.size();
  } else if (where == slam::Location::Con) {
    return _cphToProp.size();
  } else {
    return _acphToProp.size();
  }
}

size_t Template::getNumPlaceholders() {
  return _aphToProp.size() + _cphToProp.size() + _acphToProp.size();
}

void Template::loadPropositions(std::vector<Proposition *> &props,
                                slam::Location where) {

  // Check errors-----------------------------
  if (where == slam::Location::Ant) {
    messageErrorIf(_aphToProp.size() != props.size(),
                   "Expecting " + std::to_string(_aphToProp.size()) +
                       " propositions, " + std::to_string(props.size()) +
                       " given!");
  } else if (where == slam::Location::Con) {
    messageErrorIf(_cphToProp.size() != props.size(),
                   "Expecting " + std::to_string(_cphToProp.size()) +
                       " propositions, " + std::to_string(props.size()) +
                       " given!");
  } else {
    messageErrorIf(_acphToProp.size() != props.size(),
                   "Expecting " + std::to_string(_acphToProp.size()) +
                       " propositions, " + std::to_string(props.size()) +
                       " given!");
  }

  //-----------------------------------------

  // Warning: the given propositions are inserted following the alphabetic order of the placeholders
  size_t i = 0;
  if (where == slam::Location::Ant) {
    // the antecedent is modified: we need to recalculate
    _antInCache = false;
    // put the propositions in the antecedent's placeholders
    for (const auto &ph : _aphToProp) {
      dynamic_cast<Placeholder *>(ph.second)->setProposition(props[i++]);
    }
  } else if (where == slam::Location::Con) {

    for (const auto &ph : _cphToProp) {
      dynamic_cast<Placeholder *>(ph.second)->setProposition(props[i++]);
    }
    _conInCache = false;
  } else {
    for (const auto &ph : _acphToProp) {
      dynamic_cast<Placeholder *>(ph.second)->setProposition(props[i++]);
    }
    _conInCache = false;
    _antInCache = false;
  }
}


void Template::fillContingency(size_t (&ct)[3][3], bool offset) {

    // make sure the chaced values are initialized
    evaluate(0);
  
    if (offset) {
      //ant -> !con
  
      for (size_t time = 0; time < _max_length; time++) {
        //size_t shift =
        //    time + (_applyDynamicShift ? _dynamicShiftCachedValues[time] : 0) +
        //    _constShift;
        auto ant = evaluate_ant(time);
        auto con = evaluate_con(time);
        if (ant == Trinary::T && (!con) == Trinary::T) {
          ct[0][0]++;
        } else if (ant == Trinary::T && (!con) == Trinary::F) {
          assert(0);
          ct[0][1]++;
        } else if (ant == Trinary::T && (!con) == Trinary::U) {
          ct[0][2]++;
        } else if (ant == Trinary::F && (!con) == Trinary::T) {
          ct[1][0]++;
        } else if (ant == Trinary::F && (!con) == Trinary::F) {
          ct[1][1]++;
        } else if (ant == Trinary::F && (!con) == Trinary::U) {
          ct[1][2]++;
        } else if (ant == Trinary::U && (!con) == Trinary::T) {
          ct[2][0]++;
        } else if (ant == Trinary::U && (!con) == Trinary::F) {
          ct[2][1]++;
        } else if (ant == Trinary::U && (!con) == Trinary::U) {
          ct[2][2]++;
        }
      }
    } else {
      //ant -> con
  
      for (size_t time = 0; time < _max_length; time++) {
        //size_t shift =
        //    time + (_applyDynamicShift ? _dynamicShiftCachedValues[time] : 0) +
        //    _constShift;
        auto ant = evaluate_ant(time);
        auto con = evaluate_con(time);
        if (ant == Trinary::T && con == Trinary::T) {
          ct[0][0]++;
        } else if (ant == Trinary::T && con == Trinary::F) {
          ct[0][1]++;
        } else if (ant == Trinary::T && con == Trinary::U) {
          ct[0][2]++;
        } else if (ant == Trinary::F && con == Trinary::T) {
          ct[1][0]++;
        } else if (ant == Trinary::F && con == Trinary::F) {
          ct[1][1]++;
        } else if (ant == Trinary::F && con == Trinary::U) {
          ct[1][2]++;
        } else if (ant == Trinary::U && con == Trinary::T) {
          ct[2][0]++;
        } else if (ant == Trinary::U && con == Trinary::F) {
          ct[2][1]++;
        } else if (ant == Trinary::U && con == Trinary::U) {
          ct[2][2]++;
        }
      }
    }
}

void Template::setCacheAntFalse() { _antInCache = false; }

void Template::setCacheConFalse() { _conInCache = false; }


void Template::genPermutations(const std::vector<Proposition *> &antP,
                               const std::vector<Proposition *> &conP,
                               const std::vector<Proposition *> &antConP) {
  //fully instantiated : only one permutation
  if (getNumPlaceholders() == 0) {
    _pg._size.first = 1;
    _pg._size.second = 0;
    _permIndex = 0;
    return;
  }

  // save the domains of the permutations
  _aProps = antP;
  _cProps = conP;
  _acProps = antConP;

  messageErrorIf(_aProps.size() < _aphToProp.size(),
                 "Not enough 'a' propositions!");
  messageErrorIf(_cProps.size() < _cphToProp.size(),
                 "Not enough 'c' propositions!");
  messageErrorIf(_acProps.size() < _acphToProp.size(),
                 "Not enough 'ac' propositions!");

  //generate only if there are not any previously generated perms
  if (_pg._perms == nullptr) {
    _pg.genPermutations(_aProps.size(), _cProps.size(), _acProps.size(), this);
  }
  //set to the first perm
  _permIndex = 0;
}


void Template::printContingency() {

  size_t ct[3][3] = {{0}};
  fillContingency(ct, 0);
  fort::utf8_table table;
  table.set_border_style(FT_NICE_STYLE);
  ft_set_cell_span(table.getTablePointer(), 0, 0, 4);
  table.column(1).set_cell_text_align(fort::text_align::center);
  table.column(2).set_cell_text_align(fort::text_align::center);
  table.column(3).set_cell_text_align(fort::text_align::center);
  table.column(4).set_cell_text_align(fort::text_align::center);

  table << fort::header << "Contingency" << fort::endr;

  table << ""
        << "CT"
        << "CF"
        << "CU" << fort::endr;
  ft_add_separator(table.getTablePointer());
  table << "AT" << ct[0][0] << ct[0][1] << ct[0][2] << fort::endr;
  ft_add_separator(table.getTablePointer());
  table << "AF" << ct[1][0] << ct[1][1] << ct[1][2] << fort::endr;
  ft_add_separator(table.getTablePointer());
  table << "AU" << ct[2][0] << ct[2][1] << ct[2][2] << fort::endr;
  std::cout << table.to_string() << std::endl;
}
void Template::check() {
  //FIXME
  messageErrorIf(!isFullyInstantiated(),
                 "Checking is available only for fully instantiated templates "
                 "(assertions)!");
  std::cout << "==============================================================="
               "==========="
            << "\n";
  std::cout << getColoredAssertion() << "\n";
  setCacheAntFalse();
  setCacheConFalse();
  evaluate(0);
  size_t ct[3][3] = {{0}};
  fillContingency(ct, 0);

  if (!assHoldsOnTrace(slam::Location::AntCon)) {
    printContingency();
    std::cout << "Failing sub-traces:\n";
    for (size_t i = 0; i < _max_length; i++) {
      if (evaluate(i) == Trinary::F) {
        std::cout << "===================================="
                  << "\n";

        auto intv = this->getConsequentInterval();


        std::cout << "[" << i << "," << intv.second << "]"
                  << "\n";
        std::cout << _trace->printTrace(i, intv.second+1) << "\n";
        std::cout << "===================================="
                  << "\n";
      }
    }
  } else {
    printContingency();
    std::cout << "OK!"
              << "\n";
  }

  if (_max_length < 50) {
    std::cout << "Ant: ";
    for (size_t i = 0; i < _max_length; i++) {
        std::cout << evaluate_ant(i) << "(" << i << ")" << " ";
    }

    std::cout << "\n";
    std::cout << "\n";

    std::cout << "Con: ";
    for (size_t i = 0; i < _max_length; i++) {
      std::cout << evaluate_con(i) << "(" << i << ")" << " ";
    }
    std::cout << "\n";
    std::cout << "\n";
    std::cout << "Ass: ";
    for (size_t i = 0; i < _max_length; i++) {
      std::cout << evaluate(i) << "(" << i << ")"
                << " ";
    }
    std::cout << "\n";
  }
  std::cout << "\n";
  std::cout << "==============================================================="
               "==========="
            << "\n";
}

bool Template::isFullyInstantiated() {
  return (getNumPlaceholders(slam::Location::Ant) +
          getNumPlaceholders(slam::Location::Con) +
          getNumPlaceholders(slam::Location::AntCon)) == 0 &&
         _dtOp.second == nullptr;
}
std::vector<std::pair<CachedAllNumeric::EvalRet,size_t>> Template::gatherInterestingValue(CachedAllNumeric *cn, int depth, int width) {

  DTOperator *template_dt = _dtOp.second;

  Proposition *tc = new BooleanConstant(true, VarType::Bool, 1, 0);
  Proposition *fc = new BooleanConstant(false, VarType::Bool, 1, 0);
  std::vector<size_t> iv_suffix;  

  //Automaton::Node *cn = _ant->_root;
  slam::Implication * impl = _impl;
  size_t currTime = 0;
  template_dt->addItem(tc,{0,0},depth);
  while (currTime < _max_length) {
    if(impl->evaluate_ant(currTime) == Trinary::T && impl->evaluate_con(currTime) == Trinary::T)
      iv_suffix.push_back(currTime);
    // each currTime we change state, currTime increases by 1
    currTime++;
    
  }
  template_dt->popItem(depth);
  //now we have a vector of interesting values for the already instantiated part of the template
  //iterate on cn trace values, to get {value,time} pairs
  std::vector<std::pair<CachedAllNumeric::EvalRet,size_t>> ret;
  for(currTime = 0; currTime < _max_length; currTime++){
      CachedAllNumeric::EvalRet value = cn->evaluate(currTime);
      for(size_t iv : iv_suffix){
        if(iv >= currTime && ((iv - currTime) <= _limits._maxDistance) && ((iv - currTime) >= _limits._minDistance)){
          ret.push_back(std::make_pair(value,(size_t)iv-currTime));
          break;
        }
      }
  }

  delete tc;
  delete fc;
  return ret;
  
}

TemporalExp *Template::getPropByToken(const std::string &token) {
  if (_tokenToProp.count(token)) {
    return _tokenToProp.at(token);
  }
  return nullptr;
}

void Template::subPropInAssertion(Proposition *original, Proposition *newProp) {
  //FIXME
  //bool found = 0;
  //for (auto ph : _tokenToProp) {
  //  if ((*ph.second) == original) {
  //    (*ph.second) = newProp;
  //    found = 1;
  //  }
  //}
  //messageErrorIf(!found, "Did not find proposition '" + prop2String(*original) +
  //                           "' in '" + getColoredAssertion() + "'");
}


} // namespace slam
