#include "PropositionParserHandler.hh"

#define CHECK_ABORT                                                            \
  if (_abort)                                                                  \
    return;

namespace hparser {
using namespace expression;

PropositionParserHandler::PropositionParserHandler(slam::Trace *trace)
    : _abort(false), _proposition(), _logicExpressions(), _numericExpressions(),
      _trace(trace) {}

void PropositionParserHandler::exitFile(__attribute__((unused))
                                        propositionParser::FileContext *ctx) {
  _errorMessages.clear();
}
void PropositionParserHandler::enterFile(__attribute__((unused))
                                         propositionParser::FileContext *ctx) {
  _abort = false;

  while (!_proposition.empty()) {
    delete _proposition.top();
    _proposition.pop();
  }

  while (!_numericExpressions.empty()) {
    delete _numericExpressions.top();
    _numericExpressions.pop();
  }

  while (!_logicExpressions.empty()) {
    delete _logicExpressions.top();
    _logicExpressions.pop();
  }
}

void PropositionParserHandler::enterBooleanConstant(
    propositionParser::BooleanConstantContext *ctx) {
  antlr4::tree::TerminalNode *con = ctx->BOOLEAN();
  std::string conStr = std::string(con->getText());

  if (conStr == "@false") {
    auto *c = new BooleanConstant(false, VarType::Bool, 1, _trace->getLength());
    _proposition.push(c);
    return;
  } else if (conStr == "@true") {
    auto *c = new BooleanConstant(true, VarType::Bool, 1, _trace->getLength());
    _proposition.push(c);
    return;
  } else {
    messageError("Uknown boolean constant!" + printErrorMessage());
  }
}

void PropositionParserHandler::enterLogicConstant(
    propositionParser::LogicConstantContext *ctx) {
  std::string conStr = std::string(ctx->getText());

  if (ctx->VERILOG_BINARY() != nullptr) {
    messageErrorIf(conStr.size() - 2 > 64,
                   "Constant '" + conStr.substr(0, conStr.size()) +
                       "' exceeds the maximum length of 64 bits" +
                       printErrorMessage());
    ULogic value = std::stoull(conStr.substr(2, conStr.size() - 2), nullptr, 2);
    auto *c = new LogicConstant(value, VarType::ULogic, conStr.size() - 2,
                                _trace->getLength());
    _logicExpressions.push(c);
    return;
  } else if (ctx->GCC_BINARY() != nullptr) {
    messageErrorIf(conStr.size() - 2 > 64,
                   "Constant '" + conStr.substr(0, conStr.size()) +
                       "' exceeds the maximum length of 64 bits" +
                       printErrorMessage());
    ULogic value = std::stoull(conStr.substr(2, conStr.size() - 2), nullptr, 2);
    auto *c = new LogicConstant(value, VarType::ULogic, conStr.size() - 2,
                                _trace->getLength());
    _logicExpressions.push(c);
    return;
  } else if (ctx->HEX() != nullptr) {
    messageErrorIf((conStr.size() - 2) * 4 > 64,
                   "Constant '" + conStr.substr(0, conStr.size()) +
                       "' exceeds the maximum length of 64 bits" +
                       printErrorMessage());
    ULogic value =
        std::stoull(conStr.substr(2, conStr.size() - 2), nullptr, 16);
    auto *c = new LogicConstant(value, VarType::ULogic, (conStr.size() - 2) * 4,
                                _trace->getLength());
    _logicExpressions.push(c);
    return;
  } else if (ctx->NUMERIC() != nullptr) {
    size_t res = conStr.find('.');
    if (res != std::string::npos) {
      messageWarning("Float literal truncated to integer");
      conStr = conStr.substr(0, res);
    }

    if (conStr.front() == '-') {
      // Store the logic as 2s complement int
      ULogic value = std::stoll(conStr);
      auto *c =
          new LogicConstant(value, VarType::SLogic, 64, _trace->getLength());
      _logicExpressions.push(c);
    } else {
      // Store the logic as classic unsigned binary
      ULogic value = std::stoull(conStr);
      auto *c =
          new LogicConstant(value, VarType::ULogic, 64, _trace->getLength());
      _logicExpressions.push(c);
    }
    return;
  }
  messageError("Unknown logic constant!" + printErrorMessage());
}
void PropositionParserHandler::enterNumericConstant(
    propositionParser::NumericConstantContext *ctx) {
  if (ctx->NUMERIC() != nullptr) {
    Numeric value = std::stod(ctx->getText());
    auto *c =
        new NumericConstant(value, VarType::Numeric, 64, _trace->getLength());
    _numericExpressions.push(c);
    return;
  }
}

void PropositionParserHandler::enterBooleanVariable(
    propositionParser::BooleanVariableContext *ctx) {
  propositionParser::VariableContext *tNode = ctx->variable();
  std::string varName = std::string(tNode->getText());
  // //std::cout << __func__ << ": " << varName << std::endl;

  _proposition.push(_trace->getBooleanVariable(varName));
}
void PropositionParserHandler::enterLogicVariable(
    propositionParser::LogicVariableContext *ctx) {
  propositionParser::VariableContext *tNode = ctx->variable();
  std::string varName = std::string(tNode->getText());
  // //std::cout << __func__ << ": " << varName << std::endl;

  if (ctx->SIGN() != nullptr && ctx->NUMERIC() != nullptr) {
    _logicExpressions.push(_trace->getLogicVariable(varName));
  } else {
    messageError("Sign or size not set in logic variable" +
                 printErrorMessage());
  }
}
void PropositionParserHandler::enterNumericVariable(
    propositionParser::NumericVariableContext *ctx) {
  propositionParser::VariableContext *tNode = ctx->variable();
  std::string varName = std::string(tNode->getText());
  // //std::cout << __func__ << ": " << varName << std::endl;

  if (ctx->NUMERIC() != nullptr) {
    _numericExpressions.push(_trace->getNumericVariable(varName));
  }
}
void PropositionParserHandler::exitBoolean(
    propositionParser::BooleanContext *ctx) {
  if (ctx->LPAREN() && ctx->RPAREN()) {
    // std::cout<<__func__<<"()"<<std::endl;
    return;
  }
  if (ctx->boolean().size() == 1) {
    if (ctx->NOT()) {
      // std::cout<<__func__<<"!"<<std::endl;
      Proposition *p = _proposition.top();
      _proposition.pop();
      _proposition.push(makeExpression<PropositionNot>(p));
      return;
    }

    messageError("Unknown unary boolean operator!" + printErrorMessage());
  } else if (ctx->boolean().size() == 2) {
    antlr4::Token *boolop = ctx->booleanop;
    if (boolop != nullptr) {
      // std::cout<<__func__<<"boolop"<<std::endl;
      Proposition *p2 = _proposition.top();
      _proposition.pop();
      Proposition *p1 = _proposition.top();
      _proposition.pop();
      if (boolop->getText() == "&&") {
        _proposition.push(makeExpression<PropositionAnd>(p1, p2));
        return;
      } else if (boolop->getText() == "||") {
        _proposition.push(makeExpression<PropositionOr>(p1, p2));
        return;
      }
      messageError("Unknown boolean operator in expression!" +
                   printErrorMessage());
    }
    if (ctx->EQ() != nullptr) {
      // std::cout<<__func__<<"="<<std::endl;
      Proposition *p2 = _proposition.top();
      _proposition.pop();
      Proposition *p1 = _proposition.top();
      _proposition.pop();
      _proposition.push(makeExpression<PropositionEq>(p1, p2));
      return;
    }
    if (ctx->NEQ() != nullptr) {
      // std::cout<<__func__<<"!="<<std::endl;
      Proposition *p2 = _proposition.top();
      _proposition.pop();
      Proposition *p1 = _proposition.top();
      _proposition.pop();
      _proposition.push(makeExpression<PropositionNeq>(p1, p2));
      return;
    }
    messageError("Unknown binary boolean operator!" + printErrorMessage());
  }

  if (_logicExpressions.size() == 1) {
    LogicExpression *le = _logicExpressions.top();
    _logicExpressions.pop();
    _proposition.push(new LogicToBool(le));
    return;
    messageError("Unknown unary logic operator in boolean expression!" +
                 printErrorMessage());
  } else if (ctx->logic().size() == 2) {
    propositionParser::RelopContext *relop = ctx->relop();
    if (relop != nullptr) {
      // std::cout<<__func__<<"relop"<<std::endl;
      LogicExpression *le2 = _logicExpressions.top();
      _logicExpressions.pop();

      LogicExpression *le1 = _logicExpressions.top();
      _logicExpressions.pop();

      if (relop->LT() != nullptr) {
        _proposition.push(makeExpression<LogicLess>(le1, le2));
        return;
      }
      if (relop->LE() != nullptr) {
        _proposition.push(makeExpression<LogicLessEq>(le1, le2));
        return;
      }
      if (relop->GT() != nullptr) {
        _proposition.push(makeExpression<LogicGreater>(le1, le2));
        return;
      }
      if (relop->GE() != nullptr) {
        _proposition.push(makeExpression<LogicGreaterEq>(le1, le2));
        return;
      }
      messageError("Unknown relational operator!" + printErrorMessage());
    }
    if (ctx->EQ() != nullptr) {
      // std::cout<<__func__<<"="<<std::endl;
      LogicExpression *le2 = _logicExpressions.top();
      _logicExpressions.pop();
      LogicExpression *le1 = _logicExpressions.top();
      _logicExpressions.pop();
      _proposition.push(makeExpression<LogicEq>(le1, le2));
      return;
    }
    if (ctx->NEQ() != nullptr) {
      // std::cout<<__func__<<"!="<<std::endl;
      LogicExpression *le2 = _logicExpressions.top();
      _logicExpressions.pop();
      LogicExpression *le1 = _logicExpressions.top();
      _logicExpressions.pop();
      _proposition.push(makeExpression<LogicNeq>(le1, le2));
      return;
    }
    messageError("Unknown binary logic operator!" + printErrorMessage());
  }

  if (_numericExpressions.size() == 1) {
    NumericExpression *ne = _numericExpressions.top();
    _numericExpressions.pop();
    _proposition.push(new NumericToBool(ne));
    return;
  } else if (ctx->numeric().size() == 2) {
    propositionParser::RelopContext *relop = ctx->relop();
    if (relop != nullptr) {
      // std::cout<<__func__<<"relop"<<std::endl;
      NumericExpression *ne2 = _numericExpressions.top();
      _numericExpressions.pop();

      NumericExpression *ne1 = _numericExpressions.top();
      _numericExpressions.pop();

      if (relop->LT() != nullptr) {
        _proposition.push(makeExpression<NumericLess>(ne1, ne2));
        return;
      }
      if (relop->LE() != nullptr) {
        _proposition.push(makeExpression<NumericLessEq>(ne1, ne2));
        return;
      }
      if (relop->GT() != nullptr) {
        _proposition.push(makeExpression<NumericGreater>(ne1, ne2));
        return;
      }
      if (relop->GE() != nullptr) {
        _proposition.push(makeExpression<NumericGreaterEq>(ne1, ne2));
        return;
      }
      messageError("Unknown relational operator!" + printErrorMessage());
    }
    if (ctx->EQ() != nullptr) {
      // std::cout<<__func__<<"="<<std::endl;
      NumericExpression *le2 = _numericExpressions.top();
      _numericExpressions.pop();
      NumericExpression *le1 = _numericExpressions.top();
      _numericExpressions.pop();
      _proposition.push(makeExpression<NumericEq>(le1, le2));
      return;
    }
    if (ctx->NEQ() != nullptr) {
      // std::cout<<__func__<<"!="<<std::endl;
      NumericExpression *le2 = _numericExpressions.top();
      _numericExpressions.pop();
      NumericExpression *le1 = _numericExpressions.top();
      _numericExpressions.pop();
      _proposition.push(makeExpression<NumericNeq>(le1, le2));
      return;
    }
    messageError("Unknown binary numeric operator!" + printErrorMessage());
  }
}
void PropositionParserHandler::exitLogic(propositionParser::LogicContext *ctx) {
  // std::cout<<__func__<<std::endl;

  if (ctx->LPAREN() && ctx->RPAREN()) {
    return;
  }

  if (ctx->logic().size() == 1) {
    if (ctx->NEG() != nullptr) {
      LogicExpression *le_r = makeExpression<LogicNot>(_logicExpressions.top());
      _logicExpressions.pop();
      _logicExpressions.push(le_r);
      return;
    }
    if (ctx->bitSelect() != nullptr) {
      size_t left;
      size_t right;
      LogicExpression *le_r = nullptr;
      if (ctx->bitSelect()->NUMERIC().size() > 1) {
        left = std::stoul(ctx->bitSelect()->NUMERIC()[0]->getText());
        right = std::stoul(ctx->bitSelect()->NUMERIC()[1]->getText());
        le_r = new LogicBitSelector(_logicExpressions.top(), left, right);
      } else {
        left = std::stoul(ctx->bitSelect()->NUMERIC()[0]->getText());
        right = left;
        le_r = new LogicBitSelector(_logicExpressions.top(), left, right);
      }
      _logicExpressions.pop();
      _logicExpressions.push(le_r);
      return;
    }

    if (ctx->DER() != nullptr) {
      size_t shift =
          ctx->NUMERIC() != nullptr ? std::stoul(ctx->NUMERIC()->getText()) : 1;
      LogicExpression *le = _logicExpressions.top();
      _logicExpressions.pop();
      LogicExpression *le_r = new LogicDerivative(le, shift);
      _logicExpressions.push(le_r);
      return;
    }

    messageError("Unknown unary logic operator in logic expression!" +
                 printErrorMessage());

  } else if (ctx->logic().size() == 2) {
    antlr4::Token *logop = ctx->logop;

    if (logop != nullptr) {
      LogicExpression *le2 = _logicExpressions.top();
      _logicExpressions.pop();

      LogicExpression *le1 = _logicExpressions.top();
      _logicExpressions.pop();

      auto conversionResult =
          applyCStandardConversion(le1->getType(), le1->getType());

      if (logop->getText() == "&") {
        LogicExpression *le_r = makeExpression<LogicBAnd>(le1, le2);
        le_r->setType(conversionResult.first, conversionResult.second);
        _logicExpressions.push(le_r);
        return;
      }
      if (logop->getText() == "|") {
        LogicExpression *le_r = makeExpression<LogicBOr>(le1, le2);
        le_r->setType(conversionResult.first, conversionResult.second);
        _logicExpressions.push(le_r);
        return;
      }
      if (logop->getText() == "^") {
        LogicExpression *le_r = makeExpression<LogicBXor>(le1, le2);
        le_r->setType(conversionResult.first, conversionResult.second);
        _logicExpressions.push(le_r);
        return;
      }
      if (logop->getText() == "<<") {
        LogicExpression *le_r = makeExpression<LogicLShift>(le1, le2);
        le_r->setType(conversionResult.first, conversionResult.second);
        _logicExpressions.push(le_r);
        return;
      }
      if (logop->getText() == ">>") {
        LogicExpression *le_r = makeExpression<LogicRShift>(le1, le2);
        le_r->setType(conversionResult.first, conversionResult.second);
        _logicExpressions.push(le_r);
        return;
      }

      messageError("Unknown binary logic operator in logic "
                   "expression!" +
                   printErrorMessage());
    }

    antlr4::Token *artop = ctx->artop;

    if (artop != nullptr) {
      LogicExpression *le2 = _logicExpressions.top();
      _logicExpressions.pop();

      LogicExpression *le1 = _logicExpressions.top();
      _logicExpressions.pop();

      auto conversionResult =
          applyCStandardConversion(le1->getType(), le2->getType());

      if (artop->getText() == "*") {
        LogicExpression *le_r = makeExpression<LogicMul>(le1, le2);
        le_r->setType(conversionResult.first, conversionResult.second);
        _logicExpressions.push(le_r);
        return;
      }
      if (artop->getText() == "/") {
        LogicExpression *le_r = makeExpression<LogicDiv>(le1, le2);
        le_r->setType(conversionResult.first, conversionResult.second);
        _logicExpressions.push(le_r);
        return;
      }
      if (artop->getText() == "-") {
        LogicExpression *le_r = makeExpression<LogicSub>(le1, le2);
        le_r->setType(conversionResult.first, conversionResult.second);
        _logicExpressions.push(le_r);
        return;
      }
      if (artop->getText() == "+") {
        LogicExpression *le_r = makeExpression<LogicSum>(le1, le2);
        le_r->setType(conversionResult.first, conversionResult.second);
        _logicExpressions.push(le_r);
        return;
      }
      messageError("Unknown binary arithmetic operator in logic "
                   "expression!" +
                   printErrorMessage());
    }
  }
}
void PropositionParserHandler::exitNumeric(
    propositionParser::NumericContext *ctx) {
  // std::cout<<__func__<<std::endl;

  if (_logicExpressions.size() == 1) {
    LogicExpression *le = _logicExpressions.top();
    _logicExpressions.pop();
    _numericExpressions.push(new LogicToNumeric(le));
    return;
  }

  if (ctx->numeric().size() == 1) {
    if (ctx->DER() != nullptr) {
      size_t shift =
          ctx->NUMERIC() != nullptr ? std::stoul(ctx->NUMERIC()->getText()) : 1;
      NumericExpression *ne = _numericExpressions.top();
      _numericExpressions.pop();
      NumericExpression *ne_r = new NumericDerivative(ne, shift);
      _numericExpressions.push(ne_r);
    } else {
      messageError("Unknown unary numeric operator in logic expression!" +
                   printErrorMessage());
    }
  } else if (ctx->numeric().size() == 2) {
    antlr4::Token *artop = ctx->artop;

    if (artop != nullptr) {
      NumericExpression *ne2 = _numericExpressions.top();
      _numericExpressions.pop();

      NumericExpression *ne1 = _numericExpressions.top();
      _numericExpressions.pop();

      auto conversionResult =
          applyCStandardConversion(ne1->getType(), ne2->getType());

      if (artop->getText() == "*") {
        NumericExpression *ne_r = makeExpression<NumericMul>(ne1, ne2);
        ne_r->setType(conversionResult.first, conversionResult.second);
        _numericExpressions.push(ne_r);
        return;
      }
      if (artop->getText() == "/") {
        NumericExpression *ne_r = makeExpression<NumericDiv>(ne1, ne2);
        ne_r->setType(conversionResult.first, conversionResult.second);
        _numericExpressions.push(ne_r);
        return;
      }
      if (artop->getText() == "-") {
        NumericExpression *ne_r = makeExpression<NumericSub>(ne1, ne2);
        ne_r->setType(conversionResult.first, conversionResult.second);
        _numericExpressions.push(ne_r);
        return;
      }
      if (artop->getText() == "+") {
        NumericExpression *ne_r = makeExpression<NumericSum>(ne1, ne2);
        ne_r->setType(conversionResult.first, conversionResult.second);
        _numericExpressions.push(ne_r);
        return;
      }
      messageError("Unknown binary arithmetic operator in numeric "
                   "expression!" +
                   printErrorMessage());
    }
  }
  if (ctx->LPAREN() && ctx->RPAREN()) {
    return;
  }
}

Proposition *PropositionParserHandler::getProposition() {
  messageErrorIf(_proposition.size() != 1,
                 "No proposition to return" + printErrorMessage());

  Proposition *ret = _proposition.top();
  _proposition.pop();

  return ret;
}

std::string PropositionParserHandler::printErrorMessage() {
  std::stringstream ss;
  for (auto &msg : _errorMessages) {
    ss << msg << "\n";
  }
  return ss.str();
}

void PropositionParserHandler::visitErrorNode(__attribute__((unused))
                                              antlr4::tree::ErrorNode *node) {
  messageError("Antlr parse error: " + node->getText() + "\n" +
               printErrorMessage());
}
void PropositionParserHandler::addErrorMessage(const std::string &msg) {
  _errorMessages.push_back(msg);
}

} // namespace hparser
