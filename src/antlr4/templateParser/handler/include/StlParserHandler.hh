#pragma once

#include "DTLimits.hh"
#include "Trace.hh"
#include "exp.hh"
#include "stlBaseListener.h"
#include "stlLexer.h"

#include <cmath>
#include <stack>
#include <string>
#include <unordered_map>

namespace slam {
class Template;
}

namespace hparser {

class StlParserHandler : public stlBaseListener {

public:
  explicit StlParserHandler(slam::Trace *trace, slam::DTLimits limits);

  ~StlParserHandler() override = default;

  slam::Template *getTemplate() {
     
      return _template; }
  void addErrorMessage(const std::string &msg);

  bool _useCache = 1;

private:
  bool _abort;

  std::stack<expression::TemporalExp *> _tfStack;
  std::stack<std::string> _intervalNames;
  std::unordered_map<std::string, std::pair<size_t, size_t> *> _intervals;
  slam::Trace *_trace;
  slam::Template *_template;
  std::unordered_map<std::string, expression::TemporalExp **> _phToProp;
  std::unordered_map<std::string, std::string> _propStrToInst;
  size_t dtCount = 0;
  size_t instCount = 0;
  std::vector<std::string> _errorMessages;

  std::string printErrorMessage();

  void enterFile(stlParser::FileContext *ctx) override;
  void exitFile(stlParser::FileContext *ctx) override;
  virtual void visitErrorNode(antlr4::tree::ErrorNode *node) override;
  virtual void exitImplication(stlParser::ImplicationContext * ctx) override;
  virtual void exitTformula(stlParser::TformulaContext *ctx) override;
  virtual void exitInterval(stlParser::IntervalContext *ctx) override;
};

} // namespace hparser
