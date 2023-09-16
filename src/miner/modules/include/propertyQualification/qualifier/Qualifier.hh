#pragma once

#include "PropertyQualifier.hh"
#include <unordered_map>

namespace exharm {

/*! \class Qualifier
    \brief used to rank the assertions
*/
class Qualifier : public PropertyQualifier {

  /*! \struct FunctionParameter
    \brief used to keep the parameters of the "calibration" function f(x) = 1/(1 + e^(z - kx))^2

*/
  struct FunctionParameter {
    FunctionParameter(double z, double k) : _z(z), _k(k) {
      // not todo
    }
    FunctionParameter() {}

    double _z;
    double _k;
  };

public:
  explicit Qualifier();

  ~Qualifier() override {}

  /** \brief rank the assertions in the given context (print or dump the result), return the ranked assertions
   */
  virtual std::vector<Assertion *> qualify(Context &context,
                                           Trace *trace) override;

private:
  /** \brief parse a trace containing a fault
   */
  Trace *parseFaultyTrace(const std::string &ftStr);

  /** \brief evaluate the given metric on the given assertion
   */
  double evaluate(Assertion &a, Metric &m);
  /** \brief evalute the "calibrate" funtion for value x
   */
  double scoreFunction(double x, FunctionParameter &fp);
  void printAssertions(Context &context, std::vector<Assertion *> &assertions,
                       Trace *trace);
  /** \brief find fault coverage
   */
  void faultBasedQualification(std::vector<Assertion *> selected, Trace *trace);
  void fbqUsingFaultyTraces(std::vector<Assertion *> &selected);
  /** \brief faults are inserted direclty on the trace
   */
  void fbqUsingFaultOnTraceMode(std::vector<Assertion *> &selected,
                                Trace *trace, size_t &nFaults);
  void dumpAssToFile(Context &context, Trace *trace,
                     std::vector<Assertion *> &assertions);

  /** \brief for each sorting metric, gather the max values reached by any of the input assertions
   */
  std::unordered_map<std::string, double>
  getMaxValuesForSortMetrics(std::vector<Metric *> &metrics,
                             std::vector<Assertion *> &assertions);

  /** \brief for each filtering metric, gather the max values reached by any of the input assertions
   */
  std::unordered_map<std::string, double> getMaxValuesForFilterMetrics(
      std::vector<std::pair<Metric *, double>> &metrics,
      std::vector<Assertion *> &assertions);

  std::vector<Assertion *> rankAssertions(Context &context, Trace *trace);

  /** \brief sort the input assertions according to their finalScore
   */
  void sortAssertionsWithMetrics(std::vector<Metric *> &metrics,
                                 std::vector<Assertion *> &assertions,
                                 size_t currParamIndex = 19);

  /** \brief filter the input assertions using the 'filter' metrics
   */
  void filterAssertionsWithMetrics(
      std::vector<Assertion *> &assertions,
      std::vector<std::pair<Metric *, double>> &metrics);

  /** \brief load the parameters for the interactive ranking with several 'calibration' functions
   */
  void loadParams();

  /** \brief run the sat solver to find the minimum number of assertions covering the maximum number of faults
   */
  std::vector<size_t> getCoverageSet();

  /** \brief returns all the assertions were ant != con
   */
  std::vector<Assertion *>
  patchDiscardAssertions(std::vector<Assertion *> &inAssertions, Trace *trace);

  /** \brief filter redundant assertions, quikly allbeit less precisely
   */
  std::vector<Assertion *>
  extractUniqueAssertionsFast(std::vector<Assertion *> &inAssertions);

  /** \brief filter redundant assertions
   */
  std::vector<Assertion *>
  extractUniqueAssertions(std::vector<Assertion *> &inAssertions);

  size_t _traceLength;

  ///keeps the ids of the assertions covering the maximum numbers of faults
  std::vector<size_t> _coverageSet;

  std::unordered_map<size_t, FunctionParameter> _functionParams;
  /** \brief filter redundant assertions, quikly allbeit less precisely
   */
  /** \brief max value to calibrate the function in the ranking
   * values go from 1 (range is 0.1-10) to 90 (range is 0.9-1)
   */
  size_t _maxParamIndex = 0;
  ///maps the assertion to the faults they cover
  std::unordered_map<size_t, std::vector<size_t>> _aToF;
  ///maps covered faults to the assertion covering them
  std::unordered_map<size_t, std::vector<size_t>> _fToA;
  ///used in fault-on-trace mode to keep the relation between a fault and corresponding bit a variable
  std::unordered_map<size_t, std::string> _fToVar;
};

} // namespace exharm
