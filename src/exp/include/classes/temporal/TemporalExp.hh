#pragma once

#include "Trinary.hh"
#include "classes/atom/Atom.hh"
#include "message.hh"
#include <vector>

namespace expression {

class ExpVisitor;

class TemporalExp {
public:
  virtual ~TemporalExp() {}

  virtual Trinary evaluate(size_t time) = 0;

  virtual std::vector<TemporalExp *> getItems() = 0;

  virtual size_t size() = 0;

  virtual void acceptVisitor(ExpVisitor &vis) = 0;
};
}; // namespace expression
