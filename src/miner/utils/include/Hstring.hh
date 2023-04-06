#pragma once

#include "colors.hh"
#include "exp.hh"

#include <string>
#include <vector>

class Hstring {
public:
  enum class Stype {
    Temp,
    Intv,
    Ph,
    Inst,
    Imp,
    DTAnd,
    DTNext,
    DTNCReps,
    DTNextAnd,
    G
  };

  Hstring(std::string s, Stype t, expression::Proposition **pp = nullptr);

  Hstring(std::string s, Stype t, size_t **intv = nullptr);
  
  Hstring();

  ~Hstring() = default;

  Hstring operator+(const Hstring &right);
  Hstring getAnt();
  Hstring getCon();
  Hstring getImp();
  size_t size();

  Hstring &operator[](size_t i);

  std::vector<Hstring>::iterator begin();
  std::vector<Hstring>::iterator end();
  std::vector<Hstring>::reverse_iterator rbegin();
  std::vector<Hstring>::reverse_iterator rend();
  void insert(std::vector<Hstring>::iterator where, const Hstring &toInsert);

  bool exists(std::string toFind);

  std::string toColoredString(bool sub = false);
  std::string toString(bool sub = false);
  std::string toSpotString();

  std::vector<Hstring> getDTOperands();
  static bool isDT(const Hstring &e);

  std::string _s;
  Stype _t;
  expression::Proposition **_pp;
  int _offset;
  std::string _sep;
  size_t ** _intv;

private:
  std::vector<Hstring> _append;
};
  std::ostream & operator<<(std::ostream &os,const Hstring::Stype &t);
