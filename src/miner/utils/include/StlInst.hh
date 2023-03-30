#pragma once 

#include"TemporalExp.hh"
#include"Template.hh"

namespace harm{

    class StlInst: public TemporalExp{
        public:
            StlInst(Proposition ** prop);

            ~StlInst();

            Trinary evaluate(size_t time) override;

        private:
            Proposition ** _prop;

    };

};