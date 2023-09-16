  
  
  

## EX-HARM

The official repo of the EXtended Hint-Based AsseRtion Miner  

## Table of contents

[Project info](#project-info)

[Quick start](#quick-start)
1. [Install dependencies](#dependencies)
2. [Build the project](#build-the-project)
3. [Run default tests](#run-default-tests)

[How to use the miner](#how-to-use-the-miner)
* [Run with vcd trace](#run-with-a-vcd-trace)
* [Run with csv trace](#run-with-a-csv-trace)
* [Automatically generating a configuration file](#automatically-generating-a-configuration-file)

[The configuration file](#the-configuration-file)

[How to check an assertion](#how-to-check-an-assertion)



[Optional arguments](#optional-arguments)

## Project info

EX-HARM (EXtended Hint-based AsseRtion Miner) is a tool to generate Signal Temporal Logic (STL) assertions starting from a set of user-defined hints and the simulation traces of the design under verification (DUV). The tool is agnostic with respect to the design from which the trace was generated, thus the DUV source code is not necessary. The user-defined hints involve STL templates, propositions and ranking metrics that are exploited by the assertion miner to reduce the search space and improve the quality of the generated assertions. This way, the tool supports the work of the verification engineer by including his/her insights in the process of automatically generating assertions.

# Quick start

For now, we support only Linux and Mac OS (both x86 and arm64) with gcc (c++17) and cmake 3.14+.

## Dependencies
* [antlr4-runtime](https://www.antlr.org)
  

(skip this step if you already have the required dependencies on the path)

* Install all the dependencies manually or simply run the commands below.


```
sudo apt-get install -y uuid-dev pkg-config
```

* Install all dependencies in the local repository (all the dependencies will be compiled from source);

```
cd third_party
bash install_all.sh
```


## Build the project

```
mkdir build && cd build
cmake -DCMAKE_BUILD_TYPE=Release ..
```
(you can use option -DCMAKE_INSTALL_PREFIX=/path/to/install/directory/ of cmake to specify where to install ex-harm and its dependencies)
```
make
```

## Run tests
The tests for the tool can be run from the /path/to/install/Ex-harm/build directory using:

```
ctest -V -R
```
(This will run all the tests)

To show all available tests use:

```
ctest --show-only
```

To run a specific test use:
 ```
ctest -V -R testname
```
for example for the test regarding the "tank" system:
 ```
ctest -V -R tank
```

To run the tests on scalability for a specific system use:
```
ctest -V -R testname_
```
for example for the scalability tests regarding the "tank" system:
 ```
ctest -V -R tank_
```

### Mac OS only
* Install the libraries (specify a proper path usig cmake) 
```
make install
```
* Add the libraries to the runtime library path
```
export DYLD_LIBRARY_PATH=/path/to/install/directory/Ex-harm/lib:$DYLD_LIBRARY_PATH
```

# How to use the miner  
EX-HARM has two main inputs, a trace in the form of a csv file and a set of hints.
Hints consist of a set of propositions, templates and metrics; they are defined in a separate xml configuration file. 
The user can find several working examples in the "tests" directory .

## Run with a csv trace

```
./harm --csv trace.csv --conf config.xml
```
*  use --csv-dir <DIRECTORY>  to give as input a set of .csv traces
* Note that you do not have to specify a clock signal when using a csv file, as each row is already considered a clock event.
* A CSV trace must contain the declaration of the design's variables in the first row, following a C/Verilog style.
	
Example of valid csv file:
```
int var1, bool var2, float var3
23, 1, 34.7
34, 0, 99.912
```
	
## Automatically generating a configuration file
To simplify the creation of a new test, EX-HARM is capable of generating a sample configuration file using the variables found in the trace.  The user might want to modify the generated configuration file to adapt it to her/his needs.

For csv:
```
./ex-harm --csv trace.csv --conf path/to/newConfig.xml --generate-config
```

 EX-HARM will create the configuration file on the path given as argument.

#  The configuration file
 It is recommended to always start from an automatically generated configuration file (using the --generate-config option).
 Hints are organised in contexts, each context contains three types of expressions: propositions, templates and metrics (see the configuration file below).  
 ```xml
<harm>
	<context name="c1">
		<prop exp="var1 && var2" loc="a"/>
		<prop exp="var3 + var4 > 100" loc="a"/>
		<prop exp="!var5 || !var6" loc="c"/>
		<prop exp="var8" loc="c"/>
		
		<numeric clsEffort="0.3" exp="var7 + var8" loc="c"/>
		
		<template dtLimits="4A,3D,2D,-0.1E,R,O" exp="G({..F..}|-> F[0,0](P0))" /> 
		
	
		<filter name="causality" exp="1-afct/traceLength" threshold="0.45"/>
		<sort name="pRepetitions" exp="1/(pRepetitions*2+1)" />
		<sort name="frequency" exp="atct/traceLength"/>
	</context>
</harm>
```
#### Proposition
 Propositions are non-temporal boolean expressions used to fill the empty spots (placeholders) of the templates;  metrics are used to perform the final ranking of assertions. Propositions can be written using all boolean, relational an arithmetic operators of the C/C++ language.
For the full grammar of propositions, check "src/antl4/propositionParser/grammar/proposition.g4".
	
A proposition is defined inside the "exp" attribute
* WARNING: if you are using a vcd trace, the variables must include the hierarchical path as a prefix, ex. "test1::modn::a" is the variable "a" in module "modn" instantiated in module "test1". Check the vcd file to retrieve the path.
* Do not include the prefix common to all variables in the vcd, ex. If all design's variables are contained inside the global scope "test1", then variable "a" must be referenced as "modn::a"

Propositions are labelled (using the 'loc' attribute of 'prop') with "a", "c", "ac" and "dt"
* "a" propositions will be used only to fill antecedent's placeholders (not the dt operator)
* "c" propositions will be used only to fill consequent's placeholders (not the decision tree operators)
* "ac" propositions will be used only in placeholders appearing in both the antecedent and the consequent.
* "dt" propositions will be used only to fill decision tree operators 

#### Numerics
The user can specify a set of tuples N = \{(ne\_i, loc\_i, th\_i) | i =1, ..., k\} to automatically generate propositions (using a clustering algorithm) predicating over arithmetic expressions, like c==ne, c>= ne, c<= ne, c\_l<= ne <= c\_r, with c, c\_l, c\_r representing constants of numeric type, and ne indicating numerical expressions involving DUV  variables.
* ne\_i is a numeric expression ("exp" attribute)
* loc\_i is a location label (among 'a', 'c', 'ac', and 'dt', following the same meaning as in a proposition, "loc" attribute). 
* th\_i is a numeric threshold (from 0 to 1, "clsEffort" attribute) that is used to specify how much effort the tool must put in to generate propositions including the numeric expression ne\_i (for technical reasons, a threshold close to 0 is considered high effort while a threshold close to 1 is low effort).



#### Template


Templates can be written using all LTL operators, they must follow the form "G(antecedent -> consequent)"; all variables (inside the template) of the form P\<N\> are considered  placeholders. For instance, template "G(P0 && P1 -> P2 U P3)" has 4 placeholders.
For the full grammar of templates, check "src/antl4/templateParser/grammar/temporal.g4".
 
 There are three special placeholders: ..&&.., ..##\<N>.. and ..#\<N>&..;  when  employed, the miner will try to replace them with a corresponding expression using a decision tree (DT) algorithm.
 
 * ..F..  will be replaced with an expression of type v1 && F[t1,t2]v2 && .. && [tn1,tn2]vn
 
 These placeholders can only be used once in the antecedent.
 
 A template using a Decision Tree Operator (DTO) is associated with a configuration (defined in the 'dtLimits' attribute of 'template') involving several adjustable parameters:
 * \<uint\>A : the maximum number of operands to be added to the DT operator.
 * \<uint\>D : the maximum number of temporal operands to be added to the DT operator. Adding a temporal operands increases the temporal depth of the DT operator.
 * \<uint\>W : the maximum number of propositions to be added at a certain depth in the dt operator
* S, R: this parameter states if a DT operator with a temporal dimension must construct expressions following a sequential (S) or an unordered (R, random) approach. To understand this, consider a DTO ..##2.. with parameter 3D, the resulting expression must follow the implicit template o_1 ##2 o_2 ##2 o_3; however, the order in which o_1, o_2, o_3 are substituted greatly changes the outcome of the DT algorithm. A sequential DTO adds the operands in order from o_1 to o_3 while an unordered DTO can add operands in any order. The first one can only generate the expressions "o_1", "o_1 ##2 o_2", "o_1 ##2 o_2 ##2 o_3" while the latter can generate expressions such as "o_1 ##4 o_3" or "##4 o_3".
* <float>E is used to adjust the computational effort of the DT algorithm, in practice, it is used to decide the number of candidates selected by the DT algorithm to split the search space. Legal values: from 0 to 1. If E is associated with a negative value, then the algorithm will put in the least possible effort to mine assertions.
* O: this parameter states that the DT algorithm must return the assertions belonging to the offset; such assertions are obtained by negating the consequent of an implication that is false each time the antecedent is true (G(ant -> !con)), making the implication always T on the trace.

#### Metric
A metric is a numeric formula measuring the impact of an assertion's feature in the assertion ranking. 
The more prominent the feature, the higher its impact on the final ranking of the assertion. The elements of the contingency table are examples of features of an assertion. Metrics can be used either to filter or sort the assertions.
* Filtering metrics are associated with a threshold; assertions with a score below the threshold of any filtering metric are directly discarded. 
* Sorting metrics are used to perform the ranking. The ranking is computed according to an overall score.

Currently available assertion features (more will be added):

* atct : number of time units in which antecedent true implies consequent true
* afct : antecedent false and consequent true
* auct : antecedent uknown and consequent true
* atcf 
* afcf
* aucf
* atcu
* afcu
* aucu
* traceLength : length of the trace (the sum of lengths in case of multiple input traces)
* complexity : number of propositions in the assertion
* pRepetition : number of repeated propositions in the assertion

#   How to check an assertion
The template expression has an additional parameter "check", if it is set to "1" then the miner analyses the corresponding assertion on the given trace, if the assertion does not hold on the input traces, it reports the cause of failure.  Example:
```
<template check="1" exp="G((v1==100) |-> F[0,0](v3))" />
``` 
 Note that the template must be fully instantiated (no placeholders).
 
 #  Optional arguments

* \-\-cls-alg : <String> type of clustering algorithm; <kmeans>, <kde> kernel density estimation, <hc> hierarchical (default is kmeans)
* \-\-dont-fill-ass : do not populate assertions with values (saves memory)
* \-\-dump : dumps all assertions and their contingency matrix in the current folder
* \-\-dump-stat : dump mining statistics to file
* \-\-dump-to <DIRECTORY> : dump assertions to file on given path
* \-\-fd <DIRECTORY> : path to the directory containing the faulty traces (for fault coverage)
* \-\-find-min-subset : find the minimum number of assertions covering all faults (must be used with --fd)
* \-\-help : show options
* \-\-interactive : enable interactive assertion ranking
* \-\-dont-normalize : discard assertions using the absolute value (not normalized) of filterig metrics 
* \-\-isilent : disable all infos
* \-\-max-ass <uint> : the maximum number of assertions to keep after the ranking
* \-\-max-threads <uint> : max number of threads that EX-HARM is allowed to spawn
* \-\-name : <String> name of this execution (used when dumping statistics);
* \-\-psilent : disable all progress bars
* \-\-silent : disable all outputs
* \-\-split-logic : generate a config file where all bitvecots are split into single bit variables (must be used with --generate-config)
* \-\-sva : output assertions in SystemVerilog Assertion format
* \-\-vcd-r : recursively add signals for all sub-scopes
* \-\-vcd-ss <string> :  select a scope of signals in the .vcd trace
* \-\-wsilent : disable all warnings
