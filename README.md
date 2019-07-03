# README #

July, 2019

### OVERVIEW ###

This is version 2.0 of QRATPre+.

Changes from version 1.0 to 2.0:

  - more modularized code base
  - API to integrate QRATPre+ in other tools (see './examples/api-example.c')

QRATPre+ is a preprocessor to simplify quantified Boolean formulas (QBFs)
given in prenex conjunctive normal form (PCNF). For simplification, QRATPre+
tries to eliminate redundant clauses from the PCNF, or universal literals from
clauses. It implements redundancy checking based on the QRAT+ proof
system. QRAT+ is a generalisation of the QRAT proof system. QRAT was introduced by
Heule, Seidl, and Biere:

* M. Heule, M. Seidl, A. Biere: Solution Validation and Extraction for QBF
  Preprocessing. J. Autom. Reasoning 58(1), 2017.

* M. Heule, M. Seidl, A. Biere: A Unified Proof System for QBF
  Preprocessing. JCAR 2014.

For redundancy checking, the QRAT+ system relies on QBF-specific unit
propagation with universal reduction to handle the literals of certain
universal variables. This is in contrast to QRAT, which applies propositional
unit propagation and treats every variable as existentially quantified. As a
result, redundancy removal based on QRAT+ is more powerful than based on QRAT.

### PUBLICATIONS ###

A tool paper related to QRATPre+ appeared at [SAT 2019](http://sat2019.tecnico.ulisboa.pt/):

* Florian Lonsing and Uwe Egly. QRATPre+: Effective QBF Preprocessing
  via Strong Redundancy Properties. In Proc. of the 22nd International
  Conference on Theory and Applications of Satisfiability Testing
  (SAT) 2019, Springer, LNCS. Preprint: [https://arxiv.org/pdf/1904.12927.pdf](https://arxiv.org/pdf/1904.12927.pdf).

The theory behind QRATPre+ is described in our 
[IJCAR 2018](http://ijcar2018.org/) paper:

* Florian Lonsing and Uwe Egly. QRAT+: Generalizing QRAT by a More Powerful
QBF Redundancy Property. In Proc. of the 9th International Joint Conference on
Automated Reasoning (IJCAR) 2018, Springer, LNCS. Preprint: [https://arxiv.org/pdf/1804.02908](https://arxiv.org/pdf/1804.02908).

### USAGE INFORMATION ###

QRATPre+ website: https://lonsing.github.io/qratpreplus/

Run `./qratpre+ -h` or `./qratpre+ --help` to display command line help.

To preprocess a formula, call: 

`./qratpre+ --print-formula <qdimacs-file>`

where `<qdimacs-file>` is a QBF in [QDIMACS
format](http://www.qbflib.org/qdimacs.html).

By default, redundancy checking is based on the QRAT+ system. To apply the
QRAT system instead, call:

`./qratpre+ --no-eabs --print-formula <qdimacs-file>`

Depending on the given input formula, QRATPre+ may or may not run until
saturation. That is, it may happen that the output formula produced by a call
of QRATPre+ still contains redundant parts that can be removed by calling
QRATPre+ a second time on the output. This is due to the internal scheduling
of the non-confluent redundancy elimination rules applied in the QRAT and
QRAT+ proof systems.

#### Preprocessing large formulas ####

By default, QRATPre+ applies several redundancy elimination techniques, which
may be prohibitive on large formulas. In this case, it is recommended to set a
soft time limit in seconds by running QRATPre+ with parameter
`--soft-time-limit=<n>`, where `<n>` is a positive integer value. When
exceeding the soft time limit, the formula will be printed with redundancies
removed that have been detected so far.

### LICENSE ###

QRATPre+ is free software released under GPLv3:

[https://www.gnu.org/copyleft/gpl.html](https://www.gnu.org/copyleft/gpl.html)

See also file LICENSE.

### INSTALLATION ###

The latest release is available from
[GitHub](https://github.com/lonsing/qratpreplus).

Unpack the archive and run 'make'. The build process produces optimized code
without assertions (default).

### CONTACT INFORMATION ###

For comments, questions, bug reports etc. related to QRATPre+, please contact:

Florian Lonsing, Stanford University, USA

[http://www.florianlonsing.com/](http://www.florianlonsing.com/)
