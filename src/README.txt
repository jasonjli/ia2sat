/*************************
Copyright 2008 Jason Jingshi Li

************************/

README:

This software converts a Constraint Satisfaction Problem (CSP) in Interval
Algebra (IA) into a Boolean Satisfiability Problem (SAT) in Conjunctive Normal
Form (CNF). 

IA2SAT uses a partitioned-based method that divide a large problem in many
smaller problems. The partitioned-based method is described in the paper:

Jason J. Li, Jinbo Huang and Jochen Renz, A Divide-and-Conquer Approach for
Solving Interval Algebra Networks, To appear in Proceedings of the 11st
International Joint Conference on Artificial Intelligence (IJCAI-09). 

The partition of the IA-CSP uses hMeTiS v1.5.3 obtained at:

http://glaros.dtc.umn.edu/gkhome/metis/hmetis/download



/**********************************
Compilation
***********************************/

The software can be compiled by typing the following into the commandline:

make

If compilation returns an error, it may be caused by the machine architecture of
the hMeTiS library. We only provide the linux library of hMeTis (libhmetis.a).
However, libraries for other architectures can be obtained from hmetis website
described above.


/**********************************
Running
***********************************/

The program prints the CNF into the standard output stream. 

To convert an IA-CSP (example.csp) into a CNF file (example.cnf), you can do the following:

./ia2sat -pt ./example.csp > ./example.cnf

Note the "-pt" uses the point-based encoding as described in the paper. If you
wish to use the interval-based encoding, simply omit it.

./ia2sat ./example.csp > ./example.cnf

You can also solve the csp using any of your favourite satsolver via piping:

./ia2sat -pt ./example.csp | ~/satSolver/solve

(for your sat-solver located at ~/satSolver/)


/**********************************
Questions
***********************************/

For any questions please email Jason Li at:

jason.li@gmx.ch

