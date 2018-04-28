/*************************
Copyright 2008 Jason Li

This file is part of ia2sat.

IA2SAT is free software; you can redistribute it
and/or modify it under the terms of the GNU General
Public License as published by the Free Software
Foundation; either version 2 of the License, or
(at your option) any later version.

IA2SAT is distributed in the hope that it will be
useful, but WITHOUT ANY WARRANTY; without even the
implied warranty of MERCHANTABILITY or FITNESS FOR 
A PARTICULAR PURPOSE. See the GNU General Public 
License for more details.

You should have received a copy of the GNU General
Public License along with IA2SAT; if not, write to
the Free Software Foundation, Inc., 51 Franklin St, 
Fifth Floor, Boston, MA  02110-1301  USA
*************************/

#ifndef _CSP
#define _CSP
#include "Allen.h"
#include <vector>
#include <set>
#include <assert.h>
using namespace std;

#define MAX_RECURSE 	100


struct Csp{
  bool pointbased;
  bool unsat;
  unsigned vc;	    // var count
  unsigned ec;	    // edge count
  int *edges;       // storing edges as constraints between two vertices
  RELTYPE *edgeLabels;  // 1-dim. array with entries same as in csp file
  RELTYPE *cspArray;    // 1-dim. array storing csp with indexing    
  RELTYPE *cspArrayPA;
  unsigned *firstBoolVar; // first boolean variable for an edge
  unsigned *domainSize;   // domainsize of an edge
  unsigned maxBoolVar;    // max index of boolean variable
  vector<vector<int> > clauses;  // clauses to store the cnf
  vector<set<int> > encodedNodes;
  vector<set<int> > sharedIANodes; 
  Csp(void);
  Csp(FILE *f, unsigned vCount, bool pb); // constructor
  ~Csp(void);           // destructor
  void prepareIA(void); // prepare IA Encoding
  void preparePA(void);     // prepare PA Encoding
  void prepareHmetis(void); // prepare HMETIS
  void lookAllTriangles(void);
  
  void encodeAllDomainsPA(void);
  void encodeTrianglesPA(int *nodes, unsigned size);
  unsigned encodePA_SUP(int i, int j, int k);
  void encodeTriangles(int *nodes, unsigned size);
  void cutGraph(int *mynodes, int *myedges, 
  	        unsigned myNodeCount, unsigned myEdgeCount, set<int> *shared,
		unsigned recursionCount);
  
  bool makePathConsistent(void);
  bool makePathConsistentPA(void);
  bool revise(RELTYPE *rel, unsigned size, unsigned i, unsigned k, unsigned j, bool usePA);
  bool pathConsistency(RELTYPE *rel, unsigned size, bool usePA);
  void printCnf(void); // print the CNF
  void doTwo(void); // cut the graph into two then encode
  void verifySatSol(void);
};



#endif
