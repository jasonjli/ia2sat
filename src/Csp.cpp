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

#include <stdio.h>
#include <stdlib.h>
#include <ctype.h>

#include "Csp.h"

// print major points
// #define MDEBUG 1

#ifdef MDEBUG
	#define MDB(x) x
#else 
	#define MDB(x) 
#endif

// print details
//#define UPDEBUG 1

#ifdef UPDEBUG
	#define DB(x) x
#else 
	#define DB(x) 
#endif

//#define PRINTFILE 1

#ifdef PRINTFILE
	#define PR(x) x
	#define NPR(x)
#else 
	#define PR(x) 
	#define NPR(x) x
#endif




extern "C" void HMETIS_PartRecursive(int nvtxs, int nhedges, int *vwgts, 
	int *eptr, int *eind, int *hewgts, int npart, int ubfactor,
	int *options, int *part, int *edgecut);
	
Csp::Csp(FILE *ifp, unsigned vCount, bool pb): pointbased(pb), unsat(false), vc(vCount), ec(0), edges(NULL), 
                       edgeLabels(NULL), cspArray(NULL), cspArrayPA(NULL), 
                       firstBoolVar(NULL), domainSize(NULL),
                       maxBoolVar(0), clauses(){

  /*FILE *ifp;
  if ((ifp = fopen(fname, "r")) == NULL){
    fprintf(stderr, "Cannot open file: %s\n", fname);
    exit(0);
  }*/

  char line[128];
  char c;
  unsigned edgeIndex = 0;

  float cspDegree;
    
  cspDegree = 13;
  
  // Allocate memory
  DB(printf("Allocating memory\n");)
  
  edges = (int *) malloc((int) (vc * cspDegree * 2) * sizeof(int));
  edgeLabels = (RELTYPE *) malloc((int) (vc * cspDegree) * sizeof(RELTYPE));

  // Read CSP
  unsigned node1, node2;
  RELTYPE r;

  while((c=getc(ifp)) != EOF){

    if (isspace(c)) continue; else ungetc(c,ifp);

    // read line into memory
    fgets(line,128,ifp);
    
    DB(printf("Reading %s", line);)
    // Reading full stop, done
    if (line[0] == '.') {
      break;
    }

    // parse the constraint
    
    if (parsecons(line, &r, &node1, &node2)) {
      // check for error in vertices
      if ((node1 > vc) || (node1 < 0) || (node2 > vc) || (node2 < 0) ||
	  (node1 == node2)) {
	fprintf(stderr,"\n*** Illegal vertex id: '%s'\n",line);
	return;
      }
      
      // sort node1/node2
      /*if (node2 < node1){
        unsigned tmpNode = node1;
	node1 = node2;
	node2 = tmpNode;
	r = inverse(r);
      }*/
      
      // store constraint
      ec++;
      edges[edgeIndex*2] = node1;
      edges[edgeIndex*2+1] = node2;
      edgeLabels[edgeIndex++] = r; 
      
       
    } else {
      // cannot parse constraint
      fprintf(stderr, "I cannot parse constraint number %d\n", ec);
      exit(-1);
    }        
  }  // end of while loop
  if (c == EOF)
    ungetc(1, ifp);  

  cspArray = ( RELTYPE *) malloc(sizeof(RELTYPE)*vc*vc);
  assert(cspArray);
  
  for (unsigned i=0; i<vc; i++)
    for (unsigned j=0; j<vc; j++)
      cspArray[i*vc+j] = 8191;

  // add labels to indexed array   
  for (unsigned i=0; i<ec; i++){
    int node1 = edges[i*2];
    int node2 = edges[i*2+1];
    RELTYPE rel = edgeLabels[i];
    cspArray[node1*vc+node2] = rel;
    cspArray[node2*vc+node1] = inverse(rel);
  } 
  if (pointbased)
    preparePA();
  else 
    prepareIA();  
}

Csp::~Csp(void){
	free(edges);
	free(edgeLabels);
}

void Csp::prepareIA(void){

  // store the constraints in an indexed array
  
  firstBoolVar = ( unsigned *) malloc(sizeof(unsigned)*vc*vc);
  domainSize = (unsigned *) malloc(sizeof(unsigned)*vc*vc);
  
  assert(firstBoolVar);
  assert(domainSize);

  // store array with universal relation
  for (unsigned i = 0; i < vc; i++)
    for (unsigned j=0; j<vc; j++){
  
      firstBoolVar[i*vc+j] = 0;
      domainSize[i*vc+j] = 0;
    }
  

}

void Csp::preparePA(void){

  MDB(printf("Preparing PA\n");)

  // store the constraints in an indexed array
  cspArrayPA = ( RELTYPE *) malloc(sizeof(RELTYPE)*vc*2*vc*2);
  firstBoolVar = ( unsigned *) malloc(sizeof(unsigned)*vc*2*vc*2);
  domainSize = (unsigned *) malloc(sizeof(unsigned)*vc*2*vc*2);
  assert(cspArrayPA);
  assert(firstBoolVar);
  assert(domainSize);

  MDB( printf("store array\n");)
  
  // store array with universal relation
  for (unsigned i = 0; i < vc*2; i++)
    for (unsigned j=0; j<vc*2; j++){
      cspArrayPA[i*vc*2+j] = 7;
      firstBoolVar[i*vc*2+j] = 0;
      domainSize[i*vc*2+j] = 0;
    }
  
  
  maxBoolVar = 1;
  
  // ensure every interval has a beginning and end       
    
  for (unsigned i=0; i<vc; i++){
    cspArrayPA[2*i*vc*2+2*i+1] = 2; // RLT  
    cspArrayPA[(2*i+1)*vc*2+2*i] = 4; // RGT
  }
    
  // add other constraints between two points
  if (makePathConsistent())
  for (unsigned node1=0; node1<vc; node1++){
    for (unsigned node2=node1+1; node2<vc; node2++){
      
      RELTYPE rel = cspArray[node1*vc+node2];
    
      RELTYPE ss=0, se=0, es=0, ee=0;
    
      // find possible relations of end points for rel

      for (unsigned j=1; j <= countAtoms(rel); j++){
        RELTYPE rel_atom = getNthAtom(rel, j);
        ss = (ss | getEndPointLiteral(rel_atom, 0));
        se = (se | getEndPointLiteral(rel_atom, 1));
        es = (es | getEndPointLiteral(rel_atom, 2));
        ee = (ee | getEndPointLiteral(rel_atom, 3));      
      }
         
      cspArrayPA[node1*2*vc*2+node2*2] = ss;
      cspArrayPA[node1*2*vc*2+node2*2+1] = se;
      cspArrayPA[(node1*2+1)*vc*2+node2*2] = es;
      cspArrayPA[(node1*2+1)*vc*2+node2*2+1] = ee;
      
      cspArrayPA[node2*2*vc*2+node1*2] = inverse(ss);
      cspArrayPA[(node2*2+1)*vc*2+node1*2] = inverse(se);
      cspArrayPA[(node2*2)*vc*2+node1*2+1] = inverse(es);
      cspArrayPA[(node2*2+1)*vc*2+node1*2+1] = inverse(ee);
    }
  }
  
  
  
  if(!makePathConsistentPA()){    
    unsat = true;
    return;
  }

 MDB( printf("PA Prepared\n");)
}  


void Csp::prepareHmetis(void){

    int *eptr = (int *) malloc((ec+1) * sizeof(int));
    if (eptr==NULL) return;
    // graph each edge have two nodes
    for (unsigned i=0; i<=ec; i++)
    	eptr[i] = i*2;

    int *eind;
    eind = edges;
    int *part = NULL, edgecut;
    part = (int *) malloc(vc * sizeof(int));
    
    int options[9];
    
    options[0] = 1;
    options[1] = 10; // Nruns (default)
    options[2] = 1;  // CType (hybrid)
    options[3] = 1;  // RType (default)
    options[4] = 3;  // Vcycle (max-quality)
    options[5] = 0;  // Reconst (default)
    options[6] = 1;  // pre-assigned vertices
    options[7] = -1; // random seed (default)
    options[8] = 0;  // debugging info (default)
    int ubFactor = 15;   // more liberal cut    
    
    for (unsigned i=0; i<vc; i++){
      part[i] = -1;
    }
    
    for (unsigned i=2; i<50; i++){
      part[i] = 0;
    }
    
    DB(printf("preparing for HMETIS\n");)
    
    HMETIS_PartRecursive(vc, ec, NULL, 
	eptr, eind, NULL, 2, ubFactor,
	options, part, &edgecut);
    
    DB(printf("HMETIS completed\n");)

}

unsigned clauseCount = 0;
// set<int> abstractedEdges;


void Csp::doTwo(void){

  MDB( printf("entering doTwo\n");)

  maxBoolVar = 1;
  vector<int> clause;
    
  PR(FILE *myf = fopen("new.cnf", "w");)
  PR(assert(myf);)
  
  // PR(fprintf("p cnf 246693 81618498\n");)
    
  // perform path-consistency first    
  if  (!makePathConsistent()){
  
    // if path inconsistent, 
    // just give two clauses that are contradictions
    
    unsat = true;
    
    PR(fprintf(myf, "p ncnf\n");)
    PR(fclose(myf);)
    return;
  }
  
  if (pointbased)
     encodeAllDomainsPA();
  
 MDB( printf("all encoded\n");)
    
  // set array for nodes
  int *mynodes = (int *) malloc(vc*sizeof(int));
    
  for (unsigned i=0; i<vc; i++){
    mynodes[i] = i;
  }
  
  // set array for edges
  int *myedges = (int *) malloc(ec*2*sizeof(int));
  
  // copy edges from CSP
  for (unsigned i=0; i<ec; i++){
    myedges[i*2] = edges[i*2];
    myedges[i*2+1] = edges[i*2+1];
  }
  
  MDB(printf("recursively add transivity clauses, max level %d\n", MAX_RECURSE);)
  
  // encodeTrianglesPA(mynodes, vc);
   cutGraph(mynodes, myedges, vc, ec, NULL, 0);

  PR(maxBoolVar--;)
  PR(printf("printing to file %d variable, %d clauses\n", maxBoolVar, clauseCount);)

  MDB(printf("%d abstracted edges out of %d\n", abstractedEdges.size()/2, vc*vc);)
}

unsigned cutSameGraph = 0;

void Csp::cutGraph(int *mynodes, int *myedges, 
		   unsigned myNodeCount, unsigned myEdgeCount,
  		   set<int> *shared, unsigned recursionCount){

  // mynodes, an array of nodes with size myNodeCount
  // myedges, an array of edges, each edge contain the index of mynodes,
  // myNodeCount, number of nodes in mynodes
  // myEdgeCount, number of edges in myedges
  // shared, the index of the nodes that are already pre-assigned to be together.

 DB(printf("Recursion level %d\n", recursionCount);  )

  // no edges to cut
  if (myEdgeCount == 0)
    return;

  // set up pointer for edge array
  int *eptr = (int *) malloc((myEdgeCount+1) * sizeof(int));
  assert(eptr);

  // graph each edge have two nodes
  for (unsigned i=0; i<=myEdgeCount; i++)
    eptr[i] = i*2;

  // set up array to store result of the cutting
  int *part = (int *) malloc(myNodeCount * sizeof(int));
  assert(part);
  
  for (unsigned i=0; i<myNodeCount; i++)
    part[i] = -1; // vertex i is free to move

  // other variables for graph-cutting
  int edgecut;
    
  int *eind = myedges;
  
  int ubFactor= 35;

  int *options = (int *) malloc(9*sizeof(int)); 
  
  options[0] = 1;
  options[1] = 10; // Nruns (default)
  options[2] = 1;  // CType (hybrid)
  options[3] = 1;  // RType (default)
  options[4] = 1;  // Vcycle (default)
  options[5] = 0;  // Reconst (default)
  options[6] = 0;  // pre-assigned vertices
  options[7] = 1; // seed
  options[8] = 0;  // debugging info (default)  

  unsigned assignCount = 0;

  for( vector <set<int> >::iterator iter_i = sharedIANodes.begin();       	     
       iter_i < sharedIANodes.end(); ++iter_i) {
    
    for (unsigned i=0; i<myNodeCount; i++){
      if ((*iter_i).find(mynodes[i]) != (*iter_i).end() ){
        if (part[i] != 0){
	  assignCount++;
	  part[i] = 0;
	}
      }
    }	         
  } 

  if (assignCount > 1){
    options[0] = 1;
    options[1] = 10; // Nruns (default)
    options[2] = 1;  // CType (hybrid)
    options[3] = 1;  // RType (default)
    options[4] = 1;  // Vcycle (default)
    options[5] = 0;  // Reconst (default)
    options[6] = 1;  // pre-assigned vertices
    options[7] = 1; // seed
    options[8] = 0;  // debugging info (default)
    ubFactor = 35;   // more liberal cut
    
    DB(printf("%d add to part, %d free\n", assignCount,myNodeCount-assignCount);)
  }

  
  DB(printf("calling HMETIS\n");			)
  DB(printf("mynodes\n");				)
  DB(for (unsigned i=0; i<myNodeCount; i++){		)
  DB(  printf("%d ", mynodes[i]);			)
  DB(}							)
  DB(printf("\n");					)
  DB(printf("myedges\n");				)
  DB(for (unsigned i=0; i<myEdgeCount; i++){		)
  DB(  printf("%d-%d ", myedges[i*2], eind[i*2+1]);	)
  DB(}							)
  DB(printf("\n");					)
  DB(printf("eptr\n");					)
  DB(for (unsigned i=0; i<=myEdgeCount; i++){		)
  DB(  printf("%d ", eptr[i]);				)
  DB(}							)
  DB(printf("\n");					)
  DB(printf("part\n");					)
  DB(for (unsigned i=0; i<myNodeCount; i++){		)
  DB(  printf("%d ", part[i]);				)
  DB(}							)
  DB(printf("\n");					)
  
  

  // partition the graph
  // for (unsigned i=0; i<3; i++)
  HMETIS_PartRecursive(myNodeCount, myEdgeCount, NULL,
	eptr, eind, NULL, 2, ubFactor,
	options, part, &edgecut);

  DB(printf("HMETIS returned\n");)

  // in case of no partition
  if (edgecut == 0){
  
    // just encode all the triangles
    MDB(printf("no cut, level %d\n", recursionCount);)
    if (pointbased)
      encodeTrianglesPA(mynodes, myNodeCount);
    else
      encodeTriangles(mynodes, myNodeCount);
    free(part);
    free(eptr);
    free(options);
    
    return;
  }  
  
  // otherwise, the graph is cut.
  // now requires two arrays to store respective parts

  // determine the two arrays
  unsigned n1Count = 0, n2Count = 0;

  // Count number of vertices in each partition
  for (unsigned i = 0; i < myNodeCount; i++){
    if (part[i] == 0) n1Count++;
  }
  n2Count = myNodeCount-n1Count;  
  
  // count the number of "shared" nodes
  // "shared" nodes belong to whichever network that is smaller
  set<int> sharedNodes;

  // set up the number of edges in each subnetwork after cut
  unsigned myEdgeCount1=0, myEdgeCount2=0;
  
  // we add vertex from n2 to n1
  bool addN2ToN1 = (n1Count < n2Count);

  DB(printf("count number of shared nodes\n");)
  // loop over the edges
  // 1. count the number of shared nodes 
  // 2. count the number of edges for each network  
  for (unsigned i=0; i<myEdgeCount; i++){
    
    // exclusive edge for n1
    if (part[myedges[i*2]] == 0 && part[myedges[i*2+1]] == 0){
        myEdgeCount1++;
    }
    
    // shared edge n1-n2
    else if (part[myedges[i*2]] == 0 && part[myedges[i*2+1]] == 1){    
      if (addN2ToN1){
        sharedNodes.insert(mynodes[myedges[i*2+1]]);
        myEdgeCount1++;
      }
      else  {
        sharedNodes.insert(mynodes[myedges[i*2]]);
	myEdgeCount2++;
      }
    }
    
    // shared edge n2-n1
    else if (part[myedges[i*2]] == 1 && part[myedges[i*2+1]] == 0){
      
      if (addN2ToN1)  {
        sharedNodes.insert(mynodes[myedges[i*2]]);
        myEdgeCount1++;
      }
      else {
        sharedNodes.insert(mynodes[myedges[i*2+1]]);
	myEdgeCount2++;
      }
    }
    
    // exclusive edge for n2
    else if (part[myedges[i*2]] == 1 && part[myedges[i*2+1]] == 1){
      myEdgeCount2++;
    }  
    
  }  // endfor i
          
  // Add shared nodes to the other network in size
  if (addN2ToN1) n1Count += sharedNodes.size();
  else n2Count += sharedNodes.size();


  DB(printf("partitions %d n1, ", n1Count-sharedNodes.size());)
  DB(printf("%d n2, ", n2Count-sharedNodes.size());)
  DB(printf("%d shared\n", sharedNodes.size());)

  // prepare parameters to prepare for recursion
  // two edge arrays, two node arrays
  int *myEdges1, *myEdges2, *myNodes1, *myNodes2;

  myNodes1 = (int *)malloc(n1Count*sizeof(int));
  myNodes2 = (int *)malloc(n2Count*sizeof(int));
  myEdges1 = (int *)malloc(myEdgeCount1*2*sizeof(int));
  myEdges2 = (int *)malloc(myEdgeCount2*2*sizeof(int));
  
  assert(myNodes1); assert(myNodes2); assert(myEdges1); assert(myEdges2);
  
  // give a current index, work out the n1 or n2 index
  int *getN1NewIndex = (int *)malloc(myNodeCount*sizeof(int));
  int *getN2NewIndex = (int *)malloc(myNodeCount*sizeof(int));
    
  assert(getN1NewIndex); assert(getN2NewIndex);  
  
  for (unsigned i=0; i<myNodeCount; i++){
    getN1NewIndex[i] = -1;
    getN2NewIndex[i] = -1;
  }
  
  DB(printf("write nodes of sub-networks\n");)
  
  // write the nodes of the two sub-networks after cut
  unsigned n1Index=0, n2Index=0;
  
  for (unsigned i=0; i<myNodeCount; i++){
    
    // get the current vertex  
    int curNode = mynodes[i];
    
    // if this vertex is part of first sub-network
    if (part[i] == 0){
      getN1NewIndex[i] = n1Index;      // set the old for new index
      myNodes1[n1Index++] = curNode;   // store the vertex value in new array   
    }
    if (part[i] == 1){
      getN2NewIndex[i] = n2Index;     // ditto
      myNodes2[n2Index++] = curNode;  
    }
    
    // if the node is a shared node
    // add the node to the other sub-network
    if (sharedNodes.find(curNode) != sharedNodes.end()){
      if (addN2ToN1){
        getN1NewIndex[i] = n1Index;    // set the old for new index
        myNodes1[n1Index++] = curNode;	// store the vertex value in new array
      }
      else{
        getN2NewIndex[i] = n2Index;    // ditto
        myNodes2[n2Index++] = curNode;	
      }
    }    
  }
  
  DB(printf("%d %d : %d %d\n", n1Index, n1Count, n2Index, n2Count);)
 
  
  
  DB(printf("n1: ");					)
  DB(for (unsigned i=0; i<n1Count; i++){		)
  DB(  if (sharedNodes.find(myNodes1[i]) == sharedNodes.end()))
  DB(  printf("%d (%d) ", myNodes1[i], i);		)
  DB(}							)
  DB(printf("\nn2: ");					)
  DB(for (unsigned i=0; i<n2Count; i++){		)
  DB(  if (sharedNodes.find(myNodes2[i]) == sharedNodes.end()))
  DB(  printf("%d (%d) ", myNodes2[i], i);		)
  DB(}							)
  DB(printf("\nshared ");				)
  DB(for (unsigned i=0; i<myNodeCount; i++){		)
  DB(  if (sharedNodes.find(mynodes[i]) != sharedNodes.end())					)
  DB(    printf("%d (%d)(%d)(%d) ", mynodes[i], i, getN1NewIndex[i], getN2NewIndex[i]);	)
  DB(}							)
  DB(printf("\n");					)
  
  DB(printf("Edges\n");)
  DB(for (unsigned i=0; i<myEdgeCount; i++))
  DB(  printf("%d-%d\n", mynodes[myedges[i*2]], mynodes[myedges[i*2+1]]);)
  DB(printf("Edges finished\n");)

  DB(printf("Checking abstracted edges\n");)
  /*for (unsigned i=0; i<n1Count; i++){
    if (sharedNodes.find(myNodes1[i]) != sharedNodes.end()) continue;
    
    for (unsigned j=0; j<n2Count; j++){
      if (sharedNodes.find(myNodes2[j]) != sharedNodes.end()) continue;
      
      // store edge using cantor pairing function
      int thisEdge 
        = (int)(0.5*(myNodes1[i]+myNodes2[j])*(myNodes1[i]+myNodes2[j]+1)+myNodes2[j]);      
      
      int reverseEdge
        = (int)(0.5*(myNodes1[i]+myNodes2[j])*(myNodes1[i]+myNodes2[j]+1)+myNodes1[i]);
      
      if (abstractedEdges.find(thisEdge) != abstractedEdges.end()){
        printf("ERROR! abstracting an edge that is already saved\n");
	printf("Edge %d %d\n", myNodes1[i], myNodes2[j]);
	exit(0);
      }
      DB(printf("store abstracted edge %d %d\n", myNodes1[i], myNodes2[j]);)
      DB(printf("store abstracted edge %d %d\n", myNodes2[j], myNodes1[i]);)   
      abstractedEdges.insert(thisEdge);
      abstractedEdges.insert(reverseEdge);
    }        
  }*/
  
  // reset the indices  
  n1Index=0; n2Index = 0;
  
  DB(printf("write edges of sub-networks\n"); )
  
  // write the edges
  for (unsigned i=0; i<myEdgeCount; i++){
    
    // if edge is exclusively to first sub-network
    if (part[myedges[i*2]] == 0 && part[myedges[i*2+1]] == 0){
    
      // write the new edges with new indices
      myEdges1[n1Index] = getN1NewIndex[myedges[i*2]];		
      myEdges1[n1Index+1] = getN1NewIndex[myedges[i*2+1]];
      n1Index += 2;
    }
    
    // if edge is exclusively to second sub-network
    else if (part[myedges[i*2]] == 1 && part[myedges[i*2+1]] == 1){
    
      // write the new edges with new indices
      myEdges2[n2Index] = getN2NewIndex[myedges[i*2]];
      myEdges2[n2Index+1] = getN2NewIndex[myedges[i*2+1]];
      n2Index += 2;
    }
    
    // else a shared edge
    else{
    
      // if we add nodes from N2 to N1
      if (addN2ToN1){
      
        // write the new edges with new indices for N1
        myEdges1[n1Index] = getN1NewIndex[myedges[i*2]];
        myEdges1[n1Index+1] = getN1NewIndex[myedges[i*2+1]];
        n1Index += 2;        
      }
      else{ // we add nodes from N1 to N2
      
        // write the new edges with new indices for N2
        myEdges2[n2Index] = getN2NewIndex[myedges[i*2]];
        myEdges2[n2Index+1] = getN2NewIndex[myedges[i*2+1]];
        n2Index += 2;      
      }
    }
  }
  
  DB(printf("Preparation over, encode now\n");         )      
  
    
  // printf("initialize shared array\n");
  
  if (sharedNodes.size() > 1){
  
    DB(printf("Encode %d shared nodes\n", sharedNodes.size());)
    int *sharedArray = (int *) malloc(sharedNodes.size() * sizeof(int));
    
    assert(sharedArray);
    
    unsigned i=0;
    set<int> newShared;
    for( set<int>::const_iterator iter = sharedNodes.begin();
         iter != sharedNodes.end(); ++iter) {
      sharedArray[i++] = *iter;
      newShared.insert(*iter);
    }
    
    if (pointbased)  
      encodeTrianglesPA(sharedArray, sharedNodes.size()); 
    else
      encodeTriangles(sharedArray, sharedNodes.size());  
    DB(printf("add %d nodes to encoded nodes\n", sharedNodes.size());)
    sharedIANodes.push_back(newShared);

    free(sharedArray);
  } 
  else{
    DB(printf("share only two nodes\n");)
    ;
  } 

  DB(printf("N1:\n");)
  DB(for (unsigned i = 0; i<n1Count; i++){)
  DB(  printf("%d ", myNodes1[i]);)
  DB(})
  DB(printf("\n");)
  
  DB(printf("%d Edges:\n", myEdgeCount2);)
  DB(for (unsigned i=0; i<myEdgeCount1; i++){)
  DB(  printf("%d:%d-%d\n",i, myNodes1[myEdges1[i*2]],
  myNodes1[myEdges1[i*2+1]]);)
  DB(})

  DB(printf("N2:\n");)
  DB(for (unsigned i = 0; i<n2Count; i++){)
  DB(  printf("%d ", myNodes2[i]); )
  DB(})
  DB(printf("\n");)
  
  DB(printf("%d Edges:\n", myEdgeCount2);)
  DB(for (unsigned i=0; i<myEdgeCount2; i++){)
  DB(  printf("%d:%d-%d\n",i, myNodes2[myEdges2[i*2]],myNodes2[myEdges2[i*2+1]]);)
  DB(})
 
  //  
  
    
  // recursively call this function    
  if (recursionCount < MAX_RECURSE && cutSameGraph < 2){
    
    if (n1Count == assignCount) cutSameGraph++;
    
    MDB(printf("Going to recurse level %d\n", recursionCount +1);  )
    
    cutGraph(myNodes1, myEdges1, n1Count, myEdgeCount1, &sharedNodes,
             recursionCount + 1);      
    
    MDB(printf("Going second recurse level %d\n", recursionCount +1);)
    
    cutGraph(myNodes2, myEdges2, n2Count, myEdgeCount2, &sharedNodes, 
    
             recursionCount + 1);
    MDB(printf("level %d branch finished\n", recursionCount);)
  }
  else{
  
    cutSameGraph = 0;
  
    // recursion limit reached, or same partition
    
    MDB(printf("encode level %d\n", recursionCount);)
    
    if (pointbased){
      encodeTrianglesPA(myNodes1, n1Count);
      encodedNodes.pop_back();
    }
    else 
      encodeTriangles(myNodes1, n1Count);
    MDB(printf("encode second %d\n", recursionCount);)
    
    if (pointbased){
      encodeTrianglesPA(myNodes2, n2Count);
      encodedNodes.pop_back();
    }
    else
      encodeTriangles(myNodes2, n2Count);
    MDB(printf("encode finished\n");)
    // free(&sharedNodes);
  } 
  
  DB(printf("poping encodedNodes\n");)
  
  if (sharedNodes.size() > 1)
    //encodedNodes.pop_back();
    sharedIANodes.pop_back();
  
  if (pointbased)
    encodedNodes.pop_back();
  
  DB(printf("free stuff\n");)
  free(myNodes1);
  free(myNodes2);
  free(myEdges1);
  free(myEdges2);
  free(options);
  free(part);
  free(getN1NewIndex);
  free(getN2NewIndex);
  MDB(printf("all free level %d\n", recursionCount);)
}

void Csp::encodeAllDomainsPA(void){
  unsigned i,j,ii,jj, k, allALO=0, allAMO=0, allFORs=0;
  unsigned ss,se,es,ee,n1s,n1e,n2s,n2e;  
  RELTYPE rij;
  vector<int> clause;
  
  for (i=0; i<vc*2-1; i++){
    for (j=i+1; j<vc*2; j++){
    
      if (firstBoolVar[i*vc*2+j] != 0) continue; // encoded before
      
      // if (i==3 && j == 54) printf("here\n");
      
      RELTYPE rel = cspArrayPA[i*vc*2+j];
      firstBoolVar[i*vc*2+j] = maxBoolVar;
      domainSize[i*vc*2+j] = countAtoms(rel);
      maxBoolVar+=domainSize[i*vc*2+j];
      
      // ALO Clause
      clause.clear();
      
      
      for (ii=0; ii<domainSize[i*vc*2+j]; ii++)
        clause.push_back(firstBoolVar[i*vc*2+j]+ii);
      clauses.push_back(clause);
      
      allALO++;
      
      // AMO Clause      
      for (ii=0; ii<domainSize[i*vc*2+j]-1; ii++){
        for (jj=ii+1; jj<domainSize[i*vc*2+j]; jj++){
	  clause.clear();
	  clause.push_back(-1*(firstBoolVar[i*vc*2+j]+ii));
	  clause.push_back(-1*(firstBoolVar[i*vc*2+j]+jj));
	  clauses.push_back(clause);
	  allAMO++;
	}	
      }
    }
  }
  
  // forbidden clauses
  for (i=0; i<vc-1; i++){
    for (j=i+1; j<vc; j++){
      
      rij = cspArray[i*vc+j];
      
      n1s = 2*i;
      n1e = 2*i+1;
      n2s = 2*j;
      n2e = 2*j+1;
      
      // encode domain of endpoints between intervals
      ss = cspArrayPA[n1s*2*vc + n2s];
      se = cspArrayPA[n1s*2*vc + n2e];
      es = cspArrayPA[n1e*2*vc + n2s];
      ee = cspArrayPA[n1e*2*vc + n2e];      
      
      // look at forbidden constraints
      for (k=1; k<8191; k=k<<1){
        if ((k&rij) != 0) continue;
	
	if (isForbidden(ss,se,es,ee, k)){
	  
	  // k is a forbidden atom	  	  
	  // encode the forbidden clause
	  	  
	  clause.clear();
	  
	  // find out the forbidden relation at ss
	  RELTYPE ssForbidden1 = getEndPointLiteral(k,0);	
	  unsigned forIndex1 = getAtomIndex(cspArrayPA[n1s*vc*2+n2s], ssForbidden1);	  
	  clause.push_back(-1*(firstBoolVar[n1s*vc*2+n2s]+forIndex1-1));
	  
	  RELTYPE ssForbidden2 = getEndPointLiteral(k,1);	
	  unsigned forIndex2 = getAtomIndex(cspArrayPA[n1s*vc*2+n2e], ssForbidden2);
	  clause.push_back(-1*(firstBoolVar[n1s*vc*2+n2e]+forIndex2-1));
	    
	  RELTYPE ssForbidden3 = getEndPointLiteral(k,2);	
	  unsigned forIndex3 = getAtomIndex(cspArrayPA[n1e*vc*2+n2s], ssForbidden3);
	  clause.push_back(-1*(firstBoolVar[n1e*vc*2+n2s]+forIndex3-1));
	  
	  RELTYPE ssForbidden4 = getEndPointLiteral(k,3);	
	  unsigned forIndex4 = getAtomIndex(cspArrayPA[n1e*vc*2+n2e], ssForbidden4);
	  clause.push_back(-1*(firstBoolVar[n1e*vc*2+n2e]+forIndex4-1));
	  
	  clauses.push_back(clause);	  
	  
	  allFORs++;;
	  
	}
      } // endfor k
      
    }
  }  
  MDB(printf("%d ALOs\n", allALO);)
  MDB(printf("%d AMOs\n", allAMO);)
  MDB(printf("%d FORs\n", allFORs);)
  
}

void Csp::encodeTrianglesPA(int *nodes, unsigned size){
  
  set<int> thisEncodedNodes;
  
  unsigned i,j,k,ii,jj,kk;
  
  unsigned long iIndex, jIndex, kIndex;
  unsigned iMark, jMark, kMark;  
  
  PR(FILE *myf = fopen("new.cnf", "a");)
  PR(assert(myf);)
  
  unsigned sup=0;
  
  set<int> nodesToEncode;
  
  for (ii=0; ii<size; ii++){
    i = nodes[ii];
    nodesToEncode.insert(i*2);
    nodesToEncode.insert(i*2+1);
  }
  
  int *myEncodeArray = (int *)malloc(nodesToEncode.size()*sizeof(int));
  i=0;
  for (set<int>::iterator it = nodesToEncode.begin(); 
       it != nodesToEncode.end(); it++){
    myEncodeArray[i++] = (*it);    
  }
  
  // encode composition constraints 
  for (ii=0; ii<nodesToEncode.size()-2; ii++){
    i = myEncodeArray[ii];
    iMark = 0;
    iIndex = 1;
    
    for( vector <set<int> >::iterator iter_i = encodedNodes.begin();
       	     iter_i < encodedNodes.end(); ++iter_i) {
      if ((*iter_i).find(i) != (*iter_i).end() )	     
	iMark = iMark | iIndex;  
      iIndex = iIndex << 1;	    
    }    
    
    for (jj=ii+1; jj<nodesToEncode.size()-1; jj++){
      j = myEncodeArray[jj];
      
      if (j<i) printf("OUT! i:%d, j:%d, %d %d\n",i,j,ii,jj);
      
      jMark = 0; jIndex = 1;
      if (iMark != 0)
      for( vector <set<int> >::iterator iter_j = encodedNodes.begin();
       	     iter_j < encodedNodes.end(); ++iter_j) {
        if ((*iter_j).find(j) != (*iter_j).end() )	     
	  jMark = (jMark | jIndex) & iMark;  
        jIndex = jIndex << 1;	    
      }
      
      for (kk=jj+1; kk<nodesToEncode.size(); kk++){
        k = myEncodeArray[kk];
		
	kMark = 0; kIndex = 1;
	if (jMark != 0)
	for( vector <set<int> >::iterator iter_k = encodedNodes.begin();
       	     iter_k < encodedNodes.end(); ++iter_k) {
          if ((*iter_k).find(k) != (*iter_k).end() )	     
	    kMark = (kMark | kIndex) & jMark;  
          kIndex = kIndex << 1;	    
        }
	
	if (kMark != 0) continue; // i,j,k already encoded
	
	sup += encodePA_SUP(i,j,k);
	
	thisEncodedNodes.insert(i);
	thisEncodedNodes.insert(j);
	thisEncodedNodes.insert(k);

      }
    }
  }
  
  encodedNodes.push_back(thisEncodedNodes);
  MDB(printf("Encoded %d nodes in this partition\n", thisEncodedNodes.size());)
  MDB(printf("SUP %d\n", sup);)
}

unsigned Csp::encodePA_SUP(int i, int j, int k){
  
  
  unsigned sup=0;
  
  // clause to encode
  vector<int> clause;
  
  
  RELTYPE ij, jk, ik, ijAtom, jkAtom, ikAtom; 
  RELTYPE ikRefinement; 
  
  
  ij = cspArrayPA[i*vc*2+j];
  jk = cspArrayPA[j*vc*2+k];
  ik = cspArrayPA[i*vc*2+k];
  
  // if (ik >= ij && ik >= jk)
  for (ijAtom = 1; ijAtom < 8191; ijAtom = ijAtom << 1){
    if ((ijAtom & ij) == 0) continue;
    
    for (jkAtom = 1; jkAtom < 8191; jkAtom = jkAtom << 1){
      if ((jkAtom & jk)==0) continue;
      
      ikRefinement = pa_composition(ijAtom, jkAtom);
      
      if (ikRefinement == 7) continue;
      // printf("atoms: %d %d, comp %d\n", ijAtom, jkAtom, ikRefinement);
      //if (ikRefinement == 0) continue;
      ikRefinement = ikRefinement & ik;
      if (ikRefinement == ik) continue;
      
      clause.clear();
      clause.push_back(-1*(firstBoolVar[i*vc*2+j] + getAtomIndex(ij, ijAtom) - 1));
      clause.push_back(-1*(firstBoolVar[j*vc*2+k] + getAtomIndex(jk, jkAtom) - 1));
      
      /*if ((firstBoolVar[j*vc*2+k] + getAtomIndex(jk, jkAtom) - 1) == 0){
        printf("ERROR between %d %d, index %d!\n",j,k,getAtomIndex(jk,jkAtom));
	exit(0);
      }*/
      
      for (ikAtom=1; ikAtom<7; ikAtom = ikAtom << 1){
        if ((ikAtom & ikRefinement) == 0) continue;
	clause.push_back(firstBoolVar[i*vc*2+k] + getAtomIndex(ik, ikAtom) - 1);
      }
      clauses.push_back(clause);
      sup++;
    }    
  }
  /*
  else if (ij >= ik && ij >=  jk)
  for (ikAtom = 1; ikAtom < 8191; ikAtom = ikAtom << 1){
    if ((ikAtom & ik) == 0) continue;
    
    for (kjAtom = 1; kjAtom < 8191; kjAtom = kjAtom << 1){
      if ((kjAtom & inverse(jk))==0) continue;
      
      ijRefinement = pa_composition(ikAtom, kjAtom);
      
      if (ijRefinement == 7) continue;
      // printf("atoms: %d %d, comp %d\n", ijAtom, jkAtom, ikRefinement);
      //if (ikRefinement == 0) continue;
      ijRefinement = ijRefinement & ij;
      if (ijRefinement == ij) continue;
      
      clause.clear();
      clause.push_back(-1*(firstBoolVar[i*vc*2+k] + getAtomIndex(ik, ikAtom) - 1));
      clause.push_back(-1*(firstBoolVar[j*vc*2+k] + getAtomIndex(jk, inverse(kjAtom)) - 1));
      
      for (ijAtom=1; ijAtom<7; ijAtom = ijAtom << 1){
        if ((ijAtom & ijRefinement) == 0) continue;
	clause.push_back(firstBoolVar[i*vc*2+j] + getAtomIndex(ij, ijAtom) - 1);
      }
      clauses.push_back(clause);
      sup++;
    }    
  }  
  
  else if (jk >= ij && jk >= ik) // ji - ik
  
  for (jiAtom = 1; jiAtom < 8191; jiAtom = jiAtom << 1){
    if ((jiAtom & inverse(ij)) == 0) continue;
    
    for (ikAtom = 1; ikAtom < 8191; ikAtom = ikAtom << 1){
      if ((ikAtom & ik) == 0) continue;
      
      jkRefinement = pa_composition(jiAtom, ikAtom);
      
      if (jkRefinement == 7) continue;
      
      jkRefinement = jk  & jkRefinement;
      
      if (jkRefinement == jk) continue;
      clause.clear();
      clause.push_back(-1*(firstBoolVar[i*vc*2+j] + getAtomIndex(ij, inverse(jiAtom))));
      clause.push_back(-1*(firstBoolVar[i*vc*2+k] + getAtomIndex(ik, ikAtom)));
      
      for (jkAtom = 1; jkAtom<8191; jkAtom = jkAtom << 1){
        if ((jkAtom & jkRefinement) == 0) continue;
	clause.push_back(firstBoolVar[j*vc*2+k] + getAtomIndex(jk, jkAtom) - 1);
      }
      clauses.push_back(clause);
      sup++;
    }
  }
  else{
    printf("ERROR\n");
    exit(0);
  }
    */
  return sup;  
}

void Csp::encodeTriangles(int *nodes, unsigned size){

  RELTYPE rij, rik, rjk, ij, jk, ikRels, ik=0;
  vector<int> clause;
  unsigned ijIndex, jkIndex, ikIndex, ijVar, jkVar, ikVar, ikSize;
  unsigned i,j,k,ii,jj,kk; 


  PR(FILE *myf = fopen("new.cnf", "a");)
  PR(assert(myf);)
  /*// printf("Encoding triangles\n");
  */
  /*  bool p90p=false, p80p=false, p70p=false, p60p=false, p50p=false,
         p40p=false, p30p=false, p20p=false, p10p=false;
  
  printf("0 percent done, %d clauses, %d nodes\n", clauses.size(), size);
  */
  unsigned iMark, iIndex, jMark, jIndex, kMark, kIndex;
  
  // Encoding domain constraints
  for (ii=0; ii<size; ii++){
    i = nodes[ii];
    for (jj=ii+1; jj<size; jj++){
      j = nodes[jj];
      bool alreadyEncoded = false;
      for( vector <set<int> >::iterator iter_i = sharedIANodes.begin();
       	     iter_i < sharedIANodes.end(); ++iter_i) {
        if ((*iter_i).find(i) != (*iter_i).end() ){
	  if ((*iter_i).find(j) != (*iter_i).end() ){
	    alreadyEncoded = true;
	    break;
	  }
	}	     	  	    
      }
      if (alreadyEncoded) continue;      

      // identify relation between i and jth node
      rij = cspArray[i*vc+j];
      
      // set domain-size of the relation
      domainSize[i*vc+j] = countAtoms(rij);
      
      // set index of the first boolean variable for the edge
      firstBoolVar[i*vc+j] = maxBoolVar;
      maxBoolVar += domainSize[i*vc+j];
      
      // encode constraint for edge
      
      // at least one of the atoms are true AMO
      clause.clear();      
      for (ijIndex = 0; ijIndex <domainSize[i*vc+j]; ijIndex++){
	clause.push_back(firstBoolVar[i*vc+j] + ijIndex);  
	PR(fprintf(myf, "%d ", firstBoolVar[i*vc+j]+ijIndex);)
      } // endfor ijIndex      
      
      // add ALO clause to CNF
      NPR(clauses.push_back(clause);          )
      
      PR(fprintf(myf, "0\n");)
      clauseCount++;

      // At most one of the atoms can be true (AMO)            
      if (domainSize[i*vc+j] == 1){        
	// covered by ALO	
	;
      } 
      else for (unsigned ii = 0; ii < domainSize[i*vc+j]; ii++){
        for (unsigned jj = ii + 1; jj < domainSize[i*vc+j]; jj++){
	  clause.clear();
	  clause.push_back(-1*(firstBoolVar[i*vc+j]+ii));
	  clause.push_back(-1*(firstBoolVar[i*vc+j]+jj));	  
	  
	  PR(fprintf(myf, "%d ", -1*(firstBoolVar[i*vc+j]+ii));)
	  PR(fprintf(myf, "%d ", -1*(firstBoolVar[i*vc+j]+jj));)
	  PR(fprintf(myf, "0\n");)
	  clauseCount++;
	  NPR(clauses.push_back(clause);)
	} // endfor jj
      }  // endfor ii          
      
      // AMO set


    }
  }
  
  
  // Encoding transivity constraints

  for (ii=0; ii<size; ii++){
    /*
    if ((float)ii/ (float)size > 0.9 && !p90p){
      printf("90 percent done, %d clauses\n", clauses.size());
      p90p = true;
    }
    else if ((float)ii/ (float)size > 0.8 && !p80p){
     printf("80 percent done, %d clauses\n", clauses.size());
     p80p = true;
    }
    else if ((float)ii/ (float)size > 0.7 && !p70p){
     printf("70 percent done, %d clauses\n", clauses.size());
     p70p = true;
    }
    else if ((float)ii/ (float)size > 0.6 && !p60p){
     printf("60 percent done, %d clauses\n", clauses.size());
     p60p = true;
    }
    else if ((float)ii/ (float)size > 0.5 && !p50p){
     printf("50 percent done, %d clauses\n", clauses.size());
     p50p = true;
    }
    else if ((float)ii/ (float)size > 0.4 && !p40p){
     printf("40 percent done, %d clauses\n", clauses.size());
     p40p = true;
    }
    else if ((float)ii/ (float)size > 0.3 && !p30p){
     printf("30 percent done, %d clauses\n", clauses.size());
     p30p = true;
    }
    else if ((float)ii/ (float)size > 0.2 && !p20p){
     printf("20 percent done, %d clauses\n", clauses.size());
     p20p = true;
    }
    else if ((float)ii/ (float)size > 0.1 && !p10p){
     printf("10 percent done, %d clauses\n", clauses.size());
     p10p = true;
    }
    */
    i = nodes[ii];
    iMark = 0;
    iIndex = 1;
    
    for( vector <set<int> >::iterator iter_i = sharedIANodes.begin();
       	     iter_i < sharedIANodes.end(); ++iter_i) {
      if ((*iter_i).find(i) != (*iter_i).end() )	     
	iMark = iMark | iIndex;  
      iIndex = iIndex << 1;	    
    }    
    
    for (jj=ii+1; jj<size; jj++){
      j = nodes[jj];
      
      jMark = 0; jIndex = 1;
      if (iMark != 0)
      for( vector <set<int> >::iterator iter_j = sharedIANodes.begin();
       	     iter_j < sharedIANodes.end(); ++iter_j) {
        if ((*iter_j).find(j) != (*iter_j).end() )	     
	  jMark = (jMark | jIndex) & iMark;  
        jIndex = jIndex << 1;	    
      }
      
      for (kk=jj+1; kk<size; kk++){        
        
        k = nodes[kk];
	
	kMark = 0; kIndex = 1;
	if (jMark != 0)
	for( vector <set<int> >::iterator iter_k = sharedIANodes.begin();
       	     iter_k < sharedIANodes.end(); ++iter_k) {
          if ((*iter_k).find(k) != (*iter_k).end() )	     
	    kMark = (kMark | kIndex) & jMark;  
          kIndex = kIndex << 1;	    
        }
	
	if (kMark != 0) continue; // i,j,k already encoded

        rij = cspArray[i*vc+j];
	rjk = cspArray[j*vc+k];
	rik = cspArray[i*vc+k];

	// printf("%d %d %d\n",i,j,k);
	//printf("%d %d %d\n",rij,rjk,rik);

	// encode the transivity constraints
	for (ijIndex=1; ijIndex <= domainSize[i*vc+j]; ijIndex++){
	  for (jkIndex=1; jkIndex <= domainSize[j*vc+k]; jkIndex++){
	    
	    // encode the constraint
	    ij = getNthAtom(rij, ijIndex);
	    jk = getNthAtom(rjk, jkIndex);
	    ikRels = composition(ij,jk) & rik;	    
	    
	    // not ij OR not jk OR (rik INTERSECT ij comp jk)
	    ijVar = firstBoolVar[i*vc+j] + ijIndex - 1;
	    jkVar = firstBoolVar[j*vc+k] + jkIndex - 1;
	    
	    clause.clear();
	    clause.push_back(-1*ijVar);
	    clause.push_back(-1*jkVar);
	    
	    PR(fprintf(myf, "%d %d ", -1*ijVar, -1*jkVar);)
	    
	    ikSize = countAtoms(ikRels);
	    
	    for (ikIndex=1; ikIndex <= ikSize; ikIndex++){
	      ik = getNthAtom(ikRels,ikIndex);
	      ikVar = firstBoolVar[i*vc+k] + getAtomIndex(rik, ik) - 1;
	      clause.push_back(ikVar);  
	      PR(fprintf(myf, "%d ", ikVar);)
	    }
	    PR(fprintf(myf, "0\n");)
	    clauseCount++;
	    NPR(clauses.push_back(clause);)
	  }
	}
	
      }
    }
  }
  PR(fclose(myf));
}

// revise in path consistency
bool Csp::revise(RELTYPE *rel, unsigned size, unsigned i, unsigned k, unsigned j, bool usePA){
    int oldR;

    /** assign oldR */
    oldR = *(rel+i*size+j);

    /** Getting new value */
    if (!usePA)
    *(rel+i*size+j) =
    	(*(rel+i*size+j) & (composition(*(rel+i*size+k),*(rel+k*size+j))));
    else
    *(rel+i*size+j) =
    	(*(rel+i*size+j) & (pa_composition(*(rel+i*size+k),*(rel+k*size+j))));

    /** new value found, comparing */
    if (oldR == *(rel+i*size+j)) {
	/** nothing changed, returning */
    	return 0;
    }

    /** Value changed, inverting opposite */
    *(rel+j*size+i) = inverse(*(rel+i*size+j));

    return 1;
}


bool Csp::makePathConsistent(void){
  // printf("enforcing path consistency\n");
  return pathConsistency(cspArray, vc, false);
}

bool Csp::makePathConsistentPA(void){
  // printf("enforcing PA path-consistency\n");
  return (pathConsistency(cspArrayPA, vc*2, true));
}

// path-consistency
bool Csp::pathConsistency(RELTYPE *rel, unsigned size, bool usePA){
    unsigned i,j,k,change;

    change = 1;
    
    while (change){
        change = 0;
	for (i=0; i<size; i++){
	    for (j=i+1; j<size; j++){
	        for (k=0; k<size; k++){
		    if (k==i || k==j) continue;
		    if (revise(rel,size,i,j,k, usePA)){
		        if (*(rel+i*size+k)==0) {
	 	    	    return false;
	    		}
			change = 1;
		    }
		    if (revise(rel,size,k,i,j, usePA)){
		        if (*(rel+k*size+j)==0) {	    	
	 	    	    return 0;
	    		}
			change = 1;
		    }
		}
	    }
	}
    }
    return true;
}

// encode all the triangles naively
void Csp::lookAllTriangles(void){

  // prepareHmetis();
    
  // checking
  // vector< vector<int> > clauses;
    
  RELTYPE rij, rik, rjk, ij, jk, ikRels, ik=0;
  unsigned ijIndex, jkIndex, ikIndex, ijVar, jkVar, ikVar, ikSize;
  vector<int> clause;


  maxBoolVar = 1;

  
  // perform path-consistency first    
  if  (!makePathConsistent()){
    // printf("path-inconsistent!\n");
    vector<int> clause;
    clause.push_back(1);    
    clauses.push_back(clause);
    
    clause.clear();
    clause.push_back(-1);
    clauses.push_back(clause);
    maxBoolVar++;
    return;
  }
  // encode the domain values
  
  printf("adding domain clauses\n");
    
  
  for (unsigned i=0; i<vc; i++){
    for (unsigned j=i+1; j<vc; j++){
      
      rij = cspArray[i*vc+j];
      domainSize[i*vc+j] = countAtoms(rij);
      firstBoolVar[i*vc+j] = maxBoolVar;
      maxBoolVar += domainSize[i*vc+j];
      
      // encode constraint for edge
      
      // at least one of the atoms are true
      //printf("asserting ALO\n");
      clause.clear();      
      for (ijIndex = 0; ijIndex <domainSize[i*vc+j]; ijIndex++){
	clause.push_back(firstBoolVar[i*vc+j] + ijIndex);  
	//printf("%d ", firstBoolVar[i*vc+j] + ijIndex);   
      } // endfor ijIndex
      //putchar('\n');
      clauses.push_back(clause);          

      // only one of the atoms can be true
      //printf("asserting AMO\n");
            
      if (domainSize[i*vc+j] == 1){        
	// covered by ALO	
	;
      } 
      else for (unsigned ii = 0; ii < domainSize[i*vc+j]; ii++){
        for (unsigned jj = ii + 1; jj < domainSize[i*vc+j]; jj++){
	  clause.clear();
	  clause.push_back(-1*(firstBoolVar[i*vc+j]+ii));
	  clause.push_back(-1*(firstBoolVar[i*vc+j]+jj));	  
	  clauses.push_back(clause);
	} // endfor jj
      }  // endfor ii          
    } // endfor j
  } // endfor i


  printf("adding transivity clause\n");
  
  for (unsigned i=0; i<vc; i++){
    for (unsigned j=i+1; j<vc; j++){
      for (unsigned k=j+1; k<vc; k++){   
      
        rij = cspArray[i*vc+j];
	rjk = cspArray[j*vc+k];     
	rik = cspArray[i*vc+k];
	
	// printf("%d %d %d\n",i,j,k);
	//printf("%d %d %d\n",rij,rjk,rik);

	// encode the transivity constraints
	for (ijIndex=1; ijIndex <= domainSize[i*vc+j]; ijIndex++){
	  for (jkIndex=1; jkIndex <= domainSize[j*vc+k]; jkIndex++){
	    
	    // encode the constraint
	    ij = getNthAtom(rij, ijIndex);
	    jk = getNthAtom(rjk, jkIndex);
	    ikRels = composition(ij,jk) & rik;	    
	    
	    // not ij OR not jk OR (rik INTERSECT ij comp jk)
	    ijVar = firstBoolVar[i*vc+j] + ijIndex - 1;
	    jkVar = firstBoolVar[j*vc+k] + jkIndex - 1;
	    
	    //if (ijVar==4 && jkVar == 26){
	    //  printf("%d %d %d, ijVar %d jkVar %d\n", ij, jk, ikRels, ijVar,
	    //   jkVar);
	    // }
	    
	    clause.clear();
	    clause.push_back(-1*ijVar);
	    clause.push_back(-1*jkVar);
	 
	    ikSize = countAtoms(ikRels);
	    
	    for (ikIndex=1; ikIndex <= ikSize; ikIndex++){
	      ik = getNthAtom(ikRels,ikIndex);
	      ikVar = firstBoolVar[i*vc+k] + getAtomIndex(rik, ik) - 1;
	      clause.push_back(ikVar);  
	    } // endfor ikIndex
	    clauses.push_back(clause);
	  } // endfor jkINdex
	} // endfor ijIndex		
      } // endfor k      
    } // endfor j     
  } // endfor i
  return;
}

void Csp::printCnf(void){

  
  maxBoolVar--;
  MDB(printf("printing to file %d variable, %d clauses\n", maxBoolVar, clauses.size());)

  // FILE *cnfFile = fopen("allTriangles.cnf", "w");
  /*if (cnfFile == NULL) {
    fprintf(stderr, "cannot create new file for all triangles\n");
    exit(0);
  }*/
  
  if (unsat){
    // printf("UNSATISFIABLE CSP\n");
    // fprintf(cnfFile, "p uncnf\n");
    printf("p cnf 1 2\n1 0\n-1 0\n");
  }
  
  // fprintf(cnfFile, "p cnf %d %d\n", maxBoolVar, clauses.size());
  printf("p cnf %d %d\n", maxBoolVar, clauses.size());
  
  for (unsigned i=0; i<clauses.size(); i++){
    for (unsigned j=0; j<clauses[i].size(); j++){
      // fprintf(cnfFile, "%d ", clauses[i][j]);
      printf("%d ", clauses[i][j]);
    }
    // fprintf(cnfFile, "0\n");
    printf("0\n");
  }
  
  // fclose(cnfFile);
  
  MDB(printf("done!\n");)
}

void Csp::verifySatSol(void){
  RELTYPE *newCspArray = (RELTYPE *) malloc (vc*vc*sizeof(RELTYPE));
  assert(newCspArray);
  
  FILE *solFile = fopen("triangle.sol", "r");
  assert(solFile);
  
  unsigned i,j,k;
  int var;
  
  FILE *cspFile = fopen("check.csp", "w");
  
  char *cspStr = (char *) malloc (200*sizeof(char));
  
  for (i=0; i<vc; i++){    
    for (j=i+1; j<vc; j++){
      bool found = false;
      for (k=0; k<domainSize[i*vc+j]; k++){
        fscanf(solFile, "%d ", &var);
	if (var < 0) continue;
	if (found){
	  printf("AMO violated for edge %d %d, not found\n", i,j);
          exit(0);    
	}
	found = true;
	
	if ((unsigned) var < firstBoolVar[i*vc+j] || 
	    (unsigned) var >= firstBoolVar[i*vc+j] + domainSize[i*vc+j]){
	  printf("var %d not in range for edge %d %d, not found\n", var, i,j);	  
          exit(0);    
	}
	newCspArray[i*vc+j] = getNthAtom(cspArray[i*vc+j], k+1);
	newCspArray[j*vc+i] = inverse(getNthAtom(cspArray[i*vc+j], k+1));
	
	// clean string
	for (unsigned l=0; l<200; l++){
	  cspStr[l] = '\0';
	}
	
	cspStr = sprcons(cspStr, newCspArray[i*vc+j], i,j);
	fprintf(cspFile, "%s\n", cspStr);
	    
	// printf("edge %d %d, %d\n", i,j,newCspArray[i*vc+j]);
      }
      if (!found){
        printf("atomic refinement for edge %d %d not found\n", i,j);
        exit(0);
      }     
    }  // endfor j  
  } // endfor i
  printf("all atomic refinements found\n");
  
  if (!pathConsistency(newCspArray, vc, false))
    printf("atomic refinement not PC\n");    
  else
    printf("solution verified\n");

}
