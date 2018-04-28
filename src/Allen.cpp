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

/* Allen.h  */
/* Modified from original allen.c from Professor B. Nebel */
/* Original downloadable from  */
/* http://www.informatik.uni-freiburg.de/~ki/papers/allen-csp-solving.programs.tar.gz */

#include <stdio.h>
#include <stdlib.h>
#include <ctype.h>
#include <string.h>
#include "Allen.h"
#include "AllenComp.h"


// Compute composition of two relations
RELTYPE composition(RELTYPE r1, RELTYPE r2){
  RELTYPE result;
  register RELTYPE x1;
  register RELTYPE x2;
  
  result = 0;
  for (x1 = 0; x1 < MAXREL; x1++) 
    if ((r1>>x1)&1)
      for (x2 = 0; x2 < MAXREL; x2++) 
	if ((r2>>x2)&1)
	  result |= comp[x1][x2];
  return(result);
}


// get the relation of end points for a given Allen relation
RELTYPE getEndPointLiteral(RELTYPE rel, unsigned i){
  unsigned k=0;
  for (unsigned j=1; i<DALL; j=j<<1){    
    if ((j&rel) != 0) break;
    k++;
  }
  // printf("\n%d-%d\n", k, endPointLiteral[k-1][i]);
  return(endPointLiteral[k][i]);
}

// Compute composition of two pa_relations
RELTYPE pa_composition(RELTYPE r1, RELTYPE r2){
  RELTYPE result;
  register RELTYPE x1;
  register RELTYPE x2;
  
  result = 0;
  for (x1 = 0; x1 < PA_MAXREL; x1++) 
    if ((r1>>x1)&1)
      for (x2 = 0; x2 < PA_MAXREL; x2++) 
	if ((r2>>x2)&1)
	  result |= pa_comp[x1][x2];
  return(result);
}

// Compute inverse of a relation
RELTYPE inverse(RELTYPE r){
  return(((r&REQ) ? REQ : 0) |
	 ((r&RLT) ? RGT : 0) |
	 ((r&RGT) ? RLT : 0) |
	 ((r&RD)  ? RDI : 0) |
	 ((r&RDI) ? RD  : 0) |
	 ((r&RO)  ? ROI : 0) |
	 ((r&ROI) ? RO  : 0) |
	 ((r&RM)  ? RMI : 0) |
	 ((r&RMI) ? RM  : 0) |
	 ((r&RS)  ? RSI : 0) |
	 ((r&RSI) ? RS  : 0) |
	 ((r&RF)  ? RFI : 0) |
	 ((r&RFI) ? RF  : 0));
}

// Return the nth atom of a relation
RELTYPE getNthAtom(RELTYPE r, unsigned n){
  unsigned myN = 0;
  for (RELTYPE i = 1; i < DALL; i = i << 1){
    if ((i & r) != 0){
      myN++;
      if (myN == n){
        return i;
      }
    }
  }
  return 0; // nth atom not found 
}

// check if an atom is forbidden in a PA encoding
bool isForbidden(unsigned ss, unsigned se, 
                 unsigned es, unsigned ee, RELTYPE atom){
  if ((getEndPointLiteral(atom, 0) & ss) != 0)
    if ((getEndPointLiteral(atom, 1) & se) != 0)
      if ((getEndPointLiteral(atom, 2) & es) != 0)
        if ((getEndPointLiteral(atom, 3) & ee) != 0)
          return true;
  return false; 
}

// count number of atoms in a relation
unsigned countAtoms(RELTYPE r){
  unsigned myN = 0;
  for (RELTYPE i = 1; i < DALL; i = i << 1)
    if ((i & r) != 0) myN++;
        
  return myN; 
}

unsigned getAtomIndex(RELTYPE r, RELTYPE atom){
  unsigned myN = 0;
  for (RELTYPE i = 1; i < DALL; i = i << 1)
    if ((i & r) != 0){ 
      myN++;
      if (i == atom) return myN;
    }
  return 0; // index not found
}

// Compute value of a relation (See Nebel)
int relvalue(RELTYPE r){

  register int bytecnt;
  register int tempval;

  bytecnt = 0;
  tempval = 0;
  if (r & REQ) {
    bytecnt++;
    tempval += 1;
  }
  if (r & RGT) {
    bytecnt++;
    tempval += 3;
  }
  if (r & RLT) {
    bytecnt++;
    tempval += 3;
  }
  if (r & RD) {
    bytecnt++;
    tempval += 4;
  }
  if (r & RDI) {
    bytecnt++;
    tempval += 3;
  }
  if (r & RO) {
    bytecnt++;
    tempval += 4;
  }
  if (r & ROI) {
    bytecnt++;
    tempval += 4;
  }
  if (r & RM) {
    bytecnt++;
    tempval += 2;
  }
  if (r & RMI) {
    bytecnt++;
    tempval += 2;
  }
  if (r & RS) {
    bytecnt++;
    tempval += 2;
  }
  if (r & RSI) {
    bytecnt++;
    tempval += 2;
  }
  if (r & RF) {
    bytecnt++;
    tempval += 2;
  }
  if (r & RFI) {
    bytecnt++;
    tempval += 2;
  }
  return(tempval);
}

// print rel to string
char *sprrel(char *s, RELTYPE r){
  *s = '\0';
  strcat(s,"( ");
  if (r&REQ)
    strcat(s,"= ");
  if (r&RLT)
    strcat(s,"< ");
  if (r&RGT)
    strcat(s,"> ");
  if (r&RD)
    strcat(s,"d ");
  if (r&RDI)
    strcat(s,"di ");
  if (r&RO)
    strcat(s,"o ");
  if (r&ROI)
    strcat(s,"oi ");
  if (r&RM)
    strcat(s,"m ");
  if (r&RMI)
    strcat(s,"mi ");
  if (r&RS)
    strcat(s,"s ");
  if (r&RSI)
    strcat(s,"si ");
  if (r&RF)
    strcat(s,"f ");
  if (r&RFI)
    strcat(s,"fi ");
  strcat(s,")");
  return(s);
}

// print constraint to a string
char *sprcons(char *s, RELTYPE r, unsigned node1, unsigned node2)
{
  char relstr[100];
  sprintf(s,"%2d %2d ",node1,node2);
  sprrel(relstr,r);
  strcat(s,relstr);
  return s;
}

// parse a relation from a string
bool parserel(char *line, RELTYPE *r)
{
  RELTYPE result;
  char *oldline;
  
  oldline = line;
  result = 0;

  // Reading relation between ( )
  while ((*line != '\0') && (*line != '(')) line++;
  if (*(line++) != '(') {
    fprintf(stderr,"\n*** no '(' in rel spec: '%s'\n",oldline);
    return(false);
  }
  while (*line == ' ') line++;
  while ((*line != ')' ) && *line) {
    while (*line == ' ') line++;
    switch (*(line++)) {
    case '=' : result |= REQ; break;
    case '<' : result |= RLT; break;
    case '>' : result |= RGT; break;
    case 'd' : if (*line == 'i') {
      result |= RDI; line++;
    } else result |= RD;
      break;
    case 'o' : if (*line == 'i') {
      result |= ROI; line++;
    } else result |= RO;
      break;
    case 'm' : if (*line == 'i') {
      result |= RMI; line++;
    } else result |= RM;
      break;
    case 's' : if (*line == 'i') {
      result |= RSI; line++;
    } else result |= RS;
      break;
    case 'f' : if (*line == 'i') {
      result |= RFI; line++;
    } else result |= RF;
      break;
      default : fprintf(stderr,"\n*** Illegal rel spec: '%s'\n",oldline);
      return(false);
    }
    while (*line == ' ') line++;
  }
  if (*line != ')') {
    fprintf(stderr,"\n*** Missing ')' in rel spec in '%s'\n",oldline);
    return(false);
  }
  *r = result;
  return(true);
}

// Parsing a constraint from a string
bool parsecons(char *line, RELTYPE *r, unsigned *node1, unsigned *node2)
{
  // Reading two vertices
  if (sscanf(line,"%d %d",node1,node2) != 2) {
    fprintf(stderr,"\n*** no node ids in rel spec: '%s'\n",line);
    return(false);
  }

  // Read the relation
  return(parserel(line, r));
}
