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
/* Modified from original allen.h from Professor B. Nebel */

#ifndef _ALLEN
#define _ALLEN

#define RELTYPE short int /* at least 2 bytes! */
#define RELTYPESIZE sizeof(RELTYPE)



  RELTYPE getEndPointLiteral(RELTYPE rel, unsigned i);


  // Compute composition of two relations
  RELTYPE composition(RELTYPE r1, RELTYPE r2);
  
  RELTYPE pa_composition(RELTYPE r1, RELTYPE r2);

  // Compute inverse of a relation
  RELTYPE inverse(RELTYPE r);

  // Compute value of a relation (See Nebel)
  int relvalue(RELTYPE r);

  // print rel to string
  char *sprrel(char *s, RELTYPE r);
  
  // print constraint to string
  char *sprcons(char *s, RELTYPE r, unsigned node1, unsigned node2);

  // parse relation from a string
  bool parserel(char *line, RELTYPE *r);

  // parse constraint from a string
  bool parsecons(char *line, RELTYPE *r, unsigned *node1, unsigned *node2) ;

  RELTYPE getNthAtom(RELTYPE r, unsigned n);
  
  unsigned countAtoms(RELTYPE r); 

  unsigned getAtomIndex(RELTYPE r, RELTYPE atom);

  bool isForbidden(unsigned ss, unsigned se, 
                 unsigned es, unsigned ee, RELTYPE atom);
#endif
