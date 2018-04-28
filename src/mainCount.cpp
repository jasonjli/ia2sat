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


#define VERSION "0.22"
#include <stdio.h>
#include <stdlib.h>
#ifdef _MSC_VER
#include <ctime>
double _get_cpu_time(){ 
  return (double) clock() / CLOCKS_PER_SEC;
}
#else
#include <sys/time.h>
#include <sys/resource.h>
#include <unistd.h>

#include "Csp.h"


double _get_cpu_time(){ 
	struct rusage usage;
  	getrusage(RUSAGE_SELF, &usage);
  	return (usage.ru_utime.tv_usec + usage.ru_stime.tv_usec) * 
	(1e-6) + (usage.ru_utime.tv_sec + usage.ru_stime.tv_sec); 
}
#endif

int main(int argc, char **argv){

  if(argc < 2) {
    fprintf(stderr, "Usage: ./ia2sat [-pt] file.csp\n");
    exit(0);
  }
  double _start_time = _get_cpu_time();
  double _start_encode;
  
  bool encodePt=false;
  
  encodePt = (argc > 2);
  
  FILE *ifp;
  if ((ifp = fopen(argv[argc-1], "r")) == NULL){
    fprintf(stderr, "Cannot open file: %s\n", argv[1]);
    exit(0);
  }
  
  // Read Csp Header Information
  unsigned tmpCount, cspCount, vc;
  
  char line[128],c;
  size_t len = 128;

  while ((c=getc(ifp)) != EOF){
    
    if (isspace(c)) continue; else ungetc(c,ifp);
    
    fgets(line, len, ifp);
  
    if (sscanf(line, "%d #%d-N%d", 
  	&tmpCount, &cspCount, &vc) != 3){
      printf("Invalid CSP\n");
      return 0;
    }
    // printf("%s", line);
    
    Csp *csp = new Csp(ifp, vc, encodePt);
  
    // checking 
    // printf("c %d variables, %d constraints\n", csp->vc, csp->ec);
    // printf("c read in %.2fs\n", _get_cpu_time() - _start_time);
    // printf("a %d\n", (*csp).edgeLabels[0]);    
    _start_encode = _get_cpu_time();  
    
     (*csp).doTwo();
    
    //(*csp).lookAllTriangles();
    printf("%d %d %.2fs\n", (*csp).maxBoolVar-1, (*csp).clauses.size(), _get_cpu_time() - _start_encode);
    // printf("c encoded in %.2fs\n", _get_cpu_time() - _start_encode);
    // (*csp).printCnf();
    
  }
  
  fclose(ifp);
  
  
  
  // printf("finished\n");    
  //printf("total %.2fs\n", _get_cpu_time() - _start_time);
  return 0;
}
