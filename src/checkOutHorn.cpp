#include <stdio.h>
#include <stdlib.h>
#include <limits.h>

#include "Allen.h"
#include "Csp.h"

#define BITMASK(b) (1 << ((b) % CHAR_BIT))
#define BITSLOT(b) ((b) / CHAR_BIT)
#define BITSET(a,b) ((a)[BITSLOT(b)] |= BITMASK(b))
#define BITCLEAR(a,b) ((a)[BITSLOT(b)] &= ~BITMASK(b))
#define BITTEST(a,b) ((a)[BITSLOT(b)] & BITMASK(b))
#define BITNSLOTS(nb) ((nb + CHAR_BIT - 1) / CHAR_BIT)

char *readOrdHorn(void){
    char *c;
    const char *ordHornFile = "hornalg", *rmode = "r";
    char line[100];
    FILE *fp;
    RELTYPE i; int size;
   
    c = (char *)malloc(BITNSLOTS(8191)*sizeof(char));
    if (c == NULL){
    	printf("OUT OF MEMORY AT GETTING CLOSURE\n");
	return 0;
    }
    for (i=1; i<=8191; i++){
        BITCLEAR(c,i);
    }
    
    fp = fopen(ordHornFile, rmode);
    if (fp==NULL) return NULL;
    
    size = 0;
    while (fgets(line,100,fp)) {
        if ((line[0] == '.') || (line[0] == '\0')) break;
        if (!parserel(line, &i)){
	  fprintf(stderr, "Cannot parse horn constraint\n");
	  exit(0);
	}
    	if (i > 0) {
      	    BITSET(c, i);
            size++;
        } 
    }    
    
    fclose(fp);
        

    return c;  
}


int checkOutHorn(Csp *csp){

  char *ordHorn;
  ordHorn = readOrdHorn();
  
  if (ordHorn==NULL) {
    printf("Horn not read\n");
    exit(0);
  }  
       
  unsigned init=0, afterPC=0;
  unsigned ec = csp->ec;
  unsigned vc = csp->vc;
  
  RELTYPE *edgeLabels = csp->edgeLabels;
  RELTYPE *cspArray = csp->cspArray;
  
  //printf("count init\n");
  
  for (unsigned i=0; i<ec; i++){    
    // printf("%d\n", edgeLabels[i]);
    if (!BITTEST(ordHorn, edgeLabels[i]))
      init++;    
  }
  
  if (!(*csp).makePathConsistent()){
    fprintf(stderr, "NOT PC!\n");
    exit(0);
  }
    
  for (unsigned i=0; i<vc-1; i++)
    for (unsigned j=i+1; j<vc; j++)
      if (!BITTEST(ordHorn, cspArray[i*vc+j]))
        afterPC++;
    
  printf("%d %d\n", init, afterPC);
  
  return 0;
}

int main(int argc, char **argv){
  if(argc < 2) {
    fprintf(stderr, "Usage: ./checkOutHorn file.csp\n");
    exit(0);
  }
  // printf("c reading %s\n", argv[argc-1]);
  
  FILE *ifp;
  if ((ifp = fopen(argv[argc-1], "r")) == NULL){
    fprintf(stderr, "Cannot open file: %s\n", argv[1]);
    exit(0);
  }  
  
  char line[128],c;
  size_t len = 128;
  
  int tmpCount, cspCount, vc;

  while ((c=getc(ifp)) != EOF){
    
    if (isspace(c)) continue; else ungetc(c,ifp);
    
    fgets(line, len, ifp);
  
    if (sscanf(line, "%d #%d-N%d", 
  	&tmpCount, &cspCount, &vc) != 3){
      printf("Invalid CSP\n");
      return 0;
    }
    
    Csp *csp = new Csp(ifp, vc, false);
    
    checkOutHorn(csp);  
  }
  
  fclose(ifp);
  return 0;  
}
