CC = g++ -Wall -O3 -DNDEBUG
HEADERS = Csp.h Allen.h 
OBJS = Csp.o Allen.o main.o

ia2sat: $(OBJS) 
	$(CC) $(OBJS) -o ia2sat ./libhmetis.a

$(OBJS): $(HEADERS) Makefile

.cpp.o: 
	$(CC) -c $< 
