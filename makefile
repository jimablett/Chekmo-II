# Makefile for CHEKMO-II
# ANSI C Chess Program with WinBoard Protocol

CC = clang
CFLAGS =  -Wall -Ofast -flto=auto -std=c99 -D_GNU_SOURCE -static -s -w -msse3 -mssse3 -march=k8 -mtune=k8
CFLAGS += -ftree-vectorize -funroll-loops -ffast-math -finline-functions -pipe 
CFLAGS += -funsafe-math-optimizations -fno-exceptions
LDFLAGS = -lm

TARGET = chekmo
SOURCES = chekmo.c
OBJECTS = $(SOURCES:.c=.o)


#   -fprofile-instr-generate -fcoverage-mapping                                                            
#    llvm-profdata merge -output=default.profdata *.profraw                                               
#   -fprofile-use=default.profdata                                                                       


.PHONY: all clean distclean install debug test help

all: $(TARGET)

$(TARGET): $(OBJECTS)
	$(CC) $(CFLAGS) -o $@ $^ $(LDFLAGS)

%.o: %.c
	$(CC) $(CFLAGS) -c $< -o $@

debug:
	$(CC) -Wall -g -std=c99 -DDEBUG -o $(TARGET) $(SOURCES) $(LDFLAGS)

test: $(TARGET)
	./$(TARGET)

winboard: $(TARGET)
	./$(TARGET) -xboard

install: $(TARGET)
	cp $(TARGET) /usr/local/bin/

clean:
	rm -f $(OBJECTS) $(TARGET)

distclean: clean
	rm -f *~ *.bak

profile: CFLAGS += -pg
profile: $(TARGET)

small: CFLAGS = -Os -std=c99 -s
small: $(TARGET)

help:
	@echo ""
	@echo "CHEKMO-II Makefile"
	@echo "=================="
	@echo ""
	@echo "Targets:"
	@echo "  make          - Build the program"
	@echo "  make debug    - Build with debug symbols"
	@echo "  make test     - Run the program in console mode"
	@echo "  make winboard - Run the program in WinBoard mode"
	@echo "  make install  - Install to /usr/local/bin"
	@echo "  make clean    - Remove object files and executable"
	@echo "  make profile  - Build with profiling support"
	@echo "  make small    - Build for minimal size"
	@echo ""
	@echo "Console Commands (short / long):"
	@echo "  PW / white      - Computer plays white"
	@echo "  PB / black      - Computer plays black"
	@echo "  PN / neither    - Computer plays neither"
	@echo "  BD / board      - Display board"
	@echo "  IP / input      - Input position (Forsyth)"
	@echo "  RE / reset      - Reset/Resign (new game)"
	@echo "  MV / move       - Force computer to move"
	@echo "  SK / skip       - Skip a move"
	@echo "  BM / blitz      - Blitz mode (faster)"
	@echo "  TM / tournament - Tournament mode (stronger)"
	@echo "  HELP / ?        - Show help"
	@echo "  QUIT / exit     - Exit program"
	@echo ""
	@echo "Move Formats:"
	@echo "  e2e4   - Long algebraic"
	@echo "  Nf3    - Short algebraic"
	@echo "  e4     - Pawn move"
	@echo "  exd5   - Pawn capture"
	@echo "  O-O    - King side castling"
	@echo "  O-O-O  - Queen side castling"
	@echo "  e7e8q  - Promotion"
	@echo ""