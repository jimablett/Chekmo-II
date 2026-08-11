# Chekmo-II
CHEKMO-II, (CheckMo-II) the classical chess program for the PDP-8, written in the 70s by Digital Equipment Corporation instructor  John E. Comeau in PAL-8, the PDP-8 assembly. Ported to modern systems


Official description

CHEKMO-II, (CheckMo-II) the classical chess program for the PDP-8, written in the 70s by Digital Equipment Corporation instructor 
John E. Comeau in PAL-8, the PDP-8 assembly.

CHEKMO II is a chess playing program which will run on any PDP-8 family computer. The program will play either the white pieces or 
the black pieces, and will play and accept all classes of legal moves, including castling both short and long, en passant pawn captures, 
and pawn promoting moves to any legal promotion piece. The program prints out its moves m Algebraic Notation, and accepts moves using 
Algebraic Notation.



 * Converted to ANSI C with WinBoard Protocol
 * Enhanced evaluation and king safety
 * Ported by Jim Ablett (May/June 2026)
 
 
 
 Command Reference:

Short:	    Long:	             Description:

PW	        white	             Computer plays white
PB	        black	             Computer plays black
PN	        neither	             Computer plays neither (human vs human)
BD	        board or display	 Display the board
IP	        input	             Input position using Forsyth notation
RE	        reset or resign	     Reset/Resign - start new game
MV	        move	             Force computer to move
SK	        skip	             Skip a move (switch sides)
BM	        blitz	             Blitz mode (faster, weaker)
TM	        tournament	         Tournament mode (slower, stronger)
ST          <secs>               Set think time per move (default: 5)
HELP	    help or ?	         Show help screen
QUIT	    quit or exit	     Exit the program

Move Formats: e2e4, Nf3, exd5, O-O, e7e8q, etc.

Format:	                Example:           Description:

Long algebraic	        e2e4	           From square to square
Short algebraic	        Nf3	               Piece letter + target square
Pawn move	            e4	               Just target square
Pawn capture	        exd5	           File + 'x' + target square
King side castling	    O-O or 0-0	
Queen side castling	    O-O-O or 0-0-0	
Promotion	            e7e8q	           Add promotion piece letter
Capture with promotion	d7c8q



WinBoard Protocol Support

The program implements the following WinBoard commands:

xboard -               Identify as WinBoard engine

protover 2 -           Protocol version negotiation

new -                  Start new game

force -                Force mode (human controls both sides)

go -                   Computer plays its move

usermove -             User makes a move

setboard -             Set position using FEN

white / black -        Set computer's side

analyze -              Analysis mode

quit -                 Exit

resign -               Resign the game


 
 
 
 
