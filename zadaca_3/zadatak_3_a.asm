@10
D=A;
@R0
M=D;

@10
D=A;
@R1
M=D;

@R0
D=M;
@R1
D=M-D;

@skip
D;JGE

@R0
D=M;
@tmp
M=D;

@R1
D=M;
@R0
M=D;

@tmp
D=M;
@R1
M=D;

(skip)

@R2
M=0;

(start)
@R0
D=M;
@R1
D=M-D;

@end
D;JLT

@R0
D=M;
@R2
M=M+D;

@R0
M=M+1;

@start
0;JMP

(end)
@END
0;JMP
