@i
M=0

@5
M=0

@START
0;JMP

(LOOP)
@i
D = M
@4
D = D - A
@END
D;JGT

@i
A = M
D = M
@CHECK_POSITIVE
D;JLE

@5
D = M
@SKIP_UPDATE
D;JEQ

@i
A = M
D = M
@5
D = D-M
@CHECK_MIN
D;JGE

@5
M = D

(SKIP_UPDATE)
@i
A = M
D = M
@5
M = D

(CHECK_POSITIVE)
@i
M = M + 1
@START
0;JMP

(END)
@END
0;JMP
