@32767
D = A
@5
M = D

@0
D = A
@12
M = D

(LP)
@14
D = M
@5
D = D-A
@ED
D; JGE

@14
D = M
@0
A = A+D
D = M

@SK
D; JLE

@5
A = M
D = D-A
@SK
D; JGE

@14
D = M
@0
A = A+D
D = M
@5
M = D

(SK)
@14
M = M+1
@LP
0; JMP
(ED)
0; JMP
