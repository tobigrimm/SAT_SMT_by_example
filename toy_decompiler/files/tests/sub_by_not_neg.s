; arg1-2
;Found a 4-operation program:
;   neg   r1,rx
;   not   r2,r1
;   neg   r3,r2
;   not   r4,r3
;   Expr: ~(-(~(-(x))))

        mov     rax, rdi
        neg     rax
        not     rax
        neg     rax
        not     rax

