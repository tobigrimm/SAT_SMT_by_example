; tested with MK85 and Z3

(set-logic QF_BV)
(set-info :smt-lib-version 2.0)

(declare-fun x () (_ BitVec 32))
(declare-fun n () (_ BitVec 32))
(declare-fun result1 () (_ BitVec 32))
(declare-fun result2 () (_ BitVec 32))

(assert (bvule n (_ bv31 32)))

(assert (= result1 (bvashr x n)))

; ((x+0x80000000) >>u n) - (0x80000000 >>u n)
(assert (= result2
	(bvsub
		(bvlshr (bvadd x #x80000000) n)
		(bvlshr #x80000000 n)
	)
))

(assert (distinct result1 result2))

; must be unsat:
(check-sat)

