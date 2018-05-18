; tested with MK85

(set-logic QF_BV)
(declare-fun x () (_ BitVec 32))
(declare-fun y () (_ BitVec 4))
(declare-fun out () (_ BitVec 32))

; like switch() or if() tree:
(assert (= out
	(ite (= y #x2) (bvmul_no_overflow x x)
	(ite (= y #x3) (bvmul_no_overflow x x x)
	(ite (= y #x4) (bvmul_no_overflow x x x x)
	(ite (= y #x5) (bvmul_no_overflow x x x x x)
	(ite (= y #x6) (bvmul_no_overflow x x x x x x)
	(ite (= y #x7) (bvmul_no_overflow x x x x x x x)
	(_ bv0 32)))))))))

(assert (= out (_ bv19487171 32)))

(check-sat)
(get-model)

