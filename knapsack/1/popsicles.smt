; tested with MK85 and Z3

(declare-fun box1pop () (_ BitVec 16))
(declare-fun box3pop () (_ BitVec 16))
(declare-fun box5pop () (_ BitVec 16))
(declare-fun pop_total () (_ BitVec 16))
(declare-fun cost_total () (_ BitVec 16))

(assert (=
	((_ zero_extend 16) pop_total)
	(bvadd 
		((_ zero_extend 16) box1pop)
		(bvmul ((_ zero_extend 16) box3pop) #x00000003)
		(bvmul ((_ zero_extend 16) box5pop) #x00000005)
	)))

(assert (=
	((_ zero_extend 16) cost_total)
	(bvadd
		((_ zero_extend 16) box1pop)
		(bvmul ((_ zero_extend 16) box3pop) #x00000002)
		(bvmul ((_ zero_extend 16) box5pop) #x00000003)
	)))

(assert (= cost_total #x0008))

(maximize pop_total)

(check-sat)
(get-model)

; correct solution:

;(model
;        (define-fun box1pop () (_ BitVec 16) (_ bv0 16)) ; 0x0
;        (define-fun box3pop () (_ BitVec 16) (_ bv1 16)) ; 0x1
;        (define-fun box5pop () (_ BitVec 16) (_ bv2 16)) ; 0x2
;        (define-fun pop_total () (_ BitVec 16) (_ bv13 16)) ; 0xd
;        (define-fun cost_total () (_ BitVec 16) (_ bv8 16)) ; 0x8
;)

