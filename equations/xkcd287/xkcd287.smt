; tested using MK85

(set-logic QF_BV)
(set-info :smt-lib-version 2.0)

(declare-fun a () (_ BitVec 16))
(declare-fun b () (_ BitVec 16))
(declare-fun c () (_ BitVec 16))
(declare-fun d () (_ BitVec 16))
(declare-fun e () (_ BitVec 16))
(declare-fun f () (_ BitVec 16))

(assert (bvult a #x0010))
(assert (bvult b #x0010))
(assert (bvult c #x0010))
(assert (bvult d #x0010))
(assert (bvult e #x0010))
(assert (bvult f #x0010))

(assert 
	(= 
		(bvadd
			(bvmul (_ bv215 16) a)
			(bvmul (_ bv275 16) b)
			(bvmul (_ bv335 16) c)
			(bvmul (_ bv355 16) d)
			(bvmul (_ bv420 16) e)
			(bvmul (_ bv580 16) f)
		)
		(_ bv1505 16)
	)
)

;(check-sat)
;(get-model)
(get-all-models)

; correct answer:

;(model
;        (define-fun a () (_ BitVec 16) (_ bv7 16)) ; 0x7
;        (define-fun b () (_ BitVec 16) (_ bv0 16)) ; 0x0
;        (define-fun c () (_ BitVec 16) (_ bv0 16)) ; 0x0
;        (define-fun d () (_ BitVec 16) (_ bv0 16)) ; 0x0
;        (define-fun e () (_ BitVec 16) (_ bv0 16)) ; 0x0
;        (define-fun f () (_ BitVec 16) (_ bv0 16)) ; 0x0
;)
;(model
;        (define-fun a () (_ BitVec 16) (_ bv1 16)) ; 0x1
;        (define-fun b () (_ BitVec 16) (_ bv0 16)) ; 0x0
;        (define-fun c () (_ BitVec 16) (_ bv0 16)) ; 0x0
;        (define-fun d () (_ BitVec 16) (_ bv2 16)) ; 0x2
;        (define-fun e () (_ BitVec 16) (_ bv0 16)) ; 0x0
;        (define-fun f () (_ BitVec 16) (_ bv1 16)) ; 0x1
;)
;Model count: 2

