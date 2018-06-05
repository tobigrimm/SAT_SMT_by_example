(declare-fun a () (_ BitVec 4))
(declare-fun b () (_ BitVec 4))

(assert (= (bvadd a b) #x4))

; find a, b:
(get-all-models)

