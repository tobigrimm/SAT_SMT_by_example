(assert
	(forall ((arg1 (_ BitVec 64)) (arg2 (_ BitVec 64)) (arg3 (_ BitVec 64)) (arg4 (_ BitVec 64)))
		(=
			(bvshl (bvlshr arg1 #x0000000000000004) #x0000000000000004)
			(bvand arg1 #xfffffffffffffff0)
		)
	)
)
(check-sat)
