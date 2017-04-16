(assert
	(forall ((arg1 (_ BitVec 64)) (arg2 (_ BitVec 64)) (arg3 (_ BitVec 64)) (arg4 (_ BitVec 64)))
		(=
			(bvshl (bvlshr arg1 #x0000000000000003) #x0000000000000003)
			(bvand arg1 #xfffffffffffffff8)
		)
	)
)
(check-sat)
