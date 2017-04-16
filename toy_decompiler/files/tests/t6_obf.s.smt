(assert
	(forall ((arg1 (_ BitVec 64)) (arg2 (_ BitVec 64)) (arg3 (_ BitVec 64)) (arg4 (_ BitVec 64)))
		(=
			(bvand (bvneg (bvneg arg1)) (bvor arg1 #x0000000000000002))
			arg1
		)
	)
)
(check-sat)
