(assert
	(forall ((arg1 (_ BitVec 64)) (arg2 (_ BitVec 64)) (arg3 (_ BitVec 64)) (arg4 (_ BitVec 64)))
		(=
			(bvor (bvand arg1 arg1) (bvand arg1 arg1))
			arg1
		)
	)
)
(check-sat)
