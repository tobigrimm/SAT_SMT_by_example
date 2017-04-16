(assert
	(forall ((arg1 (_ BitVec 64)) (arg2 (_ BitVec 64)) (arg3 (_ BitVec 64)) (arg4 (_ BitVec 64)))
		(=
			(bvor (bvnot arg2) (bvnot arg1))
			(bvnot (bvand arg2 arg1))
		)
	)
)
(check-sat)
