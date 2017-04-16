(assert
	(forall ((arg1 (_ BitVec 64)) (arg2 (_ BitVec 64)) (arg3 (_ BitVec 64)) (arg4 (_ BitVec 64)))
		(=
			(bvxor #xffffffffffffffff arg1)
			(bvnot arg1)
		)
	)
)
(check-sat)
