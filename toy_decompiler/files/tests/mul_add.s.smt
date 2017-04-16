(assert
	(forall ((arg1 (_ BitVec 64)) (arg2 (_ BitVec 64)) (arg3 (_ BitVec 64)) (arg4 (_ BitVec 64)))
		(=
			(bvadd (bvmul arg1 arg2) arg3)
			(bvadd (bvmul arg1 arg2) arg3)
		)
	)
)
(check-sat)
