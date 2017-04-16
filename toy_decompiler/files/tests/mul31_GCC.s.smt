(assert
	(forall ((arg1 (_ BitVec 64)) (arg2 (_ BitVec 64)) (arg3 (_ BitVec 64)) (arg4 (_ BitVec 64)))
		(=
			(bvsub (bvshl arg1 #x0000000000000005) arg1)
			(bvmul arg1 #x000000000000001f)
		)
	)
)
(check-sat)
