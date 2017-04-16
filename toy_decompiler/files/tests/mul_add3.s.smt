(assert
	(forall ((arg1 (_ BitVec 64)) (arg2 (_ BitVec 64)) (arg3 (_ BitVec 64)) (arg4 (_ BitVec 64)))
		(=
			(bvadd (bvmul arg1 #x00000000000004d2) (bvmul arg2 #x000000000000162e))
			(bvadd (bvmul arg1 #x00000000000004d2) (bvmul arg2 #x000000000000162e))
		)
	)
)
(check-sat)
