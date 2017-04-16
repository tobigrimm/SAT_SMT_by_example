(assert
	(forall ((arg1 (_ BitVec 64)) (arg2 (_ BitVec 64)) (arg3 (_ BitVec 64)) (arg4 (_ BitVec 64)))
		(=
			(bvadd arg3 (bvadd #x00000000000004d2 (bvmul (bvmul arg1 #x00000000000003e8) arg2)))
			(bvadd arg3 (bvadd #x00000000000004d2 (bvmul (bvmul arg1 #x00000000000003e8) arg2)))
		)
	)
)
(check-sat)
