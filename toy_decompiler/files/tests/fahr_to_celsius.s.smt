(assert
	(forall ((arg1 (_ BitVec 64)) (arg2 (_ BitVec 64)) (arg3 (_ BitVec 64)) (arg4 (_ BitVec 64)))
		(=
			(bvudiv (bvmul (bvsub arg1 #x0000000000000020) #x0000000000000005) #x0000000000000009)
			(bvudiv (bvmul (bvsub arg1 #x0000000000000020) #x0000000000000005) #x0000000000000009)
		)
	)
)
(check-sat)
