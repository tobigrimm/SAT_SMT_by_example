(assert
	(forall ((arg1 (_ BitVec 64)) (arg2 (_ BitVec 64)) (arg3 (_ BitVec 64)) (arg4 (_ BitVec 64)))
		(=
			(bvxor (bvxor arg1 #x0000000012345678) #x0000000012345679)
			(bvxor arg1 #x0000000000000001)
		)
	)
)
(check-sat)
