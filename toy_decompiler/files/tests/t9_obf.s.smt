(assert
	(forall ((arg1 (_ BitVec 64)) (arg2 (_ BitVec 64)) (arg3 (_ BitVec 64)) (arg4 (_ BitVec 64)))
		(=
			(bvxor (bvxor (bvxor (bvxor arg1 #x0000000012345678) #x00000000deadbeef) #x0000000012345678) #x00000000deadbeef)
			arg1
		)
	)
)
(check-sat)
