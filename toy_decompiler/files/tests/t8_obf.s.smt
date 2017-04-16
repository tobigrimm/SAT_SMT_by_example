(assert
	(forall ((arg1 (_ BitVec 64)) (arg2 (_ BitVec 64)) (arg3 (_ BitVec 64)) (arg4 (_ BitVec 64)))
		(=
			(bvxor (bvxor (bvxor arg1 #x0000000012345678) #x0000000012345679) #xfffffffffffffffe)
			(bvnot arg1)
		)
	)
)
(check-sat)
