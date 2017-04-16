(assert
	(forall ((arg1 (_ BitVec 64)) (arg2 (_ BitVec 64)) (arg3 (_ BitVec 64)) (arg4 (_ BitVec 64)))
		(=
			(bvadd (bvnot arg1) #x0000000000000001)
			(bvneg arg1)
		)
	)
)
(check-sat)
