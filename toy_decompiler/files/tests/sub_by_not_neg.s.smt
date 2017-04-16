(assert
	(forall ((arg1 (_ BitVec 64)) (arg2 (_ BitVec 64)) (arg3 (_ BitVec 64)) (arg4 (_ BitVec 64)))
		(=
			(bvnot (bvneg (bvnot (bvneg arg1))))
			(bvsub arg1 #x0000000000000002)
		)
	)
)
(check-sat)
