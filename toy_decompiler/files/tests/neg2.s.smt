(assert
	(forall ((arg1 (_ BitVec 64)) (arg2 (_ BitVec 64)) (arg3 (_ BitVec 64)) (arg4 (_ BitVec 64)))
		(=
			(bvsub (bvneg arg1) arg2)
			(bvneg (bvadd arg1 arg2))
		)
	)
)
(check-sat)
