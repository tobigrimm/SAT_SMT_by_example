(assert
	(forall ((arg1 (_ BitVec 64)) (arg2 (_ BitVec 64)) (arg3 (_ BitVec 64)) (arg4 (_ BitVec 64)))
		(=
			(bvsub arg2 (bvneg arg1))
			(bvadd arg2 arg1)
		)
	)
)
(check-sat)
