(assert
	(forall ((arg1 (_ BitVec 64)) (arg2 (_ BitVec 64)) (arg3 (_ BitVec 64)) (arg4 (_ BitVec 64)))
		(=
			(bvsrem arg1 #x0000000000000003)
			(bvsrem arg1 #x0000000000000003)
		)
	)
)
(check-sat)
