(assert
	(forall ((arg1 (_ BitVec 64)) (arg2 (_ BitVec 64)) (arg3 (_ BitVec 64)) (arg4 (_ BitVec 64)))
		(=
			(bvadd (bvadd (bvshl arg1 #x0000000000000002) arg1) (bvshl (bvshl arg1 #x0000000000000002) #x0000000000000002))
			(bvmul arg1 #x0000000000000015)
		)
	)
)
(check-sat)
