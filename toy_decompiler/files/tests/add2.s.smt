(assert
	(forall ((arg1 (_ BitVec 64)) (arg2 (_ BitVec 64)) (arg3 (_ BitVec 64)) (arg4 (_ BitVec 64)))
		(=
			(bvadd (bvadd (bvadd arg1 arg1) (bvadd arg1 arg1)) (bvadd (bvadd arg1 arg1) (bvadd arg1 arg1)))
			(bvmul arg1 #x0000000000000008)
		)
	)
)
(check-sat)
