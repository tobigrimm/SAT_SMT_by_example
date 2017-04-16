(assert
	(forall ((arg1 (_ BitVec 64)) (arg2 (_ BitVec 64)) (arg3 (_ BitVec 64)) (arg4 (_ BitVec 64)))
		(=
			(bvlshr (bvlshr (bvmul arg1 #xcccccccccccccccd) #x0000000000000040) #x0000000000000003)
			(bvudiv arg1 #x000000000000000a)
		)
	)
)
(check-sat)
