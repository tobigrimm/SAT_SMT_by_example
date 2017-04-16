(assert
	(forall ((arg1 (_ BitVec 64)) (arg2 (_ BitVec 64)) (arg3 (_ BitVec 64)) (arg4 (_ BitVec 64)))
		(=
			(bvlshr (bvlshr (bvmul arg1 #x6a37991a23aead6f) #x0000000000000040) #x0000000000000009)
			(bvudiv arg1 #x00000000000004d2)
		)
	)
)
(check-sat)
