(assert
	(forall ((x Bool) (y Bool) (z Bool))
		(=
			(or (xor x y) (xor y z))
			(or (xor x z) (xor y z))
		)
	)
)
(check-sat)
