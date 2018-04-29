(assert
	(forall ((x Bool) (y Bool) (z Bool) (w Bool))
		(=
			(or (xor w x y) z)
			(xor (or w z) (or x z) (or y z))
		)
	)
)
(check-sat)
