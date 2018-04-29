(assert
	(forall ((x Bool)) (exists ((y Bool)) (exists ((z Bool))
		(and
			(or x y)
			(or (not x) z)
			(or y (not z))
		)))
	)
)
(check-sat)

