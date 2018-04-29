(assert
	(exists ((x Bool)) (forall ((y Bool)) (exists ((z Bool))
		(and
			(or x y)
			(or (not x) z)
			(or y (not z))
		)))
	)
)
(check-sat)

