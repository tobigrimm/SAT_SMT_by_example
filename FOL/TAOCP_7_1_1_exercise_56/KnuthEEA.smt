(assert
	(exists ((x Bool)) (exists ((y Bool)) (forall ((z Bool))
		(and
			(or x y)
			(or (not x) z)
			(or y (not z))
		)))
	)
)
(check-sat)

