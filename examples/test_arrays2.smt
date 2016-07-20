(set-logic QF_ALIA)
(declare-fun N () Int)
(assert (>= N 1))
(declare-range A (0 N))
(declare-fun a () (Array A Bool)) 

(assert (not
	(= N
	(+ 
		(# ind A (select a ind))
		(# ind A (not (select a ind)))
		)
	)))

(check-sat)
