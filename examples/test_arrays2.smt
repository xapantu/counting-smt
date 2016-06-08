(set-logic QF_LIA)
(declare-fun N () Int)
(declare-range A (1 N))
(declare-fun a () (Array A Bool)) 

(assert (not
	(= N
	(+ 
		(# ind A (select a ind))
		(# ind A (not (select a ind)))
		)
	)))

(check-sat)
