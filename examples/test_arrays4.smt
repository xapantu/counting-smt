(set-logic QF_LIA)
(declare-fun N () Int)
(assert (>= N 1))
(declare-range A (0 N))
(declare-fun a () (Array A Bool)) 

(assert (> (# ind A (select a ind)) N))

(check-sat)
