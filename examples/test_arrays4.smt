(set-logic QF_LIA)
(declare-fun N () Int)
(declare-range A (1 N))
(declare-fun a () (Array A Bool)) 

(assert (> (# ind A (select a ind)) N))

(check-sat)
