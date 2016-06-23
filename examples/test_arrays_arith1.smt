(set-logic QF_LIA)
(declare-fun N () Int)
(declare-range A (0 N))
(declare-fun a () (Array A Bool)) 
(assert (>= N 1))
(declare-fun i () Int)
(push 1)
(assert (and (>= i 0) (> N i)))
(assert (not (= (# x A (= x i))  1)))
(check-sat)
(pop 1)
(assert (= (# x A (select a x)) N))
(assert (= (# x A (and (= x i) (not (select a x)))) 1))
(check-sat)
