(set-logic QF_LIA)
(declare-fun N () Int)
(declare-range A (0 N))
(declare-fun a () (Array A Bool)) 
(assert (>= N 1))
(declare-fun i () Int)
(assert (and (>= i 0) (> N i)))
(assert (= (# x A (= (select a x) true)) N))
(assert (= (# x A (and (= x i) (not (select a x))))))
(check-sat)
