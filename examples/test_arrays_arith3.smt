(set-logic QF_ALIA)
(declare-fun N () Int)
(declare-range A (0 N))
(declare-fun a () (Array A Bool)) 
(assert (>= N 3))
(declare-fun i () Int)
(assert (and (>= i 1) (> (- N 1) i)))
(assert (= (# x A (select a x)) i))
(assert (= (# x A (and (>= x i) (not (select a x)))) (- N i)))
(check-sat)
