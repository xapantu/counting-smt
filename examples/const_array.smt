(set-logic QF_ALIRA)
(declare-fun N () Int)
(declare-range A (0 N))
(declare-fun x () (Array A Bool))
(assert (= x (const-array false)))
(assert (> N (# (x A) (select x a))))
(check-sat)

