(set-logic QF_LIA)
(declare-fun N () Int)
(declare-range A (0 N))
(assert (>= N 0))
(push 1)
(assert (= (# (x A) true) (+ N 1)))
(check-sat)
(pop 1)
(assert (= (# (x A) true) N))
(check-sat)
