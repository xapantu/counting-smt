(set-logic QF_LIA)

(declare-fun x () Int)
(declare-fun y () Int)

(assert (and (<= 0 x) (<= x 10)))
(assert (= y (# u Int (= y x))))

(check-sat)
(get-model)
