(set-logic QF_LIA)
(declare-fun y () Int)
(assert (= y (# z Int (and (>= z 0) (< z 15) (= (mod z 2) 0)))))
(check-sat)
(get-model)