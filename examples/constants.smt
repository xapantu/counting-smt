(set-logic QF_LIA)

(declare-fun s1 () Int)
(declare-fun s2 () Int)

(assert (= s1 (# u Int (and (>= u 1) (>= 2 u)))))
(assert (= s2 (# u Int (and (>= u 1) (>= 2 u) (>= s1 (+ u 1))))))

(check-sat)
(get-model)
