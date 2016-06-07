(set-logic QF_LIA)

(declare-fun s1 () Int)
(declare-fun s2 () Int)
(declare-fun s3 () Int)

(assert (= s1 (# u Int (and (>= u 1) (>= 2 u)))))
(assert (= s2 (# u Int (and (>= u 1) (>= 2 u) (< u s1)))))
(assert (= s3 (# u Int (and (>= u 1) (>= 2 u) (< u s2)))))

(check-sat)
(get-model)
