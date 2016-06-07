(set-logic QF_LIA)

(declare-fun x0 () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)

(declare-fun s () Int)

(assert (and (>= x0 0) (>= 3 x0)))
(assert (and (>= x1 0) (>= 3 x1)))
(assert (and (>= x2 0) (>= 3 x2)))
(assert (and (>= x3 0) (>= 3 x3)))

(assert (> x0 x1))
(assert (> x1 x2))
(assert (> x2 x3))

(assert (= s (# u Int 
  (and 
    (<= u 0) (<= u 3)
    (not (= u x0))
    (not (= u x1))
    (not (= u x2))
    (not (= u x3))     
  )
)))

(check-sat)
(get-model)
