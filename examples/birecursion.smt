(set-logic QF_LIA)

(declare-fun x () Int)
(declare-fun y () Int)

(assert (and (>= x 0) (>= 10 x)))
(assert (and (>= y 0) (>= 10 y)))

(assert (= y (# u Int 
  (and 
    (>= u 0) (>= 10 u)
    (= u x)
    (= u y)
  )
)))

(check-sat)
(assert (= x 10))
(get-model)
