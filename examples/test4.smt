(set-logic QF_LIA)

(declare-fun x () Int)
(declare-fun y () Int)

(declare-fun c () Int)

(assert (= c (# u Int 
  (and 
    (>= u 0) 
    (>= 10 u)
    (= (+ u u) (+ x y))
  )
)))

(check-sat)
(get-model)
