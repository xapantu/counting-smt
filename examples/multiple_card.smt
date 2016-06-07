(set-logic QF_LIA)

(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)

(declare-fun L () Int)
(declare-fun U () Int)

(declare-fun s1 () Int)
(declare-fun s2 () Int)

(assert (<= L x))
(assert (< x y))
(assert (< y z))
(assert (<= z U))

(assert (= s1 (# u Int 
 (and 
   (<= L u) (<= u U)
   (not (= u x))
   (not (= u y))
   (not (= u z))
 )))
)

(assert (= s2 (# u Int 
 (and 
   (<= L u) (<= u U)
   (or (= u x) (= u y) (= u z))
 )))
)

(assert (not (= (+ s1 s2) (+ (- U L) 1))))

(check-sat)
