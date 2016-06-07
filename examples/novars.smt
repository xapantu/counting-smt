(set-logic QF_LIA)

(assert (= (# u Int 
 (and 
   (<= 0 u) (<= u 10)
 ))
 11
 
))

(assert (= (# u Int 
 (and 
   (<= 0 u) (<= u 10)
   (< u 9)
 ))
 9
))


(assert (= (# u Int 
 (and 
   (<= 0 u) (<= u 10)
   (> 9 u)
 ))
 9
))

(assert (= (# u Int 
 (and 
   (<= 0 u) (<= u 10)
   (> u 8)
 ))
 2
))

(assert (= (# u Int 
 (and 
   (<= 0 u) (<= u 10)
   (< 8 u)
 ))
 2
))

(assert (= (# u Int 
 (and 
   (<= 0 u) (<= u 10)
   (< u 0)
 ))
 0))

(assert (= (# u Int 
 (and 
   (<= 0 u) (<= u 10)
   (> u 10)
 ))
 0))

(assert (=
 (# u Int 
 (and 
   (<= 0 u) (<= u 10)
   (<= u (- 0 1))
 ))
 0
))

(assert (= (# u Int 
 (and 
   (<= 0 u) (<= u 10)
   (or (< u 0) (> u 10))
 ))
 0
))

(check-sat)
