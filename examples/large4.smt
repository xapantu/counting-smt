(set-logic QF_LIA)

(declare-fun x0 () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)

(assert (>= x0 0))
(assert (>= x1 0))
(assert (>= x2 0))
(assert (>= x3 0))

(declare-fun s () Int)

(assert (= s (# u Int 
  (and

  (<= (- (+ x0 x1) x2) u)
  (<= (+ (- x1 x2) x3) u)
  (<= (- (+ x2 x3) x0) u)
  (<= (+ (- x3 x0) x1) u)

  (<= u (+ (- x0 x1) x2))
  (<= u (- (+ x1 x2) x3))
  (<= u (+ (- x2 x3) x0))
  (<= u (- (+ x3 x0) x1))

  )
)))

(assert (> s (+ (+ (+ (+ x0 x1) x2) x3) 1)))

(check-sat)
