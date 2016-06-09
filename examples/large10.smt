(set-logic QF_LIA)

(declare-fun x0 () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)
(declare-fun x5 () Int)
(declare-fun x6 () Int)
(declare-fun x7 () Int)
(declare-fun x8 () Int)
(declare-fun x9 () Int)

(assert (>= x0 0))
(assert (>= x1 0))
(assert (>= x2 0))
(assert (>= x3 0))
(assert (>= x4 0))
(assert (>= x5 0))
(assert (>= x6 0))
(assert (>= x7 0))
(assert (>= x8 0))
(assert (>= x9 0))

(declare-fun s () Int)

(assert (= s (# u Int 
  (and

  (<= (- (+ x0 x1) x2) u)
  (<= (+ (- x1 x2) x3) u)
  (<= (- (+ x2 x3) x4) u)
  (<= (+ (- x3 x4) x5) u)
  (<= (- (+ x4 x5) x6) u)
  (<= (+ (- x5 x6) x7) u)
  (<= (- (+ x6 x7) x8) u)
  (<= (+ (- x7 x8) x9) u)
  (<= (- (+ x8 x9) x0) u)
  (<= (+ (- x9 x0) x1) u)

  (<= u (+ (- x0 x1) x2))
  (<= u (- (+ x1 x2) x3))
  (<= u (+ (- x2 x3) x4))
  (<= u (- (+ x3 x4) x5))
  (<= u (+ (- x4 x5) x6))
  (<= u (- (+ x5 x6) x7))
  (<= u (+ (- x6 x7) x8))
  (<= u (- (+ x7 x8) x9))
  (<= u (+ (- x8 x9) x0))
  (<= u (- (+ x9 x0) x1))

  )
)))

(assert (> s (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ x0 x1) x2) x3) x4) x5) x6) x7) x8) x9) 1)))

(check-sat)