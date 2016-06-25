(set-logic QF_LIA)
(declare-fun N () Int)
(declare-range A (0 N))
(declare-fun a () (Array A Bool)) 
(assert (>= N 1))
(declare-fun i () Int)
(assert (and (>= i 0) (< i N)))
(check-sat)

(push 1)
(assert (not (or (select a i) (not (select a i)))))
(check-sat)
(pop 1)

(push 1)
(assert (select (store a i false) i))
(check-sat)
(pop 1)

(push 1)
(assert (not (select (store a i true) i)))
(check-sat)
(pop 1)
(push 1)
(assert (select (store a i true) i))
(check-sat)
(pop 1)
(push 1)
(assert (not (select (store a i false) i)))
(check-sat)
(pop 1)
