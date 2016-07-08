(set-info :smt-lib-version 2.0)
(set-logic QF_LIRA)
(push 1)
(declare-fun N_PID () Int)
(declare-range PID (0 N_PID))
(declare-fun |s0.round| () Real)
(declare-fun |s0.cx| () (Array PID Bool))
(declare-fun |s0.source| () PID)
(declare-fun |s0.val| () Bool)
(declare-fun |s0.good_p| () (Array PID Bool))
(assert (and (= |s0.round| 0) (= |s0.cx| (store |s0.cx| |s0.source| |s0.val|)) (> N_PID (* 3 (- N_PID (# ((|var!!0| PID)) (select |s0.good_p| |var!!0|)))))))
(push 1)
(assert (not (or (not (and (>= |s0.round| 0) (select |s0.good_p| |s0.source|))) (= (select |s0.cx| |s0.source|) |s0.val|))))
(check-sat)
(pop 1)
(declare-fun |s1.round| () Real)
(declare-fun |s1.val| () Bool)
(declare-fun |s1.source| () PID)
(declare-fun |s1.good_p| () (Array PID Bool))
(declare-fun |s1.cx| () (Array PID Bool))
(assert (or (and (> 2 |s0.round|) (forall ((|var!!0| PID)) (or (not (select |s0.good_p| |var!!0|)) (= (select |s1.cx| |var!!0|) (select |s0.cx| |s0.source|)))) (= |s1.round| (+ |s0.round| 1)) (= |s0.val| |s1.val|) (= |s0.source| |s1.source|) (= |s0.good_p| |s1.good_p|)) (and (= |s0.round| 2) (= |s0.val| |s1.val|) (= |s0.source| |s1.source|) (= |s0.cx| |s1.cx|) (= |s0.good_p| |s1.good_p|) (= |s0.round| |s1.round|))))
(push 1)
(assert (not (or (not (and (>= |s1.round| 0) (select |s1.good_p| |s1.source|))) (= (select |s1.cx| |s1.source|) |s1.val|))))
(check-sat)
(pop 1)
(declare-fun |s2.round| () Real)
(declare-fun |s2.val| () Bool)
(declare-fun |s2.source| () PID)
(declare-fun |s2.good_p| () (Array PID Bool))
(declare-fun |s2.cx| () (Array PID Bool))
(assert (or (and (> 2 |s1.round|) (forall ((|var!!0| PID)) (or (not (select |s1.good_p| |var!!0|)) (= (select |s2.cx| |var!!0|) (select |s1.cx| |s1.source|)))) (= |s2.round| (+ |s1.round| 1)) (= |s1.val| |s2.val|) (= |s1.source| |s2.source|) (= |s1.good_p| |s2.good_p|)) (and (= |s1.round| 2) (= |s1.val| |s2.val|) (= |s1.source| |s2.source|) (= |s1.cx| |s2.cx|) (= |s1.good_p| |s2.good_p|) (= |s1.round| |s2.round|))))
(push 1)
(assert (not (or (not (and (>= |s2.round| 0) (select |s2.good_p| |s2.source|))) (= (select |s2.cx| |s2.source|) |s2.val|))))
(check-sat)
(pop 1)
