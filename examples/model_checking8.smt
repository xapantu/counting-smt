(set-info :smt-lib-version 2.0)
(set-logic QF_ALIRA)
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
(assert (not (and (or (= |s0.round| 0) (= |s0.round| 1) (= |s0.round| 2)) (or (not (select |s0.good_p| |s0.source|)) (= (select |s0.cx| |s0.source|) |s0.val|)))))
(check-sat)
(pop 1)
(pop 1)
(exit)
