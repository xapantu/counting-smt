(set-info :smt-lib-version 2.0)
(set-logic QF_ALIRA)
(push 1)
(declare-fun N_P1 () Int)
(declare-range P1 (0 N_P1))
(declare-fun |s0.want| () (Array P1 Bool))
(declare-fun |s0.crit| () (Array P1 Bool))
(assert (and (forall ((|var!!0| P1)) (not (select |s0.want| |var!!0|))) (forall ((|var!!0| P1)) (not (select |s0.crit| |var!!0|)))))
(push 1)
(declare-fun |s0.i| () P1)
(assert (not (forall ((|var!!0| P1)) (or (not (and (select |s0.crit| |s0.i|) (select |s0.crit| |var!!0|))) (= |s0.i| |var!!0|)))))
(check-sat)
(pop 1)
(declare-fun |s1.want| () (Array P1 Bool))
(declare-fun |s1.crit| () (Array P1 Bool))
(declare-fun |s0.turn| () P1)
(declare-fun |s1.turn| () P1)
(declare-fun |s0.i| () P1)
(assert (or (and (not (select |s0.want| |s0.i|)) (= |s1.want| (store |s0.want| |s0.i| true)) (= |s0.crit| |s1.crit|) (= |s0.turn| |s1.turn|)) (and (select |s0.want| |s0.i|) (not (select |s0.crit| |s0.i|)) (= |s0.turn| |s0.i|) (= |s1.crit| (store |s0.crit| |s0.i| true)) (= |s0.want| |s1.want|) (= |s0.turn| |s1.turn|)) (and (select |s0.crit| |s0.i|) (= |s1.want| (store |s0.want| |s0.i| false)) (= |s1.crit| (store |s0.crit| |s0.i| false)))))
(push 1)
(declare-fun |s1.i| () P1)
(assert (not (forall ((|var!!0| P1)) (or (not (and (select |s1.crit| |s1.i|) (select |s1.crit| |var!!0|))) (= |s1.i| |var!!0|)))))
(check-sat)
(pop 1)
(declare-fun |s2.want| () (Array P1 Bool))
(declare-fun |s2.crit| () (Array P1 Bool))
(declare-fun |s2.turn| () P1)
(declare-fun |s1.i| () P1)
(assert (or (and (not (select |s1.want| |s1.i|)) (= |s2.want| (store |s1.want| |s1.i| true)) (= |s1.crit| |s2.crit|) (= |s1.turn| |s2.turn|)) (and (select |s1.want| |s1.i|) (not (select |s1.crit| |s1.i|)) (= |s1.turn| |s1.i|) (= |s2.crit| (store |s1.crit| |s1.i| true)) (= |s1.want| |s2.want|) (= |s1.turn| |s2.turn|)) (and (select |s1.crit| |s1.i|) (= |s2.want| (store |s1.want| |s1.i| false)) (= |s2.crit| (store |s1.crit| |s1.i| false)))))
(push 1)
(declare-fun |s2.i| () P1)
(assert (not (forall ((|var!!0| P1)) (or (not (and (select |s2.crit| |s2.i|) (select |s2.crit| |var!!0|))) (= |s2.i| |var!!0|)))))
(check-sat)
