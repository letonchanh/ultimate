(set-option :produce-proofs true)
(set-option :proof-check-mode true)
(set-option :print-terms-cse false)

(set-logic QF_AX)
(declare-sort U 0)
(declare-fun v1 () U)
(declare-fun v2 () U)
(declare-fun i1 () U)
(declare-fun i2 () U)
(declare-fun w1 () U)
(declare-fun w2 () U)
(declare-fun a () (Array U U))
(define-fun constU ((v U)) (Array U U) ((as const (Array U U)) v))

(assert (= (store a i1 w1) ((as const (Array U U)) v1)))
(assert (= (store a i2 w2) ((as const (Array U U)) v2)))
(assert (or (not (= v1 v2)) (not (= v1 w1)) (not (= v2 w2))))
(check-sat)
(get-proof)
(exit)