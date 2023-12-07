(set-info :smt-lib-version 2.6)
(set-option :produce-assignments true)
(set-logic BPA+)
(set-info :source | Kaya Guvendi and Ethan Bogle |)
(set-info :category "crafted")
(set-info :status unsat)
(declare-fun a () Int)
(declare-fun b () Int+)
(declare-fun c () Int+)
(declare-const d Int)
(assert (and (<= 1 a) (<= a 512)))
(assert (= (+ (Reduce b) (- (Reduce c))) (* 8 d)))
(assert (not (= (Reduce b) (Reduce c))))
(assert (let ((x (Create+ a b)) (y (Create+ a c))) (= 0 (-p x y))))
(check-sat)
(exit)