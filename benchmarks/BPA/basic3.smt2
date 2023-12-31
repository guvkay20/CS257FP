(set-info :smt-lib-version 2.6)
(set-option :produce-assignments true)
(set-logic BPA)
(set-info :source | Kaya Guvendi and Ethan Bogle |)
(set-info :category "crafted")
(set-info :status unsat)
(declare-fun a () Int)
(declare-fun b () Int)
(declare-fun c () Int)
(declare-const d Int)
(assert (and (<= 1 a) (<= a 512)))
(assert (and (<= 1 b) (<= b 512)))
(assert (and (<= 1 c) (<= c 512)))
(assert (= (+ b (- c)) (* 8 d)))
(assert (not (= b c)))
(assert (let ((x (Create a b)) (y (Create a c))) (= 0 (-p x y))))
(check-sat)
(exit)
