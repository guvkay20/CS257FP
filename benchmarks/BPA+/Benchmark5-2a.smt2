(set-info :smt-lib-version 2.6)
(set-option :produce-assignments true)
(set-logic BPA+)
(set-info :source | Kaya Guvendi and Ethan Bogle |)
(set-info :category "crafted")
(set-info :status unsat)
(declare-const p Pointer)
(declare-const q Pointer)
(declare-const ap Int)
(declare-const aq Int)
(assert (= ap (+ (Base (Block p)) (Offset p))))
(assert (= aq (+ (Base (Block q)) (Offset q))))
(assert (not (= ap 0)))
(assert (not (= aq 0)))
(assert (= (Block p) (Block q)))
(assert (<= ap aq))
(assert (not (<=p p q)))
(check-sat)
(exit)