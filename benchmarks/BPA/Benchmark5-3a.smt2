(set-info :smt-lib-version 2.6)
(set-option :produce-assignments true)
(set-logic BPA)
(set-info :source | Kaya Guvendi and Ethan Bogle |)
(set-info :category "crafted")
(set-info :status unsat)
(declare-const p Pointer)
(declare-const a Int)
(declare-const b Int)
(assert (= b (Block p)))
(assert (= a (+ b (Offset(p)))))
(assert (not (<= 0 a 512)))
(check-sat)
(exit)