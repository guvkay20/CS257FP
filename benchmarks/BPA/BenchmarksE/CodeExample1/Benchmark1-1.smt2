(set-info :smt-lib-version 2.6)
(set-option :produce-assignments true)
(set-logic BPA)
(set-info :source | Kaya Guvendi and Ethan Bogle |)
(set-info :category "crafted")
(set-info :status unsat)
(declare-const start Pointer)
(declare-const end Pointer)
(declare-const a Int)
(declare-const b Int)
(assert (=p start (Create 0 a)))
(assert (<= 1 a 512))
(assert (=p end (Create 1 b)))
(assert (<= 1 b 512))
(assert (= b (+ a (* 2 8))))
(assert (=p (+p start 2) end))
(check-sat)
(exit)