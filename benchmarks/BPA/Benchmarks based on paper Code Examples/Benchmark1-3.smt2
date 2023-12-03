(set-info :smt-lib-version 2.6)
(set-option :produce-assignments true)
(set-logic BPA)
(set-info :source | Kaya Guvendi and Ethan Bogle |)
(set-info :category "crafted")
(set-info :status unsat)
(declare-const start Pointer)
(decalre-const end Pointer)
(declare-const a Int)
(declare-const b Int)
(assert (= a (Address start)))
(assert (<= 1 a 512))
(assert (= b (Address end)))
(assert (<= 1 b 512))
(assert (not (= (Base start) (Base end))))
(assert (= b (+ a (* 2 8))))
(assert (= (+p start 2) end))
(check-sat)
(exit)