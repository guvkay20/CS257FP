(set-info :smt-lib-version 2.6)
(set-logic BPA+)
(set-info :source | Kaya Guvendi and Ethan Bogle |)
(set-info :category "crafted")
(set-info :status sat)
(declare-const x Pointer)
(declare-const y Pointer)
(declare-const o Int)
(assert (= (+p x o) y))
(assert (<= (Align x) (Align y)))
(check-sat)
(exit)
