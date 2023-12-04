(set-info :smt-lib-version 2.6)
(set-option :produce-assignments true)
(set-logic BPA)
(set-info :source | Kaya Guvendi and Ethan Bogle |)
(set-info :category "crafted")
(set-info :status unsat)
(declare-const p Pointer)
(declare-const p_to_b Pointer)
(declare-const q Pointer)
(assert (<= 1 (Address p) 512))
(assert (<= 1 (Address p_to_b) 512))
(assert (= q (+p p_to_b -1)))
(assert (= (Address p_to_b) (+ (Address p) 8)))
(assert (not (= (Address p) (Address q))))
(check-sat)
(exit)