(set-info :smt-lib-version 2.6)
(set-option :produce-assignments true)
(set-logic BPA)
(set-info :source | Kaya Guvendi and Ethan Bogle |)
(set-info :category "crafted")
(set-info :status unsat)
(declare-const pt Pointer)
(assert (or (< (Align pt) 0) (> (Align pt) 512)))
(check-sat)
(exit)