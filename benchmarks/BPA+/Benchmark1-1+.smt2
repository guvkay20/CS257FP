(set-info :smt-lib-version 2.6)
(set-option :produce-assignments true)
(set-logic BPA)
(set-info :source | Kaya Guvendi and Ethan Bogle |)
(set-info :category "crafted")
(set-info :status unsat)
(declare-const start Pointer)
(declare-const end Pointer)
(declare-const a Int+)
(declare-const b Int+)
(assert (=p start (Create+ 0 a)))
(assert (not (= Reduce(a) 0)))
(assert (=p end (Create+ 1 b)))
(assert (not (= Reduce(b) 0)))
(assert (= Reduce(b) (+ Reduce(a) (* 2 8))))
(assert (=p (+p start 2) end))
(check-sat)
(exit)