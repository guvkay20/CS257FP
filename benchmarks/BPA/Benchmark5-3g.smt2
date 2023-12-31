(set-info :smt-lib-version 2.6)
(set-option :produce-assignments true)
(set-logic BPA)
(set-info :source | Kaya Guvendi and Ethan Bogle |)
(set-info :category "crafted")
(set-info :status sat)
(declare-const p Pointer)
(declare-const a Int)
(declare-const b Int)
(assert (= b (Block p)))
(assert (not (= a (+ (Base b) (Offset p)))))
(assert (= (+ (Base (Block (Create b a))) (Offset (Create b a))) (+ (Base (Block p)) (Offset p))))
(check-sat)
(exit)