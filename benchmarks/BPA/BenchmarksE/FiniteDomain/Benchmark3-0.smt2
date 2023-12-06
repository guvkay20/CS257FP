(set-info :smt-lib-version 2.6)
(set-option :produce-assignments true)
(set-logic BPA)
(set-info :source | Kaya Guvendi and Ethan Bogle |)
(set-info :category "crafted")
(set-info :status unsat)
(declare-const p0 Pointer)
(declare-const p1 Pointer)
(declare-const p2 Pointer)
(assert (= (Align p0) 0)
(assert (= (Align p1) 0)
(assert (= (Align p2) 0)
(assert (not (= (+ (Base (Block p0)) (Offset p0)) (+ (Base (Block \
p1)) (Offset p1)))))
(assert (not (= (+ (Base (Block p0)) (Offset p0)) (+ (Base (Block \
p2)) (Offset p2)))))
(assert (not (= (+ (Base (Block p1)) (Offset p1)) (+ (Base (Block \
p2)) (Offset p2)))))
(check-sat)
(exit)