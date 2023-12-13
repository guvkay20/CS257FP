(set-info :smt-lib-version 2.6)
(set-option :produce-assignments true)
(set-logic BPA+)
(set-info :source | Kaya Guvendi and Ethan Bogle |)
(set-info :category "crafted")
(set-info :status sat)
(declare-const p Pointer)
(declare-const p_to_b Pointer)
(declare-const q Pointer)
(assert (not (= (+ (Base (Block p)) (Offset p)) 0)))
(assert (not (= (+ (Base (Block p_to_b)) (Offset p_to_b)) 0)))
(assert (= (-p p_to_b p) 1))
(assert (= (-p p_to_b q) 1))
(assert (not (= (+ (Base (Block p)) (Offset p)) (+ (Base (Block q)) (Offset q)))))
(check-sat)
(exit)