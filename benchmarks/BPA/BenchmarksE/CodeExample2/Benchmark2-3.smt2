(set-info :smt-lib-version 2.6)
(set-option :produce-assignments true)
(set-logic BPA)
(set-info :source | Kaya Guvendi and Ethan Bogle |)
(set-info :category "crafted")
(set-info :status sat)
(declare-const p Pointer)
(declare-const p_to_b Pointer)
(declare-const q Pointer)
(assert (<= 1 (+ (Base (Block p)) (Offset p)) 512))
(assert (<= 1 (+ (Base (Block p_to_b)) (Offset p_to_b)) 512))
(assert (= (- (+ (Base (Block p_to_b)) (Offset p_to_b)) (+ (Base (Block p)) (Offset p))) 1))
(assert (= (- (+ (Base (Block p_to_b)) (Offset p_to_b)) (+ (Base (Block p)) (Offset p))) 1))
(assert (= (Block q) (Block p_to_b)))
(assert (not (=p p q)))
(check-sat)
(get-model)
(exit)