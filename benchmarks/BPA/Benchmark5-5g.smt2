(set-info :smt-lib-version 2.6)
(set-option :produce-assignments true)
(set-logic BPA)
(set-info :source | Kaya Guvendi and Ethan Bogle |)
(set-info :category "crafted")
(set-info :status sat)
(declare-const pt Pointer)
(declare-const c Int)
(declare-const sum Pointer)
(declare-const a Int)
(declare-const a_sum Int)
(assert (= a (+ (Base (Block pt)) (Offset pt))))
(assert (= a_sum (+ (Base (Block (+p pt c))) (Offset (+p pt c)))))
(assert (=p sum (+p pt c)))
(assert (and (= a 400) (= c 20)))
(assert (not (= (- (Offset sum) (Offset pt)) 160)))
(check-sat)
(exit)