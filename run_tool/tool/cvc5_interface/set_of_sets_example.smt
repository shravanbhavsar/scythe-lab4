; Run with ../cvc5_code/cvc5/build/bin/cvc5 set_of_sets_example.smt

(set-logic ALL)
(set-option :produce-models true)

; Declare 'x' as a set of sets of integers.
(declare-fun x () (Set (Set Int)))
(declare-fun z () (Set Int))
(declare-fun w () (Set Int))

; Declare a function from a set to a set of sets.
(declare-fun h ((Set Int)) (Set (Set Int)))

(declare-fun Q () (Set Int))
(declare-fun Qpowerset () (Set (Set Int)))
(declare-fun Qelem () (Set Int))

; Define concrete elements of Q.
(assert (= Q (set.insert 1 2 (set.singleton 3))))

(define-fun p ((m (Set Int))) Bool
    (set.subset m Q)
)

(assert (set.subset Qelem Q))
(assert (= (set.card Qelem) 2))

(assert 
    (= 
        Qpowerset
        (set.filter p (as set.universe (Set (Set Int))))
    )
)

;(define-fun SUBSET ((S (Set Int))) (Set (Set Int))
;    (set.filter p (as set.universe (Set (Set Int))))
;)


;(assert (forall ((S (Set Int)) (k (Set Int))) 
;    (= (set.subset k S) (set.member k (SUBSET S)))))

;(define-fun Quorums ((S (Set Int))) (Set (Set Int))
;    (set.singleton S)
;)

;(assert (= ypower (SUBSET y)))

; If y and z are in h(w), then the intersection of y and z is non-empty.
;(assert (=> 
;            (and 
;                (set.member y (h w)) 
;                (set.member z (h w))) 
;            (not 
;                (= (as set.empty (Set Int)) (set.inter y z)))
;        )
;)

;(assert (set.member z x))
;(assert (not (= y z)))
;(assert (not (= x (as set.empty (Set (Set Int))))))
;(assert (not (= (h y) (as set.empty (Set (Set Int))))))

(check-sat)
(get-model)
