;; Proof obligation:
;;ASSUME NEW CONSTANT MaxTerm,
;;        NEW CONSTANT MaxConfigVersion,
;;        NEW CONSTANT Server,
;;        NEW CONSTANT Secondary,
;;        NEW CONSTANT Primary,
;;        NEW VARIABLE currentTerm,
;;        NEW VARIABLE state,
;;        NEW VARIABLE configVersion,
;;        NEW VARIABLE configTerm,
;;        NEW VARIABLE config,
;;        Term = Nat ,
;;        Version = Nat ,
;;        \A c1, c2 \in SUBSET Server :
;;           1 = Cardinality((c1 \ c2) \cup (c2 \ c1)) => QuorumsOverlap(c1, c2) ,
;;        NEW CONSTANT cfg \in SUBSET Server,
;;        NEW CONSTANT Q1 \in Quorums(cfg),
;;        NEW CONSTANT Q2 \in Quorums(cfg),
;;        IsFiniteSet(cfg) ,
;;        IsFiniteSet(Q1) /\ IsFiniteSet(Q2) ,
;;        IsFiniteSet(Q1 \cap Q2) ,
;;        Cardinality(Q1) + Cardinality(Q2) > Cardinality(cfg) ,
;;        Cardinality(Q1) + Cardinality(Q2)
;;        =< Cardinality(cfg) + Cardinality(Q1 \cap Q2) ,
;;        ASSUME NEW CONSTANT S,
;;               IsFiniteSet(S) 
;;        PROVE  /\ Cardinality(S) \in Nat
;;               /\ ExistsBijection(1..Cardinality(S), S) 
;; PROVE  Cardinality(Q1) + Cardinality(Q2)
;;        < Cardinality(Q1) + Cardinality(Q2) + Cardinality(Q1 \cap Q2)
;; TLA+ Proof Manager 1.4.5 (build 33809)
;; Proof obligation #50
;;   generated from file "./mldr_sm_IndProofs.tla", line 131, characters 19-20

(set-logic UFNIA)
(declare-sort u 0)
;; Standard TLA+ operators
(declare-fun int2u (Int) u)
(declare-fun u2int (u) Int)
(declare-fun tla__Int () u)
(declare-fun tla__plus (u u) u)
(declare-fun tla__lt (u u) Bool)
(declare-fun tla__le (u u) Bool)
(declare-fun tla__Range (u u) u)
(declare-fun boolify (u) Bool)
(declare-fun tla__in (u u) Bool)
(declare-fun tla__emptyset () u)

;; Terms, predicates and strings
(declare-fun Cardinality (u) u)
(declare-fun ExistsBijection (u u) u)
(declare-fun IsFiniteSet (u) u)
(declare-fun Quorums (u) u)
(declare-fun QuorumsOverlap (u u) u)
(declare-fun Server () u)
(declare-fun Term () u)
(declare-fun Version () u)
(declare-fun a_Q1a () u)
(declare-fun a_Q2a () u)
(declare-fun a_aunde_unde_6a () u)
(declare-fun a_aunde_unde_7a () u)
(declare-fun cfg () u)

(assert
  (forall ((X_12 Int))
  (! (= (u2int (int2u X_12)) X_12) :pattern ((int2u X_12)))))
(assert
  (forall ((X_12 u))
  (! (= (tla__in X_12 tla__Int) (exists ((N_11 Int)) (= X_12 (int2u N_11)))) :pattern ((tla__in X_12 tla__Int)))))
(assert
  (forall ((M_10 Int) (N_11 Int))
  (! (= (tla__plus (int2u M_10) (int2u N_11)) (int2u (+ M_10 N_11))) :pattern ((tla__plus (int2u M_10) (int2u N_11))))))
(assert
  (forall ((M_10 Int) (N_11 Int))
  (! (= (tla__lt (int2u M_10) (int2u N_11)) (< M_10 N_11)) :pattern ((tla__lt (int2u M_10) (int2u N_11))))))
(assert
  (forall ((M_10 Int) (N_11 Int))
  (! (= (tla__le (int2u M_10) (int2u N_11)) (<= M_10 N_11)) :pattern ((tla__le (int2u M_10) (int2u N_11))))))
(assert
  (forall ((M_10 Int) (N_11 Int) (Z_14 u))
  (=
  (tla__in Z_14 (tla__Range (int2u M_10) (int2u N_11)))
  (exists ((X_12 Int))
  (and (= Z_14 (int2u X_12)) (<= M_10 X_12) (<= X_12 N_11))))))
(assert
  (forall ((M_10 Int) (N_11 Int) (X_12 Int) (Y_13 Int))
  (=>
  (and
  (or (<= M_10 N_11) (<= X_12 Y_13))
  (=
  (tla__Range (int2u M_10) (int2u N_11))
  (tla__Range (int2u X_12) (int2u Y_13))))
  (and (= M_10 X_12) (= N_11 Y_13)))))
(assert
  (forall ((M_10 Int) (N_11 Int))
  (= (= (tla__Range (int2u M_10) (int2u N_11)) tla__emptyset) (< N_11 M_10))))
(assert
  (forall ((S_15 u) (T_16 u))
  (=>
  (forall ((X_12 u)) (= (tla__in X_12 S_15) (tla__in X_12 T_16)))
  (= S_15 T_16))))
(assert
  (forall ((X_12 u))
  (! (= (tla__in X_12 tla__emptyset) false) :pattern ((tla__in X_12 tla__emptyset)))))
(assert (not
  (tla__lt
    (tla__plus (Cardinality a_Q1a) (Cardinality a_Q2a))
    (tla__plus
      (tla__plus (Cardinality a_Q1a) (Cardinality a_Q2a))
      (Cardinality a_aunde_unde_6a)))))
(assert
  (forall ((a_v8a u))
    (! (=
         (tla__in a_v8a a_aunde_unde_6a)
         (and (tla__in a_v8a a_Q1a) (tla__in a_v8a a_Q2a))) :pattern (
    (tla__in a_v8a a_aunde_unde_6a)))))
(assert
  (forall ((a_v1a u))
    (=
      (tla__in a_v1a Term)
      (and (tla__in a_v1a tla__Int) (tla__le (int2u 0) a_v1a)))))
(assert
  (forall ((a_v2a u))
    (=
      (tla__in a_v2a Version)
      (and (tla__in a_v2a tla__Int) (tla__le (int2u 0) a_v2a)))))
(assert
  (forall ((a_c1a u))
    (=>
      (forall ((a_v3a u)) (=> (tla__in a_v3a a_c1a) (tla__in a_v3a Server)))
      (forall ((a_c2a u) (a_aunde_unde_7a u))
        (=>
          (and
            (forall ((a_v9a u))
              (=
                (tla__in a_v9a a_aunde_unde_7a)
                (or
                  (and (tla__in a_v9a a_c1a) (not (tla__in a_v9a a_c2a)))
                  (and (tla__in a_v9a a_c2a) (not (tla__in a_v9a a_c1a))))))
            (forall ((a_v4a u))
              (=> (tla__in a_v4a a_c2a) (tla__in a_v4a Server)))
            (= (int2u 1) (Cardinality a_aunde_unde_7a)))
          (boolify (QuorumsOverlap a_c1a a_c2a)))))))
(assert (forall ((a_v5a u)) (=> (tla__in a_v5a cfg) (tla__in a_v5a Server))))
(assert (tla__in a_Q1a (Quorums cfg)))
(assert (tla__in a_Q2a (Quorums cfg)))
(assert (boolify (IsFiniteSet cfg)))
(assert (boolify (IsFiniteSet a_Q1a)))
(assert (boolify (IsFiniteSet a_Q2a)))
(assert (boolify (IsFiniteSet a_aunde_unde_6a)))
(assert
  (tla__lt
    (Cardinality cfg) (tla__plus (Cardinality a_Q1a) (Cardinality a_Q2a))))
(assert
  (tla__le
    (tla__plus (Cardinality a_Q1a) (Cardinality a_Q2a))
    (tla__plus (Cardinality cfg) (Cardinality a_aunde_unde_6a))))
(assert
  (forall ((S u))
    (=>
      (boolify (IsFiniteSet S))
      (and
        (tla__in (Cardinality S) tla__Int)
        (tla__le (int2u 0) (Cardinality S))
        (boolify (ExistsBijection (tla__Range (int2u 1) (Cardinality S)) S))))))

(check-sat)
(exit)
