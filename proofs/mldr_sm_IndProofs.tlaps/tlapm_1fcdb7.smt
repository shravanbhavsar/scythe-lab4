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
;;        ASSUME NEW CONSTANT S,
;;               IsFiniteSet(S) ,
;;               NEW CONSTANT T,
;;               IsFiniteSet(T) 
;;        PROVE  /\ IsFiniteSet(S \cup T)
;;               /\ Cardinality(S \cup T)
;;                  = Cardinality(S) + Cardinality(T) - Cardinality(S \cap T) 
;; PROVE  Cardinality(Q1 \cup Q2)
;;        = Cardinality(Q1) + Cardinality(Q2) - Cardinality(Q1 \cap Q2)
;; TLA+ Proof Manager 1.4.5 (build 33809)
;; Proof obligation #44
;;   generated from file "./mldr_sm_IndProofs.tla", line 122, characters 13-14

(set-logic UFNIA)
(declare-sort u 0)
;; Standard TLA+ operators
(declare-fun int2u (Int) u)
(declare-fun u2int (u) Int)
(declare-fun tla__Int () u)
(declare-fun tla__plus (u u) u)
(declare-fun tla__minus (u u) u)
(declare-fun tla__le (u u) Bool)
(declare-fun boolify (u) Bool)
(declare-fun tla__in (u u) Bool)

;; Terms, predicates and strings
(declare-fun Cardinality (u) u)
(declare-fun IsFiniteSet (u) u)
(declare-fun Quorums (u) u)
(declare-fun QuorumsOverlap (u u) u)
(declare-fun Server () u)
(declare-fun Term () u)
(declare-fun Version () u)
(declare-fun a_Q1a () u)
(declare-fun a_Q2a () u)
(declare-fun a_aunde_unde_10a () u)
(declare-fun a_aunde_unde_6a () u)
(declare-fun a_aunde_unde_7a () u)
(declare-fun a_aunde_unde_8a () u)
(declare-fun a_aunde_unde_9a () u)
(declare-fun cfg () u)

(assert
  (forall ((X_18 Int))
  (! (= (u2int (int2u X_18)) X_18) :pattern ((int2u X_18)))))
(assert
  (forall ((X_18 u))
  (! (= (tla__in X_18 tla__Int) (exists ((N_17 Int)) (= X_18 (int2u N_17)))) :pattern ((tla__in X_18 tla__Int)))))
(assert
  (forall ((M_16 Int) (N_17 Int))
  (! (= (tla__plus (int2u M_16) (int2u N_17)) (int2u (+ M_16 N_17))) :pattern ((tla__plus (int2u M_16) (int2u N_17))))))
(assert
  (forall ((M_16 Int) (N_17 Int))
  (! (= (tla__minus (int2u M_16) (int2u N_17)) (int2u (- M_16 N_17))) :pattern ((tla__minus (int2u M_16) (int2u N_17))))))
(assert
  (forall ((M_16 Int) (N_17 Int))
  (! (= (tla__le (int2u M_16) (int2u N_17)) (<= M_16 N_17)) :pattern ((tla__le (int2u M_16) (int2u N_17))))))
(assert
  (forall ((S_21 u) (T_22 u))
  (=>
  (forall ((X_18 u)) (= (tla__in X_18 S_21) (tla__in X_18 T_22)))
  (= S_21 T_22))))
(assert (not
  (=
    (Cardinality a_aunde_unde_6a)
    (tla__plus
      (Cardinality a_Q1a)
      (tla__minus (Cardinality a_Q2a) (Cardinality a_aunde_unde_7a))))))
(assert
  (forall ((a_v11a u))
    (! (=
         (tla__in a_v11a a_aunde_unde_6a)
         (or (tla__in a_v11a a_Q1a) (tla__in a_v11a a_Q2a))) :pattern (
    (tla__in a_v11a a_aunde_unde_6a)))))
(assert
  (forall ((a_v12a u))
    (! (=
         (tla__in a_v12a a_aunde_unde_7a)
         (and (tla__in a_v12a a_Q1a) (tla__in a_v12a a_Q2a))) :pattern (
    (tla__in a_v12a a_aunde_unde_7a)))))
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
      (forall ((a_c2a u) (a_aunde_unde_8a u))
        (=>
          (and
            (forall ((a_v13a u))
              (=
                (tla__in a_v13a a_aunde_unde_8a)
                (or
                  (and (tla__in a_v13a a_c1a) (not (tla__in a_v13a a_c2a)))
                  (and (tla__in a_v13a a_c2a) (not (tla__in a_v13a a_c1a))))))
            (forall ((a_v4a u))
              (=> (tla__in a_v4a a_c2a) (tla__in a_v4a Server)))
            (= (int2u 1) (Cardinality a_aunde_unde_8a)))
          (boolify (QuorumsOverlap a_c1a a_c2a)))))))
(assert (forall ((a_v5a u)) (=> (tla__in a_v5a cfg) (tla__in a_v5a Server))))
(assert (tla__in a_Q1a (Quorums cfg)))
(assert (tla__in a_Q2a (Quorums cfg)))
(assert (boolify (IsFiniteSet cfg)))
(assert (boolify (IsFiniteSet a_Q1a)))
(assert (boolify (IsFiniteSet a_Q2a)))
(assert (boolify (IsFiniteSet a_aunde_unde_7a)))
(assert
  (forall ((S u))
    (=>
      (boolify (IsFiniteSet S))
      (forall ((T u) (a_aunde_unde_10a u) (a_aunde_unde_9a u))
        (=>
          (and
            (forall ((a_v14a u))
              (=
                (tla__in a_v14a a_aunde_unde_9a)
                (or (tla__in a_v14a S) (tla__in a_v14a T))))
            (forall ((a_v15a u))
              (=
                (tla__in a_v15a a_aunde_unde_10a)
                (and (tla__in a_v15a S) (tla__in a_v15a T))))
            (boolify (IsFiniteSet T)))
          (and
            (boolify (IsFiniteSet a_aunde_unde_9a))
            (=
              (Cardinality a_aunde_unde_9a)
              (tla__plus
                (Cardinality S)
                (tla__minus (Cardinality T) (Cardinality a_aunde_unde_10a))))))))))

(check-sat)
(exit)
