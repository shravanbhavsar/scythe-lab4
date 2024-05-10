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
;;        Q1 \in SUBSET cfg /\ Q2 \in SUBSET cfg ,
;;        ASSUME NEW CONSTANT S,
;;               IsFiniteSet(S) ,
;;               NEW CONSTANT T \in SUBSET S
;;        PROVE  /\ IsFiniteSet(T)
;;               /\ Cardinality(T) =< Cardinality(S)
;;               /\ Cardinality(S) = Cardinality(T) => S = T ,
;;        IsFiniteSet(Server) 
;; PROVE  Cardinality(Q1 \cup Q2) =< Cardinality(cfg)
;; TLA+ Proof Manager 1.4.5 (build 33809)
;; Proof obligation #46
;;   generated from file "./mldr_sm_IndProofs.tla", line 124, characters 13-14

(set-logic UFNIA)
(declare-sort u 0)
;; Standard TLA+ operators
(declare-fun int2u (Int) u)
(declare-fun u2int (u) Int)
(declare-fun tla__Int () u)
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
(declare-fun a_aunde_unde_11a () u)
(declare-fun a_aunde_unde_9a () u)
(declare-fun cfg () u)

(assert
  (forall ((X_17 Int))
  (! (= (u2int (int2u X_17)) X_17) :pattern ((int2u X_17)))))
(assert
  (forall ((X_17 u))
  (! (= (tla__in X_17 tla__Int) (exists ((N_16 Int)) (= X_17 (int2u N_16)))) :pattern ((tla__in X_17 tla__Int)))))
(assert
  (forall ((M_15 Int) (N_16 Int))
  (! (= (tla__le (int2u M_15) (int2u N_16)) (<= M_15 N_16)) :pattern ((tla__le (int2u M_15) (int2u N_16))))))
(assert
  (forall ((S_20 u) (T_21 u))
  (=>
  (forall ((X_17 u)) (= (tla__in X_17 S_20) (tla__in X_17 T_21)))
  (= S_20 T_21))))
(assert (not (tla__le (Cardinality a_aunde_unde_9a) (Cardinality cfg))))
(assert
  (forall ((a_v12a u))
    (! (=
         (tla__in a_v12a a_aunde_unde_11a)
         (and (tla__in a_v12a a_Q1a) (tla__in a_v12a a_Q2a))) :pattern (
    (tla__in a_v12a a_aunde_unde_11a)))))
(assert
  (forall ((a_v13a u))
    (! (=
         (tla__in a_v13a a_aunde_unde_9a)
         (or (tla__in a_v13a a_Q1a) (tla__in a_v13a a_Q2a))) :pattern (
    (tla__in a_v13a a_aunde_unde_9a)))))
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
      (forall ((a_c2a u) (a_aunde_unde_10a u))
        (=>
          (and
            (forall ((a_v14a u))
              (=
                (tla__in a_v14a a_aunde_unde_10a)
                (or
                  (and (tla__in a_v14a a_c1a) (not (tla__in a_v14a a_c2a)))
                  (and (tla__in a_v14a a_c2a) (not (tla__in a_v14a a_c1a))))))
            (forall ((a_v4a u))
              (=> (tla__in a_v4a a_c2a) (tla__in a_v4a Server)))
            (= (int2u 1) (Cardinality a_aunde_unde_10a)))
          (boolify (QuorumsOverlap a_c1a a_c2a)))))))
(assert (forall ((a_v5a u)) (=> (tla__in a_v5a cfg) (tla__in a_v5a Server))))
(assert (tla__in a_Q1a (Quorums cfg)))
(assert (tla__in a_Q2a (Quorums cfg)))
(assert (boolify (IsFiniteSet cfg)))
(assert (boolify (IsFiniteSet a_Q1a)))
(assert (boolify (IsFiniteSet a_Q2a)))
(assert (boolify (IsFiniteSet a_aunde_unde_11a)))
(assert (forall ((a_v6a u)) (=> (tla__in a_v6a a_Q1a) (tla__in a_v6a cfg))))
(assert (forall ((a_v7a u)) (=> (tla__in a_v7a a_Q2a) (tla__in a_v7a cfg))))
(assert
  (forall ((S u))
    (=>
      (boolify (IsFiniteSet S))
      (forall ((T u))
        (=>
          (forall ((a_v8a u)) (=> (tla__in a_v8a T) (tla__in a_v8a S)))
          (and
            (boolify (IsFiniteSet T))
            (tla__le (Cardinality T) (Cardinality S))
            (=> (= (Cardinality S) (Cardinality T)) (= S T))))))))
(assert (boolify (IsFiniteSet Server)))

(check-sat)
(exit)
