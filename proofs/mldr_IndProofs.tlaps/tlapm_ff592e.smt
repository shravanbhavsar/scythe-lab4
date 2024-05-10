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
;;        IndAuto ,
;;        Next ,
;;        NEW CONSTANT s \in Server,
;;        ?configTerm#prime[s] > configTerm[s] ,
;;        ?configVersion#prime[s] = configVersion[s] 
;; PROVE  \/ <<?configVersion#prime[s], ?configTerm#prime[s]>>[2]
;;           > <<configVersion[s], configTerm[s]>>[2]
;;        \/ /\ <<?configVersion#prime[s], ?configTerm#prime[s]>>[2]
;;              = <<configVersion[s], configTerm[s]>>[2]
;;           /\ <<?configVersion#prime[s], ?configTerm#prime[s]>>[1]
;;              > <<configVersion[s], configTerm[s]>>[1]
;; TLA+ Proof Manager 1.4.5 (build 33809)
;; Proof obligation #180
;;   generated from file "./mldr_IndProofs.tla", line 325, characters 22-23

(set-logic UFNIA)
(declare-sort u 0)
;; Standard TLA+ operators
(declare-fun int2u (Int) u)
(declare-fun u2int (u) Int)
(declare-fun tla__Int () u)
(declare-fun tla__lt (u u) Bool)
(declare-fun tla__le (u u) Bool)
(declare-fun boolify (u) Bool)
(declare-fun tla__in (u u) Bool)
(declare-fun tla__isAFcn (u) Bool)
(declare-fun tla__DOMAIN (u) u)
(declare-fun tla__fcnapp (u u) u)
(declare-fun tla__unspec (u u) u)

;; Terms, predicates and strings
(declare-fun Cardinality (u) u)
(declare-fun IndAuto () u)
(declare-fun Next () u)
(declare-fun QuorumsOverlap (u u) u)
(declare-fun Server () u)
(declare-fun Term () u)
(declare-fun Version () u)
(declare-fun a_aunde_unde_5a () u)
(declare-fun a_configTermhash_primea () u)
(declare-fun a_configVersionhash_primea () u)
(declare-fun configTerm () u)
(declare-fun configVersion () u)
(declare-fun s () u)

(assert
  (forall ((X_9 Int)) (! (= (u2int (int2u X_9)) X_9) :pattern ((int2u X_9)))))
(assert
  (forall ((X_9 u))
  (! (= (tla__in X_9 tla__Int) (exists ((N_8 Int)) (= X_9 (int2u N_8)))) :pattern ((tla__in X_9 tla__Int)))))
(assert
  (forall ((M_7 Int) (N_8 Int))
  (! (= (tla__lt (int2u M_7) (int2u N_8)) (< M_7 N_8)) :pattern ((tla__lt (int2u M_7) (int2u N_8))))))
(assert
  (forall ((M_7 Int) (N_8 Int))
  (! (= (tla__le (int2u M_7) (int2u N_8)) (<= M_7 N_8)) :pattern ((tla__le (int2u M_7) (int2u N_8))))))
(assert
  (forall ((S_12 u) (T_13 u))
  (=>
  (forall ((X_9 u)) (= (tla__in X_9 S_12) (tla__in X_9 T_13))) (= S_12 T_13))))
(assert
  (forall ((F_15 u) (G_16 u))
  (=>
  (and
  (tla__isAFcn F_15) (tla__isAFcn G_16)
  (forall ((X_9 u))
  (= (tla__in X_9 (tla__DOMAIN F_15)) (tla__in X_9 (tla__DOMAIN G_16)))))
  (= (tla__DOMAIN F_15) (tla__DOMAIN G_16)))))
(assert
  (forall ((F_15 u) (G_16 u))
  (=>
  (and
  (tla__isAFcn F_15) (tla__isAFcn G_16)
  (= (tla__DOMAIN F_15) (tla__DOMAIN G_16))
  (forall ((X_9 u))
  (=>
  (tla__in X_9 (tla__DOMAIN G_16))
  (= (tla__fcnapp F_15 X_9) (tla__fcnapp G_16 X_9)))))
  (= F_15 G_16))))
(assert (not
  (or
    (tla__lt
      (ite
        (tla__in s (tla__DOMAIN configTerm)) (tla__fcnapp configTerm s)
        (tla__unspec configTerm s))
      (ite
        (tla__in s (tla__DOMAIN a_configTermhash_primea))
        (tla__fcnapp a_configTermhash_primea s)
        (tla__unspec a_configTermhash_primea s)))
    (and
      (=
        (ite
          (tla__in s (tla__DOMAIN a_configTermhash_primea))
          (tla__fcnapp a_configTermhash_primea s)
          (tla__unspec a_configTermhash_primea s))
        (ite
          (tla__in s (tla__DOMAIN configTerm)) (tla__fcnapp configTerm s)
          (tla__unspec configTerm s)))
      (ite
        (tla__in s (tla__DOMAIN configVersion))
        (tla__lt (tla__fcnapp configVersion s) (tla__fcnapp configVersion s))
        (tla__lt (tla__unspec configVersion s) (tla__unspec configVersion s)))))))
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
      (forall ((a_c2a u) (a_aunde_unde_5a u))
        (=>
          (and
            (forall ((a_v6a u))
              (=
                (tla__in a_v6a a_aunde_unde_5a)
                (or
                  (and (tla__in a_v6a a_c1a) (not (tla__in a_v6a a_c2a)))
                  (and (tla__in a_v6a a_c2a) (not (tla__in a_v6a a_c1a))))))
            (forall ((a_v4a u))
              (=> (tla__in a_v4a a_c2a) (tla__in a_v4a Server)))
            (= (int2u 1) (Cardinality a_aunde_unde_5a)))
          (boolify (QuorumsOverlap a_c1a a_c2a)))))))
(assert (boolify IndAuto))
(assert (boolify Next))
(assert (tla__in s Server))
(assert
  (tla__lt
    (ite
      (tla__in s (tla__DOMAIN configTerm)) (tla__fcnapp configTerm s)
      (tla__unspec configTerm s))
    (ite
      (tla__in s (tla__DOMAIN a_configTermhash_primea))
      (tla__fcnapp a_configTermhash_primea s)
      (tla__unspec a_configTermhash_primea s))))
(assert
  (=
    (ite
      (tla__in s (tla__DOMAIN a_configVersionhash_primea))
      (tla__fcnapp a_configVersionhash_primea s)
      (tla__unspec a_configVersionhash_primea s))
    (ite
      (tla__in s (tla__DOMAIN configVersion)) (tla__fcnapp configVersion s)
      (tla__unspec configVersion s))))

(check-sat)
(exit)
