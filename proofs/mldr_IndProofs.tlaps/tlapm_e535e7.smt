;; Proof obligation:
;;ASSUME NEW CONSTANT Server,
;;        NEW CONSTANT Secondary,
;;        NEW CONSTANT Primary,
;;        NEW CONSTANT Nil,
;;        NEW CONSTANT InitTerm,
;;        NEW CONSTANT MaxTerm,
;;        NEW CONSTANT MaxLogLen,
;;        NEW CONSTANT MaxConfigVersion,
;;        NEW VARIABLE currentTerm,
;;        NEW VARIABLE state,
;;        NEW VARIABLE log,
;;        NEW VARIABLE immediatelyCommitted,
;;        NEW VARIABLE config,
;;        NEW VARIABLE configVersion,
;;        NEW VARIABLE configTerm,
;;        Term = Nat ,
;;        Version = Nat ,
;;        \A c1, c2 \in SUBSET Server :
;;           1 = Cardinality((c1 \ c2) \cup (c2 \ c1)) => QuorumsOverlap(c1, c2) ,
;;        TypeOK ,
;;        NEW CONSTANT s \in Server,
;;        NEW CONSTANT t \in Server,
;;        NEW CONSTANT nv \in Nat,
;;        NEW CONSTANT nt \in Nat,
;;        SendConfig(s, t, nv, nt) ,
;;        NewerConfig(?h17a541d025099e3943511403ec04a3(t), CV(t)) ,
;;        \A u \in Server : u # t => ?h17a541d025099e3943511403ec04a3(u) = CV(u) ,
;;        \A u \in Server :
;;           NewerOrEqualConfig(?h17a541d025099e3943511403ec04a3(u), CV(u)) 
;; PROVE  /\ NewerConfig(?h17a541d025099e3943511403ec04a3(t), CV(t))
;;        /\ \A u \in Server :
;;              u # t => ?h17a541d025099e3943511403ec04a3(u) = CV(u)
;;        /\ \A u \in Server :
;;              NewerOrEqualConfig(?h17a541d025099e3943511403ec04a3(u), CV(u))
;; TLA+ Proof Manager 1.4.5 (build 33809)
;; Proof obligation #135
;;   generated from file "./mldr_IndProofs.tla", line 292, characters 14-15

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
(declare-fun CV (u) u)
(declare-fun Cardinality (u) u)
(declare-fun NewerConfig (u u) u)
(declare-fun NewerOrEqualConfig (u u) u)
(declare-fun QuorumsOverlap (u u) u)
(declare-fun SendConfig (u u u u) u)
(declare-fun Server () u)
(declare-fun Term () u)
(declare-fun TypeOK () u)
(declare-fun Version () u)
(declare-fun a_aunde_unde_5a () u)
(declare-fun a_h17a541d025099e3943511403ec04a3a (u) u)
(declare-fun nt () Int)
(declare-fun nv () Int)
(declare-fun s () u)
(declare-fun t () u)

(assert
  (forall ((X_9 Int)) (! (= (u2int (int2u X_9)) X_9) :pattern ((int2u X_9)))))
(assert
  (forall ((X_9 u))
  (! (= (tla__in X_9 tla__Int) (exists ((N_8 Int)) (= X_9 (int2u N_8)))) :pattern ((tla__in X_9 tla__Int)))))
(assert
  (forall ((M_7 Int) (N_8 Int))
  (! (= (tla__le (int2u M_7) (int2u N_8)) (<= M_7 N_8)) :pattern ((tla__le (int2u M_7) (int2u N_8))))))
(assert
  (forall ((S_12 u) (T_13 u))
  (=>
  (forall ((X_9 u)) (= (tla__in X_9 S_12) (tla__in X_9 T_13))) (= S_12 T_13))))
(assert (not
  (and
    (forall ((u u))
      (=>
        (and (tla__in u Server) (not (= u t)))
        (= (a_h17a541d025099e3943511403ec04a3a u) (CV u))))
    (forall ((u u))
      (=>
        (tla__in u Server)
        (boolify
          (NewerOrEqualConfig (a_h17a541d025099e3943511403ec04a3a u) (CV u))))))))
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
(assert (boolify TypeOK))
(assert (tla__in s Server))
(assert (tla__in t Server))
(assert (<= 0 nv))
(assert (<= 0 nt))
(assert (boolify (SendConfig s t (int2u nv) (int2u nt))))
(assert
  (boolify (NewerConfig (a_h17a541d025099e3943511403ec04a3a t) (CV t))))
(assert
  (forall ((u u))
    (=>
      (and (tla__in u Server) (not (= u t)))
      (= (a_h17a541d025099e3943511403ec04a3a u) (CV u)))))
(assert
  (forall ((u u))
    (=>
      (tla__in u Server)
      (boolify
        (NewerOrEqualConfig (a_h17a541d025099e3943511403ec04a3a u) (CV u))))))

(check-sat)
(exit)
