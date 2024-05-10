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
;;        /\ currentTerm \in [Server -> Nat]
;;        /\ state \in [Server -> {Secondary, Primary}]
;;        /\ config \in [Server -> SUBSET Server]
;;        /\ configVersion \in [Server -> Nat]
;;        /\ configTerm \in [Server -> Nat]
;;        /\ log \in [Server -> Seq(Nat)]
;;        /\ immediatelyCommitted \in SUBSET Nat \X Nat ,
;;        \/ ClientRequestAction
;;        \/ GetEntriesAction
;;        \/ RollbackEntriesAction
;;        \/ \E s \in Server :
;;              \E Q \in SUBSET Server :
;;                 \E newTerm \in Term :
;;                    /\ newTerm = currentTerm[s] + 1
;;                    /\ Q \in Quorums(config[s])
;;                    /\ s \in config[s]
;;                    /\ s \in Q
;;                    /\ \A v \in Q : CanVoteForConfig(v, s, newTerm)
;;                    /\ \A v \in Q : CanVoteForOplog(v, s, newTerm)
;;                    /\ ?currentTerm#prime
;;                       = [s_1 \in Server |->
;;                            IF s_1 \in Q THEN newTerm ELSE currentTerm[s_1]]
;;                    /\ ?state#prime
;;                       = [s_1 \in Server |->
;;                            IF s_1 = s
;;                              THEN Primary
;;                              ELSE IF s_1 \in Q THEN Secondary ELSE state[s_1]]
;;                    /\ ?configTerm#prime = [configTerm EXCEPT ![s] = newTerm]
;;                    /\ /\ ?log#prime = log
;;                       /\ ?immediatelyCommitted#prime = immediatelyCommitted
;;                       /\ ?config#prime = config
;;                       /\ ?configVersion#prime = configVersion
;;        \/ CommitEntryAction
;;        \/ \E s, t \in Server :
;;              /\ /\ currentTerm[s] > currentTerm[t]
;;                 /\ ?currentTerm#prime
;;                    = [currentTerm EXCEPT ![t] = currentTerm[s]]
;;                 /\ ?state#prime = [state EXCEPT ![t] = Secondary]
;;              /\ /\ ?log#prime = log
;;                 /\ ?immediatelyCommitted#prime = immediatelyCommitted
;;                 /\ ?config#prime = config
;;                 /\ ?configVersion#prime = configVersion
;;                 /\ ?configTerm#prime = configTerm
;;        \/ \E s \in Server, newConfig \in AllConfigs, newVersion \in Version :
;;              /\ state[s] = Primary
;;              /\ ConfigQuorumCheck(s)
;;              /\ TermQuorumCheck(s)
;;              /\ 1
;;                 = Cardinality((newConfig \ config[s])
;;                               \cup (config[s] \ newConfig))
;;              /\ OplogCommitment(s)
;;              /\ s \in newConfig
;;              /\ newConfig # config[s]
;;              /\ newVersion = configVersion[s] + 1
;;              /\ ?configTerm#prime = [configTerm EXCEPT ![s] = currentTerm[s]]
;;              /\ ?configVersion#prime
;;                 = [configVersion EXCEPT ![s] = newVersion]
;;              /\ ?config#prime = [config EXCEPT ![s] = newConfig]
;;              /\ ?currentTerm#prime = currentTerm
;;              /\ ?state#prime = state
;;              /\ ?log#prime = log
;;              /\ ?immediatelyCommitted#prime = immediatelyCommitted
;;        \/ \E s, t \in Server :
;;              /\ state[t] = Secondary
;;              /\ IsNewerConfig(s, t)
;;              /\ ?configVersion#prime
;;                 = [configVersion EXCEPT ![t] = configVersion[s]]
;;              /\ ?configTerm#prime = [configTerm EXCEPT ![t] = configTerm[s]]
;;              /\ ?config#prime = [config EXCEPT ![t] = config[s]]
;;              /\ /\ ?currentTerm#prime = currentTerm
;;                 /\ ?state#prime = state
;;                 /\ ?log#prime = log
;;                 /\ ?immediatelyCommitted#prime = immediatelyCommitted 
;; PROVE  ?configVersion#prime \in [Server -> Nat]
;; TLA+ Proof Manager 1.4.5 (build 33809)
;; Proof obligation #120
;;   generated from file "./mldr_IndProofs.tla", line 231, characters 15-16

(set-logic UFNIA)
(declare-sort u 0)
;; Standard TLA+ operators
(declare-fun int2u (Int) u)
(declare-fun u2int (u) Int)
(declare-fun tla__Int () u)
(declare-fun tla__Nat () u)
(declare-fun tla__plus (u u) u)
(declare-fun tla__lt (u u) Bool)
(declare-fun tla__le (u u) Bool)
(declare-fun tla__Range (u u) u)
(declare-fun boolify (u) Bool)
(declare-fun tla__in (u u) Bool)
(declare-fun tla__emptyset () u)
(declare-fun tla__isAFcn (u) Bool)
(declare-fun tla__DOMAIN (u) u)
(declare-fun tla__fcnapp (u u) u)
(declare-fun tla__unspec (u u) u)
(declare-fun tla__Seq (u) u)
(declare-fun tla__Len (u) Int)

;; Terms, predicates and strings
(declare-fun AllConfigs () u)
(declare-fun CanVoteForConfig (u u u) u)
(declare-fun CanVoteForOplog (u u u) u)
(declare-fun Cardinality (u) u)
(declare-fun ClientRequestAction () u)
(declare-fun CommitEntryAction () u)
(declare-fun ConfigQuorumCheck (u) u)
(declare-fun GetEntriesAction () u)
(declare-fun IsNewerConfig (u u) u)
(declare-fun OplogCommitment (u) u)
(declare-fun Primary () u)
(declare-fun Quorums (u) u)
(declare-fun QuorumsOverlap (u u) u)
(declare-fun RollbackEntriesAction () u)
(declare-fun Secondary () u)
(declare-fun Server () u)
(declare-fun Term () u)
(declare-fun TermQuorumCheck (u) u)
(declare-fun Version () u)
(declare-fun a_aunde_unde_24a () u)
(declare-fun a_aunde_unde_25a () u)
(declare-fun a_aunde_unde_26a () u)
(declare-fun a_configTermhash_primea () u)
(declare-fun a_configVersionhash_primea () u)
(declare-fun a_confighash_primea () u)
(declare-fun a_currentTermhash_primea () u)
(declare-fun a_immediatelyCommittedhash_primea () u)
(declare-fun a_loghash_primea () u)
(declare-fun a_statehash_primea () u)
(declare-fun config () u)
(declare-fun configTerm () u)
(declare-fun configVersion () u)
(declare-fun currentTerm () u)
(declare-fun immediatelyCommitted () u)
(declare-fun log () u)
(declare-fun state () u)

(assert
  (forall ((X_32 Int))
  (! (= (u2int (int2u X_32)) X_32) :pattern ((int2u X_32)))))
(assert
  (forall ((X_32 u))
  (! (= (tla__in X_32 tla__Int) (exists ((N_31 Int)) (= X_32 (int2u N_31)))) :pattern ((tla__in X_32 tla__Int)))))
(assert
  (forall ((X_32 u))
  (! (=
  (tla__in X_32 tla__Nat)
  (exists ((N_31 Int)) (and (= X_32 (int2u N_31)) (<= 0 N_31)))) :pattern ((tla__in X_32 tla__Nat)))))
(assert
  (forall ((M_30 Int) (N_31 Int))
  (! (= (tla__plus (int2u M_30) (int2u N_31)) (int2u (+ M_30 N_31))) :pattern ((tla__plus (int2u M_30) (int2u N_31))))))
(assert
  (forall ((M_30 Int) (N_31 Int))
  (! (= (tla__lt (int2u M_30) (int2u N_31)) (< M_30 N_31)) :pattern ((tla__lt (int2u M_30) (int2u N_31))))))
(assert
  (forall ((M_30 Int) (N_31 Int))
  (! (= (tla__le (int2u M_30) (int2u N_31)) (<= M_30 N_31)) :pattern ((tla__le (int2u M_30) (int2u N_31))))))
(assert
  (forall ((M_30 Int) (N_31 Int) (Z_34 u))
  (=
  (tla__in Z_34 (tla__Range (int2u M_30) (int2u N_31)))
  (exists ((X_32 Int))
  (and (= Z_34 (int2u X_32)) (<= M_30 X_32) (<= X_32 N_31))))))
(assert
  (forall ((M_30 Int) (N_31 Int) (X_32 Int) (Y_33 Int))
  (=>
  (and
  (or (<= M_30 N_31) (<= X_32 Y_33))
  (=
  (tla__Range (int2u M_30) (int2u N_31))
  (tla__Range (int2u X_32) (int2u Y_33))))
  (and (= M_30 X_32) (= N_31 Y_33)))))
(assert
  (forall ((M_30 Int) (N_31 Int))
  (= (= (tla__Range (int2u M_30) (int2u N_31)) tla__emptyset) (< N_31 M_30))))
(assert
  (forall ((S_35 u) (T_36 u))
  (=>
  (forall ((X_32 u)) (= (tla__in X_32 S_35) (tla__in X_32 T_36)))
  (= S_35 T_36))))
(assert
  (forall ((X_32 u))
  (! (= (tla__in X_32 tla__emptyset) false) :pattern ((tla__in X_32 tla__emptyset)))))
(assert
  (forall ((F_38 u) (G_39 u))
  (=>
  (and
  (tla__isAFcn F_38) (tla__isAFcn G_39)
  (forall ((X_32 u))
  (= (tla__in X_32 (tla__DOMAIN F_38)) (tla__in X_32 (tla__DOMAIN G_39)))))
  (= (tla__DOMAIN F_38) (tla__DOMAIN G_39)))))
(assert
  (forall ((F_38 u) (G_39 u))
  (=>
  (and
  (tla__isAFcn F_38) (tla__isAFcn G_39)
  (= (tla__DOMAIN F_38) (tla__DOMAIN G_39))
  (forall ((X_32 u))
  (=>
  (tla__in X_32 (tla__DOMAIN G_39))
  (= (tla__fcnapp F_38 X_32) (tla__fcnapp G_39 X_32)))))
  (= F_38 G_39))))
(assert
  (forall ((S_35 u) (T_36 u))
  (=
  (tla__in S_35 (tla__Seq T_36))
  (and
  (<= 0 (tla__Len S_35)) (tla__isAFcn S_35)
  (= (tla__DOMAIN S_35) (tla__Range (int2u 1) (int2u (tla__Len S_35))))
  (forall ((I_37 Int))
  (=>
  (and (<= 1 I_37) (<= I_37 (tla__Len S_35)))
  (tla__in (tla__fcnapp S_35 (int2u I_37)) T_36)))))))
(assert
  (forall ((S_35 u) (N_31 Int))
  (=>
  (<= 0 N_31)
  (=
  (= (tla__DOMAIN S_35) (tla__Range (int2u 1) (int2u N_31)))
  (= (tla__Len S_35) N_31)))))
(assert (forall ((S_35 u)) (<= 0 (tla__Len S_35))))
(assert (not
  (and
    (tla__isAFcn a_configVersionhash_primea)
    (= (tla__DOMAIN a_configVersionhash_primea) Server)
    (forall ((a_v23a u))
      (=>
        (tla__in a_v23a Server)
        (and
          (tla__in (tla__fcnapp a_configVersionhash_primea a_v23a) tla__Int)
          (tla__le (int2u 0) (tla__fcnapp a_configVersionhash_primea a_v23a))))))))
(assert
  (forall ((a_v27a u))
    (! (=
         (tla__in a_v27a a_aunde_unde_25a)
         (or (= a_v27a (int2u 1)) (= a_v27a (int2u 2)))) :pattern ((tla__in
                                                                    a_v27a
                                                                    a_aunde_unde_25a)))))
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
      (forall ((a_c2a u) (a_aunde_unde_24a u))
        (=>
          (and
            (forall ((a_v28a u))
              (=
                (tla__in a_v28a a_aunde_unde_24a)
                (or
                  (and (tla__in a_v28a a_c1a) (not (tla__in a_v28a a_c2a)))
                  (and (tla__in a_v28a a_c2a) (not (tla__in a_v28a a_c1a))))))
            (forall ((a_v4a u))
              (=> (tla__in a_v4a a_c2a) (tla__in a_v4a Server)))
            (= (int2u 1) (Cardinality a_aunde_unde_24a)))
          (boolify (QuorumsOverlap a_c1a a_c2a)))))))
(assert (tla__isAFcn currentTerm))
(assert (= (tla__DOMAIN currentTerm) Server))
(assert
  (forall ((a_v5a u))
    (=>
      (tla__in a_v5a Server)
      (and
        (tla__in (tla__fcnapp currentTerm a_v5a) tla__Int)
        (tla__le (int2u 0) (tla__fcnapp currentTerm a_v5a))))))
(assert (tla__isAFcn state))
(assert (= (tla__DOMAIN state) Server))
(assert
  (forall ((a_v6a u))
    (=>
      (tla__in a_v6a Server)
      (or
        (= (tla__fcnapp state a_v6a) Secondary)
        (= (tla__fcnapp state a_v6a) Primary)))))
(assert (tla__isAFcn config))
(assert (= (tla__DOMAIN config) Server))
(assert
  (forall ((a_v7a u))
    (=>
      (tla__in a_v7a Server)
      (forall ((a_v8a u))
        (=>
          (tla__in a_v8a (tla__fcnapp config a_v7a)) (tla__in a_v8a Server))))))
(assert (tla__isAFcn configVersion))
(assert (= (tla__DOMAIN configVersion) Server))
(assert
  (forall ((a_v9a u))
    (=>
      (tla__in a_v9a Server)
      (and
        (tla__in (tla__fcnapp configVersion a_v9a) tla__Int)
        (tla__le (int2u 0) (tla__fcnapp configVersion a_v9a))))))
(assert (tla__isAFcn configTerm))
(assert (= (tla__DOMAIN configTerm) Server))
(assert
  (forall ((a_v10a u))
    (=>
      (tla__in a_v10a Server)
      (and
        (tla__in (tla__fcnapp configTerm a_v10a) tla__Int)
        (tla__le (int2u 0) (tla__fcnapp configTerm a_v10a))))))
(assert (tla__isAFcn log))
(assert (= (tla__DOMAIN log) Server))
(assert
  (forall ((a_v11a u))
    (=>
      (tla__in a_v11a Server)
      (tla__in (tla__fcnapp log a_v11a) (tla__Seq tla__Nat)))))
(assert
  (forall ((a_v12a u))
    (=>
      (tla__in a_v12a immediatelyCommitted)
      (and
        (tla__isAFcn a_v12a) (= (tla__DOMAIN a_v12a) a_aunde_unde_25a)
        (tla__in (tla__fcnapp a_v12a (int2u 1)) tla__Int)
        (tla__le (int2u 0) (tla__fcnapp a_v12a (int2u 1)))
        (tla__in (tla__fcnapp a_v12a (int2u 2)) tla__Int)
        (tla__le (int2u 0) (tla__fcnapp a_v12a (int2u 2)))))))
(assert
  (or
    (boolify ClientRequestAction) (boolify GetEntriesAction)
    (boolify RollbackEntriesAction)
    (exists ((s u))
      (and
        (tla__in s Server)
        (exists ((Q u))
          (and
            (forall ((a_v13a u))
              (=> (tla__in a_v13a Q) (tla__in a_v13a Server)))
            (exists ((newTerm Int))
              (and
                (ite
                  (tla__in s Server)
                  (and
                    (=
                      (int2u newTerm)
                      (tla__plus (tla__fcnapp currentTerm s) (int2u 1)))
                    (tla__in s (tla__fcnapp config s)))
                  (and
                    (=
                      (int2u newTerm)
                      (tla__plus (tla__unspec currentTerm s) (int2u 1)))
                    (tla__in s (tla__unspec config s)))) (<= 0 newTerm)
                (tla__in
                  Q
                  (Quorums
                    (ite
                      (tla__in s Server) (tla__fcnapp config s)
                      (tla__unspec config s)))) (tla__in s Q)
                (forall ((v u))
                  (=>
                    (tla__in v Q)
                    (boolify (CanVoteForConfig v s (int2u newTerm)))))
                (forall ((v u))
                  (=>
                    (tla__in v Q)
                    (boolify (CanVoteForOplog v s (int2u newTerm)))))
                (tla__isAFcn a_currentTermhash_primea)
                (= (tla__DOMAIN a_currentTermhash_primea) Server)
                (forall ((a_sunde_1a u))
                  (=>
                    (tla__in a_sunde_1a Server)
                    (ite
                      (tla__in a_sunde_1a Q)
                      (=
                        (tla__fcnapp a_currentTermhash_primea a_sunde_1a)
                        (int2u newTerm))
                      (=
                        (tla__fcnapp a_currentTermhash_primea a_sunde_1a)
                        (tla__fcnapp currentTerm a_sunde_1a)))))
                (tla__isAFcn a_statehash_primea)
                (= (tla__DOMAIN a_statehash_primea) Server)
                (forall ((a_sunde_1a u))
                  (=>
                    (tla__in a_sunde_1a Server)
                    (ite
                      (= a_sunde_1a s)
                      (= (tla__fcnapp a_statehash_primea a_sunde_1a) Primary)
                      (ite
                        (tla__in a_sunde_1a Q)
                        (=
                          (tla__fcnapp a_statehash_primea a_sunde_1a)
                          Secondary)
                        (=
                          (tla__fcnapp a_statehash_primea a_sunde_1a)
                          (tla__fcnapp state a_sunde_1a))))))
                (tla__isAFcn a_configTermhash_primea)
                (= Server (tla__DOMAIN a_configTermhash_primea))
                (=>
                  (tla__in s Server)
                  (= (tla__fcnapp a_configTermhash_primea s) (int2u newTerm)))
                (forall ((a_v14a u))
                  (=>
                    (and (tla__in a_v14a Server) (not (= a_v14a s)))
                    (=
                      (tla__fcnapp configTerm a_v14a)
                      (tla__fcnapp a_configTermhash_primea a_v14a))))
                (= a_loghash_primea log)
                (= a_immediatelyCommittedhash_primea immediatelyCommitted)
                (= a_confighash_primea config)
                (= a_configVersionhash_primea configVersion)))))))
    (boolify CommitEntryAction)
    (exists ((s u))
      (and
        (tla__in s Server)
        (exists ((t u))
          (and
            (tla__in t Server)
            (tla__lt
              (ite
                (tla__in t Server) (tla__fcnapp currentTerm t)
                (tla__unspec currentTerm t))
              (ite
                (tla__in s Server) (tla__fcnapp currentTerm s)
                (tla__unspec currentTerm s)))
            (tla__isAFcn a_currentTermhash_primea)
            (= Server (tla__DOMAIN a_currentTermhash_primea))
            (=>
              (tla__in t Server)
              (ite
                (tla__in s Server)
                (=
                  (tla__fcnapp a_currentTermhash_primea t)
                  (tla__fcnapp currentTerm s))
                (=
                  (tla__fcnapp a_currentTermhash_primea t)
                  (tla__unspec currentTerm s))))
            (forall ((a_v15a u))
              (=>
                (and (tla__in a_v15a Server) (not (= a_v15a t)))
                (=
                  (tla__fcnapp currentTerm a_v15a)
                  (tla__fcnapp a_currentTermhash_primea a_v15a))))
            (tla__isAFcn a_statehash_primea)
            (= Server (tla__DOMAIN a_statehash_primea))
            (=>
              (tla__in t Server)
              (= (tla__fcnapp a_statehash_primea t) Secondary))
            (forall ((a_v16a u))
              (=>
                (and (tla__in a_v16a Server) (not (= a_v16a t)))
                (=
                  (tla__fcnapp state a_v16a)
                  (tla__fcnapp a_statehash_primea a_v16a))))
            (= a_loghash_primea log)
            (= a_immediatelyCommittedhash_primea immediatelyCommitted)
            (= a_confighash_primea config)
            (= a_configVersionhash_primea configVersion)
            (= a_configTermhash_primea configTerm)))))
    (exists ((s u))
      (and
        (tla__in s Server)
        (exists ((newConfig u))
          (forall ((a_aunde_unde_26a u))
            (=>
              (forall ((a_v29a u))
                (=
                  (tla__in a_v29a a_aunde_unde_26a)
                  (or
                    (and
                      (tla__in a_v29a newConfig)
                      (ite
                        (tla__in s Server)
                        (not (tla__in a_v29a (tla__fcnapp config s)))
                        (not (tla__in a_v29a (tla__unspec config s)))))
                    (and
                      (ite
                        (tla__in s Server)
                        (tla__in a_v29a (tla__fcnapp config s))
                        (tla__in a_v29a (tla__unspec config s)))
                      (not (tla__in a_v29a newConfig))))))
              (and
                (tla__in newConfig AllConfigs)
                (exists ((newVersion Int))
                  (and
                    (ite
                      (tla__in s Server)
                      (and
                        (= (tla__fcnapp state s) Primary)
                        (not (= newConfig (tla__fcnapp config s)))
                        (=
                          (int2u newVersion)
                          (tla__plus (tla__fcnapp configVersion s) (int2u 1))))
                      (and
                        (= (tla__unspec state s) Primary)
                        (not (= newConfig (tla__unspec config s)))
                        (=
                          (int2u newVersion)
                          (tla__plus (tla__unspec configVersion s) (int2u 1)))))
                    (<= 0 newVersion) (boolify (ConfigQuorumCheck s))
                    (boolify (TermQuorumCheck s))
                    (= (int2u 1) (Cardinality a_aunde_unde_26a))
                    (boolify (OplogCommitment s)) (tla__in s newConfig)
                    (tla__isAFcn a_configTermhash_primea)
                    (= Server (tla__DOMAIN a_configTermhash_primea))
                    (=>
                      (tla__in s Server)
                      (ite
                        (tla__in s Server)
                        (=
                          (tla__fcnapp a_configTermhash_primea s)
                          (tla__fcnapp currentTerm s))
                        (=
                          (tla__fcnapp a_configTermhash_primea s)
                          (tla__unspec currentTerm s))))
                    (forall ((a_v17a u))
                      (=>
                        (and (tla__in a_v17a Server) (not (= a_v17a s)))
                        (=
                          (tla__fcnapp configTerm a_v17a)
                          (tla__fcnapp a_configTermhash_primea a_v17a))))
                    (tla__isAFcn a_configVersionhash_primea)
                    (= Server (tla__DOMAIN a_configVersionhash_primea))
                    (=>
                      (tla__in s Server)
                      (=
                        (tla__fcnapp a_configVersionhash_primea s)
                        (int2u newVersion)))
                    (forall ((a_v18a u))
                      (=>
                        (and (tla__in a_v18a Server) (not (= a_v18a s)))
                        (=
                          (tla__fcnapp configVersion a_v18a)
                          (tla__fcnapp a_configVersionhash_primea a_v18a))))
                    (tla__isAFcn a_confighash_primea)
                    (= Server (tla__DOMAIN a_confighash_primea))
                    (=>
                      (tla__in s Server)
                      (= (tla__fcnapp a_confighash_primea s) newConfig))
                    (forall ((a_v19a u))
                      (=>
                        (and (tla__in a_v19a Server) (not (= a_v19a s)))
                        (=
                          (tla__fcnapp config a_v19a)
                          (tla__fcnapp a_confighash_primea a_v19a))))
                    (= a_currentTermhash_primea currentTerm)
                    (= a_statehash_primea state) (= a_loghash_primea log)
                    (=
                      a_immediatelyCommittedhash_primea immediatelyCommitted)))))))))
    (exists ((s u))
      (and
        (tla__in s Server)
        (exists ((t u))
          (and
            (tla__in t Server)
            (ite
              (tla__in t Server) (= (tla__fcnapp state t) Secondary)
              (= (tla__unspec state t) Secondary))
            (boolify (IsNewerConfig s t))
            (tla__isAFcn a_configVersionhash_primea)
            (= Server (tla__DOMAIN a_configVersionhash_primea))
            (=>
              (tla__in t Server)
              (ite
                (tla__in s Server)
                (=
                  (tla__fcnapp a_configVersionhash_primea t)
                  (tla__fcnapp configVersion s))
                (=
                  (tla__fcnapp a_configVersionhash_primea t)
                  (tla__unspec configVersion s))))
            (forall ((a_v20a u))
              (=>
                (and (tla__in a_v20a Server) (not (= a_v20a t)))
                (=
                  (tla__fcnapp configVersion a_v20a)
                  (tla__fcnapp a_configVersionhash_primea a_v20a))))
            (tla__isAFcn a_configTermhash_primea)
            (= Server (tla__DOMAIN a_configTermhash_primea))
            (=>
              (tla__in t Server)
              (ite
                (tla__in s Server)
                (=
                  (tla__fcnapp a_configTermhash_primea t)
                  (tla__fcnapp configTerm s))
                (=
                  (tla__fcnapp a_configTermhash_primea t)
                  (tla__unspec configTerm s))))
            (forall ((a_v21a u))
              (=>
                (and (tla__in a_v21a Server) (not (= a_v21a t)))
                (=
                  (tla__fcnapp configTerm a_v21a)
                  (tla__fcnapp a_configTermhash_primea a_v21a))))
            (tla__isAFcn a_confighash_primea)
            (= Server (tla__DOMAIN a_confighash_primea))
            (=>
              (tla__in t Server)
              (ite
                (tla__in s Server)
                (=
                  (tla__fcnapp a_confighash_primea t) (tla__fcnapp config s))
                (=
                  (tla__fcnapp a_confighash_primea t) (tla__unspec config s))))
            (forall ((a_v22a u))
              (=>
                (and (tla__in a_v22a Server) (not (= a_v22a t)))
                (=
                  (tla__fcnapp config a_v22a)
                  (tla__fcnapp a_confighash_primea a_v22a))))
            (= a_currentTermhash_primea currentTerm)
            (= a_statehash_primea state) (= a_loghash_primea log)
            (= a_immediatelyCommittedhash_primea immediatelyCommitted)))))))

(check-sat)
(exit)
