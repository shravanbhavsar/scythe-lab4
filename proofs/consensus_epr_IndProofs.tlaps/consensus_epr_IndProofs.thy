(* automatically generated -- do not edit manually *)
theory consensus_epr_IndProofs imports Constant Zenon begin
ML_command {* writeln ("*** TLAPS PARSED\n"); *}
consts
  "isReal" :: c
  "isa_slas_a" :: "[c,c] => c"
  "isa_bksl_diva" :: "[c,c] => c"
  "isa_perc_a" :: "[c,c] => c"
  "isa_peri_peri_a" :: "[c,c] => c"
  "isInfinity" :: c
  "isa_lbrk_rbrk_a" :: "[c] => c"
  "isa_less_more_a" :: "[c] => c"

lemma ob'117:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
fixes Node
fixes Quorum
fixes Value
fixes a_voteunde_requestunde_msga a_voteunde_requestunde_msga'
fixes voted voted'
fixes a_voteunde_msga a_voteunde_msga'
fixes votes votes'
fixes leader leader'
fixes decided decided'
fixes a_requnde_historya a_requnde_historya'
(* usable definition vars suppressed *)
(* usable definition IgnoreRequestVote suppressed *)
(* usable definition ProtocolNext suppressed *)
(* usable definition OtherNext suppressed *)
(* usable definition Spec suppressed *)
(* usable definition Symmetry suppressed *)
(* usable definition Safety suppressed *)
(* usable definition SplitVote suppressed *)
(* usable definition Liveness suppressed *)
assumes v'29: "(((((((a_voteunde_requestunde_msga) \<in> ((SUBSET (((Node) \<times> (Node))))))) & (((voted) \<in> ([(Node) \<rightarrow> (BOOLEAN)]))) & (((a_voteunde_msga) \<in> ((SUBSET (((Node) \<times> (Node))))))) & (((votes) \<in> ([(Node) \<rightarrow> ((SUBSET (Node)))]))) & (((leader) \<in> ([(Node) \<rightarrow> (BOOLEAN)]))) & (((decided) \<in> ([(Node) \<rightarrow> ((SUBSET (Value)))])))) & (\<forall> a_n1a \<in> (Node) : (\<forall> a_n2a \<in> (Node) : (\<forall> a_v1a \<in> (Value) : (\<forall> a_v2a \<in> (Value) : (((((((a_v1a) \<in> (fapply ((decided), (a_n1a))))) \<and> (((a_v2a) \<in> (fapply ((decided), (a_n2a))))))) \<Rightarrow> (((a_v1a) = (a_v2a))))))))) & (\<forall> VARI \<in> (Node) : (\<forall> VARJ \<in> (Node) : (((((<<(VARJ), (VARI)>>) \<in> (a_voteunde_msga))) \<or> ((~ (((VARJ) \<in> (fapply ((votes), (VARI))))))))))) & (\<forall> VARI \<in> (Node) : (\<exists> QJ \<in> (Quorum) : (\<forall> VALI \<in> (Value) : (((((QJ) \<subseteq> (fapply ((votes), (VARI))))) \<or> ((~ (((VALI) \<in> (fapply ((decided), (VARI)))))))))))) & (\<forall> VARI \<in> (Node) : (\<forall> VARJ \<in> (Node) : (((fapply ((voted), (VARI))) \<or> ((~ (((<<(VARI), (VARJ)>>) \<in> (a_voteunde_msga))))))))) & (\<forall> VARI \<in> (Node) : (\<exists> QJ \<in> (Quorum) : (((((QJ) \<subseteq> (fapply ((votes), (VARI))))) \<or> ((~ (fapply ((leader), (VARI))))))))) & (\<forall> VARI \<in> (Node) : (\<forall> VALI \<in> (Value) : (((fapply ((leader), (VARI))) \<or> ((~ (((VALI) \<in> (fapply ((decided), (VARI))))))))))) & (\<forall> VARI \<in> (Node) : (\<forall> VARJ \<in> (Node) : (\<forall> VARK \<in> (Node) : (((((((((VARI) = (VARK))) \<and> (((votes) = (votes))))) \<or> ((~ (((<<(VARJ), (VARI)>>) \<in> (a_voteunde_msga))))))) \<or> ((~ (((VARJ) \<in> (fapply ((votes), (VARK)))))))))))) & (\<forall> VARI \<in> (Node) : (\<forall> VARJ \<in> (Node) : (\<forall> VARK \<in> (Node) : (((((((((VARJ) = (VARK))) \<and> (((votes) = (votes))))) \<or> ((~ (((<<(VARI), (VARK)>>) \<in> (a_voteunde_msga))))))) \<or> ((~ (((<<(VARI), (VARJ)>>) \<in> (a_voteunde_msga))))))))))) \<and> (((ProtocolNext) \<or> (OtherNext)))))"
assumes v'41: "(\<exists> i \<in> (Node) : (\<exists> j \<in> (Node) : (((~ (fapply ((voted), (i))))) & (((<<(j), (i)>>) \<in> (a_voteunde_requestunde_msga))) & ((((a_voteunde_requestunde_msghash_primea :: c)) = (((a_voteunde_requestunde_msga) \\ ({(<<(j), (i)>>)}))))) & ((((a_voteunde_msghash_primea :: c)) = (((a_voteunde_msga) \<union> ({(<<(i), (j)>>)}))))) & ((((a_votedhash_primea :: c)) = ([(voted) EXCEPT ![(i)] = (TRUE)]))) & ((((a_voteshash_primea :: c)) = (votes))) & ((((a_decidedhash_primea :: c)) = (decided))) & ((((a_leaderhash_primea :: c)) = (leader))) & ((((a_requnde_historyhash_primea :: c)) = (a_requnde_historya))))))"
shows "(\<forall> VARI \<in> (Node) : (\<forall> VARJ \<in> (Node) : (((((<<(VARJ), (VARI)>>) \<in> ((a_voteunde_msghash_primea :: c)))) \<or> ((~ (((VARJ) \<in> (fapply (((a_voteshash_primea :: c)), (VARI)))))))))))"(is "PROP ?ob'117")
proof -
ML_command {* writeln "*** TLAPS ENTER 117"; *}
show "PROP ?ob'117"

(* BEGIN ZENON INPUT
;; file=consensus_epr_IndProofs.tlaps/tlapm_b4a62c.znn; PATH='/home/egolf/.opam/4.07.1/bin:/home/egolf/.local/bin:/home/egolf/bin:/home/egolf/mambaforge/bin:/home/egolf/mambaforge/condabin:/home/egolf/.opam/4.07.1/bin:/home/egolf/.local/bin:/home/egolf/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/home/egolf/.local/bin/gurobi952/linux64/bin:/home/egolf/Projects/apalache/bin:/home/egolf/opt/foxitsoftware/foxitreader:/home/egolf/.local/bin/gurobi952/linux64/bin:/home/egolf/Projects/apalache/bin:/home/egolf/opt/foxitsoftware/foxitreader:/usr/local/bin:/usr/local/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >consensus_epr_IndProofs.tlaps/tlapm_b4a62c.znn.out
;; obligation #117
$hyp "v'29" (/\ (/\ (/\ (TLA.in a_voteunde_requestunde_msga
(TLA.SUBSET (TLA.prod Node Node))) (TLA.in voted
(TLA.FuncSet Node (TLA.set T. F.))) (TLA.in a_voteunde_msga
(TLA.SUBSET (TLA.prod Node Node))) (TLA.in votes
(TLA.FuncSet Node (TLA.SUBSET Node))) (TLA.in leader
(TLA.FuncSet Node (TLA.set T. F.))) (TLA.in decided
(TLA.FuncSet Node (TLA.SUBSET Value))))
(TLA.bAll Node ((a_n1a) (TLA.bAll Node ((a_n2a) (TLA.bAll Value ((a_v1a) (TLA.bAll Value ((a_v2a) (=> (/\ (TLA.in a_v1a
(TLA.fapply decided a_n1a)) (TLA.in a_v2a (TLA.fapply decided a_n2a)))
(= a_v1a a_v2a))))))))))
(TLA.bAll Node ((VARI) (TLA.bAll Node ((VARJ) (\/ (TLA.in (TLA.tuple VARJ
VARI) a_voteunde_msga) (-. (TLA.in VARJ (TLA.fapply votes VARI))))))))
(TLA.bAll Node ((VARI) (TLA.bEx Quorum ((QJ) (TLA.bAll Value ((VALI) (\/ (TLA.subseteq QJ
(TLA.fapply votes VARI)) (-. (TLA.in VALI (TLA.fapply decided VARI))))))))))
(TLA.bAll Node ((VARI) (TLA.bAll Node ((VARJ) (\/ (TLA.fapply voted VARI)
(-. (TLA.in (TLA.tuple VARI VARJ) a_voteunde_msga)))))))
(TLA.bAll Node ((VARI) (TLA.bEx Quorum ((QJ) (\/ (TLA.subseteq QJ
(TLA.fapply votes VARI)) (-. (TLA.fapply leader VARI)))))))
(TLA.bAll Node ((VARI) (TLA.bAll Value ((VALI) (\/ (TLA.fapply leader VARI)
(-. (TLA.in VALI (TLA.fapply decided VARI))))))))
(TLA.bAll Node ((VARI) (TLA.bAll Node ((VARJ) (TLA.bAll Node ((VARK) (\/ (\/ (/\ (= VARI
VARK) (= votes votes)) (-. (TLA.in (TLA.tuple VARJ VARI) a_voteunde_msga)))
(-. (TLA.in VARJ (TLA.fapply votes VARK))))))))))
(TLA.bAll Node ((VARI) (TLA.bAll Node ((VARJ) (TLA.bAll Node ((VARK) (\/ (\/ (/\ (= VARJ
VARK) (= votes votes)) (-. (TLA.in (TLA.tuple VARI VARK) a_voteunde_msga)))
(-. (TLA.in (TLA.tuple VARI VARJ) a_voteunde_msga)))))))))) (\/ ProtocolNext
OtherNext))
$hyp "v'41" (TLA.bEx Node ((i) (TLA.bEx Node ((j) (/\ (-. (TLA.fapply voted i))
(TLA.in (TLA.tuple j i) a_voteunde_requestunde_msga)
(= a_voteunde_requestunde_msghash_primea
(TLA.setminus a_voteunde_requestunde_msga (TLA.set (TLA.tuple j i))))
(= a_voteunde_msghash_primea (TLA.cup a_voteunde_msga (TLA.set (TLA.tuple i
j)))) (= a_votedhash_primea (TLA.except voted i T.)) (= a_voteshash_primea
votes) (= a_decidedhash_primea decided) (= a_leaderhash_primea leader)
(= a_requnde_historyhash_primea
a_requnde_historya))))))
$goal (TLA.bAll Node ((VARI) (TLA.bAll Node ((VARJ) (\/ (TLA.in (TLA.tuple VARJ
VARI) a_voteunde_msghash_primea) (-. (TLA.in VARJ
(TLA.fapply a_voteshash_primea VARI))))))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Ha:"((((a_voteunde_requestunde_msga \\in SUBSET(prod(Node, Node)))&((voted \\in FuncSet(Node, {TRUE, FALSE}))&((a_voteunde_msga \\in SUBSET(prod(Node, Node)))&((votes \\in FuncSet(Node, SUBSET(Node)))&((leader \\in FuncSet(Node, {TRUE, FALSE}))&(decided \\in FuncSet(Node, SUBSET(Value))))))))&(bAll(Node, (\<lambda>a_n1a. bAll(Node, (\<lambda>a_n2a. bAll(Value, (\<lambda>a_v1a. bAll(Value, (\<lambda>a_v2a. (((a_v1a \\in (decided[a_n1a]))&(a_v2a \\in (decided[a_n2a])))=>(a_v1a=a_v2a))))))))))&(bAll(Node, (\<lambda>VARI. bAll(Node, (\<lambda>VARJ. ((<<VARJ, VARI>> \\in a_voteunde_msga)|(~(VARJ \\in (votes[VARI]))))))))&(bAll(Node, (\<lambda>VARI. bEx(Quorum, (\<lambda>QJ. bAll(Value, (\<lambda>VALI. ((QJ \\subseteq (votes[VARI]))|(~(VALI \\in (decided[VARI]))))))))))&(bAll(Node, (\<lambda>VARI. bAll(Node, (\<lambda>VARJ. ((voted[VARI])|(~(<<VARI, VARJ>> \\in a_voteunde_msga)))))))&(bAll(Node, (\<lambda>VARI. bEx(Quorum, (\<lambda>QJ. ((QJ \\subseteq (votes[VARI]))|(~(leader[VARI])))))))&(bAll(Node, (\<lambda>VARI. bAll(Value, (\<lambda>VALI. ((leader[VARI])|(~(VALI \\in (decided[VARI]))))))))&(bAll(Node, (\<lambda>VARI. bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARI=VARK)&(votes=votes))|(~(<<VARJ, VARI>> \\in a_voteunde_msga)))|(~(VARJ \\in (votes[VARK]))))))))))&bAll(Node, (\<lambda>VARI. bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(votes=votes))|(~(<<VARI, VARK>> \\in a_voteunde_msga)))|(~(<<VARI, VARJ>> \\in a_voteunde_msga)))))))))))))))))&(ProtocolNext|OtherNext))" (is "?z_hd&?z_hff")
 using v'29 by blast
 have z_Hb:"bEx(Node, (\<lambda>i. bEx(Node, (\<lambda>j. ((~(voted[i]))&((<<j, i>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, i>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<i, j>>}))&((a_votedhash_primea=except(voted, i, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))" (is "?z_hb")
 using v'41 by blast
 have zenon_L1_: "((a_voteshash_primea[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))])~=(votes[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))])) ==> (a_voteshash_primea=votes) ==> FALSE" (is "?z_hgu ==> ?z_hgj ==> FALSE")
 proof -
  assume z_Hgu:"?z_hgu" (is "?z_hgv~=?z_hhj")
  assume z_Hgj:"?z_hgj"
  show FALSE
  proof (rule zenon_noteq [of "?z_hhj"])
   have z_Hhk: "(?z_hhj~=?z_hhj)"
   by (rule subst [where P="(\<lambda>zenon_Vkk. ((zenon_Vkk[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))])~=?z_hhj))", OF z_Hgj], fact z_Hgu)
   thus "(?z_hhj~=?z_hhj)" .
  qed
 qed
 assume z_Hc:"(~bAll(Node, (\<lambda>VARI. bAll(Node, (\<lambda>VARJ. ((<<VARJ, VARI>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[VARI])))))))))" (is "~?z_hhp")
 have z_Hd: "?z_hd" (is "?z_he&?z_hbh")
 by (rule zenon_and_0 [OF z_Ha])
 have z_Hbh: "?z_hbh" (is "?z_hbi&?z_hcb")
 by (rule zenon_and_1 [OF z_Hd])
 have z_Hcb: "?z_hcb" (is "?z_hcc&?z_hco")
 by (rule zenon_and_1 [OF z_Hbh])
 have z_Hcc: "?z_hcc"
 by (rule zenon_and_0 [OF z_Hcb])
 have z_Hhy_z_Hcc: "(\\A x:((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msga)|(~(VARJ \\in (votes[x])))))))) == ?z_hcc" (is "?z_hhy == _")
 by (unfold bAll_def)
 have z_Hhy: "?z_hhy" (is "\\A x : ?z_hih(x)")
 by (unfold z_Hhy_z_Hcc, fact z_Hcc)
 have z_Hii_z_Hb: "(\\E x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))) == ?z_hb" (is "?z_hii == _")
 by (unfold bEx_def)
 have z_Hii: "?z_hii" (is "\\E x : ?z_hje(x)")
 by (unfold z_Hii_z_Hb, fact z_Hb)
 have z_Hjf: "?z_hje((CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))))" (is "?z_hjh&?z_hji")
 by (rule zenon_ex_choose_0 [of "?z_hje", OF z_Hii])
 have z_Hji: "?z_hji"
 by (rule zenon_and_1 [OF z_Hjf])
 have z_Hjj_z_Hji: "(\\E x:((x \\in Node)&((~(voted[(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))]))&((<<x, (CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<x, (CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))), x>>}))&((a_votedhash_primea=except(voted, (CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))), TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))) == ?z_hji" (is "?z_hjj == _")
 by (unfold bEx_def)
 have z_Hjj: "?z_hjj" (is "\\E x : ?z_hkd(x)")
 by (unfold z_Hjj_z_Hji, fact z_Hji)
 have z_Hke: "?z_hkd((CHOOSE x:((x \\in Node)&((~(voted[(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))]))&((<<x, (CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<x, (CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))), x>>}))&((a_votedhash_primea=except(voted, (CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))), TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))" (is "?z_hkg&?z_hkh")
 by (rule zenon_ex_choose_0 [of "?z_hkd", OF z_Hjj])
 have z_Hkh: "?z_hkh" (is "?z_hjm&?z_hki")
 by (rule zenon_and_1 [OF z_Hke])
 have z_Hki: "?z_hki" (is "?z_hkj&?z_hkk")
 by (rule zenon_and_1 [OF z_Hkh])
 have z_Hkk: "?z_hkk" (is "?z_hkl&?z_hkm")
 by (rule zenon_and_1 [OF z_Hki])
 have z_Hkm: "?z_hkm" (is "?z_hkn&?z_hka")
 by (rule zenon_and_1 [OF z_Hkk])
 have z_Hkn: "?z_hkn" (is "_=?z_hko")
 by (rule zenon_and_0 [OF z_Hkm])
 have z_Hka: "?z_hka" (is "?z_hkb&?z_hgi")
 by (rule zenon_and_1 [OF z_Hkm])
 have z_Hgi: "?z_hgi" (is "?z_hgj&?z_hgl")
 by (rule zenon_and_1 [OF z_Hka])
 have z_Hgj: "?z_hgj"
 by (rule zenon_and_0 [OF z_Hgi])
 have z_Hkp_z_Hc: "(~(\\A x:((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x]))))))))) == (~?z_hhp)" (is "?z_hkp == ?z_hc")
 by (unfold bAll_def)
 have z_Hkp: "?z_hkp" (is "~(\\A x : ?z_hkr(x))")
 by (unfold z_Hkp_z_Hc, fact z_Hc)
 have z_Hks: "(\\E x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))" (is "\\E x : ?z_hkt(x)")
 by (rule zenon_notallex_0 [of "?z_hkr", OF z_Hkp])
 have z_Hku: "?z_hkt((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x]))))))))))" (is "~(?z_hkv=>?z_hkw)")
 by (rule zenon_ex_choose_0 [of "?z_hkt", OF z_Hks])
 have z_Hkv: "?z_hkv"
 by (rule zenon_notimply_0 [OF z_Hku])
 have z_Hkx: "(~?z_hkw)"
 by (rule zenon_notimply_1 [OF z_Hku])
 have z_Hky_z_Hkx: "(~(\\A x:((x \\in Node)=>((<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))>> \\in a_voteunde_msghash_primea)|(~(x \\in (a_voteshash_primea[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))]))))))) == (~?z_hkw)" (is "?z_hky == ?z_hkx")
 by (unfold bAll_def)
 have z_Hky: "?z_hky" (is "~(\\A x : ?z_hlg(x))")
 by (unfold z_Hky_z_Hkx, fact z_Hkx)
 have z_Hlh: "(\\E x:(~((x \\in Node)=>((<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))>> \\in a_voteunde_msghash_primea)|(~(x \\in (a_voteshash_primea[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))])))))))" (is "\\E x : ?z_hlj(x)")
 by (rule zenon_notallex_0 [of "?z_hlg", OF z_Hky])
 have z_Hlk: "?z_hlj((CHOOSE x:(~((x \\in Node)=>((<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))>> \\in a_voteunde_msghash_primea)|(~(x \\in (a_voteshash_primea[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))]))))))))" (is "~(?z_hlm=>?z_hln)")
 by (rule zenon_ex_choose_0 [of "?z_hlj", OF z_Hlh])
 have z_Hlm: "?z_hlm"
 by (rule zenon_notimply_0 [OF z_Hlk])
 have z_Hlo: "(~?z_hln)" (is "~(?z_hlp|?z_hlq)")
 by (rule zenon_notimply_1 [OF z_Hlk])
 have z_Hlr: "(~?z_hlp)"
 by (rule zenon_notor_0 [OF z_Hlo])
 have z_Hls: "(~?z_hlq)" (is "~~?z_hlt")
 by (rule zenon_notor_1 [OF z_Hlo])
 have z_Hlt: "?z_hlt"
 by (rule zenon_notnot_0 [OF z_Hls])
 have z_Hlu: "(~(<<(CHOOSE x:(~((x \\in Node)=>((<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))>> \\in a_voteunde_msghash_primea)|(~(x \\in (a_voteshash_primea[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))]))))))), (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))>> \\in ?z_hko))" (is "~?z_hlv")
 by (rule subst [where P="(\<lambda>zenon_Vdc. (~(<<(CHOOSE x:(~((x \\in Node)=>((<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))>> \\in a_voteunde_msghash_primea)|(~(x \\in (a_voteshash_primea[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))]))))))), (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))>> \\in zenon_Vdc)))", OF z_Hkn z_Hlr])
 have z_Hmb: "(~(<<(CHOOSE x:(~((x \\in Node)=>((<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))>> \\in a_voteunde_msghash_primea)|(~(x \\in (a_voteshash_primea[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))]))))))), (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))>> \\in a_voteunde_msga))" (is "~?z_hmc")
 by (rule zenon_notin_cup_0 [of "<<(CHOOSE x:(~((x \\in Node)=>((<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))>> \\in a_voteunde_msghash_primea)|(~(x \\in (a_voteshash_primea[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))]))))))), (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))>>" "a_voteunde_msga" "{<<(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&?z_hgi))))))))), (CHOOSE x:((x \\in Node)&(?z_hjm&((<<x, (CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&?z_hgi)))))))))>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<x, (CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&?z_hgi)))))))))>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&?z_hgi))))))))), x>>}))&?z_hka))))))>>}", OF z_Hlu])
 have z_Hmf: "?z_hih((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x]))))))))))" (is "_=>?z_hmg")
 by (rule zenon_all_0 [of "?z_hih" "(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))", OF z_Hhy])
 show FALSE
 proof (rule zenon_imply [OF z_Hmf])
  assume z_Hmh:"(~?z_hkv)"
  show FALSE
  by (rule notE [OF z_Hmh z_Hkv])
 next
  assume z_Hmg:"?z_hmg"
  have z_Hmi_z_Hmg: "(\\A x:((x \\in Node)=>((<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))>> \\in a_voteunde_msga)|(~(x \\in (votes[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))])))))) == ?z_hmg" (is "?z_hmi == _")
  by (unfold bAll_def)
  have z_Hmi: "?z_hmi" (is "\\A x : ?z_hmo(x)")
  by (unfold z_Hmi_z_Hmg, fact z_Hmg)
  have z_Hmp: "?z_hmo((CHOOSE x:(~((x \\in Node)=>((<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))>> \\in a_voteunde_msghash_primea)|(~(x \\in (a_voteshash_primea[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))]))))))))" (is "_=>?z_hmq")
  by (rule zenon_all_0 [of "?z_hmo" "(CHOOSE x:(~((x \\in Node)=>((<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))>> \\in a_voteunde_msghash_primea)|(~(x \\in (a_voteshash_primea[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))])))))))", OF z_Hmi])
  show FALSE
  proof (rule zenon_imply [OF z_Hmp])
   assume z_Hmr:"(~?z_hlm)"
   show FALSE
   by (rule notE [OF z_Hmr z_Hlm])
  next
   assume z_Hmq:"?z_hmq" (is "_|?z_hms")
   show FALSE
   proof (rule zenon_or [OF z_Hmq])
    assume z_Hmc:"?z_hmc"
    show FALSE
    by (rule notE [OF z_Hmb z_Hmc])
   next
    assume z_Hms:"?z_hms" (is "~?z_hmt")
    show FALSE
    proof (rule notE [OF z_Hms])
     have z_Hmu: "((a_voteshash_primea[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))])=(votes[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))]))" (is "?z_hgv=?z_hhj")
     proof (rule zenon_nnpp [of "(?z_hgv=?z_hhj)"])
      assume z_Hgu:"(?z_hgv~=?z_hhj)"
      show FALSE
      by (rule zenon_L1_ [OF z_Hgu z_Hgj])
     qed
     have z_Hmt: "?z_hmt"
     by (rule subst [where P="(\<lambda>zenon_Vlk. ((CHOOSE x:(~((x \\in Node)=>((<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))>> \\in a_voteunde_msghash_primea)|(~(x \\in ?z_hgv)))))) \\in zenon_Vlk))", OF z_Hmu], fact z_Hlt)
     thus "?z_hmt" .
    qed
   qed
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 117"; *} qed
lemma ob'115:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
fixes Node
fixes Quorum
fixes Value
fixes a_voteunde_requestunde_msga a_voteunde_requestunde_msga'
fixes voted voted'
fixes a_voteunde_msga a_voteunde_msga'
fixes votes votes'
fixes leader leader'
fixes decided decided'
fixes a_requnde_historya a_requnde_historya'
(* usable definition vars suppressed *)
(* usable definition IgnoreRequestVote suppressed *)
(* usable definition ProtocolNext suppressed *)
(* usable definition OtherNext suppressed *)
(* usable definition Spec suppressed *)
(* usable definition Symmetry suppressed *)
(* usable definition Safety suppressed *)
(* usable definition SplitVote suppressed *)
(* usable definition Liveness suppressed *)
assumes v'29: "(((((((a_voteunde_requestunde_msga) \<in> ((SUBSET (((Node) \<times> (Node))))))) & (((voted) \<in> ([(Node) \<rightarrow> (BOOLEAN)]))) & (((a_voteunde_msga) \<in> ((SUBSET (((Node) \<times> (Node))))))) & (((votes) \<in> ([(Node) \<rightarrow> ((SUBSET (Node)))]))) & (((leader) \<in> ([(Node) \<rightarrow> (BOOLEAN)]))) & (((decided) \<in> ([(Node) \<rightarrow> ((SUBSET (Value)))])))) & (\<forall> a_n1a \<in> (Node) : (\<forall> a_n2a \<in> (Node) : (\<forall> a_v1a \<in> (Value) : (\<forall> a_v2a \<in> (Value) : (((((((a_v1a) \<in> (fapply ((decided), (a_n1a))))) \<and> (((a_v2a) \<in> (fapply ((decided), (a_n2a))))))) \<Rightarrow> (((a_v1a) = (a_v2a))))))))) & (\<forall> VARI \<in> (Node) : (\<forall> VARJ \<in> (Node) : (((((<<(VARJ), (VARI)>>) \<in> (a_voteunde_msga))) \<or> ((~ (((VARJ) \<in> (fapply ((votes), (VARI))))))))))) & (\<forall> VARI \<in> (Node) : (\<exists> QJ \<in> (Quorum) : (\<forall> VALI \<in> (Value) : (((((QJ) \<subseteq> (fapply ((votes), (VARI))))) \<or> ((~ (((VALI) \<in> (fapply ((decided), (VARI)))))))))))) & (\<forall> VARI \<in> (Node) : (\<forall> VARJ \<in> (Node) : (((fapply ((voted), (VARI))) \<or> ((~ (((<<(VARI), (VARJ)>>) \<in> (a_voteunde_msga))))))))) & (\<forall> VARI \<in> (Node) : (\<exists> QJ \<in> (Quorum) : (((((QJ) \<subseteq> (fapply ((votes), (VARI))))) \<or> ((~ (fapply ((leader), (VARI))))))))) & (\<forall> VARI \<in> (Node) : (\<forall> VALI \<in> (Value) : (((fapply ((leader), (VARI))) \<or> ((~ (((VALI) \<in> (fapply ((decided), (VARI))))))))))) & (\<forall> VARI \<in> (Node) : (\<forall> VARJ \<in> (Node) : (\<forall> VARK \<in> (Node) : (((((((((VARI) = (VARK))) \<and> (((votes) = (votes))))) \<or> ((~ (((<<(VARJ), (VARI)>>) \<in> (a_voteunde_msga))))))) \<or> ((~ (((VARJ) \<in> (fapply ((votes), (VARK)))))))))))) & (\<forall> VARI \<in> (Node) : (\<forall> VARJ \<in> (Node) : (\<forall> VARK \<in> (Node) : (((((((((VARJ) = (VARK))) \<and> (((votes) = (votes))))) \<or> ((~ (((<<(VARI), (VARK)>>) \<in> (a_voteunde_msga))))))) \<or> ((~ (((<<(VARI), (VARJ)>>) \<in> (a_voteunde_msga))))))))))) \<and> (((ProtocolNext) \<or> (OtherNext)))))"
assumes v'40: "(\<exists> i \<in> (Node) : (\<exists> j \<in> (Node) : ((((<<(i), (j)>>) \<notin> (a_requnde_historya))) & (\<forall> a_dst2a \<in> (Node) : (((<<(i), (a_dst2a)>>) \<notin> (a_voteunde_requestunde_msga)))) & ((((a_voteunde_requestunde_msghash_primea :: c)) = (((a_voteunde_requestunde_msga) \<union> ({(<<(i), (j)>>)}))))) & ((((a_requnde_historyhash_primea :: c)) = (((a_requnde_historya) \<union> ({(<<(i), (j)>>)}))))) & (((((a_votedhash_primea :: c)) = (voted))) & ((((a_voteunde_msghash_primea :: c)) = (a_voteunde_msga))) & ((((a_voteshash_primea :: c)) = (votes))) & ((((a_leaderhash_primea :: c)) = (leader))) & ((((a_decidedhash_primea :: c)) = (decided)))))))"
shows "(\<forall> VARI \<in> (Node) : (\<forall> VARJ \<in> (Node) : (((((<<(VARJ), (VARI)>>) \<in> ((a_voteunde_msghash_primea :: c)))) \<or> ((~ (((VARJ) \<in> (fapply (((a_voteshash_primea :: c)), (VARI)))))))))))"(is "PROP ?ob'115")
proof -
ML_command {* writeln "*** TLAPS ENTER 115"; *}
show "PROP ?ob'115"

(* BEGIN ZENON INPUT
;; file=consensus_epr_IndProofs.tlaps/tlapm_3d551c.znn; PATH='/home/egolf/.opam/4.07.1/bin:/home/egolf/.local/bin:/home/egolf/bin:/home/egolf/mambaforge/bin:/home/egolf/mambaforge/condabin:/home/egolf/.opam/4.07.1/bin:/home/egolf/.local/bin:/home/egolf/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/home/egolf/.local/bin/gurobi952/linux64/bin:/home/egolf/Projects/apalache/bin:/home/egolf/opt/foxitsoftware/foxitreader:/home/egolf/.local/bin/gurobi952/linux64/bin:/home/egolf/Projects/apalache/bin:/home/egolf/opt/foxitsoftware/foxitreader:/usr/local/bin:/usr/local/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >consensus_epr_IndProofs.tlaps/tlapm_3d551c.znn.out
;; obligation #115
$hyp "v'29" (/\ (/\ (/\ (TLA.in a_voteunde_requestunde_msga
(TLA.SUBSET (TLA.prod Node Node))) (TLA.in voted
(TLA.FuncSet Node (TLA.set T. F.))) (TLA.in a_voteunde_msga
(TLA.SUBSET (TLA.prod Node Node))) (TLA.in votes
(TLA.FuncSet Node (TLA.SUBSET Node))) (TLA.in leader
(TLA.FuncSet Node (TLA.set T. F.))) (TLA.in decided
(TLA.FuncSet Node (TLA.SUBSET Value))))
(TLA.bAll Node ((a_n1a) (TLA.bAll Node ((a_n2a) (TLA.bAll Value ((a_v1a) (TLA.bAll Value ((a_v2a) (=> (/\ (TLA.in a_v1a
(TLA.fapply decided a_n1a)) (TLA.in a_v2a (TLA.fapply decided a_n2a)))
(= a_v1a a_v2a))))))))))
(TLA.bAll Node ((VARI) (TLA.bAll Node ((VARJ) (\/ (TLA.in (TLA.tuple VARJ
VARI) a_voteunde_msga) (-. (TLA.in VARJ (TLA.fapply votes VARI))))))))
(TLA.bAll Node ((VARI) (TLA.bEx Quorum ((QJ) (TLA.bAll Value ((VALI) (\/ (TLA.subseteq QJ
(TLA.fapply votes VARI)) (-. (TLA.in VALI (TLA.fapply decided VARI))))))))))
(TLA.bAll Node ((VARI) (TLA.bAll Node ((VARJ) (\/ (TLA.fapply voted VARI)
(-. (TLA.in (TLA.tuple VARI VARJ) a_voteunde_msga)))))))
(TLA.bAll Node ((VARI) (TLA.bEx Quorum ((QJ) (\/ (TLA.subseteq QJ
(TLA.fapply votes VARI)) (-. (TLA.fapply leader VARI)))))))
(TLA.bAll Node ((VARI) (TLA.bAll Value ((VALI) (\/ (TLA.fapply leader VARI)
(-. (TLA.in VALI (TLA.fapply decided VARI))))))))
(TLA.bAll Node ((VARI) (TLA.bAll Node ((VARJ) (TLA.bAll Node ((VARK) (\/ (\/ (/\ (= VARI
VARK) (= votes votes)) (-. (TLA.in (TLA.tuple VARJ VARI) a_voteunde_msga)))
(-. (TLA.in VARJ (TLA.fapply votes VARK))))))))))
(TLA.bAll Node ((VARI) (TLA.bAll Node ((VARJ) (TLA.bAll Node ((VARK) (\/ (\/ (/\ (= VARJ
VARK) (= votes votes)) (-. (TLA.in (TLA.tuple VARI VARK) a_voteunde_msga)))
(-. (TLA.in (TLA.tuple VARI VARJ) a_voteunde_msga)))))))))) (\/ ProtocolNext
OtherNext))
$hyp "v'40" (TLA.bEx Node ((i) (TLA.bEx Node ((j) (/\ (-. (TLA.in (TLA.tuple i
j) a_requnde_historya)) (TLA.bAll Node ((a_dst2a) (-. (TLA.in (TLA.tuple i
a_dst2a) a_voteunde_requestunde_msga))))
(= a_voteunde_requestunde_msghash_primea (TLA.cup a_voteunde_requestunde_msga
(TLA.set (TLA.tuple i j)))) (= a_requnde_historyhash_primea
(TLA.cup a_requnde_historya (TLA.set (TLA.tuple i j))))
(/\ (= a_votedhash_primea voted) (= a_voteunde_msghash_primea
a_voteunde_msga) (= a_voteshash_primea votes) (= a_leaderhash_primea leader)
(= a_decidedhash_primea
decided)))))))
$goal (TLA.bAll Node ((VARI) (TLA.bAll Node ((VARJ) (\/ (TLA.in (TLA.tuple VARJ
VARI) a_voteunde_msghash_primea) (-. (TLA.in VARJ
(TLA.fapply a_voteshash_primea VARI))))))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Ha:"((((a_voteunde_requestunde_msga \\in SUBSET(prod(Node, Node)))&((voted \\in FuncSet(Node, {TRUE, FALSE}))&((a_voteunde_msga \\in SUBSET(prod(Node, Node)))&((votes \\in FuncSet(Node, SUBSET(Node)))&((leader \\in FuncSet(Node, {TRUE, FALSE}))&(decided \\in FuncSet(Node, SUBSET(Value))))))))&(bAll(Node, (\<lambda>a_n1a. bAll(Node, (\<lambda>a_n2a. bAll(Value, (\<lambda>a_v1a. bAll(Value, (\<lambda>a_v2a. (((a_v1a \\in (decided[a_n1a]))&(a_v2a \\in (decided[a_n2a])))=>(a_v1a=a_v2a))))))))))&(bAll(Node, (\<lambda>VARI. bAll(Node, (\<lambda>VARJ. ((<<VARJ, VARI>> \\in a_voteunde_msga)|(~(VARJ \\in (votes[VARI]))))))))&(bAll(Node, (\<lambda>VARI. bEx(Quorum, (\<lambda>QJ. bAll(Value, (\<lambda>VALI. ((QJ \\subseteq (votes[VARI]))|(~(VALI \\in (decided[VARI]))))))))))&(bAll(Node, (\<lambda>VARI. bAll(Node, (\<lambda>VARJ. ((voted[VARI])|(~(<<VARI, VARJ>> \\in a_voteunde_msga)))))))&(bAll(Node, (\<lambda>VARI. bEx(Quorum, (\<lambda>QJ. ((QJ \\subseteq (votes[VARI]))|(~(leader[VARI])))))))&(bAll(Node, (\<lambda>VARI. bAll(Value, (\<lambda>VALI. ((leader[VARI])|(~(VALI \\in (decided[VARI]))))))))&(bAll(Node, (\<lambda>VARI. bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARI=VARK)&(votes=votes))|(~(<<VARJ, VARI>> \\in a_voteunde_msga)))|(~(VARJ \\in (votes[VARK]))))))))))&bAll(Node, (\<lambda>VARI. bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(votes=votes))|(~(<<VARI, VARK>> \\in a_voteunde_msga)))|(~(<<VARI, VARJ>> \\in a_voteunde_msga)))))))))))))))))&(ProtocolNext|OtherNext))" (is "?z_hd&?z_hff")
 using v'29 by blast
 have z_Hb:"bEx(Node, (\<lambda>i. bEx(Node, (\<lambda>j. ((~(<<i, j>> \\in a_requnde_historya))&(bAll(Node, (\<lambda>a_dst2a. (~(<<i, a_dst2a>> \\in a_voteunde_requestunde_msga))))&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\cup {<<i, j>>}))&((a_requnde_historyhash_primea=(a_requnde_historya \\cup {<<i, j>>}))&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_voteshash_primea=votes)&((a_leaderhash_primea=leader)&(a_decidedhash_primea=decided)))))))))))))" (is "?z_hb")
 using v'40 by blast
 have zenon_L1_: "((a_voteshash_primea[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))])~=(votes[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))])) ==> (a_voteshash_primea=votes) ==> FALSE" (is "?z_hgw ==> ?z_hgp ==> FALSE")
 proof -
  assume z_Hgw:"?z_hgw" (is "?z_hgx~=?z_hhl")
  assume z_Hgp:"?z_hgp"
  show FALSE
  proof (rule zenon_noteq [of "?z_hhl"])
   have z_Hhm: "(?z_hhl~=?z_hhl)"
   by (rule subst [where P="(\<lambda>zenon_Vkk. ((zenon_Vkk[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))])~=?z_hhl))", OF z_Hgp], fact z_Hgw)
   thus "(?z_hhl~=?z_hhl)" .
  qed
 qed
 assume z_Hc:"(~bAll(Node, (\<lambda>VARI. bAll(Node, (\<lambda>VARJ. ((<<VARJ, VARI>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[VARI])))))))))" (is "~?z_hhr")
 have z_Hd: "?z_hd" (is "?z_he&?z_hbh")
 by (rule zenon_and_0 [OF z_Ha])
 have z_Hbh: "?z_hbh" (is "?z_hbi&?z_hcb")
 by (rule zenon_and_1 [OF z_Hd])
 have z_Hcb: "?z_hcb" (is "?z_hcc&?z_hco")
 by (rule zenon_and_1 [OF z_Hbh])
 have z_Hcc: "?z_hcc"
 by (rule zenon_and_0 [OF z_Hcb])
 have z_Hia_z_Hcc: "(\\A x:((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msga)|(~(VARJ \\in (votes[x])))))))) == ?z_hcc" (is "?z_hia == _")
 by (unfold bAll_def)
 have z_Hia: "?z_hia" (is "\\A x : ?z_hij(x)")
 by (unfold z_Hia_z_Hcc, fact z_Hcc)
 have z_Hik_z_Hb: "(\\E x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(<<x, j>> \\in a_requnde_historya))&(bAll(Node, (\<lambda>a_dst2a. (~(<<x, a_dst2a>> \\in a_voteunde_requestunde_msga))))&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\cup {<<x, j>>}))&((a_requnde_historyhash_primea=(a_requnde_historya \\cup {<<x, j>>}))&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_voteshash_primea=votes)&((a_leaderhash_primea=leader)&(a_decidedhash_primea=decided))))))))))))) == ?z_hb" (is "?z_hik == _")
 by (unfold bEx_def)
 have z_Hik: "?z_hik" (is "\\E x : ?z_hjf(x)")
 by (unfold z_Hik_z_Hb, fact z_Hb)
 have z_Hjg: "?z_hjf((CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(<<x, j>> \\in a_requnde_historya))&(bAll(Node, (\<lambda>a_dst2a. (~(<<x, a_dst2a>> \\in a_voteunde_requestunde_msga))))&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\cup {<<x, j>>}))&((a_requnde_historyhash_primea=(a_requnde_historya \\cup {<<x, j>>}))&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_voteshash_primea=votes)&((a_leaderhash_primea=leader)&(a_decidedhash_primea=decided))))))))))))))" (is "?z_hji&?z_hjj")
 by (rule zenon_ex_choose_0 [of "?z_hjf", OF z_Hik])
 have z_Hjj: "?z_hjj"
 by (rule zenon_and_1 [OF z_Hjg])
 have z_Hjk_z_Hjj: "(\\E x:((x \\in Node)&((~(<<(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(<<x, j>> \\in a_requnde_historya))&(bAll(Node, (\<lambda>a_dst2a. (~(<<x, a_dst2a>> \\in a_voteunde_requestunde_msga))))&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\cup {<<x, j>>}))&((a_requnde_historyhash_primea=(a_requnde_historya \\cup {<<x, j>>}))&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_voteshash_primea=votes)&((a_leaderhash_primea=leader)&(a_decidedhash_primea=decided))))))))))))), x>> \\in a_requnde_historya))&(bAll(Node, (\<lambda>a_dst2a. (~(<<(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(<<x, j>> \\in a_requnde_historya))&(bAll(Node, (\<lambda>a_dst2a. (~(<<x, a_dst2a>> \\in a_voteunde_requestunde_msga))))&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\cup {<<x, j>>}))&((a_requnde_historyhash_primea=(a_requnde_historya \\cup {<<x, j>>}))&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_voteshash_primea=votes)&((a_leaderhash_primea=leader)&(a_decidedhash_primea=decided))))))))))))), a_dst2a>> \\in a_voteunde_requestunde_msga))))&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\cup {<<(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(<<x, j>> \\in a_requnde_historya))&(bAll(Node, (\<lambda>a_dst2a. (~(<<x, a_dst2a>> \\in a_voteunde_requestunde_msga))))&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\cup {<<x, j>>}))&((a_requnde_historyhash_primea=(a_requnde_historya \\cup {<<x, j>>}))&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_voteshash_primea=votes)&((a_leaderhash_primea=leader)&(a_decidedhash_primea=decided))))))))))))), x>>}))&((a_requnde_historyhash_primea=(a_requnde_historya \\cup {<<(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(<<x, j>> \\in a_requnde_historya))&(bAll(Node, (\<lambda>a_dst2a. (~(<<x, a_dst2a>> \\in a_voteunde_requestunde_msga))))&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\cup {<<x, j>>}))&((a_requnde_historyhash_primea=(a_requnde_historya \\cup {<<x, j>>}))&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_voteshash_primea=votes)&((a_leaderhash_primea=leader)&(a_decidedhash_primea=decided))))))))))))), x>>}))&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_voteshash_primea=votes)&((a_leaderhash_primea=leader)&(a_decidedhash_primea=decided))))))))))) == ?z_hjj" (is "?z_hjk == _")
 by (unfold bEx_def)
 have z_Hjk: "?z_hjk" (is "\\E x : ?z_hkd(x)")
 by (unfold z_Hjk_z_Hjj, fact z_Hjj)
 have z_Hke: "?z_hkd((CHOOSE x:((x \\in Node)&((~(<<(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(<<x, j>> \\in a_requnde_historya))&(bAll(Node, (\<lambda>a_dst2a. (~(<<x, a_dst2a>> \\in a_voteunde_requestunde_msga))))&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\cup {<<x, j>>}))&((a_requnde_historyhash_primea=(a_requnde_historya \\cup {<<x, j>>}))&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_voteshash_primea=votes)&((a_leaderhash_primea=leader)&(a_decidedhash_primea=decided))))))))))))), x>> \\in a_requnde_historya))&(bAll(Node, (\<lambda>a_dst2a. (~(<<(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(<<x, j>> \\in a_requnde_historya))&(bAll(Node, (\<lambda>a_dst2a. (~(<<x, a_dst2a>> \\in a_voteunde_requestunde_msga))))&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\cup {<<x, j>>}))&((a_requnde_historyhash_primea=(a_requnde_historya \\cup {<<x, j>>}))&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_voteshash_primea=votes)&((a_leaderhash_primea=leader)&(a_decidedhash_primea=decided))))))))))))), a_dst2a>> \\in a_voteunde_requestunde_msga))))&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\cup {<<(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(<<x, j>> \\in a_requnde_historya))&(bAll(Node, (\<lambda>a_dst2a. (~(<<x, a_dst2a>> \\in a_voteunde_requestunde_msga))))&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\cup {<<x, j>>}))&((a_requnde_historyhash_primea=(a_requnde_historya \\cup {<<x, j>>}))&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_voteshash_primea=votes)&((a_leaderhash_primea=leader)&(a_decidedhash_primea=decided))))))))))))), x>>}))&((a_requnde_historyhash_primea=(a_requnde_historya \\cup {<<(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(<<x, j>> \\in a_requnde_historya))&(bAll(Node, (\<lambda>a_dst2a. (~(<<x, a_dst2a>> \\in a_voteunde_requestunde_msga))))&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\cup {<<x, j>>}))&((a_requnde_historyhash_primea=(a_requnde_historya \\cup {<<x, j>>}))&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_voteshash_primea=votes)&((a_leaderhash_primea=leader)&(a_decidedhash_primea=decided))))))))))))), x>>}))&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_voteshash_primea=votes)&((a_leaderhash_primea=leader)&(a_decidedhash_primea=decided))))))))))))" (is "?z_hkg&?z_hkh")
 by (rule zenon_ex_choose_0 [of "?z_hkd", OF z_Hjk])
 have z_Hkh: "?z_hkh" (is "?z_hki&?z_hkj")
 by (rule zenon_and_1 [OF z_Hke])
 have z_Hkj: "?z_hkj" (is "?z_hjr&?z_hkk")
 by (rule zenon_and_1 [OF z_Hkh])
 have z_Hkk: "?z_hkk" (is "?z_hkl&?z_hkm")
 by (rule zenon_and_1 [OF z_Hkj])
 have z_Hkm: "?z_hkm" (is "?z_hkn&?z_hgi")
 by (rule zenon_and_1 [OF z_Hkk])
 have z_Hgi: "?z_hgi" (is "?z_hgj&?z_hgl")
 by (rule zenon_and_1 [OF z_Hkm])
 have z_Hgl: "?z_hgl" (is "?z_hgm&?z_hgo")
 by (rule zenon_and_1 [OF z_Hgi])
 have z_Hgm: "?z_hgm"
 by (rule zenon_and_0 [OF z_Hgl])
 have z_Hgo: "?z_hgo" (is "?z_hgp&?z_hgr")
 by (rule zenon_and_1 [OF z_Hgl])
 have z_Hgp: "?z_hgp"
 by (rule zenon_and_0 [OF z_Hgo])
 have z_Hko_z_Hc: "(~(\\A x:((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x]))))))))) == (~?z_hhr)" (is "?z_hko == ?z_hc")
 by (unfold bAll_def)
 have z_Hko: "?z_hko" (is "~(\\A x : ?z_hkq(x))")
 by (unfold z_Hko_z_Hc, fact z_Hc)
 have z_Hkr: "(\\E x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))" (is "\\E x : ?z_hks(x)")
 by (rule zenon_notallex_0 [of "?z_hkq", OF z_Hko])
 have z_Hkt: "?z_hks((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x]))))))))))" (is "~(?z_hku=>?z_hkv)")
 by (rule zenon_ex_choose_0 [of "?z_hks", OF z_Hkr])
 have z_Hku: "?z_hku"
 by (rule zenon_notimply_0 [OF z_Hkt])
 have z_Hkw: "(~?z_hkv)"
 by (rule zenon_notimply_1 [OF z_Hkt])
 have z_Hkx_z_Hkw: "(~(\\A x:((x \\in Node)=>((<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))>> \\in a_voteunde_msghash_primea)|(~(x \\in (a_voteshash_primea[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))]))))))) == (~?z_hkv)" (is "?z_hkx == ?z_hkw")
 by (unfold bAll_def)
 have z_Hkx: "?z_hkx" (is "~(\\A x : ?z_hlf(x))")
 by (unfold z_Hkx_z_Hkw, fact z_Hkw)
 have z_Hlg: "(\\E x:(~((x \\in Node)=>((<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))>> \\in a_voteunde_msghash_primea)|(~(x \\in (a_voteshash_primea[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))])))))))" (is "\\E x : ?z_hli(x)")
 by (rule zenon_notallex_0 [of "?z_hlf", OF z_Hkx])
 have z_Hlj: "?z_hli((CHOOSE x:(~((x \\in Node)=>((<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))>> \\in a_voteunde_msghash_primea)|(~(x \\in (a_voteshash_primea[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))]))))))))" (is "~(?z_hll=>?z_hlm)")
 by (rule zenon_ex_choose_0 [of "?z_hli", OF z_Hlg])
 have z_Hll: "?z_hll"
 by (rule zenon_notimply_0 [OF z_Hlj])
 have z_Hln: "(~?z_hlm)" (is "~(?z_hlo|?z_hlp)")
 by (rule zenon_notimply_1 [OF z_Hlj])
 have z_Hlq: "(~?z_hlo)"
 by (rule zenon_notor_0 [OF z_Hln])
 have z_Hlr: "(~?z_hlp)" (is "~~?z_hls")
 by (rule zenon_notor_1 [OF z_Hln])
 have z_Hls: "?z_hls"
 by (rule zenon_notnot_0 [OF z_Hlr])
 have z_Hlt: "(~(<<(CHOOSE x:(~((x \\in Node)=>((<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))>> \\in a_voteunde_msghash_primea)|(~(x \\in (a_voteshash_primea[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))]))))))), (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))>> \\in a_voteunde_msga))" (is "~?z_hlu")
 by (rule subst [where P="(\<lambda>zenon_Vdc. (~(<<(CHOOSE x:(~((x \\in Node)=>((<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))>> \\in a_voteunde_msghash_primea)|(~(x \\in (a_voteshash_primea[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))]))))))), (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))>> \\in zenon_Vdc)))", OF z_Hgm z_Hlq])
 have z_Hma: "?z_hij((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x]))))))))))" (is "_=>?z_hmb")
 by (rule zenon_all_0 [of "?z_hij" "(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))", OF z_Hia])
 show FALSE
 proof (rule zenon_imply [OF z_Hma])
  assume z_Hmc:"(~?z_hku)"
  show FALSE
  by (rule notE [OF z_Hmc z_Hku])
 next
  assume z_Hmb:"?z_hmb"
  have z_Hmd_z_Hmb: "(\\A x:((x \\in Node)=>((<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))>> \\in a_voteunde_msga)|(~(x \\in (votes[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))])))))) == ?z_hmb" (is "?z_hmd == _")
  by (unfold bAll_def)
  have z_Hmd: "?z_hmd" (is "\\A x : ?z_hmj(x)")
  by (unfold z_Hmd_z_Hmb, fact z_Hmb)
  have z_Hmk: "?z_hmj((CHOOSE x:(~((x \\in Node)=>((<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))>> \\in a_voteunde_msghash_primea)|(~(x \\in (a_voteshash_primea[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))]))))))))" (is "_=>?z_hml")
  by (rule zenon_all_0 [of "?z_hmj" "(CHOOSE x:(~((x \\in Node)=>((<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))>> \\in a_voteunde_msghash_primea)|(~(x \\in (a_voteshash_primea[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))])))))))", OF z_Hmd])
  show FALSE
  proof (rule zenon_imply [OF z_Hmk])
   assume z_Hmm:"(~?z_hll)"
   show FALSE
   by (rule notE [OF z_Hmm z_Hll])
  next
   assume z_Hml:"?z_hml" (is "_|?z_hmn")
   show FALSE
   proof (rule zenon_or [OF z_Hml])
    assume z_Hlu:"?z_hlu"
    show FALSE
    by (rule notE [OF z_Hlt z_Hlu])
   next
    assume z_Hmn:"?z_hmn" (is "~?z_hmo")
    show FALSE
    proof (rule notE [OF z_Hmn])
     have z_Hmp: "((a_voteshash_primea[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))])=(votes[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))]))" (is "?z_hgx=?z_hhl")
     proof (rule zenon_nnpp [of "(?z_hgx=?z_hhl)"])
      assume z_Hgw:"(?z_hgx~=?z_hhl)"
      show FALSE
      by (rule zenon_L1_ [OF z_Hgw z_Hgp])
     qed
     have z_Hmo: "?z_hmo"
     by (rule subst [where P="(\<lambda>zenon_Vlk. ((CHOOSE x:(~((x \\in Node)=>((<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))>> \\in a_voteunde_msghash_primea)|(~(x \\in ?z_hgx)))))) \\in zenon_Vlk))", OF z_Hmp], fact z_Hls)
     thus "?z_hmo" .
    qed
   qed
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 115"; *} qed
lemma ob'113:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
fixes Node
fixes Quorum
fixes Value
fixes a_voteunde_requestunde_msga a_voteunde_requestunde_msga'
fixes voted voted'
fixes a_voteunde_msga a_voteunde_msga'
fixes votes votes'
fixes leader leader'
fixes decided decided'
fixes a_requnde_historya a_requnde_historya'
(* usable definition vars suppressed *)
(* usable definition ProtocolNext suppressed *)
(* usable definition OtherNext suppressed *)
(* usable definition Spec suppressed *)
(* usable definition Symmetry suppressed *)
(* usable definition Safety suppressed *)
(* usable definition SplitVote suppressed *)
(* usable definition Liveness suppressed *)
assumes v'28: "(((((((a_voteunde_requestunde_msga) \<in> ((SUBSET (((Node) \<times> (Node))))))) & (((voted) \<in> ([(Node) \<rightarrow> (BOOLEAN)]))) & (((a_voteunde_msga) \<in> ((SUBSET (((Node) \<times> (Node))))))) & (((votes) \<in> ([(Node) \<rightarrow> ((SUBSET (Node)))]))) & (((leader) \<in> ([(Node) \<rightarrow> (BOOLEAN)]))) & (((decided) \<in> ([(Node) \<rightarrow> ((SUBSET (Value)))])))) & (\<forall> a_n1a \<in> (Node) : (\<forall> a_n2a \<in> (Node) : (\<forall> a_v1a \<in> (Value) : (\<forall> a_v2a \<in> (Value) : (((((((a_v1a) \<in> (fapply ((decided), (a_n1a))))) \<and> (((a_v2a) \<in> (fapply ((decided), (a_n2a))))))) \<Rightarrow> (((a_v1a) = (a_v2a))))))))) & (\<forall> VARI \<in> (Node) : (\<forall> VARJ \<in> (Node) : (((((<<(VARJ), (VARI)>>) \<in> (a_voteunde_msga))) \<or> ((~ (((VARJ) \<in> (fapply ((votes), (VARI))))))))))) & (\<forall> VARI \<in> (Node) : (\<exists> QJ \<in> (Quorum) : (\<forall> VALI \<in> (Value) : (((((QJ) \<subseteq> (fapply ((votes), (VARI))))) \<or> ((~ (((VALI) \<in> (fapply ((decided), (VARI)))))))))))) & (\<forall> VARI \<in> (Node) : (\<forall> VARJ \<in> (Node) : (((fapply ((voted), (VARI))) \<or> ((~ (((<<(VARI), (VARJ)>>) \<in> (a_voteunde_msga))))))))) & (\<forall> VARI \<in> (Node) : (\<exists> QJ \<in> (Quorum) : (((((QJ) \<subseteq> (fapply ((votes), (VARI))))) \<or> ((~ (fapply ((leader), (VARI))))))))) & (\<forall> VARI \<in> (Node) : (\<forall> VALI \<in> (Value) : (((fapply ((leader), (VARI))) \<or> ((~ (((VALI) \<in> (fapply ((decided), (VARI))))))))))) & (\<forall> VARI \<in> (Node) : (\<forall> VARJ \<in> (Node) : (\<forall> VARK \<in> (Node) : (((((((((VARI) = (VARK))) \<and> (((votes) = (votes))))) \<or> ((~ (((<<(VARJ), (VARI)>>) \<in> (a_voteunde_msga))))))) \<or> ((~ (((VARJ) \<in> (fapply ((votes), (VARK)))))))))))) & (\<forall> VARI \<in> (Node) : (\<forall> VARJ \<in> (Node) : (\<forall> VARK \<in> (Node) : (((((((((VARJ) = (VARK))) \<and> (((votes) = (votes))))) \<or> ((~ (((<<(VARI), (VARK)>>) \<in> (a_voteunde_msga))))))) \<or> ((~ (((<<(VARI), (VARJ)>>) \<in> (a_voteunde_msga))))))))))) \<and> (((ProtocolNext) \<or> (OtherNext)))))"
assumes v'38: "(\<exists> i \<in> (Node) : (\<exists> j \<in> (Node) : ((fapply ((voted), (i))) & ((((a_voteunde_requestunde_msghash_primea :: c)) = (((a_voteunde_requestunde_msga) \\ ({(<<(j), (i)>>)}))))) & ((((a_voteunde_msghash_primea :: c)) = (a_voteunde_msga))) & ((((a_votedhash_primea :: c)) = (voted))) & ((((a_voteshash_primea :: c)) = (votes))) & ((((a_decidedhash_primea :: c)) = (decided))) & ((((a_leaderhash_primea :: c)) = (leader))) & ((((a_requnde_historyhash_primea :: c)) = (a_requnde_historya))))))"
shows "(\<forall> VARI \<in> (Node) : (\<forall> VARJ \<in> (Node) : (((((<<(VARJ), (VARI)>>) \<in> ((a_voteunde_msghash_primea :: c)))) \<or> ((~ (((VARJ) \<in> (fapply (((a_voteshash_primea :: c)), (VARI)))))))))))"(is "PROP ?ob'113")
proof -
ML_command {* writeln "*** TLAPS ENTER 113"; *}
show "PROP ?ob'113"

(* BEGIN ZENON INPUT
;; file=consensus_epr_IndProofs.tlaps/tlapm_cabb07.znn; PATH='/home/egolf/.opam/4.07.1/bin:/home/egolf/.local/bin:/home/egolf/bin:/home/egolf/mambaforge/bin:/home/egolf/mambaforge/condabin:/home/egolf/.opam/4.07.1/bin:/home/egolf/.local/bin:/home/egolf/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/home/egolf/.local/bin/gurobi952/linux64/bin:/home/egolf/Projects/apalache/bin:/home/egolf/opt/foxitsoftware/foxitreader:/home/egolf/.local/bin/gurobi952/linux64/bin:/home/egolf/Projects/apalache/bin:/home/egolf/opt/foxitsoftware/foxitreader:/usr/local/bin:/usr/local/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >consensus_epr_IndProofs.tlaps/tlapm_cabb07.znn.out
;; obligation #113
$hyp "v'28" (/\ (/\ (/\ (TLA.in a_voteunde_requestunde_msga
(TLA.SUBSET (TLA.prod Node Node))) (TLA.in voted
(TLA.FuncSet Node (TLA.set T. F.))) (TLA.in a_voteunde_msga
(TLA.SUBSET (TLA.prod Node Node))) (TLA.in votes
(TLA.FuncSet Node (TLA.SUBSET Node))) (TLA.in leader
(TLA.FuncSet Node (TLA.set T. F.))) (TLA.in decided
(TLA.FuncSet Node (TLA.SUBSET Value))))
(TLA.bAll Node ((a_n1a) (TLA.bAll Node ((a_n2a) (TLA.bAll Value ((a_v1a) (TLA.bAll Value ((a_v2a) (=> (/\ (TLA.in a_v1a
(TLA.fapply decided a_n1a)) (TLA.in a_v2a (TLA.fapply decided a_n2a)))
(= a_v1a a_v2a))))))))))
(TLA.bAll Node ((VARI) (TLA.bAll Node ((VARJ) (\/ (TLA.in (TLA.tuple VARJ
VARI) a_voteunde_msga) (-. (TLA.in VARJ (TLA.fapply votes VARI))))))))
(TLA.bAll Node ((VARI) (TLA.bEx Quorum ((QJ) (TLA.bAll Value ((VALI) (\/ (TLA.subseteq QJ
(TLA.fapply votes VARI)) (-. (TLA.in VALI (TLA.fapply decided VARI))))))))))
(TLA.bAll Node ((VARI) (TLA.bAll Node ((VARJ) (\/ (TLA.fapply voted VARI)
(-. (TLA.in (TLA.tuple VARI VARJ) a_voteunde_msga)))))))
(TLA.bAll Node ((VARI) (TLA.bEx Quorum ((QJ) (\/ (TLA.subseteq QJ
(TLA.fapply votes VARI)) (-. (TLA.fapply leader VARI)))))))
(TLA.bAll Node ((VARI) (TLA.bAll Value ((VALI) (\/ (TLA.fapply leader VARI)
(-. (TLA.in VALI (TLA.fapply decided VARI))))))))
(TLA.bAll Node ((VARI) (TLA.bAll Node ((VARJ) (TLA.bAll Node ((VARK) (\/ (\/ (/\ (= VARI
VARK) (= votes votes)) (-. (TLA.in (TLA.tuple VARJ VARI) a_voteunde_msga)))
(-. (TLA.in VARJ (TLA.fapply votes VARK))))))))))
(TLA.bAll Node ((VARI) (TLA.bAll Node ((VARJ) (TLA.bAll Node ((VARK) (\/ (\/ (/\ (= VARJ
VARK) (= votes votes)) (-. (TLA.in (TLA.tuple VARI VARK) a_voteunde_msga)))
(-. (TLA.in (TLA.tuple VARI VARJ) a_voteunde_msga)))))))))) (\/ ProtocolNext
OtherNext))
$hyp "v'38" (TLA.bEx Node ((i) (TLA.bEx Node ((j) (/\ (TLA.fapply voted i)
(= a_voteunde_requestunde_msghash_primea
(TLA.setminus a_voteunde_requestunde_msga (TLA.set (TLA.tuple j i))))
(= a_voteunde_msghash_primea a_voteunde_msga) (= a_votedhash_primea voted)
(= a_voteshash_primea votes) (= a_decidedhash_primea decided)
(= a_leaderhash_primea leader) (= a_requnde_historyhash_primea
a_requnde_historya))))))
$goal (TLA.bAll Node ((VARI) (TLA.bAll Node ((VARJ) (\/ (TLA.in (TLA.tuple VARJ
VARI) a_voteunde_msghash_primea) (-. (TLA.in VARJ
(TLA.fapply a_voteshash_primea VARI))))))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Ha:"((((a_voteunde_requestunde_msga \\in SUBSET(prod(Node, Node)))&((voted \\in FuncSet(Node, {TRUE, FALSE}))&((a_voteunde_msga \\in SUBSET(prod(Node, Node)))&((votes \\in FuncSet(Node, SUBSET(Node)))&((leader \\in FuncSet(Node, {TRUE, FALSE}))&(decided \\in FuncSet(Node, SUBSET(Value))))))))&(bAll(Node, (\<lambda>a_n1a. bAll(Node, (\<lambda>a_n2a. bAll(Value, (\<lambda>a_v1a. bAll(Value, (\<lambda>a_v2a. (((a_v1a \\in (decided[a_n1a]))&(a_v2a \\in (decided[a_n2a])))=>(a_v1a=a_v2a))))))))))&(bAll(Node, (\<lambda>VARI. bAll(Node, (\<lambda>VARJ. ((<<VARJ, VARI>> \\in a_voteunde_msga)|(~(VARJ \\in (votes[VARI]))))))))&(bAll(Node, (\<lambda>VARI. bEx(Quorum, (\<lambda>QJ. bAll(Value, (\<lambda>VALI. ((QJ \\subseteq (votes[VARI]))|(~(VALI \\in (decided[VARI]))))))))))&(bAll(Node, (\<lambda>VARI. bAll(Node, (\<lambda>VARJ. ((voted[VARI])|(~(<<VARI, VARJ>> \\in a_voteunde_msga)))))))&(bAll(Node, (\<lambda>VARI. bEx(Quorum, (\<lambda>QJ. ((QJ \\subseteq (votes[VARI]))|(~(leader[VARI])))))))&(bAll(Node, (\<lambda>VARI. bAll(Value, (\<lambda>VALI. ((leader[VARI])|(~(VALI \\in (decided[VARI]))))))))&(bAll(Node, (\<lambda>VARI. bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARI=VARK)&(votes=votes))|(~(<<VARJ, VARI>> \\in a_voteunde_msga)))|(~(VARJ \\in (votes[VARK]))))))))))&bAll(Node, (\<lambda>VARI. bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(votes=votes))|(~(<<VARI, VARK>> \\in a_voteunde_msga)))|(~(<<VARI, VARJ>> \\in a_voteunde_msga)))))))))))))))))&(ProtocolNext|OtherNext))" (is "?z_hd&?z_hff")
 using v'28 by blast
 have z_Hb:"bEx(Node, (\<lambda>i. bEx(Node, (\<lambda>j. ((voted[i])&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, i>>}))&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_votedhash_primea=voted)&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))" (is "?z_hb")
 using v'38 by blast
 have zenon_L1_: "((a_voteshash_primea[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))])~=(votes[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))])) ==> (a_voteshash_primea=votes) ==> FALSE" (is "?z_hgn ==> ?z_hgc ==> FALSE")
 proof -
  assume z_Hgn:"?z_hgn" (is "?z_hgo~=?z_hhc")
  assume z_Hgc:"?z_hgc"
  show FALSE
  proof (rule zenon_noteq [of "?z_hhc"])
   have z_Hhd: "(?z_hhc~=?z_hhc)"
   by (rule subst [where P="(\<lambda>zenon_Vji. ((zenon_Vji[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))])~=?z_hhc))", OF z_Hgc], fact z_Hgn)
   thus "(?z_hhc~=?z_hhc)" .
  qed
 qed
 assume z_Hc:"(~bAll(Node, (\<lambda>VARI. bAll(Node, (\<lambda>VARJ. ((<<VARJ, VARI>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[VARI])))))))))" (is "~?z_hhi")
 have z_Hd: "?z_hd" (is "?z_he&?z_hbh")
 by (rule zenon_and_0 [OF z_Ha])
 have z_Hbh: "?z_hbh" (is "?z_hbi&?z_hcb")
 by (rule zenon_and_1 [OF z_Hd])
 have z_Hcb: "?z_hcb" (is "?z_hcc&?z_hco")
 by (rule zenon_and_1 [OF z_Hbh])
 have z_Hcc: "?z_hcc"
 by (rule zenon_and_0 [OF z_Hcb])
 have z_Hhr_z_Hcc: "(\\A x:((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msga)|(~(VARJ \\in (votes[x])))))))) == ?z_hcc" (is "?z_hhr == _")
 by (unfold bAll_def)
 have z_Hhr: "?z_hhr" (is "\\A x : ?z_hia(x)")
 by (unfold z_Hhr_z_Hcc, fact z_Hcc)
 have z_Hib_z_Hb: "(\\E x:((x \\in Node)&bEx(Node, (\<lambda>j. ((voted[x])&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_votedhash_primea=voted)&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))) == ?z_hb" (is "?z_hib == _")
 by (unfold bEx_def)
 have z_Hib: "?z_hib" (is "\\E x : ?z_him(x)")
 by (unfold z_Hib_z_Hb, fact z_Hb)
 have z_Hin: "?z_him((CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((voted[x])&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_votedhash_primea=voted)&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))" (is "?z_hip&?z_hiq")
 by (rule zenon_ex_choose_0 [of "?z_him", OF z_Hib])
 have z_Hiq: "?z_hiq"
 by (rule zenon_and_1 [OF z_Hin])
 have z_Hir_z_Hiq: "(\\E x:((x \\in Node)&((voted[(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((voted[x])&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_votedhash_primea=voted)&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))])&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<x, (CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((voted[x])&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_votedhash_primea=voted)&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))>>}))&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_votedhash_primea=voted)&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))) == ?z_hiq" (is "?z_hir == _")
 by (unfold bEx_def)
 have z_Hir: "?z_hir" (is "\\E x : ?z_hja(x)")
 by (unfold z_Hir_z_Hiq, fact z_Hiq)
 have z_Hjb: "?z_hja((CHOOSE x:((x \\in Node)&((voted[(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((voted[x])&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_votedhash_primea=voted)&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))])&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<x, (CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((voted[x])&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_votedhash_primea=voted)&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))>>}))&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_votedhash_primea=voted)&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))" (is "?z_hjd&?z_hje")
 by (rule zenon_ex_choose_0 [of "?z_hja", OF z_Hir])
 have z_Hje: "?z_hje" (is "?z_hiu&?z_hjf")
 by (rule zenon_and_1 [OF z_Hjb])
 have z_Hjf: "?z_hjf" (is "?z_hjg&?z_hfv")
 by (rule zenon_and_1 [OF z_Hje])
 have z_Hfv: "?z_hfv" (is "?z_hfw&?z_hfy")
 by (rule zenon_and_1 [OF z_Hjf])
 have z_Hfw: "?z_hfw"
 by (rule zenon_and_0 [OF z_Hfv])
 have z_Hfy: "?z_hfy" (is "?z_hfz&?z_hgb")
 by (rule zenon_and_1 [OF z_Hfv])
 have z_Hgb: "?z_hgb" (is "?z_hgc&?z_hge")
 by (rule zenon_and_1 [OF z_Hfy])
 have z_Hgc: "?z_hgc"
 by (rule zenon_and_0 [OF z_Hgb])
 have z_Hjh_z_Hc: "(~(\\A x:((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x]))))))))) == (~?z_hhi)" (is "?z_hjh == ?z_hc")
 by (unfold bAll_def)
 have z_Hjh: "?z_hjh" (is "~(\\A x : ?z_hjj(x))")
 by (unfold z_Hjh_z_Hc, fact z_Hc)
 have z_Hjk: "(\\E x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))" (is "\\E x : ?z_hjl(x)")
 by (rule zenon_notallex_0 [of "?z_hjj", OF z_Hjh])
 have z_Hjm: "?z_hjl((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x]))))))))))" (is "~(?z_hjn=>?z_hjo)")
 by (rule zenon_ex_choose_0 [of "?z_hjl", OF z_Hjk])
 have z_Hjn: "?z_hjn"
 by (rule zenon_notimply_0 [OF z_Hjm])
 have z_Hjp: "(~?z_hjo)"
 by (rule zenon_notimply_1 [OF z_Hjm])
 have z_Hjq_z_Hjp: "(~(\\A x:((x \\in Node)=>((<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))>> \\in a_voteunde_msghash_primea)|(~(x \\in (a_voteshash_primea[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))]))))))) == (~?z_hjo)" (is "?z_hjq == ?z_hjp")
 by (unfold bAll_def)
 have z_Hjq: "?z_hjq" (is "~(\\A x : ?z_hjy(x))")
 by (unfold z_Hjq_z_Hjp, fact z_Hjp)
 have z_Hjz: "(\\E x:(~((x \\in Node)=>((<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))>> \\in a_voteunde_msghash_primea)|(~(x \\in (a_voteshash_primea[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))])))))))" (is "\\E x : ?z_hkb(x)")
 by (rule zenon_notallex_0 [of "?z_hjy", OF z_Hjq])
 have z_Hkc: "?z_hkb((CHOOSE x:(~((x \\in Node)=>((<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))>> \\in a_voteunde_msghash_primea)|(~(x \\in (a_voteshash_primea[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))]))))))))" (is "~(?z_hke=>?z_hkf)")
 by (rule zenon_ex_choose_0 [of "?z_hkb", OF z_Hjz])
 have z_Hke: "?z_hke"
 by (rule zenon_notimply_0 [OF z_Hkc])
 have z_Hkg: "(~?z_hkf)" (is "~(?z_hkh|?z_hki)")
 by (rule zenon_notimply_1 [OF z_Hkc])
 have z_Hkj: "(~?z_hkh)"
 by (rule zenon_notor_0 [OF z_Hkg])
 have z_Hkk: "(~?z_hki)" (is "~~?z_hkl")
 by (rule zenon_notor_1 [OF z_Hkg])
 have z_Hkl: "?z_hkl"
 by (rule zenon_notnot_0 [OF z_Hkk])
 have z_Hkm: "(~(<<(CHOOSE x:(~((x \\in Node)=>((<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))>> \\in a_voteunde_msghash_primea)|(~(x \\in (a_voteshash_primea[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))]))))))), (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))>> \\in a_voteunde_msga))" (is "~?z_hkn")
 by (rule subst [where P="(\<lambda>zenon_Vzb. (~(<<(CHOOSE x:(~((x \\in Node)=>((<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))>> \\in a_voteunde_msghash_primea)|(~(x \\in (a_voteshash_primea[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))]))))))), (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))>> \\in zenon_Vzb)))", OF z_Hfw z_Hkj])
 have z_Hkt: "?z_hia((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x]))))))))))" (is "_=>?z_hku")
 by (rule zenon_all_0 [of "?z_hia" "(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))", OF z_Hhr])
 show FALSE
 proof (rule zenon_imply [OF z_Hkt])
  assume z_Hkv:"(~?z_hjn)"
  show FALSE
  by (rule notE [OF z_Hkv z_Hjn])
 next
  assume z_Hku:"?z_hku"
  have z_Hkw_z_Hku: "(\\A x:((x \\in Node)=>((<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))>> \\in a_voteunde_msga)|(~(x \\in (votes[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))])))))) == ?z_hku" (is "?z_hkw == _")
  by (unfold bAll_def)
  have z_Hkw: "?z_hkw" (is "\\A x : ?z_hlc(x)")
  by (unfold z_Hkw_z_Hku, fact z_Hku)
  have z_Hld: "?z_hlc((CHOOSE x:(~((x \\in Node)=>((<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))>> \\in a_voteunde_msghash_primea)|(~(x \\in (a_voteshash_primea[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))]))))))))" (is "_=>?z_hle")
  by (rule zenon_all_0 [of "?z_hlc" "(CHOOSE x:(~((x \\in Node)=>((<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))>> \\in a_voteunde_msghash_primea)|(~(x \\in (a_voteshash_primea[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))])))))))", OF z_Hkw])
  show FALSE
  proof (rule zenon_imply [OF z_Hld])
   assume z_Hlf:"(~?z_hke)"
   show FALSE
   by (rule notE [OF z_Hlf z_Hke])
  next
   assume z_Hle:"?z_hle" (is "_|?z_hlg")
   show FALSE
   proof (rule zenon_or [OF z_Hle])
    assume z_Hkn:"?z_hkn"
    show FALSE
    by (rule notE [OF z_Hkm z_Hkn])
   next
    assume z_Hlg:"?z_hlg" (is "~?z_hlh")
    show FALSE
    proof (rule notE [OF z_Hlg])
     have z_Hli: "((a_voteshash_primea[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))])=(votes[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))]))" (is "?z_hgo=?z_hhc")
     proof (rule zenon_nnpp [of "(?z_hgo=?z_hhc)"])
      assume z_Hgn:"(?z_hgo~=?z_hhc)"
      show FALSE
      by (rule zenon_L1_ [OF z_Hgn z_Hgc])
     qed
     have z_Hlh: "?z_hlh"
     by (rule subst [where P="(\<lambda>zenon_Vek. ((CHOOSE x:(~((x \\in Node)=>((<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))>> \\in a_voteunde_msghash_primea)|(~(x \\in ?z_hgo)))))) \\in zenon_Vek))", OF z_Hli], fact z_Hkl)
     thus "?z_hlh" .
    qed
   qed
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 113"; *} qed
lemma ob'123:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
fixes Node
fixes Quorum
fixes Value
fixes a_voteunde_requestunde_msga a_voteunde_requestunde_msga'
fixes voted voted'
fixes a_voteunde_msga a_voteunde_msga'
fixes votes votes'
fixes leader leader'
fixes decided decided'
fixes a_requnde_historya a_requnde_historya'
(* usable definition vars suppressed *)
(* usable definition IgnoreRequestVote suppressed *)
(* usable definition ProtocolNext suppressed *)
(* usable definition OtherNext suppressed *)
(* usable definition Spec suppressed *)
(* usable definition Symmetry suppressed *)
(* usable definition Safety suppressed *)
(* usable definition SplitVote suppressed *)
(* usable definition Liveness suppressed *)
assumes v'29: "(((((((a_voteunde_requestunde_msga) \<in> ((SUBSET (((Node) \<times> (Node))))))) & (((voted) \<in> ([(Node) \<rightarrow> (BOOLEAN)]))) & (((a_voteunde_msga) \<in> ((SUBSET (((Node) \<times> (Node))))))) & (((votes) \<in> ([(Node) \<rightarrow> ((SUBSET (Node)))]))) & (((leader) \<in> ([(Node) \<rightarrow> (BOOLEAN)]))) & (((decided) \<in> ([(Node) \<rightarrow> ((SUBSET (Value)))])))) & (\<forall> a_n1a \<in> (Node) : (\<forall> a_n2a \<in> (Node) : (\<forall> a_v1a \<in> (Value) : (\<forall> a_v2a \<in> (Value) : (((((((a_v1a) \<in> (fapply ((decided), (a_n1a))))) \<and> (((a_v2a) \<in> (fapply ((decided), (a_n2a))))))) \<Rightarrow> (((a_v1a) = (a_v2a))))))))) & (\<forall> VARI \<in> (Node) : (\<forall> VARJ \<in> (Node) : (((((<<(VARJ), (VARI)>>) \<in> (a_voteunde_msga))) \<or> ((~ (((VARJ) \<in> (fapply ((votes), (VARI))))))))))) & (\<forall> VARI \<in> (Node) : (\<exists> QJ \<in> (Quorum) : (\<forall> VALI \<in> (Value) : (((((QJ) \<subseteq> (fapply ((votes), (VARI))))) \<or> ((~ (((VALI) \<in> (fapply ((decided), (VARI)))))))))))) & (\<forall> VARI \<in> (Node) : (\<forall> VARJ \<in> (Node) : (((fapply ((voted), (VARI))) \<or> ((~ (((<<(VARI), (VARJ)>>) \<in> (a_voteunde_msga))))))))) & (\<forall> VARI \<in> (Node) : (\<exists> QJ \<in> (Quorum) : (((((QJ) \<subseteq> (fapply ((votes), (VARI))))) \<or> ((~ (fapply ((leader), (VARI))))))))) & (\<forall> VARI \<in> (Node) : (\<forall> VALI \<in> (Value) : (((fapply ((leader), (VARI))) \<or> ((~ (((VALI) \<in> (fapply ((decided), (VARI))))))))))) & (\<forall> VARI \<in> (Node) : (\<forall> VARJ \<in> (Node) : (\<forall> VARK \<in> (Node) : (((((((((VARI) = (VARK))) \<and> (((votes) = (votes))))) \<or> ((~ (((<<(VARJ), (VARI)>>) \<in> (a_voteunde_msga))))))) \<or> ((~ (((VARJ) \<in> (fapply ((votes), (VARK)))))))))))) & (\<forall> VARI \<in> (Node) : (\<forall> VARJ \<in> (Node) : (\<forall> VARK \<in> (Node) : (((((((((VARJ) = (VARK))) \<and> (((votes) = (votes))))) \<or> ((~ (((<<(VARI), (VARK)>>) \<in> (a_voteunde_msga))))))) \<or> ((~ (((<<(VARI), (VARJ)>>) \<in> (a_voteunde_msga))))))))))) \<and> (((ProtocolNext) \<or> (OtherNext)))))"
assumes v'43: "(\<exists> i \<in> (Node) : (\<exists> Q \<in> (Quorum) : ((((Q) \<subseteq> (fapply ((votes), (i))))) & ((((a_leaderhash_primea :: c)) = ([(leader) EXCEPT ![(i)] = (TRUE)]))) & ((((a_voteshash_primea :: c)) = (votes))) & ((((a_votedhash_primea :: c)) = (voted))) & ((((a_voteunde_msghash_primea :: c)) = (a_voteunde_msga))) & ((((a_decidedhash_primea :: c)) = (decided))) & ((((a_voteunde_requestunde_msghash_primea :: c)) = (a_voteunde_requestunde_msga))) & ((((a_requnde_historyhash_primea :: c)) = (a_requnde_historya))))))"
shows "(\<forall> VARI \<in> (Node) : (\<forall> VARJ \<in> (Node) : (((((<<(VARJ), (VARI)>>) \<in> ((a_voteunde_msghash_primea :: c)))) \<or> ((~ (((VARJ) \<in> (fapply (((a_voteshash_primea :: c)), (VARI)))))))))))"(is "PROP ?ob'123")
proof -
ML_command {* writeln "*** TLAPS ENTER 123"; *}
show "PROP ?ob'123"

(* BEGIN ZENON INPUT
;; file=consensus_epr_IndProofs.tlaps/tlapm_999980.znn; PATH='/home/egolf/.opam/4.07.1/bin:/home/egolf/.local/bin:/home/egolf/bin:/home/egolf/mambaforge/bin:/home/egolf/mambaforge/condabin:/home/egolf/.opam/4.07.1/bin:/home/egolf/.local/bin:/home/egolf/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/home/egolf/.local/bin/gurobi952/linux64/bin:/home/egolf/Projects/apalache/bin:/home/egolf/opt/foxitsoftware/foxitreader:/home/egolf/.local/bin/gurobi952/linux64/bin:/home/egolf/Projects/apalache/bin:/home/egolf/opt/foxitsoftware/foxitreader:/usr/local/bin:/usr/local/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >consensus_epr_IndProofs.tlaps/tlapm_999980.znn.out
;; obligation #123
$hyp "v'29" (/\ (/\ (/\ (TLA.in a_voteunde_requestunde_msga
(TLA.SUBSET (TLA.prod Node Node))) (TLA.in voted
(TLA.FuncSet Node (TLA.set T. F.))) (TLA.in a_voteunde_msga
(TLA.SUBSET (TLA.prod Node Node))) (TLA.in votes
(TLA.FuncSet Node (TLA.SUBSET Node))) (TLA.in leader
(TLA.FuncSet Node (TLA.set T. F.))) (TLA.in decided
(TLA.FuncSet Node (TLA.SUBSET Value))))
(TLA.bAll Node ((a_n1a) (TLA.bAll Node ((a_n2a) (TLA.bAll Value ((a_v1a) (TLA.bAll Value ((a_v2a) (=> (/\ (TLA.in a_v1a
(TLA.fapply decided a_n1a)) (TLA.in a_v2a (TLA.fapply decided a_n2a)))
(= a_v1a a_v2a))))))))))
(TLA.bAll Node ((VARI) (TLA.bAll Node ((VARJ) (\/ (TLA.in (TLA.tuple VARJ
VARI) a_voteunde_msga) (-. (TLA.in VARJ (TLA.fapply votes VARI))))))))
(TLA.bAll Node ((VARI) (TLA.bEx Quorum ((QJ) (TLA.bAll Value ((VALI) (\/ (TLA.subseteq QJ
(TLA.fapply votes VARI)) (-. (TLA.in VALI (TLA.fapply decided VARI))))))))))
(TLA.bAll Node ((VARI) (TLA.bAll Node ((VARJ) (\/ (TLA.fapply voted VARI)
(-. (TLA.in (TLA.tuple VARI VARJ) a_voteunde_msga)))))))
(TLA.bAll Node ((VARI) (TLA.bEx Quorum ((QJ) (\/ (TLA.subseteq QJ
(TLA.fapply votes VARI)) (-. (TLA.fapply leader VARI)))))))
(TLA.bAll Node ((VARI) (TLA.bAll Value ((VALI) (\/ (TLA.fapply leader VARI)
(-. (TLA.in VALI (TLA.fapply decided VARI))))))))
(TLA.bAll Node ((VARI) (TLA.bAll Node ((VARJ) (TLA.bAll Node ((VARK) (\/ (\/ (/\ (= VARI
VARK) (= votes votes)) (-. (TLA.in (TLA.tuple VARJ VARI) a_voteunde_msga)))
(-. (TLA.in VARJ (TLA.fapply votes VARK))))))))))
(TLA.bAll Node ((VARI) (TLA.bAll Node ((VARJ) (TLA.bAll Node ((VARK) (\/ (\/ (/\ (= VARJ
VARK) (= votes votes)) (-. (TLA.in (TLA.tuple VARI VARK) a_voteunde_msga)))
(-. (TLA.in (TLA.tuple VARI VARJ) a_voteunde_msga)))))))))) (\/ ProtocolNext
OtherNext))
$hyp "v'43" (TLA.bEx Node ((i) (TLA.bEx Quorum ((Q) (/\ (TLA.subseteq Q
(TLA.fapply votes i)) (= a_leaderhash_primea (TLA.except leader i T.))
(= a_voteshash_primea votes) (= a_votedhash_primea voted)
(= a_voteunde_msghash_primea a_voteunde_msga) (= a_decidedhash_primea
decided) (= a_voteunde_requestunde_msghash_primea
a_voteunde_requestunde_msga) (= a_requnde_historyhash_primea
a_requnde_historya))))))
$goal (TLA.bAll Node ((VARI) (TLA.bAll Node ((VARJ) (\/ (TLA.in (TLA.tuple VARJ
VARI) a_voteunde_msghash_primea) (-. (TLA.in VARJ
(TLA.fapply a_voteshash_primea VARI))))))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Ha:"((((a_voteunde_requestunde_msga \\in SUBSET(prod(Node, Node)))&((voted \\in FuncSet(Node, {TRUE, FALSE}))&((a_voteunde_msga \\in SUBSET(prod(Node, Node)))&((votes \\in FuncSet(Node, SUBSET(Node)))&((leader \\in FuncSet(Node, {TRUE, FALSE}))&(decided \\in FuncSet(Node, SUBSET(Value))))))))&(bAll(Node, (\<lambda>a_n1a. bAll(Node, (\<lambda>a_n2a. bAll(Value, (\<lambda>a_v1a. bAll(Value, (\<lambda>a_v2a. (((a_v1a \\in (decided[a_n1a]))&(a_v2a \\in (decided[a_n2a])))=>(a_v1a=a_v2a))))))))))&(bAll(Node, (\<lambda>VARI. bAll(Node, (\<lambda>VARJ. ((<<VARJ, VARI>> \\in a_voteunde_msga)|(~(VARJ \\in (votes[VARI]))))))))&(bAll(Node, (\<lambda>VARI. bEx(Quorum, (\<lambda>QJ. bAll(Value, (\<lambda>VALI. ((QJ \\subseteq (votes[VARI]))|(~(VALI \\in (decided[VARI]))))))))))&(bAll(Node, (\<lambda>VARI. bAll(Node, (\<lambda>VARJ. ((voted[VARI])|(~(<<VARI, VARJ>> \\in a_voteunde_msga)))))))&(bAll(Node, (\<lambda>VARI. bEx(Quorum, (\<lambda>QJ. ((QJ \\subseteq (votes[VARI]))|(~(leader[VARI])))))))&(bAll(Node, (\<lambda>VARI. bAll(Value, (\<lambda>VALI. ((leader[VARI])|(~(VALI \\in (decided[VARI]))))))))&(bAll(Node, (\<lambda>VARI. bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARI=VARK)&(votes=votes))|(~(<<VARJ, VARI>> \\in a_voteunde_msga)))|(~(VARJ \\in (votes[VARK]))))))))))&bAll(Node, (\<lambda>VARI. bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(votes=votes))|(~(<<VARI, VARK>> \\in a_voteunde_msga)))|(~(<<VARI, VARJ>> \\in a_voteunde_msga)))))))))))))))))&(ProtocolNext|OtherNext))" (is "?z_hd&?z_hff")
 using v'29 by blast
 have z_Hb:"bEx(Node, (\<lambda>i. bEx(Quorum, (\<lambda>Q. ((Q \\subseteq (votes[i]))&((a_leaderhash_primea=except(leader, i, TRUE))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_decidedhash_primea=decided)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))" (is "?z_hb")
 using v'43 by blast
 have zenon_L1_: "((a_voteshash_primea[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))])~=(votes[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))])) ==> (a_voteshash_primea=votes) ==> FALSE" (is "?z_hgm ==> ?z_hfv ==> FALSE")
 proof -
  assume z_Hgm:"?z_hgm" (is "?z_hgn~=?z_hhb")
  assume z_Hfv:"?z_hfv"
  show FALSE
  proof (rule zenon_noteq [of "?z_hhb"])
   have z_Hhc: "(?z_hhb~=?z_hhb)"
   by (rule subst [where P="(\<lambda>zenon_Vjl. ((zenon_Vjl[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))])~=?z_hhb))", OF z_Hfv], fact z_Hgm)
   thus "(?z_hhb~=?z_hhb)" .
  qed
 qed
 assume z_Hc:"(~bAll(Node, (\<lambda>VARI. bAll(Node, (\<lambda>VARJ. ((<<VARJ, VARI>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[VARI])))))))))" (is "~?z_hhh")
 have z_Hd: "?z_hd" (is "?z_he&?z_hbh")
 by (rule zenon_and_0 [OF z_Ha])
 have z_Hbh: "?z_hbh" (is "?z_hbi&?z_hcb")
 by (rule zenon_and_1 [OF z_Hd])
 have z_Hcb: "?z_hcb" (is "?z_hcc&?z_hco")
 by (rule zenon_and_1 [OF z_Hbh])
 have z_Hcc: "?z_hcc"
 by (rule zenon_and_0 [OF z_Hcb])
 have z_Hhq_z_Hcc: "(\\A x:((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msga)|(~(VARJ \\in (votes[x])))))))) == ?z_hcc" (is "?z_hhq == _")
 by (unfold bAll_def)
 have z_Hhq: "?z_hhq" (is "\\A x : ?z_hhz(x)")
 by (unfold z_Hhq_z_Hcc, fact z_Hcc)
 have z_Hia_z_Hb: "(\\E x:((x \\in Node)&bEx(Quorum, (\<lambda>Q. ((Q \\subseteq (votes[x]))&((a_leaderhash_primea=except(leader, x, TRUE))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_decidedhash_primea=decided)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))) == ?z_hb" (is "?z_hia == _")
 by (unfold bEx_def)
 have z_Hia: "?z_hia" (is "\\E x : ?z_hij(x)")
 by (unfold z_Hia_z_Hb, fact z_Hb)
 have z_Hik: "?z_hij((CHOOSE x:((x \\in Node)&bEx(Quorum, (\<lambda>Q. ((Q \\subseteq (votes[x]))&((a_leaderhash_primea=except(leader, x, TRUE))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_decidedhash_primea=decided)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))" (is "?z_him&?z_hin")
 by (rule zenon_ex_choose_0 [of "?z_hij", OF z_Hia])
 have z_Hin: "?z_hin"
 by (rule zenon_and_1 [OF z_Hik])
 have z_Hio_z_Hin: "(\\E x:((x \\in Quorum)&((x \\subseteq (votes[(CHOOSE x:((x \\in Node)&bEx(Quorum, (\<lambda>Q. ((Q \\subseteq (votes[x]))&((a_leaderhash_primea=except(leader, x, TRUE))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_decidedhash_primea=decided)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))]))&((a_leaderhash_primea=except(leader, (CHOOSE x:((x \\in Node)&bEx(Quorum, (\<lambda>Q. ((Q \\subseteq (votes[x]))&((a_leaderhash_primea=except(leader, x, TRUE))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_decidedhash_primea=decided)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))), TRUE))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_decidedhash_primea=decided)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))) == ?z_hin" (is "?z_hio == _")
 by (unfold bEx_def)
 have z_Hio: "?z_hio" (is "\\E x : ?z_hix(x)")
 by (unfold z_Hio_z_Hin, fact z_Hin)
 have z_Hiy: "?z_hix((CHOOSE x:((x \\in Quorum)&((x \\subseteq (votes[(CHOOSE x:((x \\in Node)&bEx(Quorum, (\<lambda>Q. ((Q \\subseteq (votes[x]))&((a_leaderhash_primea=except(leader, x, TRUE))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_decidedhash_primea=decided)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))]))&((a_leaderhash_primea=except(leader, (CHOOSE x:((x \\in Node)&bEx(Quorum, (\<lambda>Q. ((Q \\subseteq (votes[x]))&((a_leaderhash_primea=except(leader, x, TRUE))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_decidedhash_primea=decided)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))), TRUE))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_decidedhash_primea=decided)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))" (is "?z_hja&?z_hjb")
 by (rule zenon_ex_choose_0 [of "?z_hix", OF z_Hio])
 have z_Hjb: "?z_hjb" (is "?z_hjc&?z_hiu")
 by (rule zenon_and_1 [OF z_Hiy])
 have z_Hiu: "?z_hiu" (is "?z_hiv&?z_hfu")
 by (rule zenon_and_1 [OF z_Hjb])
 have z_Hfu: "?z_hfu" (is "?z_hfv&?z_hfx")
 by (rule zenon_and_1 [OF z_Hiu])
 have z_Hfv: "?z_hfv"
 by (rule zenon_and_0 [OF z_Hfu])
 have z_Hfx: "?z_hfx" (is "?z_hfy&?z_hga")
 by (rule zenon_and_1 [OF z_Hfu])
 have z_Hga: "?z_hga" (is "?z_hgb&?z_hgd")
 by (rule zenon_and_1 [OF z_Hfx])
 have z_Hgb: "?z_hgb"
 by (rule zenon_and_0 [OF z_Hga])
 have z_Hjd_z_Hc: "(~(\\A x:((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x]))))))))) == (~?z_hhh)" (is "?z_hjd == ?z_hc")
 by (unfold bAll_def)
 have z_Hjd: "?z_hjd" (is "~(\\A x : ?z_hjf(x))")
 by (unfold z_Hjd_z_Hc, fact z_Hc)
 have z_Hjg: "(\\E x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))" (is "\\E x : ?z_hjh(x)")
 by (rule zenon_notallex_0 [of "?z_hjf", OF z_Hjd])
 have z_Hji: "?z_hjh((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x]))))))))))" (is "~(?z_hjj=>?z_hjk)")
 by (rule zenon_ex_choose_0 [of "?z_hjh", OF z_Hjg])
 have z_Hjj: "?z_hjj"
 by (rule zenon_notimply_0 [OF z_Hji])
 have z_Hjl: "(~?z_hjk)"
 by (rule zenon_notimply_1 [OF z_Hji])
 have z_Hjm_z_Hjl: "(~(\\A x:((x \\in Node)=>((<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))>> \\in a_voteunde_msghash_primea)|(~(x \\in (a_voteshash_primea[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))]))))))) == (~?z_hjk)" (is "?z_hjm == ?z_hjl")
 by (unfold bAll_def)
 have z_Hjm: "?z_hjm" (is "~(\\A x : ?z_hju(x))")
 by (unfold z_Hjm_z_Hjl, fact z_Hjl)
 have z_Hjv: "(\\E x:(~((x \\in Node)=>((<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))>> \\in a_voteunde_msghash_primea)|(~(x \\in (a_voteshash_primea[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))])))))))" (is "\\E x : ?z_hjx(x)")
 by (rule zenon_notallex_0 [of "?z_hju", OF z_Hjm])
 have z_Hjy: "?z_hjx((CHOOSE x:(~((x \\in Node)=>((<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))>> \\in a_voteunde_msghash_primea)|(~(x \\in (a_voteshash_primea[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))]))))))))" (is "~(?z_hka=>?z_hkb)")
 by (rule zenon_ex_choose_0 [of "?z_hjx", OF z_Hjv])
 have z_Hka: "?z_hka"
 by (rule zenon_notimply_0 [OF z_Hjy])
 have z_Hkc: "(~?z_hkb)" (is "~(?z_hkd|?z_hke)")
 by (rule zenon_notimply_1 [OF z_Hjy])
 have z_Hkf: "(~?z_hkd)"
 by (rule zenon_notor_0 [OF z_Hkc])
 have z_Hkg: "(~?z_hke)" (is "~~?z_hkh")
 by (rule zenon_notor_1 [OF z_Hkc])
 have z_Hkh: "?z_hkh"
 by (rule zenon_notnot_0 [OF z_Hkg])
 have z_Hki: "(~(<<(CHOOSE x:(~((x \\in Node)=>((<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))>> \\in a_voteunde_msghash_primea)|(~(x \\in (a_voteshash_primea[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))]))))))), (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))>> \\in a_voteunde_msga))" (is "~?z_hkj")
 by (rule subst [where P="(\<lambda>zenon_Vbc. (~(<<(CHOOSE x:(~((x \\in Node)=>((<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))>> \\in a_voteunde_msghash_primea)|(~(x \\in (a_voteshash_primea[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))]))))))), (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))>> \\in zenon_Vbc)))", OF z_Hgb z_Hkf])
 have z_Hkp: "?z_hhz((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x]))))))))))" (is "_=>?z_hkq")
 by (rule zenon_all_0 [of "?z_hhz" "(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))", OF z_Hhq])
 show FALSE
 proof (rule zenon_imply [OF z_Hkp])
  assume z_Hkr:"(~?z_hjj)"
  show FALSE
  by (rule notE [OF z_Hkr z_Hjj])
 next
  assume z_Hkq:"?z_hkq"
  have z_Hks_z_Hkq: "(\\A x:((x \\in Node)=>((<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))>> \\in a_voteunde_msga)|(~(x \\in (votes[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))])))))) == ?z_hkq" (is "?z_hks == _")
  by (unfold bAll_def)
  have z_Hks: "?z_hks" (is "\\A x : ?z_hky(x)")
  by (unfold z_Hks_z_Hkq, fact z_Hkq)
  have z_Hkz: "?z_hky((CHOOSE x:(~((x \\in Node)=>((<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))>> \\in a_voteunde_msghash_primea)|(~(x \\in (a_voteshash_primea[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))]))))))))" (is "_=>?z_hla")
  by (rule zenon_all_0 [of "?z_hky" "(CHOOSE x:(~((x \\in Node)=>((<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))>> \\in a_voteunde_msghash_primea)|(~(x \\in (a_voteshash_primea[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))])))))))", OF z_Hks])
  show FALSE
  proof (rule zenon_imply [OF z_Hkz])
   assume z_Hlb:"(~?z_hka)"
   show FALSE
   by (rule notE [OF z_Hlb z_Hka])
  next
   assume z_Hla:"?z_hla" (is "_|?z_hlc")
   show FALSE
   proof (rule zenon_or [OF z_Hla])
    assume z_Hkj:"?z_hkj"
    show FALSE
    by (rule notE [OF z_Hki z_Hkj])
   next
    assume z_Hlc:"?z_hlc" (is "~?z_hld")
    show FALSE
    proof (rule notE [OF z_Hlc])
     have z_Hle: "((a_voteshash_primea[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))])=(votes[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))]))" (is "?z_hgn=?z_hhb")
     proof (rule zenon_nnpp [of "(?z_hgn=?z_hhb)"])
      assume z_Hgm:"(?z_hgn~=?z_hhb)"
      show FALSE
      by (rule zenon_L1_ [OF z_Hgm z_Hfv])
     qed
     have z_Hld: "?z_hld"
     by (rule subst [where P="(\<lambda>zenon_Vkl. ((CHOOSE x:(~((x \\in Node)=>((<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))>> \\in a_voteunde_msghash_primea)|(~(x \\in ?z_hgn)))))) \\in zenon_Vkl))", OF z_Hle], fact z_Hkh)
     thus "?z_hld" .
    qed
   qed
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 123"; *} qed
lemma ob'122:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
fixes Node
fixes Quorum
fixes Value
fixes a_voteunde_requestunde_msga a_voteunde_requestunde_msga'
fixes voted voted'
fixes a_voteunde_msga a_voteunde_msga'
fixes votes votes'
fixes leader leader'
fixes decided decided'
fixes a_requnde_historya a_requnde_historya'
(* usable definition vars suppressed *)
(* usable definition IgnoreRequestVote suppressed *)
(* usable definition SendVote suppressed *)
(* usable definition RecvVote suppressed *)
(* usable definition BecomeLeader suppressed *)
(* usable definition Decide suppressed *)
(* usable definition SendRequestVote suppressed *)
(* usable definition Init suppressed *)
(* usable definition ProtocolNext suppressed *)
(* usable definition OtherNext suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition Symmetry suppressed *)
(* usable definition Safety suppressed *)
(* usable definition SplitVote suppressed *)
(* usable definition Liveness suppressed *)
(* usable definition SafetyCore suppressed *)
(* usable definition TypeOK suppressed *)
(* usable definition Inv152_1_1_def suppressed *)
(* usable definition Inv693_1_2_def suppressed *)
(* usable definition Inv164_1_3_def suppressed *)
(* usable definition Inv622_1_4_def suppressed *)
(* usable definition Inv4302_2_0_def suppressed *)
(* usable definition Inv5288_2_0_def suppressed *)
(* usable definition IndAuto suppressed *)
assumes v'45: "(((IndAuto) \<and> (Next)))"
assumes v'58: "((\<And> VARI :: c. VARI \<in> (Node) \<Longrightarrow> (\<And> VARJ :: c. VARJ \<in> (Node) \<Longrightarrow> (((((<<(VARJ), (VARI)>>) \<in> ((a_voteunde_msghash_primea :: c)))) \<or> ((~ (((VARJ) \<in> (fapply (((a_voteshash_primea :: c)), (VARI))))))))))))"
shows "(\<forall> VARI \<in> (Node) : (\<forall> VARJ \<in> (Node) : (((((<<(VARJ), (VARI)>>) \<in> ((a_voteunde_msghash_primea :: c)))) \<or> ((~ (((VARJ) \<in> (fapply (((a_voteshash_primea :: c)), (VARI)))))))))))"(is "PROP ?ob'122")
proof -
ML_command {* writeln "*** TLAPS ENTER 122"; *}
show "PROP ?ob'122"

(* BEGIN ZENON INPUT
;; file=consensus_epr_IndProofs.tlaps/tlapm_63f088.znn; PATH='/home/egolf/.opam/4.07.1/bin:/home/egolf/.local/bin:/home/egolf/bin:/home/egolf/mambaforge/bin:/home/egolf/mambaforge/condabin:/home/egolf/.opam/4.07.1/bin:/home/egolf/.local/bin:/home/egolf/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/home/egolf/.local/bin/gurobi952/linux64/bin:/home/egolf/Projects/apalache/bin:/home/egolf/opt/foxitsoftware/foxitreader:/home/egolf/.local/bin/gurobi952/linux64/bin:/home/egolf/Projects/apalache/bin:/home/egolf/opt/foxitsoftware/foxitreader:/usr/local/bin:/usr/local/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >consensus_epr_IndProofs.tlaps/tlapm_63f088.znn.out
;; obligation #122
$hyp "v'45" (/\ IndAuto
Next)
$hyp "v'58" (TLA.bAll Node ((VARI) (TLA.bAll Node ((VARJ) (\/ (TLA.in (TLA.tuple VARJ
VARI) a_voteunde_msghash_primea) (-. (TLA.in VARJ
(TLA.fapply a_voteshash_primea VARI))))))))
$goal (TLA.bAll Node ((VARI) (TLA.bAll Node ((VARJ) (\/ (TLA.in (TLA.tuple VARJ
VARI) a_voteunde_msghash_primea) (-. (TLA.in VARJ
(TLA.fapply a_voteshash_primea VARI))))))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hb:"bAll(Node, (\<lambda>VARI. bAll(Node, (\<lambda>VARJ. ((<<VARJ, VARI>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[VARI]))))))))" (is "?z_hb")
 using v'58 by blast
 assume z_Hc:"(~?z_hb)"
 show FALSE
 by (rule notE [OF z_Hc z_Hb])
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 122"; *} qed
lemma ob'125:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
fixes Node
fixes Quorum
fixes Value
fixes a_voteunde_requestunde_msga a_voteunde_requestunde_msga'
fixes voted voted'
fixes a_voteunde_msga a_voteunde_msga'
fixes votes votes'
fixes leader leader'
fixes decided decided'
fixes a_requnde_historya a_requnde_historya'
(* usable definition vars suppressed *)
(* usable definition IgnoreRequestVote suppressed *)
(* usable definition ProtocolNext suppressed *)
(* usable definition OtherNext suppressed *)
(* usable definition Spec suppressed *)
(* usable definition Symmetry suppressed *)
(* usable definition Safety suppressed *)
(* usable definition SplitVote suppressed *)
(* usable definition Liveness suppressed *)
assumes v'29: "(((((((a_voteunde_requestunde_msga) \<in> ((SUBSET (((Node) \<times> (Node))))))) & (((voted) \<in> ([(Node) \<rightarrow> (BOOLEAN)]))) & (((a_voteunde_msga) \<in> ((SUBSET (((Node) \<times> (Node))))))) & (((votes) \<in> ([(Node) \<rightarrow> ((SUBSET (Node)))]))) & (((leader) \<in> ([(Node) \<rightarrow> (BOOLEAN)]))) & (((decided) \<in> ([(Node) \<rightarrow> ((SUBSET (Value)))])))) & (\<forall> a_n1a \<in> (Node) : (\<forall> a_n2a \<in> (Node) : (\<forall> a_v1a \<in> (Value) : (\<forall> a_v2a \<in> (Value) : (((((((a_v1a) \<in> (fapply ((decided), (a_n1a))))) \<and> (((a_v2a) \<in> (fapply ((decided), (a_n2a))))))) \<Rightarrow> (((a_v1a) = (a_v2a))))))))) & (\<forall> VARI \<in> (Node) : (\<forall> VARJ \<in> (Node) : (((((<<(VARJ), (VARI)>>) \<in> (a_voteunde_msga))) \<or> ((~ (((VARJ) \<in> (fapply ((votes), (VARI))))))))))) & (\<forall> VARI \<in> (Node) : (\<exists> QJ \<in> (Quorum) : (\<forall> VALI \<in> (Value) : (((((QJ) \<subseteq> (fapply ((votes), (VARI))))) \<or> ((~ (((VALI) \<in> (fapply ((decided), (VARI)))))))))))) & (\<forall> VARI \<in> (Node) : (\<forall> VARJ \<in> (Node) : (((fapply ((voted), (VARI))) \<or> ((~ (((<<(VARI), (VARJ)>>) \<in> (a_voteunde_msga))))))))) & (\<forall> VARI \<in> (Node) : (\<exists> QJ \<in> (Quorum) : (((((QJ) \<subseteq> (fapply ((votes), (VARI))))) \<or> ((~ (fapply ((leader), (VARI))))))))) & (\<forall> VARI \<in> (Node) : (\<forall> VALI \<in> (Value) : (((fapply ((leader), (VARI))) \<or> ((~ (((VALI) \<in> (fapply ((decided), (VARI))))))))))) & (\<forall> VARI \<in> (Node) : (\<forall> VARJ \<in> (Node) : (\<forall> VARK \<in> (Node) : (((((((((VARI) = (VARK))) \<and> (((votes) = (votes))))) \<or> ((~ (((<<(VARJ), (VARI)>>) \<in> (a_voteunde_msga))))))) \<or> ((~ (((VARJ) \<in> (fapply ((votes), (VARK)))))))))))) & (\<forall> VARI \<in> (Node) : (\<forall> VARJ \<in> (Node) : (\<forall> VARK \<in> (Node) : (((((((((VARJ) = (VARK))) \<and> (((votes) = (votes))))) \<or> ((~ (((<<(VARI), (VARK)>>) \<in> (a_voteunde_msga))))))) \<or> ((~ (((<<(VARI), (VARJ)>>) \<in> (a_voteunde_msga))))))))))) \<and> (((ProtocolNext) \<or> (OtherNext)))))"
assumes v'44: "(\<exists> i \<in> (Node) : (\<exists> j \<in> (Node) : (\<exists> v \<in> (Value) : ((fapply ((leader), (i))) & ((({}) = (fapply ((decided), (i))))) & ((((a_decidedhash_primea :: c)) = ([(decided) EXCEPT ![(i)] = (((fapply ((decided), (i))) \<union> ({(v)})))]))) & ((((a_voteshash_primea :: c)) = (votes))) & ((((a_votedhash_primea :: c)) = (voted))) & ((((a_voteunde_msghash_primea :: c)) = (a_voteunde_msga))) & ((((a_leaderhash_primea :: c)) = (leader))) & ((((a_voteunde_requestunde_msghash_primea :: c)) = (a_voteunde_requestunde_msga))) & ((((a_requnde_historyhash_primea :: c)) = (a_requnde_historya)))))))"
shows "(\<forall> VARI \<in> (Node) : (\<forall> VARJ \<in> (Node) : (((((<<(VARJ), (VARI)>>) \<in> ((a_voteunde_msghash_primea :: c)))) \<or> ((~ (((VARJ) \<in> (fapply (((a_voteshash_primea :: c)), (VARI)))))))))))"(is "PROP ?ob'125")
proof -
ML_command {* writeln "*** TLAPS ENTER 125"; *}
show "PROP ?ob'125"

(* BEGIN ZENON INPUT
;; file=consensus_epr_IndProofs.tlaps/tlapm_8d6763.znn; PATH='/home/egolf/.opam/4.07.1/bin:/home/egolf/.local/bin:/home/egolf/bin:/home/egolf/mambaforge/bin:/home/egolf/mambaforge/condabin:/home/egolf/.opam/4.07.1/bin:/home/egolf/.local/bin:/home/egolf/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/home/egolf/.local/bin/gurobi952/linux64/bin:/home/egolf/Projects/apalache/bin:/home/egolf/opt/foxitsoftware/foxitreader:/home/egolf/.local/bin/gurobi952/linux64/bin:/home/egolf/Projects/apalache/bin:/home/egolf/opt/foxitsoftware/foxitreader:/usr/local/bin:/usr/local/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >consensus_epr_IndProofs.tlaps/tlapm_8d6763.znn.out
;; obligation #125
$hyp "v'29" (/\ (/\ (/\ (TLA.in a_voteunde_requestunde_msga
(TLA.SUBSET (TLA.prod Node Node))) (TLA.in voted
(TLA.FuncSet Node (TLA.set T. F.))) (TLA.in a_voteunde_msga
(TLA.SUBSET (TLA.prod Node Node))) (TLA.in votes
(TLA.FuncSet Node (TLA.SUBSET Node))) (TLA.in leader
(TLA.FuncSet Node (TLA.set T. F.))) (TLA.in decided
(TLA.FuncSet Node (TLA.SUBSET Value))))
(TLA.bAll Node ((a_n1a) (TLA.bAll Node ((a_n2a) (TLA.bAll Value ((a_v1a) (TLA.bAll Value ((a_v2a) (=> (/\ (TLA.in a_v1a
(TLA.fapply decided a_n1a)) (TLA.in a_v2a (TLA.fapply decided a_n2a)))
(= a_v1a a_v2a))))))))))
(TLA.bAll Node ((VARI) (TLA.bAll Node ((VARJ) (\/ (TLA.in (TLA.tuple VARJ
VARI) a_voteunde_msga) (-. (TLA.in VARJ (TLA.fapply votes VARI))))))))
(TLA.bAll Node ((VARI) (TLA.bEx Quorum ((QJ) (TLA.bAll Value ((VALI) (\/ (TLA.subseteq QJ
(TLA.fapply votes VARI)) (-. (TLA.in VALI (TLA.fapply decided VARI))))))))))
(TLA.bAll Node ((VARI) (TLA.bAll Node ((VARJ) (\/ (TLA.fapply voted VARI)
(-. (TLA.in (TLA.tuple VARI VARJ) a_voteunde_msga)))))))
(TLA.bAll Node ((VARI) (TLA.bEx Quorum ((QJ) (\/ (TLA.subseteq QJ
(TLA.fapply votes VARI)) (-. (TLA.fapply leader VARI)))))))
(TLA.bAll Node ((VARI) (TLA.bAll Value ((VALI) (\/ (TLA.fapply leader VARI)
(-. (TLA.in VALI (TLA.fapply decided VARI))))))))
(TLA.bAll Node ((VARI) (TLA.bAll Node ((VARJ) (TLA.bAll Node ((VARK) (\/ (\/ (/\ (= VARI
VARK) (= votes votes)) (-. (TLA.in (TLA.tuple VARJ VARI) a_voteunde_msga)))
(-. (TLA.in VARJ (TLA.fapply votes VARK))))))))))
(TLA.bAll Node ((VARI) (TLA.bAll Node ((VARJ) (TLA.bAll Node ((VARK) (\/ (\/ (/\ (= VARJ
VARK) (= votes votes)) (-. (TLA.in (TLA.tuple VARI VARK) a_voteunde_msga)))
(-. (TLA.in (TLA.tuple VARI VARJ) a_voteunde_msga)))))))))) (\/ ProtocolNext
OtherNext))
$hyp "v'44" (TLA.bEx Node ((i) (TLA.bEx Node ((j) (TLA.bEx Value ((v) (/\ (TLA.fapply leader i)
(= TLA.emptyset (TLA.fapply decided i)) (= a_decidedhash_primea
(TLA.except decided i (TLA.cup (TLA.fapply decided i) (TLA.set v))))
(= a_voteshash_primea votes) (= a_votedhash_primea voted)
(= a_voteunde_msghash_primea a_voteunde_msga) (= a_leaderhash_primea leader)
(= a_voteunde_requestunde_msghash_primea a_voteunde_requestunde_msga)
(= a_requnde_historyhash_primea
a_requnde_historya))))))))
$goal (TLA.bAll Node ((VARI) (TLA.bAll Node ((VARJ) (\/ (TLA.in (TLA.tuple VARJ
VARI) a_voteunde_msghash_primea) (-. (TLA.in VARJ
(TLA.fapply a_voteshash_primea VARI))))))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Ha:"((((a_voteunde_requestunde_msga \\in SUBSET(prod(Node, Node)))&((voted \\in FuncSet(Node, {TRUE, FALSE}))&((a_voteunde_msga \\in SUBSET(prod(Node, Node)))&((votes \\in FuncSet(Node, SUBSET(Node)))&((leader \\in FuncSet(Node, {TRUE, FALSE}))&(decided \\in FuncSet(Node, SUBSET(Value))))))))&(bAll(Node, (\<lambda>a_n1a. bAll(Node, (\<lambda>a_n2a. bAll(Value, (\<lambda>a_v1a. bAll(Value, (\<lambda>a_v2a. (((a_v1a \\in (decided[a_n1a]))&(a_v2a \\in (decided[a_n2a])))=>(a_v1a=a_v2a))))))))))&(bAll(Node, (\<lambda>VARI. bAll(Node, (\<lambda>VARJ. ((<<VARJ, VARI>> \\in a_voteunde_msga)|(~(VARJ \\in (votes[VARI]))))))))&(bAll(Node, (\<lambda>VARI. bEx(Quorum, (\<lambda>QJ. bAll(Value, (\<lambda>VALI. ((QJ \\subseteq (votes[VARI]))|(~(VALI \\in (decided[VARI]))))))))))&(bAll(Node, (\<lambda>VARI. bAll(Node, (\<lambda>VARJ. ((voted[VARI])|(~(<<VARI, VARJ>> \\in a_voteunde_msga)))))))&(bAll(Node, (\<lambda>VARI. bEx(Quorum, (\<lambda>QJ. ((QJ \\subseteq (votes[VARI]))|(~(leader[VARI])))))))&(bAll(Node, (\<lambda>VARI. bAll(Value, (\<lambda>VALI. ((leader[VARI])|(~(VALI \\in (decided[VARI]))))))))&(bAll(Node, (\<lambda>VARI. bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARI=VARK)&(votes=votes))|(~(<<VARJ, VARI>> \\in a_voteunde_msga)))|(~(VARJ \\in (votes[VARK]))))))))))&bAll(Node, (\<lambda>VARI. bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(votes=votes))|(~(<<VARI, VARK>> \\in a_voteunde_msga)))|(~(<<VARI, VARJ>> \\in a_voteunde_msga)))))))))))))))))&(ProtocolNext|OtherNext))" (is "?z_hd&?z_hff")
 using v'29 by blast
 have z_Hb:"bEx(Node, (\<lambda>i. bEx(Node, (\<lambda>j. bEx(Value, (\<lambda>v. ((leader[i])&(({}=(decided[i]))&((a_decidedhash_primea=except(decided, i, ((decided[i]) \\cup {v})))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))))" (is "?z_hb")
 using v'44 by blast
 have zenon_L1_: "((a_voteshash_primea[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))])~=(votes[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))])) ==> (a_voteshash_primea=votes) ==> FALSE" (is "?z_hgt ==> ?z_hgc ==> FALSE")
 proof -
  assume z_Hgt:"?z_hgt" (is "?z_hgu~=?z_hhi")
  assume z_Hgc:"?z_hgc"
  show FALSE
  proof (rule zenon_noteq [of "?z_hhi"])
   have z_Hhj: "(?z_hhi~=?z_hhi)"
   by (rule subst [where P="(\<lambda>zenon_Vtn. ((zenon_Vtn[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))])~=?z_hhi))", OF z_Hgc], fact z_Hgt)
   thus "(?z_hhi~=?z_hhi)" .
  qed
 qed
 assume z_Hc:"(~bAll(Node, (\<lambda>VARI. bAll(Node, (\<lambda>VARJ. ((<<VARJ, VARI>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[VARI])))))))))" (is "~?z_hho")
 have z_Hd: "?z_hd" (is "?z_he&?z_hbh")
 by (rule zenon_and_0 [OF z_Ha])
 have z_Hbh: "?z_hbh" (is "?z_hbi&?z_hcb")
 by (rule zenon_and_1 [OF z_Hd])
 have z_Hcb: "?z_hcb" (is "?z_hcc&?z_hco")
 by (rule zenon_and_1 [OF z_Hbh])
 have z_Hcc: "?z_hcc"
 by (rule zenon_and_0 [OF z_Hcb])
 have z_Hhx_z_Hcc: "(\\A x:((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msga)|(~(VARJ \\in (votes[x])))))))) == ?z_hcc" (is "?z_hhx == _")
 by (unfold bAll_def)
 have z_Hhx: "?z_hhx" (is "\\A x : ?z_hig(x)")
 by (unfold z_Hhx_z_Hcc, fact z_Hcc)
 have z_Hih_z_Hb: "(\\E x:((x \\in Node)&bEx(Node, (\<lambda>j. bEx(Value, (\<lambda>v. ((leader[x])&(({}=(decided[x]))&((a_decidedhash_primea=except(decided, x, ((decided[x]) \\cup {v})))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))))) == ?z_hb" (is "?z_hih == _")
 by (unfold bEx_def)
 have z_Hih: "?z_hih" (is "\\E x : ?z_hiw(x)")
 by (unfold z_Hih_z_Hb, fact z_Hb)
 have z_Hix: "?z_hiw((CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. bEx(Value, (\<lambda>v. ((leader[x])&(({}=(decided[x]))&((a_decidedhash_primea=except(decided, x, ((decided[x]) \\cup {v})))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))))))" (is "?z_hiz&?z_hja")
 by (rule zenon_ex_choose_0 [of "?z_hiw", OF z_Hih])
 have z_Hja: "?z_hja"
 by (rule zenon_and_1 [OF z_Hix])
 have z_Hjb_z_Hja: "(\\E x:((x \\in Node)&bEx(Value, (\<lambda>v. ((leader[(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. bEx(Value, (\<lambda>v. ((leader[x])&(({}=(decided[x]))&((a_decidedhash_primea=except(decided, x, ((decided[x]) \\cup {v})))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))))])&(({}=(decided[(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. bEx(Value, (\<lambda>v. ((leader[x])&(({}=(decided[x]))&((a_decidedhash_primea=except(decided, x, ((decided[x]) \\cup {v})))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))))]))&((a_decidedhash_primea=except(decided, (CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. bEx(Value, (\<lambda>v. ((leader[x])&(({}=(decided[x]))&((a_decidedhash_primea=except(decided, x, ((decided[x]) \\cup {v})))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))))), ((decided[(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. bEx(Value, (\<lambda>v. ((leader[x])&(({}=(decided[x]))&((a_decidedhash_primea=except(decided, x, ((decided[x]) \\cup {v})))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))))]) \\cup {v})))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))) == ?z_hja" (is "?z_hjb == _")
 by (unfold bEx_def)
 have z_Hjb: "?z_hjb" (is "\\E x : ?z_hjo(x)")
 by (unfold z_Hjb_z_Hja, fact z_Hja)
 have z_Hjp: "?z_hjo((CHOOSE x:((x \\in Node)&bEx(Value, (\<lambda>v. ((leader[(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. bEx(Value, (\<lambda>v. ((leader[x])&(({}=(decided[x]))&((a_decidedhash_primea=except(decided, x, ((decided[x]) \\cup {v})))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))))])&(({}=(decided[(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. bEx(Value, (\<lambda>v. ((leader[x])&(({}=(decided[x]))&((a_decidedhash_primea=except(decided, x, ((decided[x]) \\cup {v})))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))))]))&((a_decidedhash_primea=except(decided, (CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. bEx(Value, (\<lambda>v. ((leader[x])&(({}=(decided[x]))&((a_decidedhash_primea=except(decided, x, ((decided[x]) \\cup {v})))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))))), ((decided[(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. bEx(Value, (\<lambda>v. ((leader[x])&(({}=(decided[x]))&((a_decidedhash_primea=except(decided, x, ((decided[x]) \\cup {v})))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))))]) \\cup {v})))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))))" (is "?z_hjr&?z_hjd")
 by (rule zenon_ex_choose_0 [of "?z_hjo", OF z_Hjb])
 have z_Hjd: "?z_hjd"
 by (rule zenon_and_1 [OF z_Hjp])
 have z_Hjs_z_Hjd: "(\\E x:((x \\in Value)&((leader[(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. bEx(Value, (\<lambda>v. ((leader[x])&(({}=(decided[x]))&((a_decidedhash_primea=except(decided, x, ((decided[x]) \\cup {v})))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))))])&(({}=(decided[(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. bEx(Value, (\<lambda>v. ((leader[x])&(({}=(decided[x]))&((a_decidedhash_primea=except(decided, x, ((decided[x]) \\cup {v})))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))))]))&((a_decidedhash_primea=except(decided, (CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. bEx(Value, (\<lambda>v. ((leader[x])&(({}=(decided[x]))&((a_decidedhash_primea=except(decided, x, ((decided[x]) \\cup {v})))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))))), ((decided[(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. bEx(Value, (\<lambda>v. ((leader[x])&(({}=(decided[x]))&((a_decidedhash_primea=except(decided, x, ((decided[x]) \\cup {v})))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))))]) \\cup {x})))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))) == ?z_hjd" (is "?z_hjs == _")
 by (unfold bEx_def)
 have z_Hjs: "?z_hjs" (is "\\E x : ?z_hkc(x)")
 by (unfold z_Hjs_z_Hjd, fact z_Hjd)
 have z_Hkd: "?z_hkc((CHOOSE x:((x \\in Value)&((leader[(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. bEx(Value, (\<lambda>v. ((leader[x])&(({}=(decided[x]))&((a_decidedhash_primea=except(decided, x, ((decided[x]) \\cup {v})))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))))])&(({}=(decided[(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. bEx(Value, (\<lambda>v. ((leader[x])&(({}=(decided[x]))&((a_decidedhash_primea=except(decided, x, ((decided[x]) \\cup {v})))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))))]))&((a_decidedhash_primea=except(decided, (CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. bEx(Value, (\<lambda>v. ((leader[x])&(({}=(decided[x]))&((a_decidedhash_primea=except(decided, x, ((decided[x]) \\cup {v})))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))))), ((decided[(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. bEx(Value, (\<lambda>v. ((leader[x])&(({}=(decided[x]))&((a_decidedhash_primea=except(decided, x, ((decided[x]) \\cup {v})))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))))]) \\cup {x})))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))" (is "?z_hkf&?z_hkg")
 by (rule zenon_ex_choose_0 [of "?z_hkc", OF z_Hjs])
 have z_Hkg: "?z_hkg" (is "?z_hjg&?z_hkh")
 by (rule zenon_and_1 [OF z_Hkd])
 have z_Hkh: "?z_hkh" (is "?z_hji&?z_hki")
 by (rule zenon_and_1 [OF z_Hkg])
 have z_Hki: "?z_hki" (is "?z_hkj&?z_hgb")
 by (rule zenon_and_1 [OF z_Hkh])
 have z_Hgb: "?z_hgb" (is "?z_hgc&?z_hge")
 by (rule zenon_and_1 [OF z_Hki])
 have z_Hgc: "?z_hgc"
 by (rule zenon_and_0 [OF z_Hgb])
 have z_Hge: "?z_hge" (is "?z_hgf&?z_hgh")
 by (rule zenon_and_1 [OF z_Hgb])
 have z_Hgh: "?z_hgh" (is "?z_hgi&?z_hgk")
 by (rule zenon_and_1 [OF z_Hge])
 have z_Hgi: "?z_hgi"
 by (rule zenon_and_0 [OF z_Hgh])
 have z_Hkk_z_Hc: "(~(\\A x:((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x]))))))))) == (~?z_hho)" (is "?z_hkk == ?z_hc")
 by (unfold bAll_def)
 have z_Hkk: "?z_hkk" (is "~(\\A x : ?z_hkm(x))")
 by (unfold z_Hkk_z_Hc, fact z_Hc)
 have z_Hkn: "(\\E x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))" (is "\\E x : ?z_hko(x)")
 by (rule zenon_notallex_0 [of "?z_hkm", OF z_Hkk])
 have z_Hkp: "?z_hko((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x]))))))))))" (is "~(?z_hkq=>?z_hkr)")
 by (rule zenon_ex_choose_0 [of "?z_hko", OF z_Hkn])
 have z_Hkq: "?z_hkq"
 by (rule zenon_notimply_0 [OF z_Hkp])
 have z_Hks: "(~?z_hkr)"
 by (rule zenon_notimply_1 [OF z_Hkp])
 have z_Hkt_z_Hks: "(~(\\A x:((x \\in Node)=>((<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))>> \\in a_voteunde_msghash_primea)|(~(x \\in (a_voteshash_primea[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))]))))))) == (~?z_hkr)" (is "?z_hkt == ?z_hks")
 by (unfold bAll_def)
 have z_Hkt: "?z_hkt" (is "~(\\A x : ?z_hlb(x))")
 by (unfold z_Hkt_z_Hks, fact z_Hks)
 have z_Hlc: "(\\E x:(~((x \\in Node)=>((<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))>> \\in a_voteunde_msghash_primea)|(~(x \\in (a_voteshash_primea[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))])))))))" (is "\\E x : ?z_hle(x)")
 by (rule zenon_notallex_0 [of "?z_hlb", OF z_Hkt])
 have z_Hlf: "?z_hle((CHOOSE x:(~((x \\in Node)=>((<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))>> \\in a_voteunde_msghash_primea)|(~(x \\in (a_voteshash_primea[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))]))))))))" (is "~(?z_hlh=>?z_hli)")
 by (rule zenon_ex_choose_0 [of "?z_hle", OF z_Hlc])
 have z_Hlh: "?z_hlh"
 by (rule zenon_notimply_0 [OF z_Hlf])
 have z_Hlj: "(~?z_hli)" (is "~(?z_hlk|?z_hll)")
 by (rule zenon_notimply_1 [OF z_Hlf])
 have z_Hlm: "(~?z_hlk)"
 by (rule zenon_notor_0 [OF z_Hlj])
 have z_Hln: "(~?z_hll)" (is "~~?z_hlo")
 by (rule zenon_notor_1 [OF z_Hlj])
 have z_Hlo: "?z_hlo"
 by (rule zenon_notnot_0 [OF z_Hln])
 have z_Hlp: "(~(<<(CHOOSE x:(~((x \\in Node)=>((<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))>> \\in a_voteunde_msghash_primea)|(~(x \\in (a_voteshash_primea[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))]))))))), (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))>> \\in a_voteunde_msga))" (is "~?z_hlq")
 by (rule subst [where P="(\<lambda>zenon_Vgc. (~(<<(CHOOSE x:(~((x \\in Node)=>((<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))>> \\in a_voteunde_msghash_primea)|(~(x \\in (a_voteshash_primea[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))]))))))), (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))>> \\in zenon_Vgc)))", OF z_Hgi z_Hlm])
 have z_Hlw: "?z_hig((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x]))))))))))" (is "_=>?z_hlx")
 by (rule zenon_all_0 [of "?z_hig" "(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))", OF z_Hhx])
 show FALSE
 proof (rule zenon_imply [OF z_Hlw])
  assume z_Hly:"(~?z_hkq)"
  show FALSE
  by (rule notE [OF z_Hly z_Hkq])
 next
  assume z_Hlx:"?z_hlx"
  have z_Hlz_z_Hlx: "(\\A x:((x \\in Node)=>((<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))>> \\in a_voteunde_msga)|(~(x \\in (votes[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))])))))) == ?z_hlx" (is "?z_hlz == _")
  by (unfold bAll_def)
  have z_Hlz: "?z_hlz" (is "\\A x : ?z_hmf(x)")
  by (unfold z_Hlz_z_Hlx, fact z_Hlx)
  have z_Hmg: "?z_hmf((CHOOSE x:(~((x \\in Node)=>((<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))>> \\in a_voteunde_msghash_primea)|(~(x \\in (a_voteshash_primea[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))]))))))))" (is "_=>?z_hmh")
  by (rule zenon_all_0 [of "?z_hmf" "(CHOOSE x:(~((x \\in Node)=>((<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))>> \\in a_voteunde_msghash_primea)|(~(x \\in (a_voteshash_primea[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))])))))))", OF z_Hlz])
  show FALSE
  proof (rule zenon_imply [OF z_Hmg])
   assume z_Hmi:"(~?z_hlh)"
   show FALSE
   by (rule notE [OF z_Hmi z_Hlh])
  next
   assume z_Hmh:"?z_hmh" (is "_|?z_hmj")
   show FALSE
   proof (rule zenon_or [OF z_Hmh])
    assume z_Hlq:"?z_hlq"
    show FALSE
    by (rule notE [OF z_Hlp z_Hlq])
   next
    assume z_Hmj:"?z_hmj" (is "~?z_hmk")
    show FALSE
    proof (rule notE [OF z_Hmj])
     have z_Hml: "((a_voteshash_primea[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))])=(votes[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))]))" (is "?z_hgu=?z_hhi")
     proof (rule zenon_nnpp [of "(?z_hgu=?z_hhi)"])
      assume z_Hgt:"(?z_hgu~=?z_hhi)"
      show FALSE
      by (rule zenon_L1_ [OF z_Hgt z_Hgc])
     qed
     have z_Hmk: "?z_hmk"
     by (rule subst [where P="(\<lambda>zenon_Vun. ((CHOOSE x:(~((x \\in Node)=>((<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msghash_primea)|(~(VARJ \\in (a_voteshash_primea[x])))))))))>> \\in a_voteunde_msghash_primea)|(~(x \\in ?z_hgu)))))) \\in zenon_Vun))", OF z_Hml], fact z_Hlo)
     thus "?z_hmk" .
    qed
   qed
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 125"; *} qed
lemma ob'157:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
fixes Node
fixes Quorum
fixes Value
fixes a_voteunde_requestunde_msga a_voteunde_requestunde_msga'
fixes voted voted'
fixes a_voteunde_msga a_voteunde_msga'
fixes votes votes'
fixes leader leader'
fixes decided decided'
fixes a_requnde_historya a_requnde_historya'
(* usable definition vars suppressed *)
(* usable definition Spec suppressed *)
(* usable definition Symmetry suppressed *)
(* usable definition Safety suppressed *)
(* usable definition SplitVote suppressed *)
(* usable definition Liveness suppressed *)
assumes v'26: "(((((((a_voteunde_requestunde_msga) \<in> ((SUBSET (((Node) \<times> (Node))))))) & (((voted) \<in> ([(Node) \<rightarrow> (BOOLEAN)]))) & (((a_voteunde_msga) \<in> ((SUBSET (((Node) \<times> (Node))))))) & (((votes) \<in> ([(Node) \<rightarrow> ((SUBSET (Node)))]))) & (((leader) \<in> ([(Node) \<rightarrow> (BOOLEAN)]))) & (((decided) \<in> ([(Node) \<rightarrow> ((SUBSET (Value)))])))) & (\<forall> a_n1a \<in> (Node) : (\<forall> a_n2a \<in> (Node) : (\<forall> a_v1a \<in> (Value) : (\<forall> a_v2a \<in> (Value) : (((((((a_v1a) \<in> (fapply ((decided), (a_n1a))))) \<and> (((a_v2a) \<in> (fapply ((decided), (a_n2a))))))) \<Rightarrow> (((a_v1a) = (a_v2a))))))))) & (\<forall> VARI \<in> (Node) : (\<forall> VARJ \<in> (Node) : (((((<<(VARJ), (VARI)>>) \<in> (a_voteunde_msga))) \<or> ((~ (((VARJ) \<in> (fapply ((votes), (VARI))))))))))) & (\<forall> VARI \<in> (Node) : (\<exists> QJ \<in> (Quorum) : (\<forall> VALI \<in> (Value) : (((((QJ) \<subseteq> (fapply ((votes), (VARI))))) \<or> ((~ (((VALI) \<in> (fapply ((decided), (VARI)))))))))))) & (\<forall> VARI \<in> (Node) : (\<forall> VARJ \<in> (Node) : (((fapply ((voted), (VARI))) \<or> ((~ (((<<(VARI), (VARJ)>>) \<in> (a_voteunde_msga))))))))) & (\<forall> VARI \<in> (Node) : (\<exists> QJ \<in> (Quorum) : (((((QJ) \<subseteq> (fapply ((votes), (VARI))))) \<or> ((~ (fapply ((leader), (VARI))))))))) & (\<forall> VARI \<in> (Node) : (\<forall> VALI \<in> (Value) : (((fapply ((leader), (VARI))) \<or> ((~ (((VALI) \<in> (fapply ((decided), (VARI))))))))))) & (\<forall> VARI \<in> (Node) : (\<forall> VARJ \<in> (Node) : (\<forall> VARK \<in> (Node) : (((((((((VARI) = (VARK))) \<and> (((votes) = (votes))))) \<or> ((~ (((<<(VARJ), (VARI)>>) \<in> (a_voteunde_msga))))))) \<or> ((~ (((VARJ) \<in> (fapply ((votes), (VARK)))))))))))) & (\<forall> VARI \<in> (Node) : (\<forall> VARJ \<in> (Node) : (\<forall> VARK \<in> (Node) : (((((((((VARJ) = (VARK))) \<and> (((votes) = (votes))))) \<or> ((~ (((<<(VARI), (VARK)>>) \<in> (a_voteunde_msga))))))) \<or> ((~ (((<<(VARI), (VARJ)>>) \<in> (a_voteunde_msga))))))))))) \<and> ((((\<exists> i \<in> (Node) : (\<exists> j \<in> (Node) : (((~ (fapply ((voted), (i))))) & (((<<(j), (i)>>) \<in> (a_voteunde_requestunde_msga))) & ((((a_voteunde_requestunde_msghash_primea :: c)) = (((a_voteunde_requestunde_msga) \\ ({(<<(j), (i)>>)}))))) & ((((a_voteunde_msghash_primea :: c)) = (((a_voteunde_msga) \<union> ({(<<(i), (j)>>)}))))) & ((((a_votedhash_primea :: c)) = ([(voted) EXCEPT ![(i)] = (TRUE)]))) & ((((a_voteshash_primea :: c)) = (votes))) & ((((a_decidedhash_primea :: c)) = (decided))) & ((((a_leaderhash_primea :: c)) = (leader))) & ((((a_requnde_historyhash_primea :: c)) = (a_requnde_historya)))))) | (\<exists> i \<in> (Node) : (\<exists> j \<in> (Node) : ((fapply ((voted), (i))) & ((((a_voteunde_requestunde_msghash_primea :: c)) = (((a_voteunde_requestunde_msga) \\ ({(<<(j), (i)>>)}))))) & ((((a_voteunde_msghash_primea :: c)) = (a_voteunde_msga))) & ((((a_votedhash_primea :: c)) = (voted))) & ((((a_voteshash_primea :: c)) = (votes))) & ((((a_decidedhash_primea :: c)) = (decided))) & ((((a_leaderhash_primea :: c)) = (leader))) & ((((a_requnde_historyhash_primea :: c)) = (a_requnde_historya)))))) | (\<exists> i \<in> (Node) : (\<exists> j \<in> (Node) : ((((<<(j), (i)>>) \<in> (a_voteunde_msga))) & ((((a_voteshash_primea :: c)) = ([(votes) EXCEPT ![(i)] = (((fapply ((votes), (i))) \<union> ({(j)})))]))) & ((((a_votedhash_primea :: c)) = (voted))) & ((((a_voteunde_msghash_primea :: c)) = (a_voteunde_msga))) & ((((a_leaderhash_primea :: c)) = (leader))) & ((((a_decidedhash_primea :: c)) = (decided))) & ((((a_voteunde_requestunde_msghash_primea :: c)) = (a_voteunde_requestunde_msga))) & ((((a_requnde_historyhash_primea :: c)) = (a_requnde_historya)))))) | (\<exists> i \<in> (Node) : (\<exists> Q \<in> (Quorum) : ((((Q) \<subseteq> (fapply ((votes), (i))))) & ((((a_leaderhash_primea :: c)) = ([(leader) EXCEPT ![(i)] = (TRUE)]))) & ((((a_voteshash_primea :: c)) = (votes))) & ((((a_votedhash_primea :: c)) = (voted))) & ((((a_voteunde_msghash_primea :: c)) = (a_voteunde_msga))) & ((((a_decidedhash_primea :: c)) = (decided))) & ((((a_voteunde_requestunde_msghash_primea :: c)) = (a_voteunde_requestunde_msga))) & ((((a_requnde_historyhash_primea :: c)) = (a_requnde_historya)))))) | (\<exists> i \<in> (Node) : (\<exists> j \<in> (Node) : (\<exists> v \<in> (Value) : ((fapply ((leader), (i))) & ((({}) = (fapply ((decided), (i))))) & ((((a_decidedhash_primea :: c)) = ([(decided) EXCEPT ![(i)] = (((fapply ((decided), (i))) \<union> ({(v)})))]))) & ((((a_voteshash_primea :: c)) = (votes))) & ((((a_votedhash_primea :: c)) = (voted))) & ((((a_voteunde_msghash_primea :: c)) = (a_voteunde_msga))) & ((((a_leaderhash_primea :: c)) = (leader))) & ((((a_voteunde_requestunde_msghash_primea :: c)) = (a_voteunde_requestunde_msga))) & ((((a_requnde_historyhash_primea :: c)) = (a_requnde_historya)))))))) \<or> (\<exists> i \<in> (Node) : (\<exists> j \<in> (Node) : ((((<<(i), (j)>>) \<notin> (a_requnde_historya))) & (\<forall> a_dst2a \<in> (Node) : (((<<(i), (a_dst2a)>>) \<notin> (a_voteunde_requestunde_msga)))) & ((((a_voteunde_requestunde_msghash_primea :: c)) = (((a_voteunde_requestunde_msga) \<union> ({(<<(i), (j)>>)}))))) & ((((a_requnde_historyhash_primea :: c)) = (((a_requnde_historya) \<union> ({(<<(i), (j)>>)}))))) & (((((a_votedhash_primea :: c)) = (voted))) & ((((a_voteunde_msghash_primea :: c)) = (a_voteunde_msga))) & ((((a_voteshash_primea :: c)) = (votes))) & ((((a_leaderhash_primea :: c)) = (leader))) & ((((a_decidedhash_primea :: c)) = (decided)))))))))))"
assumes v'40: "(\<exists> i \<in> (Node) : (\<exists> j \<in> (Node) : ((((<<(j), (i)>>) \<in> (a_voteunde_msga))) & ((((a_voteshash_primea :: c)) = ([(votes) EXCEPT ![(i)] = (((fapply ((votes), (i))) \<union> ({(j)})))]))) & ((((a_votedhash_primea :: c)) = (voted))) & ((((a_voteunde_msghash_primea :: c)) = (a_voteunde_msga))) & ((((a_leaderhash_primea :: c)) = (leader))) & ((((a_decidedhash_primea :: c)) = (decided))) & ((((a_voteunde_requestunde_msghash_primea :: c)) = (a_voteunde_requestunde_msga))) & ((((a_requnde_historyhash_primea :: c)) = (a_requnde_historya))))))"
shows "(\<forall> VARI \<in> (Node) : (\<forall> VARJ \<in> (Node) : (((fapply (((a_votedhash_primea :: c)), (VARI))) \<or> ((~ (((<<(VARI), (VARJ)>>) \<in> ((a_voteunde_msghash_primea :: c))))))))))"(is "PROP ?ob'157")
proof -
ML_command {* writeln "*** TLAPS ENTER 157"; *}
show "PROP ?ob'157"

(* BEGIN ZENON INPUT
;; file=consensus_epr_IndProofs.tlaps/tlapm_6831e7.znn; PATH='/home/egolf/.opam/4.07.1/bin:/home/egolf/.local/bin:/home/egolf/bin:/home/egolf/mambaforge/bin:/home/egolf/mambaforge/condabin:/home/egolf/.opam/4.07.1/bin:/home/egolf/.local/bin:/home/egolf/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/home/egolf/.local/bin/gurobi952/linux64/bin:/home/egolf/Projects/apalache/bin:/home/egolf/opt/foxitsoftware/foxitreader:/home/egolf/.local/bin/gurobi952/linux64/bin:/home/egolf/Projects/apalache/bin:/home/egolf/opt/foxitsoftware/foxitreader:/usr/local/bin:/usr/local/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >consensus_epr_IndProofs.tlaps/tlapm_6831e7.znn.out
;; obligation #157
$hyp "v'26" (/\ (/\ (/\ (TLA.in a_voteunde_requestunde_msga
(TLA.SUBSET (TLA.prod Node Node))) (TLA.in voted
(TLA.FuncSet Node (TLA.set T. F.))) (TLA.in a_voteunde_msga
(TLA.SUBSET (TLA.prod Node Node))) (TLA.in votes
(TLA.FuncSet Node (TLA.SUBSET Node))) (TLA.in leader
(TLA.FuncSet Node (TLA.set T. F.))) (TLA.in decided
(TLA.FuncSet Node (TLA.SUBSET Value))))
(TLA.bAll Node ((a_n1a) (TLA.bAll Node ((a_n2a) (TLA.bAll Value ((a_v1a) (TLA.bAll Value ((a_v2a) (=> (/\ (TLA.in a_v1a
(TLA.fapply decided a_n1a)) (TLA.in a_v2a (TLA.fapply decided a_n2a)))
(= a_v1a a_v2a))))))))))
(TLA.bAll Node ((VARI) (TLA.bAll Node ((VARJ) (\/ (TLA.in (TLA.tuple VARJ
VARI) a_voteunde_msga) (-. (TLA.in VARJ (TLA.fapply votes VARI))))))))
(TLA.bAll Node ((VARI) (TLA.bEx Quorum ((QJ) (TLA.bAll Value ((VALI) (\/ (TLA.subseteq QJ
(TLA.fapply votes VARI)) (-. (TLA.in VALI (TLA.fapply decided VARI))))))))))
(TLA.bAll Node ((VARI) (TLA.bAll Node ((VARJ) (\/ (TLA.fapply voted VARI)
(-. (TLA.in (TLA.tuple VARI VARJ) a_voteunde_msga)))))))
(TLA.bAll Node ((VARI) (TLA.bEx Quorum ((QJ) (\/ (TLA.subseteq QJ
(TLA.fapply votes VARI)) (-. (TLA.fapply leader VARI)))))))
(TLA.bAll Node ((VARI) (TLA.bAll Value ((VALI) (\/ (TLA.fapply leader VARI)
(-. (TLA.in VALI (TLA.fapply decided VARI))))))))
(TLA.bAll Node ((VARI) (TLA.bAll Node ((VARJ) (TLA.bAll Node ((VARK) (\/ (\/ (/\ (= VARI
VARK) (= votes votes)) (-. (TLA.in (TLA.tuple VARJ VARI) a_voteunde_msga)))
(-. (TLA.in VARJ (TLA.fapply votes VARK))))))))))
(TLA.bAll Node ((VARI) (TLA.bAll Node ((VARJ) (TLA.bAll Node ((VARK) (\/ (\/ (/\ (= VARJ
VARK) (= votes votes)) (-. (TLA.in (TLA.tuple VARI VARK) a_voteunde_msga)))
(-. (TLA.in (TLA.tuple VARI VARJ) a_voteunde_msga))))))))))
(\/ (\/ (TLA.bEx Node ((i) (TLA.bEx Node ((j) (/\ (-. (TLA.fapply voted i))
(TLA.in (TLA.tuple j i) a_voteunde_requestunde_msga)
(= a_voteunde_requestunde_msghash_primea
(TLA.setminus a_voteunde_requestunde_msga (TLA.set (TLA.tuple j i))))
(= a_voteunde_msghash_primea (TLA.cup a_voteunde_msga (TLA.set (TLA.tuple i
j)))) (= a_votedhash_primea (TLA.except voted i T.)) (= a_voteshash_primea
votes) (= a_decidedhash_primea decided) (= a_leaderhash_primea leader)
(= a_requnde_historyhash_primea a_requnde_historya))))))
(TLA.bEx Node ((i) (TLA.bEx Node ((j) (/\ (TLA.fapply voted i)
(= a_voteunde_requestunde_msghash_primea
(TLA.setminus a_voteunde_requestunde_msga (TLA.set (TLA.tuple j i))))
(= a_voteunde_msghash_primea a_voteunde_msga) (= a_votedhash_primea voted)
(= a_voteshash_primea votes) (= a_decidedhash_primea decided)
(= a_leaderhash_primea leader) (= a_requnde_historyhash_primea
a_requnde_historya))))))
(TLA.bEx Node ((i) (TLA.bEx Node ((j) (/\ (TLA.in (TLA.tuple j i)
a_voteunde_msga) (= a_voteshash_primea
(TLA.except votes i (TLA.cup (TLA.fapply votes i) (TLA.set j))))
(= a_votedhash_primea voted) (= a_voteunde_msghash_primea a_voteunde_msga)
(= a_leaderhash_primea leader) (= a_decidedhash_primea decided)
(= a_voteunde_requestunde_msghash_primea a_voteunde_requestunde_msga)
(= a_requnde_historyhash_primea a_requnde_historya))))))
(TLA.bEx Node ((i) (TLA.bEx Quorum ((Q) (/\ (TLA.subseteq Q
(TLA.fapply votes i)) (= a_leaderhash_primea (TLA.except leader i T.))
(= a_voteshash_primea votes) (= a_votedhash_primea voted)
(= a_voteunde_msghash_primea a_voteunde_msga) (= a_decidedhash_primea
decided) (= a_voteunde_requestunde_msghash_primea
a_voteunde_requestunde_msga) (= a_requnde_historyhash_primea
a_requnde_historya))))))
(TLA.bEx Node ((i) (TLA.bEx Node ((j) (TLA.bEx Value ((v) (/\ (TLA.fapply leader i)
(= TLA.emptyset (TLA.fapply decided i)) (= a_decidedhash_primea
(TLA.except decided i (TLA.cup (TLA.fapply decided i) (TLA.set v))))
(= a_voteshash_primea votes) (= a_votedhash_primea voted)
(= a_voteunde_msghash_primea a_voteunde_msga) (= a_leaderhash_primea leader)
(= a_voteunde_requestunde_msghash_primea a_voteunde_requestunde_msga)
(= a_requnde_historyhash_primea a_requnde_historya)))))))))
(TLA.bEx Node ((i) (TLA.bEx Node ((j) (/\ (-. (TLA.in (TLA.tuple i j)
a_requnde_historya)) (TLA.bAll Node ((a_dst2a) (-. (TLA.in (TLA.tuple i
a_dst2a) a_voteunde_requestunde_msga))))
(= a_voteunde_requestunde_msghash_primea (TLA.cup a_voteunde_requestunde_msga
(TLA.set (TLA.tuple i j)))) (= a_requnde_historyhash_primea
(TLA.cup a_requnde_historya (TLA.set (TLA.tuple i j))))
(/\ (= a_votedhash_primea voted) (= a_voteunde_msghash_primea
a_voteunde_msga) (= a_voteshash_primea votes) (= a_leaderhash_primea leader)
(= a_decidedhash_primea
decided)))))))))
$hyp "v'40" (TLA.bEx Node ((i) (TLA.bEx Node ((j) (/\ (TLA.in (TLA.tuple j i)
a_voteunde_msga) (= a_voteshash_primea
(TLA.except votes i (TLA.cup (TLA.fapply votes i) (TLA.set j))))
(= a_votedhash_primea voted) (= a_voteunde_msghash_primea a_voteunde_msga)
(= a_leaderhash_primea leader) (= a_decidedhash_primea decided)
(= a_voteunde_requestunde_msghash_primea a_voteunde_requestunde_msga)
(= a_requnde_historyhash_primea
a_requnde_historya))))))
$goal (TLA.bAll Node ((VARI) (TLA.bAll Node ((VARJ) (\/ (TLA.fapply a_votedhash_primea VARI)
(-. (TLA.in (TLA.tuple VARI VARJ)
a_voteunde_msghash_primea)))))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Ha:"((((a_voteunde_requestunde_msga \\in SUBSET(prod(Node, Node)))&((voted \\in FuncSet(Node, {TRUE, FALSE}))&((a_voteunde_msga \\in SUBSET(prod(Node, Node)))&((votes \\in FuncSet(Node, SUBSET(Node)))&((leader \\in FuncSet(Node, {TRUE, FALSE}))&(decided \\in FuncSet(Node, SUBSET(Value))))))))&(bAll(Node, (\<lambda>a_n1a. bAll(Node, (\<lambda>a_n2a. bAll(Value, (\<lambda>a_v1a. bAll(Value, (\<lambda>a_v2a. (((a_v1a \\in (decided[a_n1a]))&(a_v2a \\in (decided[a_n2a])))=>(a_v1a=a_v2a))))))))))&(bAll(Node, (\<lambda>VARI. bAll(Node, (\<lambda>VARJ. ((<<VARJ, VARI>> \\in a_voteunde_msga)|(~(VARJ \\in (votes[VARI]))))))))&(bAll(Node, (\<lambda>VARI. bEx(Quorum, (\<lambda>QJ. bAll(Value, (\<lambda>VALI. ((QJ \\subseteq (votes[VARI]))|(~(VALI \\in (decided[VARI]))))))))))&(bAll(Node, (\<lambda>VARI. bAll(Node, (\<lambda>VARJ. ((voted[VARI])|(~(<<VARI, VARJ>> \\in a_voteunde_msga)))))))&(bAll(Node, (\<lambda>VARI. bEx(Quorum, (\<lambda>QJ. ((QJ \\subseteq (votes[VARI]))|(~(leader[VARI])))))))&(bAll(Node, (\<lambda>VARI. bAll(Value, (\<lambda>VALI. ((leader[VARI])|(~(VALI \\in (decided[VARI]))))))))&(bAll(Node, (\<lambda>VARI. bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARI=VARK)&(votes=votes))|(~(<<VARJ, VARI>> \\in a_voteunde_msga)))|(~(VARJ \\in (votes[VARK]))))))))))&bAll(Node, (\<lambda>VARI. bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(votes=votes))|(~(<<VARI, VARK>> \\in a_voteunde_msga)))|(~(<<VARI, VARJ>> \\in a_voteunde_msga)))))))))))))))))&((bEx(Node, (\<lambda>i. bEx(Node, (\<lambda>j. ((~(voted[i]))&((<<j, i>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, i>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<i, j>>}))&((a_votedhash_primea=except(voted, i, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))|(bEx(Node, (\<lambda>i. bEx(Node, (\<lambda>j. ((voted[i])&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, i>>}))&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_votedhash_primea=voted)&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))|(bEx(Node, (\<lambda>i. bEx(Node, (\<lambda>j. ((<<j, i>> \\in a_voteunde_msga)&((a_voteshash_primea=except(votes, i, ((votes[i]) \\cup {j})))&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_decidedhash_primea=decided)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))|(bEx(Node, (\<lambda>i. bEx(Quorum, (\<lambda>Q. ((Q \\subseteq (votes[i]))&((a_leaderhash_primea=except(leader, i, TRUE))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_decidedhash_primea=decided)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))|bEx(Node, (\<lambda>i. bEx(Node, (\<lambda>j. bEx(Value, (\<lambda>v. ((leader[i])&(({}=(decided[i]))&((a_decidedhash_primea=except(decided, i, ((decided[i]) \\cup {v})))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))))))))|bEx(Node, (\<lambda>i. bEx(Node, (\<lambda>j. ((~(<<i, j>> \\in a_requnde_historya))&(bAll(Node, (\<lambda>a_dst2a. (~(<<i, a_dst2a>> \\in a_voteunde_requestunde_msga))))&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\cup {<<i, j>>}))&((a_requnde_historyhash_primea=(a_requnde_historya \\cup {<<i, j>>}))&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_voteshash_primea=votes)&((a_leaderhash_primea=leader)&(a_decidedhash_primea=decided)))))))))))))))" (is "?z_hd&?z_hff")
 using v'26 by blast
 have z_Hb:"bEx(Node, (\<lambda>i. bEx(Node, (\<lambda>j. ((<<j, i>> \\in a_voteunde_msga)&((a_voteshash_primea=except(votes, i, ((votes[i]) \\cup {j})))&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_decidedhash_primea=decided)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))" (is "?z_hb")
 using v'40 by blast
 have zenon_L1_: "((voted[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea))))))))])=TRUE) ==> (~(a_votedhash_primea[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea))))))))])) ==> (a_votedhash_primea=voted) ==> FALSE" (is "?z_hkf ==> ?z_hkt ==> ?z_hhe ==> FALSE")
 proof -
  assume z_Hkf:"?z_hkf" (is "?z_hkg=?z_hp")
  assume z_Hkt:"?z_hkt" (is "~?z_hku")
  assume z_Hhe:"?z_hhe"
  show FALSE
  proof (rule zenon_np_eq_l [of "?z_hku" "?z_hkg" "?z_hp", OF z_Hkt z_Hkf])
   assume z_Hkv:"(?z_hku~=?z_hkg)"
   show FALSE
   proof (rule zenon_noteq [of "?z_hkg"])
    have z_Hkw: "(?z_hkg~=?z_hkg)"
    by (rule subst [where P="(\<lambda>zenon_Vyga. ((zenon_Vyga[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea))))))))])~=?z_hkg))", OF z_Hhe], fact z_Hkv)
    thus "(?z_hkg~=?z_hkg)" .
   qed
  next
   assume z_Hlb:"(~?z_hp)"
   show FALSE
   by (rule zenon_nottrue [OF z_Hlb])
  qed
 qed
 assume z_Hc:"(~bAll(Node, (\<lambda>VARI. bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[VARI])|(~(<<VARI, VARJ>> \\in a_voteunde_msghash_primea))))))))" (is "~?z_hlc")
 have z_Hd: "?z_hd" (is "?z_he&?z_hbh")
 by (rule zenon_and_0 [OF z_Ha])
 have z_He: "?z_he" (is "?z_hf&?z_hk")
 by (rule zenon_and_0 [OF z_Hd])
 have z_Hbh: "?z_hbh" (is "?z_hbi&?z_hcb")
 by (rule zenon_and_1 [OF z_Hd])
 have z_Hcb: "?z_hcb" (is "?z_hcc&?z_hco")
 by (rule zenon_and_1 [OF z_Hbh])
 have z_Hco: "?z_hco" (is "?z_hcp&?z_hdd")
 by (rule zenon_and_1 [OF z_Hcb])
 have z_Hdd: "?z_hdd" (is "?z_hde&?z_hdn")
 by (rule zenon_and_1 [OF z_Hco])
 have z_Hde: "?z_hde"
 by (rule zenon_and_0 [OF z_Hdd])
 have z_Hk: "?z_hk" (is "?z_hl&?z_hr")
 by (rule zenon_and_1 [OF z_He])
 have z_Hl: "?z_hl"
 by (rule zenon_and_0 [OF z_Hk])
 have z_Hlk_z_Hde: "(\\A x:((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((voted[x])|(~(<<x, VARJ>> \\in a_voteunde_msga))))))) == ?z_hde" (is "?z_hlk == _")
 by (unfold bAll_def)
 have z_Hlk: "?z_hlk" (is "\\A x : ?z_hls(x)")
 by (unfold z_Hlk_z_Hde, fact z_Hde)
 have z_Hlt_z_Hb: "(\\E x:((x \\in Node)&bEx(Node, (\<lambda>j. ((<<j, x>> \\in a_voteunde_msga)&((a_voteshash_primea=except(votes, x, ((votes[x]) \\cup {j})))&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_decidedhash_primea=decided)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))) == ?z_hb" (is "?z_hlt == _")
 by (unfold bEx_def)
 have z_Hlt: "?z_hlt" (is "\\E x : ?z_hmf(x)")
 by (unfold z_Hlt_z_Hb, fact z_Hb)
 have z_Hmg: "?z_hmf((CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((<<j, x>> \\in a_voteunde_msga)&((a_voteshash_primea=except(votes, x, ((votes[x]) \\cup {j})))&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_decidedhash_primea=decided)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))" (is "?z_hmi&?z_hmj")
 by (rule zenon_ex_choose_0 [of "?z_hmf", OF z_Hlt])
 have z_Hmj: "?z_hmj"
 by (rule zenon_and_1 [OF z_Hmg])
 have z_Hmk_z_Hmj: "(\\E x:((x \\in Node)&((<<x, (CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((<<j, x>> \\in a_voteunde_msga)&((a_voteshash_primea=except(votes, x, ((votes[x]) \\cup {j})))&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_decidedhash_primea=decided)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))>> \\in a_voteunde_msga)&((a_voteshash_primea=except(votes, (CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((<<j, x>> \\in a_voteunde_msga)&((a_voteshash_primea=except(votes, x, ((votes[x]) \\cup {j})))&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_decidedhash_primea=decided)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))), ((votes[(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((<<j, x>> \\in a_voteunde_msga)&((a_voteshash_primea=except(votes, x, ((votes[x]) \\cup {j})))&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_decidedhash_primea=decided)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))]) \\cup {x})))&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_decidedhash_primea=decided)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))) == ?z_hmj" (is "?z_hmk == _")
 by (unfold bEx_def)
 have z_Hmk: "?z_hmk" (is "\\E x : ?z_hmv(x)")
 by (unfold z_Hmk_z_Hmj, fact z_Hmj)
 have z_Hmw: "?z_hmv((CHOOSE x:((x \\in Node)&((<<x, (CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((<<j, x>> \\in a_voteunde_msga)&((a_voteshash_primea=except(votes, x, ((votes[x]) \\cup {j})))&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_decidedhash_primea=decided)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))>> \\in a_voteunde_msga)&((a_voteshash_primea=except(votes, (CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((<<j, x>> \\in a_voteunde_msga)&((a_voteshash_primea=except(votes, x, ((votes[x]) \\cup {j})))&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_decidedhash_primea=decided)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))), ((votes[(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((<<j, x>> \\in a_voteunde_msga)&((a_voteshash_primea=except(votes, x, ((votes[x]) \\cup {j})))&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_decidedhash_primea=decided)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))]) \\cup {x})))&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_decidedhash_primea=decided)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))" (is "?z_hmy&?z_hmz")
 by (rule zenon_ex_choose_0 [of "?z_hmv", OF z_Hmk])
 have z_Hmz: "?z_hmz" (is "?z_hna&?z_hnb")
 by (rule zenon_and_1 [OF z_Hmw])
 have z_Hnb: "?z_hnb" (is "?z_hnc&?z_hhr")
 by (rule zenon_and_1 [OF z_Hmz])
 have z_Hhr: "?z_hhr" (is "?z_hhe&?z_hhs")
 by (rule zenon_and_1 [OF z_Hnb])
 have z_Hhe: "?z_hhe"
 by (rule zenon_and_0 [OF z_Hhr])
 have z_Hhs: "?z_hhs" (is "?z_hhc&?z_hht")
 by (rule zenon_and_1 [OF z_Hhr])
 have z_Hhc: "?z_hhc"
 by (rule zenon_and_0 [OF z_Hhs])
 have z_Hnd_z_Hc: "(~(\\A x:((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))) == (~?z_hlc)" (is "?z_hnd == ?z_hc")
 by (unfold bAll_def)
 have z_Hnd: "?z_hnd" (is "~(\\A x : ?z_hnf(x))")
 by (unfold z_Hnd_z_Hc, fact z_Hc)
 have z_Hng: "(\\E x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea))))))))" (is "\\E x : ?z_hnh(x)")
 by (rule zenon_notallex_0 [of "?z_hnf", OF z_Hnd])
 have z_Hni: "?z_hnh((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))" (is "~(?z_hnj=>?z_hnk)")
 by (rule zenon_ex_choose_0 [of "?z_hnh", OF z_Hng])
 have z_Hnj: "?z_hnj"
 by (rule zenon_notimply_0 [OF z_Hni])
 have z_Hnl: "(~?z_hnk)"
 by (rule zenon_notimply_1 [OF z_Hni])
 have z_Hnm_z_Hnl: "(~(\\A x:((x \\in Node)=>((a_votedhash_primea[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea))))))))])|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))), x>> \\in a_voteunde_msghash_primea)))))) == (~?z_hnk)" (is "?z_hnm == ?z_hnl")
 by (unfold bAll_def)
 have z_Hnm: "?z_hnm" (is "~(\\A x : ?z_hnt(x))")
 by (unfold z_Hnm_z_Hnl, fact z_Hnl)
 have z_Hnu: "(\\E x:(~((x \\in Node)=>((a_votedhash_primea[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea))))))))])|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))), x>> \\in a_voteunde_msghash_primea))))))" (is "\\E x : ?z_hnw(x)")
 by (rule zenon_notallex_0 [of "?z_hnt", OF z_Hnm])
 have z_Hnx: "?z_hnw((CHOOSE x:(~((x \\in Node)=>((a_votedhash_primea[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea))))))))])|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))), x>> \\in a_voteunde_msghash_primea)))))))" (is "~(?z_hnz=>?z_hoa)")
 by (rule zenon_ex_choose_0 [of "?z_hnw", OF z_Hnu])
 have z_Hnz: "?z_hnz"
 by (rule zenon_notimply_0 [OF z_Hnx])
 have z_Hob: "(~?z_hoa)" (is "~(?z_hku|?z_hoc)")
 by (rule zenon_notimply_1 [OF z_Hnx])
 have z_Hkt: "(~?z_hku)"
 by (rule zenon_notor_0 [OF z_Hob])
 have z_Hod: "(~?z_hoc)" (is "~~?z_hoe")
 by (rule zenon_notor_1 [OF z_Hob])
 have z_Hoe: "?z_hoe"
 by (rule zenon_notnot_0 [OF z_Hod])
 have z_Hof: "(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))), (CHOOSE x:(~((x \\in Node)=>(?z_hku|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))), x>> \\in a_voteunde_msghash_primea))))))>> \\in a_voteunde_msga)" (is "?z_hof")
 by (rule subst [where P="(\<lambda>zenon_Vyb. (<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))), (CHOOSE x:(~((x \\in Node)=>(?z_hku|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))), x>> \\in a_voteunde_msghash_primea))))))>> \\in zenon_Vyb))", OF z_Hhc z_Hoe])
 have z_Hok: "?z_hls((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))" (is "_=>?z_hol")
 by (rule zenon_all_0 [of "?z_hls" "(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea))))))))", OF z_Hlk])
 show FALSE
 proof (rule zenon_imply [OF z_Hok])
  assume z_Hom:"(~?z_hnj)"
  show FALSE
  by (rule notE [OF z_Hom z_Hnj])
 next
  assume z_Hol:"?z_hol"
  have z_Hon_z_Hol: "(\\A x:((x \\in Node)=>((voted[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea))))))))])|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))), x>> \\in a_voteunde_msga))))) == ?z_hol" (is "?z_hon == _")
  by (unfold bAll_def)
  have z_Hon: "?z_hon" (is "\\A x : ?z_hos(x)")
  by (unfold z_Hon_z_Hol, fact z_Hol)
  have z_Hot: "?z_hos((CHOOSE x:(~((x \\in Node)=>(?z_hku|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))), x>> \\in a_voteunde_msghash_primea)))))))" (is "_=>?z_hou")
  by (rule zenon_all_0 [of "?z_hos" "(CHOOSE x:(~((x \\in Node)=>(?z_hku|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))), x>> \\in a_voteunde_msghash_primea))))))", OF z_Hon])
  show FALSE
  proof (rule zenon_imply [OF z_Hot])
   assume z_Hov:"(~?z_hnz)"
   show FALSE
   by (rule notE [OF z_Hov z_Hnz])
  next
   assume z_Hou:"?z_hou" (is "?z_hkg|?z_how")
   show FALSE
   proof (rule zenon_or [OF z_Hou])
    assume z_Hkg:"?z_hkg"
    have z_Hox: "(\\A zenon_Vea:((zenon_Vea \\in Node)=>((voted[zenon_Vea]) \\in {TRUE, FALSE})))" (is "\\A x : ?z_hpd(x)")
    by (rule zenon_in_funcset_2 [of "voted" "Node" "{TRUE, FALSE}", OF z_Hl])
    have z_Hpe: "?z_hpd((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))" (is "_=>?z_hpf")
    by (rule zenon_all_0 [of "?z_hpd" "(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea))))))))", OF z_Hox])
    show FALSE
    proof (rule zenon_imply [OF z_Hpe])
     assume z_Hom:"(~?z_hnj)"
     show FALSE
     by (rule notE [OF z_Hom z_Hnj])
    next
     assume z_Hpf:"?z_hpf"
     show FALSE
     proof (rule zenon_in_addElt [of "?z_hkg" "TRUE" "{FALSE}", OF z_Hpf])
      assume z_Hkf:"(?z_hkg=TRUE)" (is "_=?z_hp")
      show FALSE
      by (rule zenon_L1_ [OF z_Hkf z_Hkt z_Hhe])
     next
      assume z_Hph:"(?z_hkg \\in {FALSE})" (is "?z_hph")
      show FALSE
      proof (rule zenon_in_addElt [of "?z_hkg" "FALSE" "{}", OF z_Hph])
       assume z_Hpj:"(?z_hkg=FALSE)" (is "_=?z_hq")
       have z_Hpk: "(~?z_hkg)"
       by (rule zenon_eq_x_false_0 [of "?z_hkg", OF z_Hpj])
       show FALSE
       by (rule notE [OF z_Hpk z_Hkg])
      next
       assume z_Hpl:"(?z_hkg \\in {})" (is "?z_hpl")
       show FALSE
       by (rule zenon_in_emptyset [of "?z_hkg", OF z_Hpl])
      qed
     qed
    qed
   next
    assume z_How:"?z_how"
    show FALSE
    by (rule notE [OF z_How z_Hof])
   qed
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 157"; *} qed
lemma ob'155:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
fixes Node
fixes Quorum
fixes Value
fixes a_voteunde_requestunde_msga a_voteunde_requestunde_msga'
fixes voted voted'
fixes a_voteunde_msga a_voteunde_msga'
fixes votes votes'
fixes leader leader'
fixes decided decided'
fixes a_requnde_historya a_requnde_historya'
(* usable definition vars suppressed *)
(* usable definition Spec suppressed *)
(* usable definition Symmetry suppressed *)
(* usable definition Safety suppressed *)
(* usable definition SplitVote suppressed *)
(* usable definition Liveness suppressed *)
assumes v'26: "(((((((a_voteunde_requestunde_msga) \<in> ((SUBSET (((Node) \<times> (Node))))))) & (((voted) \<in> ([(Node) \<rightarrow> (BOOLEAN)]))) & (((a_voteunde_msga) \<in> ((SUBSET (((Node) \<times> (Node))))))) & (((votes) \<in> ([(Node) \<rightarrow> ((SUBSET (Node)))]))) & (((leader) \<in> ([(Node) \<rightarrow> (BOOLEAN)]))) & (((decided) \<in> ([(Node) \<rightarrow> ((SUBSET (Value)))])))) & (\<forall> a_n1a \<in> (Node) : (\<forall> a_n2a \<in> (Node) : (\<forall> a_v1a \<in> (Value) : (\<forall> a_v2a \<in> (Value) : (((((((a_v1a) \<in> (fapply ((decided), (a_n1a))))) \<and> (((a_v2a) \<in> (fapply ((decided), (a_n2a))))))) \<Rightarrow> (((a_v1a) = (a_v2a))))))))) & (\<forall> VARI \<in> (Node) : (\<forall> VARJ \<in> (Node) : (((((<<(VARJ), (VARI)>>) \<in> (a_voteunde_msga))) \<or> ((~ (((VARJ) \<in> (fapply ((votes), (VARI))))))))))) & (\<forall> VARI \<in> (Node) : (\<exists> QJ \<in> (Quorum) : (\<forall> VALI \<in> (Value) : (((((QJ) \<subseteq> (fapply ((votes), (VARI))))) \<or> ((~ (((VALI) \<in> (fapply ((decided), (VARI)))))))))))) & (\<forall> VARI \<in> (Node) : (\<forall> VARJ \<in> (Node) : (((fapply ((voted), (VARI))) \<or> ((~ (((<<(VARI), (VARJ)>>) \<in> (a_voteunde_msga))))))))) & (\<forall> VARI \<in> (Node) : (\<exists> QJ \<in> (Quorum) : (((((QJ) \<subseteq> (fapply ((votes), (VARI))))) \<or> ((~ (fapply ((leader), (VARI))))))))) & (\<forall> VARI \<in> (Node) : (\<forall> VALI \<in> (Value) : (((fapply ((leader), (VARI))) \<or> ((~ (((VALI) \<in> (fapply ((decided), (VARI))))))))))) & (\<forall> VARI \<in> (Node) : (\<forall> VARJ \<in> (Node) : (\<forall> VARK \<in> (Node) : (((((((((VARI) = (VARK))) \<and> (((votes) = (votes))))) \<or> ((~ (((<<(VARJ), (VARI)>>) \<in> (a_voteunde_msga))))))) \<or> ((~ (((VARJ) \<in> (fapply ((votes), (VARK)))))))))))) & (\<forall> VARI \<in> (Node) : (\<forall> VARJ \<in> (Node) : (\<forall> VARK \<in> (Node) : (((((((((VARJ) = (VARK))) \<and> (((votes) = (votes))))) \<or> ((~ (((<<(VARI), (VARK)>>) \<in> (a_voteunde_msga))))))) \<or> ((~ (((<<(VARI), (VARJ)>>) \<in> (a_voteunde_msga))))))))))) \<and> ((((\<exists> i \<in> (Node) : (\<exists> j \<in> (Node) : (((~ (fapply ((voted), (i))))) & (((<<(j), (i)>>) \<in> (a_voteunde_requestunde_msga))) & ((((a_voteunde_requestunde_msghash_primea :: c)) = (((a_voteunde_requestunde_msga) \\ ({(<<(j), (i)>>)}))))) & ((((a_voteunde_msghash_primea :: c)) = (((a_voteunde_msga) \<union> ({(<<(i), (j)>>)}))))) & ((((a_votedhash_primea :: c)) = ([(voted) EXCEPT ![(i)] = (TRUE)]))) & ((((a_voteshash_primea :: c)) = (votes))) & ((((a_decidedhash_primea :: c)) = (decided))) & ((((a_leaderhash_primea :: c)) = (leader))) & ((((a_requnde_historyhash_primea :: c)) = (a_requnde_historya)))))) | (\<exists> i \<in> (Node) : (\<exists> j \<in> (Node) : ((fapply ((voted), (i))) & ((((a_voteunde_requestunde_msghash_primea :: c)) = (((a_voteunde_requestunde_msga) \\ ({(<<(j), (i)>>)}))))) & ((((a_voteunde_msghash_primea :: c)) = (a_voteunde_msga))) & ((((a_votedhash_primea :: c)) = (voted))) & ((((a_voteshash_primea :: c)) = (votes))) & ((((a_decidedhash_primea :: c)) = (decided))) & ((((a_leaderhash_primea :: c)) = (leader))) & ((((a_requnde_historyhash_primea :: c)) = (a_requnde_historya)))))) | (\<exists> i \<in> (Node) : (\<exists> j \<in> (Node) : ((((<<(j), (i)>>) \<in> (a_voteunde_msga))) & ((((a_voteshash_primea :: c)) = ([(votes) EXCEPT ![(i)] = (((fapply ((votes), (i))) \<union> ({(j)})))]))) & ((((a_votedhash_primea :: c)) = (voted))) & ((((a_voteunde_msghash_primea :: c)) = (a_voteunde_msga))) & ((((a_leaderhash_primea :: c)) = (leader))) & ((((a_decidedhash_primea :: c)) = (decided))) & ((((a_voteunde_requestunde_msghash_primea :: c)) = (a_voteunde_requestunde_msga))) & ((((a_requnde_historyhash_primea :: c)) = (a_requnde_historya)))))) | (\<exists> i \<in> (Node) : (\<exists> Q \<in> (Quorum) : ((((Q) \<subseteq> (fapply ((votes), (i))))) & ((((a_leaderhash_primea :: c)) = ([(leader) EXCEPT ![(i)] = (TRUE)]))) & ((((a_voteshash_primea :: c)) = (votes))) & ((((a_votedhash_primea :: c)) = (voted))) & ((((a_voteunde_msghash_primea :: c)) = (a_voteunde_msga))) & ((((a_decidedhash_primea :: c)) = (decided))) & ((((a_voteunde_requestunde_msghash_primea :: c)) = (a_voteunde_requestunde_msga))) & ((((a_requnde_historyhash_primea :: c)) = (a_requnde_historya)))))) | (\<exists> i \<in> (Node) : (\<exists> j \<in> (Node) : (\<exists> v \<in> (Value) : ((fapply ((leader), (i))) & ((({}) = (fapply ((decided), (i))))) & ((((a_decidedhash_primea :: c)) = ([(decided) EXCEPT ![(i)] = (((fapply ((decided), (i))) \<union> ({(v)})))]))) & ((((a_voteshash_primea :: c)) = (votes))) & ((((a_votedhash_primea :: c)) = (voted))) & ((((a_voteunde_msghash_primea :: c)) = (a_voteunde_msga))) & ((((a_leaderhash_primea :: c)) = (leader))) & ((((a_voteunde_requestunde_msghash_primea :: c)) = (a_voteunde_requestunde_msga))) & ((((a_requnde_historyhash_primea :: c)) = (a_requnde_historya)))))))) \<or> (\<exists> i \<in> (Node) : (\<exists> j \<in> (Node) : ((((<<(i), (j)>>) \<notin> (a_requnde_historya))) & (\<forall> a_dst2a \<in> (Node) : (((<<(i), (a_dst2a)>>) \<notin> (a_voteunde_requestunde_msga)))) & ((((a_voteunde_requestunde_msghash_primea :: c)) = (((a_voteunde_requestunde_msga) \<union> ({(<<(i), (j)>>)}))))) & ((((a_requnde_historyhash_primea :: c)) = (((a_requnde_historya) \<union> ({(<<(i), (j)>>)}))))) & (((((a_votedhash_primea :: c)) = (voted))) & ((((a_voteunde_msghash_primea :: c)) = (a_voteunde_msga))) & ((((a_voteshash_primea :: c)) = (votes))) & ((((a_leaderhash_primea :: c)) = (leader))) & ((((a_decidedhash_primea :: c)) = (decided)))))))))))"
assumes v'39: "(\<exists> i \<in> (Node) : (\<exists> j \<in> (Node) : ((fapply ((voted), (i))) & ((((a_voteunde_requestunde_msghash_primea :: c)) = (((a_voteunde_requestunde_msga) \\ ({(<<(j), (i)>>)}))))) & ((((a_voteunde_msghash_primea :: c)) = (a_voteunde_msga))) & ((((a_votedhash_primea :: c)) = (voted))) & ((((a_voteshash_primea :: c)) = (votes))) & ((((a_decidedhash_primea :: c)) = (decided))) & ((((a_leaderhash_primea :: c)) = (leader))) & ((((a_requnde_historyhash_primea :: c)) = (a_requnde_historya))))))"
shows "(\<forall> VARI \<in> (Node) : (\<forall> VARJ \<in> (Node) : (((fapply (((a_votedhash_primea :: c)), (VARI))) \<or> ((~ (((<<(VARI), (VARJ)>>) \<in> ((a_voteunde_msghash_primea :: c))))))))))"(is "PROP ?ob'155")
proof -
ML_command {* writeln "*** TLAPS ENTER 155"; *}
show "PROP ?ob'155"

(* BEGIN ZENON INPUT
;; file=consensus_epr_IndProofs.tlaps/tlapm_f62f8e.znn; PATH='/home/egolf/.opam/4.07.1/bin:/home/egolf/.local/bin:/home/egolf/bin:/home/egolf/mambaforge/bin:/home/egolf/mambaforge/condabin:/home/egolf/.opam/4.07.1/bin:/home/egolf/.local/bin:/home/egolf/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/home/egolf/.local/bin/gurobi952/linux64/bin:/home/egolf/Projects/apalache/bin:/home/egolf/opt/foxitsoftware/foxitreader:/home/egolf/.local/bin/gurobi952/linux64/bin:/home/egolf/Projects/apalache/bin:/home/egolf/opt/foxitsoftware/foxitreader:/usr/local/bin:/usr/local/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >consensus_epr_IndProofs.tlaps/tlapm_f62f8e.znn.out
;; obligation #155
$hyp "v'26" (/\ (/\ (/\ (TLA.in a_voteunde_requestunde_msga
(TLA.SUBSET (TLA.prod Node Node))) (TLA.in voted
(TLA.FuncSet Node (TLA.set T. F.))) (TLA.in a_voteunde_msga
(TLA.SUBSET (TLA.prod Node Node))) (TLA.in votes
(TLA.FuncSet Node (TLA.SUBSET Node))) (TLA.in leader
(TLA.FuncSet Node (TLA.set T. F.))) (TLA.in decided
(TLA.FuncSet Node (TLA.SUBSET Value))))
(TLA.bAll Node ((a_n1a) (TLA.bAll Node ((a_n2a) (TLA.bAll Value ((a_v1a) (TLA.bAll Value ((a_v2a) (=> (/\ (TLA.in a_v1a
(TLA.fapply decided a_n1a)) (TLA.in a_v2a (TLA.fapply decided a_n2a)))
(= a_v1a a_v2a))))))))))
(TLA.bAll Node ((VARI) (TLA.bAll Node ((VARJ) (\/ (TLA.in (TLA.tuple VARJ
VARI) a_voteunde_msga) (-. (TLA.in VARJ (TLA.fapply votes VARI))))))))
(TLA.bAll Node ((VARI) (TLA.bEx Quorum ((QJ) (TLA.bAll Value ((VALI) (\/ (TLA.subseteq QJ
(TLA.fapply votes VARI)) (-. (TLA.in VALI (TLA.fapply decided VARI))))))))))
(TLA.bAll Node ((VARI) (TLA.bAll Node ((VARJ) (\/ (TLA.fapply voted VARI)
(-. (TLA.in (TLA.tuple VARI VARJ) a_voteunde_msga)))))))
(TLA.bAll Node ((VARI) (TLA.bEx Quorum ((QJ) (\/ (TLA.subseteq QJ
(TLA.fapply votes VARI)) (-. (TLA.fapply leader VARI)))))))
(TLA.bAll Node ((VARI) (TLA.bAll Value ((VALI) (\/ (TLA.fapply leader VARI)
(-. (TLA.in VALI (TLA.fapply decided VARI))))))))
(TLA.bAll Node ((VARI) (TLA.bAll Node ((VARJ) (TLA.bAll Node ((VARK) (\/ (\/ (/\ (= VARI
VARK) (= votes votes)) (-. (TLA.in (TLA.tuple VARJ VARI) a_voteunde_msga)))
(-. (TLA.in VARJ (TLA.fapply votes VARK))))))))))
(TLA.bAll Node ((VARI) (TLA.bAll Node ((VARJ) (TLA.bAll Node ((VARK) (\/ (\/ (/\ (= VARJ
VARK) (= votes votes)) (-. (TLA.in (TLA.tuple VARI VARK) a_voteunde_msga)))
(-. (TLA.in (TLA.tuple VARI VARJ) a_voteunde_msga))))))))))
(\/ (\/ (TLA.bEx Node ((i) (TLA.bEx Node ((j) (/\ (-. (TLA.fapply voted i))
(TLA.in (TLA.tuple j i) a_voteunde_requestunde_msga)
(= a_voteunde_requestunde_msghash_primea
(TLA.setminus a_voteunde_requestunde_msga (TLA.set (TLA.tuple j i))))
(= a_voteunde_msghash_primea (TLA.cup a_voteunde_msga (TLA.set (TLA.tuple i
j)))) (= a_votedhash_primea (TLA.except voted i T.)) (= a_voteshash_primea
votes) (= a_decidedhash_primea decided) (= a_leaderhash_primea leader)
(= a_requnde_historyhash_primea a_requnde_historya))))))
(TLA.bEx Node ((i) (TLA.bEx Node ((j) (/\ (TLA.fapply voted i)
(= a_voteunde_requestunde_msghash_primea
(TLA.setminus a_voteunde_requestunde_msga (TLA.set (TLA.tuple j i))))
(= a_voteunde_msghash_primea a_voteunde_msga) (= a_votedhash_primea voted)
(= a_voteshash_primea votes) (= a_decidedhash_primea decided)
(= a_leaderhash_primea leader) (= a_requnde_historyhash_primea
a_requnde_historya))))))
(TLA.bEx Node ((i) (TLA.bEx Node ((j) (/\ (TLA.in (TLA.tuple j i)
a_voteunde_msga) (= a_voteshash_primea
(TLA.except votes i (TLA.cup (TLA.fapply votes i) (TLA.set j))))
(= a_votedhash_primea voted) (= a_voteunde_msghash_primea a_voteunde_msga)
(= a_leaderhash_primea leader) (= a_decidedhash_primea decided)
(= a_voteunde_requestunde_msghash_primea a_voteunde_requestunde_msga)
(= a_requnde_historyhash_primea a_requnde_historya))))))
(TLA.bEx Node ((i) (TLA.bEx Quorum ((Q) (/\ (TLA.subseteq Q
(TLA.fapply votes i)) (= a_leaderhash_primea (TLA.except leader i T.))
(= a_voteshash_primea votes) (= a_votedhash_primea voted)
(= a_voteunde_msghash_primea a_voteunde_msga) (= a_decidedhash_primea
decided) (= a_voteunde_requestunde_msghash_primea
a_voteunde_requestunde_msga) (= a_requnde_historyhash_primea
a_requnde_historya))))))
(TLA.bEx Node ((i) (TLA.bEx Node ((j) (TLA.bEx Value ((v) (/\ (TLA.fapply leader i)
(= TLA.emptyset (TLA.fapply decided i)) (= a_decidedhash_primea
(TLA.except decided i (TLA.cup (TLA.fapply decided i) (TLA.set v))))
(= a_voteshash_primea votes) (= a_votedhash_primea voted)
(= a_voteunde_msghash_primea a_voteunde_msga) (= a_leaderhash_primea leader)
(= a_voteunde_requestunde_msghash_primea a_voteunde_requestunde_msga)
(= a_requnde_historyhash_primea a_requnde_historya)))))))))
(TLA.bEx Node ((i) (TLA.bEx Node ((j) (/\ (-. (TLA.in (TLA.tuple i j)
a_requnde_historya)) (TLA.bAll Node ((a_dst2a) (-. (TLA.in (TLA.tuple i
a_dst2a) a_voteunde_requestunde_msga))))
(= a_voteunde_requestunde_msghash_primea (TLA.cup a_voteunde_requestunde_msga
(TLA.set (TLA.tuple i j)))) (= a_requnde_historyhash_primea
(TLA.cup a_requnde_historya (TLA.set (TLA.tuple i j))))
(/\ (= a_votedhash_primea voted) (= a_voteunde_msghash_primea
a_voteunde_msga) (= a_voteshash_primea votes) (= a_leaderhash_primea leader)
(= a_decidedhash_primea
decided)))))))))
$hyp "v'39" (TLA.bEx Node ((i) (TLA.bEx Node ((j) (/\ (TLA.fapply voted i)
(= a_voteunde_requestunde_msghash_primea
(TLA.setminus a_voteunde_requestunde_msga (TLA.set (TLA.tuple j i))))
(= a_voteunde_msghash_primea a_voteunde_msga) (= a_votedhash_primea voted)
(= a_voteshash_primea votes) (= a_decidedhash_primea decided)
(= a_leaderhash_primea leader) (= a_requnde_historyhash_primea
a_requnde_historya))))))
$goal (TLA.bAll Node ((VARI) (TLA.bAll Node ((VARJ) (\/ (TLA.fapply a_votedhash_primea VARI)
(-. (TLA.in (TLA.tuple VARI VARJ)
a_voteunde_msghash_primea)))))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Ha:"((((a_voteunde_requestunde_msga \\in SUBSET(prod(Node, Node)))&((voted \\in FuncSet(Node, {TRUE, FALSE}))&((a_voteunde_msga \\in SUBSET(prod(Node, Node)))&((votes \\in FuncSet(Node, SUBSET(Node)))&((leader \\in FuncSet(Node, {TRUE, FALSE}))&(decided \\in FuncSet(Node, SUBSET(Value))))))))&(bAll(Node, (\<lambda>a_n1a. bAll(Node, (\<lambda>a_n2a. bAll(Value, (\<lambda>a_v1a. bAll(Value, (\<lambda>a_v2a. (((a_v1a \\in (decided[a_n1a]))&(a_v2a \\in (decided[a_n2a])))=>(a_v1a=a_v2a))))))))))&(bAll(Node, (\<lambda>VARI. bAll(Node, (\<lambda>VARJ. ((<<VARJ, VARI>> \\in a_voteunde_msga)|(~(VARJ \\in (votes[VARI]))))))))&(bAll(Node, (\<lambda>VARI. bEx(Quorum, (\<lambda>QJ. bAll(Value, (\<lambda>VALI. ((QJ \\subseteq (votes[VARI]))|(~(VALI \\in (decided[VARI]))))))))))&(bAll(Node, (\<lambda>VARI. bAll(Node, (\<lambda>VARJ. ((voted[VARI])|(~(<<VARI, VARJ>> \\in a_voteunde_msga)))))))&(bAll(Node, (\<lambda>VARI. bEx(Quorum, (\<lambda>QJ. ((QJ \\subseteq (votes[VARI]))|(~(leader[VARI])))))))&(bAll(Node, (\<lambda>VARI. bAll(Value, (\<lambda>VALI. ((leader[VARI])|(~(VALI \\in (decided[VARI]))))))))&(bAll(Node, (\<lambda>VARI. bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARI=VARK)&(votes=votes))|(~(<<VARJ, VARI>> \\in a_voteunde_msga)))|(~(VARJ \\in (votes[VARK]))))))))))&bAll(Node, (\<lambda>VARI. bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(votes=votes))|(~(<<VARI, VARK>> \\in a_voteunde_msga)))|(~(<<VARI, VARJ>> \\in a_voteunde_msga)))))))))))))))))&((bEx(Node, (\<lambda>i. bEx(Node, (\<lambda>j. ((~(voted[i]))&((<<j, i>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, i>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<i, j>>}))&((a_votedhash_primea=except(voted, i, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))|(bEx(Node, (\<lambda>i. bEx(Node, (\<lambda>j. ((voted[i])&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, i>>}))&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_votedhash_primea=voted)&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))|(bEx(Node, (\<lambda>i. bEx(Node, (\<lambda>j. ((<<j, i>> \\in a_voteunde_msga)&((a_voteshash_primea=except(votes, i, ((votes[i]) \\cup {j})))&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_decidedhash_primea=decided)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))|(bEx(Node, (\<lambda>i. bEx(Quorum, (\<lambda>Q. ((Q \\subseteq (votes[i]))&((a_leaderhash_primea=except(leader, i, TRUE))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_decidedhash_primea=decided)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))|bEx(Node, (\<lambda>i. bEx(Node, (\<lambda>j. bEx(Value, (\<lambda>v. ((leader[i])&(({}=(decided[i]))&((a_decidedhash_primea=except(decided, i, ((decided[i]) \\cup {v})))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))))))))|bEx(Node, (\<lambda>i. bEx(Node, (\<lambda>j. ((~(<<i, j>> \\in a_requnde_historya))&(bAll(Node, (\<lambda>a_dst2a. (~(<<i, a_dst2a>> \\in a_voteunde_requestunde_msga))))&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\cup {<<i, j>>}))&((a_requnde_historyhash_primea=(a_requnde_historya \\cup {<<i, j>>}))&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_voteshash_primea=votes)&((a_leaderhash_primea=leader)&(a_decidedhash_primea=decided)))))))))))))))" (is "?z_hd&?z_hff")
 using v'26 by blast
 have z_Hb:"bEx(Node, (\<lambda>i. bEx(Node, (\<lambda>j. ((voted[i])&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, i>>}))&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_votedhash_primea=voted)&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))" (is "?z_hb")
 using v'39 by blast
 have zenon_L1_: "((voted[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea))))))))])=TRUE) ==> (~(a_votedhash_primea[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea))))))))])) ==> (a_votedhash_primea=voted) ==> FALSE" (is "?z_hkf ==> ?z_hkt ==> ?z_hhd ==> FALSE")
 proof -
  assume z_Hkf:"?z_hkf" (is "?z_hkg=?z_hp")
  assume z_Hkt:"?z_hkt" (is "~?z_hku")
  assume z_Hhd:"?z_hhd"
  show FALSE
  proof (rule zenon_np_eq_l [of "?z_hku" "?z_hkg" "?z_hp", OF z_Hkt z_Hkf])
   assume z_Hkv:"(?z_hku~=?z_hkg)"
   show FALSE
   proof (rule zenon_noteq [of "?z_hkg"])
    have z_Hkw: "(?z_hkg~=?z_hkg)"
    by (rule subst [where P="(\<lambda>zenon_Vnx. ((zenon_Vnx[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea))))))))])~=?z_hkg))", OF z_Hhd], fact z_Hkv)
    thus "(?z_hkg~=?z_hkg)" .
   qed
  next
   assume z_Hlb:"(~?z_hp)"
   show FALSE
   by (rule zenon_nottrue [OF z_Hlb])
  qed
 qed
 assume z_Hc:"(~bAll(Node, (\<lambda>VARI. bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[VARI])|(~(<<VARI, VARJ>> \\in a_voteunde_msghash_primea))))))))" (is "~?z_hlc")
 have z_Hd: "?z_hd" (is "?z_he&?z_hbh")
 by (rule zenon_and_0 [OF z_Ha])
 have z_He: "?z_he" (is "?z_hf&?z_hk")
 by (rule zenon_and_0 [OF z_Hd])
 have z_Hbh: "?z_hbh" (is "?z_hbi&?z_hcb")
 by (rule zenon_and_1 [OF z_Hd])
 have z_Hcb: "?z_hcb" (is "?z_hcc&?z_hco")
 by (rule zenon_and_1 [OF z_Hbh])
 have z_Hco: "?z_hco" (is "?z_hcp&?z_hdd")
 by (rule zenon_and_1 [OF z_Hcb])
 have z_Hdd: "?z_hdd" (is "?z_hde&?z_hdn")
 by (rule zenon_and_1 [OF z_Hco])
 have z_Hde: "?z_hde"
 by (rule zenon_and_0 [OF z_Hdd])
 have z_Hk: "?z_hk" (is "?z_hl&?z_hr")
 by (rule zenon_and_1 [OF z_He])
 have z_Hl: "?z_hl"
 by (rule zenon_and_0 [OF z_Hk])
 have z_Hlk_z_Hde: "(\\A x:((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((voted[x])|(~(<<x, VARJ>> \\in a_voteunde_msga))))))) == ?z_hde" (is "?z_hlk == _")
 by (unfold bAll_def)
 have z_Hlk: "?z_hlk" (is "\\A x : ?z_hls(x)")
 by (unfold z_Hlk_z_Hde, fact z_Hde)
 have z_Hlt_z_Hb: "(\\E x:((x \\in Node)&bEx(Node, (\<lambda>j. ((voted[x])&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_votedhash_primea=voted)&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))) == ?z_hb" (is "?z_hlt == _")
 by (unfold bEx_def)
 have z_Hlt: "?z_hlt" (is "\\E x : ?z_hmd(x)")
 by (unfold z_Hlt_z_Hb, fact z_Hb)
 have z_Hme: "?z_hmd((CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((voted[x])&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_votedhash_primea=voted)&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))" (is "?z_hmg&?z_hmh")
 by (rule zenon_ex_choose_0 [of "?z_hmd", OF z_Hlt])
 have z_Hmh: "?z_hmh"
 by (rule zenon_and_1 [OF z_Hme])
 have z_Hmi_z_Hmh: "(\\E x:((x \\in Node)&((voted[(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((voted[x])&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_votedhash_primea=voted)&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))])&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<x, (CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((voted[x])&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_votedhash_primea=voted)&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))>>}))&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_votedhash_primea=voted)&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))) == ?z_hmh" (is "?z_hmi == _")
 by (unfold bEx_def)
 have z_Hmi: "?z_hmi" (is "\\E x : ?z_hmr(x)")
 by (unfold z_Hmi_z_Hmh, fact z_Hmh)
 have z_Hms: "?z_hmr((CHOOSE x:((x \\in Node)&((voted[(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((voted[x])&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_votedhash_primea=voted)&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))])&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<x, (CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((voted[x])&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_votedhash_primea=voted)&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))>>}))&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_votedhash_primea=voted)&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))" (is "?z_hmu&?z_hmv")
 by (rule zenon_ex_choose_0 [of "?z_hmr", OF z_Hmi])
 have z_Hmv: "?z_hmv" (is "?z_hml&?z_hmw")
 by (rule zenon_and_1 [OF z_Hms])
 have z_Hmw: "?z_hmw" (is "?z_hmx&?z_hha")
 by (rule zenon_and_1 [OF z_Hmv])
 have z_Hha: "?z_hha" (is "?z_hhb&?z_hhc")
 by (rule zenon_and_1 [OF z_Hmw])
 have z_Hhb: "?z_hhb"
 by (rule zenon_and_0 [OF z_Hha])
 have z_Hhc: "?z_hhc" (is "?z_hhd&?z_hgi")
 by (rule zenon_and_1 [OF z_Hha])
 have z_Hhd: "?z_hhd"
 by (rule zenon_and_0 [OF z_Hhc])
 have z_Hmy_z_Hc: "(~(\\A x:((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))) == (~?z_hlc)" (is "?z_hmy == ?z_hc")
 by (unfold bAll_def)
 have z_Hmy: "?z_hmy" (is "~(\\A x : ?z_hna(x))")
 by (unfold z_Hmy_z_Hc, fact z_Hc)
 have z_Hnb: "(\\E x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea))))))))" (is "\\E x : ?z_hnc(x)")
 by (rule zenon_notallex_0 [of "?z_hna", OF z_Hmy])
 have z_Hnd: "?z_hnc((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))" (is "~(?z_hne=>?z_hnf)")
 by (rule zenon_ex_choose_0 [of "?z_hnc", OF z_Hnb])
 have z_Hne: "?z_hne"
 by (rule zenon_notimply_0 [OF z_Hnd])
 have z_Hng: "(~?z_hnf)"
 by (rule zenon_notimply_1 [OF z_Hnd])
 have z_Hnh_z_Hng: "(~(\\A x:((x \\in Node)=>((a_votedhash_primea[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea))))))))])|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))), x>> \\in a_voteunde_msghash_primea)))))) == (~?z_hnf)" (is "?z_hnh == ?z_hng")
 by (unfold bAll_def)
 have z_Hnh: "?z_hnh" (is "~(\\A x : ?z_hno(x))")
 by (unfold z_Hnh_z_Hng, fact z_Hng)
 have z_Hnp: "(\\E x:(~((x \\in Node)=>((a_votedhash_primea[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea))))))))])|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))), x>> \\in a_voteunde_msghash_primea))))))" (is "\\E x : ?z_hnr(x)")
 by (rule zenon_notallex_0 [of "?z_hno", OF z_Hnh])
 have z_Hns: "?z_hnr((CHOOSE x:(~((x \\in Node)=>((a_votedhash_primea[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea))))))))])|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))), x>> \\in a_voteunde_msghash_primea)))))))" (is "~(?z_hnu=>?z_hnv)")
 by (rule zenon_ex_choose_0 [of "?z_hnr", OF z_Hnp])
 have z_Hnu: "?z_hnu"
 by (rule zenon_notimply_0 [OF z_Hns])
 have z_Hnw: "(~?z_hnv)" (is "~(?z_hku|?z_hnx)")
 by (rule zenon_notimply_1 [OF z_Hns])
 have z_Hkt: "(~?z_hku)"
 by (rule zenon_notor_0 [OF z_Hnw])
 have z_Hny: "(~?z_hnx)" (is "~~?z_hnz")
 by (rule zenon_notor_1 [OF z_Hnw])
 have z_Hnz: "?z_hnz"
 by (rule zenon_notnot_0 [OF z_Hny])
 have z_Hoa: "(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))), (CHOOSE x:(~((x \\in Node)=>(?z_hku|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))), x>> \\in a_voteunde_msghash_primea))))))>> \\in a_voteunde_msga)" (is "?z_hoa")
 by (rule subst [where P="(\<lambda>zenon_Vxb. (<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))), (CHOOSE x:(~((x \\in Node)=>(?z_hku|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))), x>> \\in a_voteunde_msghash_primea))))))>> \\in zenon_Vxb))", OF z_Hhb z_Hnz])
 have z_Hof: "?z_hls((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))" (is "_=>?z_hog")
 by (rule zenon_all_0 [of "?z_hls" "(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea))))))))", OF z_Hlk])
 show FALSE
 proof (rule zenon_imply [OF z_Hof])
  assume z_Hoh:"(~?z_hne)"
  show FALSE
  by (rule notE [OF z_Hoh z_Hne])
 next
  assume z_Hog:"?z_hog"
  have z_Hoi_z_Hog: "(\\A x:((x \\in Node)=>((voted[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea))))))))])|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))), x>> \\in a_voteunde_msga))))) == ?z_hog" (is "?z_hoi == _")
  by (unfold bAll_def)
  have z_Hoi: "?z_hoi" (is "\\A x : ?z_hon(x)")
  by (unfold z_Hoi_z_Hog, fact z_Hog)
  have z_Hoo: "?z_hon((CHOOSE x:(~((x \\in Node)=>(?z_hku|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))), x>> \\in a_voteunde_msghash_primea)))))))" (is "_=>?z_hop")
  by (rule zenon_all_0 [of "?z_hon" "(CHOOSE x:(~((x \\in Node)=>(?z_hku|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))), x>> \\in a_voteunde_msghash_primea))))))", OF z_Hoi])
  show FALSE
  proof (rule zenon_imply [OF z_Hoo])
   assume z_Hoq:"(~?z_hnu)"
   show FALSE
   by (rule notE [OF z_Hoq z_Hnu])
  next
   assume z_Hop:"?z_hop" (is "?z_hkg|?z_hor")
   show FALSE
   proof (rule zenon_or [OF z_Hop])
    assume z_Hkg:"?z_hkg"
    have z_Hos: "(\\A zenon_Vea:((zenon_Vea \\in Node)=>((voted[zenon_Vea]) \\in {TRUE, FALSE})))" (is "\\A x : ?z_hoy(x)")
    by (rule zenon_in_funcset_2 [of "voted" "Node" "{TRUE, FALSE}", OF z_Hl])
    have z_Hoz: "?z_hoy((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))" (is "_=>?z_hpa")
    by (rule zenon_all_0 [of "?z_hoy" "(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea))))))))", OF z_Hos])
    show FALSE
    proof (rule zenon_imply [OF z_Hoz])
     assume z_Hoh:"(~?z_hne)"
     show FALSE
     by (rule notE [OF z_Hoh z_Hne])
    next
     assume z_Hpa:"?z_hpa"
     show FALSE
     proof (rule zenon_in_addElt [of "?z_hkg" "TRUE" "{FALSE}", OF z_Hpa])
      assume z_Hkf:"(?z_hkg=TRUE)" (is "_=?z_hp")
      show FALSE
      by (rule zenon_L1_ [OF z_Hkf z_Hkt z_Hhd])
     next
      assume z_Hpc:"(?z_hkg \\in {FALSE})" (is "?z_hpc")
      show FALSE
      proof (rule zenon_in_addElt [of "?z_hkg" "FALSE" "{}", OF z_Hpc])
       assume z_Hpe:"(?z_hkg=FALSE)" (is "_=?z_hq")
       have z_Hpf: "(~?z_hkg)"
       by (rule zenon_eq_x_false_0 [of "?z_hkg", OF z_Hpe])
       show FALSE
       by (rule notE [OF z_Hpf z_Hkg])
      next
       assume z_Hpg:"(?z_hkg \\in {})" (is "?z_hpg")
       show FALSE
       by (rule zenon_in_emptyset [of "?z_hkg", OF z_Hpg])
      qed
     qed
    qed
   next
    assume z_Hor:"?z_hor"
    show FALSE
    by (rule notE [OF z_Hor z_Hoa])
   qed
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 155"; *} qed
lemma ob'153:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
fixes Node
fixes Quorum
fixes Value
fixes a_voteunde_requestunde_msga a_voteunde_requestunde_msga'
fixes voted voted'
fixes a_voteunde_msga a_voteunde_msga'
fixes votes votes'
fixes leader leader'
fixes decided decided'
fixes a_requnde_historya a_requnde_historya'
(* usable definition vars suppressed *)
(* usable definition Spec suppressed *)
(* usable definition Symmetry suppressed *)
(* usable definition Safety suppressed *)
(* usable definition SplitVote suppressed *)
(* usable definition Liveness suppressed *)
assumes v'26: "(((((((a_voteunde_requestunde_msga) \<in> ((SUBSET (((Node) \<times> (Node))))))) & (((voted) \<in> ([(Node) \<rightarrow> (BOOLEAN)]))) & (((a_voteunde_msga) \<in> ((SUBSET (((Node) \<times> (Node))))))) & (((votes) \<in> ([(Node) \<rightarrow> ((SUBSET (Node)))]))) & (((leader) \<in> ([(Node) \<rightarrow> (BOOLEAN)]))) & (((decided) \<in> ([(Node) \<rightarrow> ((SUBSET (Value)))])))) & (\<forall> a_n1a \<in> (Node) : (\<forall> a_n2a \<in> (Node) : (\<forall> a_v1a \<in> (Value) : (\<forall> a_v2a \<in> (Value) : (((((((a_v1a) \<in> (fapply ((decided), (a_n1a))))) \<and> (((a_v2a) \<in> (fapply ((decided), (a_n2a))))))) \<Rightarrow> (((a_v1a) = (a_v2a))))))))) & (\<forall> VARI \<in> (Node) : (\<forall> VARJ \<in> (Node) : (((((<<(VARJ), (VARI)>>) \<in> (a_voteunde_msga))) \<or> ((~ (((VARJ) \<in> (fapply ((votes), (VARI))))))))))) & (\<forall> VARI \<in> (Node) : (\<exists> QJ \<in> (Quorum) : (\<forall> VALI \<in> (Value) : (((((QJ) \<subseteq> (fapply ((votes), (VARI))))) \<or> ((~ (((VALI) \<in> (fapply ((decided), (VARI)))))))))))) & (\<forall> VARI \<in> (Node) : (\<forall> VARJ \<in> (Node) : (((fapply ((voted), (VARI))) \<or> ((~ (((<<(VARI), (VARJ)>>) \<in> (a_voteunde_msga))))))))) & (\<forall> VARI \<in> (Node) : (\<exists> QJ \<in> (Quorum) : (((((QJ) \<subseteq> (fapply ((votes), (VARI))))) \<or> ((~ (fapply ((leader), (VARI))))))))) & (\<forall> VARI \<in> (Node) : (\<forall> VALI \<in> (Value) : (((fapply ((leader), (VARI))) \<or> ((~ (((VALI) \<in> (fapply ((decided), (VARI))))))))))) & (\<forall> VARI \<in> (Node) : (\<forall> VARJ \<in> (Node) : (\<forall> VARK \<in> (Node) : (((((((((VARI) = (VARK))) \<and> (((votes) = (votes))))) \<or> ((~ (((<<(VARJ), (VARI)>>) \<in> (a_voteunde_msga))))))) \<or> ((~ (((VARJ) \<in> (fapply ((votes), (VARK)))))))))))) & (\<forall> VARI \<in> (Node) : (\<forall> VARJ \<in> (Node) : (\<forall> VARK \<in> (Node) : (((((((((VARJ) = (VARK))) \<and> (((votes) = (votes))))) \<or> ((~ (((<<(VARI), (VARK)>>) \<in> (a_voteunde_msga))))))) \<or> ((~ (((<<(VARI), (VARJ)>>) \<in> (a_voteunde_msga))))))))))) \<and> ((((\<exists> i \<in> (Node) : (\<exists> j \<in> (Node) : (((~ (fapply ((voted), (i))))) & (((<<(j), (i)>>) \<in> (a_voteunde_requestunde_msga))) & ((((a_voteunde_requestunde_msghash_primea :: c)) = (((a_voteunde_requestunde_msga) \\ ({(<<(j), (i)>>)}))))) & ((((a_voteunde_msghash_primea :: c)) = (((a_voteunde_msga) \<union> ({(<<(i), (j)>>)}))))) & ((((a_votedhash_primea :: c)) = ([(voted) EXCEPT ![(i)] = (TRUE)]))) & ((((a_voteshash_primea :: c)) = (votes))) & ((((a_decidedhash_primea :: c)) = (decided))) & ((((a_leaderhash_primea :: c)) = (leader))) & ((((a_requnde_historyhash_primea :: c)) = (a_requnde_historya)))))) | (\<exists> i \<in> (Node) : (\<exists> j \<in> (Node) : ((fapply ((voted), (i))) & ((((a_voteunde_requestunde_msghash_primea :: c)) = (((a_voteunde_requestunde_msga) \\ ({(<<(j), (i)>>)}))))) & ((((a_voteunde_msghash_primea :: c)) = (a_voteunde_msga))) & ((((a_votedhash_primea :: c)) = (voted))) & ((((a_voteshash_primea :: c)) = (votes))) & ((((a_decidedhash_primea :: c)) = (decided))) & ((((a_leaderhash_primea :: c)) = (leader))) & ((((a_requnde_historyhash_primea :: c)) = (a_requnde_historya)))))) | (\<exists> i \<in> (Node) : (\<exists> j \<in> (Node) : ((((<<(j), (i)>>) \<in> (a_voteunde_msga))) & ((((a_voteshash_primea :: c)) = ([(votes) EXCEPT ![(i)] = (((fapply ((votes), (i))) \<union> ({(j)})))]))) & ((((a_votedhash_primea :: c)) = (voted))) & ((((a_voteunde_msghash_primea :: c)) = (a_voteunde_msga))) & ((((a_leaderhash_primea :: c)) = (leader))) & ((((a_decidedhash_primea :: c)) = (decided))) & ((((a_voteunde_requestunde_msghash_primea :: c)) = (a_voteunde_requestunde_msga))) & ((((a_requnde_historyhash_primea :: c)) = (a_requnde_historya)))))) | (\<exists> i \<in> (Node) : (\<exists> Q \<in> (Quorum) : ((((Q) \<subseteq> (fapply ((votes), (i))))) & ((((a_leaderhash_primea :: c)) = ([(leader) EXCEPT ![(i)] = (TRUE)]))) & ((((a_voteshash_primea :: c)) = (votes))) & ((((a_votedhash_primea :: c)) = (voted))) & ((((a_voteunde_msghash_primea :: c)) = (a_voteunde_msga))) & ((((a_decidedhash_primea :: c)) = (decided))) & ((((a_voteunde_requestunde_msghash_primea :: c)) = (a_voteunde_requestunde_msga))) & ((((a_requnde_historyhash_primea :: c)) = (a_requnde_historya)))))) | (\<exists> i \<in> (Node) : (\<exists> j \<in> (Node) : (\<exists> v \<in> (Value) : ((fapply ((leader), (i))) & ((({}) = (fapply ((decided), (i))))) & ((((a_decidedhash_primea :: c)) = ([(decided) EXCEPT ![(i)] = (((fapply ((decided), (i))) \<union> ({(v)})))]))) & ((((a_voteshash_primea :: c)) = (votes))) & ((((a_votedhash_primea :: c)) = (voted))) & ((((a_voteunde_msghash_primea :: c)) = (a_voteunde_msga))) & ((((a_leaderhash_primea :: c)) = (leader))) & ((((a_voteunde_requestunde_msghash_primea :: c)) = (a_voteunde_requestunde_msga))) & ((((a_requnde_historyhash_primea :: c)) = (a_requnde_historya)))))))) \<or> (\<exists> i \<in> (Node) : (\<exists> j \<in> (Node) : ((((<<(i), (j)>>) \<notin> (a_requnde_historya))) & (\<forall> a_dst2a \<in> (Node) : (((<<(i), (a_dst2a)>>) \<notin> (a_voteunde_requestunde_msga)))) & ((((a_voteunde_requestunde_msghash_primea :: c)) = (((a_voteunde_requestunde_msga) \<union> ({(<<(i), (j)>>)}))))) & ((((a_requnde_historyhash_primea :: c)) = (((a_requnde_historya) \<union> ({(<<(i), (j)>>)}))))) & (((((a_votedhash_primea :: c)) = (voted))) & ((((a_voteunde_msghash_primea :: c)) = (a_voteunde_msga))) & ((((a_voteshash_primea :: c)) = (votes))) & ((((a_leaderhash_primea :: c)) = (leader))) & ((((a_decidedhash_primea :: c)) = (decided)))))))))))"
assumes v'38: "(\<exists> i \<in> (Node) : (\<exists> j \<in> (Node) : (((~ (fapply ((voted), (i))))) & (((<<(j), (i)>>) \<in> (a_voteunde_requestunde_msga))) & ((((a_voteunde_requestunde_msghash_primea :: c)) = (((a_voteunde_requestunde_msga) \\ ({(<<(j), (i)>>)}))))) & ((((a_voteunde_msghash_primea :: c)) = (((a_voteunde_msga) \<union> ({(<<(i), (j)>>)}))))) & ((((a_votedhash_primea :: c)) = ([(voted) EXCEPT ![(i)] = (TRUE)]))) & ((((a_voteshash_primea :: c)) = (votes))) & ((((a_decidedhash_primea :: c)) = (decided))) & ((((a_leaderhash_primea :: c)) = (leader))) & ((((a_requnde_historyhash_primea :: c)) = (a_requnde_historya))))))"
shows "(\<forall> VARI \<in> (Node) : (\<forall> VARJ \<in> (Node) : (((fapply (((a_votedhash_primea :: c)), (VARI))) \<or> ((~ (((<<(VARI), (VARJ)>>) \<in> ((a_voteunde_msghash_primea :: c))))))))))"(is "PROP ?ob'153")
proof -
ML_command {* writeln "*** TLAPS ENTER 153"; *}
show "PROP ?ob'153"

(* BEGIN ZENON INPUT
;; file=consensus_epr_IndProofs.tlaps/tlapm_199c78.znn; PATH='/home/egolf/.opam/4.07.1/bin:/home/egolf/.local/bin:/home/egolf/bin:/home/egolf/mambaforge/bin:/home/egolf/mambaforge/condabin:/home/egolf/.opam/4.07.1/bin:/home/egolf/.local/bin:/home/egolf/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/home/egolf/.local/bin/gurobi952/linux64/bin:/home/egolf/Projects/apalache/bin:/home/egolf/opt/foxitsoftware/foxitreader:/home/egolf/.local/bin/gurobi952/linux64/bin:/home/egolf/Projects/apalache/bin:/home/egolf/opt/foxitsoftware/foxitreader:/usr/local/bin:/usr/local/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >consensus_epr_IndProofs.tlaps/tlapm_199c78.znn.out
;; obligation #153
$hyp "v'26" (/\ (/\ (/\ (TLA.in a_voteunde_requestunde_msga
(TLA.SUBSET (TLA.prod Node Node))) (TLA.in voted
(TLA.FuncSet Node (TLA.set T. F.))) (TLA.in a_voteunde_msga
(TLA.SUBSET (TLA.prod Node Node))) (TLA.in votes
(TLA.FuncSet Node (TLA.SUBSET Node))) (TLA.in leader
(TLA.FuncSet Node (TLA.set T. F.))) (TLA.in decided
(TLA.FuncSet Node (TLA.SUBSET Value))))
(TLA.bAll Node ((a_n1a) (TLA.bAll Node ((a_n2a) (TLA.bAll Value ((a_v1a) (TLA.bAll Value ((a_v2a) (=> (/\ (TLA.in a_v1a
(TLA.fapply decided a_n1a)) (TLA.in a_v2a (TLA.fapply decided a_n2a)))
(= a_v1a a_v2a))))))))))
(TLA.bAll Node ((VARI) (TLA.bAll Node ((VARJ) (\/ (TLA.in (TLA.tuple VARJ
VARI) a_voteunde_msga) (-. (TLA.in VARJ (TLA.fapply votes VARI))))))))
(TLA.bAll Node ((VARI) (TLA.bEx Quorum ((QJ) (TLA.bAll Value ((VALI) (\/ (TLA.subseteq QJ
(TLA.fapply votes VARI)) (-. (TLA.in VALI (TLA.fapply decided VARI))))))))))
(TLA.bAll Node ((VARI) (TLA.bAll Node ((VARJ) (\/ (TLA.fapply voted VARI)
(-. (TLA.in (TLA.tuple VARI VARJ) a_voteunde_msga)))))))
(TLA.bAll Node ((VARI) (TLA.bEx Quorum ((QJ) (\/ (TLA.subseteq QJ
(TLA.fapply votes VARI)) (-. (TLA.fapply leader VARI)))))))
(TLA.bAll Node ((VARI) (TLA.bAll Value ((VALI) (\/ (TLA.fapply leader VARI)
(-. (TLA.in VALI (TLA.fapply decided VARI))))))))
(TLA.bAll Node ((VARI) (TLA.bAll Node ((VARJ) (TLA.bAll Node ((VARK) (\/ (\/ (/\ (= VARI
VARK) (= votes votes)) (-. (TLA.in (TLA.tuple VARJ VARI) a_voteunde_msga)))
(-. (TLA.in VARJ (TLA.fapply votes VARK))))))))))
(TLA.bAll Node ((VARI) (TLA.bAll Node ((VARJ) (TLA.bAll Node ((VARK) (\/ (\/ (/\ (= VARJ
VARK) (= votes votes)) (-. (TLA.in (TLA.tuple VARI VARK) a_voteunde_msga)))
(-. (TLA.in (TLA.tuple VARI VARJ) a_voteunde_msga))))))))))
(\/ (\/ (TLA.bEx Node ((i) (TLA.bEx Node ((j) (/\ (-. (TLA.fapply voted i))
(TLA.in (TLA.tuple j i) a_voteunde_requestunde_msga)
(= a_voteunde_requestunde_msghash_primea
(TLA.setminus a_voteunde_requestunde_msga (TLA.set (TLA.tuple j i))))
(= a_voteunde_msghash_primea (TLA.cup a_voteunde_msga (TLA.set (TLA.tuple i
j)))) (= a_votedhash_primea (TLA.except voted i T.)) (= a_voteshash_primea
votes) (= a_decidedhash_primea decided) (= a_leaderhash_primea leader)
(= a_requnde_historyhash_primea a_requnde_historya))))))
(TLA.bEx Node ((i) (TLA.bEx Node ((j) (/\ (TLA.fapply voted i)
(= a_voteunde_requestunde_msghash_primea
(TLA.setminus a_voteunde_requestunde_msga (TLA.set (TLA.tuple j i))))
(= a_voteunde_msghash_primea a_voteunde_msga) (= a_votedhash_primea voted)
(= a_voteshash_primea votes) (= a_decidedhash_primea decided)
(= a_leaderhash_primea leader) (= a_requnde_historyhash_primea
a_requnde_historya))))))
(TLA.bEx Node ((i) (TLA.bEx Node ((j) (/\ (TLA.in (TLA.tuple j i)
a_voteunde_msga) (= a_voteshash_primea
(TLA.except votes i (TLA.cup (TLA.fapply votes i) (TLA.set j))))
(= a_votedhash_primea voted) (= a_voteunde_msghash_primea a_voteunde_msga)
(= a_leaderhash_primea leader) (= a_decidedhash_primea decided)
(= a_voteunde_requestunde_msghash_primea a_voteunde_requestunde_msga)
(= a_requnde_historyhash_primea a_requnde_historya))))))
(TLA.bEx Node ((i) (TLA.bEx Quorum ((Q) (/\ (TLA.subseteq Q
(TLA.fapply votes i)) (= a_leaderhash_primea (TLA.except leader i T.))
(= a_voteshash_primea votes) (= a_votedhash_primea voted)
(= a_voteunde_msghash_primea a_voteunde_msga) (= a_decidedhash_primea
decided) (= a_voteunde_requestunde_msghash_primea
a_voteunde_requestunde_msga) (= a_requnde_historyhash_primea
a_requnde_historya))))))
(TLA.bEx Node ((i) (TLA.bEx Node ((j) (TLA.bEx Value ((v) (/\ (TLA.fapply leader i)
(= TLA.emptyset (TLA.fapply decided i)) (= a_decidedhash_primea
(TLA.except decided i (TLA.cup (TLA.fapply decided i) (TLA.set v))))
(= a_voteshash_primea votes) (= a_votedhash_primea voted)
(= a_voteunde_msghash_primea a_voteunde_msga) (= a_leaderhash_primea leader)
(= a_voteunde_requestunde_msghash_primea a_voteunde_requestunde_msga)
(= a_requnde_historyhash_primea a_requnde_historya)))))))))
(TLA.bEx Node ((i) (TLA.bEx Node ((j) (/\ (-. (TLA.in (TLA.tuple i j)
a_requnde_historya)) (TLA.bAll Node ((a_dst2a) (-. (TLA.in (TLA.tuple i
a_dst2a) a_voteunde_requestunde_msga))))
(= a_voteunde_requestunde_msghash_primea (TLA.cup a_voteunde_requestunde_msga
(TLA.set (TLA.tuple i j)))) (= a_requnde_historyhash_primea
(TLA.cup a_requnde_historya (TLA.set (TLA.tuple i j))))
(/\ (= a_votedhash_primea voted) (= a_voteunde_msghash_primea
a_voteunde_msga) (= a_voteshash_primea votes) (= a_leaderhash_primea leader)
(= a_decidedhash_primea
decided)))))))))
$hyp "v'38" (TLA.bEx Node ((i) (TLA.bEx Node ((j) (/\ (-. (TLA.fapply voted i))
(TLA.in (TLA.tuple j i) a_voteunde_requestunde_msga)
(= a_voteunde_requestunde_msghash_primea
(TLA.setminus a_voteunde_requestunde_msga (TLA.set (TLA.tuple j i))))
(= a_voteunde_msghash_primea (TLA.cup a_voteunde_msga (TLA.set (TLA.tuple i
j)))) (= a_votedhash_primea (TLA.except voted i T.)) (= a_voteshash_primea
votes) (= a_decidedhash_primea decided) (= a_leaderhash_primea leader)
(= a_requnde_historyhash_primea
a_requnde_historya))))))
$goal (TLA.bAll Node ((VARI) (TLA.bAll Node ((VARJ) (\/ (TLA.fapply a_votedhash_primea VARI)
(-. (TLA.in (TLA.tuple VARI VARJ)
a_voteunde_msghash_primea)))))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Ha:"((((a_voteunde_requestunde_msga \\in SUBSET(prod(Node, Node)))&((voted \\in FuncSet(Node, {TRUE, FALSE}))&((a_voteunde_msga \\in SUBSET(prod(Node, Node)))&((votes \\in FuncSet(Node, SUBSET(Node)))&((leader \\in FuncSet(Node, {TRUE, FALSE}))&(decided \\in FuncSet(Node, SUBSET(Value))))))))&(bAll(Node, (\<lambda>a_n1a. bAll(Node, (\<lambda>a_n2a. bAll(Value, (\<lambda>a_v1a. bAll(Value, (\<lambda>a_v2a. (((a_v1a \\in (decided[a_n1a]))&(a_v2a \\in (decided[a_n2a])))=>(a_v1a=a_v2a))))))))))&(bAll(Node, (\<lambda>VARI. bAll(Node, (\<lambda>VARJ. ((<<VARJ, VARI>> \\in a_voteunde_msga)|(~(VARJ \\in (votes[VARI]))))))))&(bAll(Node, (\<lambda>VARI. bEx(Quorum, (\<lambda>QJ. bAll(Value, (\<lambda>VALI. ((QJ \\subseteq (votes[VARI]))|(~(VALI \\in (decided[VARI]))))))))))&(bAll(Node, (\<lambda>VARI. bAll(Node, (\<lambda>VARJ. ((voted[VARI])|(~(<<VARI, VARJ>> \\in a_voteunde_msga)))))))&(bAll(Node, (\<lambda>VARI. bEx(Quorum, (\<lambda>QJ. ((QJ \\subseteq (votes[VARI]))|(~(leader[VARI])))))))&(bAll(Node, (\<lambda>VARI. bAll(Value, (\<lambda>VALI. ((leader[VARI])|(~(VALI \\in (decided[VARI]))))))))&(bAll(Node, (\<lambda>VARI. bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARI=VARK)&(votes=votes))|(~(<<VARJ, VARI>> \\in a_voteunde_msga)))|(~(VARJ \\in (votes[VARK]))))))))))&bAll(Node, (\<lambda>VARI. bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(votes=votes))|(~(<<VARI, VARK>> \\in a_voteunde_msga)))|(~(<<VARI, VARJ>> \\in a_voteunde_msga)))))))))))))))))&((bEx(Node, (\<lambda>i. bEx(Node, (\<lambda>j. ((~(voted[i]))&((<<j, i>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, i>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<i, j>>}))&((a_votedhash_primea=except(voted, i, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))|(bEx(Node, (\<lambda>i. bEx(Node, (\<lambda>j. ((voted[i])&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, i>>}))&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_votedhash_primea=voted)&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))|(bEx(Node, (\<lambda>i. bEx(Node, (\<lambda>j. ((<<j, i>> \\in a_voteunde_msga)&((a_voteshash_primea=except(votes, i, ((votes[i]) \\cup {j})))&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_decidedhash_primea=decided)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))|(bEx(Node, (\<lambda>i. bEx(Quorum, (\<lambda>Q. ((Q \\subseteq (votes[i]))&((a_leaderhash_primea=except(leader, i, TRUE))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_decidedhash_primea=decided)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))|bEx(Node, (\<lambda>i. bEx(Node, (\<lambda>j. bEx(Value, (\<lambda>v. ((leader[i])&(({}=(decided[i]))&((a_decidedhash_primea=except(decided, i, ((decided[i]) \\cup {v})))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))))))))|bEx(Node, (\<lambda>i. bEx(Node, (\<lambda>j. ((~(<<i, j>> \\in a_requnde_historya))&(bAll(Node, (\<lambda>a_dst2a. (~(<<i, a_dst2a>> \\in a_voteunde_requestunde_msga))))&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\cup {<<i, j>>}))&((a_requnde_historyhash_primea=(a_requnde_historya \\cup {<<i, j>>}))&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_voteshash_primea=votes)&((a_leaderhash_primea=leader)&(a_decidedhash_primea=decided)))))))))))))))" (is "?z_hd&?z_hff")
 using v'26 by blast
 have z_Hb:"bEx(Node, (\<lambda>i. bEx(Node, (\<lambda>j. ((~(voted[i]))&((<<j, i>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, i>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<i, j>>}))&((a_votedhash_primea=except(voted, i, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))" (is "?z_hb")
 using v'38 by blast
 have zenon_L1_: "(~(a_votedhash_primea[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea))))))))])) ==> (DOMAIN(voted)=Node) ==> (<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))), (CHOOSE x:(~((x \\in Node)=>((a_votedhash_primea[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea))))))))])|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))), x>> \\in a_voteunde_msghash_primea))))))>> \\in a_voteunde_msga) ==> bAll(a_voteunde_msga, (\<lambda>x. (x \\in prod(Node, Node)))) ==> (a_votedhash_primea=except(voted, (CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))), TRUE)) ==> (~(voted[(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))])) ==> ((voted[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea))))))))])=TRUE) ==> FALSE" (is "?z_hkf ==> ?z_hkt ==> ?z_hkv ==> ?z_hle ==> ?z_hlh ==> ?z_hmf ==> ?z_hmh ==> FALSE")
 proof -
  assume z_Hkf:"?z_hkf" (is "~?z_hkg")
  assume z_Hkt:"?z_hkt" (is "?z_hku=_")
  assume z_Hkv:"?z_hkv"
  assume z_Hle:"?z_hle"
  assume z_Hlh:"?z_hlh" (is "_=?z_hli")
  assume z_Hmf:"?z_hmf" (is "~?z_hmg")
  assume z_Hmh:"?z_hmh" (is "?z_hmi=?z_hp")
  show FALSE
  proof (rule zenon_np_eq_l [of "?z_hkg" "?z_hmi" "?z_hp", OF z_Hkf z_Hmh])
   assume z_Hmj:"(?z_hkg~=?z_hmi)"
   show FALSE
   proof (rule zenon_np_eq_l [of "?z_hmg" "?z_hmi" "?z_hp", OF z_Hmf z_Hmh])
    assume z_Hmk:"(?z_hmg~=?z_hmi)"
    show FALSE
    proof (rule zenon_noteq [of "?z_hmi"])
     have z_Hml: "((CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, ?z_hp))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))=(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))" (is "?z_hlj=?z_hkh")
     proof (rule zenon_nnpp [of "(?z_hlj=?z_hkh)"])
      assume z_Hmm:"(?z_hlj~=?z_hkh)"
      have z_Hmn: "(((isAFcn(a_votedhash_primea)<=>isAFcn(?z_hli))&(DOMAIN(a_votedhash_primea)=DOMAIN(?z_hli)))&(\\A zenon_Vhb:((a_votedhash_primea[zenon_Vhb])=(?z_hli[zenon_Vhb]))))" (is "?z_hmo&?z_hmv")
      by (rule zenon_funequal_0 [of "a_votedhash_primea" "?z_hli", OF z_Hlh])
      have z_Hmv: "?z_hmv" (is "\\A x : ?z_hna(x)")
      by (rule zenon_and_1 [OF z_Hmn])
      have z_Hnb: "(<<?z_hkh, (CHOOSE x:(~((x \\in Node)=>(?z_hkg|(~(<<?z_hkh, x>> \\in a_voteunde_msghash_primea))))))>> \\in prod(Node, Node))" (is "?z_hnb")
      by (rule zenon_all_in_0 [of "a_voteunde_msga" "(\<lambda>x. (x \\in prod(Node, Node)))", OF z_Hle z_Hkv])
      have z_Hnc_z_Hnb: "(<<?z_hkh, (CHOOSE x:(~((x \\in Node)=>(?z_hkg|(~(<<?z_hkh, x>> \\in a_voteunde_msghash_primea))))))>> \\in Product(<<Node, Node>>)) == ?z_hnb" (is "?z_hnc == _")
      by (unfold prod_def)
      have z_Hnc: "?z_hnc"
      by (unfold z_Hnc_z_Hnb, fact z_Hnb)
      let ?z_hkw = "<<?z_hkh, (CHOOSE x:(~((x \\in Node)=>(?z_hkg|(~(<<?z_hkh, x>> \\in a_voteunde_msghash_primea))))))>>"
      let ?z_hne = "<<Node, Node>>"
      have z_Hnf: "isASeq(?z_hne)" by auto
      have z_Hng: "(1 \\in (1..Len(?z_hne)))" by auto
      have z_Hnk: "((?z_hkw[1]) \\in (?z_hne[1]))" (is "?z_hnk")
      by (rule zenon_in_product_i [OF z_Hnc z_Hnf z_Hng])
      have z_Hnn: "((?z_hkw[1]) \\in Node)" (is "?z_hnn")
      using z_Hnk by auto
      have z_Hno: "((?z_hkw[1]) \\in ?z_hku)" (is "?z_hno")
      by (rule ssubst [where P="(\<lambda>zenon_Vupb. ((?z_hkw[1]) \\in zenon_Vupb))", OF z_Hkt z_Hnn])
      have z_Hns: "((?z_hkw[1])=?z_hkh)" (is "?z_hnl=_")
      by auto
      have z_Hnt: "(?z_hkh \\in ?z_hku)" (is "?z_hnt")
      by (rule subst [where P="(\<lambda>zenon_Vzo. (zenon_Vzo \\in ?z_hku))", OF z_Hns z_Hno])
      have z_Hnx: "?z_hna(?z_hkh)" (is "_=?z_hny")
      by (rule zenon_all_0 [of "?z_hna" "?z_hkh", OF z_Hmv])
      show FALSE
      proof (rule zenon_fapplyexcept [of "(\<lambda>zenon_Vsvb. (?z_hkg=zenon_Vsvb))" "voted" "?z_hlj" "?z_hp" "?z_hkh", OF z_Hnx])
       assume z_Hnt:"?z_hnt"
       assume z_Hml:"(?z_hlj=?z_hkh)"
       assume z_Hoc:"(?z_hkg=?z_hp)"
       show FALSE
       by (rule notE [OF z_Hmm z_Hml])
      next
       assume z_Hnt:"?z_hnt"
       assume z_Hmm:"(?z_hlj~=?z_hkh)"
       assume z_Hod:"(?z_hkg=?z_hmi)"
       show FALSE
       by (rule notE [OF z_Hmj z_Hod])
      next
       assume z_Hoe:"(~?z_hnt)"
       show FALSE
       by (rule notE [OF z_Hoe z_Hnt])
      qed
     qed
     have z_Hof: "(?z_hmi~=?z_hmi)"
     by (rule subst [where P="(\<lambda>zenon_Vudc. ((voted[zenon_Vudc])~=?z_hmi))", OF z_Hml], fact z_Hmk)
     thus "(?z_hmi~=?z_hmi)" .
    qed
   next
    assume z_Hok:"(~?z_hp)"
    show FALSE
    by (rule zenon_nottrue [OF z_Hok])
   qed
  next
   assume z_Hok:"(~?z_hp)"
   show FALSE
   by (rule zenon_nottrue [OF z_Hok])
  qed
 qed
 have zenon_L2_: "(~(except(voted, (CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))), TRUE)[(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))])) ==> ((CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))) \\in DOMAIN(voted)) ==> FALSE" (is "?z_hol ==> ?z_hon ==> FALSE")
 proof -
  assume z_Hol:"?z_hol" (is "~?z_hom")
  assume z_Hon:"?z_hon"
  show FALSE
  proof (rule zenon_fapplyexcept [of "(\<lambda>zenon_Vf. (~zenon_Vf))" "voted" "(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))" "TRUE" "(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))", OF z_Hol])
   assume z_Hon:"?z_hon"
   assume z_Hor:"((CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))=(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))))" (is "?z_hlj=_")
   assume z_Hok:"(~TRUE)" (is "~?z_hp")
   show FALSE
   by (rule zenon_nottrue [OF z_Hok])
  next
   assume z_Hon:"?z_hon"
   assume z_Hos:"((CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))~=(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))))" (is "?z_hlj~=_")
   assume z_Hmf:"(~(voted[?z_hlj]))" (is "~?z_hmg")
   show FALSE
   by (rule zenon_noteq [OF z_Hos])
  next
   assume z_Hot:"(~?z_hon)"
   show FALSE
   by (rule notE [OF z_Hot z_Hon])
  qed
 qed
 assume z_Hc:"(~bAll(Node, (\<lambda>VARI. bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[VARI])|(~(<<VARI, VARJ>> \\in a_voteunde_msghash_primea))))))))" (is "~?z_hou")
 have z_Hd: "?z_hd" (is "?z_he&?z_hbh")
 by (rule zenon_and_0 [OF z_Ha])
 have z_He: "?z_he" (is "?z_hf&?z_hk")
 by (rule zenon_and_0 [OF z_Hd])
 have z_Hbh: "?z_hbh" (is "?z_hbi&?z_hcb")
 by (rule zenon_and_1 [OF z_Hd])
 have z_Hcb: "?z_hcb" (is "?z_hcc&?z_hco")
 by (rule zenon_and_1 [OF z_Hbh])
 have z_Hco: "?z_hco" (is "?z_hcp&?z_hdd")
 by (rule zenon_and_1 [OF z_Hcb])
 have z_Hdd: "?z_hdd" (is "?z_hde&?z_hdn")
 by (rule zenon_and_1 [OF z_Hco])
 have z_Hde: "?z_hde"
 by (rule zenon_and_0 [OF z_Hdd])
 have z_Hf: "?z_hf"
 by (rule zenon_and_0 [OF z_He])
 have z_Hk: "?z_hk" (is "?z_hl&?z_hr")
 by (rule zenon_and_1 [OF z_He])
 have z_Hl: "?z_hl"
 by (rule zenon_and_0 [OF z_Hk])
 have z_Hr: "?z_hr" (is "?z_hs&?z_hu")
 by (rule zenon_and_1 [OF z_Hk])
 have z_Hs: "?z_hs"
 by (rule zenon_and_0 [OF z_Hr])
 have z_Hpc: "(a_voteunde_requestunde_msga \\subseteq prod(Node, Node))" (is "?z_hpc")
 by (rule zenon_in_SUBSET_0 [of "a_voteunde_requestunde_msga" "prod(Node, Node)", OF z_Hf])
 have z_Hpd_z_Hpc: "bAll(a_voteunde_requestunde_msga, (\<lambda>x. (x \\in prod(Node, Node)))) == ?z_hpc" (is "?z_hpd == _")
 by (unfold subset_def)
 have z_Hpd: "?z_hpd"
 by (unfold z_Hpd_z_Hpc, fact z_Hpc)
 have z_Hpe: "(a_voteunde_msga \\subseteq prod(Node, Node))" (is "?z_hpe")
 by (rule zenon_in_SUBSET_0 [of "a_voteunde_msga" "prod(Node, Node)", OF z_Hs])
 have z_Hle_z_Hpe: "bAll(a_voteunde_msga, (\<lambda>x. (x \\in prod(Node, Node)))) == ?z_hpe" (is "?z_hle == _")
 by (unfold subset_def)
 have z_Hle: "?z_hle"
 by (unfold z_Hle_z_Hpe, fact z_Hpe)
 have z_Hpf_z_Hde: "(\\A x:((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((voted[x])|(~(<<x, VARJ>> \\in a_voteunde_msga))))))) == ?z_hde" (is "?z_hpf == _")
 by (unfold bAll_def)
 have z_Hpf: "?z_hpf" (is "\\A x : ?z_hpm(x)")
 by (unfold z_Hpf_z_Hde, fact z_Hde)
 have z_Hpn_z_Hb: "(\\E x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))) == ?z_hb" (is "?z_hpn == _")
 by (unfold bEx_def)
 have z_Hpn: "?z_hpn" (is "\\E x : ?z_hpo(x)")
 by (unfold z_Hpn_z_Hb, fact z_Hb)
 have z_Hpp: "?z_hpo((CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))))" (is "?z_hpq&?z_hpr")
 by (rule zenon_ex_choose_0 [of "?z_hpo", OF z_Hpn])
 have z_Hpr: "?z_hpr"
 by (rule zenon_and_1 [OF z_Hpp])
 have z_Hps_z_Hpr: "(\\E x:((x \\in Node)&((~(voted[(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))]))&((<<x, (CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<x, (CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))), x>>}))&((a_votedhash_primea=except(voted, (CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))), TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))) == ?z_hpr" (is "?z_hps == _")
 by (unfold bEx_def)
 have z_Hps: "?z_hps" (is "\\E x : ?z_hqi(x)")
 by (unfold z_Hps_z_Hpr, fact z_Hpr)
 have z_Hqj: "?z_hqi((CHOOSE x:((x \\in Node)&((~(voted[(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))]))&((<<x, (CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<x, (CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))), x>>}))&((a_votedhash_primea=except(voted, (CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))), TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))" (is "?z_hql&?z_hqm")
 by (rule zenon_ex_choose_0 [of "?z_hqi", OF z_Hps])
 have z_Hqm: "?z_hqm" (is "?z_hmf&?z_hqn")
 by (rule zenon_and_1 [OF z_Hqj])
 have z_Hmf: "?z_hmf" (is "~?z_hmg")
 by (rule zenon_and_0 [OF z_Hqm])
 have z_Hqn: "?z_hqn" (is "?z_hqo&?z_hqp")
 by (rule zenon_and_1 [OF z_Hqm])
 have z_Hqo: "?z_hqo"
 by (rule zenon_and_0 [OF z_Hqn])
 have z_Hqp: "?z_hqp" (is "?z_hqq&?z_hqr")
 by (rule zenon_and_1 [OF z_Hqn])
 have z_Hqr: "?z_hqr" (is "?z_hqs&?z_hqh")
 by (rule zenon_and_1 [OF z_Hqp])
 have z_Hqs: "?z_hqs" (is "_=?z_hqt")
 by (rule zenon_and_0 [OF z_Hqr])
 have z_Hqh: "?z_hqh" (is "?z_hlh&?z_hgh")
 by (rule zenon_and_1 [OF z_Hqr])
 have z_Hlh: "?z_hlh" (is "_=?z_hli")
 by (rule zenon_and_0 [OF z_Hqh])
 have z_Hqu_z_Hc: "(~(\\A x:((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))) == (~?z_hou)" (is "?z_hqu == ?z_hc")
 by (unfold bAll_def)
 have z_Hqu: "?z_hqu" (is "~(\\A x : ?z_hqw(x))")
 by (unfold z_Hqu_z_Hc, fact z_Hc)
 have z_Hqx: "(\\E x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea))))))))" (is "\\E x : ?z_hqy(x)")
 by (rule zenon_notallex_0 [of "?z_hqw", OF z_Hqu])
 have z_Hqz: "?z_hqy((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))" (is "~(?z_hra=>?z_hrb)")
 by (rule zenon_ex_choose_0 [of "?z_hqy", OF z_Hqx])
 have z_Hra: "?z_hra"
 by (rule zenon_notimply_0 [OF z_Hqz])
 have z_Hrc: "(~?z_hrb)"
 by (rule zenon_notimply_1 [OF z_Hqz])
 have z_Hrd_z_Hrc: "(~(\\A x:((x \\in Node)=>((a_votedhash_primea[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea))))))))])|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))), x>> \\in a_voteunde_msghash_primea)))))) == (~?z_hrb)" (is "?z_hrd == ?z_hrc")
 by (unfold bAll_def)
 have z_Hrd: "?z_hrd" (is "~(\\A x : ?z_hrf(x))")
 by (unfold z_Hrd_z_Hrc, fact z_Hrc)
 have z_Hrg: "(\\E x:(~((x \\in Node)=>((a_votedhash_primea[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea))))))))])|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))), x>> \\in a_voteunde_msghash_primea))))))" (is "\\E x : ?z_hrh(x)")
 by (rule zenon_notallex_0 [of "?z_hrf", OF z_Hrd])
 have z_Hri: "?z_hrh((CHOOSE x:(~((x \\in Node)=>((a_votedhash_primea[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea))))))))])|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))), x>> \\in a_voteunde_msghash_primea)))))))" (is "~(?z_hrj=>?z_hrk)")
 by (rule zenon_ex_choose_0 [of "?z_hrh", OF z_Hrg])
 have z_Hrj: "?z_hrj"
 by (rule zenon_notimply_0 [OF z_Hri])
 have z_Hrl: "(~?z_hrk)" (is "~(?z_hkg|?z_hrm)")
 by (rule zenon_notimply_1 [OF z_Hri])
 have z_Hkf: "(~?z_hkg)"
 by (rule zenon_notor_0 [OF z_Hrl])
 have z_Hrn: "(~?z_hrm)" (is "~~?z_hro")
 by (rule zenon_notor_1 [OF z_Hrl])
 have z_Hro: "?z_hro"
 by (rule zenon_notnot_0 [OF z_Hrn])
 have z_Hrp: "(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))), (CHOOSE x:(~((x \\in Node)=>(?z_hkg|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))), x>> \\in a_voteunde_msghash_primea))))))>> \\in ?z_hqt)" (is "?z_hrp")
 by (rule subst [where P="(\<lambda>zenon_Vbc. (<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))), (CHOOSE x:(~((x \\in Node)=>(?z_hkg|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))), x>> \\in a_voteunde_msghash_primea))))))>> \\in zenon_Vbc))", OF z_Hqs z_Hro])
 show FALSE
 proof (rule zenon_in_cup [of "<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))), (CHOOSE x:(~((x \\in Node)=>(?z_hkg|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))), x>> \\in a_voteunde_msghash_primea))))))>>" "a_voteunde_msga" "{<<(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&?z_hgh))))))))), (CHOOSE x:((x \\in Node)&(?z_hmf&((<<x, (CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&?z_hgh)))))))))>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<x, (CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&?z_hgh)))))))))>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&?z_hgh))))))))), x>>}))&?z_hqh))))))>>}", OF z_Hrp])
  assume z_Hkv:"(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))), (CHOOSE x:(~((x \\in Node)=>(?z_hkg|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))), x>> \\in a_voteunde_msghash_primea))))))>> \\in a_voteunde_msga)" (is "?z_hkv")
  have z_Hkt: "(DOMAIN(voted)=Node)" (is "?z_hku=_")
  by (rule zenon_in_funcset_1 [of "voted" "Node" "{TRUE, FALSE}", OF z_Hl])
  have z_Hrv: "?z_hpm((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))" (is "_=>?z_hrw")
  by (rule zenon_all_0 [of "?z_hpm" "(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea))))))))", OF z_Hpf])
  show FALSE
  proof (rule zenon_imply [OF z_Hrv])
   assume z_Hrx:"(~?z_hra)"
   show FALSE
   by (rule notE [OF z_Hrx z_Hra])
  next
   assume z_Hrw:"?z_hrw"
   have z_Hry_z_Hrw: "(\\A x:((x \\in Node)=>((voted[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea))))))))])|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))), x>> \\in a_voteunde_msga))))) == ?z_hrw" (is "?z_hry == _")
   by (unfold bAll_def)
   have z_Hry: "?z_hry" (is "\\A x : ?z_hsd(x)")
   by (unfold z_Hry_z_Hrw, fact z_Hrw)
   have z_Hse: "?z_hsd((CHOOSE x:(~((x \\in Node)=>(?z_hkg|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))), x>> \\in a_voteunde_msghash_primea)))))))" (is "_=>?z_hsf")
   by (rule zenon_all_0 [of "?z_hsd" "(CHOOSE x:(~((x \\in Node)=>(?z_hkg|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))), x>> \\in a_voteunde_msghash_primea))))))", OF z_Hry])
   show FALSE
   proof (rule zenon_imply [OF z_Hse])
    assume z_Hsg:"(~?z_hrj)"
    show FALSE
    by (rule notE [OF z_Hsg z_Hrj])
   next
    assume z_Hsf:"?z_hsf" (is "?z_hmi|?z_hsh")
    show FALSE
    proof (rule zenon_or [OF z_Hsf])
     assume z_Hmi:"?z_hmi"
     have z_Hkt: "(?z_hku=Node)"
     by (rule zenon_in_funcset_1 [of "voted" "Node" "{TRUE, FALSE}", OF z_Hl])
     have z_Hsi: "(\\A zenon_Vea:((zenon_Vea \\in Node)=>((voted[zenon_Vea]) \\in {TRUE, FALSE})))" (is "\\A x : ?z_hso(x)")
     by (rule zenon_in_funcset_2 [of "voted" "Node" "{TRUE, FALSE}", OF z_Hl])
     have z_Hsp: "?z_hso((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))" (is "_=>?z_hsq")
     by (rule zenon_all_0 [of "?z_hso" "(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea))))))))", OF z_Hsi])
     show FALSE
     proof (rule zenon_imply [OF z_Hsp])
      assume z_Hrx:"(~?z_hra)"
      show FALSE
      by (rule notE [OF z_Hrx z_Hra])
     next
      assume z_Hsq:"?z_hsq"
      show FALSE
      proof (rule zenon_in_addElt [of "?z_hmi" "TRUE" "{FALSE}", OF z_Hsq])
       assume z_Hmh:"(?z_hmi=TRUE)" (is "_=?z_hp")
       show FALSE
       by (rule zenon_L1_ [OF z_Hkf z_Hkt z_Hkv z_Hle z_Hlh z_Hmf z_Hmh])
      next
       assume z_Hss:"(?z_hmi \\in {FALSE})" (is "?z_hss")
       show FALSE
       proof (rule zenon_in_addElt [of "?z_hmi" "FALSE" "{}", OF z_Hss])
        assume z_Hsu:"(?z_hmi=FALSE)" (is "_=?z_hq")
        have z_Hsv: "(~?z_hmi)"
        by (rule zenon_eq_x_false_0 [of "?z_hmi", OF z_Hsu])
        show FALSE
        by (rule notE [OF z_Hsv z_Hmi])
       next
        assume z_Hsw:"(?z_hmi \\in {})" (is "?z_hsw")
        show FALSE
        by (rule zenon_in_emptyset [of "?z_hmi", OF z_Hsw])
       qed
      qed
     qed
    next
     assume z_Hsh:"?z_hsh"
     show FALSE
     by (rule notE [OF z_Hsh z_Hkv])
    qed
   qed
  qed
 next
  assume z_Hsx:"(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))), (CHOOSE x:(~((x \\in Node)=>(?z_hkg|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))), x>> \\in a_voteunde_msghash_primea))))))>> \\in {<<(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&?z_hgh))))))))), (CHOOSE x:((x \\in Node)&(?z_hmf&((<<x, (CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&?z_hgh)))))))))>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<x, (CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&?z_hgh)))))))))>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&?z_hgh))))))))), x>>}))&?z_hqh))))))>>})" (is "?z_hsx")
  show FALSE
  proof (rule zenon_in_addElt [of "<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))), (CHOOSE x:(~((x \\in Node)=>(?z_hkg|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))), x>> \\in a_voteunde_msghash_primea))))))>>" "<<(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&?z_hgh))))))))), (CHOOSE x:((x \\in Node)&(?z_hmf&((<<x, (CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&?z_hgh)))))))))>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<x, (CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&?z_hgh)))))))))>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&?z_hgh))))))))), x>>}))&?z_hqh))))))>>" "{}", OF z_Hsx])
   assume z_Hsy:"(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))), (CHOOSE x:(~((x \\in Node)=>(?z_hkg|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))), x>> \\in a_voteunde_msghash_primea))))))>>=<<(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&?z_hgh))))))))), (CHOOSE x:((x \\in Node)&(?z_hmf&((<<x, (CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&?z_hgh)))))))))>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<x, (CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&?z_hgh)))))))))>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&?z_hgh))))))))), x>>}))&?z_hqh))))))>>)" (is "?z_hkw=?z_hru")
   have z_Hsz: "((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea))))))))=(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&?z_hgh))))))))))" (is "?z_hkh=?z_hlj")
   using z_Hsy by auto
   have z_Hkt: "(DOMAIN(voted)=Node)" (is "?z_hku=_")
   by (rule zenon_in_funcset_1 [of "voted" "Node" "{TRUE, FALSE}", OF z_Hl])
   have z_Hmn: "(((isAFcn(a_votedhash_primea)<=>isAFcn(?z_hli))&(DOMAIN(a_votedhash_primea)=DOMAIN(?z_hli)))&(\\A zenon_Vhb:((a_votedhash_primea[zenon_Vhb])=(?z_hli[zenon_Vhb]))))" (is "?z_hmo&?z_hmv")
   by (rule zenon_funequal_0 [of "a_votedhash_primea" "?z_hli", OF z_Hlh])
   have z_Hmv: "?z_hmv" (is "\\A x : ?z_hna(x)")
   by (rule zenon_and_1 [OF z_Hmn])
   have z_Hta: "(<<(CHOOSE x:((x \\in Node)&(?z_hmf&((<<x, ?z_hlj>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<x, ?z_hlj>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<?z_hlj, x>>}))&?z_hqh)))))), ?z_hlj>> \\in prod(Node, Node))" (is "?z_hta")
   by (rule zenon_all_in_0 [of "a_voteunde_requestunde_msga" "(\<lambda>x. (x \\in prod(Node, Node)))", OF z_Hpd z_Hqo])
   have z_Htc_z_Hta: "(<<(CHOOSE x:((x \\in Node)&(?z_hmf&((<<x, ?z_hlj>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<x, ?z_hlj>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<?z_hlj, x>>}))&?z_hqh)))))), ?z_hlj>> \\in Product(<<Node, Node>>)) == ?z_hta" (is "?z_htc == _")
   by (unfold prod_def)
   have z_Htc: "?z_htc"
   by (unfold z_Htc_z_Hta, fact z_Hta)
   let ?z_htb = "<<(CHOOSE x:((x \\in Node)&(?z_hmf&((<<x, ?z_hlj>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<x, ?z_hlj>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<?z_hlj, x>>}))&?z_hqh)))))), ?z_hlj>>"
   let ?z_hne = "<<Node, Node>>"
   have z_Hnf: "isASeq(?z_hne)" by auto
   have z_Htd: "(2 \\in (1..Len(?z_hne)))" by auto
   have z_Htf: "((?z_htb[2]) \\in (?z_hne[2]))" (is "?z_htf")
   by (rule zenon_in_product_i [OF z_Htc z_Hnf z_Htd])
   have z_Hti: "((?z_htb[2]) \\in Node)" (is "?z_hti")
   using z_Htf by auto
   have z_Htj: "((?z_htb[2]) \\in ?z_hku)" (is "?z_htj")
   by (rule ssubst [where P="(\<lambda>zenon_Vqq. ((?z_htb[2]) \\in zenon_Vqq))", OF z_Hkt z_Hti])
   have z_Htn: "((?z_htb[2])=?z_hlj)" (is "?z_htg=_")
   by auto
   have z_Hon: "(?z_hlj \\in ?z_hku)" (is "?z_hon")
   by (rule subst [where P="(\<lambda>zenon_Vzo. (zenon_Vzo \\in ?z_hku))", OF z_Htn z_Htj])
   have z_Hto: "?z_hna(?z_hlj)" (is "?z_htp=?z_hom")
   by (rule zenon_all_0 [of "?z_hna" "?z_hlj", OF z_Hmv])
   show FALSE
   proof (rule zenon_np_eq_l [of "?z_hkg" "?z_htp" "?z_hom", OF z_Hkf z_Hto])
    assume z_Htq:"(?z_hkg~=?z_htp)"
    show FALSE
    proof (rule zenon_noteq [of "?z_htp"])
     have z_Htr: "(?z_htp~=?z_htp)"
     by (rule subst [where P="(\<lambda>zenon_Vvdc. ((a_votedhash_primea[zenon_Vvdc])~=?z_htp))", OF z_Hsz], fact z_Htq)
     thus "(?z_htp~=?z_htp)" .
    qed
   next
    assume z_Hol:"(~?z_hom)"
    show FALSE
    by (rule zenon_L2_ [OF z_Hol z_Hon])
   qed
  next
   assume z_Htw:"(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))), (CHOOSE x:(~((x \\in Node)=>(?z_hkg|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))), x>> \\in a_voteunde_msghash_primea))))))>> \\in {})" (is "?z_htw")
   show FALSE
   by (rule zenon_in_emptyset [of "<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))), (CHOOSE x:(~((x \\in Node)=>(?z_hkg|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))), x>> \\in a_voteunde_msghash_primea))))))>>", OF z_Htw])
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 153"; *} qed
lemma ob'163:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
fixes Node
fixes Quorum
fixes Value
fixes a_voteunde_requestunde_msga a_voteunde_requestunde_msga'
fixes voted voted'
fixes a_voteunde_msga a_voteunde_msga'
fixes votes votes'
fixes leader leader'
fixes decided decided'
fixes a_requnde_historya a_requnde_historya'
(* usable definition vars suppressed *)
(* usable definition Spec suppressed *)
(* usable definition Symmetry suppressed *)
(* usable definition Safety suppressed *)
(* usable definition SplitVote suppressed *)
(* usable definition Liveness suppressed *)
assumes v'26: "(((((((a_voteunde_requestunde_msga) \<in> ((SUBSET (((Node) \<times> (Node))))))) & (((voted) \<in> ([(Node) \<rightarrow> (BOOLEAN)]))) & (((a_voteunde_msga) \<in> ((SUBSET (((Node) \<times> (Node))))))) & (((votes) \<in> ([(Node) \<rightarrow> ((SUBSET (Node)))]))) & (((leader) \<in> ([(Node) \<rightarrow> (BOOLEAN)]))) & (((decided) \<in> ([(Node) \<rightarrow> ((SUBSET (Value)))])))) & (\<forall> a_n1a \<in> (Node) : (\<forall> a_n2a \<in> (Node) : (\<forall> a_v1a \<in> (Value) : (\<forall> a_v2a \<in> (Value) : (((((((a_v1a) \<in> (fapply ((decided), (a_n1a))))) \<and> (((a_v2a) \<in> (fapply ((decided), (a_n2a))))))) \<Rightarrow> (((a_v1a) = (a_v2a))))))))) & (\<forall> VARI \<in> (Node) : (\<forall> VARJ \<in> (Node) : (((((<<(VARJ), (VARI)>>) \<in> (a_voteunde_msga))) \<or> ((~ (((VARJ) \<in> (fapply ((votes), (VARI))))))))))) & (\<forall> VARI \<in> (Node) : (\<exists> QJ \<in> (Quorum) : (\<forall> VALI \<in> (Value) : (((((QJ) \<subseteq> (fapply ((votes), (VARI))))) \<or> ((~ (((VALI) \<in> (fapply ((decided), (VARI)))))))))))) & (\<forall> VARI \<in> (Node) : (\<forall> VARJ \<in> (Node) : (((fapply ((voted), (VARI))) \<or> ((~ (((<<(VARI), (VARJ)>>) \<in> (a_voteunde_msga))))))))) & (\<forall> VARI \<in> (Node) : (\<exists> QJ \<in> (Quorum) : (((((QJ) \<subseteq> (fapply ((votes), (VARI))))) \<or> ((~ (fapply ((leader), (VARI))))))))) & (\<forall> VARI \<in> (Node) : (\<forall> VALI \<in> (Value) : (((fapply ((leader), (VARI))) \<or> ((~ (((VALI) \<in> (fapply ((decided), (VARI))))))))))) & (\<forall> VARI \<in> (Node) : (\<forall> VARJ \<in> (Node) : (\<forall> VARK \<in> (Node) : (((((((((VARI) = (VARK))) \<and> (((votes) = (votes))))) \<or> ((~ (((<<(VARJ), (VARI)>>) \<in> (a_voteunde_msga))))))) \<or> ((~ (((VARJ) \<in> (fapply ((votes), (VARK)))))))))))) & (\<forall> VARI \<in> (Node) : (\<forall> VARJ \<in> (Node) : (\<forall> VARK \<in> (Node) : (((((((((VARJ) = (VARK))) \<and> (((votes) = (votes))))) \<or> ((~ (((<<(VARI), (VARK)>>) \<in> (a_voteunde_msga))))))) \<or> ((~ (((<<(VARI), (VARJ)>>) \<in> (a_voteunde_msga))))))))))) \<and> ((((\<exists> i \<in> (Node) : (\<exists> j \<in> (Node) : (((~ (fapply ((voted), (i))))) & (((<<(j), (i)>>) \<in> (a_voteunde_requestunde_msga))) & ((((a_voteunde_requestunde_msghash_primea :: c)) = (((a_voteunde_requestunde_msga) \\ ({(<<(j), (i)>>)}))))) & ((((a_voteunde_msghash_primea :: c)) = (((a_voteunde_msga) \<union> ({(<<(i), (j)>>)}))))) & ((((a_votedhash_primea :: c)) = ([(voted) EXCEPT ![(i)] = (TRUE)]))) & ((((a_voteshash_primea :: c)) = (votes))) & ((((a_decidedhash_primea :: c)) = (decided))) & ((((a_leaderhash_primea :: c)) = (leader))) & ((((a_requnde_historyhash_primea :: c)) = (a_requnde_historya)))))) | (\<exists> i \<in> (Node) : (\<exists> j \<in> (Node) : ((fapply ((voted), (i))) & ((((a_voteunde_requestunde_msghash_primea :: c)) = (((a_voteunde_requestunde_msga) \\ ({(<<(j), (i)>>)}))))) & ((((a_voteunde_msghash_primea :: c)) = (a_voteunde_msga))) & ((((a_votedhash_primea :: c)) = (voted))) & ((((a_voteshash_primea :: c)) = (votes))) & ((((a_decidedhash_primea :: c)) = (decided))) & ((((a_leaderhash_primea :: c)) = (leader))) & ((((a_requnde_historyhash_primea :: c)) = (a_requnde_historya)))))) | (\<exists> i \<in> (Node) : (\<exists> j \<in> (Node) : ((((<<(j), (i)>>) \<in> (a_voteunde_msga))) & ((((a_voteshash_primea :: c)) = ([(votes) EXCEPT ![(i)] = (((fapply ((votes), (i))) \<union> ({(j)})))]))) & ((((a_votedhash_primea :: c)) = (voted))) & ((((a_voteunde_msghash_primea :: c)) = (a_voteunde_msga))) & ((((a_leaderhash_primea :: c)) = (leader))) & ((((a_decidedhash_primea :: c)) = (decided))) & ((((a_voteunde_requestunde_msghash_primea :: c)) = (a_voteunde_requestunde_msga))) & ((((a_requnde_historyhash_primea :: c)) = (a_requnde_historya)))))) | (\<exists> i \<in> (Node) : (\<exists> Q \<in> (Quorum) : ((((Q) \<subseteq> (fapply ((votes), (i))))) & ((((a_leaderhash_primea :: c)) = ([(leader) EXCEPT ![(i)] = (TRUE)]))) & ((((a_voteshash_primea :: c)) = (votes))) & ((((a_votedhash_primea :: c)) = (voted))) & ((((a_voteunde_msghash_primea :: c)) = (a_voteunde_msga))) & ((((a_decidedhash_primea :: c)) = (decided))) & ((((a_voteunde_requestunde_msghash_primea :: c)) = (a_voteunde_requestunde_msga))) & ((((a_requnde_historyhash_primea :: c)) = (a_requnde_historya)))))) | (\<exists> i \<in> (Node) : (\<exists> j \<in> (Node) : (\<exists> v \<in> (Value) : ((fapply ((leader), (i))) & ((({}) = (fapply ((decided), (i))))) & ((((a_decidedhash_primea :: c)) = ([(decided) EXCEPT ![(i)] = (((fapply ((decided), (i))) \<union> ({(v)})))]))) & ((((a_voteshash_primea :: c)) = (votes))) & ((((a_votedhash_primea :: c)) = (voted))) & ((((a_voteunde_msghash_primea :: c)) = (a_voteunde_msga))) & ((((a_leaderhash_primea :: c)) = (leader))) & ((((a_voteunde_requestunde_msghash_primea :: c)) = (a_voteunde_requestunde_msga))) & ((((a_requnde_historyhash_primea :: c)) = (a_requnde_historya)))))))) \<or> (\<exists> i \<in> (Node) : (\<exists> j \<in> (Node) : ((((<<(i), (j)>>) \<notin> (a_requnde_historya))) & (\<forall> a_dst2a \<in> (Node) : (((<<(i), (a_dst2a)>>) \<notin> (a_voteunde_requestunde_msga)))) & ((((a_voteunde_requestunde_msghash_primea :: c)) = (((a_voteunde_requestunde_msga) \<union> ({(<<(i), (j)>>)}))))) & ((((a_requnde_historyhash_primea :: c)) = (((a_requnde_historya) \<union> ({(<<(i), (j)>>)}))))) & (((((a_votedhash_primea :: c)) = (voted))) & ((((a_voteunde_msghash_primea :: c)) = (a_voteunde_msga))) & ((((a_voteshash_primea :: c)) = (votes))) & ((((a_leaderhash_primea :: c)) = (leader))) & ((((a_decidedhash_primea :: c)) = (decided)))))))))))"
fixes i
assumes i_in : "(i \<in> (Node))"
fixes j
assumes j_in : "(j \<in> (Node))"
assumes v'45: "((((<<(i), (j)>>) \<notin> (a_requnde_historya))) & (\<forall> a_dst2a \<in> (Node) : (((<<(i), (a_dst2a)>>) \<notin> (a_voteunde_requestunde_msga)))))"
assumes v'46: "((((a_voteunde_requestunde_msghash_primea :: c)) = (((a_voteunde_requestunde_msga) \<union> ({(<<(i), (j)>>)})))))"
assumes v'47: "((((a_requnde_historyhash_primea :: c)) = (((a_requnde_historya) \<union> ({(<<(i), (j)>>)})))))"
assumes v'48: "((((a_votedhash_primea :: c)) = (voted)))"
assumes v'49: "((((a_voteunde_msghash_primea :: c)) = (a_voteunde_msga)))"
assumes v'50: "((((a_voteshash_primea :: c)) = (votes)))"
assumes v'51: "((((a_leaderhash_primea :: c)) = (leader)))"
assumes v'52: "((((a_decidedhash_primea :: c)) = (decided)))"
shows "(\<forall> VARI \<in> (Node) : (\<forall> VARJ \<in> (Node) : (((fapply (((a_votedhash_primea :: c)), (VARI))) \<or> ((~ (((<<(VARI), (VARJ)>>) \<in> ((a_voteunde_msghash_primea :: c))))))))))"(is "PROP ?ob'163")
proof -
ML_command {* writeln "*** TLAPS ENTER 163"; *}
show "PROP ?ob'163"

(* BEGIN ZENON INPUT
;; file=consensus_epr_IndProofs.tlaps/tlapm_76fe9b.znn; PATH='/home/egolf/.opam/4.07.1/bin:/home/egolf/.local/bin:/home/egolf/bin:/home/egolf/mambaforge/bin:/home/egolf/mambaforge/condabin:/home/egolf/.opam/4.07.1/bin:/home/egolf/.local/bin:/home/egolf/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/home/egolf/.local/bin/gurobi952/linux64/bin:/home/egolf/Projects/apalache/bin:/home/egolf/opt/foxitsoftware/foxitreader:/home/egolf/.local/bin/gurobi952/linux64/bin:/home/egolf/Projects/apalache/bin:/home/egolf/opt/foxitsoftware/foxitreader:/usr/local/bin:/usr/local/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >consensus_epr_IndProofs.tlaps/tlapm_76fe9b.znn.out
;; obligation #163
$hyp "v'26" (/\ (/\ (/\ (TLA.in a_voteunde_requestunde_msga
(TLA.SUBSET (TLA.prod Node Node))) (TLA.in voted
(TLA.FuncSet Node (TLA.set T. F.))) (TLA.in a_voteunde_msga
(TLA.SUBSET (TLA.prod Node Node))) (TLA.in votes
(TLA.FuncSet Node (TLA.SUBSET Node))) (TLA.in leader
(TLA.FuncSet Node (TLA.set T. F.))) (TLA.in decided
(TLA.FuncSet Node (TLA.SUBSET Value))))
(TLA.bAll Node ((a_n1a) (TLA.bAll Node ((a_n2a) (TLA.bAll Value ((a_v1a) (TLA.bAll Value ((a_v2a) (=> (/\ (TLA.in a_v1a
(TLA.fapply decided a_n1a)) (TLA.in a_v2a (TLA.fapply decided a_n2a)))
(= a_v1a a_v2a))))))))))
(TLA.bAll Node ((VARI) (TLA.bAll Node ((VARJ) (\/ (TLA.in (TLA.tuple VARJ
VARI) a_voteunde_msga) (-. (TLA.in VARJ (TLA.fapply votes VARI))))))))
(TLA.bAll Node ((VARI) (TLA.bEx Quorum ((QJ) (TLA.bAll Value ((VALI) (\/ (TLA.subseteq QJ
(TLA.fapply votes VARI)) (-. (TLA.in VALI (TLA.fapply decided VARI))))))))))
(TLA.bAll Node ((VARI) (TLA.bAll Node ((VARJ) (\/ (TLA.fapply voted VARI)
(-. (TLA.in (TLA.tuple VARI VARJ) a_voteunde_msga)))))))
(TLA.bAll Node ((VARI) (TLA.bEx Quorum ((QJ) (\/ (TLA.subseteq QJ
(TLA.fapply votes VARI)) (-. (TLA.fapply leader VARI)))))))
(TLA.bAll Node ((VARI) (TLA.bAll Value ((VALI) (\/ (TLA.fapply leader VARI)
(-. (TLA.in VALI (TLA.fapply decided VARI))))))))
(TLA.bAll Node ((VARI) (TLA.bAll Node ((VARJ) (TLA.bAll Node ((VARK) (\/ (\/ (/\ (= VARI
VARK) (= votes votes)) (-. (TLA.in (TLA.tuple VARJ VARI) a_voteunde_msga)))
(-. (TLA.in VARJ (TLA.fapply votes VARK))))))))))
(TLA.bAll Node ((VARI) (TLA.bAll Node ((VARJ) (TLA.bAll Node ((VARK) (\/ (\/ (/\ (= VARJ
VARK) (= votes votes)) (-. (TLA.in (TLA.tuple VARI VARK) a_voteunde_msga)))
(-. (TLA.in (TLA.tuple VARI VARJ) a_voteunde_msga))))))))))
(\/ (\/ (TLA.bEx Node ((i) (TLA.bEx Node ((j) (/\ (-. (TLA.fapply voted i))
(TLA.in (TLA.tuple j i) a_voteunde_requestunde_msga)
(= a_voteunde_requestunde_msghash_primea
(TLA.setminus a_voteunde_requestunde_msga (TLA.set (TLA.tuple j i))))
(= a_voteunde_msghash_primea (TLA.cup a_voteunde_msga (TLA.set (TLA.tuple i
j)))) (= a_votedhash_primea (TLA.except voted i T.)) (= a_voteshash_primea
votes) (= a_decidedhash_primea decided) (= a_leaderhash_primea leader)
(= a_requnde_historyhash_primea a_requnde_historya))))))
(TLA.bEx Node ((i) (TLA.bEx Node ((j) (/\ (TLA.fapply voted i)
(= a_voteunde_requestunde_msghash_primea
(TLA.setminus a_voteunde_requestunde_msga (TLA.set (TLA.tuple j i))))
(= a_voteunde_msghash_primea a_voteunde_msga) (= a_votedhash_primea voted)
(= a_voteshash_primea votes) (= a_decidedhash_primea decided)
(= a_leaderhash_primea leader) (= a_requnde_historyhash_primea
a_requnde_historya))))))
(TLA.bEx Node ((i) (TLA.bEx Node ((j) (/\ (TLA.in (TLA.tuple j i)
a_voteunde_msga) (= a_voteshash_primea
(TLA.except votes i (TLA.cup (TLA.fapply votes i) (TLA.set j))))
(= a_votedhash_primea voted) (= a_voteunde_msghash_primea a_voteunde_msga)
(= a_leaderhash_primea leader) (= a_decidedhash_primea decided)
(= a_voteunde_requestunde_msghash_primea a_voteunde_requestunde_msga)
(= a_requnde_historyhash_primea a_requnde_historya))))))
(TLA.bEx Node ((i) (TLA.bEx Quorum ((Q) (/\ (TLA.subseteq Q
(TLA.fapply votes i)) (= a_leaderhash_primea (TLA.except leader i T.))
(= a_voteshash_primea votes) (= a_votedhash_primea voted)
(= a_voteunde_msghash_primea a_voteunde_msga) (= a_decidedhash_primea
decided) (= a_voteunde_requestunde_msghash_primea
a_voteunde_requestunde_msga) (= a_requnde_historyhash_primea
a_requnde_historya))))))
(TLA.bEx Node ((i) (TLA.bEx Node ((j) (TLA.bEx Value ((v) (/\ (TLA.fapply leader i)
(= TLA.emptyset (TLA.fapply decided i)) (= a_decidedhash_primea
(TLA.except decided i (TLA.cup (TLA.fapply decided i) (TLA.set v))))
(= a_voteshash_primea votes) (= a_votedhash_primea voted)
(= a_voteunde_msghash_primea a_voteunde_msga) (= a_leaderhash_primea leader)
(= a_voteunde_requestunde_msghash_primea a_voteunde_requestunde_msga)
(= a_requnde_historyhash_primea a_requnde_historya)))))))))
(TLA.bEx Node ((i) (TLA.bEx Node ((j) (/\ (-. (TLA.in (TLA.tuple i j)
a_requnde_historya)) (TLA.bAll Node ((a_dst2a) (-. (TLA.in (TLA.tuple i
a_dst2a) a_voteunde_requestunde_msga))))
(= a_voteunde_requestunde_msghash_primea (TLA.cup a_voteunde_requestunde_msga
(TLA.set (TLA.tuple i j)))) (= a_requnde_historyhash_primea
(TLA.cup a_requnde_historya (TLA.set (TLA.tuple i j))))
(/\ (= a_votedhash_primea voted) (= a_voteunde_msghash_primea
a_voteunde_msga) (= a_voteshash_primea votes) (= a_leaderhash_primea leader)
(= a_decidedhash_primea
decided)))))))))
$hyp "i_in" (TLA.in i Node)
$hyp "j_in" (TLA.in j Node)
$hyp "v'45" (/\ (-. (TLA.in (TLA.tuple i j) a_requnde_historya))
(TLA.bAll Node ((a_dst2a) (-. (TLA.in (TLA.tuple i a_dst2a)
a_voteunde_requestunde_msga)))))
$hyp "v'46" (= a_voteunde_requestunde_msghash_primea
(TLA.cup a_voteunde_requestunde_msga (TLA.set (TLA.tuple i
j))))
$hyp "v'47" (= a_requnde_historyhash_primea (TLA.cup a_requnde_historya
(TLA.set (TLA.tuple i j))))
$hyp "v'48" (= a_votedhash_primea
voted)
$hyp "v'49" (= a_voteunde_msghash_primea
a_voteunde_msga)
$hyp "v'50" (= a_voteshash_primea votes)
$hyp "v'51" (= a_leaderhash_primea leader)
$hyp "v'52" (= a_decidedhash_primea
decided)
$goal (TLA.bAll Node ((VARI) (TLA.bAll Node ((VARJ) (\/ (TLA.fapply a_votedhash_primea VARI)
(-. (TLA.in (TLA.tuple VARI VARJ)
a_voteunde_msghash_primea)))))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Ha:"((((a_voteunde_requestunde_msga \\in SUBSET(prod(Node, Node)))&((voted \\in FuncSet(Node, {TRUE, FALSE}))&((a_voteunde_msga \\in SUBSET(prod(Node, Node)))&((votes \\in FuncSet(Node, SUBSET(Node)))&((leader \\in FuncSet(Node, {TRUE, FALSE}))&(decided \\in FuncSet(Node, SUBSET(Value))))))))&(bAll(Node, (\<lambda>a_n1a. bAll(Node, (\<lambda>a_n2a. bAll(Value, (\<lambda>a_v1a. bAll(Value, (\<lambda>a_v2a. (((a_v1a \\in (decided[a_n1a]))&(a_v2a \\in (decided[a_n2a])))=>(a_v1a=a_v2a))))))))))&(bAll(Node, (\<lambda>VARI. bAll(Node, (\<lambda>VARJ. ((<<VARJ, VARI>> \\in a_voteunde_msga)|(~(VARJ \\in (votes[VARI]))))))))&(bAll(Node, (\<lambda>VARI. bEx(Quorum, (\<lambda>QJ. bAll(Value, (\<lambda>VALI. ((QJ \\subseteq (votes[VARI]))|(~(VALI \\in (decided[VARI]))))))))))&(bAll(Node, (\<lambda>VARI. bAll(Node, (\<lambda>VARJ. ((voted[VARI])|(~(<<VARI, VARJ>> \\in a_voteunde_msga)))))))&(bAll(Node, (\<lambda>VARI. bEx(Quorum, (\<lambda>QJ. ((QJ \\subseteq (votes[VARI]))|(~(leader[VARI])))))))&(bAll(Node, (\<lambda>VARI. bAll(Value, (\<lambda>VALI. ((leader[VARI])|(~(VALI \\in (decided[VARI]))))))))&(bAll(Node, (\<lambda>VARI. bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARI=VARK)&(votes=votes))|(~(<<VARJ, VARI>> \\in a_voteunde_msga)))|(~(VARJ \\in (votes[VARK]))))))))))&bAll(Node, (\<lambda>VARI. bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(votes=votes))|(~(<<VARI, VARK>> \\in a_voteunde_msga)))|(~(<<VARI, VARJ>> \\in a_voteunde_msga)))))))))))))))))&((bEx(Node, (\<lambda>i. bEx(Node, (\<lambda>j. ((~(voted[i]))&((<<j, i>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, i>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<i, j>>}))&((a_votedhash_primea=except(voted, i, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))|(bEx(Node, (\<lambda>i. bEx(Node, (\<lambda>j. ((voted[i])&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, i>>}))&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_votedhash_primea=voted)&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))|(bEx(Node, (\<lambda>i. bEx(Node, (\<lambda>j. ((<<j, i>> \\in a_voteunde_msga)&((a_voteshash_primea=except(votes, i, ((votes[i]) \\cup {j})))&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_decidedhash_primea=decided)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))|(bEx(Node, (\<lambda>i. bEx(Quorum, (\<lambda>Q. ((Q \\subseteq (votes[i]))&((a_leaderhash_primea=except(leader, i, TRUE))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_decidedhash_primea=decided)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))|bEx(Node, (\<lambda>i. bEx(Node, (\<lambda>j. bEx(Value, (\<lambda>v. ((leader[i])&(({}=(decided[i]))&((a_decidedhash_primea=except(decided, i, ((decided[i]) \\cup {v})))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))))))))|bEx(Node, (\<lambda>i. bEx(Node, (\<lambda>j. ((~(<<i, j>> \\in a_requnde_historya))&(bAll(Node, (\<lambda>a_dst2a. (~(<<i, a_dst2a>> \\in a_voteunde_requestunde_msga))))&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\cup {<<i, j>>}))&((a_requnde_historyhash_primea=(a_requnde_historya \\cup {<<i, j>>}))&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_voteshash_primea=votes)&((a_leaderhash_primea=leader)&(a_decidedhash_primea=decided)))))))))))))))" (is "?z_hm&?z_hfo")
 using v'26 by blast
 have z_Hh:"(a_voteunde_msghash_primea=a_voteunde_msga)"
 using v'49 by blast
 have z_Hg:"(a_votedhash_primea=voted)"
 using v'48 by blast
 assume z_Hl:"(~bAll(Node, (\<lambda>VARI. bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[VARI])|(~(<<VARI, VARJ>> \\in a_voteunde_msghash_primea))))))))" (is "~?z_hki")
 have z_Hm: "?z_hm" (is "?z_hn&?z_hbq")
 by (rule zenon_and_0 [OF z_Ha])
 have z_Hbq: "?z_hbq" (is "?z_hbr&?z_hck")
 by (rule zenon_and_1 [OF z_Hm])
 have z_Hck: "?z_hck" (is "?z_hcl&?z_hcx")
 by (rule zenon_and_1 [OF z_Hbq])
 have z_Hcx: "?z_hcx" (is "?z_hcy&?z_hdm")
 by (rule zenon_and_1 [OF z_Hck])
 have z_Hdm: "?z_hdm" (is "?z_hdn&?z_hdw")
 by (rule zenon_and_1 [OF z_Hcx])
 have z_Hdn: "?z_hdn"
 by (rule zenon_and_0 [OF z_Hdm])
 have z_Hkq_z_Hdn: "(\\A x:((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((voted[x])|(~(<<x, VARJ>> \\in a_voteunde_msga))))))) == ?z_hdn" (is "?z_hkq == _")
 by (unfold bAll_def)
 have z_Hkq: "?z_hkq" (is "\\A x : ?z_hlb(x)")
 by (unfold z_Hkq_z_Hdn, fact z_Hdn)
 have z_Hlc_z_Hl: "(~(\\A x:((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))) == (~?z_hki)" (is "?z_hlc == ?z_hl")
 by (unfold bAll_def)
 have z_Hlc: "?z_hlc" (is "~(\\A x : ?z_hll(x))")
 by (unfold z_Hlc_z_Hl, fact z_Hl)
 have z_Hlm: "(\\E x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea))))))))" (is "\\E x : ?z_hlo(x)")
 by (rule zenon_notallex_0 [of "?z_hll", OF z_Hlc])
 have z_Hlp: "?z_hlo((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))" (is "~(?z_hlr=>?z_hls)")
 by (rule zenon_ex_choose_0 [of "?z_hlo", OF z_Hlm])
 have z_Hlr: "?z_hlr"
 by (rule zenon_notimply_0 [OF z_Hlp])
 have z_Hlt: "(~?z_hls)"
 by (rule zenon_notimply_1 [OF z_Hlp])
 have z_Hlu_z_Hlt: "(~(\\A x:((x \\in Node)=>((a_votedhash_primea[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea))))))))])|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))), x>> \\in a_voteunde_msghash_primea)))))) == (~?z_hls)" (is "?z_hlu == ?z_hlt")
 by (unfold bAll_def)
 have z_Hlu: "?z_hlu" (is "~(\\A x : ?z_hmc(x))")
 by (unfold z_Hlu_z_Hlt, fact z_Hlt)
 have z_Hmd: "(\\E x:(~((x \\in Node)=>((a_votedhash_primea[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea))))))))])|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))), x>> \\in a_voteunde_msghash_primea))))))" (is "\\E x : ?z_hmf(x)")
 by (rule zenon_notallex_0 [of "?z_hmc", OF z_Hlu])
 have z_Hmg: "?z_hmf((CHOOSE x:(~((x \\in Node)=>((a_votedhash_primea[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea))))))))])|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))), x>> \\in a_voteunde_msghash_primea)))))))" (is "~(?z_hmi=>?z_hmj)")
 by (rule zenon_ex_choose_0 [of "?z_hmf", OF z_Hmd])
 have z_Hmi: "?z_hmi"
 by (rule zenon_notimply_0 [OF z_Hmg])
 have z_Hmk: "(~?z_hmj)" (is "~(?z_hly|?z_hml)")
 by (rule zenon_notimply_1 [OF z_Hmg])
 have z_Hmm: "(~?z_hly)"
 by (rule zenon_notor_0 [OF z_Hmk])
 have z_Hmn: "(~?z_hml)" (is "~~?z_hmo")
 by (rule zenon_notor_1 [OF z_Hmk])
 have z_Hmo: "?z_hmo"
 by (rule zenon_notnot_0 [OF z_Hmn])
 have z_Hmp: "(~(voted[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea))))))))]))" (is "~?z_hmq")
 by (rule subst [where P="(\<lambda>zenon_Vob. (~(zenon_Vob[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea))))))))])))", OF z_Hg z_Hmm])
 have z_Hmv: "(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))), (CHOOSE x:(~((x \\in Node)=>(?z_hly|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))), x>> \\in a_voteunde_msghash_primea))))))>> \\in a_voteunde_msga)" (is "?z_hmv")
 by (rule subst [where P="(\<lambda>zenon_Vnb. (<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))), (CHOOSE x:(~((x \\in Node)=>(?z_hly|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))), x>> \\in a_voteunde_msghash_primea))))))>> \\in zenon_Vnb))", OF z_Hh z_Hmo])
 have z_Hna: "?z_hlb((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))" (is "_=>?z_hnb")
 by (rule zenon_all_0 [of "?z_hlb" "(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea))))))))", OF z_Hkq])
 show FALSE
 proof (rule zenon_imply [OF z_Hna])
  assume z_Hnc:"(~?z_hlr)"
  show FALSE
  by (rule notE [OF z_Hnc z_Hlr])
 next
  assume z_Hnb:"?z_hnb"
  have z_Hnd_z_Hnb: "(\\A x:((x \\in Node)=>(?z_hmq|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))), x>> \\in a_voteunde_msga))))) == ?z_hnb" (is "?z_hnd == _")
  by (unfold bAll_def)
  have z_Hnd: "?z_hnd" (is "\\A x : ?z_hni(x)")
  by (unfold z_Hnd_z_Hnb, fact z_Hnb)
  have z_Hnj: "?z_hni((CHOOSE x:(~((x \\in Node)=>(?z_hly|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))), x>> \\in a_voteunde_msghash_primea)))))))" (is "_=>?z_hnk")
  by (rule zenon_all_0 [of "?z_hni" "(CHOOSE x:(~((x \\in Node)=>(?z_hly|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))), x>> \\in a_voteunde_msghash_primea))))))", OF z_Hnd])
  show FALSE
  proof (rule zenon_imply [OF z_Hnj])
   assume z_Hnl:"(~?z_hmi)"
   show FALSE
   by (rule notE [OF z_Hnl z_Hmi])
  next
   assume z_Hnk:"?z_hnk" (is "_|?z_hnm")
   show FALSE
   proof (rule zenon_or [OF z_Hnk])
    assume z_Hmq:"?z_hmq"
    show FALSE
    by (rule notE [OF z_Hmp z_Hmq])
   next
    assume z_Hnm:"?z_hnm"
    show FALSE
    by (rule notE [OF z_Hnm z_Hmv])
   qed
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 163"; *} qed
lemma ob'161:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
fixes Node
fixes Quorum
fixes Value
fixes a_voteunde_requestunde_msga a_voteunde_requestunde_msga'
fixes voted voted'
fixes a_voteunde_msga a_voteunde_msga'
fixes votes votes'
fixes leader leader'
fixes decided decided'
fixes a_requnde_historya a_requnde_historya'
(* usable definition vars suppressed *)
(* usable definition Spec suppressed *)
(* usable definition Symmetry suppressed *)
(* usable definition Safety suppressed *)
(* usable definition SplitVote suppressed *)
(* usable definition Liveness suppressed *)
assumes v'26: "(((((((a_voteunde_requestunde_msga) \<in> ((SUBSET (((Node) \<times> (Node))))))) & (((voted) \<in> ([(Node) \<rightarrow> (BOOLEAN)]))) & (((a_voteunde_msga) \<in> ((SUBSET (((Node) \<times> (Node))))))) & (((votes) \<in> ([(Node) \<rightarrow> ((SUBSET (Node)))]))) & (((leader) \<in> ([(Node) \<rightarrow> (BOOLEAN)]))) & (((decided) \<in> ([(Node) \<rightarrow> ((SUBSET (Value)))])))) & (\<forall> a_n1a \<in> (Node) : (\<forall> a_n2a \<in> (Node) : (\<forall> a_v1a \<in> (Value) : (\<forall> a_v2a \<in> (Value) : (((((((a_v1a) \<in> (fapply ((decided), (a_n1a))))) \<and> (((a_v2a) \<in> (fapply ((decided), (a_n2a))))))) \<Rightarrow> (((a_v1a) = (a_v2a))))))))) & (\<forall> VARI \<in> (Node) : (\<forall> VARJ \<in> (Node) : (((((<<(VARJ), (VARI)>>) \<in> (a_voteunde_msga))) \<or> ((~ (((VARJ) \<in> (fapply ((votes), (VARI))))))))))) & (\<forall> VARI \<in> (Node) : (\<exists> QJ \<in> (Quorum) : (\<forall> VALI \<in> (Value) : (((((QJ) \<subseteq> (fapply ((votes), (VARI))))) \<or> ((~ (((VALI) \<in> (fapply ((decided), (VARI)))))))))))) & (\<forall> VARI \<in> (Node) : (\<forall> VARJ \<in> (Node) : (((fapply ((voted), (VARI))) \<or> ((~ (((<<(VARI), (VARJ)>>) \<in> (a_voteunde_msga))))))))) & (\<forall> VARI \<in> (Node) : (\<exists> QJ \<in> (Quorum) : (((((QJ) \<subseteq> (fapply ((votes), (VARI))))) \<or> ((~ (fapply ((leader), (VARI))))))))) & (\<forall> VARI \<in> (Node) : (\<forall> VALI \<in> (Value) : (((fapply ((leader), (VARI))) \<or> ((~ (((VALI) \<in> (fapply ((decided), (VARI))))))))))) & (\<forall> VARI \<in> (Node) : (\<forall> VARJ \<in> (Node) : (\<forall> VARK \<in> (Node) : (((((((((VARI) = (VARK))) \<and> (((votes) = (votes))))) \<or> ((~ (((<<(VARJ), (VARI)>>) \<in> (a_voteunde_msga))))))) \<or> ((~ (((VARJ) \<in> (fapply ((votes), (VARK)))))))))))) & (\<forall> VARI \<in> (Node) : (\<forall> VARJ \<in> (Node) : (\<forall> VARK \<in> (Node) : (((((((((VARJ) = (VARK))) \<and> (((votes) = (votes))))) \<or> ((~ (((<<(VARI), (VARK)>>) \<in> (a_voteunde_msga))))))) \<or> ((~ (((<<(VARI), (VARJ)>>) \<in> (a_voteunde_msga))))))))))) \<and> ((((\<exists> i \<in> (Node) : (\<exists> j \<in> (Node) : (((~ (fapply ((voted), (i))))) & (((<<(j), (i)>>) \<in> (a_voteunde_requestunde_msga))) & ((((a_voteunde_requestunde_msghash_primea :: c)) = (((a_voteunde_requestunde_msga) \\ ({(<<(j), (i)>>)}))))) & ((((a_voteunde_msghash_primea :: c)) = (((a_voteunde_msga) \<union> ({(<<(i), (j)>>)}))))) & ((((a_votedhash_primea :: c)) = ([(voted) EXCEPT ![(i)] = (TRUE)]))) & ((((a_voteshash_primea :: c)) = (votes))) & ((((a_decidedhash_primea :: c)) = (decided))) & ((((a_leaderhash_primea :: c)) = (leader))) & ((((a_requnde_historyhash_primea :: c)) = (a_requnde_historya)))))) | (\<exists> i \<in> (Node) : (\<exists> j \<in> (Node) : ((fapply ((voted), (i))) & ((((a_voteunde_requestunde_msghash_primea :: c)) = (((a_voteunde_requestunde_msga) \\ ({(<<(j), (i)>>)}))))) & ((((a_voteunde_msghash_primea :: c)) = (a_voteunde_msga))) & ((((a_votedhash_primea :: c)) = (voted))) & ((((a_voteshash_primea :: c)) = (votes))) & ((((a_decidedhash_primea :: c)) = (decided))) & ((((a_leaderhash_primea :: c)) = (leader))) & ((((a_requnde_historyhash_primea :: c)) = (a_requnde_historya)))))) | (\<exists> i \<in> (Node) : (\<exists> j \<in> (Node) : ((((<<(j), (i)>>) \<in> (a_voteunde_msga))) & ((((a_voteshash_primea :: c)) = ([(votes) EXCEPT ![(i)] = (((fapply ((votes), (i))) \<union> ({(j)})))]))) & ((((a_votedhash_primea :: c)) = (voted))) & ((((a_voteunde_msghash_primea :: c)) = (a_voteunde_msga))) & ((((a_leaderhash_primea :: c)) = (leader))) & ((((a_decidedhash_primea :: c)) = (decided))) & ((((a_voteunde_requestunde_msghash_primea :: c)) = (a_voteunde_requestunde_msga))) & ((((a_requnde_historyhash_primea :: c)) = (a_requnde_historya)))))) | (\<exists> i \<in> (Node) : (\<exists> Q \<in> (Quorum) : ((((Q) \<subseteq> (fapply ((votes), (i))))) & ((((a_leaderhash_primea :: c)) = ([(leader) EXCEPT ![(i)] = (TRUE)]))) & ((((a_voteshash_primea :: c)) = (votes))) & ((((a_votedhash_primea :: c)) = (voted))) & ((((a_voteunde_msghash_primea :: c)) = (a_voteunde_msga))) & ((((a_decidedhash_primea :: c)) = (decided))) & ((((a_voteunde_requestunde_msghash_primea :: c)) = (a_voteunde_requestunde_msga))) & ((((a_requnde_historyhash_primea :: c)) = (a_requnde_historya)))))) | (\<exists> i \<in> (Node) : (\<exists> j \<in> (Node) : (\<exists> v \<in> (Value) : ((fapply ((leader), (i))) & ((({}) = (fapply ((decided), (i))))) & ((((a_decidedhash_primea :: c)) = ([(decided) EXCEPT ![(i)] = (((fapply ((decided), (i))) \<union> ({(v)})))]))) & ((((a_voteshash_primea :: c)) = (votes))) & ((((a_votedhash_primea :: c)) = (voted))) & ((((a_voteunde_msghash_primea :: c)) = (a_voteunde_msga))) & ((((a_leaderhash_primea :: c)) = (leader))) & ((((a_voteunde_requestunde_msghash_primea :: c)) = (a_voteunde_requestunde_msga))) & ((((a_requnde_historyhash_primea :: c)) = (a_requnde_historya)))))))) \<or> (\<exists> i \<in> (Node) : (\<exists> j \<in> (Node) : ((((<<(i), (j)>>) \<notin> (a_requnde_historya))) & (\<forall> a_dst2a \<in> (Node) : (((<<(i), (a_dst2a)>>) \<notin> (a_voteunde_requestunde_msga)))) & ((((a_voteunde_requestunde_msghash_primea :: c)) = (((a_voteunde_requestunde_msga) \<union> ({(<<(i), (j)>>)}))))) & ((((a_requnde_historyhash_primea :: c)) = (((a_requnde_historya) \<union> ({(<<(i), (j)>>)}))))) & (((((a_votedhash_primea :: c)) = (voted))) & ((((a_voteunde_msghash_primea :: c)) = (a_voteunde_msga))) & ((((a_voteshash_primea :: c)) = (votes))) & ((((a_leaderhash_primea :: c)) = (leader))) & ((((a_decidedhash_primea :: c)) = (decided)))))))))))"
assumes v'42: "(\<exists> i \<in> (Node) : (\<exists> j \<in> (Node) : (\<exists> v \<in> (Value) : ((fapply ((leader), (i))) & ((({}) = (fapply ((decided), (i))))) & ((((a_decidedhash_primea :: c)) = ([(decided) EXCEPT ![(i)] = (((fapply ((decided), (i))) \<union> ({(v)})))]))) & ((((a_voteshash_primea :: c)) = (votes))) & ((((a_votedhash_primea :: c)) = (voted))) & ((((a_voteunde_msghash_primea :: c)) = (a_voteunde_msga))) & ((((a_leaderhash_primea :: c)) = (leader))) & ((((a_voteunde_requestunde_msghash_primea :: c)) = (a_voteunde_requestunde_msga))) & ((((a_requnde_historyhash_primea :: c)) = (a_requnde_historya)))))))"
shows "(\<forall> VARI \<in> (Node) : (\<forall> VARJ \<in> (Node) : (((fapply (((a_votedhash_primea :: c)), (VARI))) \<or> ((~ (((<<(VARI), (VARJ)>>) \<in> ((a_voteunde_msghash_primea :: c))))))))))"(is "PROP ?ob'161")
proof -
ML_command {* writeln "*** TLAPS ENTER 161"; *}
show "PROP ?ob'161"

(* BEGIN ZENON INPUT
;; file=consensus_epr_IndProofs.tlaps/tlapm_973468.znn; PATH='/home/egolf/.opam/4.07.1/bin:/home/egolf/.local/bin:/home/egolf/bin:/home/egolf/mambaforge/bin:/home/egolf/mambaforge/condabin:/home/egolf/.opam/4.07.1/bin:/home/egolf/.local/bin:/home/egolf/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/home/egolf/.local/bin/gurobi952/linux64/bin:/home/egolf/Projects/apalache/bin:/home/egolf/opt/foxitsoftware/foxitreader:/home/egolf/.local/bin/gurobi952/linux64/bin:/home/egolf/Projects/apalache/bin:/home/egolf/opt/foxitsoftware/foxitreader:/usr/local/bin:/usr/local/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >consensus_epr_IndProofs.tlaps/tlapm_973468.znn.out
;; obligation #161
$hyp "v'26" (/\ (/\ (/\ (TLA.in a_voteunde_requestunde_msga
(TLA.SUBSET (TLA.prod Node Node))) (TLA.in voted
(TLA.FuncSet Node (TLA.set T. F.))) (TLA.in a_voteunde_msga
(TLA.SUBSET (TLA.prod Node Node))) (TLA.in votes
(TLA.FuncSet Node (TLA.SUBSET Node))) (TLA.in leader
(TLA.FuncSet Node (TLA.set T. F.))) (TLA.in decided
(TLA.FuncSet Node (TLA.SUBSET Value))))
(TLA.bAll Node ((a_n1a) (TLA.bAll Node ((a_n2a) (TLA.bAll Value ((a_v1a) (TLA.bAll Value ((a_v2a) (=> (/\ (TLA.in a_v1a
(TLA.fapply decided a_n1a)) (TLA.in a_v2a (TLA.fapply decided a_n2a)))
(= a_v1a a_v2a))))))))))
(TLA.bAll Node ((VARI) (TLA.bAll Node ((VARJ) (\/ (TLA.in (TLA.tuple VARJ
VARI) a_voteunde_msga) (-. (TLA.in VARJ (TLA.fapply votes VARI))))))))
(TLA.bAll Node ((VARI) (TLA.bEx Quorum ((QJ) (TLA.bAll Value ((VALI) (\/ (TLA.subseteq QJ
(TLA.fapply votes VARI)) (-. (TLA.in VALI (TLA.fapply decided VARI))))))))))
(TLA.bAll Node ((VARI) (TLA.bAll Node ((VARJ) (\/ (TLA.fapply voted VARI)
(-. (TLA.in (TLA.tuple VARI VARJ) a_voteunde_msga)))))))
(TLA.bAll Node ((VARI) (TLA.bEx Quorum ((QJ) (\/ (TLA.subseteq QJ
(TLA.fapply votes VARI)) (-. (TLA.fapply leader VARI)))))))
(TLA.bAll Node ((VARI) (TLA.bAll Value ((VALI) (\/ (TLA.fapply leader VARI)
(-. (TLA.in VALI (TLA.fapply decided VARI))))))))
(TLA.bAll Node ((VARI) (TLA.bAll Node ((VARJ) (TLA.bAll Node ((VARK) (\/ (\/ (/\ (= VARI
VARK) (= votes votes)) (-. (TLA.in (TLA.tuple VARJ VARI) a_voteunde_msga)))
(-. (TLA.in VARJ (TLA.fapply votes VARK))))))))))
(TLA.bAll Node ((VARI) (TLA.bAll Node ((VARJ) (TLA.bAll Node ((VARK) (\/ (\/ (/\ (= VARJ
VARK) (= votes votes)) (-. (TLA.in (TLA.tuple VARI VARK) a_voteunde_msga)))
(-. (TLA.in (TLA.tuple VARI VARJ) a_voteunde_msga))))))))))
(\/ (\/ (TLA.bEx Node ((i) (TLA.bEx Node ((j) (/\ (-. (TLA.fapply voted i))
(TLA.in (TLA.tuple j i) a_voteunde_requestunde_msga)
(= a_voteunde_requestunde_msghash_primea
(TLA.setminus a_voteunde_requestunde_msga (TLA.set (TLA.tuple j i))))
(= a_voteunde_msghash_primea (TLA.cup a_voteunde_msga (TLA.set (TLA.tuple i
j)))) (= a_votedhash_primea (TLA.except voted i T.)) (= a_voteshash_primea
votes) (= a_decidedhash_primea decided) (= a_leaderhash_primea leader)
(= a_requnde_historyhash_primea a_requnde_historya))))))
(TLA.bEx Node ((i) (TLA.bEx Node ((j) (/\ (TLA.fapply voted i)
(= a_voteunde_requestunde_msghash_primea
(TLA.setminus a_voteunde_requestunde_msga (TLA.set (TLA.tuple j i))))
(= a_voteunde_msghash_primea a_voteunde_msga) (= a_votedhash_primea voted)
(= a_voteshash_primea votes) (= a_decidedhash_primea decided)
(= a_leaderhash_primea leader) (= a_requnde_historyhash_primea
a_requnde_historya))))))
(TLA.bEx Node ((i) (TLA.bEx Node ((j) (/\ (TLA.in (TLA.tuple j i)
a_voteunde_msga) (= a_voteshash_primea
(TLA.except votes i (TLA.cup (TLA.fapply votes i) (TLA.set j))))
(= a_votedhash_primea voted) (= a_voteunde_msghash_primea a_voteunde_msga)
(= a_leaderhash_primea leader) (= a_decidedhash_primea decided)
(= a_voteunde_requestunde_msghash_primea a_voteunde_requestunde_msga)
(= a_requnde_historyhash_primea a_requnde_historya))))))
(TLA.bEx Node ((i) (TLA.bEx Quorum ((Q) (/\ (TLA.subseteq Q
(TLA.fapply votes i)) (= a_leaderhash_primea (TLA.except leader i T.))
(= a_voteshash_primea votes) (= a_votedhash_primea voted)
(= a_voteunde_msghash_primea a_voteunde_msga) (= a_decidedhash_primea
decided) (= a_voteunde_requestunde_msghash_primea
a_voteunde_requestunde_msga) (= a_requnde_historyhash_primea
a_requnde_historya))))))
(TLA.bEx Node ((i) (TLA.bEx Node ((j) (TLA.bEx Value ((v) (/\ (TLA.fapply leader i)
(= TLA.emptyset (TLA.fapply decided i)) (= a_decidedhash_primea
(TLA.except decided i (TLA.cup (TLA.fapply decided i) (TLA.set v))))
(= a_voteshash_primea votes) (= a_votedhash_primea voted)
(= a_voteunde_msghash_primea a_voteunde_msga) (= a_leaderhash_primea leader)
(= a_voteunde_requestunde_msghash_primea a_voteunde_requestunde_msga)
(= a_requnde_historyhash_primea a_requnde_historya)))))))))
(TLA.bEx Node ((i) (TLA.bEx Node ((j) (/\ (-. (TLA.in (TLA.tuple i j)
a_requnde_historya)) (TLA.bAll Node ((a_dst2a) (-. (TLA.in (TLA.tuple i
a_dst2a) a_voteunde_requestunde_msga))))
(= a_voteunde_requestunde_msghash_primea (TLA.cup a_voteunde_requestunde_msga
(TLA.set (TLA.tuple i j)))) (= a_requnde_historyhash_primea
(TLA.cup a_requnde_historya (TLA.set (TLA.tuple i j))))
(/\ (= a_votedhash_primea voted) (= a_voteunde_msghash_primea
a_voteunde_msga) (= a_voteshash_primea votes) (= a_leaderhash_primea leader)
(= a_decidedhash_primea
decided)))))))))
$hyp "v'42" (TLA.bEx Node ((i) (TLA.bEx Node ((j) (TLA.bEx Value ((v) (/\ (TLA.fapply leader i)
(= TLA.emptyset (TLA.fapply decided i)) (= a_decidedhash_primea
(TLA.except decided i (TLA.cup (TLA.fapply decided i) (TLA.set v))))
(= a_voteshash_primea votes) (= a_votedhash_primea voted)
(= a_voteunde_msghash_primea a_voteunde_msga) (= a_leaderhash_primea leader)
(= a_voteunde_requestunde_msghash_primea a_voteunde_requestunde_msga)
(= a_requnde_historyhash_primea
a_requnde_historya))))))))
$goal (TLA.bAll Node ((VARI) (TLA.bAll Node ((VARJ) (\/ (TLA.fapply a_votedhash_primea VARI)
(-. (TLA.in (TLA.tuple VARI VARJ)
a_voteunde_msghash_primea)))))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Ha:"((((a_voteunde_requestunde_msga \\in SUBSET(prod(Node, Node)))&((voted \\in FuncSet(Node, {TRUE, FALSE}))&((a_voteunde_msga \\in SUBSET(prod(Node, Node)))&((votes \\in FuncSet(Node, SUBSET(Node)))&((leader \\in FuncSet(Node, {TRUE, FALSE}))&(decided \\in FuncSet(Node, SUBSET(Value))))))))&(bAll(Node, (\<lambda>a_n1a. bAll(Node, (\<lambda>a_n2a. bAll(Value, (\<lambda>a_v1a. bAll(Value, (\<lambda>a_v2a. (((a_v1a \\in (decided[a_n1a]))&(a_v2a \\in (decided[a_n2a])))=>(a_v1a=a_v2a))))))))))&(bAll(Node, (\<lambda>VARI. bAll(Node, (\<lambda>VARJ. ((<<VARJ, VARI>> \\in a_voteunde_msga)|(~(VARJ \\in (votes[VARI]))))))))&(bAll(Node, (\<lambda>VARI. bEx(Quorum, (\<lambda>QJ. bAll(Value, (\<lambda>VALI. ((QJ \\subseteq (votes[VARI]))|(~(VALI \\in (decided[VARI]))))))))))&(bAll(Node, (\<lambda>VARI. bAll(Node, (\<lambda>VARJ. ((voted[VARI])|(~(<<VARI, VARJ>> \\in a_voteunde_msga)))))))&(bAll(Node, (\<lambda>VARI. bEx(Quorum, (\<lambda>QJ. ((QJ \\subseteq (votes[VARI]))|(~(leader[VARI])))))))&(bAll(Node, (\<lambda>VARI. bAll(Value, (\<lambda>VALI. ((leader[VARI])|(~(VALI \\in (decided[VARI]))))))))&(bAll(Node, (\<lambda>VARI. bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARI=VARK)&(votes=votes))|(~(<<VARJ, VARI>> \\in a_voteunde_msga)))|(~(VARJ \\in (votes[VARK]))))))))))&bAll(Node, (\<lambda>VARI. bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(votes=votes))|(~(<<VARI, VARK>> \\in a_voteunde_msga)))|(~(<<VARI, VARJ>> \\in a_voteunde_msga)))))))))))))))))&((bEx(Node, (\<lambda>i. bEx(Node, (\<lambda>j. ((~(voted[i]))&((<<j, i>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, i>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<i, j>>}))&((a_votedhash_primea=except(voted, i, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))|(bEx(Node, (\<lambda>i. bEx(Node, (\<lambda>j. ((voted[i])&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, i>>}))&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_votedhash_primea=voted)&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))|(bEx(Node, (\<lambda>i. bEx(Node, (\<lambda>j. ((<<j, i>> \\in a_voteunde_msga)&((a_voteshash_primea=except(votes, i, ((votes[i]) \\cup {j})))&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_decidedhash_primea=decided)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))|(bEx(Node, (\<lambda>i. bEx(Quorum, (\<lambda>Q. ((Q \\subseteq (votes[i]))&((a_leaderhash_primea=except(leader, i, TRUE))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_decidedhash_primea=decided)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))|bEx(Node, (\<lambda>i. bEx(Node, (\<lambda>j. bEx(Value, (\<lambda>v. ((leader[i])&(({}=(decided[i]))&((a_decidedhash_primea=except(decided, i, ((decided[i]) \\cup {v})))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))))))))|bEx(Node, (\<lambda>i. bEx(Node, (\<lambda>j. ((~(<<i, j>> \\in a_requnde_historya))&(bAll(Node, (\<lambda>a_dst2a. (~(<<i, a_dst2a>> \\in a_voteunde_requestunde_msga))))&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\cup {<<i, j>>}))&((a_requnde_historyhash_primea=(a_requnde_historya \\cup {<<i, j>>}))&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_voteshash_primea=votes)&((a_leaderhash_primea=leader)&(a_decidedhash_primea=decided)))))))))))))))" (is "?z_hd&?z_hff")
 using v'26 by blast
 have z_Hb:"bEx(Node, (\<lambda>i. bEx(Node, (\<lambda>j. bEx(Value, (\<lambda>v. ((leader[i])&(({}=(decided[i]))&((a_decidedhash_primea=except(decided, i, ((decided[i]) \\cup {v})))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))))" (is "?z_hb")
 using v'42 by blast
 have zenon_L1_: "((voted[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea))))))))])=TRUE) ==> (~(a_votedhash_primea[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea))))))))])) ==> (a_votedhash_primea=voted) ==> FALSE" (is "?z_hkf ==> ?z_hkt ==> ?z_hhe ==> FALSE")
 proof -
  assume z_Hkf:"?z_hkf" (is "?z_hkg=?z_hp")
  assume z_Hkt:"?z_hkt" (is "~?z_hku")
  assume z_Hhe:"?z_hhe"
  show FALSE
  proof (rule zenon_np_eq_l [of "?z_hku" "?z_hkg" "?z_hp", OF z_Hkt z_Hkf])
   assume z_Hkv:"(?z_hku~=?z_hkg)"
   show FALSE
   proof (rule zenon_noteq [of "?z_hkg"])
    have z_Hkw: "(?z_hkg~=?z_hkg)"
    by (rule subst [where P="(\<lambda>zenon_Vzgb. ((zenon_Vzgb[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea))))))))])~=?z_hkg))", OF z_Hhe], fact z_Hkv)
    thus "(?z_hkg~=?z_hkg)" .
   qed
  next
   assume z_Hlb:"(~?z_hp)"
   show FALSE
   by (rule zenon_nottrue [OF z_Hlb])
  qed
 qed
 assume z_Hc:"(~bAll(Node, (\<lambda>VARI. bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[VARI])|(~(<<VARI, VARJ>> \\in a_voteunde_msghash_primea))))))))" (is "~?z_hlc")
 have z_Hd: "?z_hd" (is "?z_he&?z_hbh")
 by (rule zenon_and_0 [OF z_Ha])
 have z_He: "?z_he" (is "?z_hf&?z_hk")
 by (rule zenon_and_0 [OF z_Hd])
 have z_Hbh: "?z_hbh" (is "?z_hbi&?z_hcb")
 by (rule zenon_and_1 [OF z_Hd])
 have z_Hcb: "?z_hcb" (is "?z_hcc&?z_hco")
 by (rule zenon_and_1 [OF z_Hbh])
 have z_Hco: "?z_hco" (is "?z_hcp&?z_hdd")
 by (rule zenon_and_1 [OF z_Hcb])
 have z_Hdd: "?z_hdd" (is "?z_hde&?z_hdn")
 by (rule zenon_and_1 [OF z_Hco])
 have z_Hde: "?z_hde"
 by (rule zenon_and_0 [OF z_Hdd])
 have z_Hk: "?z_hk" (is "?z_hl&?z_hr")
 by (rule zenon_and_1 [OF z_He])
 have z_Hl: "?z_hl"
 by (rule zenon_and_0 [OF z_Hk])
 have z_Hlk_z_Hde: "(\\A x:((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((voted[x])|(~(<<x, VARJ>> \\in a_voteunde_msga))))))) == ?z_hde" (is "?z_hlk == _")
 by (unfold bAll_def)
 have z_Hlk: "?z_hlk" (is "\\A x : ?z_hls(x)")
 by (unfold z_Hlk_z_Hde, fact z_Hde)
 have z_Hlt_z_Hb: "(\\E x:((x \\in Node)&bEx(Node, (\<lambda>j. bEx(Value, (\<lambda>v. ((leader[x])&(({}=(decided[x]))&((a_decidedhash_primea=except(decided, x, ((decided[x]) \\cup {v})))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))))) == ?z_hb" (is "?z_hlt == _")
 by (unfold bEx_def)
 have z_Hlt: "?z_hlt" (is "\\E x : ?z_hmi(x)")
 by (unfold z_Hlt_z_Hb, fact z_Hb)
 have z_Hmj: "?z_hmi((CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. bEx(Value, (\<lambda>v. ((leader[x])&(({}=(decided[x]))&((a_decidedhash_primea=except(decided, x, ((decided[x]) \\cup {v})))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))))))" (is "?z_hml&?z_hmm")
 by (rule zenon_ex_choose_0 [of "?z_hmi", OF z_Hlt])
 have z_Hmm: "?z_hmm"
 by (rule zenon_and_1 [OF z_Hmj])
 have z_Hmn_z_Hmm: "(\\E x:((x \\in Node)&bEx(Value, (\<lambda>v. ((leader[(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. bEx(Value, (\<lambda>v. ((leader[x])&(({}=(decided[x]))&((a_decidedhash_primea=except(decided, x, ((decided[x]) \\cup {v})))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))))])&(({}=(decided[(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. bEx(Value, (\<lambda>v. ((leader[x])&(({}=(decided[x]))&((a_decidedhash_primea=except(decided, x, ((decided[x]) \\cup {v})))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))))]))&((a_decidedhash_primea=except(decided, (CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. bEx(Value, (\<lambda>v. ((leader[x])&(({}=(decided[x]))&((a_decidedhash_primea=except(decided, x, ((decided[x]) \\cup {v})))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))))), ((decided[(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. bEx(Value, (\<lambda>v. ((leader[x])&(({}=(decided[x]))&((a_decidedhash_primea=except(decided, x, ((decided[x]) \\cup {v})))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))))]) \\cup {v})))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))) == ?z_hmm" (is "?z_hmn == _")
 by (unfold bEx_def)
 have z_Hmn: "?z_hmn" (is "\\E x : ?z_hna(x)")
 by (unfold z_Hmn_z_Hmm, fact z_Hmm)
 have z_Hnb: "?z_hna((CHOOSE x:((x \\in Node)&bEx(Value, (\<lambda>v. ((leader[(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. bEx(Value, (\<lambda>v. ((leader[x])&(({}=(decided[x]))&((a_decidedhash_primea=except(decided, x, ((decided[x]) \\cup {v})))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))))])&(({}=(decided[(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. bEx(Value, (\<lambda>v. ((leader[x])&(({}=(decided[x]))&((a_decidedhash_primea=except(decided, x, ((decided[x]) \\cup {v})))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))))]))&((a_decidedhash_primea=except(decided, (CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. bEx(Value, (\<lambda>v. ((leader[x])&(({}=(decided[x]))&((a_decidedhash_primea=except(decided, x, ((decided[x]) \\cup {v})))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))))), ((decided[(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. bEx(Value, (\<lambda>v. ((leader[x])&(({}=(decided[x]))&((a_decidedhash_primea=except(decided, x, ((decided[x]) \\cup {v})))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))))]) \\cup {v})))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))))" (is "?z_hnd&?z_hmp")
 by (rule zenon_ex_choose_0 [of "?z_hna", OF z_Hmn])
 have z_Hmp: "?z_hmp"
 by (rule zenon_and_1 [OF z_Hnb])
 have z_Hne_z_Hmp: "(\\E x:((x \\in Value)&((leader[(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. bEx(Value, (\<lambda>v. ((leader[x])&(({}=(decided[x]))&((a_decidedhash_primea=except(decided, x, ((decided[x]) \\cup {v})))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))))])&(({}=(decided[(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. bEx(Value, (\<lambda>v. ((leader[x])&(({}=(decided[x]))&((a_decidedhash_primea=except(decided, x, ((decided[x]) \\cup {v})))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))))]))&((a_decidedhash_primea=except(decided, (CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. bEx(Value, (\<lambda>v. ((leader[x])&(({}=(decided[x]))&((a_decidedhash_primea=except(decided, x, ((decided[x]) \\cup {v})))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))))), ((decided[(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. bEx(Value, (\<lambda>v. ((leader[x])&(({}=(decided[x]))&((a_decidedhash_primea=except(decided, x, ((decided[x]) \\cup {v})))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))))]) \\cup {x})))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))) == ?z_hmp" (is "?z_hne == _")
 by (unfold bEx_def)
 have z_Hne: "?z_hne" (is "\\E x : ?z_hno(x)")
 by (unfold z_Hne_z_Hmp, fact z_Hmp)
 have z_Hnp: "?z_hno((CHOOSE x:((x \\in Value)&((leader[(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. bEx(Value, (\<lambda>v. ((leader[x])&(({}=(decided[x]))&((a_decidedhash_primea=except(decided, x, ((decided[x]) \\cup {v})))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))))])&(({}=(decided[(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. bEx(Value, (\<lambda>v. ((leader[x])&(({}=(decided[x]))&((a_decidedhash_primea=except(decided, x, ((decided[x]) \\cup {v})))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))))]))&((a_decidedhash_primea=except(decided, (CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. bEx(Value, (\<lambda>v. ((leader[x])&(({}=(decided[x]))&((a_decidedhash_primea=except(decided, x, ((decided[x]) \\cup {v})))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))))), ((decided[(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. bEx(Value, (\<lambda>v. ((leader[x])&(({}=(decided[x]))&((a_decidedhash_primea=except(decided, x, ((decided[x]) \\cup {v})))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))))]) \\cup {x})))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))" (is "?z_hnr&?z_hns")
 by (rule zenon_ex_choose_0 [of "?z_hno", OF z_Hne])
 have z_Hns: "?z_hns" (is "?z_hms&?z_hnt")
 by (rule zenon_and_1 [OF z_Hnp])
 have z_Hnt: "?z_hnt" (is "?z_hmu&?z_hnu")
 by (rule zenon_and_1 [OF z_Hns])
 have z_Hnu: "?z_hnu" (is "?z_hnv&?z_hjd")
 by (rule zenon_and_1 [OF z_Hnt])
 have z_Hjd: "?z_hjd" (is "?z_hgj&?z_hje")
 by (rule zenon_and_1 [OF z_Hnu])
 have z_Hje: "?z_hje" (is "?z_hhe&?z_hjf")
 by (rule zenon_and_1 [OF z_Hjd])
 have z_Hhe: "?z_hhe"
 by (rule zenon_and_0 [OF z_Hje])
 have z_Hjf: "?z_hjf" (is "?z_hhc&?z_hjg")
 by (rule zenon_and_1 [OF z_Hje])
 have z_Hhc: "?z_hhc"
 by (rule zenon_and_0 [OF z_Hjf])
 have z_Hnw_z_Hc: "(~(\\A x:((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))) == (~?z_hlc)" (is "?z_hnw == ?z_hc")
 by (unfold bAll_def)
 have z_Hnw: "?z_hnw" (is "~(\\A x : ?z_hny(x))")
 by (unfold z_Hnw_z_Hc, fact z_Hc)
 have z_Hnz: "(\\E x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea))))))))" (is "\\E x : ?z_hoa(x)")
 by (rule zenon_notallex_0 [of "?z_hny", OF z_Hnw])
 have z_Hob: "?z_hoa((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))" (is "~(?z_hoc=>?z_hod)")
 by (rule zenon_ex_choose_0 [of "?z_hoa", OF z_Hnz])
 have z_Hoc: "?z_hoc"
 by (rule zenon_notimply_0 [OF z_Hob])
 have z_Hoe: "(~?z_hod)"
 by (rule zenon_notimply_1 [OF z_Hob])
 have z_Hof_z_Hoe: "(~(\\A x:((x \\in Node)=>((a_votedhash_primea[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea))))))))])|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))), x>> \\in a_voteunde_msghash_primea)))))) == (~?z_hod)" (is "?z_hof == ?z_hoe")
 by (unfold bAll_def)
 have z_Hof: "?z_hof" (is "~(\\A x : ?z_hom(x))")
 by (unfold z_Hof_z_Hoe, fact z_Hoe)
 have z_Hon: "(\\E x:(~((x \\in Node)=>((a_votedhash_primea[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea))))))))])|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))), x>> \\in a_voteunde_msghash_primea))))))" (is "\\E x : ?z_hop(x)")
 by (rule zenon_notallex_0 [of "?z_hom", OF z_Hof])
 have z_Hoq: "?z_hop((CHOOSE x:(~((x \\in Node)=>((a_votedhash_primea[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea))))))))])|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))), x>> \\in a_voteunde_msghash_primea)))))))" (is "~(?z_hos=>?z_hot)")
 by (rule zenon_ex_choose_0 [of "?z_hop", OF z_Hon])
 have z_Hos: "?z_hos"
 by (rule zenon_notimply_0 [OF z_Hoq])
 have z_Hou: "(~?z_hot)" (is "~(?z_hku|?z_hov)")
 by (rule zenon_notimply_1 [OF z_Hoq])
 have z_Hkt: "(~?z_hku)"
 by (rule zenon_notor_0 [OF z_Hou])
 have z_How: "(~?z_hov)" (is "~~?z_hox")
 by (rule zenon_notor_1 [OF z_Hou])
 have z_Hox: "?z_hox"
 by (rule zenon_notnot_0 [OF z_How])
 have z_Hoy: "(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))), (CHOOSE x:(~((x \\in Node)=>(?z_hku|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))), x>> \\in a_voteunde_msghash_primea))))))>> \\in a_voteunde_msga)" (is "?z_hoy")
 by (rule subst [where P="(\<lambda>zenon_Vec. (<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))), (CHOOSE x:(~((x \\in Node)=>(?z_hku|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))), x>> \\in a_voteunde_msghash_primea))))))>> \\in zenon_Vec))", OF z_Hhc z_Hox])
 have z_Hpd: "?z_hls((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))" (is "_=>?z_hpe")
 by (rule zenon_all_0 [of "?z_hls" "(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea))))))))", OF z_Hlk])
 show FALSE
 proof (rule zenon_imply [OF z_Hpd])
  assume z_Hpf:"(~?z_hoc)"
  show FALSE
  by (rule notE [OF z_Hpf z_Hoc])
 next
  assume z_Hpe:"?z_hpe"
  have z_Hpg_z_Hpe: "(\\A x:((x \\in Node)=>((voted[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea))))))))])|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))), x>> \\in a_voteunde_msga))))) == ?z_hpe" (is "?z_hpg == _")
  by (unfold bAll_def)
  have z_Hpg: "?z_hpg" (is "\\A x : ?z_hpl(x)")
  by (unfold z_Hpg_z_Hpe, fact z_Hpe)
  have z_Hpm: "?z_hpl((CHOOSE x:(~((x \\in Node)=>(?z_hku|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))), x>> \\in a_voteunde_msghash_primea)))))))" (is "_=>?z_hpn")
  by (rule zenon_all_0 [of "?z_hpl" "(CHOOSE x:(~((x \\in Node)=>(?z_hku|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))), x>> \\in a_voteunde_msghash_primea))))))", OF z_Hpg])
  show FALSE
  proof (rule zenon_imply [OF z_Hpm])
   assume z_Hpo:"(~?z_hos)"
   show FALSE
   by (rule notE [OF z_Hpo z_Hos])
  next
   assume z_Hpn:"?z_hpn" (is "?z_hkg|?z_hpp")
   show FALSE
   proof (rule zenon_or [OF z_Hpn])
    assume z_Hkg:"?z_hkg"
    have z_Hpq: "(\\A zenon_Vea:((zenon_Vea \\in Node)=>((voted[zenon_Vea]) \\in {TRUE, FALSE})))" (is "\\A x : ?z_hpw(x)")
    by (rule zenon_in_funcset_2 [of "voted" "Node" "{TRUE, FALSE}", OF z_Hl])
    have z_Hpx: "?z_hpw((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))" (is "_=>?z_hpy")
    by (rule zenon_all_0 [of "?z_hpw" "(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea))))))))", OF z_Hpq])
    show FALSE
    proof (rule zenon_imply [OF z_Hpx])
     assume z_Hpf:"(~?z_hoc)"
     show FALSE
     by (rule notE [OF z_Hpf z_Hoc])
    next
     assume z_Hpy:"?z_hpy"
     show FALSE
     proof (rule zenon_in_addElt [of "?z_hkg" "TRUE" "{FALSE}", OF z_Hpy])
      assume z_Hkf:"(?z_hkg=TRUE)" (is "_=?z_hp")
      show FALSE
      by (rule zenon_L1_ [OF z_Hkf z_Hkt z_Hhe])
     next
      assume z_Hqa:"(?z_hkg \\in {FALSE})" (is "?z_hqa")
      show FALSE
      proof (rule zenon_in_addElt [of "?z_hkg" "FALSE" "{}", OF z_Hqa])
       assume z_Hqc:"(?z_hkg=FALSE)" (is "_=?z_hq")
       have z_Hqd: "(~?z_hkg)"
       by (rule zenon_eq_x_false_0 [of "?z_hkg", OF z_Hqc])
       show FALSE
       by (rule notE [OF z_Hqd z_Hkg])
      next
       assume z_Hqe:"(?z_hkg \\in {})" (is "?z_hqe")
       show FALSE
       by (rule zenon_in_emptyset [of "?z_hkg", OF z_Hqe])
      qed
     qed
    qed
   next
    assume z_Hpp:"?z_hpp"
    show FALSE
    by (rule notE [OF z_Hpp z_Hoy])
   qed
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 161"; *} qed
lemma ob'159:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
fixes Node
fixes Quorum
fixes Value
fixes a_voteunde_requestunde_msga a_voteunde_requestunde_msga'
fixes voted voted'
fixes a_voteunde_msga a_voteunde_msga'
fixes votes votes'
fixes leader leader'
fixes decided decided'
fixes a_requnde_historya a_requnde_historya'
(* usable definition vars suppressed *)
(* usable definition Spec suppressed *)
(* usable definition Symmetry suppressed *)
(* usable definition Safety suppressed *)
(* usable definition SplitVote suppressed *)
(* usable definition Liveness suppressed *)
assumes v'26: "(((((((a_voteunde_requestunde_msga) \<in> ((SUBSET (((Node) \<times> (Node))))))) & (((voted) \<in> ([(Node) \<rightarrow> (BOOLEAN)]))) & (((a_voteunde_msga) \<in> ((SUBSET (((Node) \<times> (Node))))))) & (((votes) \<in> ([(Node) \<rightarrow> ((SUBSET (Node)))]))) & (((leader) \<in> ([(Node) \<rightarrow> (BOOLEAN)]))) & (((decided) \<in> ([(Node) \<rightarrow> ((SUBSET (Value)))])))) & (\<forall> a_n1a \<in> (Node) : (\<forall> a_n2a \<in> (Node) : (\<forall> a_v1a \<in> (Value) : (\<forall> a_v2a \<in> (Value) : (((((((a_v1a) \<in> (fapply ((decided), (a_n1a))))) \<and> (((a_v2a) \<in> (fapply ((decided), (a_n2a))))))) \<Rightarrow> (((a_v1a) = (a_v2a))))))))) & (\<forall> VARI \<in> (Node) : (\<forall> VARJ \<in> (Node) : (((((<<(VARJ), (VARI)>>) \<in> (a_voteunde_msga))) \<or> ((~ (((VARJ) \<in> (fapply ((votes), (VARI))))))))))) & (\<forall> VARI \<in> (Node) : (\<exists> QJ \<in> (Quorum) : (\<forall> VALI \<in> (Value) : (((((QJ) \<subseteq> (fapply ((votes), (VARI))))) \<or> ((~ (((VALI) \<in> (fapply ((decided), (VARI)))))))))))) & (\<forall> VARI \<in> (Node) : (\<forall> VARJ \<in> (Node) : (((fapply ((voted), (VARI))) \<or> ((~ (((<<(VARI), (VARJ)>>) \<in> (a_voteunde_msga))))))))) & (\<forall> VARI \<in> (Node) : (\<exists> QJ \<in> (Quorum) : (((((QJ) \<subseteq> (fapply ((votes), (VARI))))) \<or> ((~ (fapply ((leader), (VARI))))))))) & (\<forall> VARI \<in> (Node) : (\<forall> VALI \<in> (Value) : (((fapply ((leader), (VARI))) \<or> ((~ (((VALI) \<in> (fapply ((decided), (VARI))))))))))) & (\<forall> VARI \<in> (Node) : (\<forall> VARJ \<in> (Node) : (\<forall> VARK \<in> (Node) : (((((((((VARI) = (VARK))) \<and> (((votes) = (votes))))) \<or> ((~ (((<<(VARJ), (VARI)>>) \<in> (a_voteunde_msga))))))) \<or> ((~ (((VARJ) \<in> (fapply ((votes), (VARK)))))))))))) & (\<forall> VARI \<in> (Node) : (\<forall> VARJ \<in> (Node) : (\<forall> VARK \<in> (Node) : (((((((((VARJ) = (VARK))) \<and> (((votes) = (votes))))) \<or> ((~ (((<<(VARI), (VARK)>>) \<in> (a_voteunde_msga))))))) \<or> ((~ (((<<(VARI), (VARJ)>>) \<in> (a_voteunde_msga))))))))))) \<and> ((((\<exists> i \<in> (Node) : (\<exists> j \<in> (Node) : (((~ (fapply ((voted), (i))))) & (((<<(j), (i)>>) \<in> (a_voteunde_requestunde_msga))) & ((((a_voteunde_requestunde_msghash_primea :: c)) = (((a_voteunde_requestunde_msga) \\ ({(<<(j), (i)>>)}))))) & ((((a_voteunde_msghash_primea :: c)) = (((a_voteunde_msga) \<union> ({(<<(i), (j)>>)}))))) & ((((a_votedhash_primea :: c)) = ([(voted) EXCEPT ![(i)] = (TRUE)]))) & ((((a_voteshash_primea :: c)) = (votes))) & ((((a_decidedhash_primea :: c)) = (decided))) & ((((a_leaderhash_primea :: c)) = (leader))) & ((((a_requnde_historyhash_primea :: c)) = (a_requnde_historya)))))) | (\<exists> i \<in> (Node) : (\<exists> j \<in> (Node) : ((fapply ((voted), (i))) & ((((a_voteunde_requestunde_msghash_primea :: c)) = (((a_voteunde_requestunde_msga) \\ ({(<<(j), (i)>>)}))))) & ((((a_voteunde_msghash_primea :: c)) = (a_voteunde_msga))) & ((((a_votedhash_primea :: c)) = (voted))) & ((((a_voteshash_primea :: c)) = (votes))) & ((((a_decidedhash_primea :: c)) = (decided))) & ((((a_leaderhash_primea :: c)) = (leader))) & ((((a_requnde_historyhash_primea :: c)) = (a_requnde_historya)))))) | (\<exists> i \<in> (Node) : (\<exists> j \<in> (Node) : ((((<<(j), (i)>>) \<in> (a_voteunde_msga))) & ((((a_voteshash_primea :: c)) = ([(votes) EXCEPT ![(i)] = (((fapply ((votes), (i))) \<union> ({(j)})))]))) & ((((a_votedhash_primea :: c)) = (voted))) & ((((a_voteunde_msghash_primea :: c)) = (a_voteunde_msga))) & ((((a_leaderhash_primea :: c)) = (leader))) & ((((a_decidedhash_primea :: c)) = (decided))) & ((((a_voteunde_requestunde_msghash_primea :: c)) = (a_voteunde_requestunde_msga))) & ((((a_requnde_historyhash_primea :: c)) = (a_requnde_historya)))))) | (\<exists> i \<in> (Node) : (\<exists> Q \<in> (Quorum) : ((((Q) \<subseteq> (fapply ((votes), (i))))) & ((((a_leaderhash_primea :: c)) = ([(leader) EXCEPT ![(i)] = (TRUE)]))) & ((((a_voteshash_primea :: c)) = (votes))) & ((((a_votedhash_primea :: c)) = (voted))) & ((((a_voteunde_msghash_primea :: c)) = (a_voteunde_msga))) & ((((a_decidedhash_primea :: c)) = (decided))) & ((((a_voteunde_requestunde_msghash_primea :: c)) = (a_voteunde_requestunde_msga))) & ((((a_requnde_historyhash_primea :: c)) = (a_requnde_historya)))))) | (\<exists> i \<in> (Node) : (\<exists> j \<in> (Node) : (\<exists> v \<in> (Value) : ((fapply ((leader), (i))) & ((({}) = (fapply ((decided), (i))))) & ((((a_decidedhash_primea :: c)) = ([(decided) EXCEPT ![(i)] = (((fapply ((decided), (i))) \<union> ({(v)})))]))) & ((((a_voteshash_primea :: c)) = (votes))) & ((((a_votedhash_primea :: c)) = (voted))) & ((((a_voteunde_msghash_primea :: c)) = (a_voteunde_msga))) & ((((a_leaderhash_primea :: c)) = (leader))) & ((((a_voteunde_requestunde_msghash_primea :: c)) = (a_voteunde_requestunde_msga))) & ((((a_requnde_historyhash_primea :: c)) = (a_requnde_historya)))))))) \<or> (\<exists> i \<in> (Node) : (\<exists> j \<in> (Node) : ((((<<(i), (j)>>) \<notin> (a_requnde_historya))) & (\<forall> a_dst2a \<in> (Node) : (((<<(i), (a_dst2a)>>) \<notin> (a_voteunde_requestunde_msga)))) & ((((a_voteunde_requestunde_msghash_primea :: c)) = (((a_voteunde_requestunde_msga) \<union> ({(<<(i), (j)>>)}))))) & ((((a_requnde_historyhash_primea :: c)) = (((a_requnde_historya) \<union> ({(<<(i), (j)>>)}))))) & (((((a_votedhash_primea :: c)) = (voted))) & ((((a_voteunde_msghash_primea :: c)) = (a_voteunde_msga))) & ((((a_voteshash_primea :: c)) = (votes))) & ((((a_leaderhash_primea :: c)) = (leader))) & ((((a_decidedhash_primea :: c)) = (decided)))))))))))"
assumes v'41: "(\<exists> i \<in> (Node) : (\<exists> Q \<in> (Quorum) : ((((Q) \<subseteq> (fapply ((votes), (i))))) & ((((a_leaderhash_primea :: c)) = ([(leader) EXCEPT ![(i)] = (TRUE)]))) & ((((a_voteshash_primea :: c)) = (votes))) & ((((a_votedhash_primea :: c)) = (voted))) & ((((a_voteunde_msghash_primea :: c)) = (a_voteunde_msga))) & ((((a_decidedhash_primea :: c)) = (decided))) & ((((a_voteunde_requestunde_msghash_primea :: c)) = (a_voteunde_requestunde_msga))) & ((((a_requnde_historyhash_primea :: c)) = (a_requnde_historya))))))"
shows "(\<forall> VARI \<in> (Node) : (\<forall> VARJ \<in> (Node) : (((fapply (((a_votedhash_primea :: c)), (VARI))) \<or> ((~ (((<<(VARI), (VARJ)>>) \<in> ((a_voteunde_msghash_primea :: c))))))))))"(is "PROP ?ob'159")
proof -
ML_command {* writeln "*** TLAPS ENTER 159"; *}
show "PROP ?ob'159"

(* BEGIN ZENON INPUT
;; file=consensus_epr_IndProofs.tlaps/tlapm_26c067.znn; PATH='/home/egolf/.opam/4.07.1/bin:/home/egolf/.local/bin:/home/egolf/bin:/home/egolf/mambaforge/bin:/home/egolf/mambaforge/condabin:/home/egolf/.opam/4.07.1/bin:/home/egolf/.local/bin:/home/egolf/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/home/egolf/.local/bin/gurobi952/linux64/bin:/home/egolf/Projects/apalache/bin:/home/egolf/opt/foxitsoftware/foxitreader:/home/egolf/.local/bin/gurobi952/linux64/bin:/home/egolf/Projects/apalache/bin:/home/egolf/opt/foxitsoftware/foxitreader:/usr/local/bin:/usr/local/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >consensus_epr_IndProofs.tlaps/tlapm_26c067.znn.out
;; obligation #159
$hyp "v'26" (/\ (/\ (/\ (TLA.in a_voteunde_requestunde_msga
(TLA.SUBSET (TLA.prod Node Node))) (TLA.in voted
(TLA.FuncSet Node (TLA.set T. F.))) (TLA.in a_voteunde_msga
(TLA.SUBSET (TLA.prod Node Node))) (TLA.in votes
(TLA.FuncSet Node (TLA.SUBSET Node))) (TLA.in leader
(TLA.FuncSet Node (TLA.set T. F.))) (TLA.in decided
(TLA.FuncSet Node (TLA.SUBSET Value))))
(TLA.bAll Node ((a_n1a) (TLA.bAll Node ((a_n2a) (TLA.bAll Value ((a_v1a) (TLA.bAll Value ((a_v2a) (=> (/\ (TLA.in a_v1a
(TLA.fapply decided a_n1a)) (TLA.in a_v2a (TLA.fapply decided a_n2a)))
(= a_v1a a_v2a))))))))))
(TLA.bAll Node ((VARI) (TLA.bAll Node ((VARJ) (\/ (TLA.in (TLA.tuple VARJ
VARI) a_voteunde_msga) (-. (TLA.in VARJ (TLA.fapply votes VARI))))))))
(TLA.bAll Node ((VARI) (TLA.bEx Quorum ((QJ) (TLA.bAll Value ((VALI) (\/ (TLA.subseteq QJ
(TLA.fapply votes VARI)) (-. (TLA.in VALI (TLA.fapply decided VARI))))))))))
(TLA.bAll Node ((VARI) (TLA.bAll Node ((VARJ) (\/ (TLA.fapply voted VARI)
(-. (TLA.in (TLA.tuple VARI VARJ) a_voteunde_msga)))))))
(TLA.bAll Node ((VARI) (TLA.bEx Quorum ((QJ) (\/ (TLA.subseteq QJ
(TLA.fapply votes VARI)) (-. (TLA.fapply leader VARI)))))))
(TLA.bAll Node ((VARI) (TLA.bAll Value ((VALI) (\/ (TLA.fapply leader VARI)
(-. (TLA.in VALI (TLA.fapply decided VARI))))))))
(TLA.bAll Node ((VARI) (TLA.bAll Node ((VARJ) (TLA.bAll Node ((VARK) (\/ (\/ (/\ (= VARI
VARK) (= votes votes)) (-. (TLA.in (TLA.tuple VARJ VARI) a_voteunde_msga)))
(-. (TLA.in VARJ (TLA.fapply votes VARK))))))))))
(TLA.bAll Node ((VARI) (TLA.bAll Node ((VARJ) (TLA.bAll Node ((VARK) (\/ (\/ (/\ (= VARJ
VARK) (= votes votes)) (-. (TLA.in (TLA.tuple VARI VARK) a_voteunde_msga)))
(-. (TLA.in (TLA.tuple VARI VARJ) a_voteunde_msga))))))))))
(\/ (\/ (TLA.bEx Node ((i) (TLA.bEx Node ((j) (/\ (-. (TLA.fapply voted i))
(TLA.in (TLA.tuple j i) a_voteunde_requestunde_msga)
(= a_voteunde_requestunde_msghash_primea
(TLA.setminus a_voteunde_requestunde_msga (TLA.set (TLA.tuple j i))))
(= a_voteunde_msghash_primea (TLA.cup a_voteunde_msga (TLA.set (TLA.tuple i
j)))) (= a_votedhash_primea (TLA.except voted i T.)) (= a_voteshash_primea
votes) (= a_decidedhash_primea decided) (= a_leaderhash_primea leader)
(= a_requnde_historyhash_primea a_requnde_historya))))))
(TLA.bEx Node ((i) (TLA.bEx Node ((j) (/\ (TLA.fapply voted i)
(= a_voteunde_requestunde_msghash_primea
(TLA.setminus a_voteunde_requestunde_msga (TLA.set (TLA.tuple j i))))
(= a_voteunde_msghash_primea a_voteunde_msga) (= a_votedhash_primea voted)
(= a_voteshash_primea votes) (= a_decidedhash_primea decided)
(= a_leaderhash_primea leader) (= a_requnde_historyhash_primea
a_requnde_historya))))))
(TLA.bEx Node ((i) (TLA.bEx Node ((j) (/\ (TLA.in (TLA.tuple j i)
a_voteunde_msga) (= a_voteshash_primea
(TLA.except votes i (TLA.cup (TLA.fapply votes i) (TLA.set j))))
(= a_votedhash_primea voted) (= a_voteunde_msghash_primea a_voteunde_msga)
(= a_leaderhash_primea leader) (= a_decidedhash_primea decided)
(= a_voteunde_requestunde_msghash_primea a_voteunde_requestunde_msga)
(= a_requnde_historyhash_primea a_requnde_historya))))))
(TLA.bEx Node ((i) (TLA.bEx Quorum ((Q) (/\ (TLA.subseteq Q
(TLA.fapply votes i)) (= a_leaderhash_primea (TLA.except leader i T.))
(= a_voteshash_primea votes) (= a_votedhash_primea voted)
(= a_voteunde_msghash_primea a_voteunde_msga) (= a_decidedhash_primea
decided) (= a_voteunde_requestunde_msghash_primea
a_voteunde_requestunde_msga) (= a_requnde_historyhash_primea
a_requnde_historya))))))
(TLA.bEx Node ((i) (TLA.bEx Node ((j) (TLA.bEx Value ((v) (/\ (TLA.fapply leader i)
(= TLA.emptyset (TLA.fapply decided i)) (= a_decidedhash_primea
(TLA.except decided i (TLA.cup (TLA.fapply decided i) (TLA.set v))))
(= a_voteshash_primea votes) (= a_votedhash_primea voted)
(= a_voteunde_msghash_primea a_voteunde_msga) (= a_leaderhash_primea leader)
(= a_voteunde_requestunde_msghash_primea a_voteunde_requestunde_msga)
(= a_requnde_historyhash_primea a_requnde_historya)))))))))
(TLA.bEx Node ((i) (TLA.bEx Node ((j) (/\ (-. (TLA.in (TLA.tuple i j)
a_requnde_historya)) (TLA.bAll Node ((a_dst2a) (-. (TLA.in (TLA.tuple i
a_dst2a) a_voteunde_requestunde_msga))))
(= a_voteunde_requestunde_msghash_primea (TLA.cup a_voteunde_requestunde_msga
(TLA.set (TLA.tuple i j)))) (= a_requnde_historyhash_primea
(TLA.cup a_requnde_historya (TLA.set (TLA.tuple i j))))
(/\ (= a_votedhash_primea voted) (= a_voteunde_msghash_primea
a_voteunde_msga) (= a_voteshash_primea votes) (= a_leaderhash_primea leader)
(= a_decidedhash_primea
decided)))))))))
$hyp "v'41" (TLA.bEx Node ((i) (TLA.bEx Quorum ((Q) (/\ (TLA.subseteq Q
(TLA.fapply votes i)) (= a_leaderhash_primea (TLA.except leader i T.))
(= a_voteshash_primea votes) (= a_votedhash_primea voted)
(= a_voteunde_msghash_primea a_voteunde_msga) (= a_decidedhash_primea
decided) (= a_voteunde_requestunde_msghash_primea
a_voteunde_requestunde_msga) (= a_requnde_historyhash_primea
a_requnde_historya))))))
$goal (TLA.bAll Node ((VARI) (TLA.bAll Node ((VARJ) (\/ (TLA.fapply a_votedhash_primea VARI)
(-. (TLA.in (TLA.tuple VARI VARJ)
a_voteunde_msghash_primea)))))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Ha:"((((a_voteunde_requestunde_msga \\in SUBSET(prod(Node, Node)))&((voted \\in FuncSet(Node, {TRUE, FALSE}))&((a_voteunde_msga \\in SUBSET(prod(Node, Node)))&((votes \\in FuncSet(Node, SUBSET(Node)))&((leader \\in FuncSet(Node, {TRUE, FALSE}))&(decided \\in FuncSet(Node, SUBSET(Value))))))))&(bAll(Node, (\<lambda>a_n1a. bAll(Node, (\<lambda>a_n2a. bAll(Value, (\<lambda>a_v1a. bAll(Value, (\<lambda>a_v2a. (((a_v1a \\in (decided[a_n1a]))&(a_v2a \\in (decided[a_n2a])))=>(a_v1a=a_v2a))))))))))&(bAll(Node, (\<lambda>VARI. bAll(Node, (\<lambda>VARJ. ((<<VARJ, VARI>> \\in a_voteunde_msga)|(~(VARJ \\in (votes[VARI]))))))))&(bAll(Node, (\<lambda>VARI. bEx(Quorum, (\<lambda>QJ. bAll(Value, (\<lambda>VALI. ((QJ \\subseteq (votes[VARI]))|(~(VALI \\in (decided[VARI]))))))))))&(bAll(Node, (\<lambda>VARI. bAll(Node, (\<lambda>VARJ. ((voted[VARI])|(~(<<VARI, VARJ>> \\in a_voteunde_msga)))))))&(bAll(Node, (\<lambda>VARI. bEx(Quorum, (\<lambda>QJ. ((QJ \\subseteq (votes[VARI]))|(~(leader[VARI])))))))&(bAll(Node, (\<lambda>VARI. bAll(Value, (\<lambda>VALI. ((leader[VARI])|(~(VALI \\in (decided[VARI]))))))))&(bAll(Node, (\<lambda>VARI. bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARI=VARK)&(votes=votes))|(~(<<VARJ, VARI>> \\in a_voteunde_msga)))|(~(VARJ \\in (votes[VARK]))))))))))&bAll(Node, (\<lambda>VARI. bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(votes=votes))|(~(<<VARI, VARK>> \\in a_voteunde_msga)))|(~(<<VARI, VARJ>> \\in a_voteunde_msga)))))))))))))))))&((bEx(Node, (\<lambda>i. bEx(Node, (\<lambda>j. ((~(voted[i]))&((<<j, i>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, i>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<i, j>>}))&((a_votedhash_primea=except(voted, i, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))|(bEx(Node, (\<lambda>i. bEx(Node, (\<lambda>j. ((voted[i])&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, i>>}))&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_votedhash_primea=voted)&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))|(bEx(Node, (\<lambda>i. bEx(Node, (\<lambda>j. ((<<j, i>> \\in a_voteunde_msga)&((a_voteshash_primea=except(votes, i, ((votes[i]) \\cup {j})))&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_decidedhash_primea=decided)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))|(bEx(Node, (\<lambda>i. bEx(Quorum, (\<lambda>Q. ((Q \\subseteq (votes[i]))&((a_leaderhash_primea=except(leader, i, TRUE))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_decidedhash_primea=decided)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))|bEx(Node, (\<lambda>i. bEx(Node, (\<lambda>j. bEx(Value, (\<lambda>v. ((leader[i])&(({}=(decided[i]))&((a_decidedhash_primea=except(decided, i, ((decided[i]) \\cup {v})))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))))))))|bEx(Node, (\<lambda>i. bEx(Node, (\<lambda>j. ((~(<<i, j>> \\in a_requnde_historya))&(bAll(Node, (\<lambda>a_dst2a. (~(<<i, a_dst2a>> \\in a_voteunde_requestunde_msga))))&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\cup {<<i, j>>}))&((a_requnde_historyhash_primea=(a_requnde_historya \\cup {<<i, j>>}))&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_voteshash_primea=votes)&((a_leaderhash_primea=leader)&(a_decidedhash_primea=decided)))))))))))))))" (is "?z_hd&?z_hff")
 using v'26 by blast
 have z_Hb:"bEx(Node, (\<lambda>i. bEx(Quorum, (\<lambda>Q. ((Q \\subseteq (votes[i]))&((a_leaderhash_primea=except(leader, i, TRUE))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_decidedhash_primea=decided)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))" (is "?z_hb")
 using v'41 by blast
 have zenon_L1_: "((voted[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea))))))))])=TRUE) ==> (~(a_votedhash_primea[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea))))))))])) ==> (a_votedhash_primea=voted) ==> FALSE" (is "?z_hkf ==> ?z_hkt ==> ?z_hhe ==> FALSE")
 proof -
  assume z_Hkf:"?z_hkf" (is "?z_hkg=?z_hp")
  assume z_Hkt:"?z_hkt" (is "~?z_hku")
  assume z_Hhe:"?z_hhe"
  show FALSE
  proof (rule zenon_np_eq_l [of "?z_hku" "?z_hkg" "?z_hp", OF z_Hkt z_Hkf])
   assume z_Hkv:"(?z_hku~=?z_hkg)"
   show FALSE
   proof (rule zenon_noteq [of "?z_hkg"])
    have z_Hkw: "(?z_hkg~=?z_hkg)"
    by (rule subst [where P="(\<lambda>zenon_Vvsa. ((zenon_Vvsa[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea))))))))])~=?z_hkg))", OF z_Hhe], fact z_Hkv)
    thus "(?z_hkg~=?z_hkg)" .
   qed
  next
   assume z_Hlb:"(~?z_hp)"
   show FALSE
   by (rule zenon_nottrue [OF z_Hlb])
  qed
 qed
 assume z_Hc:"(~bAll(Node, (\<lambda>VARI. bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[VARI])|(~(<<VARI, VARJ>> \\in a_voteunde_msghash_primea))))))))" (is "~?z_hlc")
 have z_Hd: "?z_hd" (is "?z_he&?z_hbh")
 by (rule zenon_and_0 [OF z_Ha])
 have z_He: "?z_he" (is "?z_hf&?z_hk")
 by (rule zenon_and_0 [OF z_Hd])
 have z_Hbh: "?z_hbh" (is "?z_hbi&?z_hcb")
 by (rule zenon_and_1 [OF z_Hd])
 have z_Hcb: "?z_hcb" (is "?z_hcc&?z_hco")
 by (rule zenon_and_1 [OF z_Hbh])
 have z_Hco: "?z_hco" (is "?z_hcp&?z_hdd")
 by (rule zenon_and_1 [OF z_Hcb])
 have z_Hdd: "?z_hdd" (is "?z_hde&?z_hdn")
 by (rule zenon_and_1 [OF z_Hco])
 have z_Hde: "?z_hde"
 by (rule zenon_and_0 [OF z_Hdd])
 have z_Hk: "?z_hk" (is "?z_hl&?z_hr")
 by (rule zenon_and_1 [OF z_He])
 have z_Hl: "?z_hl"
 by (rule zenon_and_0 [OF z_Hk])
 have z_Hlk_z_Hde: "(\\A x:((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((voted[x])|(~(<<x, VARJ>> \\in a_voteunde_msga))))))) == ?z_hde" (is "?z_hlk == _")
 by (unfold bAll_def)
 have z_Hlk: "?z_hlk" (is "\\A x : ?z_hls(x)")
 by (unfold z_Hlk_z_Hde, fact z_Hde)
 have z_Hlt_z_Hb: "(\\E x:((x \\in Node)&bEx(Quorum, (\<lambda>Q. ((Q \\subseteq (votes[x]))&((a_leaderhash_primea=except(leader, x, TRUE))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_decidedhash_primea=decided)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))) == ?z_hb" (is "?z_hlt == _")
 by (unfold bEx_def)
 have z_Hlt: "?z_hlt" (is "\\E x : ?z_hmd(x)")
 by (unfold z_Hlt_z_Hb, fact z_Hb)
 have z_Hme: "?z_hmd((CHOOSE x:((x \\in Node)&bEx(Quorum, (\<lambda>Q. ((Q \\subseteq (votes[x]))&((a_leaderhash_primea=except(leader, x, TRUE))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_decidedhash_primea=decided)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))" (is "?z_hmg&?z_hmh")
 by (rule zenon_ex_choose_0 [of "?z_hmd", OF z_Hlt])
 have z_Hmh: "?z_hmh"
 by (rule zenon_and_1 [OF z_Hme])
 have z_Hmi_z_Hmh: "(\\E x:((x \\in Quorum)&((x \\subseteq (votes[(CHOOSE x:((x \\in Node)&bEx(Quorum, (\<lambda>Q. ((Q \\subseteq (votes[x]))&((a_leaderhash_primea=except(leader, x, TRUE))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_decidedhash_primea=decided)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))]))&((a_leaderhash_primea=except(leader, (CHOOSE x:((x \\in Node)&bEx(Quorum, (\<lambda>Q. ((Q \\subseteq (votes[x]))&((a_leaderhash_primea=except(leader, x, TRUE))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_decidedhash_primea=decided)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))), TRUE))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_decidedhash_primea=decided)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))) == ?z_hmh" (is "?z_hmi == _")
 by (unfold bEx_def)
 have z_Hmi: "?z_hmi" (is "\\E x : ?z_hmr(x)")
 by (unfold z_Hmi_z_Hmh, fact z_Hmh)
 have z_Hms: "?z_hmr((CHOOSE x:((x \\in Quorum)&((x \\subseteq (votes[(CHOOSE x:((x \\in Node)&bEx(Quorum, (\<lambda>Q. ((Q \\subseteq (votes[x]))&((a_leaderhash_primea=except(leader, x, TRUE))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_decidedhash_primea=decided)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))]))&((a_leaderhash_primea=except(leader, (CHOOSE x:((x \\in Node)&bEx(Quorum, (\<lambda>Q. ((Q \\subseteq (votes[x]))&((a_leaderhash_primea=except(leader, x, TRUE))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_decidedhash_primea=decided)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))), TRUE))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_decidedhash_primea=decided)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))" (is "?z_hmu&?z_hmv")
 by (rule zenon_ex_choose_0 [of "?z_hmr", OF z_Hmi])
 have z_Hmv: "?z_hmv" (is "?z_hmw&?z_hmo")
 by (rule zenon_and_1 [OF z_Hms])
 have z_Hmo: "?z_hmo" (is "?z_hmp&?z_hii")
 by (rule zenon_and_1 [OF z_Hmv])
 have z_Hii: "?z_hii" (is "?z_hgj&?z_hij")
 by (rule zenon_and_1 [OF z_Hmo])
 have z_Hij: "?z_hij" (is "?z_hhe&?z_hik")
 by (rule zenon_and_1 [OF z_Hii])
 have z_Hhe: "?z_hhe"
 by (rule zenon_and_0 [OF z_Hij])
 have z_Hik: "?z_hik" (is "?z_hhc&?z_hhv")
 by (rule zenon_and_1 [OF z_Hij])
 have z_Hhc: "?z_hhc"
 by (rule zenon_and_0 [OF z_Hik])
 have z_Hmx_z_Hc: "(~(\\A x:((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))) == (~?z_hlc)" (is "?z_hmx == ?z_hc")
 by (unfold bAll_def)
 have z_Hmx: "?z_hmx" (is "~(\\A x : ?z_hmz(x))")
 by (unfold z_Hmx_z_Hc, fact z_Hc)
 have z_Hna: "(\\E x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea))))))))" (is "\\E x : ?z_hnb(x)")
 by (rule zenon_notallex_0 [of "?z_hmz", OF z_Hmx])
 have z_Hnc: "?z_hnb((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))" (is "~(?z_hnd=>?z_hne)")
 by (rule zenon_ex_choose_0 [of "?z_hnb", OF z_Hna])
 have z_Hnd: "?z_hnd"
 by (rule zenon_notimply_0 [OF z_Hnc])
 have z_Hnf: "(~?z_hne)"
 by (rule zenon_notimply_1 [OF z_Hnc])
 have z_Hng_z_Hnf: "(~(\\A x:((x \\in Node)=>((a_votedhash_primea[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea))))))))])|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))), x>> \\in a_voteunde_msghash_primea)))))) == (~?z_hne)" (is "?z_hng == ?z_hnf")
 by (unfold bAll_def)
 have z_Hng: "?z_hng" (is "~(\\A x : ?z_hnn(x))")
 by (unfold z_Hng_z_Hnf, fact z_Hnf)
 have z_Hno: "(\\E x:(~((x \\in Node)=>((a_votedhash_primea[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea))))))))])|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))), x>> \\in a_voteunde_msghash_primea))))))" (is "\\E x : ?z_hnq(x)")
 by (rule zenon_notallex_0 [of "?z_hnn", OF z_Hng])
 have z_Hnr: "?z_hnq((CHOOSE x:(~((x \\in Node)=>((a_votedhash_primea[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea))))))))])|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))), x>> \\in a_voteunde_msghash_primea)))))))" (is "~(?z_hnt=>?z_hnu)")
 by (rule zenon_ex_choose_0 [of "?z_hnq", OF z_Hno])
 have z_Hnt: "?z_hnt"
 by (rule zenon_notimply_0 [OF z_Hnr])
 have z_Hnv: "(~?z_hnu)" (is "~(?z_hku|?z_hnw)")
 by (rule zenon_notimply_1 [OF z_Hnr])
 have z_Hkt: "(~?z_hku)"
 by (rule zenon_notor_0 [OF z_Hnv])
 have z_Hnx: "(~?z_hnw)" (is "~~?z_hny")
 by (rule zenon_notor_1 [OF z_Hnv])
 have z_Hny: "?z_hny"
 by (rule zenon_notnot_0 [OF z_Hnx])
 have z_Hnz: "(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))), (CHOOSE x:(~((x \\in Node)=>(?z_hku|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))), x>> \\in a_voteunde_msghash_primea))))))>> \\in a_voteunde_msga)" (is "?z_hnz")
 by (rule subst [where P="(\<lambda>zenon_Vzb. (<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))), (CHOOSE x:(~((x \\in Node)=>(?z_hku|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))), x>> \\in a_voteunde_msghash_primea))))))>> \\in zenon_Vzb))", OF z_Hhc z_Hny])
 have z_Hoe: "?z_hls((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))" (is "_=>?z_hof")
 by (rule zenon_all_0 [of "?z_hls" "(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea))))))))", OF z_Hlk])
 show FALSE
 proof (rule zenon_imply [OF z_Hoe])
  assume z_Hog:"(~?z_hnd)"
  show FALSE
  by (rule notE [OF z_Hog z_Hnd])
 next
  assume z_Hof:"?z_hof"
  have z_Hoh_z_Hof: "(\\A x:((x \\in Node)=>((voted[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea))))))))])|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))), x>> \\in a_voteunde_msga))))) == ?z_hof" (is "?z_hoh == _")
  by (unfold bAll_def)
  have z_Hoh: "?z_hoh" (is "\\A x : ?z_hom(x)")
  by (unfold z_Hoh_z_Hof, fact z_Hof)
  have z_Hon: "?z_hom((CHOOSE x:(~((x \\in Node)=>(?z_hku|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))), x>> \\in a_voteunde_msghash_primea)))))))" (is "_=>?z_hoo")
  by (rule zenon_all_0 [of "?z_hom" "(CHOOSE x:(~((x \\in Node)=>(?z_hku|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))), x>> \\in a_voteunde_msghash_primea))))))", OF z_Hoh])
  show FALSE
  proof (rule zenon_imply [OF z_Hon])
   assume z_Hop:"(~?z_hnt)"
   show FALSE
   by (rule notE [OF z_Hop z_Hnt])
  next
   assume z_Hoo:"?z_hoo" (is "?z_hkg|?z_hoq")
   show FALSE
   proof (rule zenon_or [OF z_Hoo])
    assume z_Hkg:"?z_hkg"
    have z_Hor: "(\\A zenon_Vea:((zenon_Vea \\in Node)=>((voted[zenon_Vea]) \\in {TRUE, FALSE})))" (is "\\A x : ?z_hox(x)")
    by (rule zenon_in_funcset_2 [of "voted" "Node" "{TRUE, FALSE}", OF z_Hl])
    have z_Hoy: "?z_hox((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))" (is "_=>?z_hoz")
    by (rule zenon_all_0 [of "?z_hox" "(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((a_votedhash_primea[x])|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea))))))))", OF z_Hor])
    show FALSE
    proof (rule zenon_imply [OF z_Hoy])
     assume z_Hog:"(~?z_hnd)"
     show FALSE
     by (rule notE [OF z_Hog z_Hnd])
    next
     assume z_Hoz:"?z_hoz"
     show FALSE
     proof (rule zenon_in_addElt [of "?z_hkg" "TRUE" "{FALSE}", OF z_Hoz])
      assume z_Hkf:"(?z_hkg=TRUE)" (is "_=?z_hp")
      show FALSE
      by (rule zenon_L1_ [OF z_Hkf z_Hkt z_Hhe])
     next
      assume z_Hpb:"(?z_hkg \\in {FALSE})" (is "?z_hpb")
      show FALSE
      proof (rule zenon_in_addElt [of "?z_hkg" "FALSE" "{}", OF z_Hpb])
       assume z_Hpd:"(?z_hkg=FALSE)" (is "_=?z_hq")
       have z_Hpe: "(~?z_hkg)"
       by (rule zenon_eq_x_false_0 [of "?z_hkg", OF z_Hpd])
       show FALSE
       by (rule notE [OF z_Hpe z_Hkg])
      next
       assume z_Hpf:"(?z_hkg \\in {})" (is "?z_hpf")
       show FALSE
       by (rule zenon_in_emptyset [of "?z_hkg", OF z_Hpf])
      qed
     qed
    qed
   next
    assume z_Hoq:"?z_hoq"
    show FALSE
    by (rule notE [OF z_Hoq z_Hnz])
   qed
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 159"; *} qed
lemma ob'214:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
fixes Node
fixes Quorum
fixes Value
fixes a_voteunde_requestunde_msga a_voteunde_requestunde_msga'
fixes voted voted'
fixes a_voteunde_msga a_voteunde_msga'
fixes votes votes'
fixes leader leader'
fixes decided decided'
fixes a_requnde_historya a_requnde_historya'
(* usable definition vars suppressed *)
(* usable definition IgnoreRequestVote suppressed *)
(* usable definition ProtocolNext suppressed *)
(* usable definition OtherNext suppressed *)
(* usable definition Spec suppressed *)
(* usable definition Symmetry suppressed *)
(* usable definition Safety suppressed *)
(* usable definition SplitVote suppressed *)
(* usable definition Liveness suppressed *)
assumes v'29: "(((((((a_voteunde_requestunde_msga) \<in> ((SUBSET (((Node) \<times> (Node))))))) & (((voted) \<in> ([(Node) \<rightarrow> (BOOLEAN)]))) & (((a_voteunde_msga) \<in> ((SUBSET (((Node) \<times> (Node))))))) & (((votes) \<in> ([(Node) \<rightarrow> ((SUBSET (Node)))]))) & (((leader) \<in> ([(Node) \<rightarrow> (BOOLEAN)]))) & (((decided) \<in> ([(Node) \<rightarrow> ((SUBSET (Value)))])))) & (\<forall> a_n1a \<in> (Node) : (\<forall> a_n2a \<in> (Node) : (\<forall> a_v1a \<in> (Value) : (\<forall> a_v2a \<in> (Value) : (((((((a_v1a) \<in> (fapply ((decided), (a_n1a))))) \<and> (((a_v2a) \<in> (fapply ((decided), (a_n2a))))))) \<Rightarrow> (((a_v1a) = (a_v2a))))))))) & (\<forall> VARI \<in> (Node) : (\<forall> VARJ \<in> (Node) : (((((<<(VARJ), (VARI)>>) \<in> (a_voteunde_msga))) \<or> ((~ (((VARJ) \<in> (fapply ((votes), (VARI))))))))))) & (\<forall> VARI \<in> (Node) : (\<exists> QJ \<in> (Quorum) : (\<forall> VALI \<in> (Value) : (((((QJ) \<subseteq> (fapply ((votes), (VARI))))) \<or> ((~ (((VALI) \<in> (fapply ((decided), (VARI)))))))))))) & (\<forall> VARI \<in> (Node) : (\<forall> VARJ \<in> (Node) : (((fapply ((voted), (VARI))) \<or> ((~ (((<<(VARI), (VARJ)>>) \<in> (a_voteunde_msga))))))))) & (\<forall> VARI \<in> (Node) : (\<exists> QJ \<in> (Quorum) : (((((QJ) \<subseteq> (fapply ((votes), (VARI))))) \<or> ((~ (fapply ((leader), (VARI))))))))) & (\<forall> VARI \<in> (Node) : (\<forall> VALI \<in> (Value) : (((fapply ((leader), (VARI))) \<or> ((~ (((VALI) \<in> (fapply ((decided), (VARI))))))))))) & (\<forall> VARI \<in> (Node) : (\<forall> VARJ \<in> (Node) : (\<forall> VARK \<in> (Node) : (((((((((VARI) = (VARK))) \<and> (((votes) = (votes))))) \<or> ((~ (((<<(VARJ), (VARI)>>) \<in> (a_voteunde_msga))))))) \<or> ((~ (((VARJ) \<in> (fapply ((votes), (VARK)))))))))))) & (\<forall> VARI \<in> (Node) : (\<forall> VARJ \<in> (Node) : (\<forall> VARK \<in> (Node) : (((((((((VARJ) = (VARK))) \<and> (((votes) = (votes))))) \<or> ((~ (((<<(VARI), (VARK)>>) \<in> (a_voteunde_msga))))))) \<or> ((~ (((<<(VARI), (VARJ)>>) \<in> (a_voteunde_msga))))))))))) \<and> (((ProtocolNext) \<or> (OtherNext)))))"
assumes v'46: "(\<exists> i \<in> (Node) : (\<exists> j \<in> (Node) : (((~ (fapply ((voted), (i))))) & (((<<(j), (i)>>) \<in> (a_voteunde_requestunde_msga))) & ((((a_voteunde_requestunde_msghash_primea :: c)) = (((a_voteunde_requestunde_msga) \\ ({(<<(j), (i)>>)}))))) & ((((a_voteunde_msghash_primea :: c)) = (((a_voteunde_msga) \<union> ({(<<(i), (j)>>)}))))) & ((((a_votedhash_primea :: c)) = ([(voted) EXCEPT ![(i)] = (TRUE)]))) & ((((a_voteshash_primea :: c)) = (votes))) & ((((a_decidedhash_primea :: c)) = (decided))) & ((((a_leaderhash_primea :: c)) = (leader))) & ((((a_requnde_historyhash_primea :: c)) = (a_requnde_historya))))))"
shows "(\<forall> VARI \<in> (Node) : (\<forall> VARJ \<in> (Node) : (\<forall> VARK \<in> (Node) : (((((((((VARI) = (VARK))) \<and> ((((a_voteshash_primea :: c)) = ((a_voteshash_primea :: c)))))) \<or> ((~ (((<<(VARJ), (VARI)>>) \<in> ((a_voteunde_msghash_primea :: c)))))))) \<or> ((~ (((VARJ) \<in> (fapply (((a_voteshash_primea :: c)), (VARK))))))))))))"(is "PROP ?ob'214")
proof -
ML_command {* writeln "*** TLAPS ENTER 214"; *}
show "PROP ?ob'214"

(* BEGIN ZENON INPUT
;; file=consensus_epr_IndProofs.tlaps/tlapm_f6d3f9.znn; PATH='/home/egolf/.opam/4.07.1/bin:/home/egolf/.local/bin:/home/egolf/bin:/home/egolf/mambaforge/bin:/home/egolf/mambaforge/condabin:/home/egolf/.opam/4.07.1/bin:/home/egolf/.local/bin:/home/egolf/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/home/egolf/.local/bin/gurobi952/linux64/bin:/home/egolf/Projects/apalache/bin:/home/egolf/opt/foxitsoftware/foxitreader:/home/egolf/.local/bin/gurobi952/linux64/bin:/home/egolf/Projects/apalache/bin:/home/egolf/opt/foxitsoftware/foxitreader:/usr/local/bin:/usr/local/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >consensus_epr_IndProofs.tlaps/tlapm_f6d3f9.znn.out
;; obligation #214
$hyp "v'29" (/\ (/\ (/\ (TLA.in a_voteunde_requestunde_msga
(TLA.SUBSET (TLA.prod Node Node))) (TLA.in voted
(TLA.FuncSet Node (TLA.set T. F.))) (TLA.in a_voteunde_msga
(TLA.SUBSET (TLA.prod Node Node))) (TLA.in votes
(TLA.FuncSet Node (TLA.SUBSET Node))) (TLA.in leader
(TLA.FuncSet Node (TLA.set T. F.))) (TLA.in decided
(TLA.FuncSet Node (TLA.SUBSET Value))))
(TLA.bAll Node ((a_n1a) (TLA.bAll Node ((a_n2a) (TLA.bAll Value ((a_v1a) (TLA.bAll Value ((a_v2a) (=> (/\ (TLA.in a_v1a
(TLA.fapply decided a_n1a)) (TLA.in a_v2a (TLA.fapply decided a_n2a)))
(= a_v1a a_v2a))))))))))
(TLA.bAll Node ((VARI) (TLA.bAll Node ((VARJ) (\/ (TLA.in (TLA.tuple VARJ
VARI) a_voteunde_msga) (-. (TLA.in VARJ (TLA.fapply votes VARI))))))))
(TLA.bAll Node ((VARI) (TLA.bEx Quorum ((QJ) (TLA.bAll Value ((VALI) (\/ (TLA.subseteq QJ
(TLA.fapply votes VARI)) (-. (TLA.in VALI (TLA.fapply decided VARI))))))))))
(TLA.bAll Node ((VARI) (TLA.bAll Node ((VARJ) (\/ (TLA.fapply voted VARI)
(-. (TLA.in (TLA.tuple VARI VARJ) a_voteunde_msga)))))))
(TLA.bAll Node ((VARI) (TLA.bEx Quorum ((QJ) (\/ (TLA.subseteq QJ
(TLA.fapply votes VARI)) (-. (TLA.fapply leader VARI)))))))
(TLA.bAll Node ((VARI) (TLA.bAll Value ((VALI) (\/ (TLA.fapply leader VARI)
(-. (TLA.in VALI (TLA.fapply decided VARI))))))))
(TLA.bAll Node ((VARI) (TLA.bAll Node ((VARJ) (TLA.bAll Node ((VARK) (\/ (\/ (/\ (= VARI
VARK) (= votes votes)) (-. (TLA.in (TLA.tuple VARJ VARI) a_voteunde_msga)))
(-. (TLA.in VARJ (TLA.fapply votes VARK))))))))))
(TLA.bAll Node ((VARI) (TLA.bAll Node ((VARJ) (TLA.bAll Node ((VARK) (\/ (\/ (/\ (= VARJ
VARK) (= votes votes)) (-. (TLA.in (TLA.tuple VARI VARK) a_voteunde_msga)))
(-. (TLA.in (TLA.tuple VARI VARJ) a_voteunde_msga)))))))))) (\/ ProtocolNext
OtherNext))
$hyp "v'46" (TLA.bEx Node ((i) (TLA.bEx Node ((j) (/\ (-. (TLA.fapply voted i))
(TLA.in (TLA.tuple j i) a_voteunde_requestunde_msga)
(= a_voteunde_requestunde_msghash_primea
(TLA.setminus a_voteunde_requestunde_msga (TLA.set (TLA.tuple j i))))
(= a_voteunde_msghash_primea (TLA.cup a_voteunde_msga (TLA.set (TLA.tuple i
j)))) (= a_votedhash_primea (TLA.except voted i T.)) (= a_voteshash_primea
votes) (= a_decidedhash_primea decided) (= a_leaderhash_primea leader)
(= a_requnde_historyhash_primea
a_requnde_historya))))))
$goal (TLA.bAll Node ((VARI) (TLA.bAll Node ((VARJ) (TLA.bAll Node ((VARK) (\/ (\/ (/\ (= VARI
VARK) (= a_voteshash_primea a_voteshash_primea)) (-. (TLA.in (TLA.tuple VARJ
VARI) a_voteunde_msghash_primea))) (-. (TLA.in VARJ
(TLA.fapply a_voteshash_primea VARK))))))))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Ha:"((((a_voteunde_requestunde_msga \\in SUBSET(prod(Node, Node)))&((voted \\in FuncSet(Node, {TRUE, FALSE}))&((a_voteunde_msga \\in SUBSET(prod(Node, Node)))&((votes \\in FuncSet(Node, SUBSET(Node)))&((leader \\in FuncSet(Node, {TRUE, FALSE}))&(decided \\in FuncSet(Node, SUBSET(Value))))))))&(bAll(Node, (\<lambda>a_n1a. bAll(Node, (\<lambda>a_n2a. bAll(Value, (\<lambda>a_v1a. bAll(Value, (\<lambda>a_v2a. (((a_v1a \\in (decided[a_n1a]))&(a_v2a \\in (decided[a_n2a])))=>(a_v1a=a_v2a))))))))))&(bAll(Node, (\<lambda>VARI. bAll(Node, (\<lambda>VARJ. ((<<VARJ, VARI>> \\in a_voteunde_msga)|(~(VARJ \\in (votes[VARI]))))))))&(bAll(Node, (\<lambda>VARI. bEx(Quorum, (\<lambda>QJ. bAll(Value, (\<lambda>VALI. ((QJ \\subseteq (votes[VARI]))|(~(VALI \\in (decided[VARI]))))))))))&(bAll(Node, (\<lambda>VARI. bAll(Node, (\<lambda>VARJ. ((voted[VARI])|(~(<<VARI, VARJ>> \\in a_voteunde_msga)))))))&(bAll(Node, (\<lambda>VARI. bEx(Quorum, (\<lambda>QJ. ((QJ \\subseteq (votes[VARI]))|(~(leader[VARI])))))))&(bAll(Node, (\<lambda>VARI. bAll(Value, (\<lambda>VALI. ((leader[VARI])|(~(VALI \\in (decided[VARI]))))))))&(bAll(Node, (\<lambda>VARI. bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARI=VARK)&(votes=votes))|(~(<<VARJ, VARI>> \\in a_voteunde_msga)))|(~(VARJ \\in (votes[VARK]))))))))))&bAll(Node, (\<lambda>VARI. bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(votes=votes))|(~(<<VARI, VARK>> \\in a_voteunde_msga)))|(~(<<VARI, VARJ>> \\in a_voteunde_msga)))))))))))))))))&(ProtocolNext|OtherNext))" (is "?z_hd&?z_hff")
 using v'29 by blast
 have z_Hb:"bEx(Node, (\<lambda>i. bEx(Node, (\<lambda>j. ((~(voted[i]))&((<<j, i>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, i>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<i, j>>}))&((a_votedhash_primea=except(voted, i, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))" (is "?z_hb")
 using v'46 by blast
 have zenon_L1_: "((a_voteshash_primea[(CHOOSE x:(~((x \\in Node)=>(((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=x)&(a_voteshash_primea=a_voteshash_primea))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))), (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))) \\in (a_voteshash_primea[x])))))))])~=(votes[(CHOOSE x:(~((x \\in Node)=>(((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=x)&(a_voteshash_primea=a_voteshash_primea))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))), (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))) \\in (a_voteshash_primea[x])))))))])) ==> (a_voteshash_primea=votes) ==> FALSE" (is "?z_hgu ==> ?z_hgj ==> FALSE")
 proof -
  assume z_Hgu:"?z_hgu" (is "?z_hgv~=?z_hir")
  assume z_Hgj:"?z_hgj"
  show FALSE
  proof (rule zenon_noteq [of "?z_hir"])
   have z_His: "(?z_hir~=?z_hir)"
   by (rule subst [where P="(\<lambda>zenon_Vffa. ((zenon_Vffa[(CHOOSE x:(~((x \\in Node)=>(((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=x)&(a_voteshash_primea=a_voteshash_primea))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))), (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))) \\in (a_voteshash_primea[x])))))))])~=?z_hir))", OF z_Hgj], fact z_Hgu)
   thus "(?z_hir~=?z_hir)" .
  qed
 qed
 have zenon_L2_: "(~((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))) \\in (votes[(CHOOSE x:(~((x \\in Node)=>(((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=x)&(a_voteshash_primea=a_voteshash_primea))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))), (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))) \\in (a_voteshash_primea[x])))))))]))) ==> ((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))) \\in (a_voteshash_primea[(CHOOSE x:(~((x \\in Node)=>(((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=x)&(a_voteshash_primea=a_voteshash_primea))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))), (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))) \\in (a_voteshash_primea[x])))))))])) ==> (a_voteshash_primea=votes) ==> FALSE" (is "?z_hix ==> ?z_hiz ==> ?z_hgj ==> FALSE")
 proof -
  assume z_Hix:"?z_hix" (is "~?z_hiy")
  assume z_Hiz:"?z_hiz"
  assume z_Hgj:"?z_hgj"
  show FALSE
  proof (rule notE [OF z_Hix])
   have z_Hja: "((a_voteshash_primea[(CHOOSE x:(~((x \\in Node)=>(((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=x)&(a_voteshash_primea=a_voteshash_primea))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))), (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))) \\in (a_voteshash_primea[x])))))))])=(votes[(CHOOSE x:(~((x \\in Node)=>(((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=x)&(a_voteshash_primea=a_voteshash_primea))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))), (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))) \\in (a_voteshash_primea[x])))))))]))" (is "?z_hgv=?z_hir")
   proof (rule zenon_nnpp [of "(?z_hgv=?z_hir)"])
    assume z_Hgu:"(?z_hgv~=?z_hir)"
    show FALSE
    by (rule zenon_L1_ [OF z_Hgu z_Hgj])
   qed
   have z_Hiy: "?z_hiy"
   by (rule subst [where P="(\<lambda>zenon_Vgfa. ((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))) \\in zenon_Vgfa))", OF z_Hja], fact z_Hiz)
   thus "?z_hiy" .
  qed
 qed
 have zenon_L3_: "(~(<<(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))), (CHOOSE x:(~((x \\in Node)=>(((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=x)&(a_voteshash_primea=a_voteshash_primea))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))), (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))) \\in (a_voteshash_primea[x])))))))>> \\in a_voteunde_msga)) ==> (<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))), (CHOOSE x:(~((x \\in Node)=>(((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=x)&(a_voteshash_primea=a_voteshash_primea))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))), (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))) \\in (a_voteshash_primea[x])))))))>> \\in a_voteunde_msga) ==> ((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK])))))))))=(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))) ==> FALSE" (is "?z_hje ==> ?z_hkd ==> ?z_hkf ==> FALSE")
 proof -
  assume z_Hje:"?z_hje" (is "~?z_hjf")
  assume z_Hkd:"?z_hkd"
  assume z_Hkf:"?z_hkf" (is "?z_hia=?z_hjh")
  show FALSE
  proof (rule notE [OF z_Hje])
   have z_Hkg: "(<<?z_hia, (CHOOSE x:(~((x \\in Node)=>(((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=x)&(a_voteshash_primea=a_voteshash_primea))|(~(<<?z_hia, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(?z_hia \\in (a_voteshash_primea[x])))))))>>=<<?z_hjh, (CHOOSE x:(~((x \\in Node)=>(((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=x)&(a_voteshash_primea=a_voteshash_primea))|(~(<<?z_hia, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(?z_hia \\in (a_voteshash_primea[x])))))))>>)" (is "?z_hke=?z_hjg")
   proof (rule zenon_nnpp [of "(?z_hke=?z_hjg)"])
    assume z_Hkh:"(?z_hke~=?z_hjg)"
    show FALSE
    proof (rule zenon_noteq [of "?z_hjg"])
     have z_Hki: "(?z_hjg~=?z_hjg)"
     by (rule subst [where P="(\<lambda>zenon_Vhfa. (<<zenon_Vhfa, (CHOOSE x:(~((x \\in Node)=>(((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=x)&(a_voteshash_primea=a_voteshash_primea))|(~(<<?z_hia, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(?z_hia \\in (a_voteshash_primea[x])))))))>>~=?z_hjg))", OF z_Hkf], fact z_Hkh)
     thus "(?z_hjg~=?z_hjg)" .
    qed
   qed
   have z_Hjf: "?z_hjf"
   by (rule subst [where P="(\<lambda>zenon_Vifa. (zenon_Vifa \\in a_voteunde_msga))", OF z_Hkg], fact z_Hkd)
   thus "?z_hjf" .
  qed
 qed
 assume z_Hc:"(~bAll(Node, (\<lambda>VARI. bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARI=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, VARI>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))" (is "~?z_hkq")
 have z_Hd: "?z_hd" (is "?z_he&?z_hbh")
 by (rule zenon_and_0 [OF z_Ha])
 have z_Hbh: "?z_hbh" (is "?z_hbi&?z_hcb")
 by (rule zenon_and_1 [OF z_Hd])
 have z_Hcb: "?z_hcb" (is "?z_hcc&?z_hco")
 by (rule zenon_and_1 [OF z_Hbh])
 have z_Hcc: "?z_hcc"
 by (rule zenon_and_0 [OF z_Hcb])
 have z_Hco: "?z_hco" (is "?z_hcp&?z_hdd")
 by (rule zenon_and_1 [OF z_Hcb])
 have z_Hdd: "?z_hdd" (is "?z_hde&?z_hdn")
 by (rule zenon_and_1 [OF z_Hco])
 have z_Hde: "?z_hde"
 by (rule zenon_and_0 [OF z_Hdd])
 have z_Hdn: "?z_hdn" (is "?z_hdo&?z_hdv")
 by (rule zenon_and_1 [OF z_Hdd])
 have z_Hdv: "?z_hdv" (is "?z_hdw&?z_heb")
 by (rule zenon_and_1 [OF z_Hdn])
 have z_Heb: "?z_heb" (is "?z_hec&?z_hes")
 by (rule zenon_and_1 [OF z_Hdv])
 have z_Hes: "?z_hes"
 by (rule zenon_and_1 [OF z_Heb])
 have z_Hlb_z_Hcc: "(\\A x:((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msga)|(~(VARJ \\in (votes[x])))))))) == ?z_hcc" (is "?z_hlb == _")
 by (unfold bAll_def)
 have z_Hlb: "?z_hlb" (is "\\A x : ?z_hlk(x)")
 by (unfold z_Hlb_z_Hcc, fact z_Hcc)
 have z_Hll_z_Hde: "(\\A x:((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((voted[x])|(~(<<x, VARJ>> \\in a_voteunde_msga))))))) == ?z_hde" (is "?z_hll == _")
 by (unfold bAll_def)
 have z_Hll: "?z_hll" (is "\\A x : ?z_hlt(x)")
 by (unfold z_Hll_z_Hde, fact z_Hde)
 have z_Hlu_z_Hes: "(\\A x:((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(votes=votes))|(~(<<x, VARK>> \\in a_voteunde_msga)))|(~(<<x, VARJ>> \\in a_voteunde_msga))))))))) == ?z_hes" (is "?z_hlu == _")
 by (unfold bAll_def)
 have z_Hlu: "?z_hlu" (is "\\A x : ?z_hmf(x)")
 by (unfold z_Hlu_z_Hes, fact z_Hes)
 have z_Hmg_z_Hb: "(\\E x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))) == ?z_hb" (is "?z_hmg == _")
 by (unfold bEx_def)
 have z_Hmg: "?z_hmg" (is "\\E x : ?z_hmh(x)")
 by (unfold z_Hmg_z_Hb, fact z_Hb)
 have z_Hmi: "?z_hmh((CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))))" (is "?z_hmj&?z_hmk")
 by (rule zenon_ex_choose_0 [of "?z_hmh", OF z_Hmg])
 have z_Hmj: "?z_hmj"
 by (rule zenon_and_0 [OF z_Hmi])
 have z_Hmk: "?z_hmk"
 by (rule zenon_and_1 [OF z_Hmi])
 have z_Hml_z_Hmk: "(\\E x:((x \\in Node)&((~(voted[(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))]))&((<<x, (CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<x, (CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))), x>>}))&((a_votedhash_primea=except(voted, (CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))), TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))) == ?z_hmk" (is "?z_hml == _")
 by (unfold bEx_def)
 have z_Hml: "?z_hml" (is "\\E x : ?z_hnf(x)")
 by (unfold z_Hml_z_Hmk, fact z_Hmk)
 have z_Hng: "?z_hnf((CHOOSE x:((x \\in Node)&((~(voted[(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))]))&((<<x, (CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<x, (CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))), x>>}))&((a_votedhash_primea=except(voted, (CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))), TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))" (is "?z_hni&?z_hnj")
 by (rule zenon_ex_choose_0 [of "?z_hnf", OF z_Hml])
 have z_Hnj: "?z_hnj" (is "?z_hmo&?z_hnk")
 by (rule zenon_and_1 [OF z_Hng])
 have z_Hmo: "?z_hmo" (is "~?z_hmp")
 by (rule zenon_and_0 [OF z_Hnj])
 have z_Hnk: "?z_hnk" (is "?z_hnl&?z_hnm")
 by (rule zenon_and_1 [OF z_Hnj])
 have z_Hnm: "?z_hnm" (is "?z_hnn&?z_hno")
 by (rule zenon_and_1 [OF z_Hnk])
 have z_Hno: "?z_hno" (is "?z_hnp&?z_hnc")
 by (rule zenon_and_1 [OF z_Hnm])
 have z_Hnp: "?z_hnp" (is "_=?z_hnq")
 by (rule zenon_and_0 [OF z_Hno])
 have z_Hnc: "?z_hnc" (is "?z_hnd&?z_hgi")
 by (rule zenon_and_1 [OF z_Hno])
 have z_Hgi: "?z_hgi" (is "?z_hgj&?z_hgl")
 by (rule zenon_and_1 [OF z_Hnc])
 have z_Hgj: "?z_hgj"
 by (rule zenon_and_0 [OF z_Hgi])
 have z_Hnr_z_Hc: "(~(\\A x:((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK]))))))))))) == (~?z_hkq)" (is "?z_hnr == ?z_hc")
 by (unfold bAll_def)
 have z_Hnr: "?z_hnr" (is "~(\\A x : ?z_hnt(x))")
 by (unfold z_Hnr_z_Hc, fact z_Hc)
 have z_Hnu: "(\\E x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))" (is "\\E x : ?z_hnv(x)")
 by (rule zenon_notallex_0 [of "?z_hnt", OF z_Hnr])
 have z_Hnw: "?z_hnv((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK]))))))))))))" (is "~(?z_hnx=>?z_hny)")
 by (rule zenon_ex_choose_0 [of "?z_hnv", OF z_Hnu])
 have z_Hnx: "?z_hnx"
 by (rule zenon_notimply_0 [OF z_Hnw])
 have z_Hnz: "(~?z_hny)"
 by (rule zenon_notimply_1 [OF z_Hnw])
 have z_Hoa_z_Hnz: "(~(\\A x:((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))) == (~?z_hny)" (is "?z_hoa == ?z_hnz")
 by (unfold bAll_def)
 have z_Hoa: "?z_hoa" (is "~(\\A x : ?z_hoc(x))")
 by (unfold z_Hoa_z_Hnz, fact z_Hnz)
 have z_Hod: "(\\E x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK])))))))))" (is "\\E x : ?z_hoe(x)")
 by (rule zenon_notallex_0 [of "?z_hoc", OF z_Hoa])
 have z_Hof: "?z_hoe((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))))" (is "~(?z_hog=>?z_hoh)")
 by (rule zenon_ex_choose_0 [of "?z_hoe", OF z_Hod])
 have z_Hog: "?z_hog"
 by (rule zenon_notimply_0 [OF z_Hof])
 have z_Hoi: "(~?z_hoh)"
 by (rule zenon_notimply_1 [OF z_Hof])
 have z_Hoj_z_Hoi: "(~(\\A x:((x \\in Node)=>(((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=x)&(a_voteshash_primea=a_voteshash_primea))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))), (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))) \\in (a_voteshash_primea[x]))))))) == (~?z_hoh)" (is "?z_hoj == ?z_hoi")
 by (unfold bAll_def)
 have z_Hoj: "?z_hoj" (is "~(\\A x : ?z_hol(x))")
 by (unfold z_Hoj_z_Hoi, fact z_Hoi)
 have z_Hom: "(\\E x:(~((x \\in Node)=>(((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=x)&(a_voteshash_primea=a_voteshash_primea))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))), (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))) \\in (a_voteshash_primea[x])))))))" (is "\\E x : ?z_hon(x)")
 by (rule zenon_notallex_0 [of "?z_hol", OF z_Hoj])
 have z_Hoo: "?z_hon((CHOOSE x:(~((x \\in Node)=>(((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=x)&(a_voteshash_primea=a_voteshash_primea))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))), (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))) \\in (a_voteshash_primea[x]))))))))" (is "~(?z_hop=>?z_hoq)")
 by (rule zenon_ex_choose_0 [of "?z_hon", OF z_Hom])
 have z_Hop: "?z_hop"
 by (rule zenon_notimply_0 [OF z_Hoo])
 have z_Hor: "(~?z_hoq)" (is "~(?z_hos|?z_hot)")
 by (rule zenon_notimply_1 [OF z_Hoo])
 have z_Hou: "(~?z_hos)" (is "~(?z_hov|?z_hhx)")
 by (rule zenon_notor_0 [OF z_Hor])
 have z_How: "(~?z_hot)" (is "~~?z_hiz")
 by (rule zenon_notor_1 [OF z_Hor])
 have z_Hiz: "?z_hiz"
 by (rule zenon_notnot_0 [OF z_How])
 have z_Hox: "(~?z_hov)" (is "~(?z_hoy&?z_hhq)")
 by (rule zenon_notor_0 [OF z_Hou])
 have z_Hoz: "(~?z_hhx)" (is "~~?z_hhy")
 by (rule zenon_notor_1 [OF z_Hou])
 have z_Hhy: "?z_hhy"
 by (rule zenon_notnot_0 [OF z_Hoz])
 show FALSE
 proof (rule zenon_notand [OF z_Hox])
  assume z_Hpa:"((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&?z_hhq)|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))~=(CHOOSE x:(~((x \\in Node)=>(((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&?z_hhq)|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=x)&?z_hhq)|?z_hhx)|(~((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&?z_hhq)|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&?z_hhq)|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&?z_hhq)|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))) \\in (a_voteshash_primea[x]))))))))" (is "?z_hhf~=?z_hgw")
  have z_Hpb: "(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. ((((?z_hhf=VARK)&?z_hhq)|(~(<<x, ?z_hhf>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))), ?z_hhf>> \\in ?z_hnq)" (is "?z_hpb")
  by (rule subst [where P="(\<lambda>zenon_Vjc. (<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. ((((?z_hhf=VARK)&?z_hhq)|(~(<<x, ?z_hhf>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))), ?z_hhf>> \\in zenon_Vjc))", OF z_Hnp z_Hhy])
  show FALSE
  proof (rule zenon_in_cup [of "<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. ((((?z_hhf=VARK)&?z_hhq)|(~(<<x, ?z_hhf>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))), ?z_hhf>>" "a_voteunde_msga" "{<<(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&?z_hgi))))))))), (CHOOSE x:((x \\in Node)&(?z_hmo&((<<x, (CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&?z_hgi)))))))))>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<x, (CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&?z_hgi)))))))))>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&?z_hgi))))))))), x>>}))&?z_hnc))))))>>}", OF z_Hpb])
   assume z_Hph:"(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. ((((?z_hhf=VARK)&?z_hhq)|(~(<<x, ?z_hhf>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))), ?z_hhf>> \\in a_voteunde_msga)" (is "?z_hph")
   have z_Hpi: "?z_hlk(?z_hgw)" (is "_=>?z_hpj")
   by (rule zenon_all_0 [of "?z_hlk" "?z_hgw", OF z_Hlb])
   show FALSE
   proof (rule zenon_imply [OF z_Hpi])
    assume z_Hpk:"(~?z_hop)"
    show FALSE
    by (rule notE [OF z_Hpk z_Hop])
   next
    assume z_Hpj:"?z_hpj"
    have z_Hpl_z_Hpj: "(\\A x:((x \\in Node)=>((<<x, ?z_hgw>> \\in a_voteunde_msga)|(~(x \\in (votes[?z_hgw])))))) == ?z_hpj" (is "?z_hpl == _")
    by (unfold bAll_def)
    have z_Hpl: "?z_hpl" (is "\\A x : ?z_hps(x)")
    by (unfold z_Hpl_z_Hpj, fact z_Hpj)
    have z_Hpt: "?z_hmf((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. ((((?z_hhf=VARK)&?z_hhq)|(~(<<x, ?z_hhf>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))))" (is "_=>?z_hpu")
    by (rule zenon_all_0 [of "?z_hmf" "(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. ((((?z_hhf=VARK)&?z_hhq)|(~(<<x, ?z_hhf>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK])))))))))", OF z_Hlu])
    show FALSE
    proof (rule zenon_imply [OF z_Hpt])
     assume z_Hpv:"(~?z_hog)"
     show FALSE
     by (rule notE [OF z_Hpv z_Hog])
    next
     assume z_Hpu:"?z_hpu"
     have z_Hpw_z_Hpu: "(\\A x:((x \\in Node)=>bAll(Node, (\<lambda>VARK. ((((x=VARK)&(votes=votes))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. ((((?z_hhf=VARK)&?z_hhq)|(~(<<x, ?z_hhf>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))), VARK>> \\in a_voteunde_msga)))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. ((((?z_hhf=VARK)&?z_hhq)|(~(<<x, ?z_hhf>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))), x>> \\in a_voteunde_msga))))))) == ?z_hpu" (is "?z_hpw == _")
     by (unfold bAll_def)
     have z_Hpw: "?z_hpw" (is "\\A x : ?z_hqj(x)")
     by (unfold z_Hpw_z_Hpu, fact z_Hpu)
     have z_Hqk: "?z_hps((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. ((((?z_hhf=VARK)&?z_hhq)|(~(<<x, ?z_hhf>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))))" (is "_=>?z_hql")
     by (rule zenon_all_0 [of "?z_hps" "(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. ((((?z_hhf=VARK)&?z_hhq)|(~(<<x, ?z_hhf>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK])))))))))", OF z_Hpl])
     show FALSE
     proof (rule zenon_imply [OF z_Hqk])
      assume z_Hpv:"(~?z_hog)"
      show FALSE
      by (rule notE [OF z_Hpv z_Hog])
     next
      assume z_Hql:"?z_hql" (is "?z_hkd|?z_hix")
      show FALSE
      proof (rule zenon_or [OF z_Hql])
       assume z_Hkd:"?z_hkd"
       have z_Hqm: "?z_hqj(?z_hhf)" (is "_=>?z_hqn")
       by (rule zenon_all_0 [of "?z_hqj" "?z_hhf", OF z_Hpw])
       show FALSE
       proof (rule zenon_imply [OF z_Hqm])
        assume z_Hqo:"(~?z_hnx)"
        show FALSE
        by (rule notE [OF z_Hqo z_Hnx])
       next
        assume z_Hqn:"?z_hqn"
        have z_Hqp_z_Hqn: "(\\A x:((x \\in Node)=>((((?z_hhf=x)&(votes=votes))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. ((((?z_hhf=VARK)&?z_hhq)|(~(<<x, ?z_hhf>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))), x>> \\in a_voteunde_msga)))|(~?z_hph)))) == ?z_hqn" (is "?z_hqp == _")
        by (unfold bAll_def)
        have z_Hqp: "?z_hqp" (is "\\A x : ?z_hqv(x)")
        by (unfold z_Hqp_z_Hqn, fact z_Hqn)
        have z_Hqw: "?z_hqv(?z_hgw)" (is "_=>?z_hqx")
        by (rule zenon_all_0 [of "?z_hqv" "?z_hgw", OF z_Hqp])
        show FALSE
        proof (rule zenon_imply [OF z_Hqw])
         assume z_Hpk:"(~?z_hop)"
         show FALSE
         by (rule notE [OF z_Hpk z_Hop])
        next
         assume z_Hqx:"?z_hqx" (is "?z_hqy|?z_hqu")
         show FALSE
         proof (rule zenon_or [OF z_Hqx])
          assume z_Hqy:"?z_hqy" (is "?z_hqz|?z_hra")
          show FALSE
          proof (rule zenon_or [OF z_Hqy])
           assume z_Hqz:"?z_hqz" (is "_&?z_hen")
           have z_Hoy: "?z_hoy"
           by (rule zenon_and_0 [OF z_Hqz])
           show FALSE
           by (rule notE [OF z_Hpa z_Hoy])
          next
           assume z_Hra:"?z_hra"
           show FALSE
           by (rule notE [OF z_Hra z_Hkd])
          qed
         next
          assume z_Hqu:"?z_hqu"
          show FALSE
          by (rule notE [OF z_Hqu z_Hph])
         qed
        qed
       qed
      next
       assume z_Hix:"?z_hix" (is "~?z_hiy")
       show FALSE
       by (rule zenon_L2_ [OF z_Hix z_Hiz z_Hgj])
      qed
     qed
    qed
   qed
  next
   assume z_Hrb:"(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. ((((?z_hhf=VARK)&?z_hhq)|(~(<<x, ?z_hhf>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))), ?z_hhf>> \\in {<<(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&?z_hgi))))))))), (CHOOSE x:((x \\in Node)&(?z_hmo&((<<x, (CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&?z_hgi)))))))))>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<x, (CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&?z_hgi)))))))))>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&?z_hgi))))))))), x>>}))&?z_hnc))))))>>})" (is "?z_hrb")
   show FALSE
   proof (rule zenon_in_addElt [of "<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. ((((?z_hhf=VARK)&?z_hhq)|(~(<<x, ?z_hhf>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))), ?z_hhf>>" "<<(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&?z_hgi))))))))), (CHOOSE x:((x \\in Node)&(?z_hmo&((<<x, (CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&?z_hgi)))))))))>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<x, (CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&?z_hgi)))))))))>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&?z_hgi))))))))), x>>}))&?z_hnc))))))>>" "{}", OF z_Hrb])
    assume z_Hrd:"(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. ((((?z_hhf=VARK)&?z_hhq)|(~(<<x, ?z_hhf>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))), ?z_hhf>>=<<(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&?z_hgi))))))))), (CHOOSE x:((x \\in Node)&(?z_hmo&((<<x, (CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&?z_hgi)))))))))>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<x, (CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&?z_hgi)))))))))>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&?z_hgi))))))))), x>>}))&?z_hnc))))))>>)" (is "?z_hhz=?z_hpg")
    have z_Hkf: "((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. ((((?z_hhf=VARK)&?z_hhq)|(~(<<x, ?z_hhf>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK])))))))))=(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&?z_hgi))))))))))" (is "?z_hia=?z_hjh")
    using z_Hrd by auto
    have z_Hpi: "?z_hlk(?z_hgw)" (is "_=>?z_hpj")
    by (rule zenon_all_0 [of "?z_hlk" "?z_hgw", OF z_Hlb])
    show FALSE
    proof (rule zenon_imply [OF z_Hpi])
     assume z_Hpk:"(~?z_hop)"
     show FALSE
     by (rule notE [OF z_Hpk z_Hop])
    next
     assume z_Hpj:"?z_hpj"
     have z_Hpl_z_Hpj: "(\\A x:((x \\in Node)=>((<<x, ?z_hgw>> \\in a_voteunde_msga)|(~(x \\in (votes[?z_hgw])))))) == ?z_hpj" (is "?z_hpl == _")
     by (unfold bAll_def)
     have z_Hpl: "?z_hpl" (is "\\A x : ?z_hps(x)")
     by (unfold z_Hpl_z_Hpj, fact z_Hpj)
     have z_Hqk: "?z_hps(?z_hia)" (is "_=>?z_hql")
     by (rule zenon_all_0 [of "?z_hps" "?z_hia", OF z_Hpl])
     show FALSE
     proof (rule zenon_imply [OF z_Hqk])
      assume z_Hpv:"(~?z_hog)"
      show FALSE
      by (rule notE [OF z_Hpv z_Hog])
     next
      assume z_Hql:"?z_hql" (is "?z_hkd|?z_hix")
      show FALSE
      proof (rule zenon_or [OF z_Hql])
       assume z_Hkd:"?z_hkd"
       have z_Hre: "?z_hlt(?z_hjh)" (is "_=>?z_hrf")
       by (rule zenon_all_0 [of "?z_hlt" "?z_hjh", OF z_Hll])
       show FALSE
       proof (rule zenon_imply [OF z_Hre])
        assume z_Hrg:"(~?z_hmj)"
        show FALSE
        by (rule notE [OF z_Hrg z_Hmj])
       next
        assume z_Hrf:"?z_hrf"
        have z_Hrh_z_Hrf: "(\\A x:((x \\in Node)=>(?z_hmp|(~(<<?z_hjh, x>> \\in a_voteunde_msga))))) == ?z_hrf" (is "?z_hrh == _")
        by (unfold bAll_def)
        have z_Hrh: "?z_hrh" (is "\\A x : ?z_hrm(x)")
        by (unfold z_Hrh_z_Hrf, fact z_Hrf)
        have z_Hrn: "?z_hrm(?z_hgw)" (is "_=>?z_hro")
        by (rule zenon_all_0 [of "?z_hrm" "?z_hgw", OF z_Hrh])
        show FALSE
        proof (rule zenon_imply [OF z_Hrn])
         assume z_Hpk:"(~?z_hop)"
         show FALSE
         by (rule notE [OF z_Hpk z_Hop])
        next
         assume z_Hro:"?z_hro" (is "_|?z_hje")
         show FALSE
         proof (rule zenon_or [OF z_Hro])
          assume z_Hmp:"?z_hmp"
          show FALSE
          by (rule notE [OF z_Hmo z_Hmp])
         next
          assume z_Hje:"?z_hje" (is "~?z_hjf")
          show FALSE
          by (rule zenon_L3_ [OF z_Hje z_Hkd z_Hkf])
         qed
        qed
       qed
      next
       assume z_Hix:"?z_hix" (is "~?z_hiy")
       show FALSE
       by (rule zenon_L2_ [OF z_Hix z_Hiz z_Hgj])
      qed
     qed
    qed
   next
    assume z_Hrp:"(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. ((((?z_hhf=VARK)&?z_hhq)|(~(<<x, ?z_hhf>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))), ?z_hhf>> \\in {})" (is "?z_hrp")
    show FALSE
    by (rule zenon_in_emptyset [of "<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. ((((?z_hhf=VARK)&?z_hhq)|(~(<<x, ?z_hhf>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))), ?z_hhf>>", OF z_Hrp])
   qed
  qed
 next
  assume z_Hrq:"(a_voteshash_primea~=a_voteshash_primea)"
  show FALSE
  by (rule zenon_noteq [OF z_Hrq])
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 214"; *} qed
lemma ob'212:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
fixes Node
fixes Quorum
fixes Value
fixes a_voteunde_requestunde_msga a_voteunde_requestunde_msga'
fixes voted voted'
fixes a_voteunde_msga a_voteunde_msga'
fixes votes votes'
fixes leader leader'
fixes decided decided'
fixes a_requnde_historya a_requnde_historya'
(* usable definition vars suppressed *)
(* usable definition IgnoreRequestVote suppressed *)
(* usable definition ProtocolNext suppressed *)
(* usable definition OtherNext suppressed *)
(* usable definition Spec suppressed *)
(* usable definition Symmetry suppressed *)
(* usable definition Safety suppressed *)
(* usable definition SplitVote suppressed *)
(* usable definition Liveness suppressed *)
assumes v'29: "(((((((a_voteunde_requestunde_msga) \<in> ((SUBSET (((Node) \<times> (Node))))))) & (((voted) \<in> ([(Node) \<rightarrow> (BOOLEAN)]))) & (((a_voteunde_msga) \<in> ((SUBSET (((Node) \<times> (Node))))))) & (((votes) \<in> ([(Node) \<rightarrow> ((SUBSET (Node)))]))) & (((leader) \<in> ([(Node) \<rightarrow> (BOOLEAN)]))) & (((decided) \<in> ([(Node) \<rightarrow> ((SUBSET (Value)))])))) & (\<forall> a_n1a \<in> (Node) : (\<forall> a_n2a \<in> (Node) : (\<forall> a_v1a \<in> (Value) : (\<forall> a_v2a \<in> (Value) : (((((((a_v1a) \<in> (fapply ((decided), (a_n1a))))) \<and> (((a_v2a) \<in> (fapply ((decided), (a_n2a))))))) \<Rightarrow> (((a_v1a) = (a_v2a))))))))) & (\<forall> VARI \<in> (Node) : (\<forall> VARJ \<in> (Node) : (((((<<(VARJ), (VARI)>>) \<in> (a_voteunde_msga))) \<or> ((~ (((VARJ) \<in> (fapply ((votes), (VARI))))))))))) & (\<forall> VARI \<in> (Node) : (\<exists> QJ \<in> (Quorum) : (\<forall> VALI \<in> (Value) : (((((QJ) \<subseteq> (fapply ((votes), (VARI))))) \<or> ((~ (((VALI) \<in> (fapply ((decided), (VARI)))))))))))) & (\<forall> VARI \<in> (Node) : (\<forall> VARJ \<in> (Node) : (((fapply ((voted), (VARI))) \<or> ((~ (((<<(VARI), (VARJ)>>) \<in> (a_voteunde_msga))))))))) & (\<forall> VARI \<in> (Node) : (\<exists> QJ \<in> (Quorum) : (((((QJ) \<subseteq> (fapply ((votes), (VARI))))) \<or> ((~ (fapply ((leader), (VARI))))))))) & (\<forall> VARI \<in> (Node) : (\<forall> VALI \<in> (Value) : (((fapply ((leader), (VARI))) \<or> ((~ (((VALI) \<in> (fapply ((decided), (VARI))))))))))) & (\<forall> VARI \<in> (Node) : (\<forall> VARJ \<in> (Node) : (\<forall> VARK \<in> (Node) : (((((((((VARI) = (VARK))) \<and> (((votes) = (votes))))) \<or> ((~ (((<<(VARJ), (VARI)>>) \<in> (a_voteunde_msga))))))) \<or> ((~ (((VARJ) \<in> (fapply ((votes), (VARK)))))))))))) & (\<forall> VARI \<in> (Node) : (\<forall> VARJ \<in> (Node) : (\<forall> VARK \<in> (Node) : (((((((((VARJ) = (VARK))) \<and> (((votes) = (votes))))) \<or> ((~ (((<<(VARI), (VARK)>>) \<in> (a_voteunde_msga))))))) \<or> ((~ (((<<(VARI), (VARJ)>>) \<in> (a_voteunde_msga))))))))))) \<and> (((ProtocolNext) \<or> (OtherNext)))))"
assumes v'45: "(\<exists> i \<in> (Node) : (\<exists> j \<in> (Node) : ((((<<(i), (j)>>) \<notin> (a_requnde_historya))) & (\<forall> a_dst2a \<in> (Node) : (((<<(i), (a_dst2a)>>) \<notin> (a_voteunde_requestunde_msga)))) & ((((a_voteunde_requestunde_msghash_primea :: c)) = (((a_voteunde_requestunde_msga) \<union> ({(<<(i), (j)>>)}))))) & ((((a_requnde_historyhash_primea :: c)) = (((a_requnde_historya) \<union> ({(<<(i), (j)>>)}))))) & (((((a_votedhash_primea :: c)) = (voted))) & ((((a_voteunde_msghash_primea :: c)) = (a_voteunde_msga))) & ((((a_voteshash_primea :: c)) = (votes))) & ((((a_leaderhash_primea :: c)) = (leader))) & ((((a_decidedhash_primea :: c)) = (decided)))))))"
shows "(\<forall> VARI \<in> (Node) : (\<forall> VARJ \<in> (Node) : (\<forall> VARK \<in> (Node) : (((((((((VARI) = (VARK))) \<and> ((((a_voteshash_primea :: c)) = ((a_voteshash_primea :: c)))))) \<or> ((~ (((<<(VARJ), (VARI)>>) \<in> ((a_voteunde_msghash_primea :: c)))))))) \<or> ((~ (((VARJ) \<in> (fapply (((a_voteshash_primea :: c)), (VARK))))))))))))"(is "PROP ?ob'212")
proof -
ML_command {* writeln "*** TLAPS ENTER 212"; *}
show "PROP ?ob'212"

(* BEGIN ZENON INPUT
;; file=consensus_epr_IndProofs.tlaps/tlapm_63dc32.znn; PATH='/home/egolf/.opam/4.07.1/bin:/home/egolf/.local/bin:/home/egolf/bin:/home/egolf/mambaforge/bin:/home/egolf/mambaforge/condabin:/home/egolf/.opam/4.07.1/bin:/home/egolf/.local/bin:/home/egolf/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/home/egolf/.local/bin/gurobi952/linux64/bin:/home/egolf/Projects/apalache/bin:/home/egolf/opt/foxitsoftware/foxitreader:/home/egolf/.local/bin/gurobi952/linux64/bin:/home/egolf/Projects/apalache/bin:/home/egolf/opt/foxitsoftware/foxitreader:/usr/local/bin:/usr/local/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >consensus_epr_IndProofs.tlaps/tlapm_63dc32.znn.out
;; obligation #212
$hyp "v'29" (/\ (/\ (/\ (TLA.in a_voteunde_requestunde_msga
(TLA.SUBSET (TLA.prod Node Node))) (TLA.in voted
(TLA.FuncSet Node (TLA.set T. F.))) (TLA.in a_voteunde_msga
(TLA.SUBSET (TLA.prod Node Node))) (TLA.in votes
(TLA.FuncSet Node (TLA.SUBSET Node))) (TLA.in leader
(TLA.FuncSet Node (TLA.set T. F.))) (TLA.in decided
(TLA.FuncSet Node (TLA.SUBSET Value))))
(TLA.bAll Node ((a_n1a) (TLA.bAll Node ((a_n2a) (TLA.bAll Value ((a_v1a) (TLA.bAll Value ((a_v2a) (=> (/\ (TLA.in a_v1a
(TLA.fapply decided a_n1a)) (TLA.in a_v2a (TLA.fapply decided a_n2a)))
(= a_v1a a_v2a))))))))))
(TLA.bAll Node ((VARI) (TLA.bAll Node ((VARJ) (\/ (TLA.in (TLA.tuple VARJ
VARI) a_voteunde_msga) (-. (TLA.in VARJ (TLA.fapply votes VARI))))))))
(TLA.bAll Node ((VARI) (TLA.bEx Quorum ((QJ) (TLA.bAll Value ((VALI) (\/ (TLA.subseteq QJ
(TLA.fapply votes VARI)) (-. (TLA.in VALI (TLA.fapply decided VARI))))))))))
(TLA.bAll Node ((VARI) (TLA.bAll Node ((VARJ) (\/ (TLA.fapply voted VARI)
(-. (TLA.in (TLA.tuple VARI VARJ) a_voteunde_msga)))))))
(TLA.bAll Node ((VARI) (TLA.bEx Quorum ((QJ) (\/ (TLA.subseteq QJ
(TLA.fapply votes VARI)) (-. (TLA.fapply leader VARI)))))))
(TLA.bAll Node ((VARI) (TLA.bAll Value ((VALI) (\/ (TLA.fapply leader VARI)
(-. (TLA.in VALI (TLA.fapply decided VARI))))))))
(TLA.bAll Node ((VARI) (TLA.bAll Node ((VARJ) (TLA.bAll Node ((VARK) (\/ (\/ (/\ (= VARI
VARK) (= votes votes)) (-. (TLA.in (TLA.tuple VARJ VARI) a_voteunde_msga)))
(-. (TLA.in VARJ (TLA.fapply votes VARK))))))))))
(TLA.bAll Node ((VARI) (TLA.bAll Node ((VARJ) (TLA.bAll Node ((VARK) (\/ (\/ (/\ (= VARJ
VARK) (= votes votes)) (-. (TLA.in (TLA.tuple VARI VARK) a_voteunde_msga)))
(-. (TLA.in (TLA.tuple VARI VARJ) a_voteunde_msga)))))))))) (\/ ProtocolNext
OtherNext))
$hyp "v'45" (TLA.bEx Node ((i) (TLA.bEx Node ((j) (/\ (-. (TLA.in (TLA.tuple i
j) a_requnde_historya)) (TLA.bAll Node ((a_dst2a) (-. (TLA.in (TLA.tuple i
a_dst2a) a_voteunde_requestunde_msga))))
(= a_voteunde_requestunde_msghash_primea (TLA.cup a_voteunde_requestunde_msga
(TLA.set (TLA.tuple i j)))) (= a_requnde_historyhash_primea
(TLA.cup a_requnde_historya (TLA.set (TLA.tuple i j))))
(/\ (= a_votedhash_primea voted) (= a_voteunde_msghash_primea
a_voteunde_msga) (= a_voteshash_primea votes) (= a_leaderhash_primea leader)
(= a_decidedhash_primea
decided)))))))
$goal (TLA.bAll Node ((VARI) (TLA.bAll Node ((VARJ) (TLA.bAll Node ((VARK) (\/ (\/ (/\ (= VARI
VARK) (= a_voteshash_primea a_voteshash_primea)) (-. (TLA.in (TLA.tuple VARJ
VARI) a_voteunde_msghash_primea))) (-. (TLA.in VARJ
(TLA.fapply a_voteshash_primea VARK))))))))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Ha:"((((a_voteunde_requestunde_msga \\in SUBSET(prod(Node, Node)))&((voted \\in FuncSet(Node, {TRUE, FALSE}))&((a_voteunde_msga \\in SUBSET(prod(Node, Node)))&((votes \\in FuncSet(Node, SUBSET(Node)))&((leader \\in FuncSet(Node, {TRUE, FALSE}))&(decided \\in FuncSet(Node, SUBSET(Value))))))))&(bAll(Node, (\<lambda>a_n1a. bAll(Node, (\<lambda>a_n2a. bAll(Value, (\<lambda>a_v1a. bAll(Value, (\<lambda>a_v2a. (((a_v1a \\in (decided[a_n1a]))&(a_v2a \\in (decided[a_n2a])))=>(a_v1a=a_v2a))))))))))&(bAll(Node, (\<lambda>VARI. bAll(Node, (\<lambda>VARJ. ((<<VARJ, VARI>> \\in a_voteunde_msga)|(~(VARJ \\in (votes[VARI]))))))))&(bAll(Node, (\<lambda>VARI. bEx(Quorum, (\<lambda>QJ. bAll(Value, (\<lambda>VALI. ((QJ \\subseteq (votes[VARI]))|(~(VALI \\in (decided[VARI]))))))))))&(bAll(Node, (\<lambda>VARI. bAll(Node, (\<lambda>VARJ. ((voted[VARI])|(~(<<VARI, VARJ>> \\in a_voteunde_msga)))))))&(bAll(Node, (\<lambda>VARI. bEx(Quorum, (\<lambda>QJ. ((QJ \\subseteq (votes[VARI]))|(~(leader[VARI])))))))&(bAll(Node, (\<lambda>VARI. bAll(Value, (\<lambda>VALI. ((leader[VARI])|(~(VALI \\in (decided[VARI]))))))))&(bAll(Node, (\<lambda>VARI. bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARI=VARK)&(votes=votes))|(~(<<VARJ, VARI>> \\in a_voteunde_msga)))|(~(VARJ \\in (votes[VARK]))))))))))&bAll(Node, (\<lambda>VARI. bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(votes=votes))|(~(<<VARI, VARK>> \\in a_voteunde_msga)))|(~(<<VARI, VARJ>> \\in a_voteunde_msga)))))))))))))))))&(ProtocolNext|OtherNext))" (is "?z_hd&?z_hff")
 using v'29 by blast
 have z_Hb:"bEx(Node, (\<lambda>i. bEx(Node, (\<lambda>j. ((~(<<i, j>> \\in a_requnde_historya))&(bAll(Node, (\<lambda>a_dst2a. (~(<<i, a_dst2a>> \\in a_voteunde_requestunde_msga))))&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\cup {<<i, j>>}))&((a_requnde_historyhash_primea=(a_requnde_historya \\cup {<<i, j>>}))&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_voteshash_primea=votes)&((a_leaderhash_primea=leader)&(a_decidedhash_primea=decided)))))))))))))" (is "?z_hb")
 using v'45 by blast
 have zenon_L1_: "((a_voteshash_primea[(CHOOSE x:(~((x \\in Node)=>(((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=x)&(a_voteshash_primea=a_voteshash_primea))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))), (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))) \\in (a_voteshash_primea[x])))))))])~=(votes[(CHOOSE x:(~((x \\in Node)=>(((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=x)&(a_voteshash_primea=a_voteshash_primea))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))), (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))) \\in (a_voteshash_primea[x])))))))])) ==> (a_voteshash_primea=votes) ==> FALSE" (is "?z_hgw ==> ?z_hgp ==> FALSE")
 proof -
  assume z_Hgw:"?z_hgw" (is "?z_hgx~=?z_hit")
  assume z_Hgp:"?z_hgp"
  show FALSE
  proof (rule zenon_noteq [of "?z_hit"])
   have z_Hiu: "(?z_hit~=?z_hit)"
   by (rule subst [where P="(\<lambda>zenon_Veq. ((zenon_Veq[(CHOOSE x:(~((x \\in Node)=>(((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=x)&(a_voteshash_primea=a_voteshash_primea))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))), (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))) \\in (a_voteshash_primea[x])))))))])~=?z_hit))", OF z_Hgp], fact z_Hgw)
   thus "(?z_hit~=?z_hit)" .
  qed
 qed
 have zenon_L2_: "(~((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))) \\in (votes[(CHOOSE x:(~((x \\in Node)=>(((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=x)&(a_voteshash_primea=a_voteshash_primea))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))), (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))) \\in (a_voteshash_primea[x])))))))]))) ==> ((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))) \\in (a_voteshash_primea[(CHOOSE x:(~((x \\in Node)=>(((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=x)&(a_voteshash_primea=a_voteshash_primea))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))), (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))) \\in (a_voteshash_primea[x])))))))])) ==> (a_voteshash_primea=votes) ==> FALSE" (is "?z_hiz ==> ?z_hjb ==> ?z_hgp ==> FALSE")
 proof -
  assume z_Hiz:"?z_hiz" (is "~?z_hja")
  assume z_Hjb:"?z_hjb"
  assume z_Hgp:"?z_hgp"
  show FALSE
  proof (rule notE [OF z_Hiz])
   have z_Hjc: "((a_voteshash_primea[(CHOOSE x:(~((x \\in Node)=>(((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=x)&(a_voteshash_primea=a_voteshash_primea))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))), (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))) \\in (a_voteshash_primea[x])))))))])=(votes[(CHOOSE x:(~((x \\in Node)=>(((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=x)&(a_voteshash_primea=a_voteshash_primea))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))), (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))) \\in (a_voteshash_primea[x])))))))]))" (is "?z_hgx=?z_hit")
   proof (rule zenon_nnpp [of "(?z_hgx=?z_hit)"])
    assume z_Hgw:"(?z_hgx~=?z_hit)"
    show FALSE
    by (rule zenon_L1_ [OF z_Hgw z_Hgp])
   qed
   have z_Hja: "?z_hja"
   by (rule subst [where P="(\<lambda>zenon_Vfq. ((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))) \\in zenon_Vfq))", OF z_Hjc], fact z_Hjb)
   thus "?z_hja" .
  qed
 qed
 assume z_Hc:"(~bAll(Node, (\<lambda>VARI. bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARI=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, VARI>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))" (is "~?z_hjg")
 have z_Hd: "?z_hd" (is "?z_he&?z_hbh")
 by (rule zenon_and_0 [OF z_Ha])
 have z_Hbh: "?z_hbh" (is "?z_hbi&?z_hcb")
 by (rule zenon_and_1 [OF z_Hd])
 have z_Hcb: "?z_hcb" (is "?z_hcc&?z_hco")
 by (rule zenon_and_1 [OF z_Hbh])
 have z_Hcc: "?z_hcc"
 by (rule zenon_and_0 [OF z_Hcb])
 have z_Hco: "?z_hco" (is "?z_hcp&?z_hdd")
 by (rule zenon_and_1 [OF z_Hcb])
 have z_Hdd: "?z_hdd" (is "?z_hde&?z_hdn")
 by (rule zenon_and_1 [OF z_Hco])
 have z_Hdn: "?z_hdn" (is "?z_hdo&?z_hdv")
 by (rule zenon_and_1 [OF z_Hdd])
 have z_Hdv: "?z_hdv" (is "?z_hdw&?z_heb")
 by (rule zenon_and_1 [OF z_Hdn])
 have z_Heb: "?z_heb" (is "?z_hec&?z_hes")
 by (rule zenon_and_1 [OF z_Hdv])
 have z_Hes: "?z_hes"
 by (rule zenon_and_1 [OF z_Heb])
 have z_Hjr_z_Hcc: "(\\A x:((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msga)|(~(VARJ \\in (votes[x])))))))) == ?z_hcc" (is "?z_hjr == _")
 by (unfold bAll_def)
 have z_Hjr: "?z_hjr" (is "\\A x : ?z_hka(x)")
 by (unfold z_Hjr_z_Hcc, fact z_Hcc)
 have z_Hkb_z_Hes: "(\\A x:((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(votes=votes))|(~(<<x, VARK>> \\in a_voteunde_msga)))|(~(<<x, VARJ>> \\in a_voteunde_msga))))))))) == ?z_hes" (is "?z_hkb == _")
 by (unfold bAll_def)
 have z_Hkb: "?z_hkb" (is "\\A x : ?z_hkp(x)")
 by (unfold z_Hkb_z_Hes, fact z_Hes)
 have z_Hkq_z_Hb: "(\\E x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(<<x, j>> \\in a_requnde_historya))&(bAll(Node, (\<lambda>a_dst2a. (~(<<x, a_dst2a>> \\in a_voteunde_requestunde_msga))))&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\cup {<<x, j>>}))&((a_requnde_historyhash_primea=(a_requnde_historya \\cup {<<x, j>>}))&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_voteshash_primea=votes)&((a_leaderhash_primea=leader)&(a_decidedhash_primea=decided))))))))))))) == ?z_hb" (is "?z_hkq == _")
 by (unfold bEx_def)
 have z_Hkq: "?z_hkq" (is "\\E x : ?z_hll(x)")
 by (unfold z_Hkq_z_Hb, fact z_Hb)
 have z_Hlm: "?z_hll((CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(<<x, j>> \\in a_requnde_historya))&(bAll(Node, (\<lambda>a_dst2a. (~(<<x, a_dst2a>> \\in a_voteunde_requestunde_msga))))&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\cup {<<x, j>>}))&((a_requnde_historyhash_primea=(a_requnde_historya \\cup {<<x, j>>}))&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_voteshash_primea=votes)&((a_leaderhash_primea=leader)&(a_decidedhash_primea=decided))))))))))))))" (is "?z_hlo&?z_hlp")
 by (rule zenon_ex_choose_0 [of "?z_hll", OF z_Hkq])
 have z_Hlp: "?z_hlp"
 by (rule zenon_and_1 [OF z_Hlm])
 have z_Hlq_z_Hlp: "(\\E x:((x \\in Node)&((~(<<(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(<<x, j>> \\in a_requnde_historya))&(bAll(Node, (\<lambda>a_dst2a. (~(<<x, a_dst2a>> \\in a_voteunde_requestunde_msga))))&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\cup {<<x, j>>}))&((a_requnde_historyhash_primea=(a_requnde_historya \\cup {<<x, j>>}))&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_voteshash_primea=votes)&((a_leaderhash_primea=leader)&(a_decidedhash_primea=decided))))))))))))), x>> \\in a_requnde_historya))&(bAll(Node, (\<lambda>a_dst2a. (~(<<(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(<<x, j>> \\in a_requnde_historya))&(bAll(Node, (\<lambda>a_dst2a. (~(<<x, a_dst2a>> \\in a_voteunde_requestunde_msga))))&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\cup {<<x, j>>}))&((a_requnde_historyhash_primea=(a_requnde_historya \\cup {<<x, j>>}))&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_voteshash_primea=votes)&((a_leaderhash_primea=leader)&(a_decidedhash_primea=decided))))))))))))), a_dst2a>> \\in a_voteunde_requestunde_msga))))&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\cup {<<(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(<<x, j>> \\in a_requnde_historya))&(bAll(Node, (\<lambda>a_dst2a. (~(<<x, a_dst2a>> \\in a_voteunde_requestunde_msga))))&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\cup {<<x, j>>}))&((a_requnde_historyhash_primea=(a_requnde_historya \\cup {<<x, j>>}))&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_voteshash_primea=votes)&((a_leaderhash_primea=leader)&(a_decidedhash_primea=decided))))))))))))), x>>}))&((a_requnde_historyhash_primea=(a_requnde_historya \\cup {<<(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(<<x, j>> \\in a_requnde_historya))&(bAll(Node, (\<lambda>a_dst2a. (~(<<x, a_dst2a>> \\in a_voteunde_requestunde_msga))))&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\cup {<<x, j>>}))&((a_requnde_historyhash_primea=(a_requnde_historya \\cup {<<x, j>>}))&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_voteshash_primea=votes)&((a_leaderhash_primea=leader)&(a_decidedhash_primea=decided))))))))))))), x>>}))&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_voteshash_primea=votes)&((a_leaderhash_primea=leader)&(a_decidedhash_primea=decided))))))))))) == ?z_hlp" (is "?z_hlq == _")
 by (unfold bEx_def)
 have z_Hlq: "?z_hlq" (is "\\E x : ?z_hmj(x)")
 by (unfold z_Hlq_z_Hlp, fact z_Hlp)
 have z_Hmk: "?z_hmj((CHOOSE x:((x \\in Node)&((~(<<(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(<<x, j>> \\in a_requnde_historya))&(bAll(Node, (\<lambda>a_dst2a. (~(<<x, a_dst2a>> \\in a_voteunde_requestunde_msga))))&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\cup {<<x, j>>}))&((a_requnde_historyhash_primea=(a_requnde_historya \\cup {<<x, j>>}))&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_voteshash_primea=votes)&((a_leaderhash_primea=leader)&(a_decidedhash_primea=decided))))))))))))), x>> \\in a_requnde_historya))&(bAll(Node, (\<lambda>a_dst2a. (~(<<(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(<<x, j>> \\in a_requnde_historya))&(bAll(Node, (\<lambda>a_dst2a. (~(<<x, a_dst2a>> \\in a_voteunde_requestunde_msga))))&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\cup {<<x, j>>}))&((a_requnde_historyhash_primea=(a_requnde_historya \\cup {<<x, j>>}))&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_voteshash_primea=votes)&((a_leaderhash_primea=leader)&(a_decidedhash_primea=decided))))))))))))), a_dst2a>> \\in a_voteunde_requestunde_msga))))&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\cup {<<(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(<<x, j>> \\in a_requnde_historya))&(bAll(Node, (\<lambda>a_dst2a. (~(<<x, a_dst2a>> \\in a_voteunde_requestunde_msga))))&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\cup {<<x, j>>}))&((a_requnde_historyhash_primea=(a_requnde_historya \\cup {<<x, j>>}))&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_voteshash_primea=votes)&((a_leaderhash_primea=leader)&(a_decidedhash_primea=decided))))))))))))), x>>}))&((a_requnde_historyhash_primea=(a_requnde_historya \\cup {<<(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(<<x, j>> \\in a_requnde_historya))&(bAll(Node, (\<lambda>a_dst2a. (~(<<x, a_dst2a>> \\in a_voteunde_requestunde_msga))))&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\cup {<<x, j>>}))&((a_requnde_historyhash_primea=(a_requnde_historya \\cup {<<x, j>>}))&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_voteshash_primea=votes)&((a_leaderhash_primea=leader)&(a_decidedhash_primea=decided))))))))))))), x>>}))&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_voteshash_primea=votes)&((a_leaderhash_primea=leader)&(a_decidedhash_primea=decided))))))))))))" (is "?z_hmm&?z_hmn")
 by (rule zenon_ex_choose_0 [of "?z_hmj", OF z_Hlq])
 have z_Hmn: "?z_hmn" (is "?z_hmo&?z_hmp")
 by (rule zenon_and_1 [OF z_Hmk])
 have z_Hmp: "?z_hmp" (is "?z_hlx&?z_hmq")
 by (rule zenon_and_1 [OF z_Hmn])
 have z_Hmq: "?z_hmq" (is "?z_hmr&?z_hms")
 by (rule zenon_and_1 [OF z_Hmp])
 have z_Hms: "?z_hms" (is "?z_hmt&?z_hgi")
 by (rule zenon_and_1 [OF z_Hmq])
 have z_Hgi: "?z_hgi" (is "?z_hgj&?z_hgl")
 by (rule zenon_and_1 [OF z_Hms])
 have z_Hgl: "?z_hgl" (is "?z_hgm&?z_hgo")
 by (rule zenon_and_1 [OF z_Hgi])
 have z_Hgm: "?z_hgm"
 by (rule zenon_and_0 [OF z_Hgl])
 have z_Hgo: "?z_hgo" (is "?z_hgp&?z_hgr")
 by (rule zenon_and_1 [OF z_Hgl])
 have z_Hgp: "?z_hgp"
 by (rule zenon_and_0 [OF z_Hgo])
 have z_Hmu_z_Hc: "(~(\\A x:((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK]))))))))))) == (~?z_hjg)" (is "?z_hmu == ?z_hc")
 by (unfold bAll_def)
 have z_Hmu: "?z_hmu" (is "~(\\A x : ?z_hmw(x))")
 by (unfold z_Hmu_z_Hc, fact z_Hc)
 have z_Hmx: "(\\E x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))" (is "\\E x : ?z_hmy(x)")
 by (rule zenon_notallex_0 [of "?z_hmw", OF z_Hmu])
 have z_Hmz: "?z_hmy((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK]))))))))))))" (is "~(?z_hna=>?z_hnb)")
 by (rule zenon_ex_choose_0 [of "?z_hmy", OF z_Hmx])
 have z_Hna: "?z_hna"
 by (rule zenon_notimply_0 [OF z_Hmz])
 have z_Hnc: "(~?z_hnb)"
 by (rule zenon_notimply_1 [OF z_Hmz])
 have z_Hnd_z_Hnc: "(~(\\A x:((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))) == (~?z_hnb)" (is "?z_hnd == ?z_hnc")
 by (unfold bAll_def)
 have z_Hnd: "?z_hnd" (is "~(\\A x : ?z_hnf(x))")
 by (unfold z_Hnd_z_Hnc, fact z_Hnc)
 have z_Hng: "(\\E x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK])))))))))" (is "\\E x : ?z_hnh(x)")
 by (rule zenon_notallex_0 [of "?z_hnf", OF z_Hnd])
 have z_Hni: "?z_hnh((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))))" (is "~(?z_hnj=>?z_hnk)")
 by (rule zenon_ex_choose_0 [of "?z_hnh", OF z_Hng])
 have z_Hnj: "?z_hnj"
 by (rule zenon_notimply_0 [OF z_Hni])
 have z_Hnl: "(~?z_hnk)"
 by (rule zenon_notimply_1 [OF z_Hni])
 have z_Hnm_z_Hnl: "(~(\\A x:((x \\in Node)=>(((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=x)&(a_voteshash_primea=a_voteshash_primea))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))), (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))) \\in (a_voteshash_primea[x]))))))) == (~?z_hnk)" (is "?z_hnm == ?z_hnl")
 by (unfold bAll_def)
 have z_Hnm: "?z_hnm" (is "~(\\A x : ?z_hno(x))")
 by (unfold z_Hnm_z_Hnl, fact z_Hnl)
 have z_Hnp: "(\\E x:(~((x \\in Node)=>(((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=x)&(a_voteshash_primea=a_voteshash_primea))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))), (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))) \\in (a_voteshash_primea[x])))))))" (is "\\E x : ?z_hnq(x)")
 by (rule zenon_notallex_0 [of "?z_hno", OF z_Hnm])
 have z_Hnr: "?z_hnq((CHOOSE x:(~((x \\in Node)=>(((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=x)&(a_voteshash_primea=a_voteshash_primea))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))), (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))) \\in (a_voteshash_primea[x]))))))))" (is "~(?z_hns=>?z_hnt)")
 by (rule zenon_ex_choose_0 [of "?z_hnq", OF z_Hnp])
 have z_Hns: "?z_hns"
 by (rule zenon_notimply_0 [OF z_Hnr])
 have z_Hnu: "(~?z_hnt)" (is "~(?z_hnv|?z_hnw)")
 by (rule zenon_notimply_1 [OF z_Hnr])
 have z_Hnx: "(~?z_hnv)" (is "~(?z_hny|?z_hhz)")
 by (rule zenon_notor_0 [OF z_Hnu])
 have z_Hnz: "(~?z_hnw)" (is "~~?z_hjb")
 by (rule zenon_notor_1 [OF z_Hnu])
 have z_Hjb: "?z_hjb"
 by (rule zenon_notnot_0 [OF z_Hnz])
 have z_Hoa: "(~?z_hny)" (is "~(?z_hob&?z_hhs)")
 by (rule zenon_notor_0 [OF z_Hnx])
 have z_Hoc: "(~?z_hhz)" (is "~~?z_hia")
 by (rule zenon_notor_1 [OF z_Hnx])
 have z_Hia: "?z_hia"
 by (rule zenon_notnot_0 [OF z_Hoc])
 show FALSE
 proof (rule zenon_notand [OF z_Hoa])
  assume z_Hod:"((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&?z_hhs)|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))~=(CHOOSE x:(~((x \\in Node)=>(((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&?z_hhs)|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=x)&?z_hhs)|?z_hhz)|(~((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&?z_hhs)|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&?z_hhs)|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&?z_hhs)|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))) \\in (a_voteshash_primea[x]))))))))" (is "?z_hhh~=?z_hgy")
  have z_Hoe: "(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. ((((?z_hhh=VARK)&?z_hhs)|(~(<<x, ?z_hhh>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))), ?z_hhh>> \\in a_voteunde_msga)" (is "?z_hoe")
  by (rule subst [where P="(\<lambda>zenon_Vjc. (<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. ((((?z_hhh=VARK)&?z_hhs)|(~(<<x, ?z_hhh>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))), ?z_hhh>> \\in zenon_Vjc))", OF z_Hgm z_Hia])
  have z_Hoi: "?z_hka(?z_hgy)" (is "_=>?z_hoj")
  by (rule zenon_all_0 [of "?z_hka" "?z_hgy", OF z_Hjr])
  show FALSE
  proof (rule zenon_imply [OF z_Hoi])
   assume z_Hok:"(~?z_hns)"
   show FALSE
   by (rule notE [OF z_Hok z_Hns])
  next
   assume z_Hoj:"?z_hoj"
   have z_Hol_z_Hoj: "(\\A x:((x \\in Node)=>((<<x, ?z_hgy>> \\in a_voteunde_msga)|(~(x \\in (votes[?z_hgy])))))) == ?z_hoj" (is "?z_hol == _")
   by (unfold bAll_def)
   have z_Hol: "?z_hol" (is "\\A x : ?z_hos(x)")
   by (unfold z_Hol_z_Hoj, fact z_Hoj)
   have z_Hot: "?z_hkp((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. ((((?z_hhh=VARK)&?z_hhs)|(~(<<x, ?z_hhh>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))))" (is "_=>?z_hou")
   by (rule zenon_all_0 [of "?z_hkp" "(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. ((((?z_hhh=VARK)&?z_hhs)|(~(<<x, ?z_hhh>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK])))))))))", OF z_Hkb])
   show FALSE
   proof (rule zenon_imply [OF z_Hot])
    assume z_Hov:"(~?z_hnj)"
    show FALSE
    by (rule notE [OF z_Hov z_Hnj])
   next
    assume z_Hou:"?z_hou"
    have z_How_z_Hou: "(\\A x:((x \\in Node)=>bAll(Node, (\<lambda>VARK. ((((x=VARK)&(votes=votes))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. ((((?z_hhh=VARK)&?z_hhs)|(~(<<x, ?z_hhh>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))), VARK>> \\in a_voteunde_msga)))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. ((((?z_hhh=VARK)&?z_hhs)|(~(<<x, ?z_hhh>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))), x>> \\in a_voteunde_msga))))))) == ?z_hou" (is "?z_how == _")
    by (unfold bAll_def)
    have z_How: "?z_how" (is "\\A x : ?z_hpj(x)")
    by (unfold z_How_z_Hou, fact z_Hou)
    have z_Hpk: "?z_hos((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. ((((?z_hhh=VARK)&?z_hhs)|(~(<<x, ?z_hhh>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))))" (is "_=>?z_hpl")
    by (rule zenon_all_0 [of "?z_hos" "(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. ((((?z_hhh=VARK)&?z_hhs)|(~(<<x, ?z_hhh>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK])))))))))", OF z_Hol])
    show FALSE
    proof (rule zenon_imply [OF z_Hpk])
     assume z_Hov:"(~?z_hnj)"
     show FALSE
     by (rule notE [OF z_Hov z_Hnj])
    next
     assume z_Hpl:"?z_hpl" (is "?z_hpm|?z_hiz")
     show FALSE
     proof (rule zenon_or [OF z_Hpl])
      assume z_Hpm:"?z_hpm"
      have z_Hpn: "?z_hpj(?z_hhh)" (is "_=>?z_hpo")
      by (rule zenon_all_0 [of "?z_hpj" "?z_hhh", OF z_How])
      show FALSE
      proof (rule zenon_imply [OF z_Hpn])
       assume z_Hpp:"(~?z_hna)"
       show FALSE
       by (rule notE [OF z_Hpp z_Hna])
      next
       assume z_Hpo:"?z_hpo"
       have z_Hpq_z_Hpo: "(\\A x:((x \\in Node)=>((((?z_hhh=x)&(votes=votes))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. ((((?z_hhh=VARK)&?z_hhs)|(~(<<x, ?z_hhh>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))), x>> \\in a_voteunde_msga)))|(~?z_hoe)))) == ?z_hpo" (is "?z_hpq == _")
       by (unfold bAll_def)
       have z_Hpq: "?z_hpq" (is "\\A x : ?z_hpw(x)")
       by (unfold z_Hpq_z_Hpo, fact z_Hpo)
       have z_Hpx: "?z_hpw(?z_hgy)" (is "_=>?z_hpy")
       by (rule zenon_all_0 [of "?z_hpw" "?z_hgy", OF z_Hpq])
       show FALSE
       proof (rule zenon_imply [OF z_Hpx])
        assume z_Hok:"(~?z_hns)"
        show FALSE
        by (rule notE [OF z_Hok z_Hns])
       next
        assume z_Hpy:"?z_hpy" (is "?z_hpz|?z_hpv")
        show FALSE
        proof (rule zenon_or [OF z_Hpy])
         assume z_Hpz:"?z_hpz" (is "?z_hqa|?z_hqb")
         show FALSE
         proof (rule zenon_or [OF z_Hpz])
          assume z_Hqa:"?z_hqa" (is "_&?z_hen")
          have z_Hob: "?z_hob"
          by (rule zenon_and_0 [OF z_Hqa])
          show FALSE
          by (rule notE [OF z_Hod z_Hob])
         next
          assume z_Hqb:"?z_hqb"
          show FALSE
          by (rule notE [OF z_Hqb z_Hpm])
         qed
        next
         assume z_Hpv:"?z_hpv"
         show FALSE
         by (rule notE [OF z_Hpv z_Hoe])
        qed
       qed
      qed
     next
      assume z_Hiz:"?z_hiz" (is "~?z_hja")
      show FALSE
      by (rule zenon_L2_ [OF z_Hiz z_Hjb z_Hgp])
     qed
    qed
   qed
  qed
 next
  assume z_Hqc:"(a_voteshash_primea~=a_voteshash_primea)"
  show FALSE
  by (rule zenon_noteq [OF z_Hqc])
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 212"; *} qed
lemma ob'210:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
fixes Node
fixes Quorum
fixes Value
fixes a_voteunde_requestunde_msga a_voteunde_requestunde_msga'
fixes voted voted'
fixes a_voteunde_msga a_voteunde_msga'
fixes votes votes'
fixes leader leader'
fixes decided decided'
fixes a_requnde_historya a_requnde_historya'
(* usable definition vars suppressed *)
(* usable definition ProtocolNext suppressed *)
(* usable definition OtherNext suppressed *)
(* usable definition Spec suppressed *)
(* usable definition Symmetry suppressed *)
(* usable definition Safety suppressed *)
(* usable definition SplitVote suppressed *)
(* usable definition Liveness suppressed *)
assumes v'28: "(((((((a_voteunde_requestunde_msga) \<in> ((SUBSET (((Node) \<times> (Node))))))) & (((voted) \<in> ([(Node) \<rightarrow> (BOOLEAN)]))) & (((a_voteunde_msga) \<in> ((SUBSET (((Node) \<times> (Node))))))) & (((votes) \<in> ([(Node) \<rightarrow> ((SUBSET (Node)))]))) & (((leader) \<in> ([(Node) \<rightarrow> (BOOLEAN)]))) & (((decided) \<in> ([(Node) \<rightarrow> ((SUBSET (Value)))])))) & (\<forall> a_n1a \<in> (Node) : (\<forall> a_n2a \<in> (Node) : (\<forall> a_v1a \<in> (Value) : (\<forall> a_v2a \<in> (Value) : (((((((a_v1a) \<in> (fapply ((decided), (a_n1a))))) \<and> (((a_v2a) \<in> (fapply ((decided), (a_n2a))))))) \<Rightarrow> (((a_v1a) = (a_v2a))))))))) & (\<forall> VARI \<in> (Node) : (\<forall> VARJ \<in> (Node) : (((((<<(VARJ), (VARI)>>) \<in> (a_voteunde_msga))) \<or> ((~ (((VARJ) \<in> (fapply ((votes), (VARI))))))))))) & (\<forall> VARI \<in> (Node) : (\<exists> QJ \<in> (Quorum) : (\<forall> VALI \<in> (Value) : (((((QJ) \<subseteq> (fapply ((votes), (VARI))))) \<or> ((~ (((VALI) \<in> (fapply ((decided), (VARI)))))))))))) & (\<forall> VARI \<in> (Node) : (\<forall> VARJ \<in> (Node) : (((fapply ((voted), (VARI))) \<or> ((~ (((<<(VARI), (VARJ)>>) \<in> (a_voteunde_msga))))))))) & (\<forall> VARI \<in> (Node) : (\<exists> QJ \<in> (Quorum) : (((((QJ) \<subseteq> (fapply ((votes), (VARI))))) \<or> ((~ (fapply ((leader), (VARI))))))))) & (\<forall> VARI \<in> (Node) : (\<forall> VALI \<in> (Value) : (((fapply ((leader), (VARI))) \<or> ((~ (((VALI) \<in> (fapply ((decided), (VARI))))))))))) & (\<forall> VARI \<in> (Node) : (\<forall> VARJ \<in> (Node) : (\<forall> VARK \<in> (Node) : (((((((((VARI) = (VARK))) \<and> (((votes) = (votes))))) \<or> ((~ (((<<(VARJ), (VARI)>>) \<in> (a_voteunde_msga))))))) \<or> ((~ (((VARJ) \<in> (fapply ((votes), (VARK)))))))))))) & (\<forall> VARI \<in> (Node) : (\<forall> VARJ \<in> (Node) : (\<forall> VARK \<in> (Node) : (((((((((VARJ) = (VARK))) \<and> (((votes) = (votes))))) \<or> ((~ (((<<(VARI), (VARK)>>) \<in> (a_voteunde_msga))))))) \<or> ((~ (((<<(VARI), (VARJ)>>) \<in> (a_voteunde_msga))))))))))) \<and> (((ProtocolNext) \<or> (OtherNext)))))"
assumes v'43: "(\<exists> i \<in> (Node) : (\<exists> j \<in> (Node) : ((fapply ((voted), (i))) & ((((a_voteunde_requestunde_msghash_primea :: c)) = (((a_voteunde_requestunde_msga) \\ ({(<<(j), (i)>>)}))))) & ((((a_voteunde_msghash_primea :: c)) = (a_voteunde_msga))) & ((((a_votedhash_primea :: c)) = (voted))) & ((((a_voteshash_primea :: c)) = (votes))) & ((((a_decidedhash_primea :: c)) = (decided))) & ((((a_leaderhash_primea :: c)) = (leader))) & ((((a_requnde_historyhash_primea :: c)) = (a_requnde_historya))))))"
shows "(\<forall> VARI \<in> (Node) : (\<forall> VARJ \<in> (Node) : (\<forall> VARK \<in> (Node) : (((((((((VARI) = (VARK))) \<and> ((((a_voteshash_primea :: c)) = ((a_voteshash_primea :: c)))))) \<or> ((~ (((<<(VARJ), (VARI)>>) \<in> ((a_voteunde_msghash_primea :: c)))))))) \<or> ((~ (((VARJ) \<in> (fapply (((a_voteshash_primea :: c)), (VARK))))))))))))"(is "PROP ?ob'210")
proof -
ML_command {* writeln "*** TLAPS ENTER 210"; *}
show "PROP ?ob'210"

(* BEGIN ZENON INPUT
;; file=consensus_epr_IndProofs.tlaps/tlapm_e072b7.znn; PATH='/home/egolf/.opam/4.07.1/bin:/home/egolf/.local/bin:/home/egolf/bin:/home/egolf/mambaforge/bin:/home/egolf/mambaforge/condabin:/home/egolf/.opam/4.07.1/bin:/home/egolf/.local/bin:/home/egolf/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/home/egolf/.local/bin/gurobi952/linux64/bin:/home/egolf/Projects/apalache/bin:/home/egolf/opt/foxitsoftware/foxitreader:/home/egolf/.local/bin/gurobi952/linux64/bin:/home/egolf/Projects/apalache/bin:/home/egolf/opt/foxitsoftware/foxitreader:/usr/local/bin:/usr/local/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >consensus_epr_IndProofs.tlaps/tlapm_e072b7.znn.out
;; obligation #210
$hyp "v'28" (/\ (/\ (/\ (TLA.in a_voteunde_requestunde_msga
(TLA.SUBSET (TLA.prod Node Node))) (TLA.in voted
(TLA.FuncSet Node (TLA.set T. F.))) (TLA.in a_voteunde_msga
(TLA.SUBSET (TLA.prod Node Node))) (TLA.in votes
(TLA.FuncSet Node (TLA.SUBSET Node))) (TLA.in leader
(TLA.FuncSet Node (TLA.set T. F.))) (TLA.in decided
(TLA.FuncSet Node (TLA.SUBSET Value))))
(TLA.bAll Node ((a_n1a) (TLA.bAll Node ((a_n2a) (TLA.bAll Value ((a_v1a) (TLA.bAll Value ((a_v2a) (=> (/\ (TLA.in a_v1a
(TLA.fapply decided a_n1a)) (TLA.in a_v2a (TLA.fapply decided a_n2a)))
(= a_v1a a_v2a))))))))))
(TLA.bAll Node ((VARI) (TLA.bAll Node ((VARJ) (\/ (TLA.in (TLA.tuple VARJ
VARI) a_voteunde_msga) (-. (TLA.in VARJ (TLA.fapply votes VARI))))))))
(TLA.bAll Node ((VARI) (TLA.bEx Quorum ((QJ) (TLA.bAll Value ((VALI) (\/ (TLA.subseteq QJ
(TLA.fapply votes VARI)) (-. (TLA.in VALI (TLA.fapply decided VARI))))))))))
(TLA.bAll Node ((VARI) (TLA.bAll Node ((VARJ) (\/ (TLA.fapply voted VARI)
(-. (TLA.in (TLA.tuple VARI VARJ) a_voteunde_msga)))))))
(TLA.bAll Node ((VARI) (TLA.bEx Quorum ((QJ) (\/ (TLA.subseteq QJ
(TLA.fapply votes VARI)) (-. (TLA.fapply leader VARI)))))))
(TLA.bAll Node ((VARI) (TLA.bAll Value ((VALI) (\/ (TLA.fapply leader VARI)
(-. (TLA.in VALI (TLA.fapply decided VARI))))))))
(TLA.bAll Node ((VARI) (TLA.bAll Node ((VARJ) (TLA.bAll Node ((VARK) (\/ (\/ (/\ (= VARI
VARK) (= votes votes)) (-. (TLA.in (TLA.tuple VARJ VARI) a_voteunde_msga)))
(-. (TLA.in VARJ (TLA.fapply votes VARK))))))))))
(TLA.bAll Node ((VARI) (TLA.bAll Node ((VARJ) (TLA.bAll Node ((VARK) (\/ (\/ (/\ (= VARJ
VARK) (= votes votes)) (-. (TLA.in (TLA.tuple VARI VARK) a_voteunde_msga)))
(-. (TLA.in (TLA.tuple VARI VARJ) a_voteunde_msga)))))))))) (\/ ProtocolNext
OtherNext))
$hyp "v'43" (TLA.bEx Node ((i) (TLA.bEx Node ((j) (/\ (TLA.fapply voted i)
(= a_voteunde_requestunde_msghash_primea
(TLA.setminus a_voteunde_requestunde_msga (TLA.set (TLA.tuple j i))))
(= a_voteunde_msghash_primea a_voteunde_msga) (= a_votedhash_primea voted)
(= a_voteshash_primea votes) (= a_decidedhash_primea decided)
(= a_leaderhash_primea leader) (= a_requnde_historyhash_primea
a_requnde_historya))))))
$goal (TLA.bAll Node ((VARI) (TLA.bAll Node ((VARJ) (TLA.bAll Node ((VARK) (\/ (\/ (/\ (= VARI
VARK) (= a_voteshash_primea a_voteshash_primea)) (-. (TLA.in (TLA.tuple VARJ
VARI) a_voteunde_msghash_primea))) (-. (TLA.in VARJ
(TLA.fapply a_voteshash_primea VARK))))))))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Ha:"((((a_voteunde_requestunde_msga \\in SUBSET(prod(Node, Node)))&((voted \\in FuncSet(Node, {TRUE, FALSE}))&((a_voteunde_msga \\in SUBSET(prod(Node, Node)))&((votes \\in FuncSet(Node, SUBSET(Node)))&((leader \\in FuncSet(Node, {TRUE, FALSE}))&(decided \\in FuncSet(Node, SUBSET(Value))))))))&(bAll(Node, (\<lambda>a_n1a. bAll(Node, (\<lambda>a_n2a. bAll(Value, (\<lambda>a_v1a. bAll(Value, (\<lambda>a_v2a. (((a_v1a \\in (decided[a_n1a]))&(a_v2a \\in (decided[a_n2a])))=>(a_v1a=a_v2a))))))))))&(bAll(Node, (\<lambda>VARI. bAll(Node, (\<lambda>VARJ. ((<<VARJ, VARI>> \\in a_voteunde_msga)|(~(VARJ \\in (votes[VARI]))))))))&(bAll(Node, (\<lambda>VARI. bEx(Quorum, (\<lambda>QJ. bAll(Value, (\<lambda>VALI. ((QJ \\subseteq (votes[VARI]))|(~(VALI \\in (decided[VARI]))))))))))&(bAll(Node, (\<lambda>VARI. bAll(Node, (\<lambda>VARJ. ((voted[VARI])|(~(<<VARI, VARJ>> \\in a_voteunde_msga)))))))&(bAll(Node, (\<lambda>VARI. bEx(Quorum, (\<lambda>QJ. ((QJ \\subseteq (votes[VARI]))|(~(leader[VARI])))))))&(bAll(Node, (\<lambda>VARI. bAll(Value, (\<lambda>VALI. ((leader[VARI])|(~(VALI \\in (decided[VARI]))))))))&(bAll(Node, (\<lambda>VARI. bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARI=VARK)&(votes=votes))|(~(<<VARJ, VARI>> \\in a_voteunde_msga)))|(~(VARJ \\in (votes[VARK]))))))))))&bAll(Node, (\<lambda>VARI. bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(votes=votes))|(~(<<VARI, VARK>> \\in a_voteunde_msga)))|(~(<<VARI, VARJ>> \\in a_voteunde_msga)))))))))))))))))&(ProtocolNext|OtherNext))" (is "?z_hd&?z_hff")
 using v'28 by blast
 have z_Hb:"bEx(Node, (\<lambda>i. bEx(Node, (\<lambda>j. ((voted[i])&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, i>>}))&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_votedhash_primea=voted)&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))" (is "?z_hb")
 using v'43 by blast
 have zenon_L1_: "((a_voteshash_primea[(CHOOSE x:(~((x \\in Node)=>(((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=x)&(a_voteshash_primea=a_voteshash_primea))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))), (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))) \\in (a_voteshash_primea[x])))))))])~=(votes[(CHOOSE x:(~((x \\in Node)=>(((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=x)&(a_voteshash_primea=a_voteshash_primea))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))), (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))) \\in (a_voteshash_primea[x])))))))])) ==> (a_voteshash_primea=votes) ==> FALSE" (is "?z_hgn ==> ?z_hgc ==> FALSE")
 proof -
  assume z_Hgn:"?z_hgn" (is "?z_hgo~=?z_hik")
  assume z_Hgc:"?z_hgc"
  show FALSE
  proof (rule zenon_noteq [of "?z_hik"])
   have z_Hil: "(?z_hik~=?z_hik)"
   by (rule subst [where P="(\<lambda>zenon_Vyp. ((zenon_Vyp[(CHOOSE x:(~((x \\in Node)=>(((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=x)&(a_voteshash_primea=a_voteshash_primea))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))), (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))) \\in (a_voteshash_primea[x])))))))])~=?z_hik))", OF z_Hgc], fact z_Hgn)
   thus "(?z_hik~=?z_hik)" .
  qed
 qed
 have zenon_L2_: "(~((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))) \\in (votes[(CHOOSE x:(~((x \\in Node)=>(((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=x)&(a_voteshash_primea=a_voteshash_primea))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))), (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))) \\in (a_voteshash_primea[x])))))))]))) ==> ((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))) \\in (a_voteshash_primea[(CHOOSE x:(~((x \\in Node)=>(((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=x)&(a_voteshash_primea=a_voteshash_primea))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))), (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))) \\in (a_voteshash_primea[x])))))))])) ==> (a_voteshash_primea=votes) ==> FALSE" (is "?z_hiq ==> ?z_his ==> ?z_hgc ==> FALSE")
 proof -
  assume z_Hiq:"?z_hiq" (is "~?z_hir")
  assume z_His:"?z_his"
  assume z_Hgc:"?z_hgc"
  show FALSE
  proof (rule notE [OF z_Hiq])
   have z_Hit: "((a_voteshash_primea[(CHOOSE x:(~((x \\in Node)=>(((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=x)&(a_voteshash_primea=a_voteshash_primea))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))), (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))) \\in (a_voteshash_primea[x])))))))])=(votes[(CHOOSE x:(~((x \\in Node)=>(((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=x)&(a_voteshash_primea=a_voteshash_primea))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))), (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))) \\in (a_voteshash_primea[x])))))))]))" (is "?z_hgo=?z_hik")
   proof (rule zenon_nnpp [of "(?z_hgo=?z_hik)"])
    assume z_Hgn:"(?z_hgo~=?z_hik)"
    show FALSE
    by (rule zenon_L1_ [OF z_Hgn z_Hgc])
   qed
   have z_Hir: "?z_hir"
   by (rule subst [where P="(\<lambda>zenon_Vzp. ((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))) \\in zenon_Vzp))", OF z_Hit], fact z_His)
   thus "?z_hir" .
  qed
 qed
 assume z_Hc:"(~bAll(Node, (\<lambda>VARI. bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARI=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, VARI>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))" (is "~?z_hix")
 have z_Hd: "?z_hd" (is "?z_he&?z_hbh")
 by (rule zenon_and_0 [OF z_Ha])
 have z_Hbh: "?z_hbh" (is "?z_hbi&?z_hcb")
 by (rule zenon_and_1 [OF z_Hd])
 have z_Hcb: "?z_hcb" (is "?z_hcc&?z_hco")
 by (rule zenon_and_1 [OF z_Hbh])
 have z_Hcc: "?z_hcc"
 by (rule zenon_and_0 [OF z_Hcb])
 have z_Hco: "?z_hco" (is "?z_hcp&?z_hdd")
 by (rule zenon_and_1 [OF z_Hcb])
 have z_Hdd: "?z_hdd" (is "?z_hde&?z_hdn")
 by (rule zenon_and_1 [OF z_Hco])
 have z_Hdn: "?z_hdn" (is "?z_hdo&?z_hdv")
 by (rule zenon_and_1 [OF z_Hdd])
 have z_Hdv: "?z_hdv" (is "?z_hdw&?z_heb")
 by (rule zenon_and_1 [OF z_Hdn])
 have z_Heb: "?z_heb" (is "?z_hec&?z_hes")
 by (rule zenon_and_1 [OF z_Hdv])
 have z_Hes: "?z_hes"
 by (rule zenon_and_1 [OF z_Heb])
 have z_Hji_z_Hcc: "(\\A x:((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msga)|(~(VARJ \\in (votes[x])))))))) == ?z_hcc" (is "?z_hji == _")
 by (unfold bAll_def)
 have z_Hji: "?z_hji" (is "\\A x : ?z_hjr(x)")
 by (unfold z_Hji_z_Hcc, fact z_Hcc)
 have z_Hjs_z_Hes: "(\\A x:((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(votes=votes))|(~(<<x, VARK>> \\in a_voteunde_msga)))|(~(<<x, VARJ>> \\in a_voteunde_msga))))))))) == ?z_hes" (is "?z_hjs == _")
 by (unfold bAll_def)
 have z_Hjs: "?z_hjs" (is "\\A x : ?z_hkg(x)")
 by (unfold z_Hjs_z_Hes, fact z_Hes)
 have z_Hkh_z_Hb: "(\\E x:((x \\in Node)&bEx(Node, (\<lambda>j. ((voted[x])&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_votedhash_primea=voted)&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))) == ?z_hb" (is "?z_hkh == _")
 by (unfold bEx_def)
 have z_Hkh: "?z_hkh" (is "\\E x : ?z_hks(x)")
 by (unfold z_Hkh_z_Hb, fact z_Hb)
 have z_Hkt: "?z_hks((CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((voted[x])&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_votedhash_primea=voted)&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))" (is "?z_hkv&?z_hkw")
 by (rule zenon_ex_choose_0 [of "?z_hks", OF z_Hkh])
 have z_Hkw: "?z_hkw"
 by (rule zenon_and_1 [OF z_Hkt])
 have z_Hkx_z_Hkw: "(\\E x:((x \\in Node)&((voted[(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((voted[x])&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_votedhash_primea=voted)&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))])&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<x, (CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((voted[x])&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_votedhash_primea=voted)&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))>>}))&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_votedhash_primea=voted)&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))) == ?z_hkw" (is "?z_hkx == _")
 by (unfold bEx_def)
 have z_Hkx: "?z_hkx" (is "\\E x : ?z_hlg(x)")
 by (unfold z_Hkx_z_Hkw, fact z_Hkw)
 have z_Hlh: "?z_hlg((CHOOSE x:((x \\in Node)&((voted[(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((voted[x])&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_votedhash_primea=voted)&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))])&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<x, (CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((voted[x])&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_votedhash_primea=voted)&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))>>}))&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_votedhash_primea=voted)&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))" (is "?z_hlj&?z_hlk")
 by (rule zenon_ex_choose_0 [of "?z_hlg", OF z_Hkx])
 have z_Hlk: "?z_hlk" (is "?z_hla&?z_hll")
 by (rule zenon_and_1 [OF z_Hlh])
 have z_Hll: "?z_hll" (is "?z_hlm&?z_hfv")
 by (rule zenon_and_1 [OF z_Hlk])
 have z_Hfv: "?z_hfv" (is "?z_hfw&?z_hfy")
 by (rule zenon_and_1 [OF z_Hll])
 have z_Hfw: "?z_hfw"
 by (rule zenon_and_0 [OF z_Hfv])
 have z_Hfy: "?z_hfy" (is "?z_hfz&?z_hgb")
 by (rule zenon_and_1 [OF z_Hfv])
 have z_Hgb: "?z_hgb" (is "?z_hgc&?z_hge")
 by (rule zenon_and_1 [OF z_Hfy])
 have z_Hgc: "?z_hgc"
 by (rule zenon_and_0 [OF z_Hgb])
 have z_Hln_z_Hc: "(~(\\A x:((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK]))))))))))) == (~?z_hix)" (is "?z_hln == ?z_hc")
 by (unfold bAll_def)
 have z_Hln: "?z_hln" (is "~(\\A x : ?z_hlp(x))")
 by (unfold z_Hln_z_Hc, fact z_Hc)
 have z_Hlq: "(\\E x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))" (is "\\E x : ?z_hlr(x)")
 by (rule zenon_notallex_0 [of "?z_hlp", OF z_Hln])
 have z_Hls: "?z_hlr((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK]))))))))))))" (is "~(?z_hlt=>?z_hlu)")
 by (rule zenon_ex_choose_0 [of "?z_hlr", OF z_Hlq])
 have z_Hlt: "?z_hlt"
 by (rule zenon_notimply_0 [OF z_Hls])
 have z_Hlv: "(~?z_hlu)"
 by (rule zenon_notimply_1 [OF z_Hls])
 have z_Hlw_z_Hlv: "(~(\\A x:((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))) == (~?z_hlu)" (is "?z_hlw == ?z_hlv")
 by (unfold bAll_def)
 have z_Hlw: "?z_hlw" (is "~(\\A x : ?z_hly(x))")
 by (unfold z_Hlw_z_Hlv, fact z_Hlv)
 have z_Hlz: "(\\E x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK])))))))))" (is "\\E x : ?z_hma(x)")
 by (rule zenon_notallex_0 [of "?z_hly", OF z_Hlw])
 have z_Hmb: "?z_hma((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))))" (is "~(?z_hmc=>?z_hmd)")
 by (rule zenon_ex_choose_0 [of "?z_hma", OF z_Hlz])
 have z_Hmc: "?z_hmc"
 by (rule zenon_notimply_0 [OF z_Hmb])
 have z_Hme: "(~?z_hmd)"
 by (rule zenon_notimply_1 [OF z_Hmb])
 have z_Hmf_z_Hme: "(~(\\A x:((x \\in Node)=>(((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=x)&(a_voteshash_primea=a_voteshash_primea))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))), (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))) \\in (a_voteshash_primea[x]))))))) == (~?z_hmd)" (is "?z_hmf == ?z_hme")
 by (unfold bAll_def)
 have z_Hmf: "?z_hmf" (is "~(\\A x : ?z_hmh(x))")
 by (unfold z_Hmf_z_Hme, fact z_Hme)
 have z_Hmi: "(\\E x:(~((x \\in Node)=>(((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=x)&(a_voteshash_primea=a_voteshash_primea))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))), (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))) \\in (a_voteshash_primea[x])))))))" (is "\\E x : ?z_hmj(x)")
 by (rule zenon_notallex_0 [of "?z_hmh", OF z_Hmf])
 have z_Hmk: "?z_hmj((CHOOSE x:(~((x \\in Node)=>(((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=x)&(a_voteshash_primea=a_voteshash_primea))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))), (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))) \\in (a_voteshash_primea[x]))))))))" (is "~(?z_hml=>?z_hmm)")
 by (rule zenon_ex_choose_0 [of "?z_hmj", OF z_Hmi])
 have z_Hml: "?z_hml"
 by (rule zenon_notimply_0 [OF z_Hmk])
 have z_Hmn: "(~?z_hmm)" (is "~(?z_hmo|?z_hmp)")
 by (rule zenon_notimply_1 [OF z_Hmk])
 have z_Hmq: "(~?z_hmo)" (is "~(?z_hmr|?z_hhq)")
 by (rule zenon_notor_0 [OF z_Hmn])
 have z_Hms: "(~?z_hmp)" (is "~~?z_his")
 by (rule zenon_notor_1 [OF z_Hmn])
 have z_His: "?z_his"
 by (rule zenon_notnot_0 [OF z_Hms])
 have z_Hmt: "(~?z_hmr)" (is "~(?z_hmu&?z_hhj)")
 by (rule zenon_notor_0 [OF z_Hmq])
 have z_Hmv: "(~?z_hhq)" (is "~~?z_hhr")
 by (rule zenon_notor_1 [OF z_Hmq])
 have z_Hhr: "?z_hhr"
 by (rule zenon_notnot_0 [OF z_Hmv])
 show FALSE
 proof (rule zenon_notand [OF z_Hmt])
  assume z_Hmw:"((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&?z_hhj)|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))~=(CHOOSE x:(~((x \\in Node)=>(((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&?z_hhj)|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=x)&?z_hhj)|?z_hhq)|(~((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&?z_hhj)|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&?z_hhj)|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&?z_hhj)|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))) \\in (a_voteshash_primea[x]))))))))" (is "?z_hgy~=?z_hgp")
  have z_Hmx: "(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. ((((?z_hgy=VARK)&?z_hhj)|(~(<<x, ?z_hgy>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))), ?z_hgy>> \\in a_voteunde_msga)" (is "?z_hmx")
  by (rule subst [where P="(\<lambda>zenon_Vfc. (<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. ((((?z_hgy=VARK)&?z_hhj)|(~(<<x, ?z_hgy>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))), ?z_hgy>> \\in zenon_Vfc))", OF z_Hfw z_Hhr])
  have z_Hnb: "?z_hjr(?z_hgp)" (is "_=>?z_hnc")
  by (rule zenon_all_0 [of "?z_hjr" "?z_hgp", OF z_Hji])
  show FALSE
  proof (rule zenon_imply [OF z_Hnb])
   assume z_Hnd:"(~?z_hml)"
   show FALSE
   by (rule notE [OF z_Hnd z_Hml])
  next
   assume z_Hnc:"?z_hnc"
   have z_Hne_z_Hnc: "(\\A x:((x \\in Node)=>((<<x, ?z_hgp>> \\in a_voteunde_msga)|(~(x \\in (votes[?z_hgp])))))) == ?z_hnc" (is "?z_hne == _")
   by (unfold bAll_def)
   have z_Hne: "?z_hne" (is "\\A x : ?z_hnl(x)")
   by (unfold z_Hne_z_Hnc, fact z_Hnc)
   have z_Hnm: "?z_hkg((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. ((((?z_hgy=VARK)&?z_hhj)|(~(<<x, ?z_hgy>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))))" (is "_=>?z_hnn")
   by (rule zenon_all_0 [of "?z_hkg" "(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. ((((?z_hgy=VARK)&?z_hhj)|(~(<<x, ?z_hgy>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK])))))))))", OF z_Hjs])
   show FALSE
   proof (rule zenon_imply [OF z_Hnm])
    assume z_Hno:"(~?z_hmc)"
    show FALSE
    by (rule notE [OF z_Hno z_Hmc])
   next
    assume z_Hnn:"?z_hnn"
    have z_Hnp_z_Hnn: "(\\A x:((x \\in Node)=>bAll(Node, (\<lambda>VARK. ((((x=VARK)&(votes=votes))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. ((((?z_hgy=VARK)&?z_hhj)|(~(<<x, ?z_hgy>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))), VARK>> \\in a_voteunde_msga)))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. ((((?z_hgy=VARK)&?z_hhj)|(~(<<x, ?z_hgy>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))), x>> \\in a_voteunde_msga))))))) == ?z_hnn" (is "?z_hnp == _")
    by (unfold bAll_def)
    have z_Hnp: "?z_hnp" (is "\\A x : ?z_hoc(x)")
    by (unfold z_Hnp_z_Hnn, fact z_Hnn)
    have z_Hod: "?z_hnl((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. ((((?z_hgy=VARK)&?z_hhj)|(~(<<x, ?z_hgy>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))))" (is "_=>?z_hoe")
    by (rule zenon_all_0 [of "?z_hnl" "(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. ((((?z_hgy=VARK)&?z_hhj)|(~(<<x, ?z_hgy>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK])))))))))", OF z_Hne])
    show FALSE
    proof (rule zenon_imply [OF z_Hod])
     assume z_Hno:"(~?z_hmc)"
     show FALSE
     by (rule notE [OF z_Hno z_Hmc])
    next
     assume z_Hoe:"?z_hoe" (is "?z_hof|?z_hiq")
     show FALSE
     proof (rule zenon_or [OF z_Hoe])
      assume z_Hof:"?z_hof"
      have z_Hog: "?z_hoc(?z_hgy)" (is "_=>?z_hoh")
      by (rule zenon_all_0 [of "?z_hoc" "?z_hgy", OF z_Hnp])
      show FALSE
      proof (rule zenon_imply [OF z_Hog])
       assume z_Hoi:"(~?z_hlt)"
       show FALSE
       by (rule notE [OF z_Hoi z_Hlt])
      next
       assume z_Hoh:"?z_hoh"
       have z_Hoj_z_Hoh: "(\\A x:((x \\in Node)=>((((?z_hgy=x)&(votes=votes))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. ((((?z_hgy=VARK)&?z_hhj)|(~(<<x, ?z_hgy>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))), x>> \\in a_voteunde_msga)))|(~?z_hmx)))) == ?z_hoh" (is "?z_hoj == _")
       by (unfold bAll_def)
       have z_Hoj: "?z_hoj" (is "\\A x : ?z_hop(x)")
       by (unfold z_Hoj_z_Hoh, fact z_Hoh)
       have z_Hoq: "?z_hop(?z_hgp)" (is "_=>?z_hor")
       by (rule zenon_all_0 [of "?z_hop" "?z_hgp", OF z_Hoj])
       show FALSE
       proof (rule zenon_imply [OF z_Hoq])
        assume z_Hnd:"(~?z_hml)"
        show FALSE
        by (rule notE [OF z_Hnd z_Hml])
       next
        assume z_Hor:"?z_hor" (is "?z_hos|?z_hoo")
        show FALSE
        proof (rule zenon_or [OF z_Hor])
         assume z_Hos:"?z_hos" (is "?z_hot|?z_hou")
         show FALSE
         proof (rule zenon_or [OF z_Hos])
          assume z_Hot:"?z_hot" (is "_&?z_hen")
          have z_Hmu: "?z_hmu"
          by (rule zenon_and_0 [OF z_Hot])
          show FALSE
          by (rule notE [OF z_Hmw z_Hmu])
         next
          assume z_Hou:"?z_hou"
          show FALSE
          by (rule notE [OF z_Hou z_Hof])
         qed
        next
         assume z_Hoo:"?z_hoo"
         show FALSE
         by (rule notE [OF z_Hoo z_Hmx])
        qed
       qed
      qed
     next
      assume z_Hiq:"?z_hiq" (is "~?z_hir")
      show FALSE
      by (rule zenon_L2_ [OF z_Hiq z_His z_Hgc])
     qed
    qed
   qed
  qed
 next
  assume z_Hov:"(a_voteshash_primea~=a_voteshash_primea)"
  show FALSE
  by (rule zenon_noteq [OF z_Hov])
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 210"; *} qed
lemma ob'219:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
fixes Node
fixes Quorum
fixes Value
fixes a_voteunde_requestunde_msga a_voteunde_requestunde_msga'
fixes voted voted'
fixes a_voteunde_msga a_voteunde_msga'
fixes votes votes'
fixes leader leader'
fixes decided decided'
fixes a_requnde_historya a_requnde_historya'
(* usable definition vars suppressed *)
(* usable definition IgnoreRequestVote suppressed *)
(* usable definition ProtocolNext suppressed *)
(* usable definition OtherNext suppressed *)
(* usable definition Spec suppressed *)
(* usable definition Symmetry suppressed *)
(* usable definition Safety suppressed *)
(* usable definition SplitVote suppressed *)
(* usable definition Liveness suppressed *)
assumes v'29: "(((((((a_voteunde_requestunde_msga) \<in> ((SUBSET (((Node) \<times> (Node))))))) & (((voted) \<in> ([(Node) \<rightarrow> (BOOLEAN)]))) & (((a_voteunde_msga) \<in> ((SUBSET (((Node) \<times> (Node))))))) & (((votes) \<in> ([(Node) \<rightarrow> ((SUBSET (Node)))]))) & (((leader) \<in> ([(Node) \<rightarrow> (BOOLEAN)]))) & (((decided) \<in> ([(Node) \<rightarrow> ((SUBSET (Value)))])))) & (\<forall> a_n1a \<in> (Node) : (\<forall> a_n2a \<in> (Node) : (\<forall> a_v1a \<in> (Value) : (\<forall> a_v2a \<in> (Value) : (((((((a_v1a) \<in> (fapply ((decided), (a_n1a))))) \<and> (((a_v2a) \<in> (fapply ((decided), (a_n2a))))))) \<Rightarrow> (((a_v1a) = (a_v2a))))))))) & (\<forall> VARI \<in> (Node) : (\<forall> VARJ \<in> (Node) : (((((<<(VARJ), (VARI)>>) \<in> (a_voteunde_msga))) \<or> ((~ (((VARJ) \<in> (fapply ((votes), (VARI))))))))))) & (\<forall> VARI \<in> (Node) : (\<exists> QJ \<in> (Quorum) : (\<forall> VALI \<in> (Value) : (((((QJ) \<subseteq> (fapply ((votes), (VARI))))) \<or> ((~ (((VALI) \<in> (fapply ((decided), (VARI)))))))))))) & (\<forall> VARI \<in> (Node) : (\<forall> VARJ \<in> (Node) : (((fapply ((voted), (VARI))) \<or> ((~ (((<<(VARI), (VARJ)>>) \<in> (a_voteunde_msga))))))))) & (\<forall> VARI \<in> (Node) : (\<exists> QJ \<in> (Quorum) : (((((QJ) \<subseteq> (fapply ((votes), (VARI))))) \<or> ((~ (fapply ((leader), (VARI))))))))) & (\<forall> VARI \<in> (Node) : (\<forall> VALI \<in> (Value) : (((fapply ((leader), (VARI))) \<or> ((~ (((VALI) \<in> (fapply ((decided), (VARI))))))))))) & (\<forall> VARI \<in> (Node) : (\<forall> VARJ \<in> (Node) : (\<forall> VARK \<in> (Node) : (((((((((VARI) = (VARK))) \<and> (((votes) = (votes))))) \<or> ((~ (((<<(VARJ), (VARI)>>) \<in> (a_voteunde_msga))))))) \<or> ((~ (((VARJ) \<in> (fapply ((votes), (VARK)))))))))))) & (\<forall> VARI \<in> (Node) : (\<forall> VARJ \<in> (Node) : (\<forall> VARK \<in> (Node) : (((((((((VARJ) = (VARK))) \<and> (((votes) = (votes))))) \<or> ((~ (((<<(VARI), (VARK)>>) \<in> (a_voteunde_msga))))))) \<or> ((~ (((<<(VARI), (VARJ)>>) \<in> (a_voteunde_msga))))))))))) \<and> (((ProtocolNext) \<or> (OtherNext)))))"
assumes v'48: "(\<exists> i \<in> (Node) : (\<exists> Q \<in> (Quorum) : ((((Q) \<subseteq> (fapply ((votes), (i))))) & ((((a_leaderhash_primea :: c)) = ([(leader) EXCEPT ![(i)] = (TRUE)]))) & ((((a_voteshash_primea :: c)) = (votes))) & ((((a_votedhash_primea :: c)) = (voted))) & ((((a_voteunde_msghash_primea :: c)) = (a_voteunde_msga))) & ((((a_decidedhash_primea :: c)) = (decided))) & ((((a_voteunde_requestunde_msghash_primea :: c)) = (a_voteunde_requestunde_msga))) & ((((a_requnde_historyhash_primea :: c)) = (a_requnde_historya))))))"
shows "(\<forall> VARI \<in> (Node) : (\<forall> VARJ \<in> (Node) : (\<forall> VARK \<in> (Node) : (((((((((VARI) = (VARK))) \<and> ((((a_voteshash_primea :: c)) = ((a_voteshash_primea :: c)))))) \<or> ((~ (((<<(VARJ), (VARI)>>) \<in> ((a_voteunde_msghash_primea :: c)))))))) \<or> ((~ (((VARJ) \<in> (fapply (((a_voteshash_primea :: c)), (VARK))))))))))))"(is "PROP ?ob'219")
proof -
ML_command {* writeln "*** TLAPS ENTER 219"; *}
show "PROP ?ob'219"

(* BEGIN ZENON INPUT
;; file=consensus_epr_IndProofs.tlaps/tlapm_94ca53.znn; PATH='/home/egolf/.opam/4.07.1/bin:/home/egolf/.local/bin:/home/egolf/bin:/home/egolf/mambaforge/bin:/home/egolf/mambaforge/condabin:/home/egolf/.opam/4.07.1/bin:/home/egolf/.local/bin:/home/egolf/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/home/egolf/.local/bin/gurobi952/linux64/bin:/home/egolf/Projects/apalache/bin:/home/egolf/opt/foxitsoftware/foxitreader:/home/egolf/.local/bin/gurobi952/linux64/bin:/home/egolf/Projects/apalache/bin:/home/egolf/opt/foxitsoftware/foxitreader:/usr/local/bin:/usr/local/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >consensus_epr_IndProofs.tlaps/tlapm_94ca53.znn.out
;; obligation #219
$hyp "v'29" (/\ (/\ (/\ (TLA.in a_voteunde_requestunde_msga
(TLA.SUBSET (TLA.prod Node Node))) (TLA.in voted
(TLA.FuncSet Node (TLA.set T. F.))) (TLA.in a_voteunde_msga
(TLA.SUBSET (TLA.prod Node Node))) (TLA.in votes
(TLA.FuncSet Node (TLA.SUBSET Node))) (TLA.in leader
(TLA.FuncSet Node (TLA.set T. F.))) (TLA.in decided
(TLA.FuncSet Node (TLA.SUBSET Value))))
(TLA.bAll Node ((a_n1a) (TLA.bAll Node ((a_n2a) (TLA.bAll Value ((a_v1a) (TLA.bAll Value ((a_v2a) (=> (/\ (TLA.in a_v1a
(TLA.fapply decided a_n1a)) (TLA.in a_v2a (TLA.fapply decided a_n2a)))
(= a_v1a a_v2a))))))))))
(TLA.bAll Node ((VARI) (TLA.bAll Node ((VARJ) (\/ (TLA.in (TLA.tuple VARJ
VARI) a_voteunde_msga) (-. (TLA.in VARJ (TLA.fapply votes VARI))))))))
(TLA.bAll Node ((VARI) (TLA.bEx Quorum ((QJ) (TLA.bAll Value ((VALI) (\/ (TLA.subseteq QJ
(TLA.fapply votes VARI)) (-. (TLA.in VALI (TLA.fapply decided VARI))))))))))
(TLA.bAll Node ((VARI) (TLA.bAll Node ((VARJ) (\/ (TLA.fapply voted VARI)
(-. (TLA.in (TLA.tuple VARI VARJ) a_voteunde_msga)))))))
(TLA.bAll Node ((VARI) (TLA.bEx Quorum ((QJ) (\/ (TLA.subseteq QJ
(TLA.fapply votes VARI)) (-. (TLA.fapply leader VARI)))))))
(TLA.bAll Node ((VARI) (TLA.bAll Value ((VALI) (\/ (TLA.fapply leader VARI)
(-. (TLA.in VALI (TLA.fapply decided VARI))))))))
(TLA.bAll Node ((VARI) (TLA.bAll Node ((VARJ) (TLA.bAll Node ((VARK) (\/ (\/ (/\ (= VARI
VARK) (= votes votes)) (-. (TLA.in (TLA.tuple VARJ VARI) a_voteunde_msga)))
(-. (TLA.in VARJ (TLA.fapply votes VARK))))))))))
(TLA.bAll Node ((VARI) (TLA.bAll Node ((VARJ) (TLA.bAll Node ((VARK) (\/ (\/ (/\ (= VARJ
VARK) (= votes votes)) (-. (TLA.in (TLA.tuple VARI VARK) a_voteunde_msga)))
(-. (TLA.in (TLA.tuple VARI VARJ) a_voteunde_msga)))))))))) (\/ ProtocolNext
OtherNext))
$hyp "v'48" (TLA.bEx Node ((i) (TLA.bEx Quorum ((Q) (/\ (TLA.subseteq Q
(TLA.fapply votes i)) (= a_leaderhash_primea (TLA.except leader i T.))
(= a_voteshash_primea votes) (= a_votedhash_primea voted)
(= a_voteunde_msghash_primea a_voteunde_msga) (= a_decidedhash_primea
decided) (= a_voteunde_requestunde_msghash_primea
a_voteunde_requestunde_msga) (= a_requnde_historyhash_primea
a_requnde_historya))))))
$goal (TLA.bAll Node ((VARI) (TLA.bAll Node ((VARJ) (TLA.bAll Node ((VARK) (\/ (\/ (/\ (= VARI
VARK) (= a_voteshash_primea a_voteshash_primea)) (-. (TLA.in (TLA.tuple VARJ
VARI) a_voteunde_msghash_primea))) (-. (TLA.in VARJ
(TLA.fapply a_voteshash_primea VARK))))))))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Ha:"((((a_voteunde_requestunde_msga \\in SUBSET(prod(Node, Node)))&((voted \\in FuncSet(Node, {TRUE, FALSE}))&((a_voteunde_msga \\in SUBSET(prod(Node, Node)))&((votes \\in FuncSet(Node, SUBSET(Node)))&((leader \\in FuncSet(Node, {TRUE, FALSE}))&(decided \\in FuncSet(Node, SUBSET(Value))))))))&(bAll(Node, (\<lambda>a_n1a. bAll(Node, (\<lambda>a_n2a. bAll(Value, (\<lambda>a_v1a. bAll(Value, (\<lambda>a_v2a. (((a_v1a \\in (decided[a_n1a]))&(a_v2a \\in (decided[a_n2a])))=>(a_v1a=a_v2a))))))))))&(bAll(Node, (\<lambda>VARI. bAll(Node, (\<lambda>VARJ. ((<<VARJ, VARI>> \\in a_voteunde_msga)|(~(VARJ \\in (votes[VARI]))))))))&(bAll(Node, (\<lambda>VARI. bEx(Quorum, (\<lambda>QJ. bAll(Value, (\<lambda>VALI. ((QJ \\subseteq (votes[VARI]))|(~(VALI \\in (decided[VARI]))))))))))&(bAll(Node, (\<lambda>VARI. bAll(Node, (\<lambda>VARJ. ((voted[VARI])|(~(<<VARI, VARJ>> \\in a_voteunde_msga)))))))&(bAll(Node, (\<lambda>VARI. bEx(Quorum, (\<lambda>QJ. ((QJ \\subseteq (votes[VARI]))|(~(leader[VARI])))))))&(bAll(Node, (\<lambda>VARI. bAll(Value, (\<lambda>VALI. ((leader[VARI])|(~(VALI \\in (decided[VARI]))))))))&(bAll(Node, (\<lambda>VARI. bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARI=VARK)&(votes=votes))|(~(<<VARJ, VARI>> \\in a_voteunde_msga)))|(~(VARJ \\in (votes[VARK]))))))))))&bAll(Node, (\<lambda>VARI. bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(votes=votes))|(~(<<VARI, VARK>> \\in a_voteunde_msga)))|(~(<<VARI, VARJ>> \\in a_voteunde_msga)))))))))))))))))&(ProtocolNext|OtherNext))" (is "?z_hd&?z_hff")
 using v'29 by blast
 have z_Hb:"bEx(Node, (\<lambda>i. bEx(Quorum, (\<lambda>Q. ((Q \\subseteq (votes[i]))&((a_leaderhash_primea=except(leader, i, TRUE))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_decidedhash_primea=decided)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))" (is "?z_hb")
 using v'48 by blast
 have zenon_L1_: "((a_voteshash_primea[(CHOOSE x:(~((x \\in Node)=>(((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=x)&(a_voteshash_primea=a_voteshash_primea))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))), (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))) \\in (a_voteshash_primea[x])))))))])~=(votes[(CHOOSE x:(~((x \\in Node)=>(((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=x)&(a_voteshash_primea=a_voteshash_primea))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))), (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))) \\in (a_voteshash_primea[x])))))))])) ==> (a_voteshash_primea=votes) ==> FALSE" (is "?z_hgm ==> ?z_hfv ==> FALSE")
 proof -
  assume z_Hgm:"?z_hgm" (is "?z_hgn~=?z_hij")
  assume z_Hfv:"?z_hfv"
  show FALSE
  proof (rule zenon_noteq [of "?z_hij"])
   have z_Hik: "(?z_hij~=?z_hij)"
   by (rule subst [where P="(\<lambda>zenon_Vjs. ((zenon_Vjs[(CHOOSE x:(~((x \\in Node)=>(((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=x)&(a_voteshash_primea=a_voteshash_primea))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))), (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))) \\in (a_voteshash_primea[x])))))))])~=?z_hij))", OF z_Hfv], fact z_Hgm)
   thus "(?z_hij~=?z_hij)" .
  qed
 qed
 have zenon_L2_: "(~((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))) \\in (votes[(CHOOSE x:(~((x \\in Node)=>(((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=x)&(a_voteshash_primea=a_voteshash_primea))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))), (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))) \\in (a_voteshash_primea[x])))))))]))) ==> ((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))) \\in (a_voteshash_primea[(CHOOSE x:(~((x \\in Node)=>(((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=x)&(a_voteshash_primea=a_voteshash_primea))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))), (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))) \\in (a_voteshash_primea[x])))))))])) ==> (a_voteshash_primea=votes) ==> FALSE" (is "?z_hip ==> ?z_hir ==> ?z_hfv ==> FALSE")
 proof -
  assume z_Hip:"?z_hip" (is "~?z_hiq")
  assume z_Hir:"?z_hir"
  assume z_Hfv:"?z_hfv"
  show FALSE
  proof (rule notE [OF z_Hip])
   have z_His: "((a_voteshash_primea[(CHOOSE x:(~((x \\in Node)=>(((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=x)&(a_voteshash_primea=a_voteshash_primea))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))), (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))) \\in (a_voteshash_primea[x])))))))])=(votes[(CHOOSE x:(~((x \\in Node)=>(((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=x)&(a_voteshash_primea=a_voteshash_primea))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))), (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))) \\in (a_voteshash_primea[x])))))))]))" (is "?z_hgn=?z_hij")
   proof (rule zenon_nnpp [of "(?z_hgn=?z_hij)"])
    assume z_Hgm:"(?z_hgn~=?z_hij)"
    show FALSE
    by (rule zenon_L1_ [OF z_Hgm z_Hfv])
   qed
   have z_Hiq: "?z_hiq"
   by (rule subst [where P="(\<lambda>zenon_Vks. ((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))) \\in zenon_Vks))", OF z_His], fact z_Hir)
   thus "?z_hiq" .
  qed
 qed
 assume z_Hc:"(~bAll(Node, (\<lambda>VARI. bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARI=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, VARI>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))" (is "~?z_hiw")
 have z_Hd: "?z_hd" (is "?z_he&?z_hbh")
 by (rule zenon_and_0 [OF z_Ha])
 have z_Hbh: "?z_hbh" (is "?z_hbi&?z_hcb")
 by (rule zenon_and_1 [OF z_Hd])
 have z_Hcb: "?z_hcb" (is "?z_hcc&?z_hco")
 by (rule zenon_and_1 [OF z_Hbh])
 have z_Hcc: "?z_hcc"
 by (rule zenon_and_0 [OF z_Hcb])
 have z_Hco: "?z_hco" (is "?z_hcp&?z_hdd")
 by (rule zenon_and_1 [OF z_Hcb])
 have z_Hdd: "?z_hdd" (is "?z_hde&?z_hdn")
 by (rule zenon_and_1 [OF z_Hco])
 have z_Hdn: "?z_hdn" (is "?z_hdo&?z_hdv")
 by (rule zenon_and_1 [OF z_Hdd])
 have z_Hdv: "?z_hdv" (is "?z_hdw&?z_heb")
 by (rule zenon_and_1 [OF z_Hdn])
 have z_Heb: "?z_heb" (is "?z_hec&?z_hes")
 by (rule zenon_and_1 [OF z_Hdv])
 have z_Hes: "?z_hes"
 by (rule zenon_and_1 [OF z_Heb])
 have z_Hjh_z_Hcc: "(\\A x:((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msga)|(~(VARJ \\in (votes[x])))))))) == ?z_hcc" (is "?z_hjh == _")
 by (unfold bAll_def)
 have z_Hjh: "?z_hjh" (is "\\A x : ?z_hjq(x)")
 by (unfold z_Hjh_z_Hcc, fact z_Hcc)
 have z_Hjr_z_Hes: "(\\A x:((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(votes=votes))|(~(<<x, VARK>> \\in a_voteunde_msga)))|(~(<<x, VARJ>> \\in a_voteunde_msga))))))))) == ?z_hes" (is "?z_hjr == _")
 by (unfold bAll_def)
 have z_Hjr: "?z_hjr" (is "\\A x : ?z_hkf(x)")
 by (unfold z_Hjr_z_Hes, fact z_Hes)
 have z_Hkg_z_Hb: "(\\E x:((x \\in Node)&bEx(Quorum, (\<lambda>Q. ((Q \\subseteq (votes[x]))&((a_leaderhash_primea=except(leader, x, TRUE))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_decidedhash_primea=decided)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))) == ?z_hb" (is "?z_hkg == _")
 by (unfold bEx_def)
 have z_Hkg: "?z_hkg" (is "\\E x : ?z_hkp(x)")
 by (unfold z_Hkg_z_Hb, fact z_Hb)
 have z_Hkq: "?z_hkp((CHOOSE x:((x \\in Node)&bEx(Quorum, (\<lambda>Q. ((Q \\subseteq (votes[x]))&((a_leaderhash_primea=except(leader, x, TRUE))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_decidedhash_primea=decided)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))" (is "?z_hks&?z_hkt")
 by (rule zenon_ex_choose_0 [of "?z_hkp", OF z_Hkg])
 have z_Hkt: "?z_hkt"
 by (rule zenon_and_1 [OF z_Hkq])
 have z_Hku_z_Hkt: "(\\E x:((x \\in Quorum)&((x \\subseteq (votes[(CHOOSE x:((x \\in Node)&bEx(Quorum, (\<lambda>Q. ((Q \\subseteq (votes[x]))&((a_leaderhash_primea=except(leader, x, TRUE))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_decidedhash_primea=decided)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))]))&((a_leaderhash_primea=except(leader, (CHOOSE x:((x \\in Node)&bEx(Quorum, (\<lambda>Q. ((Q \\subseteq (votes[x]))&((a_leaderhash_primea=except(leader, x, TRUE))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_decidedhash_primea=decided)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))), TRUE))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_decidedhash_primea=decided)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))) == ?z_hkt" (is "?z_hku == _")
 by (unfold bEx_def)
 have z_Hku: "?z_hku" (is "\\E x : ?z_hld(x)")
 by (unfold z_Hku_z_Hkt, fact z_Hkt)
 have z_Hle: "?z_hld((CHOOSE x:((x \\in Quorum)&((x \\subseteq (votes[(CHOOSE x:((x \\in Node)&bEx(Quorum, (\<lambda>Q. ((Q \\subseteq (votes[x]))&((a_leaderhash_primea=except(leader, x, TRUE))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_decidedhash_primea=decided)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))]))&((a_leaderhash_primea=except(leader, (CHOOSE x:((x \\in Node)&bEx(Quorum, (\<lambda>Q. ((Q \\subseteq (votes[x]))&((a_leaderhash_primea=except(leader, x, TRUE))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_decidedhash_primea=decided)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))), TRUE))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_decidedhash_primea=decided)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))" (is "?z_hlg&?z_hlh")
 by (rule zenon_ex_choose_0 [of "?z_hld", OF z_Hku])
 have z_Hlh: "?z_hlh" (is "?z_hli&?z_hla")
 by (rule zenon_and_1 [OF z_Hle])
 have z_Hla: "?z_hla" (is "?z_hlb&?z_hfu")
 by (rule zenon_and_1 [OF z_Hlh])
 have z_Hfu: "?z_hfu" (is "?z_hfv&?z_hfx")
 by (rule zenon_and_1 [OF z_Hla])
 have z_Hfv: "?z_hfv"
 by (rule zenon_and_0 [OF z_Hfu])
 have z_Hfx: "?z_hfx" (is "?z_hfy&?z_hga")
 by (rule zenon_and_1 [OF z_Hfu])
 have z_Hga: "?z_hga" (is "?z_hgb&?z_hgd")
 by (rule zenon_and_1 [OF z_Hfx])
 have z_Hgb: "?z_hgb"
 by (rule zenon_and_0 [OF z_Hga])
 have z_Hlj_z_Hc: "(~(\\A x:((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK]))))))))))) == (~?z_hiw)" (is "?z_hlj == ?z_hc")
 by (unfold bAll_def)
 have z_Hlj: "?z_hlj" (is "~(\\A x : ?z_hll(x))")
 by (unfold z_Hlj_z_Hc, fact z_Hc)
 have z_Hlm: "(\\E x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))" (is "\\E x : ?z_hln(x)")
 by (rule zenon_notallex_0 [of "?z_hll", OF z_Hlj])
 have z_Hlo: "?z_hln((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK]))))))))))))" (is "~(?z_hlp=>?z_hlq)")
 by (rule zenon_ex_choose_0 [of "?z_hln", OF z_Hlm])
 have z_Hlp: "?z_hlp"
 by (rule zenon_notimply_0 [OF z_Hlo])
 have z_Hlr: "(~?z_hlq)"
 by (rule zenon_notimply_1 [OF z_Hlo])
 have z_Hls_z_Hlr: "(~(\\A x:((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))) == (~?z_hlq)" (is "?z_hls == ?z_hlr")
 by (unfold bAll_def)
 have z_Hls: "?z_hls" (is "~(\\A x : ?z_hlu(x))")
 by (unfold z_Hls_z_Hlr, fact z_Hlr)
 have z_Hlv: "(\\E x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK])))))))))" (is "\\E x : ?z_hlw(x)")
 by (rule zenon_notallex_0 [of "?z_hlu", OF z_Hls])
 have z_Hlx: "?z_hlw((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))))" (is "~(?z_hly=>?z_hlz)")
 by (rule zenon_ex_choose_0 [of "?z_hlw", OF z_Hlv])
 have z_Hly: "?z_hly"
 by (rule zenon_notimply_0 [OF z_Hlx])
 have z_Hma: "(~?z_hlz)"
 by (rule zenon_notimply_1 [OF z_Hlx])
 have z_Hmb_z_Hma: "(~(\\A x:((x \\in Node)=>(((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=x)&(a_voteshash_primea=a_voteshash_primea))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))), (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))) \\in (a_voteshash_primea[x]))))))) == (~?z_hlz)" (is "?z_hmb == ?z_hma")
 by (unfold bAll_def)
 have z_Hmb: "?z_hmb" (is "~(\\A x : ?z_hmd(x))")
 by (unfold z_Hmb_z_Hma, fact z_Hma)
 have z_Hme: "(\\E x:(~((x \\in Node)=>(((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=x)&(a_voteshash_primea=a_voteshash_primea))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))), (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))) \\in (a_voteshash_primea[x])))))))" (is "\\E x : ?z_hmf(x)")
 by (rule zenon_notallex_0 [of "?z_hmd", OF z_Hmb])
 have z_Hmg: "?z_hmf((CHOOSE x:(~((x \\in Node)=>(((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=x)&(a_voteshash_primea=a_voteshash_primea))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))), (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))) \\in (a_voteshash_primea[x]))))))))" (is "~(?z_hmh=>?z_hmi)")
 by (rule zenon_ex_choose_0 [of "?z_hmf", OF z_Hme])
 have z_Hmh: "?z_hmh"
 by (rule zenon_notimply_0 [OF z_Hmg])
 have z_Hmj: "(~?z_hmi)" (is "~(?z_hmk|?z_hml)")
 by (rule zenon_notimply_1 [OF z_Hmg])
 have z_Hmm: "(~?z_hmk)" (is "~(?z_hmn|?z_hhp)")
 by (rule zenon_notor_0 [OF z_Hmj])
 have z_Hmo: "(~?z_hml)" (is "~~?z_hir")
 by (rule zenon_notor_1 [OF z_Hmj])
 have z_Hir: "?z_hir"
 by (rule zenon_notnot_0 [OF z_Hmo])
 have z_Hmp: "(~?z_hmn)" (is "~(?z_hmq&?z_hhi)")
 by (rule zenon_notor_0 [OF z_Hmm])
 have z_Hmr: "(~?z_hhp)" (is "~~?z_hhq")
 by (rule zenon_notor_1 [OF z_Hmm])
 have z_Hhq: "?z_hhq"
 by (rule zenon_notnot_0 [OF z_Hmr])
 show FALSE
 proof (rule zenon_notand [OF z_Hmp])
  assume z_Hms:"((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&?z_hhi)|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))~=(CHOOSE x:(~((x \\in Node)=>(((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&?z_hhi)|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=x)&?z_hhi)|?z_hhp)|(~((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&?z_hhi)|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&?z_hhi)|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&?z_hhi)|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))) \\in (a_voteshash_primea[x]))))))))" (is "?z_hgx~=?z_hgo")
  have z_Hmt: "(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. ((((?z_hgx=VARK)&?z_hhi)|(~(<<x, ?z_hgx>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))), ?z_hgx>> \\in a_voteunde_msga)" (is "?z_hmt")
  by (rule subst [where P="(\<lambda>zenon_Vhc. (<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. ((((?z_hgx=VARK)&?z_hhi)|(~(<<x, ?z_hgx>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))), ?z_hgx>> \\in zenon_Vhc))", OF z_Hgb z_Hhq])
  have z_Hmx: "?z_hjq(?z_hgo)" (is "_=>?z_hmy")
  by (rule zenon_all_0 [of "?z_hjq" "?z_hgo", OF z_Hjh])
  show FALSE
  proof (rule zenon_imply [OF z_Hmx])
   assume z_Hmz:"(~?z_hmh)"
   show FALSE
   by (rule notE [OF z_Hmz z_Hmh])
  next
   assume z_Hmy:"?z_hmy"
   have z_Hna_z_Hmy: "(\\A x:((x \\in Node)=>((<<x, ?z_hgo>> \\in a_voteunde_msga)|(~(x \\in (votes[?z_hgo])))))) == ?z_hmy" (is "?z_hna == _")
   by (unfold bAll_def)
   have z_Hna: "?z_hna" (is "\\A x : ?z_hnh(x)")
   by (unfold z_Hna_z_Hmy, fact z_Hmy)
   have z_Hni: "?z_hnh((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. ((((?z_hgx=VARK)&?z_hhi)|(~(<<x, ?z_hgx>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))))" (is "_=>?z_hnj")
   by (rule zenon_all_0 [of "?z_hnh" "(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. ((((?z_hgx=VARK)&?z_hhi)|(~(<<x, ?z_hgx>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK])))))))))", OF z_Hna])
   show FALSE
   proof (rule zenon_imply [OF z_Hni])
    assume z_Hnk:"(~?z_hly)"
    show FALSE
    by (rule notE [OF z_Hnk z_Hly])
   next
    assume z_Hnj:"?z_hnj" (is "?z_hnl|?z_hip")
    show FALSE
    proof (rule zenon_or [OF z_Hnj])
     assume z_Hnl:"?z_hnl"
     have z_Hnm: "?z_hkf((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. ((((?z_hgx=VARK)&?z_hhi)|(~(<<x, ?z_hgx>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))))" (is "_=>?z_hnn")
     by (rule zenon_all_0 [of "?z_hkf" "(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. ((((?z_hgx=VARK)&?z_hhi)|(~(<<x, ?z_hgx>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK])))))))))", OF z_Hjr])
     show FALSE
     proof (rule zenon_imply [OF z_Hnm])
      assume z_Hnk:"(~?z_hly)"
      show FALSE
      by (rule notE [OF z_Hnk z_Hly])
     next
      assume z_Hnn:"?z_hnn"
      have z_Hno_z_Hnn: "(\\A x:((x \\in Node)=>bAll(Node, (\<lambda>VARK. ((((x=VARK)&(votes=votes))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. ((((?z_hgx=VARK)&?z_hhi)|(~(<<x, ?z_hgx>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))), VARK>> \\in a_voteunde_msga)))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. ((((?z_hgx=VARK)&?z_hhi)|(~(<<x, ?z_hgx>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))), x>> \\in a_voteunde_msga))))))) == ?z_hnn" (is "?z_hno == _")
      by (unfold bAll_def)
      have z_Hno: "?z_hno" (is "\\A x : ?z_hob(x)")
      by (unfold z_Hno_z_Hnn, fact z_Hnn)
      have z_Hoc: "?z_hob(?z_hgx)" (is "_=>?z_hod")
      by (rule zenon_all_0 [of "?z_hob" "?z_hgx", OF z_Hno])
      show FALSE
      proof (rule zenon_imply [OF z_Hoc])
       assume z_Hoe:"(~?z_hlp)"
       show FALSE
       by (rule notE [OF z_Hoe z_Hlp])
      next
       assume z_Hod:"?z_hod"
       have z_Hof_z_Hod: "(\\A x:((x \\in Node)=>((((?z_hgx=x)&(votes=votes))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. ((((?z_hgx=VARK)&?z_hhi)|(~(<<x, ?z_hgx>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))), x>> \\in a_voteunde_msga)))|(~?z_hmt)))) == ?z_hod" (is "?z_hof == _")
       by (unfold bAll_def)
       have z_Hof: "?z_hof" (is "\\A x : ?z_hol(x)")
       by (unfold z_Hof_z_Hod, fact z_Hod)
       have z_Hom: "?z_hol(?z_hgo)" (is "_=>?z_hon")
       by (rule zenon_all_0 [of "?z_hol" "?z_hgo", OF z_Hof])
       show FALSE
       proof (rule zenon_imply [OF z_Hom])
        assume z_Hmz:"(~?z_hmh)"
        show FALSE
        by (rule notE [OF z_Hmz z_Hmh])
       next
        assume z_Hon:"?z_hon" (is "?z_hoo|?z_hok")
        show FALSE
        proof (rule zenon_or [OF z_Hon])
         assume z_Hoo:"?z_hoo" (is "?z_hop|?z_hoq")
         show FALSE
         proof (rule zenon_or [OF z_Hoo])
          assume z_Hop:"?z_hop" (is "_&?z_hen")
          have z_Hmq: "?z_hmq"
          by (rule zenon_and_0 [OF z_Hop])
          show FALSE
          by (rule notE [OF z_Hms z_Hmq])
         next
          assume z_Hoq:"?z_hoq"
          show FALSE
          by (rule notE [OF z_Hoq z_Hnl])
         qed
        next
         assume z_Hok:"?z_hok"
         show FALSE
         by (rule notE [OF z_Hok z_Hmt])
        qed
       qed
      qed
     qed
    next
     assume z_Hip:"?z_hip" (is "~?z_hiq")
     show FALSE
     by (rule zenon_L2_ [OF z_Hip z_Hir z_Hfv])
    qed
   qed
  qed
 next
  assume z_Hor:"(a_voteshash_primea~=a_voteshash_primea)"
  show FALSE
  by (rule zenon_noteq [OF z_Hor])
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 219"; *} qed
lemma ob'218:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
fixes Node
fixes Quorum
fixes Value
fixes a_voteunde_requestunde_msga a_voteunde_requestunde_msga'
fixes voted voted'
fixes a_voteunde_msga a_voteunde_msga'
fixes votes votes'
fixes leader leader'
fixes decided decided'
fixes a_requnde_historya a_requnde_historya'
(* usable definition vars suppressed *)
(* usable definition IgnoreRequestVote suppressed *)
(* usable definition SendVote suppressed *)
(* usable definition RecvVote suppressed *)
(* usable definition BecomeLeader suppressed *)
(* usable definition Decide suppressed *)
(* usable definition SendRequestVote suppressed *)
(* usable definition Init suppressed *)
(* usable definition ProtocolNext suppressed *)
(* usable definition OtherNext suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition Symmetry suppressed *)
(* usable definition Safety suppressed *)
(* usable definition SplitVote suppressed *)
(* usable definition Liveness suppressed *)
(* usable definition SafetyCore suppressed *)
(* usable definition TypeOK suppressed *)
(* usable definition Inv119_1_0_def suppressed *)
(* usable definition Inv152_1_1_def suppressed *)
(* usable definition Inv693_1_2_def suppressed *)
(* usable definition Inv164_1_3_def suppressed *)
(* usable definition Inv622_1_4_def suppressed *)
(* usable definition Inv5288_2_0_def suppressed *)
(* usable definition IndAuto suppressed *)
assumes v'45: "(((IndAuto) \<and> (Next)))"
assumes v'63: "((\<And> VARI :: c. VARI \<in> (Node) \<Longrightarrow> (\<And> VARJ :: c. VARJ \<in> (Node) \<Longrightarrow> (\<forall> VARK \<in> (Node) : (((((((((VARI) = (VARK))) \<and> ((((a_voteshash_primea :: c)) = ((a_voteshash_primea :: c)))))) \<or> ((~ (((<<(VARJ), (VARI)>>) \<in> ((a_voteunde_msghash_primea :: c)))))))) \<or> ((~ (((VARJ) \<in> (fapply (((a_voteshash_primea :: c)), (VARK)))))))))))))"
shows "(\<forall> VARI \<in> (Node) : (\<forall> VARJ \<in> (Node) : (\<forall> VARK \<in> (Node) : (((((((((VARI) = (VARK))) \<and> ((((a_voteshash_primea :: c)) = ((a_voteshash_primea :: c)))))) \<or> ((~ (((<<(VARJ), (VARI)>>) \<in> ((a_voteunde_msghash_primea :: c)))))))) \<or> ((~ (((VARJ) \<in> (fapply (((a_voteshash_primea :: c)), (VARK))))))))))))"(is "PROP ?ob'218")
proof -
ML_command {* writeln "*** TLAPS ENTER 218"; *}
show "PROP ?ob'218"

(* BEGIN ZENON INPUT
;; file=consensus_epr_IndProofs.tlaps/tlapm_ae6071.znn; PATH='/home/egolf/.opam/4.07.1/bin:/home/egolf/.local/bin:/home/egolf/bin:/home/egolf/mambaforge/bin:/home/egolf/mambaforge/condabin:/home/egolf/.opam/4.07.1/bin:/home/egolf/.local/bin:/home/egolf/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/home/egolf/.local/bin/gurobi952/linux64/bin:/home/egolf/Projects/apalache/bin:/home/egolf/opt/foxitsoftware/foxitreader:/home/egolf/.local/bin/gurobi952/linux64/bin:/home/egolf/Projects/apalache/bin:/home/egolf/opt/foxitsoftware/foxitreader:/usr/local/bin:/usr/local/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >consensus_epr_IndProofs.tlaps/tlapm_ae6071.znn.out
;; obligation #218
$hyp "v'45" (/\ IndAuto
Next)
$hyp "v'63" (TLA.bAll Node ((VARI) (TLA.bAll Node ((VARJ) (TLA.bAll Node ((VARK) (\/ (\/ (/\ (= VARI
VARK) (= a_voteshash_primea a_voteshash_primea)) (-. (TLA.in (TLA.tuple VARJ
VARI) a_voteunde_msghash_primea))) (-. (TLA.in VARJ
(TLA.fapply a_voteshash_primea VARK))))))))))
$goal (TLA.bAll Node ((VARI) (TLA.bAll Node ((VARJ) (TLA.bAll Node ((VARK) (\/ (\/ (/\ (= VARI
VARK) (= a_voteshash_primea a_voteshash_primea)) (-. (TLA.in (TLA.tuple VARJ
VARI) a_voteunde_msghash_primea))) (-. (TLA.in VARJ
(TLA.fapply a_voteshash_primea VARK))))))))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hb:"bAll(Node, (\<lambda>VARI. bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARI=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, VARI>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK]))))))))))" (is "?z_hb")
 using v'63 by blast
 assume z_Hc:"(~?z_hb)"
 show FALSE
 by (rule notE [OF z_Hc z_Hb])
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 218"; *} qed
lemma ob'221:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
fixes Node
fixes Quorum
fixes Value
fixes a_voteunde_requestunde_msga a_voteunde_requestunde_msga'
fixes voted voted'
fixes a_voteunde_msga a_voteunde_msga'
fixes votes votes'
fixes leader leader'
fixes decided decided'
fixes a_requnde_historya a_requnde_historya'
(* usable definition vars suppressed *)
(* usable definition IgnoreRequestVote suppressed *)
(* usable definition ProtocolNext suppressed *)
(* usable definition OtherNext suppressed *)
(* usable definition Spec suppressed *)
(* usable definition Symmetry suppressed *)
(* usable definition Safety suppressed *)
(* usable definition SplitVote suppressed *)
(* usable definition Liveness suppressed *)
assumes v'29: "(((((((a_voteunde_requestunde_msga) \<in> ((SUBSET (((Node) \<times> (Node))))))) & (((voted) \<in> ([(Node) \<rightarrow> (BOOLEAN)]))) & (((a_voteunde_msga) \<in> ((SUBSET (((Node) \<times> (Node))))))) & (((votes) \<in> ([(Node) \<rightarrow> ((SUBSET (Node)))]))) & (((leader) \<in> ([(Node) \<rightarrow> (BOOLEAN)]))) & (((decided) \<in> ([(Node) \<rightarrow> ((SUBSET (Value)))])))) & (\<forall> a_n1a \<in> (Node) : (\<forall> a_n2a \<in> (Node) : (\<forall> a_v1a \<in> (Value) : (\<forall> a_v2a \<in> (Value) : (((((((a_v1a) \<in> (fapply ((decided), (a_n1a))))) \<and> (((a_v2a) \<in> (fapply ((decided), (a_n2a))))))) \<Rightarrow> (((a_v1a) = (a_v2a))))))))) & (\<forall> VARI \<in> (Node) : (\<forall> VARJ \<in> (Node) : (((((<<(VARJ), (VARI)>>) \<in> (a_voteunde_msga))) \<or> ((~ (((VARJ) \<in> (fapply ((votes), (VARI))))))))))) & (\<forall> VARI \<in> (Node) : (\<exists> QJ \<in> (Quorum) : (\<forall> VALI \<in> (Value) : (((((QJ) \<subseteq> (fapply ((votes), (VARI))))) \<or> ((~ (((VALI) \<in> (fapply ((decided), (VARI)))))))))))) & (\<forall> VARI \<in> (Node) : (\<forall> VARJ \<in> (Node) : (((fapply ((voted), (VARI))) \<or> ((~ (((<<(VARI), (VARJ)>>) \<in> (a_voteunde_msga))))))))) & (\<forall> VARI \<in> (Node) : (\<exists> QJ \<in> (Quorum) : (((((QJ) \<subseteq> (fapply ((votes), (VARI))))) \<or> ((~ (fapply ((leader), (VARI))))))))) & (\<forall> VARI \<in> (Node) : (\<forall> VALI \<in> (Value) : (((fapply ((leader), (VARI))) \<or> ((~ (((VALI) \<in> (fapply ((decided), (VARI))))))))))) & (\<forall> VARI \<in> (Node) : (\<forall> VARJ \<in> (Node) : (\<forall> VARK \<in> (Node) : (((((((((VARI) = (VARK))) \<and> (((votes) = (votes))))) \<or> ((~ (((<<(VARJ), (VARI)>>) \<in> (a_voteunde_msga))))))) \<or> ((~ (((VARJ) \<in> (fapply ((votes), (VARK)))))))))))) & (\<forall> VARI \<in> (Node) : (\<forall> VARJ \<in> (Node) : (\<forall> VARK \<in> (Node) : (((((((((VARJ) = (VARK))) \<and> (((votes) = (votes))))) \<or> ((~ (((<<(VARI), (VARK)>>) \<in> (a_voteunde_msga))))))) \<or> ((~ (((<<(VARI), (VARJ)>>) \<in> (a_voteunde_msga))))))))))) \<and> (((ProtocolNext) \<or> (OtherNext)))))"
assumes v'49: "(\<exists> i \<in> (Node) : (\<exists> j \<in> (Node) : (\<exists> v \<in> (Value) : ((fapply ((leader), (i))) & ((({}) = (fapply ((decided), (i))))) & ((((a_decidedhash_primea :: c)) = ([(decided) EXCEPT ![(i)] = (((fapply ((decided), (i))) \<union> ({(v)})))]))) & ((((a_voteshash_primea :: c)) = (votes))) & ((((a_votedhash_primea :: c)) = (voted))) & ((((a_voteunde_msghash_primea :: c)) = (a_voteunde_msga))) & ((((a_leaderhash_primea :: c)) = (leader))) & ((((a_voteunde_requestunde_msghash_primea :: c)) = (a_voteunde_requestunde_msga))) & ((((a_requnde_historyhash_primea :: c)) = (a_requnde_historya)))))))"
shows "(\<forall> VARI \<in> (Node) : (\<forall> VARJ \<in> (Node) : (\<forall> VARK \<in> (Node) : (((((((((VARI) = (VARK))) \<and> ((((a_voteshash_primea :: c)) = ((a_voteshash_primea :: c)))))) \<or> ((~ (((<<(VARJ), (VARI)>>) \<in> ((a_voteunde_msghash_primea :: c)))))))) \<or> ((~ (((VARJ) \<in> (fapply (((a_voteshash_primea :: c)), (VARK))))))))))))"(is "PROP ?ob'221")
proof -
ML_command {* writeln "*** TLAPS ENTER 221"; *}
show "PROP ?ob'221"

(* BEGIN ZENON INPUT
;; file=consensus_epr_IndProofs.tlaps/tlapm_df683f.znn; PATH='/home/egolf/.opam/4.07.1/bin:/home/egolf/.local/bin:/home/egolf/bin:/home/egolf/mambaforge/bin:/home/egolf/mambaforge/condabin:/home/egolf/.opam/4.07.1/bin:/home/egolf/.local/bin:/home/egolf/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/home/egolf/.local/bin/gurobi952/linux64/bin:/home/egolf/Projects/apalache/bin:/home/egolf/opt/foxitsoftware/foxitreader:/home/egolf/.local/bin/gurobi952/linux64/bin:/home/egolf/Projects/apalache/bin:/home/egolf/opt/foxitsoftware/foxitreader:/usr/local/bin:/usr/local/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >consensus_epr_IndProofs.tlaps/tlapm_df683f.znn.out
;; obligation #221
$hyp "v'29" (/\ (/\ (/\ (TLA.in a_voteunde_requestunde_msga
(TLA.SUBSET (TLA.prod Node Node))) (TLA.in voted
(TLA.FuncSet Node (TLA.set T. F.))) (TLA.in a_voteunde_msga
(TLA.SUBSET (TLA.prod Node Node))) (TLA.in votes
(TLA.FuncSet Node (TLA.SUBSET Node))) (TLA.in leader
(TLA.FuncSet Node (TLA.set T. F.))) (TLA.in decided
(TLA.FuncSet Node (TLA.SUBSET Value))))
(TLA.bAll Node ((a_n1a) (TLA.bAll Node ((a_n2a) (TLA.bAll Value ((a_v1a) (TLA.bAll Value ((a_v2a) (=> (/\ (TLA.in a_v1a
(TLA.fapply decided a_n1a)) (TLA.in a_v2a (TLA.fapply decided a_n2a)))
(= a_v1a a_v2a))))))))))
(TLA.bAll Node ((VARI) (TLA.bAll Node ((VARJ) (\/ (TLA.in (TLA.tuple VARJ
VARI) a_voteunde_msga) (-. (TLA.in VARJ (TLA.fapply votes VARI))))))))
(TLA.bAll Node ((VARI) (TLA.bEx Quorum ((QJ) (TLA.bAll Value ((VALI) (\/ (TLA.subseteq QJ
(TLA.fapply votes VARI)) (-. (TLA.in VALI (TLA.fapply decided VARI))))))))))
(TLA.bAll Node ((VARI) (TLA.bAll Node ((VARJ) (\/ (TLA.fapply voted VARI)
(-. (TLA.in (TLA.tuple VARI VARJ) a_voteunde_msga)))))))
(TLA.bAll Node ((VARI) (TLA.bEx Quorum ((QJ) (\/ (TLA.subseteq QJ
(TLA.fapply votes VARI)) (-. (TLA.fapply leader VARI)))))))
(TLA.bAll Node ((VARI) (TLA.bAll Value ((VALI) (\/ (TLA.fapply leader VARI)
(-. (TLA.in VALI (TLA.fapply decided VARI))))))))
(TLA.bAll Node ((VARI) (TLA.bAll Node ((VARJ) (TLA.bAll Node ((VARK) (\/ (\/ (/\ (= VARI
VARK) (= votes votes)) (-. (TLA.in (TLA.tuple VARJ VARI) a_voteunde_msga)))
(-. (TLA.in VARJ (TLA.fapply votes VARK))))))))))
(TLA.bAll Node ((VARI) (TLA.bAll Node ((VARJ) (TLA.bAll Node ((VARK) (\/ (\/ (/\ (= VARJ
VARK) (= votes votes)) (-. (TLA.in (TLA.tuple VARI VARK) a_voteunde_msga)))
(-. (TLA.in (TLA.tuple VARI VARJ) a_voteunde_msga)))))))))) (\/ ProtocolNext
OtherNext))
$hyp "v'49" (TLA.bEx Node ((i) (TLA.bEx Node ((j) (TLA.bEx Value ((v) (/\ (TLA.fapply leader i)
(= TLA.emptyset (TLA.fapply decided i)) (= a_decidedhash_primea
(TLA.except decided i (TLA.cup (TLA.fapply decided i) (TLA.set v))))
(= a_voteshash_primea votes) (= a_votedhash_primea voted)
(= a_voteunde_msghash_primea a_voteunde_msga) (= a_leaderhash_primea leader)
(= a_voteunde_requestunde_msghash_primea a_voteunde_requestunde_msga)
(= a_requnde_historyhash_primea
a_requnde_historya))))))))
$goal (TLA.bAll Node ((VARI) (TLA.bAll Node ((VARJ) (TLA.bAll Node ((VARK) (\/ (\/ (/\ (= VARI
VARK) (= a_voteshash_primea a_voteshash_primea)) (-. (TLA.in (TLA.tuple VARJ
VARI) a_voteunde_msghash_primea))) (-. (TLA.in VARJ
(TLA.fapply a_voteshash_primea VARK))))))))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Ha:"((((a_voteunde_requestunde_msga \\in SUBSET(prod(Node, Node)))&((voted \\in FuncSet(Node, {TRUE, FALSE}))&((a_voteunde_msga \\in SUBSET(prod(Node, Node)))&((votes \\in FuncSet(Node, SUBSET(Node)))&((leader \\in FuncSet(Node, {TRUE, FALSE}))&(decided \\in FuncSet(Node, SUBSET(Value))))))))&(bAll(Node, (\<lambda>a_n1a. bAll(Node, (\<lambda>a_n2a. bAll(Value, (\<lambda>a_v1a. bAll(Value, (\<lambda>a_v2a. (((a_v1a \\in (decided[a_n1a]))&(a_v2a \\in (decided[a_n2a])))=>(a_v1a=a_v2a))))))))))&(bAll(Node, (\<lambda>VARI. bAll(Node, (\<lambda>VARJ. ((<<VARJ, VARI>> \\in a_voteunde_msga)|(~(VARJ \\in (votes[VARI]))))))))&(bAll(Node, (\<lambda>VARI. bEx(Quorum, (\<lambda>QJ. bAll(Value, (\<lambda>VALI. ((QJ \\subseteq (votes[VARI]))|(~(VALI \\in (decided[VARI]))))))))))&(bAll(Node, (\<lambda>VARI. bAll(Node, (\<lambda>VARJ. ((voted[VARI])|(~(<<VARI, VARJ>> \\in a_voteunde_msga)))))))&(bAll(Node, (\<lambda>VARI. bEx(Quorum, (\<lambda>QJ. ((QJ \\subseteq (votes[VARI]))|(~(leader[VARI])))))))&(bAll(Node, (\<lambda>VARI. bAll(Value, (\<lambda>VALI. ((leader[VARI])|(~(VALI \\in (decided[VARI]))))))))&(bAll(Node, (\<lambda>VARI. bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARI=VARK)&(votes=votes))|(~(<<VARJ, VARI>> \\in a_voteunde_msga)))|(~(VARJ \\in (votes[VARK]))))))))))&bAll(Node, (\<lambda>VARI. bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(votes=votes))|(~(<<VARI, VARK>> \\in a_voteunde_msga)))|(~(<<VARI, VARJ>> \\in a_voteunde_msga)))))))))))))))))&(ProtocolNext|OtherNext))" (is "?z_hd&?z_hff")
 using v'29 by blast
 have z_Hb:"bEx(Node, (\<lambda>i. bEx(Node, (\<lambda>j. bEx(Value, (\<lambda>v. ((leader[i])&(({}=(decided[i]))&((a_decidedhash_primea=except(decided, i, ((decided[i]) \\cup {v})))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))))" (is "?z_hb")
 using v'49 by blast
 have zenon_L1_: "((a_voteshash_primea[(CHOOSE x:(~((x \\in Node)=>(((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=x)&(a_voteshash_primea=a_voteshash_primea))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))), (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))) \\in (a_voteshash_primea[x])))))))])~=(votes[(CHOOSE x:(~((x \\in Node)=>(((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=x)&(a_voteshash_primea=a_voteshash_primea))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))), (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))) \\in (a_voteshash_primea[x])))))))])) ==> (a_voteshash_primea=votes) ==> FALSE" (is "?z_hgt ==> ?z_hgc ==> FALSE")
 proof -
  assume z_Hgt:"?z_hgt" (is "?z_hgu~=?z_hiq")
  assume z_Hgc:"?z_hgc"
  show FALSE
  proof (rule zenon_noteq [of "?z_hiq"])
   have z_Hir: "(?z_hiq~=?z_hiq)"
   by (rule subst [where P="(\<lambda>zenon_Viv. ((zenon_Viv[(CHOOSE x:(~((x \\in Node)=>(((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=x)&(a_voteshash_primea=a_voteshash_primea))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))), (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))) \\in (a_voteshash_primea[x])))))))])~=?z_hiq))", OF z_Hgc], fact z_Hgt)
   thus "(?z_hiq~=?z_hiq)" .
  qed
 qed
 have zenon_L2_: "(~((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))) \\in (votes[(CHOOSE x:(~((x \\in Node)=>(((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=x)&(a_voteshash_primea=a_voteshash_primea))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))), (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))) \\in (a_voteshash_primea[x])))))))]))) ==> ((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))) \\in (a_voteshash_primea[(CHOOSE x:(~((x \\in Node)=>(((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=x)&(a_voteshash_primea=a_voteshash_primea))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))), (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))) \\in (a_voteshash_primea[x])))))))])) ==> (a_voteshash_primea=votes) ==> FALSE" (is "?z_hiw ==> ?z_hiy ==> ?z_hgc ==> FALSE")
 proof -
  assume z_Hiw:"?z_hiw" (is "~?z_hix")
  assume z_Hiy:"?z_hiy"
  assume z_Hgc:"?z_hgc"
  show FALSE
  proof (rule notE [OF z_Hiw])
   have z_Hiz: "((a_voteshash_primea[(CHOOSE x:(~((x \\in Node)=>(((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=x)&(a_voteshash_primea=a_voteshash_primea))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))), (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))) \\in (a_voteshash_primea[x])))))))])=(votes[(CHOOSE x:(~((x \\in Node)=>(((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=x)&(a_voteshash_primea=a_voteshash_primea))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))), (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))) \\in (a_voteshash_primea[x])))))))]))" (is "?z_hgu=?z_hiq")
   proof (rule zenon_nnpp [of "(?z_hgu=?z_hiq)"])
    assume z_Hgt:"(?z_hgu~=?z_hiq)"
    show FALSE
    by (rule zenon_L1_ [OF z_Hgt z_Hgc])
   qed
   have z_Hix: "?z_hix"
   by (rule subst [where P="(\<lambda>zenon_Vjv. ((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))) \\in zenon_Vjv))", OF z_Hiz], fact z_Hiy)
   thus "?z_hix" .
  qed
 qed
 assume z_Hc:"(~bAll(Node, (\<lambda>VARI. bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARI=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, VARI>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))" (is "~?z_hjd")
 have z_Hd: "?z_hd" (is "?z_he&?z_hbh")
 by (rule zenon_and_0 [OF z_Ha])
 have z_Hbh: "?z_hbh" (is "?z_hbi&?z_hcb")
 by (rule zenon_and_1 [OF z_Hd])
 have z_Hcb: "?z_hcb" (is "?z_hcc&?z_hco")
 by (rule zenon_and_1 [OF z_Hbh])
 have z_Hcc: "?z_hcc"
 by (rule zenon_and_0 [OF z_Hcb])
 have z_Hco: "?z_hco" (is "?z_hcp&?z_hdd")
 by (rule zenon_and_1 [OF z_Hcb])
 have z_Hdd: "?z_hdd" (is "?z_hde&?z_hdn")
 by (rule zenon_and_1 [OF z_Hco])
 have z_Hdn: "?z_hdn" (is "?z_hdo&?z_hdv")
 by (rule zenon_and_1 [OF z_Hdd])
 have z_Hdv: "?z_hdv" (is "?z_hdw&?z_heb")
 by (rule zenon_and_1 [OF z_Hdn])
 have z_Heb: "?z_heb" (is "?z_hec&?z_hes")
 by (rule zenon_and_1 [OF z_Hdv])
 have z_Hes: "?z_hes"
 by (rule zenon_and_1 [OF z_Heb])
 have z_Hjo_z_Hcc: "(\\A x:((x \\in Node)=>bAll(Node, (\<lambda>VARJ. ((<<VARJ, x>> \\in a_voteunde_msga)|(~(VARJ \\in (votes[x])))))))) == ?z_hcc" (is "?z_hjo == _")
 by (unfold bAll_def)
 have z_Hjo: "?z_hjo" (is "\\A x : ?z_hjx(x)")
 by (unfold z_Hjo_z_Hcc, fact z_Hcc)
 have z_Hjy_z_Hes: "(\\A x:((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(votes=votes))|(~(<<x, VARK>> \\in a_voteunde_msga)))|(~(<<x, VARJ>> \\in a_voteunde_msga))))))))) == ?z_hes" (is "?z_hjy == _")
 by (unfold bAll_def)
 have z_Hjy: "?z_hjy" (is "\\A x : ?z_hkm(x)")
 by (unfold z_Hjy_z_Hes, fact z_Hes)
 have z_Hkn_z_Hb: "(\\E x:((x \\in Node)&bEx(Node, (\<lambda>j. bEx(Value, (\<lambda>v. ((leader[x])&(({}=(decided[x]))&((a_decidedhash_primea=except(decided, x, ((decided[x]) \\cup {v})))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))))) == ?z_hb" (is "?z_hkn == _")
 by (unfold bEx_def)
 have z_Hkn: "?z_hkn" (is "\\E x : ?z_hlc(x)")
 by (unfold z_Hkn_z_Hb, fact z_Hb)
 have z_Hld: "?z_hlc((CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. bEx(Value, (\<lambda>v. ((leader[x])&(({}=(decided[x]))&((a_decidedhash_primea=except(decided, x, ((decided[x]) \\cup {v})))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))))))" (is "?z_hlf&?z_hlg")
 by (rule zenon_ex_choose_0 [of "?z_hlc", OF z_Hkn])
 have z_Hlg: "?z_hlg"
 by (rule zenon_and_1 [OF z_Hld])
 have z_Hlh_z_Hlg: "(\\E x:((x \\in Node)&bEx(Value, (\<lambda>v. ((leader[(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. bEx(Value, (\<lambda>v. ((leader[x])&(({}=(decided[x]))&((a_decidedhash_primea=except(decided, x, ((decided[x]) \\cup {v})))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))))])&(({}=(decided[(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. bEx(Value, (\<lambda>v. ((leader[x])&(({}=(decided[x]))&((a_decidedhash_primea=except(decided, x, ((decided[x]) \\cup {v})))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))))]))&((a_decidedhash_primea=except(decided, (CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. bEx(Value, (\<lambda>v. ((leader[x])&(({}=(decided[x]))&((a_decidedhash_primea=except(decided, x, ((decided[x]) \\cup {v})))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))))), ((decided[(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. bEx(Value, (\<lambda>v. ((leader[x])&(({}=(decided[x]))&((a_decidedhash_primea=except(decided, x, ((decided[x]) \\cup {v})))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))))]) \\cup {v})))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))) == ?z_hlg" (is "?z_hlh == _")
 by (unfold bEx_def)
 have z_Hlh: "?z_hlh" (is "\\E x : ?z_hlu(x)")
 by (unfold z_Hlh_z_Hlg, fact z_Hlg)
 have z_Hlv: "?z_hlu((CHOOSE x:((x \\in Node)&bEx(Value, (\<lambda>v. ((leader[(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. bEx(Value, (\<lambda>v. ((leader[x])&(({}=(decided[x]))&((a_decidedhash_primea=except(decided, x, ((decided[x]) \\cup {v})))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))))])&(({}=(decided[(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. bEx(Value, (\<lambda>v. ((leader[x])&(({}=(decided[x]))&((a_decidedhash_primea=except(decided, x, ((decided[x]) \\cup {v})))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))))]))&((a_decidedhash_primea=except(decided, (CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. bEx(Value, (\<lambda>v. ((leader[x])&(({}=(decided[x]))&((a_decidedhash_primea=except(decided, x, ((decided[x]) \\cup {v})))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))))), ((decided[(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. bEx(Value, (\<lambda>v. ((leader[x])&(({}=(decided[x]))&((a_decidedhash_primea=except(decided, x, ((decided[x]) \\cup {v})))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))))]) \\cup {v})))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))))" (is "?z_hlx&?z_hlj")
 by (rule zenon_ex_choose_0 [of "?z_hlu", OF z_Hlh])
 have z_Hlj: "?z_hlj"
 by (rule zenon_and_1 [OF z_Hlv])
 have z_Hly_z_Hlj: "(\\E x:((x \\in Value)&((leader[(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. bEx(Value, (\<lambda>v. ((leader[x])&(({}=(decided[x]))&((a_decidedhash_primea=except(decided, x, ((decided[x]) \\cup {v})))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))))])&(({}=(decided[(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. bEx(Value, (\<lambda>v. ((leader[x])&(({}=(decided[x]))&((a_decidedhash_primea=except(decided, x, ((decided[x]) \\cup {v})))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))))]))&((a_decidedhash_primea=except(decided, (CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. bEx(Value, (\<lambda>v. ((leader[x])&(({}=(decided[x]))&((a_decidedhash_primea=except(decided, x, ((decided[x]) \\cup {v})))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))))), ((decided[(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. bEx(Value, (\<lambda>v. ((leader[x])&(({}=(decided[x]))&((a_decidedhash_primea=except(decided, x, ((decided[x]) \\cup {v})))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))))]) \\cup {x})))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))) == ?z_hlj" (is "?z_hly == _")
 by (unfold bEx_def)
 have z_Hly: "?z_hly" (is "\\E x : ?z_hmi(x)")
 by (unfold z_Hly_z_Hlj, fact z_Hlj)
 have z_Hmj: "?z_hmi((CHOOSE x:((x \\in Value)&((leader[(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. bEx(Value, (\<lambda>v. ((leader[x])&(({}=(decided[x]))&((a_decidedhash_primea=except(decided, x, ((decided[x]) \\cup {v})))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))))])&(({}=(decided[(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. bEx(Value, (\<lambda>v. ((leader[x])&(({}=(decided[x]))&((a_decidedhash_primea=except(decided, x, ((decided[x]) \\cup {v})))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))))]))&((a_decidedhash_primea=except(decided, (CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. bEx(Value, (\<lambda>v. ((leader[x])&(({}=(decided[x]))&((a_decidedhash_primea=except(decided, x, ((decided[x]) \\cup {v})))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))))), ((decided[(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. bEx(Value, (\<lambda>v. ((leader[x])&(({}=(decided[x]))&((a_decidedhash_primea=except(decided, x, ((decided[x]) \\cup {v})))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))))]) \\cup {x})))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))" (is "?z_hml&?z_hmm")
 by (rule zenon_ex_choose_0 [of "?z_hmi", OF z_Hly])
 have z_Hmm: "?z_hmm" (is "?z_hlm&?z_hmn")
 by (rule zenon_and_1 [OF z_Hmj])
 have z_Hmn: "?z_hmn" (is "?z_hlo&?z_hmo")
 by (rule zenon_and_1 [OF z_Hmm])
 have z_Hmo: "?z_hmo" (is "?z_hmp&?z_hgb")
 by (rule zenon_and_1 [OF z_Hmn])
 have z_Hgb: "?z_hgb" (is "?z_hgc&?z_hge")
 by (rule zenon_and_1 [OF z_Hmo])
 have z_Hgc: "?z_hgc"
 by (rule zenon_and_0 [OF z_Hgb])
 have z_Hge: "?z_hge" (is "?z_hgf&?z_hgh")
 by (rule zenon_and_1 [OF z_Hgb])
 have z_Hgh: "?z_hgh" (is "?z_hgi&?z_hgk")
 by (rule zenon_and_1 [OF z_Hge])
 have z_Hgi: "?z_hgi"
 by (rule zenon_and_0 [OF z_Hgh])
 have z_Hmq_z_Hc: "(~(\\A x:((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK]))))))))))) == (~?z_hjd)" (is "?z_hmq == ?z_hc")
 by (unfold bAll_def)
 have z_Hmq: "?z_hmq" (is "~(\\A x : ?z_hms(x))")
 by (unfold z_Hmq_z_Hc, fact z_Hc)
 have z_Hmt: "(\\E x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))" (is "\\E x : ?z_hmu(x)")
 by (rule zenon_notallex_0 [of "?z_hms", OF z_Hmq])
 have z_Hmv: "?z_hmu((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK]))))))))))))" (is "~(?z_hmw=>?z_hmx)")
 by (rule zenon_ex_choose_0 [of "?z_hmu", OF z_Hmt])
 have z_Hmw: "?z_hmw"
 by (rule zenon_notimply_0 [OF z_Hmv])
 have z_Hmy: "(~?z_hmx)"
 by (rule zenon_notimply_1 [OF z_Hmv])
 have z_Hmz_z_Hmy: "(~(\\A x:((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))) == (~?z_hmx)" (is "?z_hmz == ?z_hmy")
 by (unfold bAll_def)
 have z_Hmz: "?z_hmz" (is "~(\\A x : ?z_hnb(x))")
 by (unfold z_Hmz_z_Hmy, fact z_Hmy)
 have z_Hnc: "(\\E x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK])))))))))" (is "\\E x : ?z_hnd(x)")
 by (rule zenon_notallex_0 [of "?z_hnb", OF z_Hmz])
 have z_Hne: "?z_hnd((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))))" (is "~(?z_hnf=>?z_hng)")
 by (rule zenon_ex_choose_0 [of "?z_hnd", OF z_Hnc])
 have z_Hnf: "?z_hnf"
 by (rule zenon_notimply_0 [OF z_Hne])
 have z_Hnh: "(~?z_hng)"
 by (rule zenon_notimply_1 [OF z_Hne])
 have z_Hni_z_Hnh: "(~(\\A x:((x \\in Node)=>(((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=x)&(a_voteshash_primea=a_voteshash_primea))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))), (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))) \\in (a_voteshash_primea[x]))))))) == (~?z_hng)" (is "?z_hni == ?z_hnh")
 by (unfold bAll_def)
 have z_Hni: "?z_hni" (is "~(\\A x : ?z_hnk(x))")
 by (unfold z_Hni_z_Hnh, fact z_Hnh)
 have z_Hnl: "(\\E x:(~((x \\in Node)=>(((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=x)&(a_voteshash_primea=a_voteshash_primea))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))), (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))) \\in (a_voteshash_primea[x])))))))" (is "\\E x : ?z_hnm(x)")
 by (rule zenon_notallex_0 [of "?z_hnk", OF z_Hni])
 have z_Hnn: "?z_hnm((CHOOSE x:(~((x \\in Node)=>(((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=x)&(a_voteshash_primea=a_voteshash_primea))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))), (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))) \\in (a_voteshash_primea[x]))))))))" (is "~(?z_hno=>?z_hnp)")
 by (rule zenon_ex_choose_0 [of "?z_hnm", OF z_Hnl])
 have z_Hno: "?z_hno"
 by (rule zenon_notimply_0 [OF z_Hnn])
 have z_Hnq: "(~?z_hnp)" (is "~(?z_hnr|?z_hns)")
 by (rule zenon_notimply_1 [OF z_Hnn])
 have z_Hnt: "(~?z_hnr)" (is "~(?z_hnu|?z_hhw)")
 by (rule zenon_notor_0 [OF z_Hnq])
 have z_Hnv: "(~?z_hns)" (is "~~?z_hiy")
 by (rule zenon_notor_1 [OF z_Hnq])
 have z_Hiy: "?z_hiy"
 by (rule zenon_notnot_0 [OF z_Hnv])
 have z_Hnw: "(~?z_hnu)" (is "~(?z_hnx&?z_hhp)")
 by (rule zenon_notor_0 [OF z_Hnt])
 have z_Hny: "(~?z_hhw)" (is "~~?z_hhx")
 by (rule zenon_notor_1 [OF z_Hnt])
 have z_Hhx: "?z_hhx"
 by (rule zenon_notnot_0 [OF z_Hny])
 show FALSE
 proof (rule zenon_notand [OF z_Hnw])
  assume z_Hnz:"((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&?z_hhp)|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))~=(CHOOSE x:(~((x \\in Node)=>(((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&?z_hhp)|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=x)&?z_hhp)|?z_hhw)|(~((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. (((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&?z_hhp)|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))=VARK)&?z_hhp)|(~(<<x, (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((x=VARK)&?z_hhp)|(~(<<VARJ, x>> \\in a_voteunde_msghash_primea)))|(~(VARJ \\in (a_voteshash_primea[VARK])))))))))))>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))) \\in (a_voteshash_primea[x]))))))))" (is "?z_hhe~=?z_hgv")
  have z_Hoa: "(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. ((((?z_hhe=VARK)&?z_hhp)|(~(<<x, ?z_hhe>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))), ?z_hhe>> \\in a_voteunde_msga)" (is "?z_hoa")
  by (rule subst [where P="(\<lambda>zenon_Vmc. (<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. ((((?z_hhe=VARK)&?z_hhp)|(~(<<x, ?z_hhe>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))), ?z_hhe>> \\in zenon_Vmc))", OF z_Hgi z_Hhx])
  have z_Hoe: "?z_hjx(?z_hgv)" (is "_=>?z_hof")
  by (rule zenon_all_0 [of "?z_hjx" "?z_hgv", OF z_Hjo])
  show FALSE
  proof (rule zenon_imply [OF z_Hoe])
   assume z_Hog:"(~?z_hno)"
   show FALSE
   by (rule notE [OF z_Hog z_Hno])
  next
   assume z_Hof:"?z_hof"
   have z_Hoh_z_Hof: "(\\A x:((x \\in Node)=>((<<x, ?z_hgv>> \\in a_voteunde_msga)|(~(x \\in (votes[?z_hgv])))))) == ?z_hof" (is "?z_hoh == _")
   by (unfold bAll_def)
   have z_Hoh: "?z_hoh" (is "\\A x : ?z_hoo(x)")
   by (unfold z_Hoh_z_Hof, fact z_Hof)
   have z_Hop: "?z_hoo((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. ((((?z_hhe=VARK)&?z_hhp)|(~(<<x, ?z_hhe>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))))" (is "_=>?z_hoq")
   by (rule zenon_all_0 [of "?z_hoo" "(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. ((((?z_hhe=VARK)&?z_hhp)|(~(<<x, ?z_hhe>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK])))))))))", OF z_Hoh])
   show FALSE
   proof (rule zenon_imply [OF z_Hop])
    assume z_Hor:"(~?z_hnf)"
    show FALSE
    by (rule notE [OF z_Hor z_Hnf])
   next
    assume z_Hoq:"?z_hoq" (is "?z_hos|?z_hiw")
    show FALSE
    proof (rule zenon_or [OF z_Hoq])
     assume z_Hos:"?z_hos"
     have z_Hot: "?z_hkm((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. ((((?z_hhe=VARK)&?z_hhp)|(~(<<x, ?z_hhe>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))))" (is "_=>?z_hou")
     by (rule zenon_all_0 [of "?z_hkm" "(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. ((((?z_hhe=VARK)&?z_hhp)|(~(<<x, ?z_hhe>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK])))))))))", OF z_Hjy])
     show FALSE
     proof (rule zenon_imply [OF z_Hot])
      assume z_Hor:"(~?z_hnf)"
      show FALSE
      by (rule notE [OF z_Hor z_Hnf])
     next
      assume z_Hou:"?z_hou"
      have z_Hov_z_Hou: "(\\A x:((x \\in Node)=>bAll(Node, (\<lambda>VARK. ((((x=VARK)&(votes=votes))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. ((((?z_hhe=VARK)&?z_hhp)|(~(<<x, ?z_hhe>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))), VARK>> \\in a_voteunde_msga)))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. ((((?z_hhe=VARK)&?z_hhp)|(~(<<x, ?z_hhe>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))), x>> \\in a_voteunde_msga))))))) == ?z_hou" (is "?z_hov == _")
      by (unfold bAll_def)
      have z_Hov: "?z_hov" (is "\\A x : ?z_hpi(x)")
      by (unfold z_Hov_z_Hou, fact z_Hou)
      have z_Hpj: "?z_hpi(?z_hhe)" (is "_=>?z_hpk")
      by (rule zenon_all_0 [of "?z_hpi" "?z_hhe", OF z_Hov])
      show FALSE
      proof (rule zenon_imply [OF z_Hpj])
       assume z_Hpl:"(~?z_hmw)"
       show FALSE
       by (rule notE [OF z_Hpl z_Hmw])
      next
       assume z_Hpk:"?z_hpk"
       have z_Hpm_z_Hpk: "(\\A x:((x \\in Node)=>((((?z_hhe=x)&(votes=votes))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. ((((?z_hhe=VARK)&?z_hhp)|(~(<<x, ?z_hhe>> \\in a_voteunde_msghash_primea)))|(~(x \\in (a_voteshash_primea[VARK]))))))))), x>> \\in a_voteunde_msga)))|(~?z_hoa)))) == ?z_hpk" (is "?z_hpm == _")
       by (unfold bAll_def)
       have z_Hpm: "?z_hpm" (is "\\A x : ?z_hps(x)")
       by (unfold z_Hpm_z_Hpk, fact z_Hpk)
       have z_Hpt: "?z_hps(?z_hgv)" (is "_=>?z_hpu")
       by (rule zenon_all_0 [of "?z_hps" "?z_hgv", OF z_Hpm])
       show FALSE
       proof (rule zenon_imply [OF z_Hpt])
        assume z_Hog:"(~?z_hno)"
        show FALSE
        by (rule notE [OF z_Hog z_Hno])
       next
        assume z_Hpu:"?z_hpu" (is "?z_hpv|?z_hpr")
        show FALSE
        proof (rule zenon_or [OF z_Hpu])
         assume z_Hpv:"?z_hpv" (is "?z_hpw|?z_hpx")
         show FALSE
         proof (rule zenon_or [OF z_Hpv])
          assume z_Hpw:"?z_hpw" (is "_&?z_hen")
          have z_Hnx: "?z_hnx"
          by (rule zenon_and_0 [OF z_Hpw])
          show FALSE
          by (rule notE [OF z_Hnz z_Hnx])
         next
          assume z_Hpx:"?z_hpx"
          show FALSE
          by (rule notE [OF z_Hpx z_Hos])
         qed
        next
         assume z_Hpr:"?z_hpr"
         show FALSE
         by (rule notE [OF z_Hpr z_Hoa])
        qed
       qed
      qed
     qed
    next
     assume z_Hiw:"?z_hiw" (is "~?z_hix")
     show FALSE
     by (rule zenon_L2_ [OF z_Hiw z_Hiy z_Hgc])
    qed
   qed
  qed
 next
  assume z_Hpy:"(a_voteshash_primea~=a_voteshash_primea)"
  show FALSE
  by (rule zenon_noteq [OF z_Hpy])
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 221"; *} qed
lemma ob'223:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
fixes Node
fixes Quorum
fixes Value
fixes a_voteunde_requestunde_msga a_voteunde_requestunde_msga'
fixes voted voted'
fixes a_voteunde_msga a_voteunde_msga'
fixes votes votes'
fixes leader leader'
fixes decided decided'
fixes a_requnde_historya a_requnde_historya'
(* usable definition vars suppressed *)
(* usable definition Spec suppressed *)
(* usable definition Symmetry suppressed *)
(* usable definition Safety suppressed *)
(* usable definition SplitVote suppressed *)
(* usable definition Liveness suppressed *)
assumes v'26: "(((((((a_voteunde_requestunde_msga) \<in> ((SUBSET (((Node) \<times> (Node))))))) & (((voted) \<in> ([(Node) \<rightarrow> (BOOLEAN)]))) & (((a_voteunde_msga) \<in> ((SUBSET (((Node) \<times> (Node))))))) & (((votes) \<in> ([(Node) \<rightarrow> ((SUBSET (Node)))]))) & (((leader) \<in> ([(Node) \<rightarrow> (BOOLEAN)]))) & (((decided) \<in> ([(Node) \<rightarrow> ((SUBSET (Value)))])))) & (\<forall> a_n1a \<in> (Node) : (\<forall> a_n2a \<in> (Node) : (\<forall> a_v1a \<in> (Value) : (\<forall> a_v2a \<in> (Value) : (((((((a_v1a) \<in> (fapply ((decided), (a_n1a))))) \<and> (((a_v2a) \<in> (fapply ((decided), (a_n2a))))))) \<Rightarrow> (((a_v1a) = (a_v2a))))))))) & (\<forall> VARI \<in> (Node) : (\<forall> VARJ \<in> (Node) : (((((<<(VARJ), (VARI)>>) \<in> (a_voteunde_msga))) \<or> ((~ (((VARJ) \<in> (fapply ((votes), (VARI))))))))))) & (\<forall> VARI \<in> (Node) : (\<exists> QJ \<in> (Quorum) : (\<forall> VALI \<in> (Value) : (((((QJ) \<subseteq> (fapply ((votes), (VARI))))) \<or> ((~ (((VALI) \<in> (fapply ((decided), (VARI)))))))))))) & (\<forall> VARI \<in> (Node) : (\<forall> VARJ \<in> (Node) : (((fapply ((voted), (VARI))) \<or> ((~ (((<<(VARI), (VARJ)>>) \<in> (a_voteunde_msga))))))))) & (\<forall> VARI \<in> (Node) : (\<exists> QJ \<in> (Quorum) : (((((QJ) \<subseteq> (fapply ((votes), (VARI))))) \<or> ((~ (fapply ((leader), (VARI))))))))) & (\<forall> VARI \<in> (Node) : (\<forall> VALI \<in> (Value) : (((fapply ((leader), (VARI))) \<or> ((~ (((VALI) \<in> (fapply ((decided), (VARI))))))))))) & (\<forall> VARI \<in> (Node) : (\<forall> VARJ \<in> (Node) : (\<forall> VARK \<in> (Node) : (((((((((VARI) = (VARK))) \<and> (((votes) = (votes))))) \<or> ((~ (((<<(VARJ), (VARI)>>) \<in> (a_voteunde_msga))))))) \<or> ((~ (((VARJ) \<in> (fapply ((votes), (VARK)))))))))))) & (\<forall> VARI \<in> (Node) : (\<forall> VARJ \<in> (Node) : (\<forall> VARK \<in> (Node) : (((((((((VARJ) = (VARK))) \<and> (((votes) = (votes))))) \<or> ((~ (((<<(VARI), (VARK)>>) \<in> (a_voteunde_msga))))))) \<or> ((~ (((<<(VARI), (VARJ)>>) \<in> (a_voteunde_msga))))))))))) \<and> ((((\<exists> i \<in> (Node) : (\<exists> j \<in> (Node) : (((~ (fapply ((voted), (i))))) & (((<<(j), (i)>>) \<in> (a_voteunde_requestunde_msga))) & ((((a_voteunde_requestunde_msghash_primea :: c)) = (((a_voteunde_requestunde_msga) \\ ({(<<(j), (i)>>)}))))) & ((((a_voteunde_msghash_primea :: c)) = (((a_voteunde_msga) \<union> ({(<<(i), (j)>>)}))))) & ((((a_votedhash_primea :: c)) = ([(voted) EXCEPT ![(i)] = (TRUE)]))) & ((((a_voteshash_primea :: c)) = (votes))) & ((((a_decidedhash_primea :: c)) = (decided))) & ((((a_leaderhash_primea :: c)) = (leader))) & ((((a_requnde_historyhash_primea :: c)) = (a_requnde_historya)))))) | (\<exists> i \<in> (Node) : (\<exists> j \<in> (Node) : ((fapply ((voted), (i))) & ((((a_voteunde_requestunde_msghash_primea :: c)) = (((a_voteunde_requestunde_msga) \\ ({(<<(j), (i)>>)}))))) & ((((a_voteunde_msghash_primea :: c)) = (a_voteunde_msga))) & ((((a_votedhash_primea :: c)) = (voted))) & ((((a_voteshash_primea :: c)) = (votes))) & ((((a_decidedhash_primea :: c)) = (decided))) & ((((a_leaderhash_primea :: c)) = (leader))) & ((((a_requnde_historyhash_primea :: c)) = (a_requnde_historya)))))) | (\<exists> i \<in> (Node) : (\<exists> j \<in> (Node) : ((((<<(j), (i)>>) \<in> (a_voteunde_msga))) & ((((a_voteshash_primea :: c)) = ([(votes) EXCEPT ![(i)] = (((fapply ((votes), (i))) \<union> ({(j)})))]))) & ((((a_votedhash_primea :: c)) = (voted))) & ((((a_voteunde_msghash_primea :: c)) = (a_voteunde_msga))) & ((((a_leaderhash_primea :: c)) = (leader))) & ((((a_decidedhash_primea :: c)) = (decided))) & ((((a_voteunde_requestunde_msghash_primea :: c)) = (a_voteunde_requestunde_msga))) & ((((a_requnde_historyhash_primea :: c)) = (a_requnde_historya)))))) | (\<exists> i \<in> (Node) : (\<exists> Q \<in> (Quorum) : ((((Q) \<subseteq> (fapply ((votes), (i))))) & ((((a_leaderhash_primea :: c)) = ([(leader) EXCEPT ![(i)] = (TRUE)]))) & ((((a_voteshash_primea :: c)) = (votes))) & ((((a_votedhash_primea :: c)) = (voted))) & ((((a_voteunde_msghash_primea :: c)) = (a_voteunde_msga))) & ((((a_decidedhash_primea :: c)) = (decided))) & ((((a_voteunde_requestunde_msghash_primea :: c)) = (a_voteunde_requestunde_msga))) & ((((a_requnde_historyhash_primea :: c)) = (a_requnde_historya)))))) | (\<exists> i \<in> (Node) : (\<exists> j \<in> (Node) : (\<exists> v \<in> (Value) : ((fapply ((leader), (i))) & ((({}) = (fapply ((decided), (i))))) & ((((a_decidedhash_primea :: c)) = ([(decided) EXCEPT ![(i)] = (((fapply ((decided), (i))) \<union> ({(v)})))]))) & ((((a_voteshash_primea :: c)) = (votes))) & ((((a_votedhash_primea :: c)) = (voted))) & ((((a_voteunde_msghash_primea :: c)) = (a_voteunde_msga))) & ((((a_leaderhash_primea :: c)) = (leader))) & ((((a_voteunde_requestunde_msghash_primea :: c)) = (a_voteunde_requestunde_msga))) & ((((a_requnde_historyhash_primea :: c)) = (a_requnde_historya)))))))) \<or> (\<exists> i \<in> (Node) : (\<exists> j \<in> (Node) : ((((<<(i), (j)>>) \<notin> (a_requnde_historya))) & (\<forall> a_dst2a \<in> (Node) : (((<<(i), (a_dst2a)>>) \<notin> (a_voteunde_requestunde_msga)))) & ((((a_voteunde_requestunde_msghash_primea :: c)) = (((a_voteunde_requestunde_msga) \<union> ({(<<(i), (j)>>)}))))) & ((((a_requnde_historyhash_primea :: c)) = (((a_requnde_historya) \<union> ({(<<(i), (j)>>)}))))) & (((((a_votedhash_primea :: c)) = (voted))) & ((((a_voteunde_msghash_primea :: c)) = (a_voteunde_msga))) & ((((a_voteshash_primea :: c)) = (votes))) & ((((a_leaderhash_primea :: c)) = (leader))) & ((((a_decidedhash_primea :: c)) = (decided)))))))))))"
shows "(\<forall> VARI \<in> (Node) : (\<forall> VARJ \<in> (Node) : (\<forall> VARK \<in> (Node) : (((((((((VARJ) = (VARK))) \<and> ((((a_voteshash_primea :: c)) = ((a_voteshash_primea :: c)))))) \<or> ((~ (((<<(VARI), (VARK)>>) \<in> ((a_voteunde_msghash_primea :: c)))))))) \<or> ((~ (((<<(VARI), (VARJ)>>) \<in> ((a_voteunde_msghash_primea :: c)))))))))))"(is "PROP ?ob'223")
proof -
ML_command {* writeln "*** TLAPS ENTER 223"; *}
show "PROP ?ob'223"

(* BEGIN ZENON INPUT
;; file=consensus_epr_IndProofs.tlaps/tlapm_ecc290.znn; PATH='/home/egolf/.opam/4.07.1/bin:/home/egolf/.local/bin:/home/egolf/bin:/home/egolf/mambaforge/bin:/home/egolf/mambaforge/condabin:/home/egolf/.opam/4.07.1/bin:/home/egolf/.local/bin:/home/egolf/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/home/egolf/.local/bin/gurobi952/linux64/bin:/home/egolf/Projects/apalache/bin:/home/egolf/opt/foxitsoftware/foxitreader:/home/egolf/.local/bin/gurobi952/linux64/bin:/home/egolf/Projects/apalache/bin:/home/egolf/opt/foxitsoftware/foxitreader:/usr/local/bin:/usr/local/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >consensus_epr_IndProofs.tlaps/tlapm_ecc290.znn.out
;; obligation #223
$hyp "v'26" (/\ (/\ (/\ (TLA.in a_voteunde_requestunde_msga
(TLA.SUBSET (TLA.prod Node Node))) (TLA.in voted
(TLA.FuncSet Node (TLA.set T. F.))) (TLA.in a_voteunde_msga
(TLA.SUBSET (TLA.prod Node Node))) (TLA.in votes
(TLA.FuncSet Node (TLA.SUBSET Node))) (TLA.in leader
(TLA.FuncSet Node (TLA.set T. F.))) (TLA.in decided
(TLA.FuncSet Node (TLA.SUBSET Value))))
(TLA.bAll Node ((a_n1a) (TLA.bAll Node ((a_n2a) (TLA.bAll Value ((a_v1a) (TLA.bAll Value ((a_v2a) (=> (/\ (TLA.in a_v1a
(TLA.fapply decided a_n1a)) (TLA.in a_v2a (TLA.fapply decided a_n2a)))
(= a_v1a a_v2a))))))))))
(TLA.bAll Node ((VARI) (TLA.bAll Node ((VARJ) (\/ (TLA.in (TLA.tuple VARJ
VARI) a_voteunde_msga) (-. (TLA.in VARJ (TLA.fapply votes VARI))))))))
(TLA.bAll Node ((VARI) (TLA.bEx Quorum ((QJ) (TLA.bAll Value ((VALI) (\/ (TLA.subseteq QJ
(TLA.fapply votes VARI)) (-. (TLA.in VALI (TLA.fapply decided VARI))))))))))
(TLA.bAll Node ((VARI) (TLA.bAll Node ((VARJ) (\/ (TLA.fapply voted VARI)
(-. (TLA.in (TLA.tuple VARI VARJ) a_voteunde_msga)))))))
(TLA.bAll Node ((VARI) (TLA.bEx Quorum ((QJ) (\/ (TLA.subseteq QJ
(TLA.fapply votes VARI)) (-. (TLA.fapply leader VARI)))))))
(TLA.bAll Node ((VARI) (TLA.bAll Value ((VALI) (\/ (TLA.fapply leader VARI)
(-. (TLA.in VALI (TLA.fapply decided VARI))))))))
(TLA.bAll Node ((VARI) (TLA.bAll Node ((VARJ) (TLA.bAll Node ((VARK) (\/ (\/ (/\ (= VARI
VARK) (= votes votes)) (-. (TLA.in (TLA.tuple VARJ VARI) a_voteunde_msga)))
(-. (TLA.in VARJ (TLA.fapply votes VARK))))))))))
(TLA.bAll Node ((VARI) (TLA.bAll Node ((VARJ) (TLA.bAll Node ((VARK) (\/ (\/ (/\ (= VARJ
VARK) (= votes votes)) (-. (TLA.in (TLA.tuple VARI VARK) a_voteunde_msga)))
(-. (TLA.in (TLA.tuple VARI VARJ) a_voteunde_msga))))))))))
(\/ (\/ (TLA.bEx Node ((i) (TLA.bEx Node ((j) (/\ (-. (TLA.fapply voted i))
(TLA.in (TLA.tuple j i) a_voteunde_requestunde_msga)
(= a_voteunde_requestunde_msghash_primea
(TLA.setminus a_voteunde_requestunde_msga (TLA.set (TLA.tuple j i))))
(= a_voteunde_msghash_primea (TLA.cup a_voteunde_msga (TLA.set (TLA.tuple i
j)))) (= a_votedhash_primea (TLA.except voted i T.)) (= a_voteshash_primea
votes) (= a_decidedhash_primea decided) (= a_leaderhash_primea leader)
(= a_requnde_historyhash_primea a_requnde_historya))))))
(TLA.bEx Node ((i) (TLA.bEx Node ((j) (/\ (TLA.fapply voted i)
(= a_voteunde_requestunde_msghash_primea
(TLA.setminus a_voteunde_requestunde_msga (TLA.set (TLA.tuple j i))))
(= a_voteunde_msghash_primea a_voteunde_msga) (= a_votedhash_primea voted)
(= a_voteshash_primea votes) (= a_decidedhash_primea decided)
(= a_leaderhash_primea leader) (= a_requnde_historyhash_primea
a_requnde_historya))))))
(TLA.bEx Node ((i) (TLA.bEx Node ((j) (/\ (TLA.in (TLA.tuple j i)
a_voteunde_msga) (= a_voteshash_primea
(TLA.except votes i (TLA.cup (TLA.fapply votes i) (TLA.set j))))
(= a_votedhash_primea voted) (= a_voteunde_msghash_primea a_voteunde_msga)
(= a_leaderhash_primea leader) (= a_decidedhash_primea decided)
(= a_voteunde_requestunde_msghash_primea a_voteunde_requestunde_msga)
(= a_requnde_historyhash_primea a_requnde_historya))))))
(TLA.bEx Node ((i) (TLA.bEx Quorum ((Q) (/\ (TLA.subseteq Q
(TLA.fapply votes i)) (= a_leaderhash_primea (TLA.except leader i T.))
(= a_voteshash_primea votes) (= a_votedhash_primea voted)
(= a_voteunde_msghash_primea a_voteunde_msga) (= a_decidedhash_primea
decided) (= a_voteunde_requestunde_msghash_primea
a_voteunde_requestunde_msga) (= a_requnde_historyhash_primea
a_requnde_historya))))))
(TLA.bEx Node ((i) (TLA.bEx Node ((j) (TLA.bEx Value ((v) (/\ (TLA.fapply leader i)
(= TLA.emptyset (TLA.fapply decided i)) (= a_decidedhash_primea
(TLA.except decided i (TLA.cup (TLA.fapply decided i) (TLA.set v))))
(= a_voteshash_primea votes) (= a_votedhash_primea voted)
(= a_voteunde_msghash_primea a_voteunde_msga) (= a_leaderhash_primea leader)
(= a_voteunde_requestunde_msghash_primea a_voteunde_requestunde_msga)
(= a_requnde_historyhash_primea a_requnde_historya)))))))))
(TLA.bEx Node ((i) (TLA.bEx Node ((j) (/\ (-. (TLA.in (TLA.tuple i j)
a_requnde_historya)) (TLA.bAll Node ((a_dst2a) (-. (TLA.in (TLA.tuple i
a_dst2a) a_voteunde_requestunde_msga))))
(= a_voteunde_requestunde_msghash_primea (TLA.cup a_voteunde_requestunde_msga
(TLA.set (TLA.tuple i j)))) (= a_requnde_historyhash_primea
(TLA.cup a_requnde_historya (TLA.set (TLA.tuple i j))))
(/\ (= a_votedhash_primea voted) (= a_voteunde_msghash_primea
a_voteunde_msga) (= a_voteshash_primea votes) (= a_leaderhash_primea leader)
(= a_decidedhash_primea
decided)))))))))
$goal (TLA.bAll Node ((VARI) (TLA.bAll Node ((VARJ) (TLA.bAll Node ((VARK) (\/ (\/ (/\ (= VARJ
VARK) (= a_voteshash_primea a_voteshash_primea)) (-. (TLA.in (TLA.tuple VARI
VARK) a_voteunde_msghash_primea))) (-. (TLA.in (TLA.tuple VARI VARJ)
a_voteunde_msghash_primea)))))))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Ha:"((((a_voteunde_requestunde_msga \\in SUBSET(prod(Node, Node)))&((voted \\in FuncSet(Node, {TRUE, FALSE}))&((a_voteunde_msga \\in SUBSET(prod(Node, Node)))&((votes \\in FuncSet(Node, SUBSET(Node)))&((leader \\in FuncSet(Node, {TRUE, FALSE}))&(decided \\in FuncSet(Node, SUBSET(Value))))))))&(bAll(Node, (\<lambda>a_n1a. bAll(Node, (\<lambda>a_n2a. bAll(Value, (\<lambda>a_v1a. bAll(Value, (\<lambda>a_v2a. (((a_v1a \\in (decided[a_n1a]))&(a_v2a \\in (decided[a_n2a])))=>(a_v1a=a_v2a))))))))))&(bAll(Node, (\<lambda>VARI. bAll(Node, (\<lambda>VARJ. ((<<VARJ, VARI>> \\in a_voteunde_msga)|(~(VARJ \\in (votes[VARI]))))))))&(bAll(Node, (\<lambda>VARI. bEx(Quorum, (\<lambda>QJ. bAll(Value, (\<lambda>VALI. ((QJ \\subseteq (votes[VARI]))|(~(VALI \\in (decided[VARI]))))))))))&(bAll(Node, (\<lambda>VARI. bAll(Node, (\<lambda>VARJ. ((voted[VARI])|(~(<<VARI, VARJ>> \\in a_voteunde_msga)))))))&(bAll(Node, (\<lambda>VARI. bEx(Quorum, (\<lambda>QJ. ((QJ \\subseteq (votes[VARI]))|(~(leader[VARI])))))))&(bAll(Node, (\<lambda>VARI. bAll(Value, (\<lambda>VALI. ((leader[VARI])|(~(VALI \\in (decided[VARI]))))))))&(bAll(Node, (\<lambda>VARI. bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARI=VARK)&(votes=votes))|(~(<<VARJ, VARI>> \\in a_voteunde_msga)))|(~(VARJ \\in (votes[VARK]))))))))))&bAll(Node, (\<lambda>VARI. bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(votes=votes))|(~(<<VARI, VARK>> \\in a_voteunde_msga)))|(~(<<VARI, VARJ>> \\in a_voteunde_msga)))))))))))))))))&((bEx(Node, (\<lambda>i. bEx(Node, (\<lambda>j. ((~(voted[i]))&((<<j, i>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, i>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<i, j>>}))&((a_votedhash_primea=except(voted, i, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))|(bEx(Node, (\<lambda>i. bEx(Node, (\<lambda>j. ((voted[i])&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, i>>}))&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_votedhash_primea=voted)&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))|(bEx(Node, (\<lambda>i. bEx(Node, (\<lambda>j. ((<<j, i>> \\in a_voteunde_msga)&((a_voteshash_primea=except(votes, i, ((votes[i]) \\cup {j})))&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_decidedhash_primea=decided)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))|(bEx(Node, (\<lambda>i. bEx(Quorum, (\<lambda>Q. ((Q \\subseteq (votes[i]))&((a_leaderhash_primea=except(leader, i, TRUE))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_decidedhash_primea=decided)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))|bEx(Node, (\<lambda>i. bEx(Node, (\<lambda>j. bEx(Value, (\<lambda>v. ((leader[i])&(({}=(decided[i]))&((a_decidedhash_primea=except(decided, i, ((decided[i]) \\cup {v})))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))))))))|bEx(Node, (\<lambda>i. bEx(Node, (\<lambda>j. ((~(<<i, j>> \\in a_requnde_historya))&(bAll(Node, (\<lambda>a_dst2a. (~(<<i, a_dst2a>> \\in a_voteunde_requestunde_msga))))&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\cup {<<i, j>>}))&((a_requnde_historyhash_primea=(a_requnde_historya \\cup {<<i, j>>}))&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_voteshash_primea=votes)&((a_leaderhash_primea=leader)&(a_decidedhash_primea=decided)))))))))))))))" (is "?z_hc&?z_hfe")
 using v'26 by blast
 have zenon_L1_: "(\\A zenon_Vda:((zenon_Vda \\in Node)=>((voted[zenon_Vda]) \\in {TRUE, FALSE}))) ==> ((CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))) \\in Node) ==> ((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea))))))))))=(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))) ==> (voted[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea))))))))))]) ==> (~(voted[(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))])) ==> FALSE" (is "?z_hkf ==> ?z_hkl ==> ?z_hlk ==> ?z_hmc ==> ?z_hmd ==> FALSE")
 proof -
  assume z_Hkf:"?z_hkf" (is "\\A x : ?z_hmf(x)")
  assume z_Hkl:"?z_hkl"
  assume z_Hlk:"?z_hlk" (is "?z_hll=?z_hkm")
  assume z_Hmc:"?z_hmc"
  assume z_Hmd:"?z_hmd" (is "~?z_hme")
  have z_Hmg: "?z_hmf(?z_hkm)" (is "_=>?z_hmh")
  by (rule zenon_all_0 [of "?z_hmf" "?z_hkm", OF z_Hkf])
  show FALSE
  proof (rule zenon_imply [OF z_Hmg])
   assume z_Hmi:"(~?z_hkl)"
   show FALSE
   by (rule notE [OF z_Hmi z_Hkl])
  next
   assume z_Hmh:"?z_hmh"
   show FALSE
   proof (rule zenon_in_addElt [of "?z_hme" "TRUE" "{FALSE}", OF z_Hmh])
    assume z_Hmk:"(?z_hme=TRUE)" (is "_=?z_ho")
    have z_Hme: "?z_hme"
    by (rule zenon_eq_x_true_0 [of "?z_hme", OF z_Hmk])
    show FALSE
    by (rule notE [OF z_Hmd z_Hme])
   next
    assume z_Hml:"(?z_hme \\in {FALSE})" (is "?z_hml")
    show FALSE
    proof (rule zenon_in_addElt [of "?z_hme" "FALSE" "{}", OF z_Hml])
     assume z_Hmn:"(?z_hme=FALSE)" (is "_=?z_hp")
     show FALSE
     proof (rule zenon_p_eq_l [of "?z_hmc" "?z_hme" "?z_hp", OF z_Hmc z_Hmn])
      assume z_Hmo:"(?z_hmc~=?z_hme)"
      show FALSE
      proof (rule zenon_noteq [of "?z_hme"])
       have z_Hmp: "(?z_hme~=?z_hme)"
       by (rule subst [where P="(\<lambda>zenon_Vgjb. ((voted[zenon_Vgjb])~=?z_hme))", OF z_Hlk], fact z_Hmo)
       thus "(?z_hme~=?z_hme)" .
      qed
     next
      assume z_Hp:"?z_hp"
      show FALSE
      by (rule z_Hp)
     qed
    next
     assume z_Hmu:"(?z_hme \\in {})" (is "?z_hmu")
     show FALSE
     by (rule zenon_in_emptyset [of "?z_hme", OF z_Hmu])
    qed
   qed
  qed
 qed
 have zenon_L2_: "(a_voteunde_msghash_primea=a_voteunde_msga) ==> (~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), VARK>> \\in a_voteunde_msghash_primea)))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), x>> \\in a_voteunde_msghash_primea))))))))>> \\in a_voteunde_msga)) ==> (<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), VARK>> \\in a_voteunde_msghash_primea)))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), x>> \\in a_voteunde_msghash_primea))))))))>> \\in a_voteunde_msghash_primea) ==> FALSE" (is "?z_hhb ==> ?z_hmv ==> ?z_hnn ==> FALSE")
 proof -
  assume z_Hhb:"?z_hhb"
  assume z_Hmv:"?z_hmv" (is "~?z_hmw")
  assume z_Hnn:"?z_hnn"
  have z_Hno: "(~?z_hnn)"
  by (rule ssubst [where P="(\<lambda>zenon_Vcl. (~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), VARK>> \\in a_voteunde_msghash_primea)))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), x>> \\in a_voteunde_msghash_primea))))))))>> \\in zenon_Vcl)))", OF z_Hhb z_Hmv])
  show FALSE
  by (rule notE [OF z_Hno z_Hnn])
 qed
 have zenon_L3_: "(a_voteunde_msghash_primea=a_voteunde_msga) ==> (~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), (CHOOSE x:(~((x \\in Node)=>(((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), VARK>> \\in a_voteunde_msghash_primea)))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), x>> \\in a_voteunde_msghash_primea))))))))=x)&(a_voteshash_primea=a_voteshash_primea))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), x>> \\in a_voteunde_msghash_primea)))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), VARK>> \\in a_voteunde_msghash_primea)))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), x>> \\in a_voteunde_msghash_primea))))))))>> \\in a_voteunde_msghash_primea))))))>> \\in a_voteunde_msga)) ==> (<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), (CHOOSE x:(~((x \\in Node)=>(((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), VARK>> \\in a_voteunde_msghash_primea)))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), x>> \\in a_voteunde_msghash_primea))))))))=x)&(a_voteshash_primea=a_voteshash_primea))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), x>> \\in a_voteunde_msghash_primea)))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), VARK>> \\in a_voteunde_msghash_primea)))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), x>> \\in a_voteunde_msghash_primea))))))))>> \\in a_voteunde_msghash_primea))))))>> \\in a_voteunde_msghash_primea) ==> FALSE" (is "?z_hhb ==> ?z_hnt ==> ?z_hod ==> FALSE")
 proof -
  assume z_Hhb:"?z_hhb"
  assume z_Hnt:"?z_hnt" (is "~?z_hnu")
  assume z_Hod:"?z_hod"
  have z_Hoe: "(~?z_hod)"
  by (rule ssubst [where P="(\<lambda>zenon_Vok. (~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), (CHOOSE x:(~((x \\in Node)=>(((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), VARK>> \\in a_voteunde_msghash_primea)))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), x>> \\in a_voteunde_msghash_primea))))))))=x)&(a_voteshash_primea=a_voteshash_primea))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), x>> \\in a_voteunde_msghash_primea)))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), VARK>> \\in a_voteunde_msghash_primea)))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), x>> \\in a_voteunde_msghash_primea))))))))>> \\in a_voteunde_msghash_primea))))))>> \\in zenon_Vok)))", OF z_Hhb z_Hnt])
  show FALSE
  by (rule notE [OF z_Hoe z_Hod])
 qed
 have zenon_L4_: "(\\A x:((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(votes=votes))|(~(<<x, VARK>> \\in a_voteunde_msga)))|(~(<<x, VARJ>> \\in a_voteunde_msga))))))))) ==> ((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))) \\in Node) ==> ((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), VARK>> \\in a_voteunde_msghash_primea)))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), x>> \\in a_voteunde_msghash_primea)))))))) \\in Node) ==> ((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), VARK>> \\in a_voteunde_msghash_primea)))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), x>> \\in a_voteunde_msghash_primea))))))))~=(CHOOSE x:(~((x \\in Node)=>(((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), VARK>> \\in a_voteunde_msghash_primea)))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), x>> \\in a_voteunde_msghash_primea))))))))=x)&(a_voteshash_primea=a_voteshash_primea))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), x>> \\in a_voteunde_msghash_primea)))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), VARK>> \\in a_voteunde_msghash_primea)))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), x>> \\in a_voteunde_msghash_primea))))))))>> \\in a_voteunde_msghash_primea))))))) ==> (a_voteunde_msghash_primea=a_voteunde_msga) ==> (<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), VARK>> \\in a_voteunde_msghash_primea)))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), x>> \\in a_voteunde_msghash_primea))))))))>> \\in a_voteunde_msghash_primea) ==> (<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), (CHOOSE x:(~((x \\in Node)=>(((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), VARK>> \\in a_voteunde_msghash_primea)))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), x>> \\in a_voteunde_msghash_primea))))))))=x)&(a_voteshash_primea=a_voteshash_primea))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), x>> \\in a_voteunde_msghash_primea)))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), VARK>> \\in a_voteunde_msghash_primea)))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), x>> \\in a_voteunde_msghash_primea))))))))>> \\in a_voteunde_msghash_primea))))))>> \\in a_voteunde_msghash_primea) ==> ((CHOOSE x:(~((x \\in Node)=>(((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), VARK>> \\in a_voteunde_msghash_primea)))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), x>> \\in a_voteunde_msghash_primea))))))))=x)&(a_voteshash_primea=a_voteshash_primea))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), x>> \\in a_voteunde_msghash_primea)))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), VARK>> \\in a_voteunde_msghash_primea)))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), x>> \\in a_voteunde_msghash_primea))))))))>> \\in a_voteunde_msghash_primea)))))) \\in Node) ==> FALSE" (is "?z_hoj ==> ?z_hov ==> ?z_how ==> ?z_hox ==> ?z_hhb ==> ?z_hnn ==> ?z_hod ==> ?z_hoy ==> FALSE")
 proof -
  assume z_Hoj:"?z_hoj" (is "\\A x : ?z_hoz(x)")
  assume z_Hov:"?z_hov"
  assume z_How:"?z_how"
  assume z_Hox:"?z_hox" (is "?z_hmy~=?z_hnw")
  assume z_Hhb:"?z_hhb"
  assume z_Hnn:"?z_hnn"
  assume z_Hod:"?z_hod"
  assume z_Hoy:"?z_hoy"
  have z_Hpa: "?z_hoz((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))))" (is "_=>?z_hpb")
  by (rule zenon_all_0 [of "?z_hoz" "(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea))))))))))", OF z_Hoj])
  show FALSE
  proof (rule zenon_imply [OF z_Hpa])
   assume z_Hpc:"(~?z_hov)"
   show FALSE
   by (rule notE [OF z_Hpc z_Hov])
  next
   assume z_Hpb:"?z_hpb"
   have z_Hpd_z_Hpb: "(\\A x:((x \\in Node)=>bAll(Node, (\<lambda>VARK. ((((x=VARK)&(votes=votes))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), VARK>> \\in a_voteunde_msga)))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), x>> \\in a_voteunde_msga))))))) == ?z_hpb" (is "?z_hpd == _")
   by (unfold bAll_def)
   have z_Hpd: "?z_hpd" (is "\\A x : ?z_hpo(x)")
   by (unfold z_Hpd_z_Hpb, fact z_Hpb)
   have z_Hpp: "?z_hpo(?z_hnw)" (is "_=>?z_hpq")
   by (rule zenon_all_0 [of "?z_hpo" "?z_hnw", OF z_Hpd])
   show FALSE
   proof (rule zenon_imply [OF z_Hpp])
    assume z_Hpr:"(~?z_hoy)"
    show FALSE
    by (rule notE [OF z_Hpr z_Hoy])
   next
    assume z_Hpq:"?z_hpq"
    have z_Hps_z_Hpq: "(\\A x:((x \\in Node)=>((((?z_hnw=x)&(votes=votes))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), x>> \\in a_voteunde_msga)))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), ?z_hnw>> \\in a_voteunde_msga))))) == ?z_hpq" (is "?z_hps == _")
    by (unfold bAll_def)
    have z_Hps: "?z_hps" (is "\\A x : ?z_hpy(x)")
    by (unfold z_Hps_z_Hpq, fact z_Hpq)
    have z_Hpz: "?z_hpy(?z_hmy)" (is "_=>?z_hqa")
    by (rule zenon_all_0 [of "?z_hpy" "?z_hmy", OF z_Hps])
    show FALSE
    proof (rule zenon_imply [OF z_Hpz])
     assume z_Hqb:"(~?z_how)"
     show FALSE
     by (rule notE [OF z_Hqb z_How])
    next
     assume z_Hqa:"?z_hqa" (is "?z_hqc|?z_hnt")
     show FALSE
     proof (rule zenon_or [OF z_Hqa])
      assume z_Hqc:"?z_hqc" (is "?z_hqd|?z_hmv")
      show FALSE
      proof (rule zenon_or [OF z_Hqc])
       assume z_Hqd:"?z_hqd" (is "?z_hqe&?z_hem")
       have z_Hqe: "?z_hqe"
       by (rule zenon_and_0 [OF z_Hqd])
       show FALSE
       by (rule zenon_eqsym [OF z_Hqe z_Hox])
      next
       assume z_Hmv:"?z_hmv" (is "~?z_hmw")
       show FALSE
       by (rule zenon_L2_ [OF z_Hhb z_Hmv z_Hnn])
      qed
     next
      assume z_Hnt:"?z_hnt" (is "~?z_hnu")
      show FALSE
      by (rule zenon_L3_ [OF z_Hhb z_Hnt z_Hod])
     qed
    qed
   qed
  qed
 qed
 assume z_Hb:"(~bAll(Node, (\<lambda>VARI. bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<VARI, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<VARI, VARJ>> \\in a_voteunde_msghash_primea))))))))))" (is "~?z_hqf")
 have z_Hc: "?z_hc" (is "?z_hd&?z_hbg")
 by (rule zenon_and_0 [OF z_Ha])
 have z_Hfe: "?z_hfe" (is "?z_hff|?z_hjh")
 by (rule zenon_and_1 [OF z_Ha])
 have z_Hd: "?z_hd" (is "?z_he&?z_hj")
 by (rule zenon_and_0 [OF z_Hc])
 have z_Hbg: "?z_hbg" (is "?z_hbh&?z_hca")
 by (rule zenon_and_1 [OF z_Hc])
 have z_Hca: "?z_hca" (is "?z_hcb&?z_hcn")
 by (rule zenon_and_1 [OF z_Hbg])
 have z_Hcn: "?z_hcn" (is "?z_hco&?z_hdc")
 by (rule zenon_and_1 [OF z_Hca])
 have z_Hdc: "?z_hdc" (is "?z_hdd&?z_hdm")
 by (rule zenon_and_1 [OF z_Hcn])
 have z_Hdd: "?z_hdd"
 by (rule zenon_and_0 [OF z_Hdc])
 have z_Hdm: "?z_hdm" (is "?z_hdn&?z_hdu")
 by (rule zenon_and_1 [OF z_Hdc])
 have z_Hdu: "?z_hdu" (is "?z_hdv&?z_hea")
 by (rule zenon_and_1 [OF z_Hdm])
 have z_Hea: "?z_hea" (is "?z_heb&?z_her")
 by (rule zenon_and_1 [OF z_Hdu])
 have z_Her: "?z_her"
 by (rule zenon_and_1 [OF z_Hea])
 have z_Hj: "?z_hj" (is "?z_hk&?z_hq")
 by (rule zenon_and_1 [OF z_Hd])
 have z_Hk: "?z_hk"
 by (rule zenon_and_0 [OF z_Hj])
 have z_Hoj_z_Her: "(\\A x:((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(votes=votes))|(~(<<x, VARK>> \\in a_voteunde_msga)))|(~(<<x, VARJ>> \\in a_voteunde_msga))))))))) == ?z_her" (is "?z_hoj == _")
 by (unfold bAll_def)
 have z_Hoj: "?z_hoj" (is "\\A x : ?z_hoz(x)")
 by (unfold z_Hoj_z_Her, fact z_Her)
 have z_Hqr_z_Hb: "(~(\\A x:((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))) == (~?z_hqf)" (is "?z_hqr == ?z_hb")
 by (unfold bAll_def)
 have z_Hqr: "?z_hqr" (is "~(\\A x : ?z_hqt(x))")
 by (unfold z_Hqr_z_Hb, fact z_Hb)
 have z_Hqu: "(\\E x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea))))))))))" (is "\\E x : ?z_hqv(x)")
 by (rule zenon_notallex_0 [of "?z_hqt", OF z_Hqr])
 have z_Hqw: "?z_hqv((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))))" (is "~(?z_hov=>?z_hqx)")
 by (rule zenon_ex_choose_0 [of "?z_hqv", OF z_Hqu])
 have z_Hov: "?z_hov"
 by (rule zenon_notimply_0 [OF z_Hqw])
 have z_Hqy: "(~?z_hqx)"
 by (rule zenon_notimply_1 [OF z_Hqw])
 have z_Hqz_z_Hqy: "(~(\\A x:((x \\in Node)=>bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), VARK>> \\in a_voteunde_msghash_primea)))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), x>> \\in a_voteunde_msghash_primea)))))))) == (~?z_hqx)" (is "?z_hqz == ?z_hqy")
 by (unfold bAll_def)
 have z_Hqz: "?z_hqz" (is "~(\\A x : ?z_hrb(x))")
 by (unfold z_Hqz_z_Hqy, fact z_Hqy)
 have z_Hrc: "(\\E x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), VARK>> \\in a_voteunde_msghash_primea)))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), x>> \\in a_voteunde_msghash_primea))))))))" (is "\\E x : ?z_hrd(x)")
 by (rule zenon_notallex_0 [of "?z_hrb", OF z_Hqz])
 have z_Hre: "?z_hrd((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), VARK>> \\in a_voteunde_msghash_primea)))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), x>> \\in a_voteunde_msghash_primea)))))))))" (is "~(?z_how=>?z_hrf)")
 by (rule zenon_ex_choose_0 [of "?z_hrd", OF z_Hrc])
 have z_How: "?z_how"
 by (rule zenon_notimply_0 [OF z_Hre])
 have z_Hrg: "(~?z_hrf)"
 by (rule zenon_notimply_1 [OF z_Hre])
 have z_Hrh_z_Hrg: "(~(\\A x:((x \\in Node)=>(((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), VARK>> \\in a_voteunde_msghash_primea)))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), x>> \\in a_voteunde_msghash_primea))))))))=x)&(a_voteshash_primea=a_voteshash_primea))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), x>> \\in a_voteunde_msghash_primea)))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), VARK>> \\in a_voteunde_msghash_primea)))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), x>> \\in a_voteunde_msghash_primea))))))))>> \\in a_voteunde_msghash_primea)))))) == (~?z_hrf)" (is "?z_hrh == ?z_hrg")
 by (unfold bAll_def)
 have z_Hrh: "?z_hrh" (is "~(\\A x : ?z_hrj(x))")
 by (unfold z_Hrh_z_Hrg, fact z_Hrg)
 have z_Hrk: "(\\E x:(~((x \\in Node)=>(((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), VARK>> \\in a_voteunde_msghash_primea)))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), x>> \\in a_voteunde_msghash_primea))))))))=x)&(a_voteshash_primea=a_voteshash_primea))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), x>> \\in a_voteunde_msghash_primea)))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), VARK>> \\in a_voteunde_msghash_primea)))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), x>> \\in a_voteunde_msghash_primea))))))))>> \\in a_voteunde_msghash_primea))))))" (is "\\E x : ?z_hrl(x)")
 by (rule zenon_notallex_0 [of "?z_hrj", OF z_Hrh])
 have z_Hrm: "?z_hrl((CHOOSE x:(~((x \\in Node)=>(((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), VARK>> \\in a_voteunde_msghash_primea)))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), x>> \\in a_voteunde_msghash_primea))))))))=x)&(a_voteshash_primea=a_voteshash_primea))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), x>> \\in a_voteunde_msghash_primea)))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), (CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. ((((x=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), VARK>> \\in a_voteunde_msghash_primea)))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(a_voteshash_primea=a_voteshash_primea))|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), x>> \\in a_voteunde_msghash_primea))))))))>> \\in a_voteunde_msghash_primea)))))))" (is "~(?z_hoy=>?z_hrn)")
 by (rule zenon_ex_choose_0 [of "?z_hrl", OF z_Hrk])
 have z_Hoy: "?z_hoy"
 by (rule zenon_notimply_0 [OF z_Hrm])
 have z_Hro: "(~?z_hrn)" (is "~(?z_hrp|?z_hno)")
 by (rule zenon_notimply_1 [OF z_Hrm])
 have z_Hrq: "(~?z_hrp)" (is "~(?z_hrr|?z_hoe)")
 by (rule zenon_notor_0 [OF z_Hro])
 have z_Hrs: "(~?z_hno)" (is "~~?z_hnn")
 by (rule zenon_notor_1 [OF z_Hro])
 have z_Hnn: "?z_hnn"
 by (rule zenon_notnot_0 [OF z_Hrs])
 have z_Hrt: "(~?z_hrr)" (is "~(?z_hru&?z_hlv)")
 by (rule zenon_notor_0 [OF z_Hrq])
 have z_Hrv: "(~?z_hoe)" (is "~~?z_hod")
 by (rule zenon_notor_1 [OF z_Hrq])
 have z_Hod: "?z_hod"
 by (rule zenon_notnot_0 [OF z_Hrv])
 show FALSE
 proof (rule zenon_notand [OF z_Hrt])
  assume z_Hox:"((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. ((((x=VARK)&?z_hlv)|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&?z_hlv)|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), VARK>> \\in a_voteunde_msghash_primea)))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&?z_hlv)|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), x>> \\in a_voteunde_msghash_primea))))))))~=(CHOOSE x:(~((x \\in Node)=>(((((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARK. ((((x=VARK)&?z_hlv)|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&?z_hlv)|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), VARK>> \\in a_voteunde_msghash_primea)))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&?z_hlv)|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), x>> \\in a_voteunde_msghash_primea))))))))=x)&?z_hlv)|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&?z_hlv)|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), x>> \\in a_voteunde_msghash_primea)))|?z_hno)))))" (is "?z_hmy~=?z_hnw")
  show FALSE
  proof (rule zenon_or [OF z_Hfe])
   assume z_Hff:"?z_hff" (is "?z_hfg|?z_hgt")
   show FALSE
   proof (rule zenon_or [OF z_Hff])
    assume z_Hfg:"?z_hfg"
    have z_Hrw_z_Hfg: "(\\E x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))) == ?z_hfg" (is "?z_hrw == _")
    by (unfold bEx_def)
    have z_Hrw: "?z_hrw" (is "\\E x : ?z_hrx(x)")
    by (unfold z_Hrw_z_Hfg, fact z_Hfg)
    have z_Hry: "?z_hrx((CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))))" (is "?z_hkl&?z_hrz")
    by (rule zenon_ex_choose_0 [of "?z_hrx", OF z_Hrw])
    have z_Hkl: "?z_hkl"
    by (rule zenon_and_0 [OF z_Hry])
    have z_Hrz: "?z_hrz"
    by (rule zenon_and_1 [OF z_Hry])
    have z_Hsa_z_Hrz: "(\\E x:((x \\in Node)&((~(voted[(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))]))&((<<x, (CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<x, (CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))), x>>}))&((a_votedhash_primea=except(voted, (CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))), TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))) == ?z_hrz" (is "?z_hsa == _")
    by (unfold bEx_def)
    have z_Hsa: "?z_hsa" (is "\\E x : ?z_hss(x)")
    by (unfold z_Hsa_z_Hrz, fact z_Hrz)
    have z_Hst: "?z_hss((CHOOSE x:((x \\in Node)&((~(voted[(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))]))&((<<x, (CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<x, (CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))), x>>}))&((a_votedhash_primea=except(voted, (CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))), TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))" (is "?z_hsv&?z_hsw")
    by (rule zenon_ex_choose_0 [of "?z_hss", OF z_Hsa])
    have z_Hsw: "?z_hsw" (is "?z_hmd&?z_hsx")
    by (rule zenon_and_1 [OF z_Hst])
    have z_Hmd: "?z_hmd" (is "~?z_hme")
    by (rule zenon_and_0 [OF z_Hsw])
    have z_Hsx: "?z_hsx" (is "?z_hsy&?z_hsz")
    by (rule zenon_and_1 [OF z_Hsw])
    have z_Hsz: "?z_hsz" (is "?z_hta&?z_htb")
    by (rule zenon_and_1 [OF z_Hsx])
    have z_Htb: "?z_htb" (is "?z_htc&?z_hsp")
    by (rule zenon_and_1 [OF z_Hsz])
    have z_Htc: "?z_htc" (is "_=?z_htd")
    by (rule zenon_and_0 [OF z_Htb])
    have z_Hkf: "(\\A zenon_Vda:((zenon_Vda \\in Node)=>((voted[zenon_Vda]) \\in {TRUE, FALSE})))" (is "\\A x : ?z_hmf(x)")
    by (rule zenon_in_funcset_2 [of "voted" "Node" "{TRUE, FALSE}", OF z_Hk])
    have z_Hpb: "bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(votes=votes))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&?z_hlv)|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), VARK>> \\in a_voteunde_msga)))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&?z_hlv)|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), VARJ>> \\in a_voteunde_msga)))))))" (is "?z_hpb")
    by (rule zenon_all_in_0 [of "Node" "(\<lambda>VARI. bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&(votes=votes))|(~(<<VARI, VARK>> \\in a_voteunde_msga)))|(~(<<VARI, VARJ>> \\in a_voteunde_msga))))))))", OF z_Her z_Hov])
    have z_Hpd_z_Hpb: "(\\A x:((x \\in Node)=>bAll(Node, (\<lambda>VARK. ((((x=VARK)&(votes=votes))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&?z_hlv)|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), VARK>> \\in a_voteunde_msga)))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&?z_hlv)|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), x>> \\in a_voteunde_msga))))))) == ?z_hpb" (is "?z_hpd == _")
    by (unfold bAll_def)
    have z_Hpd: "?z_hpd" (is "\\A x : ?z_hpo(x)")
    by (unfold z_Hpd_z_Hpb, fact z_Hpb)
    have z_Htm: "bAll(Node, (\<lambda>VARJ. ((voted[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&?z_hlv)|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea))))))))))])|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&?z_hlv)|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), VARJ>> \\in a_voteunde_msga)))))" (is "?z_htm")
    by (rule zenon_all_in_0 [of "Node" "(\<lambda>VARI. bAll(Node, (\<lambda>VARJ. ((voted[VARI])|(~(<<VARI, VARJ>> \\in a_voteunde_msga))))))", OF z_Hdd z_Hov])
    have z_Htp_z_Htm: "(\\A x:((x \\in Node)=>((voted[(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&?z_hlv)|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea))))))))))])|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&?z_hlv)|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), x>> \\in a_voteunde_msga))))) == ?z_htm" (is "?z_htp == _")
    by (unfold bAll_def)
    have z_Htp: "?z_htp" (is "\\A x : ?z_hts(x)")
    by (unfold z_Htp_z_Htm, fact z_Htm)
    have z_Htt: "(\\E zenon_Vrb:(~((~((zenon_Vrb \\in Node)=>bAll(Node, (\<lambda>VARK. ((((zenon_Vrb=VARK)&?z_hlv)|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&?z_hlv)|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), VARK>> \\in a_voteunde_msghash_primea)))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&?z_hlv)|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), zenon_Vrb>> \\in a_voteunde_msghash_primea)))))))<=>(~((zenon_Vrb \\in Node)=>((((?z_hmy=zenon_Vrb)&?z_hlv)|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&?z_hlv)|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), zenon_Vrb>> \\in a_voteunde_msghash_primea)))|?z_hno))))))" (is "\\E x : ?z_hup(x)")
    by (rule zenon_choose_diff_choose_0 [of "?z_hrd" "?z_hrl", OF z_Hox])
    have z_Huq: "?z_hup((CHOOSE zenon_Vrb:(~((~((zenon_Vrb \\in Node)=>bAll(Node, (\<lambda>VARK. ((((zenon_Vrb=VARK)&?z_hlv)|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&?z_hlv)|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), VARK>> \\in a_voteunde_msghash_primea)))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&?z_hlv)|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), zenon_Vrb>> \\in a_voteunde_msghash_primea)))))))<=>(~((zenon_Vrb \\in Node)=>((((?z_hmy=zenon_Vrb)&?z_hlv)|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&?z_hlv)|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), zenon_Vrb>> \\in a_voteunde_msghash_primea)))|?z_hno)))))))" (is "~(?z_hus<=>?z_hut)")
    by (rule zenon_ex_choose_0 [of "?z_hup", OF z_Htt])
    show FALSE
    proof (rule zenon_notequiv [OF z_Huq])
     assume z_Huu:"(~?z_hus)" (is "~~?z_huv")
     assume z_Hut:"?z_hut" (is "~(?z_huw=>?z_hux)")
     have z_Huv: "?z_huv" (is "_=>?z_huy")
     by (rule zenon_notnot_0 [OF z_Huu])
     have z_Huw: "?z_huw"
     by (rule zenon_notimply_0 [OF z_Hut])
     have z_Huz: "(~?z_hux)" (is "~(?z_hva|_)")
     by (rule zenon_notimply_1 [OF z_Hut])
     have z_Hvb: "(~?z_hva)" (is "~(?z_hvc|?z_hvd)")
     by (rule zenon_notor_0 [OF z_Huz])
     have z_Hrs: "(~?z_hno)"
     by (rule zenon_notor_1 [OF z_Huz])
     have z_Hnn: "?z_hnn"
     by (rule zenon_notnot_0 [OF z_Hrs])
     have z_Hve: "(~?z_hvc)" (is "~(?z_hvf&_)")
     by (rule zenon_notor_0 [OF z_Hvb])
     have z_Hvg: "(~?z_hvd)" (is "~~?z_hvh")
     by (rule zenon_notor_1 [OF z_Hvb])
     have z_Hvh: "?z_hvh"
     by (rule zenon_notnot_0 [OF z_Hvg])
     show FALSE
     proof (rule zenon_notand [OF z_Hve])
      assume z_Hvi:"(?z_hmy~=(CHOOSE zenon_Vrb:(~((~((zenon_Vrb \\in Node)=>bAll(Node, (\<lambda>VARK. ((((zenon_Vrb=VARK)&?z_hlv)|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&?z_hlv)|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), VARK>> \\in a_voteunde_msghash_primea)))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&?z_hlv)|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), zenon_Vrb>> \\in a_voteunde_msghash_primea)))))))<=>(~((zenon_Vrb \\in Node)=>((((?z_hmy=zenon_Vrb)&?z_hlv)|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&?z_hlv)|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), zenon_Vrb>> \\in a_voteunde_msghash_primea)))|?z_hno)))))))" (is "_~=?z_hur")
      show FALSE
      proof (rule zenon_imply [OF z_Huv])
       assume z_Hvj:"(~?z_huw)"
       show FALSE
       by (rule notE [OF z_Hvj z_Huw])
      next
       assume z_Huy:"?z_huy"
       have z_Hvk_z_Huy: "(\\A x:((x \\in Node)=>((((?z_hur=x)&?z_hlv)|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&?z_hlv)|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), x>> \\in a_voteunde_msghash_primea)))|?z_hvd))) == ?z_huy" (is "?z_hvk == _")
       by (unfold bAll_def)
       have z_Hvk: "?z_hvk" (is "\\A x : ?z_hvq(x)")
       by (unfold z_Hvk_z_Huy, fact z_Huy)
       have z_Hvr: "?z_hvq(?z_hmy)" (is "_=>?z_hvs")
       by (rule zenon_all_0 [of "?z_hvq" "?z_hmy", OF z_Hvk])
       show FALSE
       proof (rule zenon_imply [OF z_Hvr])
        assume z_Hqb:"(~?z_how)"
        show FALSE
        by (rule notE [OF z_Hqb z_How])
       next
        assume z_Hvs:"?z_hvs" (is "?z_hvt|_")
        show FALSE
        proof (rule zenon_or [OF z_Hvs])
         assume z_Hvt:"?z_hvt" (is "?z_hvu|_")
         show FALSE
         proof (rule zenon_or [OF z_Hvt])
          assume z_Hvu:"?z_hvu" (is "?z_hvv&_")
          have z_Hvv: "?z_hvv"
          by (rule zenon_and_0 [OF z_Hvu])
          show FALSE
          by (rule zenon_eqsym [OF z_Hvv z_Hvi])
         next
          assume z_Hno:"?z_hno"
          show FALSE
          by (rule notE [OF z_Hno z_Hnn])
         qed
        next
         assume z_Hvd:"?z_hvd"
         show FALSE
         by (rule notE [OF z_Hvd z_Hvh])
        qed
       qed
      qed
     next
      assume z_Hvw:"(a_voteshash_primea~=a_voteshash_primea)"
      show FALSE
      by (rule zenon_noteq [OF z_Hvw])
     qed
    next
     assume z_Hus:"?z_hus" (is "~(?z_huw=>?z_huy)")
     assume z_Hvx:"(~?z_hut)" (is "~~?z_hvy")
     have z_Huw: "?z_huw"
     by (rule zenon_notimply_0 [OF z_Hus])
     have z_Hvz: "(~?z_huy)"
     by (rule zenon_notimply_1 [OF z_Hus])
     have z_Hwa_z_Hvz: "(~(\\A x:((x \\in Node)=>(((((CHOOSE zenon_Vrb:(~((~((zenon_Vrb \\in Node)=>bAll(Node, (\<lambda>VARK. ((((zenon_Vrb=VARK)&?z_hlv)|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&?z_hlv)|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), VARK>> \\in a_voteunde_msghash_primea)))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&?z_hlv)|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), zenon_Vrb>> \\in a_voteunde_msghash_primea)))))))<=>(~((zenon_Vrb \\in Node)=>((((?z_hmy=zenon_Vrb)&?z_hlv)|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&?z_hlv)|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), zenon_Vrb>> \\in a_voteunde_msghash_primea)))|?z_hno))))))=x)&?z_hlv)|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&?z_hlv)|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), x>> \\in a_voteunde_msghash_primea)))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&?z_hlv)|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), (CHOOSE zenon_Vrb:(~((~((zenon_Vrb \\in Node)=>bAll(Node, (\<lambda>VARK. ((((zenon_Vrb=VARK)&?z_hlv)|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&?z_hlv)|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), VARK>> \\in a_voteunde_msghash_primea)))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&?z_hlv)|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), zenon_Vrb>> \\in a_voteunde_msghash_primea)))))))<=>(~((zenon_Vrb \\in Node)=>((((?z_hmy=zenon_Vrb)&?z_hlv)|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&?z_hlv)|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), zenon_Vrb>> \\in a_voteunde_msghash_primea)))|?z_hno))))))>> \\in a_voteunde_msghash_primea)))))) == (~?z_huy)" (is "?z_hwa == ?z_hvz")
     by (unfold bAll_def)
     have z_Hwa: "?z_hwa" (is "~(\\A x : ?z_hvq(x))")
     by (unfold z_Hwa_z_Hvz, fact z_Hvz)
     have z_Hwc: "(\\E x:(~((x \\in Node)=>(((((CHOOSE zenon_Vrb:(~((~((zenon_Vrb \\in Node)=>bAll(Node, (\<lambda>VARK. ((((zenon_Vrb=VARK)&?z_hlv)|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&?z_hlv)|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), VARK>> \\in a_voteunde_msghash_primea)))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&?z_hlv)|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), zenon_Vrb>> \\in a_voteunde_msghash_primea)))))))<=>(~((zenon_Vrb \\in Node)=>((((?z_hmy=zenon_Vrb)&?z_hlv)|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&?z_hlv)|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), zenon_Vrb>> \\in a_voteunde_msghash_primea)))|?z_hno))))))=x)&?z_hlv)|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&?z_hlv)|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), x>> \\in a_voteunde_msghash_primea)))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&?z_hlv)|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), (CHOOSE zenon_Vrb:(~((~((zenon_Vrb \\in Node)=>bAll(Node, (\<lambda>VARK. ((((zenon_Vrb=VARK)&?z_hlv)|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&?z_hlv)|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), VARK>> \\in a_voteunde_msghash_primea)))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&?z_hlv)|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), zenon_Vrb>> \\in a_voteunde_msghash_primea)))))))<=>(~((zenon_Vrb \\in Node)=>((((?z_hmy=zenon_Vrb)&?z_hlv)|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&?z_hlv)|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), zenon_Vrb>> \\in a_voteunde_msghash_primea)))|?z_hno))))))>> \\in a_voteunde_msghash_primea))))))" (is "\\E x : ?z_hwe(x)")
     by (rule zenon_notallex_0 [of "?z_hvq", OF z_Hwa])
     have z_Hwf: "?z_hwe((CHOOSE x:(~((x \\in Node)=>(((((CHOOSE zenon_Vrb:(~((~((zenon_Vrb \\in Node)=>bAll(Node, (\<lambda>VARK. ((((zenon_Vrb=VARK)&?z_hlv)|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&?z_hlv)|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), VARK>> \\in a_voteunde_msghash_primea)))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&?z_hlv)|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), zenon_Vrb>> \\in a_voteunde_msghash_primea)))))))<=>(~((zenon_Vrb \\in Node)=>((((?z_hmy=zenon_Vrb)&?z_hlv)|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&?z_hlv)|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), zenon_Vrb>> \\in a_voteunde_msghash_primea)))|?z_hno))))))=x)&?z_hlv)|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&?z_hlv)|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), x>> \\in a_voteunde_msghash_primea)))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&?z_hlv)|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), (CHOOSE zenon_Vrb:(~((~((zenon_Vrb \\in Node)=>bAll(Node, (\<lambda>VARK. ((((zenon_Vrb=VARK)&?z_hlv)|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&?z_hlv)|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), VARK>> \\in a_voteunde_msghash_primea)))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&?z_hlv)|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), zenon_Vrb>> \\in a_voteunde_msghash_primea)))))))<=>(~((zenon_Vrb \\in Node)=>((((?z_hmy=zenon_Vrb)&?z_hlv)|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&?z_hlv)|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), zenon_Vrb>> \\in a_voteunde_msghash_primea)))|?z_hno))))))>> \\in a_voteunde_msghash_primea)))))))" (is "~(?z_hwh=>?z_hwi)")
     by (rule zenon_ex_choose_0 [of "?z_hwe", OF z_Hwc])
     have z_Hwh: "?z_hwh"
     by (rule zenon_notimply_0 [OF z_Hwf])
     have z_Hwj: "(~?z_hwi)" (is "~(?z_hwk|?z_hvd)")
     by (rule zenon_notimply_1 [OF z_Hwf])
     have z_Hwl: "(~?z_hwk)" (is "~(?z_hwm|?z_hwn)")
     by (rule zenon_notor_0 [OF z_Hwj])
     have z_Hvg: "(~?z_hvd)" (is "~~?z_hvh")
     by (rule zenon_notor_1 [OF z_Hwj])
     have z_Hvh: "?z_hvh"
     by (rule zenon_notnot_0 [OF z_Hvg])
     have z_Hwo: "(~?z_hwm)" (is "~(?z_hwp&_)")
     by (rule zenon_notor_0 [OF z_Hwl])
     have z_Hwq: "(~?z_hwn)" (is "~~?z_hwr")
     by (rule zenon_notor_1 [OF z_Hwl])
     have z_Hwr: "?z_hwr"
     by (rule zenon_notnot_0 [OF z_Hwq])
     show FALSE
     proof (rule zenon_notand [OF z_Hwo])
      assume z_Hws:"((CHOOSE zenon_Vrb:(~((~((zenon_Vrb \\in Node)=>bAll(Node, (\<lambda>VARK. ((((zenon_Vrb=VARK)&?z_hlv)|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&?z_hlv)|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), VARK>> \\in a_voteunde_msghash_primea)))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&?z_hlv)|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), zenon_Vrb>> \\in a_voteunde_msghash_primea)))))))<=>(~((zenon_Vrb \\in Node)=>((((?z_hmy=zenon_Vrb)&?z_hlv)|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&?z_hlv)|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), zenon_Vrb>> \\in a_voteunde_msghash_primea)))|?z_hno))))))~=(CHOOSE x:(~((x \\in Node)=>(((((CHOOSE zenon_Vrb:(~((~((zenon_Vrb \\in Node)=>bAll(Node, (\<lambda>VARK. ((((zenon_Vrb=VARK)&?z_hlv)|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&?z_hlv)|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), VARK>> \\in a_voteunde_msghash_primea)))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&?z_hlv)|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), zenon_Vrb>> \\in a_voteunde_msghash_primea)))))))<=>(~((zenon_Vrb \\in Node)=>((((?z_hmy=zenon_Vrb)&?z_hlv)|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&?z_hlv)|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), zenon_Vrb>> \\in a_voteunde_msghash_primea)))|?z_hno))))))=x)&?z_hlv)|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&?z_hlv)|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), x>> \\in a_voteunde_msghash_primea)))|?z_hvd)))))" (is "?z_hur~=?z_hwg")
      have z_Hwt: "(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&?z_hlv)|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), ?z_hwg>> \\in ?z_htd)" (is "?z_hwt")
      by (rule subst [where P="(\<lambda>zenon_Vvea. (<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&?z_hlv)|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), ?z_hwg>> \\in zenon_Vvea))", OF z_Htc z_Hwr])
      show FALSE
      proof (rule zenon_in_cup [of "<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&?z_hlv)|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), ?z_hwg>>" "a_voteunde_msga" "{<<(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))), (CHOOSE x:((x \\in Node)&(?z_hmd&((<<x, (CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<x, (CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))), x>>}))&?z_hsp))))))>>}", OF z_Hwt])
       assume z_Hxa:"(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&?z_hlv)|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), ?z_hwg>> \\in a_voteunde_msga)" (is "?z_hxa")
       have z_Hxb: "(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&?z_hlv)|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), ?z_hur>> \\in ?z_htd)" (is "?z_hxb")
       by (rule subst [where P="(\<lambda>zenon_Vtea. (<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&?z_hlv)|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), ?z_hur>> \\in zenon_Vtea))", OF z_Htc z_Hvh])
       show FALSE
       proof (rule zenon_in_cup [of "<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&?z_hlv)|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), ?z_hur>>" "a_voteunde_msga" "{<<(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))), (CHOOSE x:((x \\in Node)&(?z_hmd&((<<x, (CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<x, (CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))), x>>}))&?z_hsp))))))>>}", OF z_Hxb])
        assume z_Hxf:"(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&?z_hlv)|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), ?z_hur>> \\in a_voteunde_msga)" (is "?z_hxf")
        have z_Hxg: "?z_hpo(?z_hwg)" (is "_=>?z_hxh")
        by (rule zenon_all_0 [of "?z_hpo" "?z_hwg", OF z_Hpd])
        show FALSE
        proof (rule zenon_imply [OF z_Hxg])
         assume z_Hxi:"(~?z_hwh)"
         show FALSE
         by (rule notE [OF z_Hxi z_Hwh])
        next
         assume z_Hxh:"?z_hxh"
         have z_Hxj_z_Hxh: "(\\A x:((x \\in Node)=>((((?z_hwg=x)&(votes=votes))|(~(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&?z_hlv)|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), x>> \\in a_voteunde_msga)))|(~?z_hxa)))) == ?z_hxh" (is "?z_hxj == _")
         by (unfold bAll_def)
         have z_Hxj: "?z_hxj" (is "\\A x : ?z_hxq(x)")
         by (unfold z_Hxj_z_Hxh, fact z_Hxh)
         have z_Hxr: "?z_hxq(?z_hur)" (is "_=>?z_hxs")
         by (rule zenon_all_0 [of "?z_hxq" "?z_hur", OF z_Hxj])
         show FALSE
         proof (rule zenon_imply [OF z_Hxr])
          assume z_Hvj:"(~?z_huw)"
          show FALSE
          by (rule notE [OF z_Hvj z_Huw])
         next
          assume z_Hxs:"?z_hxs" (is "?z_hxt|?z_hxp")
          show FALSE
          proof (rule zenon_or [OF z_Hxs])
           assume z_Hxt:"?z_hxt" (is "?z_hxu|?z_hxv")
           show FALSE
           proof (rule zenon_or [OF z_Hxt])
            assume z_Hxu:"?z_hxu" (is "?z_hxw&?z_hem")
            have z_Hxw: "?z_hxw"
            by (rule zenon_and_0 [OF z_Hxu])
            show FALSE
            by (rule zenon_eqsym [OF z_Hxw z_Hws])
           next
            assume z_Hxv:"?z_hxv"
            show FALSE
            by (rule notE [OF z_Hxv z_Hxf])
           qed
          next
           assume z_Hxp:"?z_hxp"
           show FALSE
           by (rule notE [OF z_Hxp z_Hxa])
          qed
         qed
        qed
       next
        assume z_Hxx:"(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&?z_hlv)|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), ?z_hur>> \\in {<<(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))), (CHOOSE x:((x \\in Node)&(?z_hmd&((<<x, (CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<x, (CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))), x>>}))&?z_hsp))))))>>})" (is "?z_hxx")
        show FALSE
        proof (rule zenon_in_addElt [of "<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&?z_hlv)|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), ?z_hur>>" "<<(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))), (CHOOSE x:((x \\in Node)&(?z_hmd&((<<x, (CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<x, (CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))), x>>}))&?z_hsp))))))>>" "{}", OF z_Hxx])
         assume z_Hxy:"(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&?z_hlv)|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), ?z_hur>>=<<(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))), (CHOOSE x:((x \\in Node)&(?z_hmd&((<<x, (CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<x, (CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))), x>>}))&?z_hsp))))))>>)" (is "?z_hwb=?z_hwz")
         have z_Hlk: "((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&?z_hlv)|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea))))))))))=(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))))" (is "?z_hll=?z_hkm")
         using z_Hxy by auto
         have z_Hxz: "?z_hts(?z_hwg)" (is "_=>?z_hya")
         by (rule zenon_all_0 [of "?z_hts" "?z_hwg", OF z_Htp])
         show FALSE
         proof (rule zenon_imply [OF z_Hxz])
          assume z_Hxi:"(~?z_hwh)"
          show FALSE
          by (rule notE [OF z_Hxi z_Hwh])
         next
          assume z_Hya:"?z_hya" (is "?z_hmc|?z_hxp")
          show FALSE
          proof (rule zenon_or [OF z_Hya])
           assume z_Hmc:"?z_hmc"
           show FALSE
           by (rule zenon_L1_ [OF z_Hkf z_Hkl z_Hlk z_Hmc z_Hmd])
          next
           assume z_Hxp:"?z_hxp"
           show FALSE
           by (rule notE [OF z_Hxp z_Hxa])
          qed
         qed
        next
         assume z_Hyb:"(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&?z_hlv)|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), ?z_hur>> \\in {})" (is "?z_hyb")
         show FALSE
         by (rule zenon_in_emptyset [of "<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&?z_hlv)|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), ?z_hur>>", OF z_Hyb])
        qed
       qed
      next
       assume z_Hyc:"(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&?z_hlv)|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), ?z_hwg>> \\in {<<(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))), (CHOOSE x:((x \\in Node)&(?z_hmd&((<<x, (CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<x, (CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))), x>>}))&?z_hsp))))))>>})" (is "?z_hyc")
       show FALSE
       proof (rule zenon_in_addElt [of "<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&?z_hlv)|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), ?z_hwg>>" "<<(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))), (CHOOSE x:((x \\in Node)&(?z_hmd&((<<x, (CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<x, (CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))), x>>}))&?z_hsp))))))>>" "{}", OF z_Hyc])
        assume z_Hyd:"(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&?z_hlv)|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), ?z_hwg>>=<<(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))), (CHOOSE x:((x \\in Node)&(?z_hmd&((<<x, (CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<x, (CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))), x>>}))&?z_hsp))))))>>)" (is "?z_hwu=?z_hwz")
        have z_Hlk: "((CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&?z_hlv)|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea))))))))))=(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(voted[x]))&((<<j, x>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<x, j>>}))&((a_votedhash_primea=except(voted, x, TRUE))&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))))" (is "?z_hll=?z_hkm")
        using z_Hyd by auto
        have z_Hye: "(?z_hwg=(CHOOSE x:((x \\in Node)&(?z_hmd&((<<x, ?z_hkm>> \\in a_voteunde_requestunde_msga)&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<x, ?z_hkm>>}))&((a_voteunde_msghash_primea=(a_voteunde_msga \\cup {<<?z_hkm, x>>}))&?z_hsp)))))))" (is "_=?z_hsu")
        using z_Hyd by auto
        have z_Hxb: "(<<?z_hll, ?z_hur>> \\in ?z_htd)" (is "?z_hxb")
        by (rule subst [where P="(\<lambda>zenon_Vtea. (<<?z_hll, ?z_hur>> \\in zenon_Vtea))", OF z_Htc z_Hvh])
        show FALSE
        proof (rule zenon_in_cup [of "<<?z_hll, ?z_hur>>" "a_voteunde_msga" "{?z_hwz}", OF z_Hxb])
         assume z_Hxf:"(<<?z_hll, ?z_hur>> \\in a_voteunde_msga)" (is "?z_hxf")
         have z_Hyf: "?z_hts(?z_hur)" (is "_=>?z_hyg")
         by (rule zenon_all_0 [of "?z_hts" "?z_hur", OF z_Htp])
         show FALSE
         proof (rule zenon_imply [OF z_Hyf])
          assume z_Hvj:"(~?z_huw)"
          show FALSE
          by (rule notE [OF z_Hvj z_Huw])
         next
          assume z_Hyg:"?z_hyg" (is "?z_hmc|?z_hxv")
          show FALSE
          proof (rule zenon_or [OF z_Hyg])
           assume z_Hmc:"?z_hmc"
           show FALSE
           by (rule zenon_L1_ [OF z_Hkf z_Hkl z_Hlk z_Hmc z_Hmd])
          next
           assume z_Hxv:"?z_hxv"
           show FALSE
           by (rule notE [OF z_Hxv z_Hxf])
          qed
         qed
        next
         assume z_Hxx:"(<<?z_hll, ?z_hur>> \\in {?z_hwz})" (is "?z_hxx")
         show FALSE
         proof (rule zenon_in_addElt [of "<<?z_hll, ?z_hur>>" "?z_hwz" "{}", OF z_Hxx])
          assume z_Hxy:"(<<?z_hll, ?z_hur>>=?z_hwz)" (is "?z_hwb=_")
          have z_Hyh: "(?z_hur=?z_hsu)"
          using z_Hxy by auto
          show FALSE
          proof (rule zenon_em [of "(?z_hwg=?z_hwg)"])
           assume z_Hyi:"(?z_hwg=?z_hwg)"
           show FALSE
           proof (rule notE [OF z_Hws])
            have z_Hxw: "(?z_hwg=?z_hur)"
            proof (rule zenon_nnpp [of "(?z_hwg=?z_hur)"])
             assume z_Hyj:"(?z_hwg~=?z_hur)"
             show FALSE
             proof (rule notE [OF z_Hyj])
              have z_Hyk: "(?z_hsu=?z_hur)"
              by (rule sym [OF z_Hyh])
              have z_Hxw: "(?z_hwg=?z_hur)"
              by (rule subst [where P="(\<lambda>zenon_Vhjb. (?z_hwg=zenon_Vhjb))", OF z_Hyk], fact z_Hye)
              thus "(?z_hwg=?z_hur)" .
             qed
            qed
            have z_Hwp: "?z_hwp"
            by (rule subst [where P="(\<lambda>zenon_Vijb. (zenon_Vijb=?z_hwg))", OF z_Hxw], fact z_Hyi)
            thus "?z_hwp" .
           qed
          next
           assume z_Hyr:"(?z_hwg~=?z_hwg)"
           show FALSE
           by (rule zenon_noteq [OF z_Hyr])
          qed
         next
          assume z_Hyb:"(<<?z_hll, ?z_hur>> \\in {})" (is "?z_hyb")
          show FALSE
          by (rule zenon_in_emptyset [of "<<?z_hll, ?z_hur>>", OF z_Hyb])
         qed
        qed
       next
        assume z_Hys:"(<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&?z_hlv)|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), ?z_hwg>> \\in {})" (is "?z_hys")
        show FALSE
        by (rule zenon_in_emptyset [of "<<(CHOOSE x:(~((x \\in Node)=>bAll(Node, (\<lambda>VARJ. bAll(Node, (\<lambda>VARK. ((((VARJ=VARK)&?z_hlv)|(~(<<x, VARK>> \\in a_voteunde_msghash_primea)))|(~(<<x, VARJ>> \\in a_voteunde_msghash_primea)))))))))), ?z_hwg>>", OF z_Hys])
       qed
      qed
     next
      assume z_Hvw:"(a_voteshash_primea~=a_voteshash_primea)"
      show FALSE
      by (rule zenon_noteq [OF z_Hvw])
     qed
    qed
   next
    assume z_Hgt:"?z_hgt" (is "?z_hgu|?z_hhe")
    show FALSE
    proof (rule zenon_or [OF z_Hgt])
     assume z_Hgu:"?z_hgu"
     have z_Hyt_z_Hgu: "(\\E x:((x \\in Node)&bEx(Node, (\<lambda>j. ((voted[x])&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_votedhash_primea=voted)&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))) == ?z_hgu" (is "?z_hyt == _")
     by (unfold bEx_def)
     have z_Hyt: "?z_hyt" (is "\\E x : ?z_hyz(x)")
     by (unfold z_Hyt_z_Hgu, fact z_Hgu)
     have z_Hza: "?z_hyz((CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((voted[x])&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_votedhash_primea=voted)&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))" (is "?z_hzc&?z_hzd")
     by (rule zenon_ex_choose_0 [of "?z_hyz", OF z_Hyt])
     have z_Hzd: "?z_hzd"
     by (rule zenon_and_1 [OF z_Hza])
     have z_Hze_z_Hzd: "(\\E x:((x \\in Node)&((voted[(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((voted[x])&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_votedhash_primea=voted)&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))])&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<x, (CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((voted[x])&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_votedhash_primea=voted)&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))>>}))&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_votedhash_primea=voted)&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))) == ?z_hzd" (is "?z_hze == _")
     by (unfold bEx_def)
     have z_Hze: "?z_hze" (is "\\E x : ?z_hzn(x)")
     by (unfold z_Hze_z_Hzd, fact z_Hzd)
     have z_Hzo: "?z_hzn((CHOOSE x:((x \\in Node)&((voted[(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((voted[x])&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_votedhash_primea=voted)&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))])&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<x, (CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((voted[x])&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\ {<<j, x>>}))&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_votedhash_primea=voted)&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))>>}))&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_votedhash_primea=voted)&((a_voteshash_primea=votes)&((a_decidedhash_primea=decided)&((a_leaderhash_primea=leader)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))" (is "?z_hzq&?z_hzr")
     by (rule zenon_ex_choose_0 [of "?z_hzn", OF z_Hze])
     have z_Hzr: "?z_hzr" (is "?z_hzh&?z_hzs")
     by (rule zenon_and_1 [OF z_Hzo])
     have z_Hzs: "?z_hzs" (is "?z_hzt&?z_hha")
     by (rule zenon_and_1 [OF z_Hzr])
     have z_Hha: "?z_hha" (is "?z_hhb&?z_hhc")
     by (rule zenon_and_1 [OF z_Hzs])
     have z_Hhb: "?z_hhb"
     by (rule zenon_and_0 [OF z_Hha])
     show FALSE
     by (rule zenon_L4_ [OF z_Hoj z_Hov z_How z_Hox z_Hhb z_Hnn z_Hod z_Hoy])
    next
     assume z_Hhe:"?z_hhe" (is "?z_hhf|?z_hhx")
     show FALSE
     proof (rule zenon_or [OF z_Hhe])
      assume z_Hhf:"?z_hhf"
      have z_Hzu_z_Hhf: "(\\E x:((x \\in Node)&bEx(Node, (\<lambda>j. ((<<j, x>> \\in a_voteunde_msga)&((a_voteshash_primea=except(votes, x, ((votes[x]) \\cup {j})))&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_decidedhash_primea=decided)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))) == ?z_hhf" (is "?z_hzu == _")
      by (unfold bEx_def)
      have z_Hzu: "?z_hzu" (is "\\E x : ?z_hbaf(x)")
      by (unfold z_Hzu_z_Hhf, fact z_Hhf)
      have z_Hbag: "?z_hbaf((CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((<<j, x>> \\in a_voteunde_msga)&((a_voteshash_primea=except(votes, x, ((votes[x]) \\cup {j})))&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_decidedhash_primea=decided)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))" (is "?z_hbai&?z_hbaj")
      by (rule zenon_ex_choose_0 [of "?z_hbaf", OF z_Hzu])
      have z_Hbaj: "?z_hbaj"
      by (rule zenon_and_1 [OF z_Hbag])
      have z_Hbak_z_Hbaj: "(\\E x:((x \\in Node)&((<<x, (CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((<<j, x>> \\in a_voteunde_msga)&((a_voteshash_primea=except(votes, x, ((votes[x]) \\cup {j})))&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_decidedhash_primea=decided)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))>> \\in a_voteunde_msga)&((a_voteshash_primea=except(votes, (CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((<<j, x>> \\in a_voteunde_msga)&((a_voteshash_primea=except(votes, x, ((votes[x]) \\cup {j})))&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_decidedhash_primea=decided)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))), ((votes[(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((<<j, x>> \\in a_voteunde_msga)&((a_voteshash_primea=except(votes, x, ((votes[x]) \\cup {j})))&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_decidedhash_primea=decided)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))]) \\cup {x})))&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_decidedhash_primea=decided)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))) == ?z_hbaj" (is "?z_hbak == _")
      by (unfold bEx_def)
      have z_Hbak: "?z_hbak" (is "\\E x : ?z_hbav(x)")
      by (unfold z_Hbak_z_Hbaj, fact z_Hbaj)
      have z_Hbaw: "?z_hbav((CHOOSE x:((x \\in Node)&((<<x, (CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((<<j, x>> \\in a_voteunde_msga)&((a_voteshash_primea=except(votes, x, ((votes[x]) \\cup {j})))&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_decidedhash_primea=decided)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))>> \\in a_voteunde_msga)&((a_voteshash_primea=except(votes, (CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((<<j, x>> \\in a_voteunde_msga)&((a_voteshash_primea=except(votes, x, ((votes[x]) \\cup {j})))&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_decidedhash_primea=decided)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))), ((votes[(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((<<j, x>> \\in a_voteunde_msga)&((a_voteshash_primea=except(votes, x, ((votes[x]) \\cup {j})))&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_decidedhash_primea=decided)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))]) \\cup {x})))&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_decidedhash_primea=decided)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))" (is "?z_hbay&?z_hbaz")
      by (rule zenon_ex_choose_0 [of "?z_hbav", OF z_Hbak])
      have z_Hbaz: "?z_hbaz" (is "?z_hbba&?z_hbbb")
      by (rule zenon_and_1 [OF z_Hbaw])
      have z_Hbbb: "?z_hbbb" (is "?z_hbbc&?z_hhr")
      by (rule zenon_and_1 [OF z_Hbaz])
      have z_Hhr: "?z_hhr" (is "?z_hhd&?z_hhs")
      by (rule zenon_and_1 [OF z_Hbbb])
      have z_Hhs: "?z_hhs" (is "?z_hhb&?z_hht")
      by (rule zenon_and_1 [OF z_Hhr])
      have z_Hhb: "?z_hhb"
      by (rule zenon_and_0 [OF z_Hhs])
      show FALSE
      by (rule zenon_L4_ [OF z_Hoj z_Hov z_How z_Hox z_Hhb z_Hnn z_Hod z_Hoy])
     next
      assume z_Hhx:"?z_hhx" (is "?z_hhy|?z_hil")
      show FALSE
      proof (rule zenon_or [OF z_Hhx])
       assume z_Hhy:"?z_hhy"
       have z_Hbbd_z_Hhy: "(\\E x:((x \\in Node)&bEx(Quorum, (\<lambda>Q. ((Q \\subseteq (votes[x]))&((a_leaderhash_primea=except(leader, x, TRUE))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_decidedhash_primea=decided)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))) == ?z_hhy" (is "?z_hbbd == _")
       by (unfold bEx_def)
       have z_Hbbd: "?z_hbbd" (is "\\E x : ?z_hbbm(x)")
       by (unfold z_Hbbd_z_Hhy, fact z_Hhy)
       have z_Hbbn: "?z_hbbm((CHOOSE x:((x \\in Node)&bEx(Quorum, (\<lambda>Q. ((Q \\subseteq (votes[x]))&((a_leaderhash_primea=except(leader, x, TRUE))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_decidedhash_primea=decided)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))" (is "?z_hbbp&?z_hbbq")
       by (rule zenon_ex_choose_0 [of "?z_hbbm", OF z_Hbbd])
       have z_Hbbq: "?z_hbbq"
       by (rule zenon_and_1 [OF z_Hbbn])
       have z_Hbbr_z_Hbbq: "(\\E x:((x \\in Quorum)&((x \\subseteq (votes[(CHOOSE x:((x \\in Node)&bEx(Quorum, (\<lambda>Q. ((Q \\subseteq (votes[x]))&((a_leaderhash_primea=except(leader, x, TRUE))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_decidedhash_primea=decided)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))]))&((a_leaderhash_primea=except(leader, (CHOOSE x:((x \\in Node)&bEx(Quorum, (\<lambda>Q. ((Q \\subseteq (votes[x]))&((a_leaderhash_primea=except(leader, x, TRUE))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_decidedhash_primea=decided)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))), TRUE))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_decidedhash_primea=decided)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))) == ?z_hbbq" (is "?z_hbbr == _")
       by (unfold bEx_def)
       have z_Hbbr: "?z_hbbr" (is "\\E x : ?z_hbca(x)")
       by (unfold z_Hbbr_z_Hbbq, fact z_Hbbq)
       have z_Hbcb: "?z_hbca((CHOOSE x:((x \\in Quorum)&((x \\subseteq (votes[(CHOOSE x:((x \\in Node)&bEx(Quorum, (\<lambda>Q. ((Q \\subseteq (votes[x]))&((a_leaderhash_primea=except(leader, x, TRUE))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_decidedhash_primea=decided)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))]))&((a_leaderhash_primea=except(leader, (CHOOSE x:((x \\in Node)&bEx(Quorum, (\<lambda>Q. ((Q \\subseteq (votes[x]))&((a_leaderhash_primea=except(leader, x, TRUE))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_decidedhash_primea=decided)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))), TRUE))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_decidedhash_primea=decided)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))" (is "?z_hbcd&?z_hbce")
       by (rule zenon_ex_choose_0 [of "?z_hbca", OF z_Hbbr])
       have z_Hbce: "?z_hbce" (is "?z_hbcf&?z_hbbx")
       by (rule zenon_and_1 [OF z_Hbcb])
       have z_Hbbx: "?z_hbbx" (is "?z_hbby&?z_hii")
       by (rule zenon_and_1 [OF z_Hbce])
       have z_Hii: "?z_hii" (is "?z_hgi&?z_hij")
       by (rule zenon_and_1 [OF z_Hbbx])
       have z_Hij: "?z_hij" (is "?z_hhd&?z_hik")
       by (rule zenon_and_1 [OF z_Hii])
       have z_Hik: "?z_hik" (is "?z_hhb&?z_hhu")
       by (rule zenon_and_1 [OF z_Hij])
       have z_Hhb: "?z_hhb"
       by (rule zenon_and_0 [OF z_Hik])
       show FALSE
       by (rule zenon_L4_ [OF z_Hoj z_Hov z_How z_Hox z_Hhb z_Hnn z_Hod z_Hoy])
      next
       assume z_Hil:"?z_hil"
       have z_Hbcg_z_Hil: "(\\E x:((x \\in Node)&bEx(Node, (\<lambda>j. bEx(Value, (\<lambda>v. ((leader[x])&(({}=(decided[x]))&((a_decidedhash_primea=except(decided, x, ((decided[x]) \\cup {v})))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))))) == ?z_hil" (is "?z_hbcg == _")
       by (unfold bEx_def)
       have z_Hbcg: "?z_hbcg" (is "\\E x : ?z_hbcv(x)")
       by (unfold z_Hbcg_z_Hil, fact z_Hil)
       have z_Hbcw: "?z_hbcv((CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. bEx(Value, (\<lambda>v. ((leader[x])&(({}=(decided[x]))&((a_decidedhash_primea=except(decided, x, ((decided[x]) \\cup {v})))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))))))" (is "?z_hbcy&?z_hbcz")
       by (rule zenon_ex_choose_0 [of "?z_hbcv", OF z_Hbcg])
       have z_Hbcz: "?z_hbcz"
       by (rule zenon_and_1 [OF z_Hbcw])
       have z_Hbda_z_Hbcz: "(\\E x:((x \\in Node)&bEx(Value, (\<lambda>v. ((leader[(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. bEx(Value, (\<lambda>v. ((leader[x])&(({}=(decided[x]))&((a_decidedhash_primea=except(decided, x, ((decided[x]) \\cup {v})))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))))])&(({}=(decided[(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. bEx(Value, (\<lambda>v. ((leader[x])&(({}=(decided[x]))&((a_decidedhash_primea=except(decided, x, ((decided[x]) \\cup {v})))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))))]))&((a_decidedhash_primea=except(decided, (CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. bEx(Value, (\<lambda>v. ((leader[x])&(({}=(decided[x]))&((a_decidedhash_primea=except(decided, x, ((decided[x]) \\cup {v})))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))))), ((decided[(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. bEx(Value, (\<lambda>v. ((leader[x])&(({}=(decided[x]))&((a_decidedhash_primea=except(decided, x, ((decided[x]) \\cup {v})))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))))]) \\cup {v})))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))) == ?z_hbcz" (is "?z_hbda == _")
       by (unfold bEx_def)
       have z_Hbda: "?z_hbda" (is "\\E x : ?z_hbdn(x)")
       by (unfold z_Hbda_z_Hbcz, fact z_Hbcz)
       have z_Hbdo: "?z_hbdn((CHOOSE x:((x \\in Node)&bEx(Value, (\<lambda>v. ((leader[(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. bEx(Value, (\<lambda>v. ((leader[x])&(({}=(decided[x]))&((a_decidedhash_primea=except(decided, x, ((decided[x]) \\cup {v})))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))))])&(({}=(decided[(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. bEx(Value, (\<lambda>v. ((leader[x])&(({}=(decided[x]))&((a_decidedhash_primea=except(decided, x, ((decided[x]) \\cup {v})))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))))]))&((a_decidedhash_primea=except(decided, (CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. bEx(Value, (\<lambda>v. ((leader[x])&(({}=(decided[x]))&((a_decidedhash_primea=except(decided, x, ((decided[x]) \\cup {v})))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))))), ((decided[(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. bEx(Value, (\<lambda>v. ((leader[x])&(({}=(decided[x]))&((a_decidedhash_primea=except(decided, x, ((decided[x]) \\cup {v})))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))))]) \\cup {v})))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))))" (is "?z_hbdq&?z_hbdc")
       by (rule zenon_ex_choose_0 [of "?z_hbdn", OF z_Hbda])
       have z_Hbdc: "?z_hbdc"
       by (rule zenon_and_1 [OF z_Hbdo])
       have z_Hbdr_z_Hbdc: "(\\E x:((x \\in Value)&((leader[(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. bEx(Value, (\<lambda>v. ((leader[x])&(({}=(decided[x]))&((a_decidedhash_primea=except(decided, x, ((decided[x]) \\cup {v})))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))))])&(({}=(decided[(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. bEx(Value, (\<lambda>v. ((leader[x])&(({}=(decided[x]))&((a_decidedhash_primea=except(decided, x, ((decided[x]) \\cup {v})))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))))]))&((a_decidedhash_primea=except(decided, (CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. bEx(Value, (\<lambda>v. ((leader[x])&(({}=(decided[x]))&((a_decidedhash_primea=except(decided, x, ((decided[x]) \\cup {v})))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))))), ((decided[(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. bEx(Value, (\<lambda>v. ((leader[x])&(({}=(decided[x]))&((a_decidedhash_primea=except(decided, x, ((decided[x]) \\cup {v})))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))))]) \\cup {x})))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))) == ?z_hbdc" (is "?z_hbdr == _")
       by (unfold bEx_def)
       have z_Hbdr: "?z_hbdr" (is "\\E x : ?z_hbea(x)")
       by (unfold z_Hbdr_z_Hbdc, fact z_Hbdc)
       have z_Hbeb: "?z_hbea((CHOOSE x:((x \\in Value)&((leader[(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. bEx(Value, (\<lambda>v. ((leader[x])&(({}=(decided[x]))&((a_decidedhash_primea=except(decided, x, ((decided[x]) \\cup {v})))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))))])&(({}=(decided[(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. bEx(Value, (\<lambda>v. ((leader[x])&(({}=(decided[x]))&((a_decidedhash_primea=except(decided, x, ((decided[x]) \\cup {v})))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))))]))&((a_decidedhash_primea=except(decided, (CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. bEx(Value, (\<lambda>v. ((leader[x])&(({}=(decided[x]))&((a_decidedhash_primea=except(decided, x, ((decided[x]) \\cup {v})))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))))), ((decided[(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. bEx(Value, (\<lambda>v. ((leader[x])&(({}=(decided[x]))&((a_decidedhash_primea=except(decided, x, ((decided[x]) \\cup {v})))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya)))))))))))))))]) \\cup {x})))&((a_voteshash_primea=votes)&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_leaderhash_primea=leader)&((a_voteunde_requestunde_msghash_primea=a_voteunde_requestunde_msga)&(a_requnde_historyhash_primea=a_requnde_historya))))))))))))" (is "?z_hbed&?z_hbee")
       by (rule zenon_ex_choose_0 [of "?z_hbea", OF z_Hbdr])
       have z_Hbee: "?z_hbee" (is "?z_hbdf&?z_hbef")
       by (rule zenon_and_1 [OF z_Hbeb])
       have z_Hbef: "?z_hbef" (is "?z_hbdh&?z_hbeg")
       by (rule zenon_and_1 [OF z_Hbee])
       have z_Hbeg: "?z_hbeg" (is "?z_hbeh&?z_hjd")
       by (rule zenon_and_1 [OF z_Hbef])
       have z_Hjd: "?z_hjd" (is "?z_hgi&?z_hje")
       by (rule zenon_and_1 [OF z_Hbeg])
       have z_Hje: "?z_hje" (is "?z_hhd&?z_hjf")
       by (rule zenon_and_1 [OF z_Hjd])
       have z_Hjf: "?z_hjf" (is "?z_hhb&?z_hjg")
       by (rule zenon_and_1 [OF z_Hje])
       have z_Hhb: "?z_hhb"
       by (rule zenon_and_0 [OF z_Hjf])
       show FALSE
       by (rule zenon_L4_ [OF z_Hoj z_Hov z_How z_Hox z_Hhb z_Hnn z_Hod z_Hoy])
      qed
     qed
    qed
   qed
  next
   assume z_Hjh:"?z_hjh"
   have z_Hbei_z_Hjh: "(\\E x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(<<x, j>> \\in a_requnde_historya))&(bAll(Node, (\<lambda>a_dst2a. (~(<<x, a_dst2a>> \\in a_voteunde_requestunde_msga))))&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\cup {<<x, j>>}))&((a_requnde_historyhash_primea=(a_requnde_historya \\cup {<<x, j>>}))&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_voteshash_primea=votes)&((a_leaderhash_primea=leader)&(a_decidedhash_primea=decided))))))))))))) == ?z_hjh" (is "?z_hbei == _")
   by (unfold bEx_def)
   have z_Hbei: "?z_hbei" (is "\\E x : ?z_hbfb(x)")
   by (unfold z_Hbei_z_Hjh, fact z_Hjh)
   have z_Hbfc: "?z_hbfb((CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(<<x, j>> \\in a_requnde_historya))&(bAll(Node, (\<lambda>a_dst2a. (~(<<x, a_dst2a>> \\in a_voteunde_requestunde_msga))))&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\cup {<<x, j>>}))&((a_requnde_historyhash_primea=(a_requnde_historya \\cup {<<x, j>>}))&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_voteshash_primea=votes)&((a_leaderhash_primea=leader)&(a_decidedhash_primea=decided))))))))))))))" (is "?z_hbfe&?z_hbff")
   by (rule zenon_ex_choose_0 [of "?z_hbfb", OF z_Hbei])
   have z_Hbff: "?z_hbff"
   by (rule zenon_and_1 [OF z_Hbfc])
   have z_Hbfg_z_Hbff: "(\\E x:((x \\in Node)&((~(<<(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(<<x, j>> \\in a_requnde_historya))&(bAll(Node, (\<lambda>a_dst2a. (~(<<x, a_dst2a>> \\in a_voteunde_requestunde_msga))))&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\cup {<<x, j>>}))&((a_requnde_historyhash_primea=(a_requnde_historya \\cup {<<x, j>>}))&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_voteshash_primea=votes)&((a_leaderhash_primea=leader)&(a_decidedhash_primea=decided))))))))))))), x>> \\in a_requnde_historya))&(bAll(Node, (\<lambda>a_dst2a. (~(<<(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(<<x, j>> \\in a_requnde_historya))&(bAll(Node, (\<lambda>a_dst2a. (~(<<x, a_dst2a>> \\in a_voteunde_requestunde_msga))))&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\cup {<<x, j>>}))&((a_requnde_historyhash_primea=(a_requnde_historya \\cup {<<x, j>>}))&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_voteshash_primea=votes)&((a_leaderhash_primea=leader)&(a_decidedhash_primea=decided))))))))))))), a_dst2a>> \\in a_voteunde_requestunde_msga))))&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\cup {<<(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(<<x, j>> \\in a_requnde_historya))&(bAll(Node, (\<lambda>a_dst2a. (~(<<x, a_dst2a>> \\in a_voteunde_requestunde_msga))))&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\cup {<<x, j>>}))&((a_requnde_historyhash_primea=(a_requnde_historya \\cup {<<x, j>>}))&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_voteshash_primea=votes)&((a_leaderhash_primea=leader)&(a_decidedhash_primea=decided))))))))))))), x>>}))&((a_requnde_historyhash_primea=(a_requnde_historya \\cup {<<(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(<<x, j>> \\in a_requnde_historya))&(bAll(Node, (\<lambda>a_dst2a. (~(<<x, a_dst2a>> \\in a_voteunde_requestunde_msga))))&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\cup {<<x, j>>}))&((a_requnde_historyhash_primea=(a_requnde_historya \\cup {<<x, j>>}))&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_voteshash_primea=votes)&((a_leaderhash_primea=leader)&(a_decidedhash_primea=decided))))))))))))), x>>}))&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_voteshash_primea=votes)&((a_leaderhash_primea=leader)&(a_decidedhash_primea=decided))))))))))) == ?z_hbff" (is "?z_hbfg == _")
   by (unfold bEx_def)
   have z_Hbfg: "?z_hbfg" (is "\\E x : ?z_hbfz(x)")
   by (unfold z_Hbfg_z_Hbff, fact z_Hbff)
   have z_Hbga: "?z_hbfz((CHOOSE x:((x \\in Node)&((~(<<(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(<<x, j>> \\in a_requnde_historya))&(bAll(Node, (\<lambda>a_dst2a. (~(<<x, a_dst2a>> \\in a_voteunde_requestunde_msga))))&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\cup {<<x, j>>}))&((a_requnde_historyhash_primea=(a_requnde_historya \\cup {<<x, j>>}))&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_voteshash_primea=votes)&((a_leaderhash_primea=leader)&(a_decidedhash_primea=decided))))))))))))), x>> \\in a_requnde_historya))&(bAll(Node, (\<lambda>a_dst2a. (~(<<(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(<<x, j>> \\in a_requnde_historya))&(bAll(Node, (\<lambda>a_dst2a. (~(<<x, a_dst2a>> \\in a_voteunde_requestunde_msga))))&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\cup {<<x, j>>}))&((a_requnde_historyhash_primea=(a_requnde_historya \\cup {<<x, j>>}))&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_voteshash_primea=votes)&((a_leaderhash_primea=leader)&(a_decidedhash_primea=decided))))))))))))), a_dst2a>> \\in a_voteunde_requestunde_msga))))&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\cup {<<(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(<<x, j>> \\in a_requnde_historya))&(bAll(Node, (\<lambda>a_dst2a. (~(<<x, a_dst2a>> \\in a_voteunde_requestunde_msga))))&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\cup {<<x, j>>}))&((a_requnde_historyhash_primea=(a_requnde_historya \\cup {<<x, j>>}))&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_voteshash_primea=votes)&((a_leaderhash_primea=leader)&(a_decidedhash_primea=decided))))))))))))), x>>}))&((a_requnde_historyhash_primea=(a_requnde_historya \\cup {<<(CHOOSE x:((x \\in Node)&bEx(Node, (\<lambda>j. ((~(<<x, j>> \\in a_requnde_historya))&(bAll(Node, (\<lambda>a_dst2a. (~(<<x, a_dst2a>> \\in a_voteunde_requestunde_msga))))&((a_voteunde_requestunde_msghash_primea=(a_voteunde_requestunde_msga \\cup {<<x, j>>}))&((a_requnde_historyhash_primea=(a_requnde_historya \\cup {<<x, j>>}))&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_voteshash_primea=votes)&((a_leaderhash_primea=leader)&(a_decidedhash_primea=decided))))))))))))), x>>}))&((a_votedhash_primea=voted)&((a_voteunde_msghash_primea=a_voteunde_msga)&((a_voteshash_primea=votes)&((a_leaderhash_primea=leader)&(a_decidedhash_primea=decided))))))))))))" (is "?z_hbgc&?z_hbgd")
   by (rule zenon_ex_choose_0 [of "?z_hbfz", OF z_Hbfg])
   have z_Hbgd: "?z_hbgd" (is "?z_hbge&?z_hbgf")
   by (rule zenon_and_1 [OF z_Hbga])
   have z_Hbgf: "?z_hbgf" (is "?z_hbfn&?z_hbgg")
   by (rule zenon_and_1 [OF z_Hbgd])
   have z_Hbgg: "?z_hbgg" (is "?z_hbgh&?z_hbgi")
   by (rule zenon_and_1 [OF z_Hbgf])
   have z_Hbgi: "?z_hbgi" (is "?z_hbgj&?z_hkb")
   by (rule zenon_and_1 [OF z_Hbgg])
   have z_Hkb: "?z_hkb" (is "?z_hhd&?z_hkc")
   by (rule zenon_and_1 [OF z_Hbgi])
   have z_Hkc: "?z_hkc" (is "?z_hhb&?z_hkd")
   by (rule zenon_and_1 [OF z_Hkb])
   have z_Hhb: "?z_hhb"
   by (rule zenon_and_0 [OF z_Hkc])
   show FALSE
   by (rule zenon_L4_ [OF z_Hoj z_Hov z_How z_Hox z_Hhb z_Hnn z_Hod z_Hoy])
  qed
 next
  assume z_Hvw:"(a_voteshash_primea~=a_voteshash_primea)"
  show FALSE
  by (rule zenon_noteq [OF z_Hvw])
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 223"; *} qed
end
