(* automatically generated -- do not edit manually *)
theory peterson_IndProofs imports Constant Zenon begin
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

lemma ob'8:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
fixes flag flag'
fixes turn turn'
fixes pc pc'
(* usable definition vars suppressed *)
fixes ProcSet
(* usable definition Other suppressed *)
(* usable definition Spec suppressed *)
(* usable definition Liveness suppressed *)
assumes v'12: "(((ProcSet) = ({((0)), ((Succ[0]))})))"
assumes v'14: "(((((((flag) \<in> ([(ProcSet) \<rightarrow> ({(TRUE), (FALSE)})]))) & (((turn) \<in> (ProcSet))) & (((pc) \<in> ([(ProcSet) \<rightarrow> ({((0)), ((Succ[0])), ((Succ[Succ[0]])), ((Succ[Succ[Succ[0]]])), ((Succ[Succ[Succ[Succ[0]]]])), ((Succ[Succ[Succ[Succ[Succ[0]]]]]))})])))) & (\<forall> p \<in> (ProcSet) : (\<forall> q \<in> (ProcSet) : (((((p) \<noteq> (q))) \<Rightarrow> ((~ (((((fapply ((pc), (p))) = ((0)))) \<and> (((fapply ((pc), (q))) = ((0)))))))))))) & (\<forall> self \<in> (ProcSet) : (\<forall> other \<in> (ProcSet) : (((((turn) = (self))) \<or> ((~ (((fapply ((pc), (self))) = ((0))))))))))) \<and> ((\<exists> self \<in> (ProcSet) : (((((fapply ((pc), (self))) = ((Succ[0])))) & ((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(self)] = ((Succ[Succ[0]]))]))) & ((((a_flaghash_primea :: c)) = (flag))) & ((((a_turnhash_primea :: c)) = (turn)))) | ((((fapply ((pc), (self))) = ((Succ[Succ[0]])))) & ((((a_flaghash_primea :: c)) = ([(flag) EXCEPT ![(self)] = (TRUE)]))) & ((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(self)] = ((Succ[Succ[Succ[0]]]))]))) & ((((a_turnhash_primea :: c)) = (turn)))) | ((((fapply ((pc), (self))) = ((0)))) & ((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(self)] = ((Succ[Succ[Succ[Succ[Succ[0]]]]]))]))) & ((((a_flaghash_primea :: c)) = (flag))) & ((((a_turnhash_primea :: c)) = (turn)))) | ((((fapply ((pc), (self))) = ((Succ[Succ[Succ[Succ[Succ[0]]]]])))) & ((((a_flaghash_primea :: c)) = ([(flag) EXCEPT ![(self)] = (FALSE)]))) & ((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(self)] = ((Succ[0]))]))) & ((((a_turnhash_primea :: c)) = (turn)))))) | (\<exists> self \<in> (ProcSet) : (\<exists> other \<in> (ProcSet) : (((((fapply ((pc), (self))) = ((Succ[Succ[Succ[0]]])))) & (((self) \<noteq> (other))) & ((((a_turnhash_primea :: c)) = (other))) & ((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(self)] = ((Succ[Succ[Succ[Succ[0]]]]))]))) & ((((a_flaghash_primea :: c)) = (flag)))) | ((fapply ((flag), (self))) & (((turn) = (self))) & ((((Succ[Succ[Succ[Succ[0]]]])) = (fapply ((pc), (self))))) & ((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(self)] = ((0))]))) & ((((a_flaghash_primea :: c)) = (flag))) & ((((a_turnhash_primea :: c)) = (turn))))))))))"
shows "(((((a_flaghash_primea :: c)) \<in> ([(ProcSet) \<rightarrow> ({(TRUE), (FALSE)})]))) & ((((a_turnhash_primea :: c)) \<in> (ProcSet))) & ((((a_pchash_primea :: c)) \<in> ([(ProcSet) \<rightarrow> ({((0)), ((Succ[0])), ((Succ[Succ[0]])), ((Succ[Succ[Succ[0]]])), ((Succ[Succ[Succ[Succ[0]]]])), ((Succ[Succ[Succ[Succ[Succ[0]]]]]))})]))))"(is "PROP ?ob'8")
proof -
ML_command {* writeln "*** TLAPS ENTER 8"; *}
show "PROP ?ob'8"

(* BEGIN ZENON INPUT
;; file=peterson_IndProofs.tlaps/tlapm_999b79.znn; PATH='/home/egolf/.opam/4.07.1/bin:/home/egolf/.local/bin:/home/egolf/bin:/home/egolf/mambaforge/bin:/home/egolf/mambaforge/condabin:/home/egolf/.opam/4.07.1/bin:/home/egolf/.local/bin:/home/egolf/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/home/egolf/.local/bin/gurobi952/linux64/bin:/home/egolf/Projects/apalache/bin:/home/egolf/opt/foxitsoftware/foxitreader:/home/egolf/.local/bin/gurobi952/linux64/bin:/home/egolf/Projects/apalache/bin:/home/egolf/opt/foxitsoftware/foxitreader:/usr/local/bin:/usr/local/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >peterson_IndProofs.tlaps/tlapm_999b79.znn.out
;; obligation #8
$hyp "v'12" (= ProcSet
(TLA.set 0 (TLA.fapply TLA.Succ 0)))
$hyp "v'14" (/\ (/\ (/\ (TLA.in flag (TLA.FuncSet ProcSet (TLA.set T. F.)))
(TLA.in turn ProcSet) (TLA.in pc
(TLA.FuncSet ProcSet (TLA.set 0 (TLA.fapply TLA.Succ 0) (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0)) (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0))) (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0)))) (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0)))))))))
(TLA.bAll ProcSet ((p) (TLA.bAll ProcSet ((q) (=> (-. (= p q))
(-. (/\ (= (TLA.fapply pc p) 0) (= (TLA.fapply pc q) 0))))))))
(TLA.bAll ProcSet ((self) (TLA.bAll ProcSet ((other) (\/ (= turn self)
(-. (= (TLA.fapply pc self) 0))))))))
(\/ (TLA.bEx ProcSet ((self) (\/ (/\ (= (TLA.fapply pc self)
(TLA.fapply TLA.Succ 0)) (= a_pchash_primea
(TLA.except pc self (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0))))
(= a_flaghash_primea flag) (= a_turnhash_primea turn))
(/\ (= (TLA.fapply pc self) (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0)))
(= a_flaghash_primea (TLA.except flag self T.)) (= a_pchash_primea
(TLA.except pc self (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0)))))
(= a_turnhash_primea turn)) (/\ (= (TLA.fapply pc self) 0) (= a_pchash_primea
(TLA.except pc self (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0)))))))
(= a_flaghash_primea flag) (= a_turnhash_primea turn))
(/\ (= (TLA.fapply pc self)
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0))))))
(= a_flaghash_primea (TLA.except flag self F.)) (= a_pchash_primea
(TLA.except pc self (TLA.fapply TLA.Succ 0))) (= a_turnhash_primea turn)))))
(TLA.bEx ProcSet ((self) (TLA.bEx ProcSet ((other) (\/ (/\ (= (TLA.fapply pc self)
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0))))
(-. (= self other)) (= a_turnhash_primea other) (= a_pchash_primea
(TLA.except pc self (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0))))))
(= a_flaghash_primea flag)) (/\ (TLA.fapply flag self) (= turn self)
(= (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0))))
(TLA.fapply pc self)) (= a_pchash_primea (TLA.except pc self 0))
(= a_flaghash_primea flag) (= a_turnhash_primea
turn)))))))))
$goal (/\ (TLA.in a_flaghash_primea (TLA.FuncSet ProcSet (TLA.set T. F.)))
(TLA.in a_turnhash_primea ProcSet) (TLA.in a_pchash_primea
(TLA.FuncSet ProcSet (TLA.set 0 (TLA.fapply TLA.Succ 0) (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0)) (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0))) (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0)))) (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0)))))))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hb:"((((flag \\in FuncSet(ProcSet, {TRUE, FALSE}))&((turn \\in ProcSet)&(pc \\in FuncSet(ProcSet, {0, 1, 2, 3, 4, 5}))))&(bAll(ProcSet, (\<lambda>p. bAll(ProcSet, (\<lambda>q. ((p~=q)=>(~(((pc[p])=0)&((pc[q])=0))))))))&bAll(ProcSet, (\<lambda>self. bAll(ProcSet, (\<lambda>other. ((turn=self)|((pc[self])~=0))))))))&(bEx(ProcSet, (\<lambda>self. ((((pc[self])=1)&((a_pchash_primea=except(pc, self, 2))&((a_flaghash_primea=flag)&(a_turnhash_primea=turn))))|((((pc[self])=2)&((a_flaghash_primea=except(flag, self, TRUE))&((a_pchash_primea=except(pc, self, 3))&(a_turnhash_primea=turn))))|((((pc[self])=0)&((a_pchash_primea=except(pc, self, 5))&((a_flaghash_primea=flag)&(a_turnhash_primea=turn))))|(((pc[self])=5)&((a_flaghash_primea=except(flag, self, FALSE))&((a_pchash_primea=except(pc, self, 1))&(a_turnhash_primea=turn)))))))))|bEx(ProcSet, (\<lambda>self. bEx(ProcSet, (\<lambda>other. ((((pc[self])=3)&((self~=other)&((a_turnhash_primea=other)&((a_pchash_primea=except(pc, self, 4))&(a_flaghash_primea=flag)))))|((flag[self])&((turn=self)&((4=(pc[self]))&((a_pchash_primea=except(pc, self, 0))&((a_flaghash_primea=flag)&(a_turnhash_primea=turn)))))))))))))" (is "?z_hd&?z_hbx")
 using v'14 by blast
 have z_Ha:"(ProcSet={0, 1})" (is "_=?z_heg")
 using v'12 by blast
 have zenon_L1_: "(~(a_flaghash_primea \\in FuncSet(ProcSet, {TRUE, FALSE}))) ==> (flag \\in FuncSet(ProcSet, {TRUE, FALSE})) ==> (a_flaghash_primea=flag) ==> FALSE" (is "?z_heh ==> ?z_hf ==> ?z_hci ==> FALSE")
 proof -
  assume z_Heh:"?z_heh" (is "~?z_hei")
  assume z_Hf:"?z_hf"
  assume z_Hci:"?z_hci"
  show FALSE
  proof (rule notE [OF z_Heh])
   have z_Hej: "(flag=a_flaghash_primea)"
   by (rule sym [OF z_Hci])
   have z_Hei: "?z_hei"
   by (rule subst [where P="(\<lambda>zenon_Vplv. (zenon_Vplv \\in FuncSet(ProcSet, {TRUE, FALSE})))", OF z_Hej], fact z_Hf)
   thus "?z_hei" .
  qed
 qed
 have zenon_L2_: "(ProcSet=?z_heg) ==> (turn \\in ProcSet) ==> (a_turnhash_primea~=1) ==> (a_turnhash_primea=turn) ==> (a_turnhash_primea~=0) ==> FALSE" (is "?z_ha ==> ?z_hn ==> ?z_hen ==> ?z_hck ==> ?z_heo ==> FALSE")
 proof -
  assume z_Ha:"?z_ha"
  assume z_Hn:"?z_hn"
  assume z_Hen:"?z_hen" (is "_~=?z_hu")
  assume z_Hck:"?z_hck"
  assume z_Heo:"?z_heo"
  have z_Hep: "(turn \\in ?z_heg)" (is "?z_hep")
  by (rule subst [where P="(\<lambda>zenon_Vymr. (turn \\in zenon_Vymr))", OF z_Ha z_Hn])
  show FALSE
  proof (rule zenon_in_addElt [of "turn" "0" "{?z_hu}", OF z_Hep])
   assume z_Heu:"(turn=0)"
   show FALSE
   proof (rule notE [OF z_Heo])
    have z_Hev: "(a_turnhash_primea=0)"
    by (rule subst [where P="(\<lambda>zenon_Vqlv. (a_turnhash_primea=zenon_Vqlv))", OF z_Heu], fact z_Hck)
    thus "(a_turnhash_primea=0)" .
   qed
  next
   assume z_Hez:"(turn \\in {?z_hu})" (is "?z_hez")
   show FALSE
   proof (rule zenon_in_addElt [of "turn" "?z_hu" "{}", OF z_Hez])
    assume z_Hfb:"(turn=?z_hu)"
    show FALSE
    proof (rule notE [OF z_Hen])
     have z_Hfc: "(a_turnhash_primea=?z_hu)"
     by (rule subst [where P="(\<lambda>zenon_Vqlv. (a_turnhash_primea=zenon_Vqlv))", OF z_Hfb], fact z_Hck)
     thus "(a_turnhash_primea=?z_hu)" .
    qed
   next
    assume z_Hfd:"(turn \\in {})" (is "?z_hfd")
    show FALSE
    by (rule zenon_in_emptyset [of "turn", OF z_Hfd])
   qed
  qed
 qed
 have zenon_L3_: "(ProcSet=?z_heg) ==> (~(a_turnhash_primea \\in ProcSet)) ==> (a_turnhash_primea=turn) ==> (turn \\in ProcSet) ==> FALSE" (is "?z_ha ==> ?z_hfe ==> ?z_hck ==> ?z_hn ==> FALSE")
 proof -
  assume z_Ha:"?z_ha"
  assume z_Hfe:"?z_hfe" (is "~?z_hff")
  assume z_Hck:"?z_hck"
  assume z_Hn:"?z_hn"
  have z_Hfg: "(~(a_turnhash_primea \\in ?z_heg))" (is "~?z_hfh")
  by (rule subst [where P="(\<lambda>zenon_Vckv. (~(a_turnhash_primea \\in zenon_Vckv)))", OF z_Ha z_Hfe])
  have z_Heo: "(a_turnhash_primea~=0)"
  by (rule zenon_notin_addElt_0 [of "a_turnhash_primea" "0" "{1}", OF z_Hfg])
  have z_Hfm: "(~(a_turnhash_primea \\in {1}))" (is "~?z_hfn")
  by (rule zenon_notin_addElt_1 [of "a_turnhash_primea" "0" "{1}", OF z_Hfg])
  have z_Hen: "(a_turnhash_primea~=1)" (is "_~=?z_hu")
  by (rule zenon_notin_addElt_0 [of "a_turnhash_primea" "?z_hu" "{}", OF z_Hfm])
  show FALSE
  by (rule zenon_L2_ [OF z_Ha z_Hn z_Hen z_Hck z_Heo])
 qed
 have zenon_L4_: "(\\A zenon_Vm:((zenon_Vm \\in ProcSet)=>((pc[zenon_Vm]) \\in {0, 1, 2, 3, 4, 5}))) ==> ((CHOOSE zenon_Vpa:(~((zenon_Vpa \\in ProcSet)=>((a_pchash_primea[zenon_Vpa]) \\in {0, 1, 2, 3, 4, 5})))) \\in ProcSet) ==> (~((a_pchash_primea[(CHOOSE zenon_Vpa:(~((zenon_Vpa \\in ProcSet)=>((a_pchash_primea[zenon_Vpa]) \\in {0, 1, 2, 3, 4, 5}))))]) \\in {0, 1, 2, 3, 4, 5})) ==> ((a_pchash_primea[(CHOOSE zenon_Vpa:(~((zenon_Vpa \\in ProcSet)=>((a_pchash_primea[zenon_Vpa]) \\in {0, 1, 2, 3, 4, 5}))))])=(pc[(CHOOSE zenon_Vpa:(~((zenon_Vpa \\in ProcSet)=>((a_pchash_primea[zenon_Vpa]) \\in {0, 1, 2, 3, 4, 5}))))])) ==> FALSE" (is "?z_hfo ==> ?z_hfu ==> ?z_hgc ==> ?z_hgf ==> FALSE")
 proof -
  assume z_Hfo:"?z_hfo" (is "\\A x : ?z_hgh(x)")
  assume z_Hfu:"?z_hfu"
  assume z_Hgc:"?z_hgc" (is "~?z_hgd")
  assume z_Hgf:"?z_hgf" (is "?z_hge=?z_hgg")
  have z_Hgi: "?z_hgh((CHOOSE zenon_Vpa:(~((zenon_Vpa \\in ProcSet)=>((a_pchash_primea[zenon_Vpa]) \\in {0, 1, 2, 3, 4, 5})))))" (is "_=>?z_hgj")
  by (rule zenon_all_0 [of "?z_hgh" "(CHOOSE zenon_Vpa:(~((zenon_Vpa \\in ProcSet)=>((a_pchash_primea[zenon_Vpa]) \\in {0, 1, 2, 3, 4, 5}))))", OF z_Hfo])
  show FALSE
  proof (rule zenon_imply [OF z_Hgi])
   assume z_Hgk:"(~?z_hfu)"
   show FALSE
   by (rule notE [OF z_Hgk z_Hfu])
  next
   assume z_Hgj:"?z_hgj"
   show FALSE
   proof (rule notE [OF z_Hgc])
    have z_Hgl: "(?z_hgg=?z_hge)"
    by (rule sym [OF z_Hgf])
    have z_Hgd: "?z_hgd"
    by (rule subst [where P="(\<lambda>zenon_Vlce. (zenon_Vlce \\in {0, 1, 2, 3, 4, 5}))", OF z_Hgl], fact z_Hgj)
    thus "?z_hgd" .
   qed
  qed
 qed
 have zenon_L5_: "(\\A zenon_Vr:((zenon_Vr \\in ProcSet)=>((flag[zenon_Vr]) \\in {TRUE, FALSE}))) ==> ((CHOOSE zenon_Vhsb:(~((zenon_Vhsb \\in ProcSet)=>((a_flaghash_primea[zenon_Vhsb]) \\in {TRUE, FALSE})))) \\in ProcSet) ==> (~((a_flaghash_primea[(CHOOSE zenon_Vhsb:(~((zenon_Vhsb \\in ProcSet)=>((a_flaghash_primea[zenon_Vhsb]) \\in {TRUE, FALSE}))))]) \\in {TRUE, FALSE})) ==> ((a_flaghash_primea[(CHOOSE zenon_Vhsb:(~((zenon_Vhsb \\in ProcSet)=>((a_flaghash_primea[zenon_Vhsb]) \\in {TRUE, FALSE}))))])=(flag[(CHOOSE zenon_Vhsb:(~((zenon_Vhsb \\in ProcSet)=>((a_flaghash_primea[zenon_Vhsb]) \\in {TRUE, FALSE}))))])) ==> FALSE" (is "?z_hgp ==> ?z_hgv ==> ?z_hhd ==> ?z_hhg ==> FALSE")
 proof -
  assume z_Hgp:"?z_hgp" (is "\\A x : ?z_hhi(x)")
  assume z_Hgv:"?z_hgv"
  assume z_Hhd:"?z_hhd" (is "~?z_hhe")
  assume z_Hhg:"?z_hhg" (is "?z_hhf=?z_hhh")
  have z_Hhj: "?z_hhi((CHOOSE zenon_Vhsb:(~((zenon_Vhsb \\in ProcSet)=>((a_flaghash_primea[zenon_Vhsb]) \\in {TRUE, FALSE})))))" (is "_=>?z_hhk")
  by (rule zenon_all_0 [of "?z_hhi" "(CHOOSE zenon_Vhsb:(~((zenon_Vhsb \\in ProcSet)=>((a_flaghash_primea[zenon_Vhsb]) \\in {TRUE, FALSE}))))", OF z_Hgp])
  show FALSE
  proof (rule zenon_imply [OF z_Hhj])
   assume z_Hhl:"(~?z_hgv)"
   show FALSE
   by (rule notE [OF z_Hhl z_Hgv])
  next
   assume z_Hhk:"?z_hhk"
   show FALSE
   proof (rule notE [OF z_Hhd])
    have z_Hhm: "(?z_hhh=?z_hhf)"
    by (rule sym [OF z_Hhg])
    have z_Hhe: "?z_hhe"
    by (rule subst [where P="(\<lambda>zenon_Vtk. (zenon_Vtk \\in {TRUE, FALSE}))", OF z_Hhm], fact z_Hhk)
    thus "?z_hhe" .
   qed
  qed
 qed
 have zenon_L6_: "(~isAFcn(except(pc, (CHOOSE x:((x \\in ProcSet)&bEx(ProcSet, (\<lambda>other. ((((pc[x])=3)&((x~=other)&((a_turnhash_primea=other)&((a_pchash_primea=except(pc, x, 4))&(a_flaghash_primea=flag)))))|((flag[x])&((turn=x)&((4=(pc[x]))&((a_pchash_primea=except(pc, x, 0))&((a_flaghash_primea=flag)&(a_turnhash_primea=turn))))))))))), 4))) ==> FALSE" (is "?z_hhq ==> FALSE")
 proof -
  assume z_Hhq:"?z_hhq" (is "~?z_hhr")
  show FALSE
  by (rule zenon_notisafcn_except [of "pc" "(CHOOSE x:((x \\in ProcSet)&bEx(ProcSet, (\<lambda>other. ((((pc[x])=3)&((x~=other)&((a_turnhash_primea=other)&((a_pchash_primea=except(pc, x, 4))&(a_flaghash_primea=flag)))))|((flag[x])&((turn=x)&((4=(pc[x]))&((a_pchash_primea=except(pc, x, 0))&((a_flaghash_primea=flag)&(a_turnhash_primea=turn)))))))))))" "4", OF z_Hhq])
 qed
 have zenon_L7_: "(ProcSet=?z_heg) ==> (DOMAIN(a_pchash_primea)~=ProcSet) ==> (a_pchash_primea=except(pc, (CHOOSE x:((x \\in ProcSet)&bEx(ProcSet, (\<lambda>other. ((((pc[x])=3)&((x~=other)&((a_turnhash_primea=other)&((a_pchash_primea=except(pc, x, 4))&(a_flaghash_primea=flag)))))|((flag[x])&((turn=x)&((4=(pc[x]))&((a_pchash_primea=except(pc, x, 0))&((a_flaghash_primea=flag)&(a_turnhash_primea=turn))))))))))), 4)) ==> (DOMAIN(pc)=?z_heg) ==> FALSE" (is "?z_ha ==> ?z_his ==> ?z_hiu ==> ?z_hiv ==> FALSE")
 proof -
  assume z_Ha:"?z_ha"
  assume z_His:"?z_his" (is "?z_hit~=_")
  assume z_Hiu:"?z_hiu" (is "_=?z_hhs")
  assume z_Hiv:"?z_hiv" (is "?z_hiw=_")
  have z_Hix: "(?z_hit~=?z_heg)"
  by (rule subst [where P="(\<lambda>zenon_Vikv. (?z_hit~=zenon_Vikv))", OF z_Ha z_His])
  have z_Hjb: "(DOMAIN(?z_hhs)~=?z_heg)" (is "?z_hjc~=_")
  by (rule subst [where P="(\<lambda>zenon_Vos. (DOMAIN(zenon_Vos)~=?z_heg))", OF z_Hiu z_Hix])
  have z_Hjh: "(?z_hiw~=?z_heg)"
  by (rule zenon_domain_except_0 [of "(\<lambda>zenon_Vns. (zenon_Vns~=?z_heg))" "pc" "(CHOOSE x:((x \\in ProcSet)&bEx(ProcSet, (\<lambda>other. ((((pc[x])=3)&((x~=other)&((a_turnhash_primea=other)&((a_pchash_primea=except(pc, x, 4))&(a_flaghash_primea=flag)))))|((flag[x])&((turn=x)&((4=(pc[x]))&((a_pchash_primea=except(pc, x, 0))&((a_flaghash_primea=flag)&(a_turnhash_primea=turn)))))))))))" "4", OF z_Hjb])
  show FALSE
  by (rule notE [OF z_Hjh z_Hiv])
 qed
 have zenon_L8_: "(~isAFcn(except(pc, (CHOOSE x:((x \\in ProcSet)&bEx(ProcSet, (\<lambda>other. ((((pc[x])=3)&((x~=other)&((a_turnhash_primea=other)&((a_pchash_primea=except(pc, x, 4))&(a_flaghash_primea=flag)))))|((flag[x])&((turn=x)&((4=(pc[x]))&((a_pchash_primea=except(pc, x, 0))&((a_flaghash_primea=flag)&(a_turnhash_primea=turn))))))))))), 0))) ==> FALSE" (is "?z_hjl ==> FALSE")
 proof -
  assume z_Hjl:"?z_hjl" (is "~?z_hjm")
  show FALSE
  by (rule zenon_notisafcn_except [of "pc" "(CHOOSE x:((x \\in ProcSet)&bEx(ProcSet, (\<lambda>other. ((((pc[x])=3)&((x~=other)&((a_turnhash_primea=other)&((a_pchash_primea=except(pc, x, 4))&(a_flaghash_primea=flag)))))|((flag[x])&((turn=x)&((4=(pc[x]))&((a_pchash_primea=except(pc, x, 0))&((a_flaghash_primea=flag)&(a_turnhash_primea=turn)))))))))))" "0", OF z_Hjl])
 qed
 have zenon_L9_: "(ProcSet=?z_heg) ==> (DOMAIN(a_pchash_primea)~=ProcSet) ==> (a_pchash_primea=except(pc, (CHOOSE x:((x \\in ProcSet)&bEx(ProcSet, (\<lambda>other. ((((pc[x])=3)&((x~=other)&((a_turnhash_primea=other)&((a_pchash_primea=except(pc, x, 4))&(a_flaghash_primea=flag)))))|((flag[x])&((turn=x)&((4=(pc[x]))&((a_pchash_primea=except(pc, x, 0))&((a_flaghash_primea=flag)&(a_turnhash_primea=turn))))))))))), 0)) ==> (DOMAIN(pc)=?z_heg) ==> FALSE" (is "?z_ha ==> ?z_his ==> ?z_hjo ==> ?z_hiv ==> FALSE")
 proof -
  assume z_Ha:"?z_ha"
  assume z_His:"?z_his" (is "?z_hit~=_")
  assume z_Hjo:"?z_hjo" (is "_=?z_hjn")
  assume z_Hiv:"?z_hiv" (is "?z_hiw=_")
  have z_Hix: "(?z_hit~=?z_heg)"
  by (rule subst [where P="(\<lambda>zenon_Vikv. (?z_hit~=zenon_Vikv))", OF z_Ha z_His])
  have z_Hjp: "(DOMAIN(?z_hjn)~=?z_heg)" (is "?z_hjq~=_")
  by (rule subst [where P="(\<lambda>zenon_Vos. (DOMAIN(zenon_Vos)~=?z_heg))", OF z_Hjo z_Hix])
  have z_Hjh: "(?z_hiw~=?z_heg)"
  by (rule zenon_domain_except_0 [of "(\<lambda>zenon_Vns. (zenon_Vns~=?z_heg))" "pc" "(CHOOSE x:((x \\in ProcSet)&bEx(ProcSet, (\<lambda>other. ((((pc[x])=3)&((x~=other)&((a_turnhash_primea=other)&((a_pchash_primea=except(pc, x, 4))&(a_flaghash_primea=flag)))))|((flag[x])&((turn=x)&((4=(pc[x]))&((a_pchash_primea=except(pc, x, 0))&((a_flaghash_primea=flag)&(a_turnhash_primea=turn)))))))))))" "0", OF z_Hjp])
  show FALSE
  by (rule notE [OF z_Hjh z_Hiv])
 qed
 have zenon_L10_: "((flag[(CHOOSE x:((x \\in ProcSet)&bEx(ProcSet, (\<lambda>other. ((((pc[x])=3)&((x~=other)&((a_turnhash_primea=other)&((a_pchash_primea=except(pc, x, 4))&(a_flaghash_primea=flag)))))|((flag[x])&((turn=x)&((4=(pc[x]))&((a_pchash_primea=except(pc, x, 0))&((a_flaghash_primea=flag)&(a_turnhash_primea=turn)))))))))))])&((turn=(CHOOSE x:((x \\in ProcSet)&bEx(ProcSet, (\<lambda>other. ((((pc[x])=3)&((x~=other)&((a_turnhash_primea=other)&((a_pchash_primea=except(pc, x, 4))&(a_flaghash_primea=flag)))))|((flag[x])&((turn=x)&((4=(pc[x]))&((a_pchash_primea=except(pc, x, 0))&((a_flaghash_primea=flag)&(a_turnhash_primea=turn))))))))))))&((4=(pc[(CHOOSE x:((x \\in ProcSet)&bEx(ProcSet, (\<lambda>other. ((((pc[x])=3)&((x~=other)&((a_turnhash_primea=other)&((a_pchash_primea=except(pc, x, 4))&(a_flaghash_primea=flag)))))|((flag[x])&((turn=x)&((4=(pc[x]))&((a_pchash_primea=except(pc, x, 0))&((a_flaghash_primea=flag)&(a_turnhash_primea=turn)))))))))))]))&((a_pchash_primea=except(pc, (CHOOSE x:((x \\in ProcSet)&bEx(ProcSet, (\<lambda>other. ((((pc[x])=3)&((x~=other)&((a_turnhash_primea=other)&((a_pchash_primea=except(pc, x, 4))&(a_flaghash_primea=flag)))))|((flag[x])&((turn=x)&((4=(pc[x]))&((a_pchash_primea=except(pc, x, 0))&((a_flaghash_primea=flag)&(a_turnhash_primea=turn))))))))))), 0))&((a_flaghash_primea=flag)&(a_turnhash_primea=turn)))))) ==> (~((a_flaghash_primea \\in FuncSet(ProcSet, {TRUE, FALSE}))&((a_turnhash_primea \\in ProcSet)&(a_pchash_primea \\in FuncSet(ProcSet, {0, 1, 2, 3, 4, 5}))))) ==> (flag \\in FuncSet(ProcSet, {TRUE, FALSE})) ==> (turn \\in ProcSet) ==> (ProcSet=?z_heg) ==> (pc \\in FuncSet(ProcSet, {0, 1, 2, 3, 4, 5})) ==> FALSE" (is "?z_hjr ==> ?z_hc ==> ?z_hf ==> ?z_hn ==> ?z_ha ==> ?z_hp ==> FALSE")
 proof -
  assume z_Hjr:"?z_hjr" (is "?z_hjs&?z_hjt")
  assume z_Hc:"?z_hc" (is "~(?z_hei&?z_hka)")
  assume z_Hf:"?z_hf"
  assume z_Hn:"?z_hn"
  assume z_Ha:"?z_ha"
  assume z_Hp:"?z_hp"
  have z_Hjt: "?z_hjt" (is "?z_hju&?z_hjv")
  by (rule zenon_and_1 [OF z_Hjr])
  have z_Hjv: "?z_hjv" (is "?z_hjw&?z_hjy")
  by (rule zenon_and_1 [OF z_Hjt])
  have z_Hjy: "?z_hjy" (is "?z_hjo&?z_hch")
  by (rule zenon_and_1 [OF z_Hjv])
  have z_Hjo: "?z_hjo" (is "_=?z_hjn")
  by (rule zenon_and_0 [OF z_Hjy])
  have z_Hch: "?z_hch" (is "?z_hci&?z_hck")
  by (rule zenon_and_1 [OF z_Hjy])
  have z_Hci: "?z_hci"
  by (rule zenon_and_0 [OF z_Hch])
  have z_Hck: "?z_hck"
  by (rule zenon_and_1 [OF z_Hch])
  show FALSE
  proof (rule zenon_notand [OF z_Hc])
   assume z_Heh:"(~?z_hei)"
   show FALSE
   by (rule zenon_L1_ [OF z_Heh z_Hf z_Hci])
  next
   assume z_Hkc:"(~?z_hka)" (is "~(?z_hff&?z_hkb)")
   show FALSE
   proof (rule zenon_notand [OF z_Hkc])
    assume z_Hfe:"(~?z_hff)"
    show FALSE
    by (rule zenon_L3_ [OF z_Ha z_Hfe z_Hck z_Hn])
   next
    assume z_Hkd:"(~?z_hkb)"
    have z_Hke: "(pc \\in FuncSet(?z_heg, {0, 1, 2, 3, 4, 5}))" (is "?z_hke")
    by (rule subst [where P="(\<lambda>zenon_Vgkv. (pc \\in FuncSet(zenon_Vgkv, {0, 1, 2, 3, 4, 5})))", OF z_Ha z_Hp])
    have z_Hiv: "(DOMAIN(pc)=?z_heg)" (is "?z_hiw=_")
    by (rule zenon_in_funcset_1 [of "pc" "?z_heg" "{0, 1, 2, 3, 4, 5}", OF z_Hke])
    have z_Hkk: "(?z_hiw=ProcSet)"
    by (rule zenon_in_funcset_1 [of "pc" "ProcSet" "{0, 1, 2, 3, 4, 5}", OF z_Hp])
    have z_Hkk: "(?z_hiw=ProcSet)"
    by (rule zenon_in_funcset_1 [of "pc" "ProcSet" "{0, 1, 2, 3, 4, 5}", OF z_Hp])
    have z_Hfo: "(\\A zenon_Vm:((zenon_Vm \\in ProcSet)=>((pc[zenon_Vm]) \\in {0, 1, 2, 3, 4, 5})))" (is "\\A x : ?z_hgh(x)")
    by (rule zenon_in_funcset_2 [of "pc" "ProcSet" "{0, 1, 2, 3, 4, 5}", OF z_Hp])
    have z_Hkl: "(((isAFcn(a_pchash_primea)<=>isAFcn(?z_hjn))&(DOMAIN(a_pchash_primea)=DOMAIN(?z_hjn)))&(\\A zenon_Vja:((a_pchash_primea[zenon_Vja])=(?z_hjn[zenon_Vja]))))" (is "?z_hkm&?z_hkq")
    by (rule zenon_funequal_0 [of "a_pchash_primea" "?z_hjn", OF z_Hjo])
    have z_Hkm: "?z_hkm" (is "?z_hkn&?z_hkp")
    by (rule zenon_and_0 [OF z_Hkl])
    have z_Hkq: "?z_hkq" (is "\\A x : ?z_hkv(x)")
    by (rule zenon_and_1 [OF z_Hkl])
    have z_Hkn: "?z_hkn" (is "?z_hko<=>?z_hjm")
    by (rule zenon_and_0 [OF z_Hkm])
    show FALSE
    proof (rule zenon_equiv [OF z_Hkn])
     assume z_Hkw:"(~?z_hko)"
     assume z_Hjl:"(~?z_hjm)"
     show FALSE
     by (rule zenon_L8_ [OF z_Hjl])
    next
     assume z_Hko:"?z_hko"
     assume z_Hjm:"?z_hjm"
     show FALSE
     proof (rule zenon_notin_funcset [of "a_pchash_primea" "ProcSet" "{0, 1, 2, 3, 4, 5}", OF z_Hkd])
      assume z_Hkw:"(~?z_hko)"
      show FALSE
      by (rule notE [OF z_Hkw z_Hko])
     next
      assume z_His:"(DOMAIN(a_pchash_primea)~=ProcSet)" (is "?z_hit~=_")
      show FALSE
      by (rule zenon_L9_ [OF z_Ha z_His z_Hjo z_Hiv])
     next
      assume z_Hkx:"(~(\\A zenon_Vpa:((zenon_Vpa \\in ProcSet)=>((a_pchash_primea[zenon_Vpa]) \\in {0, 1, 2, 3, 4, 5}))))" (is "~(\\A x : ?z_hkz(x))")
      have z_Hla: "(\\E zenon_Vpa:(~((zenon_Vpa \\in ProcSet)=>((a_pchash_primea[zenon_Vpa]) \\in {0, 1, 2, 3, 4, 5}))))" (is "\\E x : ?z_hlb(x)")
      by (rule zenon_notallex_0 [of "?z_hkz", OF z_Hkx])
      have z_Hlc: "?z_hlb((CHOOSE zenon_Vpa:(~((zenon_Vpa \\in ProcSet)=>((a_pchash_primea[zenon_Vpa]) \\in {0, 1, 2, 3, 4, 5})))))" (is "~(?z_hfu=>?z_hgd)")
      by (rule zenon_ex_choose_0 [of "?z_hlb", OF z_Hla])
      have z_Hfu: "?z_hfu"
      by (rule zenon_notimply_0 [OF z_Hlc])
      have z_Hgc: "(~?z_hgd)"
      by (rule zenon_notimply_1 [OF z_Hlc])
      have z_Hld: "((a_pchash_primea[(CHOOSE zenon_Vpa:(~((zenon_Vpa \\in ProcSet)=>((a_pchash_primea[zenon_Vpa]) \\in {0, 1, 2, 3, 4, 5}))))])~=0)" (is "?z_hge~=_")
      by (rule zenon_notin_addElt_0 [of "?z_hge" "0" "{1, 2, 3, 4, 5}", OF z_Hgc])
      have z_Hlf: "((CHOOSE zenon_Vpa:(~((zenon_Vpa \\in ProcSet)=>((a_pchash_primea[zenon_Vpa]) \\in {0, 1, 2, 3, 4, 5})))) \\in ?z_hiw)" (is "?z_hlf")
      by (rule ssubst [where P="(\<lambda>zenon_Vip. ((CHOOSE zenon_Vpa:(~((zenon_Vpa \\in ProcSet)=>((a_pchash_primea[zenon_Vpa]) \\in {0, 1, 2, 3, 4, 5})))) \\in zenon_Vip))", OF z_Hkk z_Hfu])
      have z_Hlj: "?z_hkv((CHOOSE zenon_Vpa:(~((zenon_Vpa \\in ProcSet)=>((a_pchash_primea[zenon_Vpa]) \\in {0, 1, 2, 3, 4, 5})))))" (is "_=?z_hlk")
      by (rule zenon_all_0 [of "?z_hkv" "(CHOOSE zenon_Vpa:(~((zenon_Vpa \\in ProcSet)=>((a_pchash_primea[zenon_Vpa]) \\in {0, 1, 2, 3, 4, 5}))))", OF z_Hkq])
      show FALSE
      proof (rule zenon_fapplyexcept [of "(\<lambda>zenon_Vgs. (?z_hge=zenon_Vgs))" "pc" "(CHOOSE x:((x \\in ProcSet)&bEx(ProcSet, (\<lambda>other. ((((pc[x])=3)&((x~=other)&((a_turnhash_primea=other)&((a_pchash_primea=except(pc, x, 4))&?z_hci))))|((flag[x])&((turn=x)&((4=(pc[x]))&((a_pchash_primea=except(pc, x, 0))&?z_hch)))))))))" "0" "(CHOOSE zenon_Vpa:(~((zenon_Vpa \\in ProcSet)=>((a_pchash_primea[zenon_Vpa]) \\in {0, 1, 2, 3, 4, 5}))))", OF z_Hlj])
       assume z_Hlf:"?z_hlf"
       assume z_Hlo:"((CHOOSE x:((x \\in ProcSet)&bEx(ProcSet, (\<lambda>other. ((((pc[x])=3)&((x~=other)&((a_turnhash_primea=other)&((a_pchash_primea=except(pc, x, 4))&?z_hci))))|((flag[x])&((turn=x)&((4=(pc[x]))&((a_pchash_primea=except(pc, x, 0))&?z_hch)))))))))=(CHOOSE zenon_Vpa:(~((zenon_Vpa \\in ProcSet)=>((a_pchash_primea[zenon_Vpa]) \\in {0, 1, 2, 3, 4, 5})))))" (is "?z_hht=?z_hfv")
       assume z_Hlp:"(?z_hge=0)"
       show FALSE
       by (rule notE [OF z_Hld z_Hlp])
      next
       assume z_Hlf:"?z_hlf"
       assume z_Hlq:"((CHOOSE x:((x \\in ProcSet)&bEx(ProcSet, (\<lambda>other. ((((pc[x])=3)&((x~=other)&((a_turnhash_primea=other)&((a_pchash_primea=except(pc, x, 4))&?z_hci))))|((flag[x])&((turn=x)&((4=(pc[x]))&((a_pchash_primea=except(pc, x, 0))&?z_hch)))))))))~=(CHOOSE zenon_Vpa:(~((zenon_Vpa \\in ProcSet)=>((a_pchash_primea[zenon_Vpa]) \\in {0, 1, 2, 3, 4, 5})))))" (is "?z_hht~=?z_hfv")
       assume z_Hgf:"(?z_hge=(pc[?z_hfv]))" (is "_=?z_hgg")
       show FALSE
       by (rule zenon_L4_ [OF z_Hfo z_Hfu z_Hgc z_Hgf])
      next
       assume z_Hlr:"(~?z_hlf)"
       show FALSE
       by (rule notE [OF z_Hlr z_Hlf])
      qed
     qed
    qed
   qed
  qed
 qed
 assume z_Hc:"(~((a_flaghash_primea \\in FuncSet(ProcSet, {TRUE, FALSE}))&((a_turnhash_primea \\in ProcSet)&(a_pchash_primea \\in FuncSet(ProcSet, {0, 1, 2, 3, 4, 5})))))" (is "~(?z_hei&?z_hka)")
 have z_Hd: "?z_hd" (is "?z_he&?z_hz")
 by (rule zenon_and_0 [OF z_Hb])
 have z_Hbx: "?z_hbx" (is "?z_hby|?z_hdj")
 by (rule zenon_and_1 [OF z_Hb])
 have z_He: "?z_he" (is "?z_hf&?z_hm")
 by (rule zenon_and_0 [OF z_Hd])
 have z_Hf: "?z_hf"
 by (rule zenon_and_0 [OF z_He])
 have z_Hm: "?z_hm" (is "?z_hn&?z_hp")
 by (rule zenon_and_1 [OF z_He])
 have z_Hn: "?z_hn"
 by (rule zenon_and_0 [OF z_Hm])
 have z_Hp: "?z_hp"
 by (rule zenon_and_1 [OF z_Hm])
 show FALSE
 proof (rule zenon_or [OF z_Hbx])
  assume z_Hby:"?z_hby"
  have z_Hls_z_Hby: "(\\E x:((x \\in ProcSet)&((((pc[x])=1)&((a_pchash_primea=except(pc, x, 2))&((a_flaghash_primea=flag)&(a_turnhash_primea=turn))))|((((pc[x])=2)&((a_flaghash_primea=except(flag, x, TRUE))&((a_pchash_primea=except(pc, x, 3))&(a_turnhash_primea=turn))))|((((pc[x])=0)&((a_pchash_primea=except(pc, x, 5))&((a_flaghash_primea=flag)&(a_turnhash_primea=turn))))|(((pc[x])=5)&((a_flaghash_primea=except(flag, x, FALSE))&((a_pchash_primea=except(pc, x, 1))&(a_turnhash_primea=turn))))))))) == ?z_hby" (is "?z_hls == _")
  by (unfold bEx_def)
  have z_Hls: "?z_hls" (is "\\E x : ?z_hmx(x)")
  by (unfold z_Hls_z_Hby, fact z_Hby)
  have z_Hmy: "?z_hmx((CHOOSE x:((x \\in ProcSet)&((((pc[x])=1)&((a_pchash_primea=except(pc, x, 2))&((a_flaghash_primea=flag)&(a_turnhash_primea=turn))))|((((pc[x])=2)&((a_flaghash_primea=except(flag, x, TRUE))&((a_pchash_primea=except(pc, x, 3))&(a_turnhash_primea=turn))))|((((pc[x])=0)&((a_pchash_primea=except(pc, x, 5))&((a_flaghash_primea=flag)&(a_turnhash_primea=turn))))|(((pc[x])=5)&((a_flaghash_primea=except(flag, x, FALSE))&((a_pchash_primea=except(pc, x, 1))&(a_turnhash_primea=turn))))))))))" (is "?z_hna&?z_hnb")
  by (rule zenon_ex_choose_0 [of "?z_hmx", OF z_Hls])
  have z_Hnb: "?z_hnb" (is "?z_hnc|?z_hnd")
  by (rule zenon_and_1 [OF z_Hmy])
  show FALSE
  proof (rule zenon_or [OF z_Hnb])
   assume z_Hnc:"?z_hnc" (is "?z_hne&?z_hnf")
   have z_Hnf: "?z_hnf" (is "?z_hng&?z_hch")
   by (rule zenon_and_1 [OF z_Hnc])
   have z_Hng: "?z_hng" (is "_=?z_hnh")
   by (rule zenon_and_0 [OF z_Hnf])
   have z_Hch: "?z_hch" (is "?z_hci&?z_hck")
   by (rule zenon_and_1 [OF z_Hnf])
   have z_Hci: "?z_hci"
   by (rule zenon_and_0 [OF z_Hch])
   have z_Hck: "?z_hck"
   by (rule zenon_and_1 [OF z_Hch])
   show FALSE
   proof (rule zenon_notand [OF z_Hc])
    assume z_Heh:"(~?z_hei)"
    show FALSE
    by (rule zenon_L1_ [OF z_Heh z_Hf z_Hci])
   next
    assume z_Hkc:"(~?z_hka)" (is "~(?z_hff&?z_hkb)")
    show FALSE
    proof (rule zenon_notand [OF z_Hkc])
     assume z_Hfe:"(~?z_hff)"
     show FALSE
     by (rule zenon_L3_ [OF z_Ha z_Hfe z_Hck z_Hn])
    next
     assume z_Hkd:"(~?z_hkb)"
     have z_Hke: "(pc \\in FuncSet(?z_heg, {0, 1, 2, 3, 4, 5}))" (is "?z_hke")
     by (rule subst [where P="(\<lambda>zenon_Vgkv. (pc \\in FuncSet(zenon_Vgkv, {0, 1, 2, 3, 4, 5})))", OF z_Ha z_Hp])
     have z_Hiv: "(DOMAIN(pc)=?z_heg)" (is "?z_hiw=_")
     by (rule zenon_in_funcset_1 [of "pc" "?z_heg" "{0, 1, 2, 3, 4, 5}", OF z_Hke])
     have z_Hkk: "(?z_hiw=ProcSet)"
     by (rule zenon_in_funcset_1 [of "pc" "ProcSet" "{0, 1, 2, 3, 4, 5}", OF z_Hp])
     have z_Hkk: "(?z_hiw=ProcSet)"
     by (rule zenon_in_funcset_1 [of "pc" "ProcSet" "{0, 1, 2, 3, 4, 5}", OF z_Hp])
     have z_Hfo: "(\\A zenon_Vm:((zenon_Vm \\in ProcSet)=>((pc[zenon_Vm]) \\in {0, 1, 2, 3, 4, 5})))" (is "\\A x : ?z_hgh(x)")
     by (rule zenon_in_funcset_2 [of "pc" "ProcSet" "{0, 1, 2, 3, 4, 5}", OF z_Hp])
     have z_Hni: "(((isAFcn(a_pchash_primea)<=>isAFcn(?z_hnh))&(DOMAIN(a_pchash_primea)=DOMAIN(?z_hnh)))&(\\A zenon_Vvjs:((a_pchash_primea[zenon_Vvjs])=(?z_hnh[zenon_Vvjs]))))" (is "?z_hnj&?z_hno")
     by (rule zenon_funequal_0 [of "a_pchash_primea" "?z_hnh", OF z_Hng])
     have z_Hnj: "?z_hnj" (is "?z_hnk&?z_hnm")
     by (rule zenon_and_0 [OF z_Hni])
     have z_Hno: "?z_hno" (is "\\A x : ?z_hnt(x)")
     by (rule zenon_and_1 [OF z_Hni])
     have z_Hnk: "?z_hnk" (is "?z_hko<=>?z_hnl")
     by (rule zenon_and_0 [OF z_Hnj])
     show FALSE
     proof (rule zenon_equiv [OF z_Hnk])
      assume z_Hkw:"(~?z_hko)"
      assume z_Hnu:"(~?z_hnl)"
      show FALSE
      by (rule zenon_notisafcn_except [of "pc" "(CHOOSE x:((x \\in ProcSet)&((((pc[x])=1)&((a_pchash_primea=except(pc, x, 2))&?z_hch))|((((pc[x])=2)&((a_flaghash_primea=except(flag, x, TRUE))&((a_pchash_primea=except(pc, x, 3))&?z_hck)))|((((pc[x])=0)&((a_pchash_primea=except(pc, x, 5))&?z_hch))|(((pc[x])=5)&((a_flaghash_primea=except(flag, x, FALSE))&((a_pchash_primea=except(pc, x, 1))&?z_hck))))))))" "2", OF z_Hnu])
     next
      assume z_Hko:"?z_hko"
      assume z_Hnl:"?z_hnl"
      show FALSE
      proof (rule zenon_notin_funcset [of "a_pchash_primea" "ProcSet" "{0, 1, 2, 3, 4, 5}", OF z_Hkd])
       assume z_Hkw:"(~?z_hko)"
       show FALSE
       by (rule notE [OF z_Hkw z_Hko])
      next
       assume z_His:"(DOMAIN(a_pchash_primea)~=ProcSet)" (is "?z_hit~=_")
       have z_Hix: "(?z_hit~=?z_heg)"
       by (rule subst [where P="(\<lambda>zenon_Vikv. (?z_hit~=zenon_Vikv))", OF z_Ha z_His])
       have z_Hnv: "(DOMAIN(?z_hnh)~=?z_heg)" (is "?z_hnn~=_")
       by (rule subst [where P="(\<lambda>zenon_Vos. (DOMAIN(zenon_Vos)~=?z_heg))", OF z_Hng z_Hix])
       have z_Hjh: "(?z_hiw~=?z_heg)"
       by (rule zenon_domain_except_0 [of "(\<lambda>zenon_Vns. (zenon_Vns~=?z_heg))" "pc" "(CHOOSE x:((x \\in ProcSet)&((((pc[x])=1)&((a_pchash_primea=except(pc, x, 2))&?z_hch))|((((pc[x])=2)&((a_flaghash_primea=except(flag, x, TRUE))&((a_pchash_primea=except(pc, x, 3))&?z_hck)))|((((pc[x])=0)&((a_pchash_primea=except(pc, x, 5))&?z_hch))|(((pc[x])=5)&((a_flaghash_primea=except(flag, x, FALSE))&((a_pchash_primea=except(pc, x, 1))&?z_hck))))))))" "2", OF z_Hnv])
       show FALSE
       by (rule notE [OF z_Hjh z_Hiv])
      next
       assume z_Hkx:"(~(\\A zenon_Vpa:((zenon_Vpa \\in ProcSet)=>((a_pchash_primea[zenon_Vpa]) \\in {0, 1, 2, 3, 4, 5}))))" (is "~(\\A x : ?z_hkz(x))")
       have z_Hla: "(\\E zenon_Vpa:(~((zenon_Vpa \\in ProcSet)=>((a_pchash_primea[zenon_Vpa]) \\in {0, 1, 2, 3, 4, 5}))))" (is "\\E x : ?z_hlb(x)")
       by (rule zenon_notallex_0 [of "?z_hkz", OF z_Hkx])
       have z_Hlc: "?z_hlb((CHOOSE zenon_Vpa:(~((zenon_Vpa \\in ProcSet)=>((a_pchash_primea[zenon_Vpa]) \\in {0, 1, 2, 3, 4, 5})))))" (is "~(?z_hfu=>?z_hgd)")
       by (rule zenon_ex_choose_0 [of "?z_hlb", OF z_Hla])
       have z_Hfu: "?z_hfu"
       by (rule zenon_notimply_0 [OF z_Hlc])
       have z_Hgc: "(~?z_hgd)"
       by (rule zenon_notimply_1 [OF z_Hlc])
       have z_Hnw: "(~((a_pchash_primea[(CHOOSE zenon_Vpa:(~((zenon_Vpa \\in ProcSet)=>((a_pchash_primea[zenon_Vpa]) \\in {0, 1, 2, 3, 4, 5}))))]) \\in {1, 2, 3, 4, 5}))" (is "~?z_hnx")
       by (rule zenon_notin_addElt_1 [of "(a_pchash_primea[(CHOOSE zenon_Vpa:(~((zenon_Vpa \\in ProcSet)=>((a_pchash_primea[zenon_Vpa]) \\in {0, 1, 2, 3, 4, 5}))))])" "0" "{1, 2, 3, 4, 5}", OF z_Hgc])
       have z_Hny: "(~((a_pchash_primea[(CHOOSE zenon_Vpa:(~((zenon_Vpa \\in ProcSet)=>((a_pchash_primea[zenon_Vpa]) \\in {0, 1, 2, 3, 4, 5}))))]) \\in {2, 3, 4, 5}))" (is "~?z_hnz")
       by (rule zenon_notin_addElt_1 [of "(a_pchash_primea[(CHOOSE zenon_Vpa:(~((zenon_Vpa \\in ProcSet)=>((a_pchash_primea[zenon_Vpa]) \\in {0, 1, 2, 3, 4, 5}))))])" "1" "{2, 3, 4, 5}", OF z_Hnw])
       have z_Hob: "((a_pchash_primea[(CHOOSE zenon_Vpa:(~((zenon_Vpa \\in ProcSet)=>((a_pchash_primea[zenon_Vpa]) \\in {0, 1, 2, 3, 4, 5}))))])~=2)" (is "?z_hge~=?z_hv")
       by (rule zenon_notin_addElt_0 [of "?z_hge" "?z_hv" "{3, 4, 5}", OF z_Hny])
       have z_Hlf: "((CHOOSE zenon_Vpa:(~((zenon_Vpa \\in ProcSet)=>((a_pchash_primea[zenon_Vpa]) \\in {0, 1, ?z_hv, 3, 4, 5})))) \\in ?z_hiw)" (is "?z_hlf")
       by (rule ssubst [where P="(\<lambda>zenon_Vip. ((CHOOSE zenon_Vpa:(~((zenon_Vpa \\in ProcSet)=>((a_pchash_primea[zenon_Vpa]) \\in {0, 1, ?z_hv, 3, 4, 5})))) \\in zenon_Vip))", OF z_Hkk z_Hfu])
       have z_Hod: "?z_hnt((CHOOSE zenon_Vpa:(~((zenon_Vpa \\in ProcSet)=>((a_pchash_primea[zenon_Vpa]) \\in {0, 1, ?z_hv, 3, 4, 5})))))" (is "_=?z_hoe")
       by (rule zenon_all_0 [of "?z_hnt" "(CHOOSE zenon_Vpa:(~((zenon_Vpa \\in ProcSet)=>((a_pchash_primea[zenon_Vpa]) \\in {0, 1, ?z_hv, 3, 4, 5}))))", OF z_Hno])
       show FALSE
       proof (rule zenon_fapplyexcept [of "(\<lambda>zenon_Vgs. (?z_hge=zenon_Vgs))" "pc" "(CHOOSE x:((x \\in ProcSet)&((((pc[x])=1)&((a_pchash_primea=except(pc, x, ?z_hv))&?z_hch))|((((pc[x])=?z_hv)&((a_flaghash_primea=except(flag, x, TRUE))&((a_pchash_primea=except(pc, x, 3))&?z_hck)))|((((pc[x])=0)&((a_pchash_primea=except(pc, x, 5))&?z_hch))|(((pc[x])=5)&((a_flaghash_primea=except(flag, x, FALSE))&((a_pchash_primea=except(pc, x, 1))&?z_hck))))))))" "?z_hv" "(CHOOSE zenon_Vpa:(~((zenon_Vpa \\in ProcSet)=>((a_pchash_primea[zenon_Vpa]) \\in {0, 1, ?z_hv, 3, 4, 5}))))", OF z_Hod])
        assume z_Hlf:"?z_hlf"
        assume z_Hof:"((CHOOSE x:((x \\in ProcSet)&((((pc[x])=1)&((a_pchash_primea=except(pc, x, ?z_hv))&?z_hch))|((((pc[x])=?z_hv)&((a_flaghash_primea=except(flag, x, TRUE))&((a_pchash_primea=except(pc, x, 3))&?z_hck)))|((((pc[x])=0)&((a_pchash_primea=except(pc, x, 5))&?z_hch))|(((pc[x])=5)&((a_flaghash_primea=except(flag, x, FALSE))&((a_pchash_primea=except(pc, x, 1))&?z_hck))))))))=(CHOOSE zenon_Vpa:(~((zenon_Vpa \\in ProcSet)=>((a_pchash_primea[zenon_Vpa]) \\in {0, 1, ?z_hv, 3, 4, 5})))))" (is "?z_hmz=?z_hfv")
        assume z_Hog:"(?z_hge=?z_hv)"
        show FALSE
        by (rule notE [OF z_Hob z_Hog])
       next
        assume z_Hlf:"?z_hlf"
        assume z_Hoh:"((CHOOSE x:((x \\in ProcSet)&((((pc[x])=1)&((a_pchash_primea=except(pc, x, ?z_hv))&?z_hch))|((((pc[x])=?z_hv)&((a_flaghash_primea=except(flag, x, TRUE))&((a_pchash_primea=except(pc, x, 3))&?z_hck)))|((((pc[x])=0)&((a_pchash_primea=except(pc, x, 5))&?z_hch))|(((pc[x])=5)&((a_flaghash_primea=except(flag, x, FALSE))&((a_pchash_primea=except(pc, x, 1))&?z_hck))))))))~=(CHOOSE zenon_Vpa:(~((zenon_Vpa \\in ProcSet)=>((a_pchash_primea[zenon_Vpa]) \\in {0, 1, ?z_hv, 3, 4, 5})))))" (is "?z_hmz~=?z_hfv")
        assume z_Hgf:"(?z_hge=(pc[?z_hfv]))" (is "_=?z_hgg")
        show FALSE
        by (rule zenon_L4_ [OF z_Hfo z_Hfu z_Hgc z_Hgf])
       next
        assume z_Hlr:"(~?z_hlf)"
        show FALSE
        by (rule notE [OF z_Hlr z_Hlf])
       qed
      qed
     qed
    qed
   qed
  next
   assume z_Hnd:"?z_hnd" (is "?z_hoi|?z_hoj")
   show FALSE
   proof (rule zenon_or [OF z_Hnd])
    assume z_Hoi:"?z_hoi" (is "?z_hok&?z_hol")
    have z_Hol: "?z_hol" (is "?z_hom&?z_hon")
    by (rule zenon_and_1 [OF z_Hoi])
    have z_Hom: "?z_hom" (is "_=?z_hoo")
    by (rule zenon_and_0 [OF z_Hol])
    have z_Hon: "?z_hon" (is "?z_hop&?z_hck")
    by (rule zenon_and_1 [OF z_Hol])
    have z_Hop: "?z_hop" (is "_=?z_hoq")
    by (rule zenon_and_0 [OF z_Hon])
    have z_Hck: "?z_hck"
    by (rule zenon_and_1 [OF z_Hon])
    show FALSE
    proof (rule zenon_notand [OF z_Hc])
     assume z_Heh:"(~?z_hei)"
     have z_Hor: "(flag \\in FuncSet(?z_heg, {TRUE, FALSE}))" (is "?z_hor")
     by (rule subst [where P="(\<lambda>zenon_Vkkv. (flag \\in FuncSet(zenon_Vkkv, {TRUE, FALSE})))", OF z_Ha z_Hf])
     have z_Hox: "(DOMAIN(flag)=?z_heg)" (is "?z_hoy=_")
     by (rule zenon_in_funcset_1 [of "flag" "?z_heg" "{TRUE, FALSE}", OF z_Hor])
     have z_Hoz: "(?z_hoy=ProcSet)"
     by (rule zenon_in_funcset_1 [of "flag" "ProcSet" "{TRUE, FALSE}", OF z_Hf])
     have z_Hkk: "(DOMAIN(pc)=ProcSet)" (is "?z_hiw=_")
     by (rule zenon_in_funcset_1 [of "pc" "ProcSet" "{0, 1, 2, 3, 4, 5}", OF z_Hp])
     have z_Hoz: "(?z_hoy=ProcSet)"
     by (rule zenon_in_funcset_1 [of "flag" "ProcSet" "{TRUE, FALSE}", OF z_Hf])
     have z_Hgp: "(\\A zenon_Vr:((zenon_Vr \\in ProcSet)=>((flag[zenon_Vr]) \\in {TRUE, FALSE})))" (is "\\A x : ?z_hhi(x)")
     by (rule zenon_in_funcset_2 [of "flag" "ProcSet" "{TRUE, FALSE}", OF z_Hf])
     have z_Hpa: "(((isAFcn(a_pchash_primea)<=>isAFcn(?z_hoq))&(DOMAIN(a_pchash_primea)=DOMAIN(?z_hoq)))&(\\A zenon_Vjut:((a_pchash_primea[zenon_Vjut])=(?z_hoq[zenon_Vjut]))))" (is "?z_hpb&?z_hpg")
     by (rule zenon_funequal_0 [of "a_pchash_primea" "?z_hoq", OF z_Hop])
     have z_Hpg: "?z_hpg" (is "\\A x : ?z_hpl(x)")
     by (rule zenon_and_1 [OF z_Hpa])
     have z_Hpm: "(((isAFcn(a_flaghash_primea)<=>isAFcn(?z_hoo))&(DOMAIN(a_flaghash_primea)=DOMAIN(?z_hoo)))&(\\A zenon_Vlut:((a_flaghash_primea[zenon_Vlut])=(?z_hoo[zenon_Vlut]))))" (is "?z_hpn&?z_hpu")
     by (rule zenon_funequal_0 [of "a_flaghash_primea" "?z_hoo", OF z_Hom])
     have z_Hpn: "?z_hpn" (is "?z_hpo&?z_hpr")
     by (rule zenon_and_0 [OF z_Hpm])
     have z_Hpu: "?z_hpu" (is "\\A x : ?z_hpz(x)")
     by (rule zenon_and_1 [OF z_Hpm])
     have z_Hpo: "?z_hpo" (is "?z_hpp<=>?z_hpq")
     by (rule zenon_and_0 [OF z_Hpn])
     show FALSE
     proof (rule zenon_equiv [OF z_Hpo])
      assume z_Hqa:"(~?z_hpp)"
      assume z_Hqb:"(~?z_hpq)"
      show FALSE
      by (rule zenon_notisafcn_except [of "flag" "(CHOOSE x:((x \\in ProcSet)&((((pc[x])=1)&((a_pchash_primea=except(pc, x, 2))&((a_flaghash_primea=flag)&?z_hck)))|((((pc[x])=2)&((a_flaghash_primea=except(flag, x, TRUE))&((a_pchash_primea=except(pc, x, 3))&?z_hck)))|((((pc[x])=0)&((a_pchash_primea=except(pc, x, 5))&((a_flaghash_primea=flag)&?z_hck)))|(((pc[x])=5)&((a_flaghash_primea=except(flag, x, FALSE))&((a_pchash_primea=except(pc, x, 1))&?z_hck))))))))" "TRUE", OF z_Hqb])
     next
      assume z_Hpp:"?z_hpp"
      assume z_Hpq:"?z_hpq"
      show FALSE
      proof (rule zenon_notin_funcset [of "a_flaghash_primea" "ProcSet" "{TRUE, FALSE}", OF z_Heh])
       assume z_Hqa:"(~?z_hpp)"
       show FALSE
       by (rule notE [OF z_Hqa z_Hpp])
      next
       assume z_Hqc:"(DOMAIN(a_flaghash_primea)~=ProcSet)" (is "?z_hps~=_")
       have z_Hqd: "(?z_hps~=?z_heg)"
       by (rule subst [where P="(\<lambda>zenon_Vmkv. (?z_hps~=zenon_Vmkv))", OF z_Ha z_Hqc])
       have z_Hqh: "(DOMAIN(?z_hoo)~=?z_heg)" (is "?z_hpt~=_")
       by (rule subst [where P="(\<lambda>zenon_Vos. (DOMAIN(zenon_Vos)~=?z_heg))", OF z_Hom z_Hqd])
       have z_Hqi: "(?z_hoy~=?z_heg)"
       by (rule zenon_domain_except_0 [of "(\<lambda>zenon_Vns. (zenon_Vns~=?z_heg))" "flag" "(CHOOSE x:((x \\in ProcSet)&((((pc[x])=1)&((a_pchash_primea=except(pc, x, 2))&((a_flaghash_primea=flag)&?z_hck)))|((((pc[x])=2)&((a_flaghash_primea=except(flag, x, TRUE))&((a_pchash_primea=except(pc, x, 3))&?z_hck)))|((((pc[x])=0)&((a_pchash_primea=except(pc, x, 5))&((a_flaghash_primea=flag)&?z_hck)))|(((pc[x])=5)&((a_flaghash_primea=except(flag, x, FALSE))&((a_pchash_primea=except(pc, x, 1))&?z_hck))))))))" "TRUE", OF z_Hqh])
       show FALSE
       by (rule notE [OF z_Hqi z_Hox])
      next
       assume z_Hqj:"(~(\\A zenon_Vhsb:((zenon_Vhsb \\in ProcSet)=>((a_flaghash_primea[zenon_Vhsb]) \\in {TRUE, FALSE}))))" (is "~(\\A x : ?z_hql(x))")
       have z_Hqm: "(\\E zenon_Vhsb:(~((zenon_Vhsb \\in ProcSet)=>((a_flaghash_primea[zenon_Vhsb]) \\in {TRUE, FALSE}))))" (is "\\E x : ?z_hqn(x)")
       by (rule zenon_notallex_0 [of "?z_hql", OF z_Hqj])
       have z_Hqo: "?z_hqn((CHOOSE zenon_Vhsb:(~((zenon_Vhsb \\in ProcSet)=>((a_flaghash_primea[zenon_Vhsb]) \\in {TRUE, FALSE})))))" (is "~(?z_hgv=>?z_hhe)")
       by (rule zenon_ex_choose_0 [of "?z_hqn", OF z_Hqm])
       have z_Hgv: "?z_hgv"
       by (rule zenon_notimply_0 [OF z_Hqo])
       have z_Hhd: "(~?z_hhe)"
       by (rule zenon_notimply_1 [OF z_Hqo])
       have z_Hqp: "((a_flaghash_primea[(CHOOSE zenon_Vhsb:(~((zenon_Vhsb \\in ProcSet)=>((a_flaghash_primea[zenon_Vhsb]) \\in {TRUE, FALSE}))))])~=TRUE)" (is "?z_hhf~=?z_hk")
       by (rule zenon_notin_addElt_0 [of "?z_hhf" "?z_hk" "{FALSE}", OF z_Hhd])
       have z_Hqr: "((CHOOSE zenon_Vhsb:(~((zenon_Vhsb \\in ProcSet)=>((a_flaghash_primea[zenon_Vhsb]) \\in {?z_hk, FALSE})))) \\in ?z_hoy)" (is "?z_hqr")
       by (rule ssubst [where P="(\<lambda>zenon_Vrhs. ((CHOOSE zenon_Vhsb:(~((zenon_Vhsb \\in ProcSet)=>((a_flaghash_primea[zenon_Vhsb]) \\in {?z_hk, FALSE})))) \\in zenon_Vrhs))", OF z_Hoz z_Hgv])
       have z_Hqv: "((CHOOSE zenon_Vhsb:(~((zenon_Vhsb \\in ProcSet)=>((a_flaghash_primea[zenon_Vhsb]) \\in {?z_hk, FALSE})))) \\in ?z_hiw)" (is "?z_hqv")
       by (rule ssubst [where P="(\<lambda>zenon_Vrhs. ((CHOOSE zenon_Vhsb:(~((zenon_Vhsb \\in ProcSet)=>((a_flaghash_primea[zenon_Vhsb]) \\in {?z_hk, FALSE})))) \\in zenon_Vrhs))", OF z_Hkk z_Hgv])
       have z_Hqw: "?z_hpl((CHOOSE zenon_Vhsb:(~((zenon_Vhsb \\in ProcSet)=>((a_flaghash_primea[zenon_Vhsb]) \\in {?z_hk, FALSE})))))" (is "?z_hqx=?z_hqy")
       by (rule zenon_all_0 [of "?z_hpl" "(CHOOSE zenon_Vhsb:(~((zenon_Vhsb \\in ProcSet)=>((a_flaghash_primea[zenon_Vhsb]) \\in {?z_hk, FALSE}))))", OF z_Hpg])
       show FALSE
       proof (rule zenon_fapplyexcept [of "(\<lambda>zenon_Vois. (?z_hqx=zenon_Vois))" "pc" "(CHOOSE x:((x \\in ProcSet)&((((pc[x])=1)&((a_pchash_primea=except(pc, x, 2))&((a_flaghash_primea=flag)&?z_hck)))|((((pc[x])=2)&((a_flaghash_primea=except(flag, x, ?z_hk))&((a_pchash_primea=except(pc, x, 3))&?z_hck)))|((((pc[x])=0)&((a_pchash_primea=except(pc, x, 5))&((a_flaghash_primea=flag)&?z_hck)))|(((pc[x])=5)&((a_flaghash_primea=except(flag, x, FALSE))&((a_pchash_primea=except(pc, x, 1))&?z_hck))))))))" "3" "(CHOOSE zenon_Vhsb:(~((zenon_Vhsb \\in ProcSet)=>((a_flaghash_primea[zenon_Vhsb]) \\in {?z_hk, FALSE}))))", OF z_Hqw])
        assume z_Hqv:"?z_hqv"
        assume z_Hrc:"((CHOOSE x:((x \\in ProcSet)&((((pc[x])=1)&((a_pchash_primea=except(pc, x, 2))&((a_flaghash_primea=flag)&?z_hck)))|((((pc[x])=2)&((a_flaghash_primea=except(flag, x, ?z_hk))&((a_pchash_primea=except(pc, x, 3))&?z_hck)))|((((pc[x])=0)&((a_pchash_primea=except(pc, x, 5))&((a_flaghash_primea=flag)&?z_hck)))|(((pc[x])=5)&((a_flaghash_primea=except(flag, x, FALSE))&((a_pchash_primea=except(pc, x, 1))&?z_hck))))))))=(CHOOSE zenon_Vhsb:(~((zenon_Vhsb \\in ProcSet)=>((a_flaghash_primea[zenon_Vhsb]) \\in {?z_hk, FALSE})))))" (is "?z_hmz=?z_hgw")
        assume z_Hrd:"(?z_hqx=3)" (is "_=?z_hw")
        have z_Hre: "?z_hpz(?z_hgw)" (is "_=?z_hrf")
        by (rule zenon_all_0 [of "?z_hpz" "?z_hgw", OF z_Hpu])
        show FALSE
        proof (rule zenon_fapplyexcept [of "(\<lambda>zenon_Vsis. (?z_hhf=zenon_Vsis))" "flag" "?z_hmz" "?z_hk" "?z_hgw", OF z_Hre])
         assume z_Hqr:"?z_hqr"
         assume z_Hrc:"(?z_hmz=?z_hgw)"
         assume z_Hrj:"(?z_hhf=?z_hk)"
         show FALSE
         by (rule notE [OF z_Hqp z_Hrj])
        next
         assume z_Hqr:"?z_hqr"
         assume z_Hrk:"(?z_hmz~=?z_hgw)"
         assume z_Hhg:"(?z_hhf=(flag[?z_hgw]))" (is "_=?z_hhh")
         show FALSE
         by (rule notE [OF z_Hrk z_Hrc])
        next
         assume z_Hrl:"(~?z_hqr)"
         show FALSE
         by (rule notE [OF z_Hrl z_Hqr])
        qed
       next
        assume z_Hqv:"?z_hqv"
        assume z_Hrk:"((CHOOSE x:((x \\in ProcSet)&((((pc[x])=1)&((a_pchash_primea=except(pc, x, 2))&((a_flaghash_primea=flag)&?z_hck)))|((((pc[x])=2)&((a_flaghash_primea=except(flag, x, ?z_hk))&((a_pchash_primea=except(pc, x, 3))&?z_hck)))|((((pc[x])=0)&((a_pchash_primea=except(pc, x, 5))&((a_flaghash_primea=flag)&?z_hck)))|(((pc[x])=5)&((a_flaghash_primea=except(flag, x, FALSE))&((a_pchash_primea=except(pc, x, 1))&?z_hck))))))))~=(CHOOSE zenon_Vhsb:(~((zenon_Vhsb \\in ProcSet)=>((a_flaghash_primea[zenon_Vhsb]) \\in {?z_hk, FALSE})))))" (is "?z_hmz~=?z_hgw")
        assume z_Hrm:"(?z_hqx=(pc[?z_hgw]))" (is "_=?z_hrn")
        have z_Hre: "?z_hpz(?z_hgw)" (is "_=?z_hrf")
        by (rule zenon_all_0 [of "?z_hpz" "?z_hgw", OF z_Hpu])
        show FALSE
        proof (rule zenon_fapplyexcept [of "(\<lambda>zenon_Vsis. (?z_hhf=zenon_Vsis))" "flag" "?z_hmz" "?z_hk" "?z_hgw", OF z_Hre])
         assume z_Hqr:"?z_hqr"
         assume z_Hrc:"(?z_hmz=?z_hgw)"
         assume z_Hrj:"(?z_hhf=?z_hk)"
         show FALSE
         by (rule notE [OF z_Hrk z_Hrc])
        next
         assume z_Hqr:"?z_hqr"
         assume z_Hrk:"(?z_hmz~=?z_hgw)"
         assume z_Hhg:"(?z_hhf=(flag[?z_hgw]))" (is "_=?z_hhh")
         show FALSE
         by (rule zenon_L5_ [OF z_Hgp z_Hgv z_Hhd z_Hhg])
        next
         assume z_Hrl:"(~?z_hqr)"
         show FALSE
         by (rule notE [OF z_Hrl z_Hqr])
        qed
       next
        assume z_Hro:"(~?z_hqv)"
        show FALSE
        by (rule notE [OF z_Hro z_Hqv])
       qed
      qed
     qed
    next
     assume z_Hkc:"(~?z_hka)" (is "~(?z_hff&?z_hkb)")
     show FALSE
     proof (rule zenon_notand [OF z_Hkc])
      assume z_Hfe:"(~?z_hff)"
      show FALSE
      by (rule zenon_L3_ [OF z_Ha z_Hfe z_Hck z_Hn])
     next
      assume z_Hkd:"(~?z_hkb)"
      have z_Hke: "(pc \\in FuncSet(?z_heg, {0, 1, 2, 3, 4, 5}))" (is "?z_hke")
      by (rule subst [where P="(\<lambda>zenon_Vgkv. (pc \\in FuncSet(zenon_Vgkv, {0, 1, 2, 3, 4, 5})))", OF z_Ha z_Hp])
      have z_Hiv: "(DOMAIN(pc)=?z_heg)" (is "?z_hiw=_")
      by (rule zenon_in_funcset_1 [of "pc" "?z_heg" "{0, 1, 2, 3, 4, 5}", OF z_Hke])
      have z_Hkk: "(?z_hiw=ProcSet)"
      by (rule zenon_in_funcset_1 [of "pc" "ProcSet" "{0, 1, 2, 3, 4, 5}", OF z_Hp])
      have z_Hkk: "(?z_hiw=ProcSet)"
      by (rule zenon_in_funcset_1 [of "pc" "ProcSet" "{0, 1, 2, 3, 4, 5}", OF z_Hp])
      have z_Hfo: "(\\A zenon_Vm:((zenon_Vm \\in ProcSet)=>((pc[zenon_Vm]) \\in {0, 1, 2, 3, 4, 5})))" (is "\\A x : ?z_hgh(x)")
      by (rule zenon_in_funcset_2 [of "pc" "ProcSet" "{0, 1, 2, 3, 4, 5}", OF z_Hp])
      have z_Hpa: "(((isAFcn(a_pchash_primea)<=>isAFcn(?z_hoq))&(DOMAIN(a_pchash_primea)=DOMAIN(?z_hoq)))&(\\A zenon_Vjut:((a_pchash_primea[zenon_Vjut])=(?z_hoq[zenon_Vjut]))))" (is "?z_hpb&?z_hpg")
      by (rule zenon_funequal_0 [of "a_pchash_primea" "?z_hoq", OF z_Hop])
      have z_Hpb: "?z_hpb" (is "?z_hpc&?z_hpe")
      by (rule zenon_and_0 [OF z_Hpa])
      have z_Hpg: "?z_hpg" (is "\\A x : ?z_hpl(x)")
      by (rule zenon_and_1 [OF z_Hpa])
      have z_Hpc: "?z_hpc" (is "?z_hko<=>?z_hpd")
      by (rule zenon_and_0 [OF z_Hpb])
      show FALSE
      proof (rule zenon_equiv [OF z_Hpc])
       assume z_Hkw:"(~?z_hko)"
       assume z_Hrp:"(~?z_hpd)"
       show FALSE
       by (rule zenon_notisafcn_except [of "pc" "(CHOOSE x:((x \\in ProcSet)&((((pc[x])=1)&((a_pchash_primea=except(pc, x, 2))&((a_flaghash_primea=flag)&?z_hck)))|((((pc[x])=2)&((a_flaghash_primea=except(flag, x, TRUE))&((a_pchash_primea=except(pc, x, 3))&?z_hck)))|((((pc[x])=0)&((a_pchash_primea=except(pc, x, 5))&((a_flaghash_primea=flag)&?z_hck)))|(((pc[x])=5)&((a_flaghash_primea=except(flag, x, FALSE))&((a_pchash_primea=except(pc, x, 1))&?z_hck))))))))" "3", OF z_Hrp])
      next
       assume z_Hko:"?z_hko"
       assume z_Hpd:"?z_hpd"
       show FALSE
       proof (rule zenon_notin_funcset [of "a_pchash_primea" "ProcSet" "{0, 1, 2, 3, 4, 5}", OF z_Hkd])
        assume z_Hkw:"(~?z_hko)"
        show FALSE
        by (rule notE [OF z_Hkw z_Hko])
       next
        assume z_His:"(DOMAIN(a_pchash_primea)~=ProcSet)" (is "?z_hit~=_")
        have z_Hix: "(?z_hit~=?z_heg)"
        by (rule subst [where P="(\<lambda>zenon_Vikv. (?z_hit~=zenon_Vikv))", OF z_Ha z_His])
        have z_Hrq: "(DOMAIN(?z_hoq)~=?z_heg)" (is "?z_hpf~=_")
        by (rule subst [where P="(\<lambda>zenon_Vos. (DOMAIN(zenon_Vos)~=?z_heg))", OF z_Hop z_Hix])
        have z_Hjh: "(?z_hiw~=?z_heg)"
        by (rule zenon_domain_except_0 [of "(\<lambda>zenon_Vns. (zenon_Vns~=?z_heg))" "pc" "(CHOOSE x:((x \\in ProcSet)&((((pc[x])=1)&((a_pchash_primea=except(pc, x, 2))&((a_flaghash_primea=flag)&?z_hck)))|((((pc[x])=2)&((a_flaghash_primea=except(flag, x, TRUE))&((a_pchash_primea=except(pc, x, 3))&?z_hck)))|((((pc[x])=0)&((a_pchash_primea=except(pc, x, 5))&((a_flaghash_primea=flag)&?z_hck)))|(((pc[x])=5)&((a_flaghash_primea=except(flag, x, FALSE))&((a_pchash_primea=except(pc, x, 1))&?z_hck))))))))" "3", OF z_Hrq])
        show FALSE
        by (rule notE [OF z_Hjh z_Hiv])
       next
        assume z_Hkx:"(~(\\A zenon_Vpa:((zenon_Vpa \\in ProcSet)=>((a_pchash_primea[zenon_Vpa]) \\in {0, 1, 2, 3, 4, 5}))))" (is "~(\\A x : ?z_hkz(x))")
        have z_Hla: "(\\E zenon_Vpa:(~((zenon_Vpa \\in ProcSet)=>((a_pchash_primea[zenon_Vpa]) \\in {0, 1, 2, 3, 4, 5}))))" (is "\\E x : ?z_hlb(x)")
        by (rule zenon_notallex_0 [of "?z_hkz", OF z_Hkx])
        have z_Hlc: "?z_hlb((CHOOSE zenon_Vpa:(~((zenon_Vpa \\in ProcSet)=>((a_pchash_primea[zenon_Vpa]) \\in {0, 1, 2, 3, 4, 5})))))" (is "~(?z_hfu=>?z_hgd)")
        by (rule zenon_ex_choose_0 [of "?z_hlb", OF z_Hla])
        have z_Hfu: "?z_hfu"
        by (rule zenon_notimply_0 [OF z_Hlc])
        have z_Hgc: "(~?z_hgd)"
        by (rule zenon_notimply_1 [OF z_Hlc])
        have z_Hnw: "(~((a_pchash_primea[(CHOOSE zenon_Vpa:(~((zenon_Vpa \\in ProcSet)=>((a_pchash_primea[zenon_Vpa]) \\in {0, 1, 2, 3, 4, 5}))))]) \\in {1, 2, 3, 4, 5}))" (is "~?z_hnx")
        by (rule zenon_notin_addElt_1 [of "(a_pchash_primea[(CHOOSE zenon_Vpa:(~((zenon_Vpa \\in ProcSet)=>((a_pchash_primea[zenon_Vpa]) \\in {0, 1, 2, 3, 4, 5}))))])" "0" "{1, 2, 3, 4, 5}", OF z_Hgc])
        have z_Hny: "(~((a_pchash_primea[(CHOOSE zenon_Vpa:(~((zenon_Vpa \\in ProcSet)=>((a_pchash_primea[zenon_Vpa]) \\in {0, 1, 2, 3, 4, 5}))))]) \\in {2, 3, 4, 5}))" (is "~?z_hnz")
        by (rule zenon_notin_addElt_1 [of "(a_pchash_primea[(CHOOSE zenon_Vpa:(~((zenon_Vpa \\in ProcSet)=>((a_pchash_primea[zenon_Vpa]) \\in {0, 1, 2, 3, 4, 5}))))])" "1" "{2, 3, 4, 5}", OF z_Hnw])
        have z_Hrr: "(~((a_pchash_primea[(CHOOSE zenon_Vpa:(~((zenon_Vpa \\in ProcSet)=>((a_pchash_primea[zenon_Vpa]) \\in {0, 1, 2, 3, 4, 5}))))]) \\in {3, 4, 5}))" (is "~?z_hrs")
        by (rule zenon_notin_addElt_1 [of "(a_pchash_primea[(CHOOSE zenon_Vpa:(~((zenon_Vpa \\in ProcSet)=>((a_pchash_primea[zenon_Vpa]) \\in {0, 1, 2, 3, 4, 5}))))])" "2" "{3, 4, 5}", OF z_Hny])
        have z_Hrt: "((a_pchash_primea[(CHOOSE zenon_Vpa:(~((zenon_Vpa \\in ProcSet)=>((a_pchash_primea[zenon_Vpa]) \\in {0, 1, 2, 3, 4, 5}))))])~=3)" (is "?z_hge~=?z_hw")
        by (rule zenon_notin_addElt_0 [of "?z_hge" "?z_hw" "{4, 5}", OF z_Hrr])
        have z_Hlf: "((CHOOSE zenon_Vpa:(~((zenon_Vpa \\in ProcSet)=>((a_pchash_primea[zenon_Vpa]) \\in {0, 1, 2, ?z_hw, 4, 5})))) \\in ?z_hiw)" (is "?z_hlf")
        by (rule ssubst [where P="(\<lambda>zenon_Vip. ((CHOOSE zenon_Vpa:(~((zenon_Vpa \\in ProcSet)=>((a_pchash_primea[zenon_Vpa]) \\in {0, 1, 2, ?z_hw, 4, 5})))) \\in zenon_Vip))", OF z_Hkk z_Hfu])
        have z_Hrv: "?z_hpl((CHOOSE zenon_Vpa:(~((zenon_Vpa \\in ProcSet)=>((a_pchash_primea[zenon_Vpa]) \\in {0, 1, 2, ?z_hw, 4, 5})))))" (is "_=?z_hrw")
        by (rule zenon_all_0 [of "?z_hpl" "(CHOOSE zenon_Vpa:(~((zenon_Vpa \\in ProcSet)=>((a_pchash_primea[zenon_Vpa]) \\in {0, 1, 2, ?z_hw, 4, 5}))))", OF z_Hpg])
        show FALSE
        proof (rule zenon_fapplyexcept [of "(\<lambda>zenon_Vgs. (?z_hge=zenon_Vgs))" "pc" "(CHOOSE x:((x \\in ProcSet)&((((pc[x])=1)&((a_pchash_primea=except(pc, x, 2))&((a_flaghash_primea=flag)&?z_hck)))|((((pc[x])=2)&((a_flaghash_primea=except(flag, x, TRUE))&((a_pchash_primea=except(pc, x, ?z_hw))&?z_hck)))|((((pc[x])=0)&((a_pchash_primea=except(pc, x, 5))&((a_flaghash_primea=flag)&?z_hck)))|(((pc[x])=5)&((a_flaghash_primea=except(flag, x, FALSE))&((a_pchash_primea=except(pc, x, 1))&?z_hck))))))))" "?z_hw" "(CHOOSE zenon_Vpa:(~((zenon_Vpa \\in ProcSet)=>((a_pchash_primea[zenon_Vpa]) \\in {0, 1, 2, ?z_hw, 4, 5}))))", OF z_Hrv])
         assume z_Hlf:"?z_hlf"
         assume z_Hof:"((CHOOSE x:((x \\in ProcSet)&((((pc[x])=1)&((a_pchash_primea=except(pc, x, 2))&((a_flaghash_primea=flag)&?z_hck)))|((((pc[x])=2)&((a_flaghash_primea=except(flag, x, TRUE))&((a_pchash_primea=except(pc, x, ?z_hw))&?z_hck)))|((((pc[x])=0)&((a_pchash_primea=except(pc, x, 5))&((a_flaghash_primea=flag)&?z_hck)))|(((pc[x])=5)&((a_flaghash_primea=except(flag, x, FALSE))&((a_pchash_primea=except(pc, x, 1))&?z_hck))))))))=(CHOOSE zenon_Vpa:(~((zenon_Vpa \\in ProcSet)=>((a_pchash_primea[zenon_Vpa]) \\in {0, 1, 2, ?z_hw, 4, 5})))))" (is "?z_hmz=?z_hfv")
         assume z_Hrx:"(?z_hge=?z_hw)"
         show FALSE
         by (rule notE [OF z_Hrt z_Hrx])
        next
         assume z_Hlf:"?z_hlf"
         assume z_Hoh:"((CHOOSE x:((x \\in ProcSet)&((((pc[x])=1)&((a_pchash_primea=except(pc, x, 2))&((a_flaghash_primea=flag)&?z_hck)))|((((pc[x])=2)&((a_flaghash_primea=except(flag, x, TRUE))&((a_pchash_primea=except(pc, x, ?z_hw))&?z_hck)))|((((pc[x])=0)&((a_pchash_primea=except(pc, x, 5))&((a_flaghash_primea=flag)&?z_hck)))|(((pc[x])=5)&((a_flaghash_primea=except(flag, x, FALSE))&((a_pchash_primea=except(pc, x, 1))&?z_hck))))))))~=(CHOOSE zenon_Vpa:(~((zenon_Vpa \\in ProcSet)=>((a_pchash_primea[zenon_Vpa]) \\in {0, 1, 2, ?z_hw, 4, 5})))))" (is "?z_hmz~=?z_hfv")
         assume z_Hgf:"(?z_hge=(pc[?z_hfv]))" (is "_=?z_hgg")
         show FALSE
         by (rule zenon_L4_ [OF z_Hfo z_Hfu z_Hgc z_Hgf])
        next
         assume z_Hlr:"(~?z_hlf)"
         show FALSE
         by (rule notE [OF z_Hlr z_Hlf])
        qed
       qed
      qed
     qed
    qed
   next
    assume z_Hoj:"?z_hoj" (is "?z_hry|?z_hrz")
    show FALSE
    proof (rule zenon_or [OF z_Hoj])
     assume z_Hry:"?z_hry" (is "?z_hsa&?z_hsb")
     have z_Hsb: "?z_hsb" (is "?z_hsc&?z_hch")
     by (rule zenon_and_1 [OF z_Hry])
     have z_Hsc: "?z_hsc" (is "_=?z_hsd")
     by (rule zenon_and_0 [OF z_Hsb])
     have z_Hch: "?z_hch" (is "?z_hci&?z_hck")
     by (rule zenon_and_1 [OF z_Hsb])
     have z_Hci: "?z_hci"
     by (rule zenon_and_0 [OF z_Hch])
     have z_Hck: "?z_hck"
     by (rule zenon_and_1 [OF z_Hch])
     show FALSE
     proof (rule zenon_notand [OF z_Hc])
      assume z_Heh:"(~?z_hei)"
      show FALSE
      by (rule zenon_L1_ [OF z_Heh z_Hf z_Hci])
     next
      assume z_Hkc:"(~?z_hka)" (is "~(?z_hff&?z_hkb)")
      show FALSE
      proof (rule zenon_notand [OF z_Hkc])
       assume z_Hfe:"(~?z_hff)"
       show FALSE
       by (rule zenon_L3_ [OF z_Ha z_Hfe z_Hck z_Hn])
      next
       assume z_Hkd:"(~?z_hkb)"
       have z_Hke: "(pc \\in FuncSet(?z_heg, {0, 1, 2, 3, 4, 5}))" (is "?z_hke")
       by (rule subst [where P="(\<lambda>zenon_Vgkv. (pc \\in FuncSet(zenon_Vgkv, {0, 1, 2, 3, 4, 5})))", OF z_Ha z_Hp])
       have z_Hiv: "(DOMAIN(pc)=?z_heg)" (is "?z_hiw=_")
       by (rule zenon_in_funcset_1 [of "pc" "?z_heg" "{0, 1, 2, 3, 4, 5}", OF z_Hke])
       have z_Hkk: "(?z_hiw=ProcSet)"
       by (rule zenon_in_funcset_1 [of "pc" "ProcSet" "{0, 1, 2, 3, 4, 5}", OF z_Hp])
       have z_Hkk: "(?z_hiw=ProcSet)"
       by (rule zenon_in_funcset_1 [of "pc" "ProcSet" "{0, 1, 2, 3, 4, 5}", OF z_Hp])
       have z_Hfo: "(\\A zenon_Vm:((zenon_Vm \\in ProcSet)=>((pc[zenon_Vm]) \\in {0, 1, 2, 3, 4, 5})))" (is "\\A x : ?z_hgh(x)")
       by (rule zenon_in_funcset_2 [of "pc" "ProcSet" "{0, 1, 2, 3, 4, 5}", OF z_Hp])
       have z_Hse: "(((isAFcn(a_pchash_primea)<=>isAFcn(?z_hsd))&(DOMAIN(a_pchash_primea)=DOMAIN(?z_hsd)))&(\\A zenon_Vqzs:((a_pchash_primea[zenon_Vqzs])=(?z_hsd[zenon_Vqzs]))))" (is "?z_hsf&?z_hsk")
       by (rule zenon_funequal_0 [of "a_pchash_primea" "?z_hsd", OF z_Hsc])
       have z_Hsf: "?z_hsf" (is "?z_hsg&?z_hsi")
       by (rule zenon_and_0 [OF z_Hse])
       have z_Hsk: "?z_hsk" (is "\\A x : ?z_hsp(x)")
       by (rule zenon_and_1 [OF z_Hse])
       have z_Hsg: "?z_hsg" (is "?z_hko<=>?z_hsh")
       by (rule zenon_and_0 [OF z_Hsf])
       show FALSE
       proof (rule zenon_equiv [OF z_Hsg])
        assume z_Hkw:"(~?z_hko)"
        assume z_Hsq:"(~?z_hsh)"
        show FALSE
        by (rule zenon_notisafcn_except [of "pc" "(CHOOSE x:((x \\in ProcSet)&((((pc[x])=1)&((a_pchash_primea=except(pc, x, 2))&?z_hch))|((((pc[x])=2)&((a_flaghash_primea=except(flag, x, TRUE))&((a_pchash_primea=except(pc, x, 3))&?z_hck)))|((((pc[x])=0)&((a_pchash_primea=except(pc, x, 5))&?z_hch))|(((pc[x])=5)&((a_flaghash_primea=except(flag, x, FALSE))&((a_pchash_primea=except(pc, x, 1))&?z_hck))))))))" "5", OF z_Hsq])
       next
        assume z_Hko:"?z_hko"
        assume z_Hsh:"?z_hsh"
        show FALSE
        proof (rule zenon_notin_funcset [of "a_pchash_primea" "ProcSet" "{0, 1, 2, 3, 4, 5}", OF z_Hkd])
         assume z_Hkw:"(~?z_hko)"
         show FALSE
         by (rule notE [OF z_Hkw z_Hko])
        next
         assume z_His:"(DOMAIN(a_pchash_primea)~=ProcSet)" (is "?z_hit~=_")
         have z_Hix: "(?z_hit~=?z_heg)"
         by (rule subst [where P="(\<lambda>zenon_Vikv. (?z_hit~=zenon_Vikv))", OF z_Ha z_His])
         have z_Hsr: "(DOMAIN(?z_hsd)~=?z_heg)" (is "?z_hsj~=_")
         by (rule subst [where P="(\<lambda>zenon_Vos. (DOMAIN(zenon_Vos)~=?z_heg))", OF z_Hsc z_Hix])
         have z_Hjh: "(?z_hiw~=?z_heg)"
         by (rule zenon_domain_except_0 [of "(\<lambda>zenon_Vns. (zenon_Vns~=?z_heg))" "pc" "(CHOOSE x:((x \\in ProcSet)&((((pc[x])=1)&((a_pchash_primea=except(pc, x, 2))&?z_hch))|((((pc[x])=2)&((a_flaghash_primea=except(flag, x, TRUE))&((a_pchash_primea=except(pc, x, 3))&?z_hck)))|((((pc[x])=0)&((a_pchash_primea=except(pc, x, 5))&?z_hch))|(((pc[x])=5)&((a_flaghash_primea=except(flag, x, FALSE))&((a_pchash_primea=except(pc, x, 1))&?z_hck))))))))" "5", OF z_Hsr])
         show FALSE
         by (rule notE [OF z_Hjh z_Hiv])
        next
         assume z_Hkx:"(~(\\A zenon_Vpa:((zenon_Vpa \\in ProcSet)=>((a_pchash_primea[zenon_Vpa]) \\in {0, 1, 2, 3, 4, 5}))))" (is "~(\\A x : ?z_hkz(x))")
         have z_Hla: "(\\E zenon_Vpa:(~((zenon_Vpa \\in ProcSet)=>((a_pchash_primea[zenon_Vpa]) \\in {0, 1, 2, 3, 4, 5}))))" (is "\\E x : ?z_hlb(x)")
         by (rule zenon_notallex_0 [of "?z_hkz", OF z_Hkx])
         have z_Hlc: "?z_hlb((CHOOSE zenon_Vpa:(~((zenon_Vpa \\in ProcSet)=>((a_pchash_primea[zenon_Vpa]) \\in {0, 1, 2, 3, 4, 5})))))" (is "~(?z_hfu=>?z_hgd)")
         by (rule zenon_ex_choose_0 [of "?z_hlb", OF z_Hla])
         have z_Hfu: "?z_hfu"
         by (rule zenon_notimply_0 [OF z_Hlc])
         have z_Hgc: "(~?z_hgd)"
         by (rule zenon_notimply_1 [OF z_Hlc])
         have z_Hnw: "(~((a_pchash_primea[(CHOOSE zenon_Vpa:(~((zenon_Vpa \\in ProcSet)=>((a_pchash_primea[zenon_Vpa]) \\in {0, 1, 2, 3, 4, 5}))))]) \\in {1, 2, 3, 4, 5}))" (is "~?z_hnx")
         by (rule zenon_notin_addElt_1 [of "(a_pchash_primea[(CHOOSE zenon_Vpa:(~((zenon_Vpa \\in ProcSet)=>((a_pchash_primea[zenon_Vpa]) \\in {0, 1, 2, 3, 4, 5}))))])" "0" "{1, 2, 3, 4, 5}", OF z_Hgc])
         have z_Hny: "(~((a_pchash_primea[(CHOOSE zenon_Vpa:(~((zenon_Vpa \\in ProcSet)=>((a_pchash_primea[zenon_Vpa]) \\in {0, 1, 2, 3, 4, 5}))))]) \\in {2, 3, 4, 5}))" (is "~?z_hnz")
         by (rule zenon_notin_addElt_1 [of "(a_pchash_primea[(CHOOSE zenon_Vpa:(~((zenon_Vpa \\in ProcSet)=>((a_pchash_primea[zenon_Vpa]) \\in {0, 1, 2, 3, 4, 5}))))])" "1" "{2, 3, 4, 5}", OF z_Hnw])
         have z_Hrr: "(~((a_pchash_primea[(CHOOSE zenon_Vpa:(~((zenon_Vpa \\in ProcSet)=>((a_pchash_primea[zenon_Vpa]) \\in {0, 1, 2, 3, 4, 5}))))]) \\in {3, 4, 5}))" (is "~?z_hrs")
         by (rule zenon_notin_addElt_1 [of "(a_pchash_primea[(CHOOSE zenon_Vpa:(~((zenon_Vpa \\in ProcSet)=>((a_pchash_primea[zenon_Vpa]) \\in {0, 1, 2, 3, 4, 5}))))])" "2" "{3, 4, 5}", OF z_Hny])
         have z_Hss: "(~((a_pchash_primea[(CHOOSE zenon_Vpa:(~((zenon_Vpa \\in ProcSet)=>((a_pchash_primea[zenon_Vpa]) \\in {0, 1, 2, 3, 4, 5}))))]) \\in {4, 5}))" (is "~?z_hst")
         by (rule zenon_notin_addElt_1 [of "(a_pchash_primea[(CHOOSE zenon_Vpa:(~((zenon_Vpa \\in ProcSet)=>((a_pchash_primea[zenon_Vpa]) \\in {0, 1, 2, 3, 4, 5}))))])" "3" "{4, 5}", OF z_Hrr])
         have z_Hsu: "(~((a_pchash_primea[(CHOOSE zenon_Vpa:(~((zenon_Vpa \\in ProcSet)=>((a_pchash_primea[zenon_Vpa]) \\in {0, 1, 2, 3, 4, 5}))))]) \\in {5}))" (is "~?z_hsv")
         by (rule zenon_notin_addElt_1 [of "(a_pchash_primea[(CHOOSE zenon_Vpa:(~((zenon_Vpa \\in ProcSet)=>((a_pchash_primea[zenon_Vpa]) \\in {0, 1, 2, 3, 4, 5}))))])" "4" "{5}", OF z_Hss])
         have z_Hsx: "((a_pchash_primea[(CHOOSE zenon_Vpa:(~((zenon_Vpa \\in ProcSet)=>((a_pchash_primea[zenon_Vpa]) \\in {0, 1, 2, 3, 4, 5}))))])~=5)" (is "?z_hge~=?z_hy")
         by (rule zenon_notin_addElt_0 [of "?z_hge" "?z_hy" "{}", OF z_Hsu])
         have z_Hlf: "((CHOOSE zenon_Vpa:(~((zenon_Vpa \\in ProcSet)=>((a_pchash_primea[zenon_Vpa]) \\in {0, 1, 2, 3, 4, ?z_hy})))) \\in ?z_hiw)" (is "?z_hlf")
         by (rule ssubst [where P="(\<lambda>zenon_Vip. ((CHOOSE zenon_Vpa:(~((zenon_Vpa \\in ProcSet)=>((a_pchash_primea[zenon_Vpa]) \\in {0, 1, 2, 3, 4, ?z_hy})))) \\in zenon_Vip))", OF z_Hkk z_Hfu])
         have z_Hsy: "?z_hsp((CHOOSE zenon_Vpa:(~((zenon_Vpa \\in ProcSet)=>((a_pchash_primea[zenon_Vpa]) \\in {0, 1, 2, 3, 4, ?z_hy})))))" (is "_=?z_hsz")
         by (rule zenon_all_0 [of "?z_hsp" "(CHOOSE zenon_Vpa:(~((zenon_Vpa \\in ProcSet)=>((a_pchash_primea[zenon_Vpa]) \\in {0, 1, 2, 3, 4, ?z_hy}))))", OF z_Hsk])
         show FALSE
         proof (rule zenon_fapplyexcept [of "(\<lambda>zenon_Vgs. (?z_hge=zenon_Vgs))" "pc" "(CHOOSE x:((x \\in ProcSet)&((((pc[x])=1)&((a_pchash_primea=except(pc, x, 2))&?z_hch))|((((pc[x])=2)&((a_flaghash_primea=except(flag, x, TRUE))&((a_pchash_primea=except(pc, x, 3))&?z_hck)))|((((pc[x])=0)&((a_pchash_primea=except(pc, x, ?z_hy))&?z_hch))|(((pc[x])=?z_hy)&((a_flaghash_primea=except(flag, x, FALSE))&((a_pchash_primea=except(pc, x, 1))&?z_hck))))))))" "?z_hy" "(CHOOSE zenon_Vpa:(~((zenon_Vpa \\in ProcSet)=>((a_pchash_primea[zenon_Vpa]) \\in {0, 1, 2, 3, 4, ?z_hy}))))", OF z_Hsy])
          assume z_Hlf:"?z_hlf"
          assume z_Hof:"((CHOOSE x:((x \\in ProcSet)&((((pc[x])=1)&((a_pchash_primea=except(pc, x, 2))&?z_hch))|((((pc[x])=2)&((a_flaghash_primea=except(flag, x, TRUE))&((a_pchash_primea=except(pc, x, 3))&?z_hck)))|((((pc[x])=0)&((a_pchash_primea=except(pc, x, ?z_hy))&?z_hch))|(((pc[x])=?z_hy)&((a_flaghash_primea=except(flag, x, FALSE))&((a_pchash_primea=except(pc, x, 1))&?z_hck))))))))=(CHOOSE zenon_Vpa:(~((zenon_Vpa \\in ProcSet)=>((a_pchash_primea[zenon_Vpa]) \\in {0, 1, 2, 3, 4, ?z_hy})))))" (is "?z_hmz=?z_hfv")
          assume z_Hta:"(?z_hge=?z_hy)"
          show FALSE
          by (rule notE [OF z_Hsx z_Hta])
         next
          assume z_Hlf:"?z_hlf"
          assume z_Hoh:"((CHOOSE x:((x \\in ProcSet)&((((pc[x])=1)&((a_pchash_primea=except(pc, x, 2))&?z_hch))|((((pc[x])=2)&((a_flaghash_primea=except(flag, x, TRUE))&((a_pchash_primea=except(pc, x, 3))&?z_hck)))|((((pc[x])=0)&((a_pchash_primea=except(pc, x, ?z_hy))&?z_hch))|(((pc[x])=?z_hy)&((a_flaghash_primea=except(flag, x, FALSE))&((a_pchash_primea=except(pc, x, 1))&?z_hck))))))))~=(CHOOSE zenon_Vpa:(~((zenon_Vpa \\in ProcSet)=>((a_pchash_primea[zenon_Vpa]) \\in {0, 1, 2, 3, 4, ?z_hy})))))" (is "?z_hmz~=?z_hfv")
          assume z_Hgf:"(?z_hge=(pc[?z_hfv]))" (is "_=?z_hgg")
          show FALSE
          by (rule zenon_L4_ [OF z_Hfo z_Hfu z_Hgc z_Hgf])
         next
          assume z_Hlr:"(~?z_hlf)"
          show FALSE
          by (rule notE [OF z_Hlr z_Hlf])
         qed
        qed
       qed
      qed
     qed
    next
     assume z_Hrz:"?z_hrz" (is "?z_htb&?z_htc")
     have z_Htc: "?z_htc" (is "?z_htd&?z_hte")
     by (rule zenon_and_1 [OF z_Hrz])
     have z_Htd: "?z_htd" (is "_=?z_htf")
     by (rule zenon_and_0 [OF z_Htc])
     have z_Hte: "?z_hte" (is "?z_htg&?z_hck")
     by (rule zenon_and_1 [OF z_Htc])
     have z_Htg: "?z_htg" (is "_=?z_hth")
     by (rule zenon_and_0 [OF z_Hte])
     have z_Hck: "?z_hck"
     by (rule zenon_and_1 [OF z_Hte])
     show FALSE
     proof (rule zenon_notand [OF z_Hc])
      assume z_Heh:"(~?z_hei)"
      have z_Hor: "(flag \\in FuncSet(?z_heg, {TRUE, FALSE}))" (is "?z_hor")
      by (rule subst [where P="(\<lambda>zenon_Vkkv. (flag \\in FuncSet(zenon_Vkkv, {TRUE, FALSE})))", OF z_Ha z_Hf])
      have z_Hox: "(DOMAIN(flag)=?z_heg)" (is "?z_hoy=_")
      by (rule zenon_in_funcset_1 [of "flag" "?z_heg" "{TRUE, FALSE}", OF z_Hor])
      have z_Hoz: "(?z_hoy=ProcSet)"
      by (rule zenon_in_funcset_1 [of "flag" "ProcSet" "{TRUE, FALSE}", OF z_Hf])
      have z_Hkk: "(DOMAIN(pc)=ProcSet)" (is "?z_hiw=_")
      by (rule zenon_in_funcset_1 [of "pc" "ProcSet" "{0, 1, 2, 3, 4, 5}", OF z_Hp])
      have z_Hoz: "(?z_hoy=ProcSet)"
      by (rule zenon_in_funcset_1 [of "flag" "ProcSet" "{TRUE, FALSE}", OF z_Hf])
      have z_Hgp: "(\\A zenon_Vr:((zenon_Vr \\in ProcSet)=>((flag[zenon_Vr]) \\in {TRUE, FALSE})))" (is "\\A x : ?z_hhi(x)")
      by (rule zenon_in_funcset_2 [of "flag" "ProcSet" "{TRUE, FALSE}", OF z_Hf])
      have z_Hti: "(((isAFcn(a_pchash_primea)<=>isAFcn(?z_hth))&(DOMAIN(a_pchash_primea)=DOMAIN(?z_hth)))&(\\A zenon_Vqxq:((a_pchash_primea[zenon_Vqxq])=(?z_hth[zenon_Vqxq]))))" (is "?z_htj&?z_hto")
      by (rule zenon_funequal_0 [of "a_pchash_primea" "?z_hth", OF z_Htg])
      have z_Hto: "?z_hto" (is "\\A x : ?z_htt(x)")
      by (rule zenon_and_1 [OF z_Hti])
      have z_Htu: "(((isAFcn(a_flaghash_primea)<=>isAFcn(?z_htf))&(DOMAIN(a_flaghash_primea)=DOMAIN(?z_htf)))&(\\A zenon_Vsxq:((a_flaghash_primea[zenon_Vsxq])=(?z_htf[zenon_Vsxq]))))" (is "?z_htv&?z_hua")
      by (rule zenon_funequal_0 [of "a_flaghash_primea" "?z_htf", OF z_Htd])
      have z_Htv: "?z_htv" (is "?z_htw&?z_hty")
      by (rule zenon_and_0 [OF z_Htu])
      have z_Hua: "?z_hua" (is "\\A x : ?z_huf(x)")
      by (rule zenon_and_1 [OF z_Htu])
      have z_Htw: "?z_htw" (is "?z_hpp<=>?z_htx")
      by (rule zenon_and_0 [OF z_Htv])
      show FALSE
      proof (rule zenon_equiv [OF z_Htw])
       assume z_Hqa:"(~?z_hpp)"
       assume z_Hug:"(~?z_htx)"
       show FALSE
       by (rule zenon_notisafcn_except [of "flag" "(CHOOSE x:((x \\in ProcSet)&((((pc[x])=1)&((a_pchash_primea=except(pc, x, 2))&((a_flaghash_primea=flag)&?z_hck)))|((((pc[x])=2)&((a_flaghash_primea=except(flag, x, TRUE))&((a_pchash_primea=except(pc, x, 3))&?z_hck)))|((((pc[x])=0)&((a_pchash_primea=except(pc, x, 5))&((a_flaghash_primea=flag)&?z_hck)))|(((pc[x])=5)&((a_flaghash_primea=except(flag, x, FALSE))&((a_pchash_primea=except(pc, x, 1))&?z_hck))))))))" "FALSE", OF z_Hug])
      next
       assume z_Hpp:"?z_hpp"
       assume z_Htx:"?z_htx"
       show FALSE
       proof (rule zenon_notin_funcset [of "a_flaghash_primea" "ProcSet" "{TRUE, FALSE}", OF z_Heh])
        assume z_Hqa:"(~?z_hpp)"
        show FALSE
        by (rule notE [OF z_Hqa z_Hpp])
       next
        assume z_Hqc:"(DOMAIN(a_flaghash_primea)~=ProcSet)" (is "?z_hps~=_")
        have z_Hqd: "(?z_hps~=?z_heg)"
        by (rule subst [where P="(\<lambda>zenon_Vmkv. (?z_hps~=zenon_Vmkv))", OF z_Ha z_Hqc])
        have z_Huh: "(DOMAIN(?z_htf)~=?z_heg)" (is "?z_htz~=_")
        by (rule subst [where P="(\<lambda>zenon_Vos. (DOMAIN(zenon_Vos)~=?z_heg))", OF z_Htd z_Hqd])
        have z_Hqi: "(?z_hoy~=?z_heg)"
        by (rule zenon_domain_except_0 [of "(\<lambda>zenon_Vns. (zenon_Vns~=?z_heg))" "flag" "(CHOOSE x:((x \\in ProcSet)&((((pc[x])=1)&((a_pchash_primea=except(pc, x, 2))&((a_flaghash_primea=flag)&?z_hck)))|((((pc[x])=2)&((a_flaghash_primea=except(flag, x, TRUE))&((a_pchash_primea=except(pc, x, 3))&?z_hck)))|((((pc[x])=0)&((a_pchash_primea=except(pc, x, 5))&((a_flaghash_primea=flag)&?z_hck)))|(((pc[x])=5)&((a_flaghash_primea=except(flag, x, FALSE))&((a_pchash_primea=except(pc, x, 1))&?z_hck))))))))" "FALSE", OF z_Huh])
        show FALSE
        by (rule notE [OF z_Hqi z_Hox])
       next
        assume z_Hqj:"(~(\\A zenon_Vhsb:((zenon_Vhsb \\in ProcSet)=>((a_flaghash_primea[zenon_Vhsb]) \\in {TRUE, FALSE}))))" (is "~(\\A x : ?z_hql(x))")
        have z_Hqm: "(\\E zenon_Vhsb:(~((zenon_Vhsb \\in ProcSet)=>((a_flaghash_primea[zenon_Vhsb]) \\in {TRUE, FALSE}))))" (is "\\E x : ?z_hqn(x)")
        by (rule zenon_notallex_0 [of "?z_hql", OF z_Hqj])
        have z_Hqo: "?z_hqn((CHOOSE zenon_Vhsb:(~((zenon_Vhsb \\in ProcSet)=>((a_flaghash_primea[zenon_Vhsb]) \\in {TRUE, FALSE})))))" (is "~(?z_hgv=>?z_hhe)")
        by (rule zenon_ex_choose_0 [of "?z_hqn", OF z_Hqm])
        have z_Hgv: "?z_hgv"
        by (rule zenon_notimply_0 [OF z_Hqo])
        have z_Hhd: "(~?z_hhe)"
        by (rule zenon_notimply_1 [OF z_Hqo])
        have z_Hui: "(~((a_flaghash_primea[(CHOOSE zenon_Vhsb:(~((zenon_Vhsb \\in ProcSet)=>((a_flaghash_primea[zenon_Vhsb]) \\in {TRUE, FALSE}))))]) \\in {FALSE}))" (is "~?z_huj")
        by (rule zenon_notin_addElt_1 [of "(a_flaghash_primea[(CHOOSE zenon_Vhsb:(~((zenon_Vhsb \\in ProcSet)=>((a_flaghash_primea[zenon_Vhsb]) \\in {TRUE, FALSE}))))])" "TRUE" "{FALSE}", OF z_Hhd])
        have z_Huk: "((a_flaghash_primea[(CHOOSE zenon_Vhsb:(~((zenon_Vhsb \\in ProcSet)=>((a_flaghash_primea[zenon_Vhsb]) \\in {TRUE, FALSE}))))])~=FALSE)" (is "?z_hhf~=?z_hl")
        by (rule zenon_notin_addElt_0 [of "?z_hhf" "?z_hl" "{}", OF z_Hui])
        have z_Hqr: "((CHOOSE zenon_Vhsb:(~((zenon_Vhsb \\in ProcSet)=>((a_flaghash_primea[zenon_Vhsb]) \\in {TRUE, ?z_hl})))) \\in ?z_hoy)" (is "?z_hqr")
        by (rule ssubst [where P="(\<lambda>zenon_Vrhs. ((CHOOSE zenon_Vhsb:(~((zenon_Vhsb \\in ProcSet)=>((a_flaghash_primea[zenon_Vhsb]) \\in {TRUE, ?z_hl})))) \\in zenon_Vrhs))", OF z_Hoz z_Hgv])
        have z_Hqv: "((CHOOSE zenon_Vhsb:(~((zenon_Vhsb \\in ProcSet)=>((a_flaghash_primea[zenon_Vhsb]) \\in {TRUE, ?z_hl})))) \\in ?z_hiw)" (is "?z_hqv")
        by (rule ssubst [where P="(\<lambda>zenon_Vrhs. ((CHOOSE zenon_Vhsb:(~((zenon_Vhsb \\in ProcSet)=>((a_flaghash_primea[zenon_Vhsb]) \\in {TRUE, ?z_hl})))) \\in zenon_Vrhs))", OF z_Hkk z_Hgv])
        have z_Hul: "?z_htt((CHOOSE zenon_Vhsb:(~((zenon_Vhsb \\in ProcSet)=>((a_flaghash_primea[zenon_Vhsb]) \\in {TRUE, ?z_hl})))))" (is "?z_hqx=?z_hum")
        by (rule zenon_all_0 [of "?z_htt" "(CHOOSE zenon_Vhsb:(~((zenon_Vhsb \\in ProcSet)=>((a_flaghash_primea[zenon_Vhsb]) \\in {TRUE, ?z_hl}))))", OF z_Hto])
        show FALSE
        proof (rule zenon_fapplyexcept [of "(\<lambda>zenon_Vois. (?z_hqx=zenon_Vois))" "pc" "(CHOOSE x:((x \\in ProcSet)&((((pc[x])=1)&((a_pchash_primea=except(pc, x, 2))&((a_flaghash_primea=flag)&?z_hck)))|((((pc[x])=2)&((a_flaghash_primea=except(flag, x, TRUE))&((a_pchash_primea=except(pc, x, 3))&?z_hck)))|((((pc[x])=0)&((a_pchash_primea=except(pc, x, 5))&((a_flaghash_primea=flag)&?z_hck)))|(((pc[x])=5)&((a_flaghash_primea=except(flag, x, ?z_hl))&((a_pchash_primea=except(pc, x, 1))&?z_hck))))))))" "1" "(CHOOSE zenon_Vhsb:(~((zenon_Vhsb \\in ProcSet)=>((a_flaghash_primea[zenon_Vhsb]) \\in {TRUE, ?z_hl}))))", OF z_Hul])
         assume z_Hqv:"?z_hqv"
         assume z_Hrc:"((CHOOSE x:((x \\in ProcSet)&((((pc[x])=1)&((a_pchash_primea=except(pc, x, 2))&((a_flaghash_primea=flag)&?z_hck)))|((((pc[x])=2)&((a_flaghash_primea=except(flag, x, TRUE))&((a_pchash_primea=except(pc, x, 3))&?z_hck)))|((((pc[x])=0)&((a_pchash_primea=except(pc, x, 5))&((a_flaghash_primea=flag)&?z_hck)))|(((pc[x])=5)&((a_flaghash_primea=except(flag, x, ?z_hl))&((a_pchash_primea=except(pc, x, 1))&?z_hck))))))))=(CHOOSE zenon_Vhsb:(~((zenon_Vhsb \\in ProcSet)=>((a_flaghash_primea[zenon_Vhsb]) \\in {TRUE, ?z_hl})))))" (is "?z_hmz=?z_hgw")
         assume z_Hun:"(?z_hqx=1)" (is "_=?z_hu")
         have z_Huo: "?z_huf(?z_hgw)" (is "_=?z_hup")
         by (rule zenon_all_0 [of "?z_huf" "?z_hgw", OF z_Hua])
         show FALSE
         proof (rule zenon_fapplyexcept [of "(\<lambda>zenon_Vsis. (?z_hhf=zenon_Vsis))" "flag" "?z_hmz" "?z_hl" "?z_hgw", OF z_Huo])
          assume z_Hqr:"?z_hqr"
          assume z_Hrc:"(?z_hmz=?z_hgw)"
          assume z_Huq:"(?z_hhf=?z_hl)"
          show FALSE
          by (rule notE [OF z_Huk z_Huq])
         next
          assume z_Hqr:"?z_hqr"
          assume z_Hrk:"(?z_hmz~=?z_hgw)"
          assume z_Hhg:"(?z_hhf=(flag[?z_hgw]))" (is "_=?z_hhh")
          show FALSE
          by (rule notE [OF z_Hrk z_Hrc])
         next
          assume z_Hrl:"(~?z_hqr)"
          show FALSE
          by (rule notE [OF z_Hrl z_Hqr])
         qed
        next
         assume z_Hqv:"?z_hqv"
         assume z_Hrk:"((CHOOSE x:((x \\in ProcSet)&((((pc[x])=1)&((a_pchash_primea=except(pc, x, 2))&((a_flaghash_primea=flag)&?z_hck)))|((((pc[x])=2)&((a_flaghash_primea=except(flag, x, TRUE))&((a_pchash_primea=except(pc, x, 3))&?z_hck)))|((((pc[x])=0)&((a_pchash_primea=except(pc, x, 5))&((a_flaghash_primea=flag)&?z_hck)))|(((pc[x])=5)&((a_flaghash_primea=except(flag, x, ?z_hl))&((a_pchash_primea=except(pc, x, 1))&?z_hck))))))))~=(CHOOSE zenon_Vhsb:(~((zenon_Vhsb \\in ProcSet)=>((a_flaghash_primea[zenon_Vhsb]) \\in {TRUE, ?z_hl})))))" (is "?z_hmz~=?z_hgw")
         assume z_Hrm:"(?z_hqx=(pc[?z_hgw]))" (is "_=?z_hrn")
         have z_Huo: "?z_huf(?z_hgw)" (is "_=?z_hup")
         by (rule zenon_all_0 [of "?z_huf" "?z_hgw", OF z_Hua])
         show FALSE
         proof (rule zenon_fapplyexcept [of "(\<lambda>zenon_Vsis. (?z_hhf=zenon_Vsis))" "flag" "?z_hmz" "?z_hl" "?z_hgw", OF z_Huo])
          assume z_Hqr:"?z_hqr"
          assume z_Hrc:"(?z_hmz=?z_hgw)"
          assume z_Huq:"(?z_hhf=?z_hl)"
          show FALSE
          by (rule notE [OF z_Hrk z_Hrc])
         next
          assume z_Hqr:"?z_hqr"
          assume z_Hrk:"(?z_hmz~=?z_hgw)"
          assume z_Hhg:"(?z_hhf=(flag[?z_hgw]))" (is "_=?z_hhh")
          show FALSE
          by (rule zenon_L5_ [OF z_Hgp z_Hgv z_Hhd z_Hhg])
         next
          assume z_Hrl:"(~?z_hqr)"
          show FALSE
          by (rule notE [OF z_Hrl z_Hqr])
         qed
        next
         assume z_Hro:"(~?z_hqv)"
         show FALSE
         by (rule notE [OF z_Hro z_Hqv])
        qed
       qed
      qed
     next
      assume z_Hkc:"(~?z_hka)" (is "~(?z_hff&?z_hkb)")
      show FALSE
      proof (rule zenon_notand [OF z_Hkc])
       assume z_Hfe:"(~?z_hff)"
       show FALSE
       by (rule zenon_L3_ [OF z_Ha z_Hfe z_Hck z_Hn])
      next
       assume z_Hkd:"(~?z_hkb)"
       have z_Hke: "(pc \\in FuncSet(?z_heg, {0, 1, 2, 3, 4, 5}))" (is "?z_hke")
       by (rule subst [where P="(\<lambda>zenon_Vgkv. (pc \\in FuncSet(zenon_Vgkv, {0, 1, 2, 3, 4, 5})))", OF z_Ha z_Hp])
       have z_Hiv: "(DOMAIN(pc)=?z_heg)" (is "?z_hiw=_")
       by (rule zenon_in_funcset_1 [of "pc" "?z_heg" "{0, 1, 2, 3, 4, 5}", OF z_Hke])
       have z_Hkk: "(?z_hiw=ProcSet)"
       by (rule zenon_in_funcset_1 [of "pc" "ProcSet" "{0, 1, 2, 3, 4, 5}", OF z_Hp])
       have z_Hkk: "(?z_hiw=ProcSet)"
       by (rule zenon_in_funcset_1 [of "pc" "ProcSet" "{0, 1, 2, 3, 4, 5}", OF z_Hp])
       have z_Hfo: "(\\A zenon_Vm:((zenon_Vm \\in ProcSet)=>((pc[zenon_Vm]) \\in {0, 1, 2, 3, 4, 5})))" (is "\\A x : ?z_hgh(x)")
       by (rule zenon_in_funcset_2 [of "pc" "ProcSet" "{0, 1, 2, 3, 4, 5}", OF z_Hp])
       have z_Hti: "(((isAFcn(a_pchash_primea)<=>isAFcn(?z_hth))&(DOMAIN(a_pchash_primea)=DOMAIN(?z_hth)))&(\\A zenon_Vqxq:((a_pchash_primea[zenon_Vqxq])=(?z_hth[zenon_Vqxq]))))" (is "?z_htj&?z_hto")
       by (rule zenon_funequal_0 [of "a_pchash_primea" "?z_hth", OF z_Htg])
       have z_Htj: "?z_htj" (is "?z_htk&?z_htm")
       by (rule zenon_and_0 [OF z_Hti])
       have z_Hto: "?z_hto" (is "\\A x : ?z_htt(x)")
       by (rule zenon_and_1 [OF z_Hti])
       have z_Htk: "?z_htk" (is "?z_hko<=>?z_htl")
       by (rule zenon_and_0 [OF z_Htj])
       show FALSE
       proof (rule zenon_equiv [OF z_Htk])
        assume z_Hkw:"(~?z_hko)"
        assume z_Hur:"(~?z_htl)"
        show FALSE
        by (rule zenon_notisafcn_except [of "pc" "(CHOOSE x:((x \\in ProcSet)&((((pc[x])=1)&((a_pchash_primea=except(pc, x, 2))&((a_flaghash_primea=flag)&?z_hck)))|((((pc[x])=2)&((a_flaghash_primea=except(flag, x, TRUE))&((a_pchash_primea=except(pc, x, 3))&?z_hck)))|((((pc[x])=0)&((a_pchash_primea=except(pc, x, 5))&((a_flaghash_primea=flag)&?z_hck)))|(((pc[x])=5)&((a_flaghash_primea=except(flag, x, FALSE))&((a_pchash_primea=except(pc, x, 1))&?z_hck))))))))" "1", OF z_Hur])
       next
        assume z_Hko:"?z_hko"
        assume z_Htl:"?z_htl"
        show FALSE
        proof (rule zenon_notin_funcset [of "a_pchash_primea" "ProcSet" "{0, 1, 2, 3, 4, 5}", OF z_Hkd])
         assume z_Hkw:"(~?z_hko)"
         show FALSE
         by (rule notE [OF z_Hkw z_Hko])
        next
         assume z_His:"(DOMAIN(a_pchash_primea)~=ProcSet)" (is "?z_hit~=_")
         have z_Hix: "(?z_hit~=?z_heg)"
         by (rule subst [where P="(\<lambda>zenon_Vikv. (?z_hit~=zenon_Vikv))", OF z_Ha z_His])
         have z_Hus: "(DOMAIN(?z_hth)~=?z_heg)" (is "?z_htn~=_")
         by (rule subst [where P="(\<lambda>zenon_Vos. (DOMAIN(zenon_Vos)~=?z_heg))", OF z_Htg z_Hix])
         have z_Hjh: "(?z_hiw~=?z_heg)"
         by (rule zenon_domain_except_0 [of "(\<lambda>zenon_Vns. (zenon_Vns~=?z_heg))" "pc" "(CHOOSE x:((x \\in ProcSet)&((((pc[x])=1)&((a_pchash_primea=except(pc, x, 2))&((a_flaghash_primea=flag)&?z_hck)))|((((pc[x])=2)&((a_flaghash_primea=except(flag, x, TRUE))&((a_pchash_primea=except(pc, x, 3))&?z_hck)))|((((pc[x])=0)&((a_pchash_primea=except(pc, x, 5))&((a_flaghash_primea=flag)&?z_hck)))|(((pc[x])=5)&((a_flaghash_primea=except(flag, x, FALSE))&((a_pchash_primea=except(pc, x, 1))&?z_hck))))))))" "1", OF z_Hus])
         show FALSE
         by (rule notE [OF z_Hjh z_Hiv])
        next
         assume z_Hkx:"(~(\\A zenon_Vpa:((zenon_Vpa \\in ProcSet)=>((a_pchash_primea[zenon_Vpa]) \\in {0, 1, 2, 3, 4, 5}))))" (is "~(\\A x : ?z_hkz(x))")
         have z_Hla: "(\\E zenon_Vpa:(~((zenon_Vpa \\in ProcSet)=>((a_pchash_primea[zenon_Vpa]) \\in {0, 1, 2, 3, 4, 5}))))" (is "\\E x : ?z_hlb(x)")
         by (rule zenon_notallex_0 [of "?z_hkz", OF z_Hkx])
         have z_Hlc: "?z_hlb((CHOOSE zenon_Vpa:(~((zenon_Vpa \\in ProcSet)=>((a_pchash_primea[zenon_Vpa]) \\in {0, 1, 2, 3, 4, 5})))))" (is "~(?z_hfu=>?z_hgd)")
         by (rule zenon_ex_choose_0 [of "?z_hlb", OF z_Hla])
         have z_Hfu: "?z_hfu"
         by (rule zenon_notimply_0 [OF z_Hlc])
         have z_Hgc: "(~?z_hgd)"
         by (rule zenon_notimply_1 [OF z_Hlc])
         have z_Hnw: "(~((a_pchash_primea[(CHOOSE zenon_Vpa:(~((zenon_Vpa \\in ProcSet)=>((a_pchash_primea[zenon_Vpa]) \\in {0, 1, 2, 3, 4, 5}))))]) \\in {1, 2, 3, 4, 5}))" (is "~?z_hnx")
         by (rule zenon_notin_addElt_1 [of "(a_pchash_primea[(CHOOSE zenon_Vpa:(~((zenon_Vpa \\in ProcSet)=>((a_pchash_primea[zenon_Vpa]) \\in {0, 1, 2, 3, 4, 5}))))])" "0" "{1, 2, 3, 4, 5}", OF z_Hgc])
         have z_Hut: "((a_pchash_primea[(CHOOSE zenon_Vpa:(~((zenon_Vpa \\in ProcSet)=>((a_pchash_primea[zenon_Vpa]) \\in {0, 1, 2, 3, 4, 5}))))])~=1)" (is "?z_hge~=?z_hu")
         by (rule zenon_notin_addElt_0 [of "?z_hge" "?z_hu" "{2, 3, 4, 5}", OF z_Hnw])
         have z_Hlf: "((CHOOSE zenon_Vpa:(~((zenon_Vpa \\in ProcSet)=>((a_pchash_primea[zenon_Vpa]) \\in {0, ?z_hu, 2, 3, 4, 5})))) \\in ?z_hiw)" (is "?z_hlf")
         by (rule ssubst [where P="(\<lambda>zenon_Vip. ((CHOOSE zenon_Vpa:(~((zenon_Vpa \\in ProcSet)=>((a_pchash_primea[zenon_Vpa]) \\in {0, ?z_hu, 2, 3, 4, 5})))) \\in zenon_Vip))", OF z_Hkk z_Hfu])
         have z_Huu: "?z_htt((CHOOSE zenon_Vpa:(~((zenon_Vpa \\in ProcSet)=>((a_pchash_primea[zenon_Vpa]) \\in {0, ?z_hu, 2, 3, 4, 5})))))" (is "_=?z_huv")
         by (rule zenon_all_0 [of "?z_htt" "(CHOOSE zenon_Vpa:(~((zenon_Vpa \\in ProcSet)=>((a_pchash_primea[zenon_Vpa]) \\in {0, ?z_hu, 2, 3, 4, 5}))))", OF z_Hto])
         show FALSE
         proof (rule zenon_fapplyexcept [of "(\<lambda>zenon_Vgs. (?z_hge=zenon_Vgs))" "pc" "(CHOOSE x:((x \\in ProcSet)&((((pc[x])=?z_hu)&((a_pchash_primea=except(pc, x, 2))&((a_flaghash_primea=flag)&?z_hck)))|((((pc[x])=2)&((a_flaghash_primea=except(flag, x, TRUE))&((a_pchash_primea=except(pc, x, 3))&?z_hck)))|((((pc[x])=0)&((a_pchash_primea=except(pc, x, 5))&((a_flaghash_primea=flag)&?z_hck)))|(((pc[x])=5)&((a_flaghash_primea=except(flag, x, FALSE))&((a_pchash_primea=except(pc, x, ?z_hu))&?z_hck))))))))" "?z_hu" "(CHOOSE zenon_Vpa:(~((zenon_Vpa \\in ProcSet)=>((a_pchash_primea[zenon_Vpa]) \\in {0, ?z_hu, 2, 3, 4, 5}))))", OF z_Huu])
          assume z_Hlf:"?z_hlf"
          assume z_Hof:"((CHOOSE x:((x \\in ProcSet)&((((pc[x])=?z_hu)&((a_pchash_primea=except(pc, x, 2))&((a_flaghash_primea=flag)&?z_hck)))|((((pc[x])=2)&((a_flaghash_primea=except(flag, x, TRUE))&((a_pchash_primea=except(pc, x, 3))&?z_hck)))|((((pc[x])=0)&((a_pchash_primea=except(pc, x, 5))&((a_flaghash_primea=flag)&?z_hck)))|(((pc[x])=5)&((a_flaghash_primea=except(flag, x, FALSE))&((a_pchash_primea=except(pc, x, ?z_hu))&?z_hck))))))))=(CHOOSE zenon_Vpa:(~((zenon_Vpa \\in ProcSet)=>((a_pchash_primea[zenon_Vpa]) \\in {0, ?z_hu, 2, 3, 4, 5})))))" (is "?z_hmz=?z_hfv")
          assume z_Huw:"(?z_hge=?z_hu)"
          show FALSE
          by (rule notE [OF z_Hut z_Huw])
         next
          assume z_Hlf:"?z_hlf"
          assume z_Hoh:"((CHOOSE x:((x \\in ProcSet)&((((pc[x])=?z_hu)&((a_pchash_primea=except(pc, x, 2))&((a_flaghash_primea=flag)&?z_hck)))|((((pc[x])=2)&((a_flaghash_primea=except(flag, x, TRUE))&((a_pchash_primea=except(pc, x, 3))&?z_hck)))|((((pc[x])=0)&((a_pchash_primea=except(pc, x, 5))&((a_flaghash_primea=flag)&?z_hck)))|(((pc[x])=5)&((a_flaghash_primea=except(flag, x, FALSE))&((a_pchash_primea=except(pc, x, ?z_hu))&?z_hck))))))))~=(CHOOSE zenon_Vpa:(~((zenon_Vpa \\in ProcSet)=>((a_pchash_primea[zenon_Vpa]) \\in {0, ?z_hu, 2, 3, 4, 5})))))" (is "?z_hmz~=?z_hfv")
          assume z_Hgf:"(?z_hge=(pc[?z_hfv]))" (is "_=?z_hgg")
          show FALSE
          by (rule zenon_L4_ [OF z_Hfo z_Hfu z_Hgc z_Hgf])
         next
          assume z_Hlr:"(~?z_hlf)"
          show FALSE
          by (rule notE [OF z_Hlr z_Hlf])
         qed
        qed
       qed
      qed
     qed
    qed
   qed
  qed
 next
  assume z_Hdj:"?z_hdj"
  have z_Hux_z_Hdj: "(\\E x:((x \\in ProcSet)&bEx(ProcSet, (\<lambda>other. ((((pc[x])=3)&((x~=other)&((a_turnhash_primea=other)&((a_pchash_primea=except(pc, x, 4))&(a_flaghash_primea=flag)))))|((flag[x])&((turn=x)&((4=(pc[x]))&((a_pchash_primea=except(pc, x, 0))&((a_flaghash_primea=flag)&(a_turnhash_primea=turn))))))))))) == ?z_hdj" (is "?z_hux == _")
  by (unfold bEx_def)
  have z_Hux: "?z_hux" (is "\\E x : ?z_huy(x)")
  by (unfold z_Hux_z_Hdj, fact z_Hdj)
  have z_Huz: "?z_huy((CHOOSE x:((x \\in ProcSet)&bEx(ProcSet, (\<lambda>other. ((((pc[x])=3)&((x~=other)&((a_turnhash_primea=other)&((a_pchash_primea=except(pc, x, 4))&(a_flaghash_primea=flag)))))|((flag[x])&((turn=x)&((4=(pc[x]))&((a_pchash_primea=except(pc, x, 0))&((a_flaghash_primea=flag)&(a_turnhash_primea=turn))))))))))))" (is "?z_hva&?z_hvb")
  by (rule zenon_ex_choose_0 [of "?z_huy", OF z_Hux])
  have z_Hvb: "?z_hvb"
  by (rule zenon_and_1 [OF z_Huz])
  have z_Hvc_z_Hvb: "(\\E x:((x \\in ProcSet)&((((pc[(CHOOSE x:((x \\in ProcSet)&bEx(ProcSet, (\<lambda>other. ((((pc[x])=3)&((x~=other)&((a_turnhash_primea=other)&((a_pchash_primea=except(pc, x, 4))&(a_flaghash_primea=flag)))))|((flag[x])&((turn=x)&((4=(pc[x]))&((a_pchash_primea=except(pc, x, 0))&((a_flaghash_primea=flag)&(a_turnhash_primea=turn)))))))))))])=3)&(((CHOOSE x:((x \\in ProcSet)&bEx(ProcSet, (\<lambda>other. ((((pc[x])=3)&((x~=other)&((a_turnhash_primea=other)&((a_pchash_primea=except(pc, x, 4))&(a_flaghash_primea=flag)))))|((flag[x])&((turn=x)&((4=(pc[x]))&((a_pchash_primea=except(pc, x, 0))&((a_flaghash_primea=flag)&(a_turnhash_primea=turn)))))))))))~=x)&((a_turnhash_primea=x)&((a_pchash_primea=except(pc, (CHOOSE x:((x \\in ProcSet)&bEx(ProcSet, (\<lambda>other. ((((pc[x])=3)&((x~=other)&((a_turnhash_primea=other)&((a_pchash_primea=except(pc, x, 4))&(a_flaghash_primea=flag)))))|((flag[x])&((turn=x)&((4=(pc[x]))&((a_pchash_primea=except(pc, x, 0))&((a_flaghash_primea=flag)&(a_turnhash_primea=turn))))))))))), 4))&(a_flaghash_primea=flag)))))|((flag[(CHOOSE x:((x \\in ProcSet)&bEx(ProcSet, (\<lambda>other. ((((pc[x])=3)&((x~=other)&((a_turnhash_primea=other)&((a_pchash_primea=except(pc, x, 4))&(a_flaghash_primea=flag)))))|((flag[x])&((turn=x)&((4=(pc[x]))&((a_pchash_primea=except(pc, x, 0))&((a_flaghash_primea=flag)&(a_turnhash_primea=turn)))))))))))])&((turn=(CHOOSE x:((x \\in ProcSet)&bEx(ProcSet, (\<lambda>other. ((((pc[x])=3)&((x~=other)&((a_turnhash_primea=other)&((a_pchash_primea=except(pc, x, 4))&(a_flaghash_primea=flag)))))|((flag[x])&((turn=x)&((4=(pc[x]))&((a_pchash_primea=except(pc, x, 0))&((a_flaghash_primea=flag)&(a_turnhash_primea=turn))))))))))))&((4=(pc[(CHOOSE x:((x \\in ProcSet)&bEx(ProcSet, (\<lambda>other. ((((pc[x])=3)&((x~=other)&((a_turnhash_primea=other)&((a_pchash_primea=except(pc, x, 4))&(a_flaghash_primea=flag)))))|((flag[x])&((turn=x)&((4=(pc[x]))&((a_pchash_primea=except(pc, x, 0))&((a_flaghash_primea=flag)&(a_turnhash_primea=turn)))))))))))]))&((a_pchash_primea=except(pc, (CHOOSE x:((x \\in ProcSet)&bEx(ProcSet, (\<lambda>other. ((((pc[x])=3)&((x~=other)&((a_turnhash_primea=other)&((a_pchash_primea=except(pc, x, 4))&(a_flaghash_primea=flag)))))|((flag[x])&((turn=x)&((4=(pc[x]))&((a_pchash_primea=except(pc, x, 0))&((a_flaghash_primea=flag)&(a_turnhash_primea=turn))))))))))), 0))&((a_flaghash_primea=flag)&(a_turnhash_primea=turn))))))))) == ?z_hvb" (is "?z_hvc == _")
  by (unfold bEx_def)
  have z_Hvc: "?z_hvc" (is "\\E x : ?z_hvm(x)")
  by (unfold z_Hvc_z_Hvb, fact z_Hvb)
  have z_Hvn: "?z_hvm((CHOOSE x:((x \\in ProcSet)&((((pc[(CHOOSE x:((x \\in ProcSet)&bEx(ProcSet, (\<lambda>other. ((((pc[x])=3)&((x~=other)&((a_turnhash_primea=other)&((a_pchash_primea=except(pc, x, 4))&(a_flaghash_primea=flag)))))|((flag[x])&((turn=x)&((4=(pc[x]))&((a_pchash_primea=except(pc, x, 0))&((a_flaghash_primea=flag)&(a_turnhash_primea=turn)))))))))))])=3)&(((CHOOSE x:((x \\in ProcSet)&bEx(ProcSet, (\<lambda>other. ((((pc[x])=3)&((x~=other)&((a_turnhash_primea=other)&((a_pchash_primea=except(pc, x, 4))&(a_flaghash_primea=flag)))))|((flag[x])&((turn=x)&((4=(pc[x]))&((a_pchash_primea=except(pc, x, 0))&((a_flaghash_primea=flag)&(a_turnhash_primea=turn)))))))))))~=x)&((a_turnhash_primea=x)&((a_pchash_primea=except(pc, (CHOOSE x:((x \\in ProcSet)&bEx(ProcSet, (\<lambda>other. ((((pc[x])=3)&((x~=other)&((a_turnhash_primea=other)&((a_pchash_primea=except(pc, x, 4))&(a_flaghash_primea=flag)))))|((flag[x])&((turn=x)&((4=(pc[x]))&((a_pchash_primea=except(pc, x, 0))&((a_flaghash_primea=flag)&(a_turnhash_primea=turn))))))))))), 4))&(a_flaghash_primea=flag)))))|((flag[(CHOOSE x:((x \\in ProcSet)&bEx(ProcSet, (\<lambda>other. ((((pc[x])=3)&((x~=other)&((a_turnhash_primea=other)&((a_pchash_primea=except(pc, x, 4))&(a_flaghash_primea=flag)))))|((flag[x])&((turn=x)&((4=(pc[x]))&((a_pchash_primea=except(pc, x, 0))&((a_flaghash_primea=flag)&(a_turnhash_primea=turn)))))))))))])&((turn=(CHOOSE x:((x \\in ProcSet)&bEx(ProcSet, (\<lambda>other. ((((pc[x])=3)&((x~=other)&((a_turnhash_primea=other)&((a_pchash_primea=except(pc, x, 4))&(a_flaghash_primea=flag)))))|((flag[x])&((turn=x)&((4=(pc[x]))&((a_pchash_primea=except(pc, x, 0))&((a_flaghash_primea=flag)&(a_turnhash_primea=turn))))))))))))&((4=(pc[(CHOOSE x:((x \\in ProcSet)&bEx(ProcSet, (\<lambda>other. ((((pc[x])=3)&((x~=other)&((a_turnhash_primea=other)&((a_pchash_primea=except(pc, x, 4))&(a_flaghash_primea=flag)))))|((flag[x])&((turn=x)&((4=(pc[x]))&((a_pchash_primea=except(pc, x, 0))&((a_flaghash_primea=flag)&(a_turnhash_primea=turn)))))))))))]))&((a_pchash_primea=except(pc, (CHOOSE x:((x \\in ProcSet)&bEx(ProcSet, (\<lambda>other. ((((pc[x])=3)&((x~=other)&((a_turnhash_primea=other)&((a_pchash_primea=except(pc, x, 4))&(a_flaghash_primea=flag)))))|((flag[x])&((turn=x)&((4=(pc[x]))&((a_pchash_primea=except(pc, x, 0))&((a_flaghash_primea=flag)&(a_turnhash_primea=turn))))))))))), 0))&((a_flaghash_primea=flag)&(a_turnhash_primea=turn))))))))))" (is "?z_hvp&?z_hvq")
  by (rule zenon_ex_choose_0 [of "?z_hvm", OF z_Hvc])
  have z_Hvp: "?z_hvp"
  by (rule zenon_and_0 [OF z_Hvn])
  have z_Hvq: "?z_hvq" (is "?z_hvr|?z_hjr")
  by (rule zenon_and_1 [OF z_Hvn])
  show FALSE
  proof (rule zenon_or [OF z_Hvq])
   assume z_Hvr:"?z_hvr" (is "?z_hvg&?z_hvs")
   have z_Hvs: "?z_hvs" (is "?z_hvt&?z_hvu")
   by (rule zenon_and_1 [OF z_Hvr])
   have z_Hvu: "?z_hvu" (is "?z_hvv&?z_hvl")
   by (rule zenon_and_1 [OF z_Hvs])
   have z_Hvv: "?z_hvv" (is "_=?z_hvo")
   by (rule zenon_and_0 [OF z_Hvu])
   have z_Hvl: "?z_hvl" (is "?z_hiu&?z_hci")
   by (rule zenon_and_1 [OF z_Hvu])
   have z_Hiu: "?z_hiu" (is "_=?z_hhs")
   by (rule zenon_and_0 [OF z_Hvl])
   have z_Hci: "?z_hci"
   by (rule zenon_and_1 [OF z_Hvl])
   show FALSE
   proof (rule zenon_notand [OF z_Hc])
    assume z_Heh:"(~?z_hei)"
    show FALSE
    by (rule zenon_L1_ [OF z_Heh z_Hf z_Hci])
   next
    assume z_Hkc:"(~?z_hka)" (is "~(?z_hff&?z_hkb)")
    show FALSE
    proof (rule zenon_notand [OF z_Hkc])
     assume z_Hfe:"(~?z_hff)"
     have z_Hfg: "(~(a_turnhash_primea \\in ?z_heg))" (is "~?z_hfh")
     by (rule subst [where P="(\<lambda>zenon_Vckv. (~(a_turnhash_primea \\in zenon_Vckv)))", OF z_Ha z_Hfe])
     have z_Heo: "(a_turnhash_primea~=0)"
     by (rule zenon_notin_addElt_0 [of "a_turnhash_primea" "0" "{1}", OF z_Hfg])
     have z_Hfm: "(~(a_turnhash_primea \\in {1}))" (is "~?z_hfn")
     by (rule zenon_notin_addElt_1 [of "a_turnhash_primea" "0" "{1}", OF z_Hfg])
     have z_Hen: "(a_turnhash_primea~=1)" (is "_~=?z_hu")
     by (rule zenon_notin_addElt_0 [of "a_turnhash_primea" "?z_hu" "{}", OF z_Hfm])
     have z_Hvw: "(?z_hvo \\in ?z_heg)" (is "?z_hvw")
     by (rule subst [where P="(\<lambda>zenon_Vglv. (?z_hvo \\in zenon_Vglv))", OF z_Ha z_Hvp])
     show FALSE
     proof (rule zenon_in_addElt [of "?z_hvo" "0" "{?z_hu}", OF z_Hvw])
      assume z_Hwa:"(?z_hvo=0)"
      show FALSE
      proof (rule notE [OF z_Heo])
       have z_Hev: "(a_turnhash_primea=0)"
       by (rule subst [where P="(\<lambda>zenon_Vqlv. (a_turnhash_primea=zenon_Vqlv))", OF z_Hwa], fact z_Hvv)
       thus "(a_turnhash_primea=0)" .
      qed
     next
      assume z_Hwb:"(?z_hvo \\in {?z_hu})" (is "?z_hwb")
      show FALSE
      proof (rule zenon_in_addElt [of "?z_hvo" "?z_hu" "{}", OF z_Hwb])
       assume z_Hwc:"(?z_hvo=?z_hu)"
       show FALSE
       proof (rule notE [OF z_Hen])
        have z_Hfc: "(a_turnhash_primea=?z_hu)"
        by (rule subst [where P="(\<lambda>zenon_Vqlv. (a_turnhash_primea=zenon_Vqlv))", OF z_Hwc], fact z_Hvv)
        thus "(a_turnhash_primea=?z_hu)" .
       qed
      next
       assume z_Hwd:"(?z_hvo \\in {})" (is "?z_hwd")
       show FALSE
       by (rule zenon_in_emptyset [of "?z_hvo", OF z_Hwd])
      qed
     qed
    next
     assume z_Hkd:"(~?z_hkb)"
     have z_Hke: "(pc \\in FuncSet(?z_heg, {0, 1, 2, 3, 4, 5}))" (is "?z_hke")
     by (rule subst [where P="(\<lambda>zenon_Vgkv. (pc \\in FuncSet(zenon_Vgkv, {0, 1, 2, 3, 4, 5})))", OF z_Ha z_Hp])
     have z_Hiv: "(DOMAIN(pc)=?z_heg)" (is "?z_hiw=_")
     by (rule zenon_in_funcset_1 [of "pc" "?z_heg" "{0, 1, 2, 3, 4, 5}", OF z_Hke])
     have z_Hkk: "(?z_hiw=ProcSet)"
     by (rule zenon_in_funcset_1 [of "pc" "ProcSet" "{0, 1, 2, 3, 4, 5}", OF z_Hp])
     have z_Hkk: "(?z_hiw=ProcSet)"
     by (rule zenon_in_funcset_1 [of "pc" "ProcSet" "{0, 1, 2, 3, 4, 5}", OF z_Hp])
     have z_Hfo: "(\\A zenon_Vm:((zenon_Vm \\in ProcSet)=>((pc[zenon_Vm]) \\in {0, 1, 2, 3, 4, 5})))" (is "\\A x : ?z_hgh(x)")
     by (rule zenon_in_funcset_2 [of "pc" "ProcSet" "{0, 1, 2, 3, 4, 5}", OF z_Hp])
     have z_Hwe: "(((isAFcn(a_pchash_primea)<=>isAFcn(?z_hhs))&(DOMAIN(a_pchash_primea)=DOMAIN(?z_hhs)))&(\\A zenon_Vlmc:((a_pchash_primea[zenon_Vlmc])=(?z_hhs[zenon_Vlmc]))))" (is "?z_hwf&?z_hwi")
     by (rule zenon_funequal_0 [of "a_pchash_primea" "?z_hhs", OF z_Hiu])
     have z_Hwf: "?z_hwf" (is "?z_hwg&?z_hwh")
     by (rule zenon_and_0 [OF z_Hwe])
     have z_Hwi: "?z_hwi" (is "\\A x : ?z_hwn(x)")
     by (rule zenon_and_1 [OF z_Hwe])
     have z_Hwg: "?z_hwg" (is "?z_hko<=>?z_hhr")
     by (rule zenon_and_0 [OF z_Hwf])
     show FALSE
     proof (rule zenon_equiv [OF z_Hwg])
      assume z_Hkw:"(~?z_hko)"
      assume z_Hhq:"(~?z_hhr)"
      show FALSE
      by (rule zenon_L6_ [OF z_Hhq])
     next
      assume z_Hko:"?z_hko"
      assume z_Hhr:"?z_hhr"
      show FALSE
      proof (rule zenon_notin_funcset [of "a_pchash_primea" "ProcSet" "{0, 1, 2, 3, 4, 5}", OF z_Hkd])
       assume z_Hkw:"(~?z_hko)"
       show FALSE
       by (rule notE [OF z_Hkw z_Hko])
      next
       assume z_His:"(DOMAIN(a_pchash_primea)~=ProcSet)" (is "?z_hit~=_")
       show FALSE
       by (rule zenon_L7_ [OF z_Ha z_His z_Hiu z_Hiv])
      next
       assume z_Hkx:"(~(\\A zenon_Vpa:((zenon_Vpa \\in ProcSet)=>((a_pchash_primea[zenon_Vpa]) \\in {0, 1, 2, 3, 4, 5}))))" (is "~(\\A x : ?z_hkz(x))")
       have z_Hla: "(\\E zenon_Vpa:(~((zenon_Vpa \\in ProcSet)=>((a_pchash_primea[zenon_Vpa]) \\in {0, 1, 2, 3, 4, 5}))))" (is "\\E x : ?z_hlb(x)")
       by (rule zenon_notallex_0 [of "?z_hkz", OF z_Hkx])
       have z_Hlc: "?z_hlb((CHOOSE zenon_Vpa:(~((zenon_Vpa \\in ProcSet)=>((a_pchash_primea[zenon_Vpa]) \\in {0, 1, 2, 3, 4, 5})))))" (is "~(?z_hfu=>?z_hgd)")
       by (rule zenon_ex_choose_0 [of "?z_hlb", OF z_Hla])
       have z_Hfu: "?z_hfu"
       by (rule zenon_notimply_0 [OF z_Hlc])
       have z_Hgc: "(~?z_hgd)"
       by (rule zenon_notimply_1 [OF z_Hlc])
       have z_Hnw: "(~((a_pchash_primea[(CHOOSE zenon_Vpa:(~((zenon_Vpa \\in ProcSet)=>((a_pchash_primea[zenon_Vpa]) \\in {0, 1, 2, 3, 4, 5}))))]) \\in {1, 2, 3, 4, 5}))" (is "~?z_hnx")
       by (rule zenon_notin_addElt_1 [of "(a_pchash_primea[(CHOOSE zenon_Vpa:(~((zenon_Vpa \\in ProcSet)=>((a_pchash_primea[zenon_Vpa]) \\in {0, 1, 2, 3, 4, 5}))))])" "0" "{1, 2, 3, 4, 5}", OF z_Hgc])
       have z_Hny: "(~((a_pchash_primea[(CHOOSE zenon_Vpa:(~((zenon_Vpa \\in ProcSet)=>((a_pchash_primea[zenon_Vpa]) \\in {0, 1, 2, 3, 4, 5}))))]) \\in {2, 3, 4, 5}))" (is "~?z_hnz")
       by (rule zenon_notin_addElt_1 [of "(a_pchash_primea[(CHOOSE zenon_Vpa:(~((zenon_Vpa \\in ProcSet)=>((a_pchash_primea[zenon_Vpa]) \\in {0, 1, 2, 3, 4, 5}))))])" "1" "{2, 3, 4, 5}", OF z_Hnw])
       have z_Hrr: "(~((a_pchash_primea[(CHOOSE zenon_Vpa:(~((zenon_Vpa \\in ProcSet)=>((a_pchash_primea[zenon_Vpa]) \\in {0, 1, 2, 3, 4, 5}))))]) \\in {3, 4, 5}))" (is "~?z_hrs")
       by (rule zenon_notin_addElt_1 [of "(a_pchash_primea[(CHOOSE zenon_Vpa:(~((zenon_Vpa \\in ProcSet)=>((a_pchash_primea[zenon_Vpa]) \\in {0, 1, 2, 3, 4, 5}))))])" "2" "{3, 4, 5}", OF z_Hny])
       have z_Hss: "(~((a_pchash_primea[(CHOOSE zenon_Vpa:(~((zenon_Vpa \\in ProcSet)=>((a_pchash_primea[zenon_Vpa]) \\in {0, 1, 2, 3, 4, 5}))))]) \\in {4, 5}))" (is "~?z_hst")
       by (rule zenon_notin_addElt_1 [of "(a_pchash_primea[(CHOOSE zenon_Vpa:(~((zenon_Vpa \\in ProcSet)=>((a_pchash_primea[zenon_Vpa]) \\in {0, 1, 2, 3, 4, 5}))))])" "3" "{4, 5}", OF z_Hrr])
       have z_Hwo: "((a_pchash_primea[(CHOOSE zenon_Vpa:(~((zenon_Vpa \\in ProcSet)=>((a_pchash_primea[zenon_Vpa]) \\in {0, 1, 2, 3, 4, 5}))))])~=4)" (is "?z_hge~=?z_hx")
       by (rule zenon_notin_addElt_0 [of "?z_hge" "?z_hx" "{5}", OF z_Hss])
       have z_Hlf: "((CHOOSE zenon_Vpa:(~((zenon_Vpa \\in ProcSet)=>((a_pchash_primea[zenon_Vpa]) \\in {0, 1, 2, 3, ?z_hx, 5})))) \\in ?z_hiw)" (is "?z_hlf")
       by (rule ssubst [where P="(\<lambda>zenon_Vip. ((CHOOSE zenon_Vpa:(~((zenon_Vpa \\in ProcSet)=>((a_pchash_primea[zenon_Vpa]) \\in {0, 1, 2, 3, ?z_hx, 5})))) \\in zenon_Vip))", OF z_Hkk z_Hfu])
       have z_Hwp: "?z_hwn((CHOOSE zenon_Vpa:(~((zenon_Vpa \\in ProcSet)=>((a_pchash_primea[zenon_Vpa]) \\in {0, 1, 2, 3, ?z_hx, 5})))))" (is "_=?z_hwq")
       by (rule zenon_all_0 [of "?z_hwn" "(CHOOSE zenon_Vpa:(~((zenon_Vpa \\in ProcSet)=>((a_pchash_primea[zenon_Vpa]) \\in {0, 1, 2, 3, ?z_hx, 5}))))", OF z_Hwi])
       show FALSE
       proof (rule zenon_fapplyexcept [of "(\<lambda>zenon_Vgs. (?z_hge=zenon_Vgs))" "pc" "(CHOOSE x:((x \\in ProcSet)&bEx(ProcSet, (\<lambda>other. ((((pc[x])=3)&((x~=other)&((a_turnhash_primea=other)&((a_pchash_primea=except(pc, x, ?z_hx))&?z_hci))))|((flag[x])&((turn=x)&((?z_hx=(pc[x]))&((a_pchash_primea=except(pc, x, 0))&(?z_hci&(a_turnhash_primea=turn)))))))))))" "?z_hx" "(CHOOSE zenon_Vpa:(~((zenon_Vpa \\in ProcSet)=>((a_pchash_primea[zenon_Vpa]) \\in {0, 1, 2, 3, ?z_hx, 5}))))", OF z_Hwp])
        assume z_Hlf:"?z_hlf"
        assume z_Hlo:"((CHOOSE x:((x \\in ProcSet)&bEx(ProcSet, (\<lambda>other. ((((pc[x])=3)&((x~=other)&((a_turnhash_primea=other)&((a_pchash_primea=except(pc, x, ?z_hx))&?z_hci))))|((flag[x])&((turn=x)&((?z_hx=(pc[x]))&((a_pchash_primea=except(pc, x, 0))&(?z_hci&(a_turnhash_primea=turn)))))))))))=(CHOOSE zenon_Vpa:(~((zenon_Vpa \\in ProcSet)=>((a_pchash_primea[zenon_Vpa]) \\in {0, 1, 2, 3, ?z_hx, 5})))))" (is "?z_hht=?z_hfv")
        assume z_Hwr:"(?z_hge=?z_hx)"
        show FALSE
        by (rule notE [OF z_Hwo z_Hwr])
       next
        assume z_Hlf:"?z_hlf"
        assume z_Hlq:"((CHOOSE x:((x \\in ProcSet)&bEx(ProcSet, (\<lambda>other. ((((pc[x])=3)&((x~=other)&((a_turnhash_primea=other)&((a_pchash_primea=except(pc, x, ?z_hx))&?z_hci))))|((flag[x])&((turn=x)&((?z_hx=(pc[x]))&((a_pchash_primea=except(pc, x, 0))&(?z_hci&(a_turnhash_primea=turn)))))))))))~=(CHOOSE zenon_Vpa:(~((zenon_Vpa \\in ProcSet)=>((a_pchash_primea[zenon_Vpa]) \\in {0, 1, 2, 3, ?z_hx, 5})))))" (is "?z_hht~=?z_hfv")
        assume z_Hgf:"(?z_hge=(pc[?z_hfv]))" (is "_=?z_hgg")
        show FALSE
        by (rule zenon_L4_ [OF z_Hfo z_Hfu z_Hgc z_Hgf])
       next
        assume z_Hlr:"(~?z_hlf)"
        show FALSE
        by (rule notE [OF z_Hlr z_Hlf])
       qed
      qed
     qed
    qed
   qed
  next
   assume z_Hjr:"?z_hjr" (is "?z_hjs&?z_hjt")
   show FALSE
   by (rule zenon_L10_ [OF z_Hjr z_Hc z_Hf z_Hn z_Ha z_Hp])
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 8"; *} qed
end
