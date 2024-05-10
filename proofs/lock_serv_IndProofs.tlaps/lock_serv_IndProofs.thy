(* automatically generated -- do not edit manually *)
theory lock_serv_IndProofs imports Constant Zenon begin
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

lemma ob'14:
fixes Node
fixes a_lockunde_msga a_lockunde_msga'
fixes a_grantunde_msga a_grantunde_msga'
fixes a_unlockunde_msga a_unlockunde_msga'
fixes a_holdsunde_locka a_holdsunde_locka'
fixes a_serverunde_holdsunde_locka a_serverunde_holdsunde_locka'
(* usable definition vars suppressed *)
(* usable definition Spec suppressed *)
(* usable definition Liveness suppressed *)
assumes v'10: "(((((((a_lockunde_msga) \<in> ([(Node) \<rightarrow> (BOOLEAN)]))) & (((a_grantunde_msga) \<in> ([(Node) \<rightarrow> (BOOLEAN)]))) & (((a_unlockunde_msga) \<in> ([(Node) \<rightarrow> (BOOLEAN)]))) & (((a_holdsunde_locka) \<in> ([(Node) \<rightarrow> (BOOLEAN)]))) & (((a_serverunde_holdsunde_locka) \<in> (BOOLEAN)))) & (\<forall> x \<in> (Node) : (\<forall> y \<in> (Node) : (((((fapply ((a_holdsunde_locka), (x))) \<and> (fapply ((a_holdsunde_locka), (y))))) \<Rightarrow> (((x) = (y))))))) & (\<forall> VARI \<in> (Node) : (\<forall> VARJ \<in> (Node) : ((((~ (fapply ((a_grantunde_msga), (VARI))))) \<or> ((~ (fapply ((a_unlockunde_msga), (VARJ))))))))) & (\<forall> VARI \<in> (Node) : ((((~ (fapply ((a_holdsunde_locka), (VARI))))) \<or> ((~ (a_serverunde_holdsunde_locka)))))) & (\<forall> VARI \<in> (Node) : (\<forall> VARJ \<in> (Node) : ((((~ (fapply ((a_grantunde_msga), (VARI))))) \<or> ((~ (fapply ((a_holdsunde_locka), (VARJ))))))))) & (\<forall> VARI \<in> (Node) : (\<forall> VARJ \<in> (Node) : ((((~ (fapply ((a_holdsunde_locka), (VARI))))) \<or> ((~ (fapply ((a_unlockunde_msga), (VARJ))))))))) & (\<forall> VARI \<in> (Node) : ((((~ (fapply ((a_grantunde_msga), (VARI))))) \<or> ((~ (a_serverunde_holdsunde_locka)))))) & (\<forall> VARI \<in> (Node) : ((((~ (a_serverunde_holdsunde_locka))) \<or> ((~ (fapply ((a_unlockunde_msga), (VARI)))))))) & (\<forall> VARI \<in> (Node) : (\<forall> VARJ \<in> (Node) : (((((((VARI) = (VARJ))) \<or> ((~ (fapply ((a_grantunde_msga), (VARJ))))))) \<or> ((~ (fapply ((a_grantunde_msga), (VARI))))))))) & (\<forall> VARI \<in> (Node) : (\<forall> VARJ \<in> (Node) : (((((VARI) = (VARJ))) \<or> ((((~ (fapply ((a_unlockunde_msga), (VARI))))) \<or> ((~ (fapply ((a_unlockunde_msga), (VARJ)))))))))))) \<and> (\<exists> n \<in> (Node) : ((((((a_lockunde_msghash_primea :: c)) = ([(a_lockunde_msga) EXCEPT ![(n)] = (TRUE)]))) & ((((a_grantunde_msghash_primea :: c)) = (a_grantunde_msga))) & ((((a_holdsunde_lockhash_primea :: c)) = (a_holdsunde_locka))) & ((((a_unlockunde_msghash_primea :: c)) = (a_unlockunde_msga))) & ((((a_serverunde_holdsunde_lockhash_primea :: c)) = (a_serverunde_holdsunde_locka)))) | ((a_serverunde_holdsunde_locka) & (fapply ((a_lockunde_msga), (n))) & ((((a_serverunde_holdsunde_lockhash_primea :: c)) = (FALSE))) & ((((a_lockunde_msghash_primea :: c)) = ([(a_lockunde_msga) EXCEPT ![(n)] = (FALSE)]))) & ((((a_grantunde_msghash_primea :: c)) = ([(a_grantunde_msga) EXCEPT ![(n)] = (TRUE)]))) & ((((a_unlockunde_msghash_primea :: c)) = (a_unlockunde_msga))) & ((((a_holdsunde_lockhash_primea :: c)) = (a_holdsunde_locka)))) | ((fapply ((a_grantunde_msga), (n))) & ((((a_grantunde_msghash_primea :: c)) = ([(a_grantunde_msga) EXCEPT ![(n)] = (FALSE)]))) & ((((a_holdsunde_lockhash_primea :: c)) = ([(a_holdsunde_locka) EXCEPT ![(n)] = (TRUE)]))) & ((((a_lockunde_msghash_primea :: c)) = (a_lockunde_msga))) & ((((a_unlockunde_msghash_primea :: c)) = (a_unlockunde_msga))) & ((((a_serverunde_holdsunde_lockhash_primea :: c)) = (a_serverunde_holdsunde_locka)))) | ((fapply ((a_holdsunde_locka), (n))) & ((((a_holdsunde_lockhash_primea :: c)) = ([(a_holdsunde_locka) EXCEPT ![(n)] = (FALSE)]))) & ((((a_unlockunde_msghash_primea :: c)) = ([(a_unlockunde_msga) EXCEPT ![(n)] = (TRUE)]))) & ((((a_lockunde_msghash_primea :: c)) = (a_lockunde_msga))) & ((((a_grantunde_msghash_primea :: c)) = (a_grantunde_msga))) & ((((a_serverunde_holdsunde_lockhash_primea :: c)) = (a_serverunde_holdsunde_locka)))) | ((fapply ((a_unlockunde_msga), (n))) & ((((a_unlockunde_msghash_primea :: c)) = ([(a_unlockunde_msga) EXCEPT ![(n)] = (FALSE)]))) & ((((a_serverunde_holdsunde_lockhash_primea :: c)) = (TRUE))) & ((((a_lockunde_msghash_primea :: c)) = (a_lockunde_msga))) & ((((a_grantunde_msghash_primea :: c)) = (a_grantunde_msga))) & ((((a_holdsunde_lockhash_primea :: c)) = (a_holdsunde_locka))))))))"
shows "(((((a_lockunde_msghash_primea :: c)) \<in> ([(Node) \<rightarrow> (BOOLEAN)]))) & ((((a_grantunde_msghash_primea :: c)) \<in> ([(Node) \<rightarrow> (BOOLEAN)]))) & ((((a_unlockunde_msghash_primea :: c)) \<in> ([(Node) \<rightarrow> (BOOLEAN)]))) & ((((a_holdsunde_lockhash_primea :: c)) \<in> ([(Node) \<rightarrow> (BOOLEAN)]))) & ((((a_serverunde_holdsunde_lockhash_primea :: c)) \<in> (BOOLEAN))))"(is "PROP ?ob'14")
proof -
ML_command {* writeln "*** TLAPS ENTER 14"; *}
show "PROP ?ob'14"

(* BEGIN ZENON INPUT
;; file=lock_serv_IndProofs.tlaps/tlapm_f5ba55.znn; PATH='/home/egolf/.opam/4.07.1/bin:/home/egolf/.local/bin:/home/egolf/bin:/home/egolf/mambaforge/bin:/home/egolf/mambaforge/condabin:/home/egolf/.opam/4.07.1/bin:/home/egolf/.local/bin:/home/egolf/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/home/egolf/.local/bin/gurobi952/linux64/bin:/home/egolf/Projects/apalache/bin:/home/egolf/opt/foxitsoftware/foxitreader:/home/egolf/.local/bin/gurobi952/linux64/bin:/home/egolf/Projects/apalache/bin:/home/egolf/opt/foxitsoftware/foxitreader:/usr/local/bin:/usr/local/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >lock_serv_IndProofs.tlaps/tlapm_f5ba55.znn.out
;; obligation #14
$hyp "v'10" (/\ (/\ (/\ (TLA.in a_lockunde_msga
(TLA.FuncSet Node (TLA.set T. F.))) (TLA.in a_grantunde_msga
(TLA.FuncSet Node (TLA.set T. F.))) (TLA.in a_unlockunde_msga
(TLA.FuncSet Node (TLA.set T. F.))) (TLA.in a_holdsunde_locka
(TLA.FuncSet Node (TLA.set T. F.))) (TLA.in a_serverunde_holdsunde_locka
(TLA.set T. F.)))
(TLA.bAll Node ((x) (TLA.bAll Node ((y) (=> (/\ (TLA.fapply a_holdsunde_locka x)
(TLA.fapply a_holdsunde_locka y)) (= x y))))))
(TLA.bAll Node ((VARI) (TLA.bAll Node ((VARJ) (\/ (-. (TLA.fapply a_grantunde_msga VARI))
(-. (TLA.fapply a_unlockunde_msga VARJ)))))))
(TLA.bAll Node ((VARI) (\/ (-. (TLA.fapply a_holdsunde_locka VARI))
(-. a_serverunde_holdsunde_locka))))
(TLA.bAll Node ((VARI) (TLA.bAll Node ((VARJ) (\/ (-. (TLA.fapply a_grantunde_msga VARI))
(-. (TLA.fapply a_holdsunde_locka VARJ)))))))
(TLA.bAll Node ((VARI) (TLA.bAll Node ((VARJ) (\/ (-. (TLA.fapply a_holdsunde_locka VARI))
(-. (TLA.fapply a_unlockunde_msga VARJ)))))))
(TLA.bAll Node ((VARI) (\/ (-. (TLA.fapply a_grantunde_msga VARI))
(-. a_serverunde_holdsunde_locka))))
(TLA.bAll Node ((VARI) (\/ (-. a_serverunde_holdsunde_locka)
(-. (TLA.fapply a_unlockunde_msga VARI)))))
(TLA.bAll Node ((VARI) (TLA.bAll Node ((VARJ) (\/ (\/ (= VARI VARJ)
(-. (TLA.fapply a_grantunde_msga VARJ)))
(-. (TLA.fapply a_grantunde_msga VARI)))))))
(TLA.bAll Node ((VARI) (TLA.bAll Node ((VARJ) (\/ (= VARI VARJ)
(\/ (-. (TLA.fapply a_unlockunde_msga VARI))
(-. (TLA.fapply a_unlockunde_msga VARJ)))))))))
(TLA.bEx Node ((n) (\/ (/\ (= a_lockunde_msghash_primea
(TLA.except a_lockunde_msga n T.)) (= a_grantunde_msghash_primea
a_grantunde_msga) (= a_holdsunde_lockhash_primea a_holdsunde_locka)
(= a_unlockunde_msghash_primea a_unlockunde_msga)
(= a_serverunde_holdsunde_lockhash_primea a_serverunde_holdsunde_locka))
(/\ a_serverunde_holdsunde_locka (TLA.fapply a_lockunde_msga n)
(= a_serverunde_holdsunde_lockhash_primea F.) (= a_lockunde_msghash_primea
(TLA.except a_lockunde_msga n F.)) (= a_grantunde_msghash_primea
(TLA.except a_grantunde_msga n T.)) (= a_unlockunde_msghash_primea
a_unlockunde_msga) (= a_holdsunde_lockhash_primea a_holdsunde_locka))
(/\ (TLA.fapply a_grantunde_msga n) (= a_grantunde_msghash_primea
(TLA.except a_grantunde_msga n F.)) (= a_holdsunde_lockhash_primea
(TLA.except a_holdsunde_locka n T.)) (= a_lockunde_msghash_primea
a_lockunde_msga) (= a_unlockunde_msghash_primea a_unlockunde_msga)
(= a_serverunde_holdsunde_lockhash_primea a_serverunde_holdsunde_locka))
(/\ (TLA.fapply a_holdsunde_locka n) (= a_holdsunde_lockhash_primea
(TLA.except a_holdsunde_locka n F.)) (= a_unlockunde_msghash_primea
(TLA.except a_unlockunde_msga n T.)) (= a_lockunde_msghash_primea
a_lockunde_msga) (= a_grantunde_msghash_primea a_grantunde_msga)
(= a_serverunde_holdsunde_lockhash_primea a_serverunde_holdsunde_locka))
(/\ (TLA.fapply a_unlockunde_msga n) (= a_unlockunde_msghash_primea
(TLA.except a_unlockunde_msga n F.))
(= a_serverunde_holdsunde_lockhash_primea T.) (= a_lockunde_msghash_primea
a_lockunde_msga) (= a_grantunde_msghash_primea a_grantunde_msga)
(= a_holdsunde_lockhash_primea
a_holdsunde_locka))))))
$goal (/\ (TLA.in a_lockunde_msghash_primea
(TLA.FuncSet Node (TLA.set T. F.))) (TLA.in a_grantunde_msghash_primea
(TLA.FuncSet Node (TLA.set T. F.))) (TLA.in a_unlockunde_msghash_primea
(TLA.FuncSet Node (TLA.set T. F.))) (TLA.in a_holdsunde_lockhash_primea
(TLA.FuncSet Node (TLA.set T. F.)))
(TLA.in a_serverunde_holdsunde_lockhash_primea
(TLA.set T. F.)))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Ha:"((((a_lockunde_msga \\in FuncSet(Node, {TRUE, FALSE}))&((a_grantunde_msga \\in FuncSet(Node, {TRUE, FALSE}))&((a_unlockunde_msga \\in FuncSet(Node, {TRUE, FALSE}))&((a_holdsunde_locka \\in FuncSet(Node, {TRUE, FALSE}))&(a_serverunde_holdsunde_locka \\in {TRUE, FALSE})))))&(bAll(Node, (\<lambda>x. bAll(Node, (\<lambda>y. (((a_holdsunde_locka[x])&(a_holdsunde_locka[y]))=>(x=y))))))&(bAll(Node, (\<lambda>VARI. bAll(Node, (\<lambda>VARJ. ((~(a_grantunde_msga[VARI]))|(~(a_unlockunde_msga[VARJ])))))))&(bAll(Node, (\<lambda>VARI. ((~(a_holdsunde_locka[VARI]))|(~a_serverunde_holdsunde_locka))))&(bAll(Node, (\<lambda>VARI. bAll(Node, (\<lambda>VARJ. ((~(a_grantunde_msga[VARI]))|(~(a_holdsunde_locka[VARJ])))))))&(bAll(Node, (\<lambda>VARI. bAll(Node, (\<lambda>VARJ. ((~(a_holdsunde_locka[VARI]))|(~(a_unlockunde_msga[VARJ])))))))&(bAll(Node, (\<lambda>VARI. ((~(a_grantunde_msga[VARI]))|(~a_serverunde_holdsunde_locka))))&(bAll(Node, (\<lambda>VARI. ((~a_serverunde_holdsunde_locka)|(~(a_unlockunde_msga[VARI])))))&(bAll(Node, (\<lambda>VARI. bAll(Node, (\<lambda>VARJ. (((VARI=VARJ)|(~(a_grantunde_msga[VARJ])))|(~(a_grantunde_msga[VARI])))))))&bAll(Node, (\<lambda>VARI. bAll(Node, (\<lambda>VARJ. ((VARI=VARJ)|((~(a_unlockunde_msga[VARI]))|(~(a_unlockunde_msga[VARJ])))))))))))))))))&bEx(Node, (\<lambda>n. (((a_lockunde_msghash_primea=except(a_lockunde_msga, n, TRUE))&((a_grantunde_msghash_primea=a_grantunde_msga)&((a_holdsunde_lockhash_primea=a_holdsunde_locka)&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka)))))|((a_serverunde_holdsunde_locka&((a_lockunde_msga[n])&((a_serverunde_holdsunde_lockhash_primea=FALSE)&((a_lockunde_msghash_primea=except(a_lockunde_msga, n, FALSE))&((a_grantunde_msghash_primea=except(a_grantunde_msga, n, TRUE))&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_holdsunde_lockhash_primea=a_holdsunde_locka)))))))|(((a_grantunde_msga[n])&((a_grantunde_msghash_primea=except(a_grantunde_msga, n, FALSE))&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, n, TRUE))&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|(((a_holdsunde_locka[n])&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, n, FALSE))&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, n, TRUE))&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_grantunde_msghash_primea=a_grantunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|((a_unlockunde_msga[n])&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, n, FALSE))&((a_serverunde_holdsunde_lockhash_primea=TRUE)&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_grantunde_msghash_primea=a_grantunde_msga)&(a_holdsunde_lockhash_primea=a_holdsunde_locka)))))))))))))" (is "?z_hc&?z_hdp")
 using v'10 by blast
 have zenon_L1_: "(\\A zenon_Vea:((zenon_Vea \\in Node)=>((a_lockunde_msga[zenon_Vea]) \\in {TRUE, FALSE}))) ==> ((CHOOSE zenon_Vlha:(~((zenon_Vlha \\in Node)=>((a_lockunde_msghash_primea[zenon_Vlha]) \\in {TRUE, FALSE})))) \\in Node) ==> (~((a_lockunde_msghash_primea[(CHOOSE zenon_Vlha:(~((zenon_Vlha \\in Node)=>((a_lockunde_msghash_primea[zenon_Vlha]) \\in {TRUE, FALSE}))))]) \\in {TRUE, FALSE})) ==> ((a_lockunde_msghash_primea[(CHOOSE zenon_Vlha:(~((zenon_Vlha \\in Node)=>((a_lockunde_msghash_primea[zenon_Vlha]) \\in {TRUE, FALSE}))))])=(a_lockunde_msga[(CHOOSE zenon_Vlha:(~((zenon_Vlha \\in Node)=>((a_lockunde_msghash_primea[zenon_Vlha]) \\in {TRUE, FALSE}))))])) ==> FALSE" (is "?z_hga ==> ?z_hgg ==> ?z_hgo ==> ?z_hgr ==> FALSE")
 proof -
  assume z_Hga:"?z_hga" (is "\\A x : ?z_hgt(x)")
  assume z_Hgg:"?z_hgg"
  assume z_Hgo:"?z_hgo" (is "~?z_hgp")
  assume z_Hgr:"?z_hgr" (is "?z_hgq=?z_hgs")
  have z_Hgu: "?z_hgt((CHOOSE zenon_Vlha:(~((zenon_Vlha \\in Node)=>((a_lockunde_msghash_primea[zenon_Vlha]) \\in {TRUE, FALSE})))))" (is "_=>?z_hgv")
  by (rule zenon_all_0 [of "?z_hgt" "(CHOOSE zenon_Vlha:(~((zenon_Vlha \\in Node)=>((a_lockunde_msghash_primea[zenon_Vlha]) \\in {TRUE, FALSE}))))", OF z_Hga])
  show FALSE
  proof (rule zenon_imply [OF z_Hgu])
   assume z_Hgw:"(~?z_hgg)"
   show FALSE
   by (rule notE [OF z_Hgw z_Hgg])
  next
   assume z_Hgv:"?z_hgv"
   show FALSE
   proof (rule notE [OF z_Hgo])
    have z_Hgx: "(?z_hgs=?z_hgq)"
    by (rule sym [OF z_Hgr])
    have z_Hgp: "?z_hgp"
    by (rule subst [where P="(\<lambda>zenon_Vr. (zenon_Vr \\in {TRUE, FALSE}))", OF z_Hgx], fact z_Hgv)
    thus "?z_hgp" .
   qed
  qed
 qed
 have zenon_L2_: "(a_lockunde_msghash_primea=except(a_lockunde_msga, (CHOOSE x:((x \\in Node)&(((a_lockunde_msghash_primea=except(a_lockunde_msga, x, TRUE))&((a_grantunde_msghash_primea=a_grantunde_msga)&((a_holdsunde_lockhash_primea=a_holdsunde_locka)&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka)))))|((a_serverunde_holdsunde_locka&((a_lockunde_msga[x])&((a_serverunde_holdsunde_lockhash_primea=FALSE)&((a_lockunde_msghash_primea=except(a_lockunde_msga, x, FALSE))&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, TRUE))&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_holdsunde_lockhash_primea=a_holdsunde_locka)))))))|(((a_grantunde_msga[x])&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, FALSE))&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, TRUE))&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|(((a_holdsunde_locka[x])&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, FALSE))&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, TRUE))&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_grantunde_msghash_primea=a_grantunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|((a_unlockunde_msga[x])&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, FALSE))&((a_serverunde_holdsunde_lockhash_primea=TRUE)&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_grantunde_msghash_primea=a_grantunde_msga)&(a_holdsunde_lockhash_primea=a_holdsunde_locka)))))))))))), TRUE)) ==> (~(a_lockunde_msghash_primea \\in FuncSet(Node, {TRUE, FALSE}))) ==> (a_lockunde_msga \\in FuncSet(Node, {TRUE, FALSE})) ==> FALSE" (is "?z_hhb ==> ?z_hir ==> ?z_he ==> FALSE")
 proof -
  assume z_Hhb:"?z_hhb" (is "_=?z_hhc")
  assume z_Hir:"?z_hir" (is "~?z_his")
  assume z_He:"?z_he"
  have z_Hit: "(DOMAIN(a_lockunde_msga)=Node)" (is "?z_hiu=_")
  by (rule zenon_in_funcset_1 [of "a_lockunde_msga" "Node" "{TRUE, FALSE}", OF z_He])
  have z_Hit: "(?z_hiu=Node)"
  by (rule zenon_in_funcset_1 [of "a_lockunde_msga" "Node" "{TRUE, FALSE}", OF z_He])
  have z_Hga: "(\\A zenon_Vea:((zenon_Vea \\in Node)=>((a_lockunde_msga[zenon_Vea]) \\in {TRUE, FALSE})))" (is "\\A x : ?z_hgt(x)")
  by (rule zenon_in_funcset_2 [of "a_lockunde_msga" "Node" "{TRUE, FALSE}", OF z_He])
  have z_Hiv: "(((isAFcn(a_lockunde_msghash_primea)<=>isAFcn(?z_hhc))&(DOMAIN(a_lockunde_msghash_primea)=DOMAIN(?z_hhc)))&(\\A zenon_Vbra:((a_lockunde_msghash_primea[zenon_Vbra])=(?z_hhc[zenon_Vbra]))))" (is "?z_hiw&?z_hjd")
  by (rule zenon_funequal_0 [of "a_lockunde_msghash_primea" "?z_hhc", OF z_Hhb])
  have z_Hiw: "?z_hiw" (is "?z_hix&?z_hja")
  by (rule zenon_and_0 [OF z_Hiv])
  have z_Hjd: "?z_hjd" (is "\\A x : ?z_hji(x)")
  by (rule zenon_and_1 [OF z_Hiv])
  have z_Hix: "?z_hix" (is "?z_hiy<=>?z_hiz")
  by (rule zenon_and_0 [OF z_Hiw])
  show FALSE
  proof (rule zenon_equiv [OF z_Hix])
   assume z_Hjj:"(~?z_hiy)"
   assume z_Hjk:"(~?z_hiz)"
   show FALSE
   by (rule zenon_notisafcn_except [of "a_lockunde_msga" "(CHOOSE x:((x \\in Node)&(((a_lockunde_msghash_primea=except(a_lockunde_msga, x, TRUE))&((a_grantunde_msghash_primea=a_grantunde_msga)&((a_holdsunde_lockhash_primea=a_holdsunde_locka)&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka)))))|((a_serverunde_holdsunde_locka&((a_lockunde_msga[x])&((a_serverunde_holdsunde_lockhash_primea=FALSE)&((a_lockunde_msghash_primea=except(a_lockunde_msga, x, FALSE))&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, TRUE))&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_holdsunde_lockhash_primea=a_holdsunde_locka)))))))|(((a_grantunde_msga[x])&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, FALSE))&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, TRUE))&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|(((a_holdsunde_locka[x])&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, FALSE))&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, TRUE))&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_grantunde_msghash_primea=a_grantunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|((a_unlockunde_msga[x])&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, FALSE))&((a_serverunde_holdsunde_lockhash_primea=TRUE)&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_grantunde_msghash_primea=a_grantunde_msga)&(a_holdsunde_lockhash_primea=a_holdsunde_locka))))))))))))" "TRUE", OF z_Hjk])
  next
   assume z_Hiy:"?z_hiy"
   assume z_Hiz:"?z_hiz"
   show FALSE
   proof (rule zenon_notin_funcset [of "a_lockunde_msghash_primea" "Node" "{TRUE, FALSE}", OF z_Hir])
    assume z_Hjj:"(~?z_hiy)"
    show FALSE
    by (rule notE [OF z_Hjj z_Hiy])
   next
    assume z_Hjl:"(DOMAIN(a_lockunde_msghash_primea)~=Node)" (is "?z_hjb~=_")
    have z_Hjm: "(DOMAIN(?z_hhc)~=Node)" (is "?z_hjc~=_")
    by (rule subst [where P="(\<lambda>zenon_Vlw. (DOMAIN(zenon_Vlw)~=Node))", OF z_Hhb z_Hjl])
    have z_Hjr: "(?z_hiu~=Node)"
    by (rule zenon_domain_except_0 [of "(\<lambda>zenon_Vkw. (zenon_Vkw~=Node))" "a_lockunde_msga" "(CHOOSE x:((x \\in Node)&(((a_lockunde_msghash_primea=except(a_lockunde_msga, x, TRUE))&((a_grantunde_msghash_primea=a_grantunde_msga)&((a_holdsunde_lockhash_primea=a_holdsunde_locka)&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka)))))|((a_serverunde_holdsunde_locka&((a_lockunde_msga[x])&((a_serverunde_holdsunde_lockhash_primea=FALSE)&((a_lockunde_msghash_primea=except(a_lockunde_msga, x, FALSE))&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, TRUE))&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_holdsunde_lockhash_primea=a_holdsunde_locka)))))))|(((a_grantunde_msga[x])&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, FALSE))&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, TRUE))&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|(((a_holdsunde_locka[x])&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, FALSE))&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, TRUE))&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_grantunde_msghash_primea=a_grantunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|((a_unlockunde_msga[x])&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, FALSE))&((a_serverunde_holdsunde_lockhash_primea=TRUE)&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_grantunde_msghash_primea=a_grantunde_msga)&(a_holdsunde_lockhash_primea=a_holdsunde_locka))))))))))))" "TRUE", OF z_Hjm])
    show FALSE
    by (rule notE [OF z_Hjr z_Hit])
   next
    assume z_Hjv:"(~(\\A zenon_Vlha:((zenon_Vlha \\in Node)=>((a_lockunde_msghash_primea[zenon_Vlha]) \\in {TRUE, FALSE}))))" (is "~(\\A x : ?z_hjx(x))")
    have z_Hjy: "(\\E zenon_Vlha:(~((zenon_Vlha \\in Node)=>((a_lockunde_msghash_primea[zenon_Vlha]) \\in {TRUE, FALSE}))))" (is "\\E x : ?z_hjz(x)")
    by (rule zenon_notallex_0 [of "?z_hjx", OF z_Hjv])
    have z_Hka: "?z_hjz((CHOOSE zenon_Vlha:(~((zenon_Vlha \\in Node)=>((a_lockunde_msghash_primea[zenon_Vlha]) \\in {TRUE, FALSE})))))" (is "~(?z_hgg=>?z_hgp)")
    by (rule zenon_ex_choose_0 [of "?z_hjz", OF z_Hjy])
    have z_Hgg: "?z_hgg"
    by (rule zenon_notimply_0 [OF z_Hka])
    have z_Hgo: "(~?z_hgp)"
    by (rule zenon_notimply_1 [OF z_Hka])
    have z_Hkb: "((a_lockunde_msghash_primea[(CHOOSE zenon_Vlha:(~((zenon_Vlha \\in Node)=>((a_lockunde_msghash_primea[zenon_Vlha]) \\in {TRUE, FALSE}))))])~=TRUE)" (is "?z_hgq~=?z_hj")
    by (rule zenon_notin_addElt_0 [of "?z_hgq" "?z_hj" "{FALSE}", OF z_Hgo])
    have z_Hkd: "((CHOOSE zenon_Vlha:(~((zenon_Vlha \\in Node)=>((a_lockunde_msghash_primea[zenon_Vlha]) \\in {?z_hj, FALSE})))) \\in ?z_hiu)" (is "?z_hkd")
    by (rule ssubst [where P="(\<lambda>zenon_Vagb. ((CHOOSE zenon_Vlha:(~((zenon_Vlha \\in Node)=>((a_lockunde_msghash_primea[zenon_Vlha]) \\in {?z_hj, FALSE})))) \\in zenon_Vagb))", OF z_Hit z_Hgg])
    have z_Hkh: "?z_hji((CHOOSE zenon_Vlha:(~((zenon_Vlha \\in Node)=>((a_lockunde_msghash_primea[zenon_Vlha]) \\in {?z_hj, FALSE})))))" (is "_=?z_hki")
    by (rule zenon_all_0 [of "?z_hji" "(CHOOSE zenon_Vlha:(~((zenon_Vlha \\in Node)=>((a_lockunde_msghash_primea[zenon_Vlha]) \\in {?z_hj, FALSE}))))", OF z_Hjd])
    show FALSE
    proof (rule zenon_fapplyexcept [of "(\<lambda>zenon_Vqhb. (?z_hgq=zenon_Vqhb))" "a_lockunde_msga" "(CHOOSE x:((x \\in Node)&(((a_lockunde_msghash_primea=except(a_lockunde_msga, x, ?z_hj))&((a_grantunde_msghash_primea=a_grantunde_msga)&((a_holdsunde_lockhash_primea=a_holdsunde_locka)&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka)))))|((a_serverunde_holdsunde_locka&((a_lockunde_msga[x])&((a_serverunde_holdsunde_lockhash_primea=FALSE)&((a_lockunde_msghash_primea=except(a_lockunde_msga, x, FALSE))&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, ?z_hj))&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_holdsunde_lockhash_primea=a_holdsunde_locka)))))))|(((a_grantunde_msga[x])&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, FALSE))&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, ?z_hj))&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|(((a_holdsunde_locka[x])&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, FALSE))&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, ?z_hj))&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_grantunde_msghash_primea=a_grantunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|((a_unlockunde_msga[x])&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, FALSE))&((a_serverunde_holdsunde_lockhash_primea=?z_hj)&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_grantunde_msghash_primea=a_grantunde_msga)&(a_holdsunde_lockhash_primea=a_holdsunde_locka))))))))))))" "?z_hj" "(CHOOSE zenon_Vlha:(~((zenon_Vlha \\in Node)=>((a_lockunde_msghash_primea[zenon_Vlha]) \\in {?z_hj, FALSE}))))", OF z_Hkh])
     assume z_Hkd:"?z_hkd"
     assume z_Hkm:"((CHOOSE x:((x \\in Node)&(((a_lockunde_msghash_primea=except(a_lockunde_msga, x, ?z_hj))&((a_grantunde_msghash_primea=a_grantunde_msga)&((a_holdsunde_lockhash_primea=a_holdsunde_locka)&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka)))))|((a_serverunde_holdsunde_locka&((a_lockunde_msga[x])&((a_serverunde_holdsunde_lockhash_primea=FALSE)&((a_lockunde_msghash_primea=except(a_lockunde_msga, x, FALSE))&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, ?z_hj))&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_holdsunde_lockhash_primea=a_holdsunde_locka)))))))|(((a_grantunde_msga[x])&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, FALSE))&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, ?z_hj))&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|(((a_holdsunde_locka[x])&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, FALSE))&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, ?z_hj))&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_grantunde_msghash_primea=a_grantunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|((a_unlockunde_msga[x])&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, FALSE))&((a_serverunde_holdsunde_lockhash_primea=?z_hj)&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_grantunde_msghash_primea=a_grantunde_msga)&(a_holdsunde_lockhash_primea=a_holdsunde_locka))))))))))))=(CHOOSE zenon_Vlha:(~((zenon_Vlha \\in Node)=>((a_lockunde_msghash_primea[zenon_Vlha]) \\in {?z_hj, FALSE})))))" (is "?z_hhd=?z_hgh")
     assume z_Hkn:"(?z_hgq=?z_hj)"
     show FALSE
     by (rule notE [OF z_Hkb z_Hkn])
    next
     assume z_Hkd:"?z_hkd"
     assume z_Hko:"((CHOOSE x:((x \\in Node)&(((a_lockunde_msghash_primea=except(a_lockunde_msga, x, ?z_hj))&((a_grantunde_msghash_primea=a_grantunde_msga)&((a_holdsunde_lockhash_primea=a_holdsunde_locka)&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka)))))|((a_serverunde_holdsunde_locka&((a_lockunde_msga[x])&((a_serverunde_holdsunde_lockhash_primea=FALSE)&((a_lockunde_msghash_primea=except(a_lockunde_msga, x, FALSE))&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, ?z_hj))&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_holdsunde_lockhash_primea=a_holdsunde_locka)))))))|(((a_grantunde_msga[x])&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, FALSE))&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, ?z_hj))&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|(((a_holdsunde_locka[x])&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, FALSE))&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, ?z_hj))&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_grantunde_msghash_primea=a_grantunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|((a_unlockunde_msga[x])&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, FALSE))&((a_serverunde_holdsunde_lockhash_primea=?z_hj)&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_grantunde_msghash_primea=a_grantunde_msga)&(a_holdsunde_lockhash_primea=a_holdsunde_locka))))))))))))~=(CHOOSE zenon_Vlha:(~((zenon_Vlha \\in Node)=>((a_lockunde_msghash_primea[zenon_Vlha]) \\in {?z_hj, FALSE})))))" (is "?z_hhd~=?z_hgh")
     assume z_Hgr:"(?z_hgq=(a_lockunde_msga[?z_hgh]))" (is "_=?z_hgs")
     show FALSE
     by (rule zenon_L1_ [OF z_Hga z_Hgg z_Hgo z_Hgr])
    next
     assume z_Hkp:"(~?z_hkd)"
     show FALSE
     by (rule notE [OF z_Hkp z_Hkd])
    qed
   qed
  qed
 qed
 have zenon_L3_: "(~(a_grantunde_msghash_primea \\in FuncSet(Node, {TRUE, FALSE}))) ==> (a_grantunde_msga \\in FuncSet(Node, {TRUE, FALSE})) ==> (a_grantunde_msghash_primea=a_grantunde_msga) ==> FALSE" (is "?z_hkq ==> ?z_hm ==> ?z_hdy ==> FALSE")
 proof -
  assume z_Hkq:"?z_hkq" (is "~?z_hkr")
  assume z_Hm:"?z_hm"
  assume z_Hdy:"?z_hdy"
  show FALSE
  proof (rule notE [OF z_Hkq])
   have z_Hks: "(a_grantunde_msga=a_grantunde_msghash_primea)"
   by (rule sym [OF z_Hdy])
   have z_Hkr: "?z_hkr"
   by (rule subst [where P="(\<lambda>zenon_Vzfe. (zenon_Vzfe \\in FuncSet(Node, {TRUE, FALSE})))", OF z_Hks], fact z_Hm)
   thus "?z_hkr" .
  qed
 qed
 have zenon_L4_: "(~(a_unlockunde_msghash_primea \\in FuncSet(Node, {TRUE, FALSE}))) ==> (a_unlockunde_msga \\in FuncSet(Node, {TRUE, FALSE})) ==> (a_unlockunde_msghash_primea=a_unlockunde_msga) ==> FALSE" (is "?z_hkw ==> ?z_hp ==> ?z_hee ==> FALSE")
 proof -
  assume z_Hkw:"?z_hkw" (is "~?z_hkx")
  assume z_Hp:"?z_hp"
  assume z_Hee:"?z_hee"
  show FALSE
  proof (rule notE [OF z_Hkw])
   have z_Hky: "(a_unlockunde_msga=a_unlockunde_msghash_primea)"
   by (rule sym [OF z_Hee])
   have z_Hkx: "?z_hkx"
   by (rule subst [where P="(\<lambda>zenon_Vzfe. (zenon_Vzfe \\in FuncSet(Node, {TRUE, FALSE})))", OF z_Hky], fact z_Hp)
   thus "?z_hkx" .
  qed
 qed
 have zenon_L5_: "(~(a_holdsunde_lockhash_primea \\in FuncSet(Node, {TRUE, FALSE}))) ==> (a_holdsunde_locka \\in FuncSet(Node, {TRUE, FALSE})) ==> (a_holdsunde_lockhash_primea=a_holdsunde_locka) ==> FALSE" (is "?z_hkz ==> ?z_hs ==> ?z_heb ==> FALSE")
 proof -
  assume z_Hkz:"?z_hkz" (is "~?z_hla")
  assume z_Hs:"?z_hs"
  assume z_Heb:"?z_heb"
  show FALSE
  proof (rule notE [OF z_Hkz])
   have z_Hlb: "(a_holdsunde_locka=a_holdsunde_lockhash_primea)"
   by (rule sym [OF z_Heb])
   have z_Hla: "?z_hla"
   by (rule subst [where P="(\<lambda>zenon_Vzfe. (zenon_Vzfe \\in FuncSet(Node, {TRUE, FALSE})))", OF z_Hlb], fact z_Hs)
   thus "?z_hla" .
  qed
 qed
 have zenon_L6_: "(~(a_serverunde_holdsunde_lockhash_primea \\in {TRUE, FALSE})) ==> (a_serverunde_holdsunde_locka=TRUE) ==> (a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka) ==> FALSE" (is "?z_hlc ==> ?z_hle ==> ?z_heg ==> FALSE")
 proof -
  assume z_Hlc:"?z_hlc" (is "~?z_hld")
  assume z_Hle:"?z_hle" (is "_=?z_hj")
  assume z_Heg:"?z_heg"
  have z_Hlf: "(a_serverunde_holdsunde_lockhash_primea~=?z_hj)"
  by (rule zenon_notin_addElt_0 [of "a_serverunde_holdsunde_lockhash_primea" "?z_hj" "{FALSE}", OF z_Hlc])
  show FALSE
  proof (rule notE [OF z_Hlf])
   have z_Hfx: "(a_serverunde_holdsunde_lockhash_primea=?z_hj)"
   by (rule subst [where P="(\<lambda>zenon_Vcge. (a_serverunde_holdsunde_lockhash_primea=zenon_Vcge))", OF z_Hle], fact z_Heg)
   thus "(a_serverunde_holdsunde_lockhash_primea=?z_hj)" .
  qed
 qed
 have zenon_L7_: "(~(a_serverunde_holdsunde_lockhash_primea \\in {TRUE, FALSE})) ==> (a_serverunde_holdsunde_locka=FALSE) ==> (a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka) ==> FALSE" (is "?z_hlc ==> ?z_hlj ==> ?z_heg ==> FALSE")
 proof -
  assume z_Hlc:"?z_hlc" (is "~?z_hld")
  assume z_Hlj:"?z_hlj" (is "_=?z_hk")
  assume z_Heg:"?z_heg"
  have z_Hlk: "(~(a_serverunde_holdsunde_lockhash_primea \\in {?z_hk}))" (is "~?z_hll")
  by (rule zenon_notin_addElt_1 [of "a_serverunde_holdsunde_lockhash_primea" "TRUE" "{?z_hk}", OF z_Hlc])
  have z_Hlm: "(a_serverunde_holdsunde_lockhash_primea~=?z_hk)"
  by (rule zenon_notin_addElt_0 [of "a_serverunde_holdsunde_lockhash_primea" "?z_hk" "{}", OF z_Hlk])
  show FALSE
  proof (rule notE [OF z_Hlm])
   have z_Hen: "(a_serverunde_holdsunde_lockhash_primea=?z_hk)"
   by (rule subst [where P="(\<lambda>zenon_Vcge. (a_serverunde_holdsunde_lockhash_primea=zenon_Vcge))", OF z_Hlj], fact z_Heg)
   thus "(a_serverunde_holdsunde_lockhash_primea=?z_hk)" .
  qed
 qed
 have zenon_L8_: "(\\A zenon_Vba:((zenon_Vba \\in Node)=>((a_grantunde_msga[zenon_Vba]) \\in {TRUE, FALSE}))) ==> ((CHOOSE zenon_Vvw:(~((zenon_Vvw \\in Node)=>((a_grantunde_msghash_primea[zenon_Vvw]) \\in {TRUE, FALSE})))) \\in Node) ==> (~((a_grantunde_msghash_primea[(CHOOSE zenon_Vvw:(~((zenon_Vvw \\in Node)=>((a_grantunde_msghash_primea[zenon_Vvw]) \\in {TRUE, FALSE}))))]) \\in {TRUE, FALSE})) ==> ((a_grantunde_msghash_primea[(CHOOSE zenon_Vvw:(~((zenon_Vvw \\in Node)=>((a_grantunde_msghash_primea[zenon_Vvw]) \\in {TRUE, FALSE}))))])=(a_grantunde_msga[(CHOOSE zenon_Vvw:(~((zenon_Vvw \\in Node)=>((a_grantunde_msghash_primea[zenon_Vvw]) \\in {TRUE, FALSE}))))])) ==> FALSE" (is "?z_hlo ==> ?z_hlu ==> ?z_hmc ==> ?z_hmf ==> FALSE")
 proof -
  assume z_Hlo:"?z_hlo" (is "\\A x : ?z_hmh(x)")
  assume z_Hlu:"?z_hlu"
  assume z_Hmc:"?z_hmc" (is "~?z_hmd")
  assume z_Hmf:"?z_hmf" (is "?z_hme=?z_hmg")
  have z_Hmi: "?z_hmh((CHOOSE zenon_Vvw:(~((zenon_Vvw \\in Node)=>((a_grantunde_msghash_primea[zenon_Vvw]) \\in {TRUE, FALSE})))))" (is "_=>?z_hmj")
  by (rule zenon_all_0 [of "?z_hmh" "(CHOOSE zenon_Vvw:(~((zenon_Vvw \\in Node)=>((a_grantunde_msghash_primea[zenon_Vvw]) \\in {TRUE, FALSE}))))", OF z_Hlo])
  show FALSE
  proof (rule zenon_imply [OF z_Hmi])
   assume z_Hmk:"(~?z_hlu)"
   show FALSE
   by (rule notE [OF z_Hmk z_Hlu])
  next
   assume z_Hmj:"?z_hmj"
   show FALSE
   proof (rule notE [OF z_Hmc])
    have z_Hml: "(?z_hmg=?z_hme)"
    by (rule sym [OF z_Hmf])
    have z_Hmd: "?z_hmd"
    by (rule subst [where P="(\<lambda>zenon_Vr. (zenon_Vr \\in {TRUE, FALSE}))", OF z_Hml], fact z_Hmj)
    thus "?z_hmd" .
   qed
  qed
 qed
 have zenon_L9_: "(\\A zenon_Vekd:((a_grantunde_msghash_primea[zenon_Vekd])=(except(a_grantunde_msga, (CHOOSE x:((x \\in Node)&(((a_lockunde_msghash_primea=except(a_lockunde_msga, x, TRUE))&((a_grantunde_msghash_primea=a_grantunde_msga)&((a_holdsunde_lockhash_primea=a_holdsunde_locka)&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka)))))|((a_serverunde_holdsunde_locka&((a_lockunde_msga[x])&((a_serverunde_holdsunde_lockhash_primea=FALSE)&((a_lockunde_msghash_primea=except(a_lockunde_msga, x, FALSE))&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, TRUE))&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_holdsunde_lockhash_primea=a_holdsunde_locka)))))))|(((a_grantunde_msga[x])&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, FALSE))&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, TRUE))&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|(((a_holdsunde_locka[x])&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, FALSE))&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, TRUE))&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_grantunde_msghash_primea=a_grantunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|((a_unlockunde_msga[x])&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, FALSE))&((a_serverunde_holdsunde_lockhash_primea=TRUE)&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_grantunde_msghash_primea=a_grantunde_msga)&(a_holdsunde_lockhash_primea=a_holdsunde_locka)))))))))))), TRUE)[zenon_Vekd]))) ==> ((CHOOSE x:((x \\in Node)&(((a_lockunde_msghash_primea=except(a_lockunde_msga, x, TRUE))&((a_grantunde_msghash_primea=a_grantunde_msga)&((a_holdsunde_lockhash_primea=a_holdsunde_locka)&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka)))))|((a_serverunde_holdsunde_locka&((a_lockunde_msga[x])&((a_serverunde_holdsunde_lockhash_primea=FALSE)&((a_lockunde_msghash_primea=except(a_lockunde_msga, x, FALSE))&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, TRUE))&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_holdsunde_lockhash_primea=a_holdsunde_locka)))))))|(((a_grantunde_msga[x])&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, FALSE))&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, TRUE))&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|(((a_holdsunde_locka[x])&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, FALSE))&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, TRUE))&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_grantunde_msghash_primea=a_grantunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|((a_unlockunde_msga[x])&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, FALSE))&((a_serverunde_holdsunde_lockhash_primea=TRUE)&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_grantunde_msghash_primea=a_grantunde_msga)&(a_holdsunde_lockhash_primea=a_holdsunde_locka))))))))))))~=(CHOOSE zenon_Vvw:(~((zenon_Vvw \\in Node)=>((a_grantunde_msghash_primea[zenon_Vvw]) \\in {TRUE, FALSE}))))) ==> (\\A zenon_Vba:((zenon_Vba \\in Node)=>((a_grantunde_msga[zenon_Vba]) \\in {TRUE, FALSE}))) ==> ((CHOOSE zenon_Vvw:(~((zenon_Vvw \\in Node)=>((a_grantunde_msghash_primea[zenon_Vvw]) \\in {TRUE, FALSE})))) \\in Node) ==> (~((a_grantunde_msghash_primea[(CHOOSE zenon_Vvw:(~((zenon_Vvw \\in Node)=>((a_grantunde_msghash_primea[zenon_Vvw]) \\in {TRUE, FALSE}))))]) \\in {TRUE, FALSE})) ==> ((CHOOSE zenon_Vvw:(~((zenon_Vvw \\in Node)=>((a_grantunde_msghash_primea[zenon_Vvw]) \\in {TRUE, FALSE})))) \\in DOMAIN(a_grantunde_msga)) ==> FALSE" (is "?z_hmm ==> ?z_hms ==> ?z_hlo ==> ?z_hlu ==> ?z_hmc ==> ?z_hmt ==> FALSE")
 proof -
  assume z_Hmm:"?z_hmm" (is "\\A x : ?z_hmv(x)")
  assume z_Hms:"?z_hms" (is "?z_hhd~=?z_hlv")
  assume z_Hlo:"?z_hlo" (is "\\A x : ?z_hmh(x)")
  assume z_Hlu:"?z_hlu"
  assume z_Hmc:"?z_hmc" (is "~?z_hmd")
  assume z_Hmt:"?z_hmt"
  have z_Hmw: "?z_hmv(?z_hlv)" (is "?z_hme=?z_hmx")
  by (rule zenon_all_0 [of "?z_hmv" "?z_hlv", OF z_Hmm])
  show FALSE
  proof (rule zenon_fapplyexcept [of "(\<lambda>zenon_Vchd. (?z_hme=zenon_Vchd))" "a_grantunde_msga" "?z_hhd" "TRUE" "?z_hlv", OF z_Hmw])
   assume z_Hmt:"?z_hmt"
   assume z_Hnb:"(?z_hhd=?z_hlv)"
   assume z_Hnc:"(?z_hme=TRUE)" (is "_=?z_hj")
   show FALSE
   by (rule notE [OF z_Hms z_Hnb])
  next
   assume z_Hmt:"?z_hmt"
   assume z_Hms:"?z_hms"
   assume z_Hmf:"(?z_hme=(a_grantunde_msga[?z_hlv]))" (is "_=?z_hmg")
   show FALSE
   by (rule zenon_L8_ [OF z_Hlo z_Hlu z_Hmc z_Hmf])
  next
   assume z_Hnd:"(~?z_hmt)"
   show FALSE
   by (rule notE [OF z_Hnd z_Hmt])
  qed
 qed
 have zenon_L10_: "(~(a_lockunde_msghash_primea \\in FuncSet(Node, {TRUE, FALSE}))) ==> (a_lockunde_msga \\in FuncSet(Node, {TRUE, FALSE})) ==> (a_lockunde_msghash_primea=a_lockunde_msga) ==> FALSE" (is "?z_hir ==> ?z_he ==> ?z_hff ==> FALSE")
 proof -
  assume z_Hir:"?z_hir" (is "~?z_his")
  assume z_He:"?z_he"
  assume z_Hff:"?z_hff"
  show FALSE
  proof (rule notE [OF z_Hir])
   have z_Hne: "(a_lockunde_msga=a_lockunde_msghash_primea)"
   by (rule sym [OF z_Hff])
   have z_His: "?z_his"
   by (rule subst [where P="(\<lambda>zenon_Vzfe. (zenon_Vzfe \\in FuncSet(Node, {TRUE, FALSE})))", OF z_Hne], fact z_He)
   thus "?z_his" .
  qed
 qed
 have zenon_L11_: "(\\A zenon_Vqmc:((a_grantunde_msghash_primea[zenon_Vqmc])=(except(a_grantunde_msga, (CHOOSE x:((x \\in Node)&(((a_lockunde_msghash_primea=except(a_lockunde_msga, x, TRUE))&((a_grantunde_msghash_primea=a_grantunde_msga)&((a_holdsunde_lockhash_primea=a_holdsunde_locka)&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka)))))|((a_serverunde_holdsunde_locka&((a_lockunde_msga[x])&((a_serverunde_holdsunde_lockhash_primea=FALSE)&((a_lockunde_msghash_primea=except(a_lockunde_msga, x, FALSE))&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, TRUE))&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_holdsunde_lockhash_primea=a_holdsunde_locka)))))))|(((a_grantunde_msga[x])&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, FALSE))&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, TRUE))&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|(((a_holdsunde_locka[x])&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, FALSE))&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, TRUE))&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_grantunde_msghash_primea=a_grantunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|((a_unlockunde_msga[x])&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, FALSE))&((a_serverunde_holdsunde_lockhash_primea=TRUE)&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_grantunde_msghash_primea=a_grantunde_msga)&(a_holdsunde_lockhash_primea=a_holdsunde_locka)))))))))))), FALSE)[zenon_Vqmc]))) ==> ((CHOOSE x:((x \\in Node)&(((a_lockunde_msghash_primea=except(a_lockunde_msga, x, TRUE))&((a_grantunde_msghash_primea=a_grantunde_msga)&((a_holdsunde_lockhash_primea=a_holdsunde_locka)&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka)))))|((a_serverunde_holdsunde_locka&((a_lockunde_msga[x])&((a_serverunde_holdsunde_lockhash_primea=FALSE)&((a_lockunde_msghash_primea=except(a_lockunde_msga, x, FALSE))&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, TRUE))&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_holdsunde_lockhash_primea=a_holdsunde_locka)))))))|(((a_grantunde_msga[x])&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, FALSE))&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, TRUE))&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|(((a_holdsunde_locka[x])&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, FALSE))&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, TRUE))&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_grantunde_msghash_primea=a_grantunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|((a_unlockunde_msga[x])&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, FALSE))&((a_serverunde_holdsunde_lockhash_primea=TRUE)&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_grantunde_msghash_primea=a_grantunde_msga)&(a_holdsunde_lockhash_primea=a_holdsunde_locka))))))))))))~=(CHOOSE zenon_Vvw:(~((zenon_Vvw \\in Node)=>((a_grantunde_msghash_primea[zenon_Vvw]) \\in {TRUE, FALSE}))))) ==> (\\A zenon_Vba:((zenon_Vba \\in Node)=>((a_grantunde_msga[zenon_Vba]) \\in {TRUE, FALSE}))) ==> ((CHOOSE zenon_Vvw:(~((zenon_Vvw \\in Node)=>((a_grantunde_msghash_primea[zenon_Vvw]) \\in {TRUE, FALSE})))) \\in Node) ==> (~((a_grantunde_msghash_primea[(CHOOSE zenon_Vvw:(~((zenon_Vvw \\in Node)=>((a_grantunde_msghash_primea[zenon_Vvw]) \\in {TRUE, FALSE}))))]) \\in {TRUE, FALSE})) ==> ((CHOOSE zenon_Vvw:(~((zenon_Vvw \\in Node)=>((a_grantunde_msghash_primea[zenon_Vvw]) \\in {TRUE, FALSE})))) \\in DOMAIN(a_grantunde_msga)) ==> FALSE" (is "?z_hnf ==> ?z_hms ==> ?z_hlo ==> ?z_hlu ==> ?z_hmc ==> ?z_hmt ==> FALSE")
 proof -
  assume z_Hnf:"?z_hnf" (is "\\A x : ?z_hnl(x)")
  assume z_Hms:"?z_hms" (is "?z_hhd~=?z_hlv")
  assume z_Hlo:"?z_hlo" (is "\\A x : ?z_hmh(x)")
  assume z_Hlu:"?z_hlu"
  assume z_Hmc:"?z_hmc" (is "~?z_hmd")
  assume z_Hmt:"?z_hmt"
  have z_Hnm: "?z_hnl(?z_hlv)" (is "?z_hme=?z_hnn")
  by (rule zenon_all_0 [of "?z_hnl" "?z_hlv", OF z_Hnf])
  show FALSE
  proof (rule zenon_fapplyexcept [of "(\<lambda>zenon_Vchd. (?z_hme=zenon_Vchd))" "a_grantunde_msga" "?z_hhd" "FALSE" "?z_hlv", OF z_Hnm])
   assume z_Hmt:"?z_hmt"
   assume z_Hnb:"(?z_hhd=?z_hlv)"
   assume z_Hno:"(?z_hme=FALSE)" (is "_=?z_hk")
   show FALSE
   by (rule notE [OF z_Hms z_Hnb])
  next
   assume z_Hmt:"?z_hmt"
   assume z_Hms:"?z_hms"
   assume z_Hmf:"(?z_hme=(a_grantunde_msga[?z_hlv]))" (is "_=?z_hmg")
   show FALSE
   by (rule zenon_L8_ [OF z_Hlo z_Hlu z_Hmc z_Hmf])
  next
   assume z_Hnd:"(~?z_hmt)"
   show FALSE
   by (rule notE [OF z_Hnd z_Hmt])
  qed
 qed
 have zenon_L12_: "(a_grantunde_msga \\in FuncSet(Node, {TRUE, FALSE})) ==> (~(a_grantunde_msghash_primea \\in FuncSet(Node, {TRUE, FALSE}))) ==> (a_grantunde_msghash_primea=except(a_grantunde_msga, (CHOOSE x:((x \\in Node)&(((a_lockunde_msghash_primea=except(a_lockunde_msga, x, TRUE))&((a_grantunde_msghash_primea=a_grantunde_msga)&((a_holdsunde_lockhash_primea=a_holdsunde_locka)&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka)))))|((a_serverunde_holdsunde_locka&((a_lockunde_msga[x])&((a_serverunde_holdsunde_lockhash_primea=FALSE)&((a_lockunde_msghash_primea=except(a_lockunde_msga, x, FALSE))&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, TRUE))&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_holdsunde_lockhash_primea=a_holdsunde_locka)))))))|(((a_grantunde_msga[x])&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, FALSE))&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, TRUE))&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|(((a_holdsunde_locka[x])&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, FALSE))&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, TRUE))&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_grantunde_msghash_primea=a_grantunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|((a_unlockunde_msga[x])&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, FALSE))&((a_serverunde_holdsunde_lockhash_primea=TRUE)&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_grantunde_msghash_primea=a_grantunde_msga)&(a_holdsunde_lockhash_primea=a_holdsunde_locka)))))))))))), FALSE)) ==> (a_holdsunde_lockhash_primea=except(a_holdsunde_locka, (CHOOSE x:((x \\in Node)&(((a_lockunde_msghash_primea=except(a_lockunde_msga, x, TRUE))&((a_grantunde_msghash_primea=a_grantunde_msga)&((a_holdsunde_lockhash_primea=a_holdsunde_locka)&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka)))))|((a_serverunde_holdsunde_locka&((a_lockunde_msga[x])&((a_serverunde_holdsunde_lockhash_primea=FALSE)&((a_lockunde_msghash_primea=except(a_lockunde_msga, x, FALSE))&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, TRUE))&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_holdsunde_lockhash_primea=a_holdsunde_locka)))))))|(((a_grantunde_msga[x])&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, FALSE))&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, TRUE))&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|(((a_holdsunde_locka[x])&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, FALSE))&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, TRUE))&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_grantunde_msghash_primea=a_grantunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|((a_unlockunde_msga[x])&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, FALSE))&((a_serverunde_holdsunde_lockhash_primea=TRUE)&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_grantunde_msghash_primea=a_grantunde_msga)&(a_holdsunde_lockhash_primea=a_holdsunde_locka)))))))))))), TRUE)) ==> (a_holdsunde_locka \\in FuncSet(Node, {TRUE, FALSE})) ==> FALSE" (is "?z_hm ==> ?z_hkq ==> ?z_hnp ==> ?z_hnq ==> ?z_hs ==> FALSE")
 proof -
  assume z_Hm:"?z_hm"
  assume z_Hkq:"?z_hkq" (is "~?z_hkr")
  assume z_Hnp:"?z_hnp" (is "_=?z_hnk")
  assume z_Hnq:"?z_hnq" (is "_=?z_hnr")
  assume z_Hs:"?z_hs"
  have z_Hns: "(DOMAIN(a_grantunde_msga)=Node)" (is "?z_hmu=_")
  by (rule zenon_in_funcset_1 [of "a_grantunde_msga" "Node" "{TRUE, FALSE}", OF z_Hm])
  have z_Hnt: "(DOMAIN(a_holdsunde_locka)=Node)" (is "?z_hnu=_")
  by (rule zenon_in_funcset_1 [of "a_holdsunde_locka" "Node" "{TRUE, FALSE}", OF z_Hs])
  have z_Hns: "(?z_hmu=Node)"
  by (rule zenon_in_funcset_1 [of "a_grantunde_msga" "Node" "{TRUE, FALSE}", OF z_Hm])
  have z_Hlo: "(\\A zenon_Vba:((zenon_Vba \\in Node)=>((a_grantunde_msga[zenon_Vba]) \\in {TRUE, FALSE})))" (is "\\A x : ?z_hmh(x)")
  by (rule zenon_in_funcset_2 [of "a_grantunde_msga" "Node" "{TRUE, FALSE}", OF z_Hm])
  have z_Hnv: "(((isAFcn(a_holdsunde_lockhash_primea)<=>isAFcn(?z_hnr))&(DOMAIN(a_holdsunde_lockhash_primea)=DOMAIN(?z_hnr)))&(\\A zenon_Vomc:((a_holdsunde_lockhash_primea[zenon_Vomc])=(?z_hnr[zenon_Vomc]))))" (is "?z_hnw&?z_hod")
  by (rule zenon_funequal_0 [of "a_holdsunde_lockhash_primea" "?z_hnr", OF z_Hnq])
  have z_Hod: "?z_hod" (is "\\A x : ?z_hoi(x)")
  by (rule zenon_and_1 [OF z_Hnv])
  have z_Hoj: "(((isAFcn(a_grantunde_msghash_primea)<=>isAFcn(?z_hnk))&(DOMAIN(a_grantunde_msghash_primea)=DOMAIN(?z_hnk)))&(\\A zenon_Vqmc:((a_grantunde_msghash_primea[zenon_Vqmc])=(?z_hnk[zenon_Vqmc]))))" (is "?z_hok&?z_hnf")
  by (rule zenon_funequal_0 [of "a_grantunde_msghash_primea" "?z_hnk", OF z_Hnp])
  have z_Hok: "?z_hok" (is "?z_hol&?z_hoo")
  by (rule zenon_and_0 [OF z_Hoj])
  have z_Hnf: "?z_hnf" (is "\\A x : ?z_hnl(x)")
  by (rule zenon_and_1 [OF z_Hoj])
  have z_Hol: "?z_hol" (is "?z_hom<=>?z_hon")
  by (rule zenon_and_0 [OF z_Hok])
  show FALSE
  proof (rule zenon_equiv [OF z_Hol])
   assume z_Hor:"(~?z_hom)"
   assume z_Hos:"(~?z_hon)"
   show FALSE
   by (rule zenon_notisafcn_except [of "a_grantunde_msga" "(CHOOSE x:((x \\in Node)&(((a_lockunde_msghash_primea=except(a_lockunde_msga, x, TRUE))&((a_grantunde_msghash_primea=a_grantunde_msga)&((a_holdsunde_lockhash_primea=a_holdsunde_locka)&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka)))))|((a_serverunde_holdsunde_locka&((a_lockunde_msga[x])&((a_serverunde_holdsunde_lockhash_primea=FALSE)&((a_lockunde_msghash_primea=except(a_lockunde_msga, x, FALSE))&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, TRUE))&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_holdsunde_lockhash_primea=a_holdsunde_locka)))))))|(((a_grantunde_msga[x])&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, FALSE))&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, TRUE))&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|(((a_holdsunde_locka[x])&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, FALSE))&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, TRUE))&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_grantunde_msghash_primea=a_grantunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|((a_unlockunde_msga[x])&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, FALSE))&((a_serverunde_holdsunde_lockhash_primea=TRUE)&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_grantunde_msghash_primea=a_grantunde_msga)&(a_holdsunde_lockhash_primea=a_holdsunde_locka))))))))))))" "FALSE", OF z_Hos])
  next
   assume z_Hom:"?z_hom"
   assume z_Hon:"?z_hon"
   show FALSE
   proof (rule zenon_notin_funcset [of "a_grantunde_msghash_primea" "Node" "{TRUE, FALSE}", OF z_Hkq])
    assume z_Hor:"(~?z_hom)"
    show FALSE
    by (rule notE [OF z_Hor z_Hom])
   next
    assume z_Hot:"(DOMAIN(a_grantunde_msghash_primea)~=Node)" (is "?z_hop~=_")
    have z_Hou: "(DOMAIN(?z_hnk)~=Node)" (is "?z_hoq~=_")
    by (rule subst [where P="(\<lambda>zenon_Vlw. (DOMAIN(zenon_Vlw)~=Node))", OF z_Hnp z_Hot])
    have z_Hov: "(?z_hmu~=Node)"
    by (rule zenon_domain_except_0 [of "(\<lambda>zenon_Vkw. (zenon_Vkw~=Node))" "a_grantunde_msga" "(CHOOSE x:((x \\in Node)&(((a_lockunde_msghash_primea=except(a_lockunde_msga, x, TRUE))&((a_grantunde_msghash_primea=a_grantunde_msga)&((a_holdsunde_lockhash_primea=a_holdsunde_locka)&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka)))))|((a_serverunde_holdsunde_locka&((a_lockunde_msga[x])&((a_serverunde_holdsunde_lockhash_primea=FALSE)&((a_lockunde_msghash_primea=except(a_lockunde_msga, x, FALSE))&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, TRUE))&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_holdsunde_lockhash_primea=a_holdsunde_locka)))))))|(((a_grantunde_msga[x])&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, FALSE))&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, TRUE))&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|(((a_holdsunde_locka[x])&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, FALSE))&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, TRUE))&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_grantunde_msghash_primea=a_grantunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|((a_unlockunde_msga[x])&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, FALSE))&((a_serverunde_holdsunde_lockhash_primea=TRUE)&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_grantunde_msghash_primea=a_grantunde_msga)&(a_holdsunde_lockhash_primea=a_holdsunde_locka))))))))))))" "FALSE", OF z_Hou])
    show FALSE
    by (rule notE [OF z_Hov z_Hns])
   next
    assume z_How:"(~(\\A zenon_Vvw:((zenon_Vvw \\in Node)=>((a_grantunde_msghash_primea[zenon_Vvw]) \\in {TRUE, FALSE}))))" (is "~(\\A x : ?z_hoy(x))")
    have z_Hoz: "(\\E zenon_Vvw:(~((zenon_Vvw \\in Node)=>((a_grantunde_msghash_primea[zenon_Vvw]) \\in {TRUE, FALSE}))))" (is "\\E x : ?z_hpa(x)")
    by (rule zenon_notallex_0 [of "?z_hoy", OF z_How])
    have z_Hpb: "?z_hpa((CHOOSE zenon_Vvw:(~((zenon_Vvw \\in Node)=>((a_grantunde_msghash_primea[zenon_Vvw]) \\in {TRUE, FALSE})))))" (is "~(?z_hlu=>?z_hmd)")
    by (rule zenon_ex_choose_0 [of "?z_hpa", OF z_Hoz])
    have z_Hlu: "?z_hlu"
    by (rule zenon_notimply_0 [OF z_Hpb])
    have z_Hmc: "(~?z_hmd)"
    by (rule zenon_notimply_1 [OF z_Hpb])
    have z_Hpc: "(~((a_grantunde_msghash_primea[(CHOOSE zenon_Vvw:(~((zenon_Vvw \\in Node)=>((a_grantunde_msghash_primea[zenon_Vvw]) \\in {TRUE, FALSE}))))]) \\in {FALSE}))" (is "~?z_hpd")
    by (rule zenon_notin_addElt_1 [of "(a_grantunde_msghash_primea[(CHOOSE zenon_Vvw:(~((zenon_Vvw \\in Node)=>((a_grantunde_msghash_primea[zenon_Vvw]) \\in {TRUE, FALSE}))))])" "TRUE" "{FALSE}", OF z_Hmc])
    have z_Hpe: "((a_grantunde_msghash_primea[(CHOOSE zenon_Vvw:(~((zenon_Vvw \\in Node)=>((a_grantunde_msghash_primea[zenon_Vvw]) \\in {TRUE, FALSE}))))])~=FALSE)" (is "?z_hme~=?z_hk")
    by (rule zenon_notin_addElt_0 [of "?z_hme" "?z_hk" "{}", OF z_Hpc])
    have z_Hmt: "((CHOOSE zenon_Vvw:(~((zenon_Vvw \\in Node)=>((a_grantunde_msghash_primea[zenon_Vvw]) \\in {TRUE, ?z_hk})))) \\in ?z_hmu)" (is "?z_hmt")
    by (rule ssubst [where P="(\<lambda>zenon_Vtea. ((CHOOSE zenon_Vvw:(~((zenon_Vvw \\in Node)=>((a_grantunde_msghash_primea[zenon_Vvw]) \\in {TRUE, ?z_hk})))) \\in zenon_Vtea))", OF z_Hns z_Hlu])
    have z_Hpi: "((CHOOSE zenon_Vvw:(~((zenon_Vvw \\in Node)=>((a_grantunde_msghash_primea[zenon_Vvw]) \\in {TRUE, ?z_hk})))) \\in ?z_hnu)" (is "?z_hpi")
    by (rule ssubst [where P="(\<lambda>zenon_Vtea. ((CHOOSE zenon_Vvw:(~((zenon_Vvw \\in Node)=>((a_grantunde_msghash_primea[zenon_Vvw]) \\in {TRUE, ?z_hk})))) \\in zenon_Vtea))", OF z_Hnt z_Hlu])
    have z_Hpj: "?z_hoi((CHOOSE zenon_Vvw:(~((zenon_Vvw \\in Node)=>((a_grantunde_msghash_primea[zenon_Vvw]) \\in {TRUE, ?z_hk})))))" (is "?z_hpk=?z_hpl")
    by (rule zenon_all_0 [of "?z_hoi" "(CHOOSE zenon_Vvw:(~((zenon_Vvw \\in Node)=>((a_grantunde_msghash_primea[zenon_Vvw]) \\in {TRUE, ?z_hk}))))", OF z_Hod])
    show FALSE
    proof (rule zenon_fapplyexcept [of "(\<lambda>zenon_Vahd. (?z_hpk=zenon_Vahd))" "a_holdsunde_locka" "(CHOOSE x:((x \\in Node)&(((a_lockunde_msghash_primea=except(a_lockunde_msga, x, TRUE))&((a_grantunde_msghash_primea=a_grantunde_msga)&((a_holdsunde_lockhash_primea=a_holdsunde_locka)&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka)))))|((a_serverunde_holdsunde_locka&((a_lockunde_msga[x])&((a_serverunde_holdsunde_lockhash_primea=?z_hk)&((a_lockunde_msghash_primea=except(a_lockunde_msga, x, ?z_hk))&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, TRUE))&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_holdsunde_lockhash_primea=a_holdsunde_locka)))))))|(((a_grantunde_msga[x])&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, ?z_hk))&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, TRUE))&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|(((a_holdsunde_locka[x])&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, ?z_hk))&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, TRUE))&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_grantunde_msghash_primea=a_grantunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|((a_unlockunde_msga[x])&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, ?z_hk))&((a_serverunde_holdsunde_lockhash_primea=TRUE)&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_grantunde_msghash_primea=a_grantunde_msga)&(a_holdsunde_lockhash_primea=a_holdsunde_locka))))))))))))" "TRUE" "(CHOOSE zenon_Vvw:(~((zenon_Vvw \\in Node)=>((a_grantunde_msghash_primea[zenon_Vvw]) \\in {TRUE, ?z_hk}))))", OF z_Hpj])
     assume z_Hpi:"?z_hpi"
     assume z_Hnb:"((CHOOSE x:((x \\in Node)&(((a_lockunde_msghash_primea=except(a_lockunde_msga, x, TRUE))&((a_grantunde_msghash_primea=a_grantunde_msga)&((a_holdsunde_lockhash_primea=a_holdsunde_locka)&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka)))))|((a_serverunde_holdsunde_locka&((a_lockunde_msga[x])&((a_serverunde_holdsunde_lockhash_primea=?z_hk)&((a_lockunde_msghash_primea=except(a_lockunde_msga, x, ?z_hk))&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, TRUE))&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_holdsunde_lockhash_primea=a_holdsunde_locka)))))))|(((a_grantunde_msga[x])&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, ?z_hk))&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, TRUE))&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|(((a_holdsunde_locka[x])&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, ?z_hk))&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, TRUE))&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_grantunde_msghash_primea=a_grantunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|((a_unlockunde_msga[x])&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, ?z_hk))&((a_serverunde_holdsunde_lockhash_primea=TRUE)&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_grantunde_msghash_primea=a_grantunde_msga)&(a_holdsunde_lockhash_primea=a_holdsunde_locka))))))))))))=(CHOOSE zenon_Vvw:(~((zenon_Vvw \\in Node)=>((a_grantunde_msghash_primea[zenon_Vvw]) \\in {TRUE, ?z_hk})))))" (is "?z_hhd=?z_hlv")
     assume z_Hpp:"(?z_hpk=TRUE)" (is "_=?z_hj")
     have z_Hnm: "?z_hnl(?z_hlv)" (is "_=?z_hnn")
     by (rule zenon_all_0 [of "?z_hnl" "?z_hlv", OF z_Hnf])
     show FALSE
     proof (rule zenon_fapplyexcept [of "(\<lambda>zenon_Vchd. (?z_hme=zenon_Vchd))" "a_grantunde_msga" "?z_hhd" "?z_hk" "?z_hlv", OF z_Hnm])
      assume z_Hmt:"?z_hmt"
      assume z_Hnb:"(?z_hhd=?z_hlv)"
      assume z_Hno:"(?z_hme=?z_hk)"
      show FALSE
      by (rule notE [OF z_Hpe z_Hno])
     next
      assume z_Hmt:"?z_hmt"
      assume z_Hms:"(?z_hhd~=?z_hlv)"
      assume z_Hmf:"(?z_hme=(a_grantunde_msga[?z_hlv]))" (is "_=?z_hmg")
      show FALSE
      by (rule notE [OF z_Hms z_Hnb])
     next
      assume z_Hnd:"(~?z_hmt)"
      show FALSE
      by (rule notE [OF z_Hnd z_Hmt])
     qed
    next
     assume z_Hpi:"?z_hpi"
     assume z_Hms:"((CHOOSE x:((x \\in Node)&(((a_lockunde_msghash_primea=except(a_lockunde_msga, x, TRUE))&((a_grantunde_msghash_primea=a_grantunde_msga)&((a_holdsunde_lockhash_primea=a_holdsunde_locka)&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka)))))|((a_serverunde_holdsunde_locka&((a_lockunde_msga[x])&((a_serverunde_holdsunde_lockhash_primea=?z_hk)&((a_lockunde_msghash_primea=except(a_lockunde_msga, x, ?z_hk))&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, TRUE))&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_holdsunde_lockhash_primea=a_holdsunde_locka)))))))|(((a_grantunde_msga[x])&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, ?z_hk))&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, TRUE))&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|(((a_holdsunde_locka[x])&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, ?z_hk))&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, TRUE))&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_grantunde_msghash_primea=a_grantunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|((a_unlockunde_msga[x])&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, ?z_hk))&((a_serverunde_holdsunde_lockhash_primea=TRUE)&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_grantunde_msghash_primea=a_grantunde_msga)&(a_holdsunde_lockhash_primea=a_holdsunde_locka))))))))))))~=(CHOOSE zenon_Vvw:(~((zenon_Vvw \\in Node)=>((a_grantunde_msghash_primea[zenon_Vvw]) \\in {TRUE, ?z_hk})))))" (is "?z_hhd~=?z_hlv")
     assume z_Hpq:"(?z_hpk=(a_holdsunde_locka[?z_hlv]))" (is "_=?z_hpr")
     show FALSE
     by (rule zenon_L11_ [OF z_Hnf z_Hms z_Hlo z_Hlu z_Hmc z_Hmt])
    next
     assume z_Hps:"(~?z_hpi)"
     show FALSE
     by (rule notE [OF z_Hps z_Hpi])
    qed
   qed
  qed
 qed
 have zenon_L13_: "(\\A zenon_Vv:((zenon_Vv \\in Node)=>((a_holdsunde_locka[zenon_Vv]) \\in {TRUE, FALSE}))) ==> ((CHOOSE zenon_Vjb:(~((zenon_Vjb \\in Node)=>((a_holdsunde_lockhash_primea[zenon_Vjb]) \\in {TRUE, FALSE})))) \\in Node) ==> (~((a_holdsunde_lockhash_primea[(CHOOSE zenon_Vjb:(~((zenon_Vjb \\in Node)=>((a_holdsunde_lockhash_primea[zenon_Vjb]) \\in {TRUE, FALSE}))))]) \\in {TRUE, FALSE})) ==> ((a_holdsunde_lockhash_primea[(CHOOSE zenon_Vjb:(~((zenon_Vjb \\in Node)=>((a_holdsunde_lockhash_primea[zenon_Vjb]) \\in {TRUE, FALSE}))))])=(a_holdsunde_locka[(CHOOSE zenon_Vjb:(~((zenon_Vjb \\in Node)=>((a_holdsunde_lockhash_primea[zenon_Vjb]) \\in {TRUE, FALSE}))))])) ==> FALSE" (is "?z_hpt ==> ?z_hpz ==> ?z_hqh ==> ?z_hqk ==> FALSE")
 proof -
  assume z_Hpt:"?z_hpt" (is "\\A x : ?z_hqm(x)")
  assume z_Hpz:"?z_hpz"
  assume z_Hqh:"?z_hqh" (is "~?z_hqi")
  assume z_Hqk:"?z_hqk" (is "?z_hqj=?z_hql")
  have z_Hqn: "?z_hqm((CHOOSE zenon_Vjb:(~((zenon_Vjb \\in Node)=>((a_holdsunde_lockhash_primea[zenon_Vjb]) \\in {TRUE, FALSE})))))" (is "_=>?z_hqo")
  by (rule zenon_all_0 [of "?z_hqm" "(CHOOSE zenon_Vjb:(~((zenon_Vjb \\in Node)=>((a_holdsunde_lockhash_primea[zenon_Vjb]) \\in {TRUE, FALSE}))))", OF z_Hpt])
  show FALSE
  proof (rule zenon_imply [OF z_Hqn])
   assume z_Hqp:"(~?z_hpz)"
   show FALSE
   by (rule notE [OF z_Hqp z_Hpz])
  next
   assume z_Hqo:"?z_hqo"
   show FALSE
   proof (rule notE [OF z_Hqh])
    have z_Hqq: "(?z_hql=?z_hqj)"
    by (rule sym [OF z_Hqk])
    have z_Hqi: "?z_hqi"
    by (rule subst [where P="(\<lambda>zenon_Vr. (zenon_Vr \\in {TRUE, FALSE}))", OF z_Hqq], fact z_Hqo)
    thus "?z_hqi" .
   qed
  qed
 qed
 have zenon_L14_: "(a_holdsunde_lockhash_primea=except(a_holdsunde_locka, (CHOOSE x:((x \\in Node)&(((a_lockunde_msghash_primea=except(a_lockunde_msga, x, TRUE))&((a_grantunde_msghash_primea=a_grantunde_msga)&((a_holdsunde_lockhash_primea=a_holdsunde_locka)&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka)))))|((a_serverunde_holdsunde_locka&((a_lockunde_msga[x])&((a_serverunde_holdsunde_lockhash_primea=FALSE)&((a_lockunde_msghash_primea=except(a_lockunde_msga, x, FALSE))&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, TRUE))&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_holdsunde_lockhash_primea=a_holdsunde_locka)))))))|(((a_grantunde_msga[x])&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, FALSE))&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, TRUE))&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|(((a_holdsunde_locka[x])&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, FALSE))&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, TRUE))&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_grantunde_msghash_primea=a_grantunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|((a_unlockunde_msga[x])&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, FALSE))&((a_serverunde_holdsunde_lockhash_primea=TRUE)&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_grantunde_msghash_primea=a_grantunde_msga)&(a_holdsunde_lockhash_primea=a_holdsunde_locka)))))))))))), TRUE)) ==> (~(a_holdsunde_lockhash_primea \\in FuncSet(Node, {TRUE, FALSE}))) ==> (a_holdsunde_locka \\in FuncSet(Node, {TRUE, FALSE})) ==> FALSE" (is "?z_hnq ==> ?z_hkz ==> ?z_hs ==> FALSE")
 proof -
  assume z_Hnq:"?z_hnq" (is "_=?z_hnr")
  assume z_Hkz:"?z_hkz" (is "~?z_hla")
  assume z_Hs:"?z_hs"
  have z_Hnt: "(DOMAIN(a_holdsunde_locka)=Node)" (is "?z_hnu=_")
  by (rule zenon_in_funcset_1 [of "a_holdsunde_locka" "Node" "{TRUE, FALSE}", OF z_Hs])
  have z_Hnt: "(?z_hnu=Node)"
  by (rule zenon_in_funcset_1 [of "a_holdsunde_locka" "Node" "{TRUE, FALSE}", OF z_Hs])
  have z_Hpt: "(\\A zenon_Vv:((zenon_Vv \\in Node)=>((a_holdsunde_locka[zenon_Vv]) \\in {TRUE, FALSE})))" (is "\\A x : ?z_hqm(x)")
  by (rule zenon_in_funcset_2 [of "a_holdsunde_locka" "Node" "{TRUE, FALSE}", OF z_Hs])
  have z_Hnv: "(((isAFcn(a_holdsunde_lockhash_primea)<=>isAFcn(?z_hnr))&(DOMAIN(a_holdsunde_lockhash_primea)=DOMAIN(?z_hnr)))&(\\A zenon_Vomc:((a_holdsunde_lockhash_primea[zenon_Vomc])=(?z_hnr[zenon_Vomc]))))" (is "?z_hnw&?z_hod")
  by (rule zenon_funequal_0 [of "a_holdsunde_lockhash_primea" "?z_hnr", OF z_Hnq])
  have z_Hnw: "?z_hnw" (is "?z_hnx&?z_hoa")
  by (rule zenon_and_0 [OF z_Hnv])
  have z_Hod: "?z_hod" (is "\\A x : ?z_hoi(x)")
  by (rule zenon_and_1 [OF z_Hnv])
  have z_Hnx: "?z_hnx" (is "?z_hny<=>?z_hnz")
  by (rule zenon_and_0 [OF z_Hnw])
  show FALSE
  proof (rule zenon_equiv [OF z_Hnx])
   assume z_Hqr:"(~?z_hny)"
   assume z_Hqs:"(~?z_hnz)"
   show FALSE
   by (rule zenon_notisafcn_except [of "a_holdsunde_locka" "(CHOOSE x:((x \\in Node)&(((a_lockunde_msghash_primea=except(a_lockunde_msga, x, TRUE))&((a_grantunde_msghash_primea=a_grantunde_msga)&((a_holdsunde_lockhash_primea=a_holdsunde_locka)&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka)))))|((a_serverunde_holdsunde_locka&((a_lockunde_msga[x])&((a_serverunde_holdsunde_lockhash_primea=FALSE)&((a_lockunde_msghash_primea=except(a_lockunde_msga, x, FALSE))&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, TRUE))&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_holdsunde_lockhash_primea=a_holdsunde_locka)))))))|(((a_grantunde_msga[x])&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, FALSE))&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, TRUE))&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|(((a_holdsunde_locka[x])&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, FALSE))&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, TRUE))&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_grantunde_msghash_primea=a_grantunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|((a_unlockunde_msga[x])&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, FALSE))&((a_serverunde_holdsunde_lockhash_primea=TRUE)&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_grantunde_msghash_primea=a_grantunde_msga)&(a_holdsunde_lockhash_primea=a_holdsunde_locka))))))))))))" "TRUE", OF z_Hqs])
  next
   assume z_Hny:"?z_hny"
   assume z_Hnz:"?z_hnz"
   show FALSE
   proof (rule zenon_notin_funcset [of "a_holdsunde_lockhash_primea" "Node" "{TRUE, FALSE}", OF z_Hkz])
    assume z_Hqr:"(~?z_hny)"
    show FALSE
    by (rule notE [OF z_Hqr z_Hny])
   next
    assume z_Hqt:"(DOMAIN(a_holdsunde_lockhash_primea)~=Node)" (is "?z_hob~=_")
    have z_Hqu: "(DOMAIN(?z_hnr)~=Node)" (is "?z_hoc~=_")
    by (rule subst [where P="(\<lambda>zenon_Vlw. (DOMAIN(zenon_Vlw)~=Node))", OF z_Hnq z_Hqt])
    have z_Hqv: "(?z_hnu~=Node)"
    by (rule zenon_domain_except_0 [of "(\<lambda>zenon_Vkw. (zenon_Vkw~=Node))" "a_holdsunde_locka" "(CHOOSE x:((x \\in Node)&(((a_lockunde_msghash_primea=except(a_lockunde_msga, x, TRUE))&((a_grantunde_msghash_primea=a_grantunde_msga)&((a_holdsunde_lockhash_primea=a_holdsunde_locka)&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka)))))|((a_serverunde_holdsunde_locka&((a_lockunde_msga[x])&((a_serverunde_holdsunde_lockhash_primea=FALSE)&((a_lockunde_msghash_primea=except(a_lockunde_msga, x, FALSE))&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, TRUE))&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_holdsunde_lockhash_primea=a_holdsunde_locka)))))))|(((a_grantunde_msga[x])&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, FALSE))&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, TRUE))&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|(((a_holdsunde_locka[x])&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, FALSE))&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, TRUE))&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_grantunde_msghash_primea=a_grantunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|((a_unlockunde_msga[x])&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, FALSE))&((a_serverunde_holdsunde_lockhash_primea=TRUE)&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_grantunde_msghash_primea=a_grantunde_msga)&(a_holdsunde_lockhash_primea=a_holdsunde_locka))))))))))))" "TRUE", OF z_Hqu])
    show FALSE
    by (rule notE [OF z_Hqv z_Hnt])
   next
    assume z_Hqw:"(~(\\A zenon_Vjb:((zenon_Vjb \\in Node)=>((a_holdsunde_lockhash_primea[zenon_Vjb]) \\in {TRUE, FALSE}))))" (is "~(\\A x : ?z_hqy(x))")
    have z_Hqz: "(\\E zenon_Vjb:(~((zenon_Vjb \\in Node)=>((a_holdsunde_lockhash_primea[zenon_Vjb]) \\in {TRUE, FALSE}))))" (is "\\E x : ?z_hra(x)")
    by (rule zenon_notallex_0 [of "?z_hqy", OF z_Hqw])
    have z_Hrb: "?z_hra((CHOOSE zenon_Vjb:(~((zenon_Vjb \\in Node)=>((a_holdsunde_lockhash_primea[zenon_Vjb]) \\in {TRUE, FALSE})))))" (is "~(?z_hpz=>?z_hqi)")
    by (rule zenon_ex_choose_0 [of "?z_hra", OF z_Hqz])
    have z_Hpz: "?z_hpz"
    by (rule zenon_notimply_0 [OF z_Hrb])
    have z_Hqh: "(~?z_hqi)"
    by (rule zenon_notimply_1 [OF z_Hrb])
    have z_Hrc: "((a_holdsunde_lockhash_primea[(CHOOSE zenon_Vjb:(~((zenon_Vjb \\in Node)=>((a_holdsunde_lockhash_primea[zenon_Vjb]) \\in {TRUE, FALSE}))))])~=TRUE)" (is "?z_hqj~=?z_hj")
    by (rule zenon_notin_addElt_0 [of "?z_hqj" "?z_hj" "{FALSE}", OF z_Hqh])
    have z_Hrd: "((CHOOSE zenon_Vjb:(~((zenon_Vjb \\in Node)=>((a_holdsunde_lockhash_primea[zenon_Vjb]) \\in {?z_hj, FALSE})))) \\in ?z_hnu)" (is "?z_hrd")
    by (rule ssubst [where P="(\<lambda>zenon_Vixb. ((CHOOSE zenon_Vjb:(~((zenon_Vjb \\in Node)=>((a_holdsunde_lockhash_primea[zenon_Vjb]) \\in {?z_hj, FALSE})))) \\in zenon_Vixb))", OF z_Hnt z_Hpz])
    have z_Hrh: "?z_hoi((CHOOSE zenon_Vjb:(~((zenon_Vjb \\in Node)=>((a_holdsunde_lockhash_primea[zenon_Vjb]) \\in {?z_hj, FALSE})))))" (is "_=?z_hri")
    by (rule zenon_all_0 [of "?z_hoi" "(CHOOSE zenon_Vjb:(~((zenon_Vjb \\in Node)=>((a_holdsunde_lockhash_primea[zenon_Vjb]) \\in {?z_hj, FALSE}))))", OF z_Hod])
    show FALSE
    proof (rule zenon_fapplyexcept [of "(\<lambda>zenon_Vsyb. (?z_hqj=zenon_Vsyb))" "a_holdsunde_locka" "(CHOOSE x:((x \\in Node)&(((a_lockunde_msghash_primea=except(a_lockunde_msga, x, ?z_hj))&((a_grantunde_msghash_primea=a_grantunde_msga)&((a_holdsunde_lockhash_primea=a_holdsunde_locka)&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka)))))|((a_serverunde_holdsunde_locka&((a_lockunde_msga[x])&((a_serverunde_holdsunde_lockhash_primea=FALSE)&((a_lockunde_msghash_primea=except(a_lockunde_msga, x, FALSE))&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, ?z_hj))&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_holdsunde_lockhash_primea=a_holdsunde_locka)))))))|(((a_grantunde_msga[x])&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, FALSE))&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, ?z_hj))&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|(((a_holdsunde_locka[x])&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, FALSE))&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, ?z_hj))&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_grantunde_msghash_primea=a_grantunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|((a_unlockunde_msga[x])&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, FALSE))&((a_serverunde_holdsunde_lockhash_primea=?z_hj)&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_grantunde_msghash_primea=a_grantunde_msga)&(a_holdsunde_lockhash_primea=a_holdsunde_locka))))))))))))" "?z_hj" "(CHOOSE zenon_Vjb:(~((zenon_Vjb \\in Node)=>((a_holdsunde_lockhash_primea[zenon_Vjb]) \\in {?z_hj, FALSE}))))", OF z_Hrh])
     assume z_Hrd:"?z_hrd"
     assume z_Hrm:"((CHOOSE x:((x \\in Node)&(((a_lockunde_msghash_primea=except(a_lockunde_msga, x, ?z_hj))&((a_grantunde_msghash_primea=a_grantunde_msga)&((a_holdsunde_lockhash_primea=a_holdsunde_locka)&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka)))))|((a_serverunde_holdsunde_locka&((a_lockunde_msga[x])&((a_serverunde_holdsunde_lockhash_primea=FALSE)&((a_lockunde_msghash_primea=except(a_lockunde_msga, x, FALSE))&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, ?z_hj))&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_holdsunde_lockhash_primea=a_holdsunde_locka)))))))|(((a_grantunde_msga[x])&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, FALSE))&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, ?z_hj))&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|(((a_holdsunde_locka[x])&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, FALSE))&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, ?z_hj))&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_grantunde_msghash_primea=a_grantunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|((a_unlockunde_msga[x])&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, FALSE))&((a_serverunde_holdsunde_lockhash_primea=?z_hj)&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_grantunde_msghash_primea=a_grantunde_msga)&(a_holdsunde_lockhash_primea=a_holdsunde_locka))))))))))))=(CHOOSE zenon_Vjb:(~((zenon_Vjb \\in Node)=>((a_holdsunde_lockhash_primea[zenon_Vjb]) \\in {?z_hj, FALSE})))))" (is "?z_hhd=?z_hqa")
     assume z_Hrn:"(?z_hqj=?z_hj)"
     show FALSE
     by (rule notE [OF z_Hrc z_Hrn])
    next
     assume z_Hrd:"?z_hrd"
     assume z_Hro:"((CHOOSE x:((x \\in Node)&(((a_lockunde_msghash_primea=except(a_lockunde_msga, x, ?z_hj))&((a_grantunde_msghash_primea=a_grantunde_msga)&((a_holdsunde_lockhash_primea=a_holdsunde_locka)&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka)))))|((a_serverunde_holdsunde_locka&((a_lockunde_msga[x])&((a_serverunde_holdsunde_lockhash_primea=FALSE)&((a_lockunde_msghash_primea=except(a_lockunde_msga, x, FALSE))&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, ?z_hj))&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_holdsunde_lockhash_primea=a_holdsunde_locka)))))))|(((a_grantunde_msga[x])&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, FALSE))&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, ?z_hj))&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|(((a_holdsunde_locka[x])&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, FALSE))&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, ?z_hj))&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_grantunde_msghash_primea=a_grantunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|((a_unlockunde_msga[x])&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, FALSE))&((a_serverunde_holdsunde_lockhash_primea=?z_hj)&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_grantunde_msghash_primea=a_grantunde_msga)&(a_holdsunde_lockhash_primea=a_holdsunde_locka))))))))))))~=(CHOOSE zenon_Vjb:(~((zenon_Vjb \\in Node)=>((a_holdsunde_lockhash_primea[zenon_Vjb]) \\in {?z_hj, FALSE})))))" (is "?z_hhd~=?z_hqa")
     assume z_Hqk:"(?z_hqj=(a_holdsunde_locka[?z_hqa]))" (is "_=?z_hql")
     show FALSE
     by (rule zenon_L13_ [OF z_Hpt z_Hpz z_Hqh z_Hqk])
    next
     assume z_Hrp:"(~?z_hrd)"
     show FALSE
     by (rule notE [OF z_Hrp z_Hrd])
    qed
   qed
  qed
 qed
 have zenon_L15_: "(\\A zenon_Vy:((zenon_Vy \\in Node)=>((a_unlockunde_msga[zenon_Vy]) \\in {TRUE, FALSE}))) ==> ((CHOOSE zenon_Vll:(~((zenon_Vll \\in Node)=>((a_unlockunde_msghash_primea[zenon_Vll]) \\in {TRUE, FALSE})))) \\in Node) ==> (~((a_unlockunde_msghash_primea[(CHOOSE zenon_Vll:(~((zenon_Vll \\in Node)=>((a_unlockunde_msghash_primea[zenon_Vll]) \\in {TRUE, FALSE}))))]) \\in {TRUE, FALSE})) ==> ((a_unlockunde_msghash_primea[(CHOOSE zenon_Vll:(~((zenon_Vll \\in Node)=>((a_unlockunde_msghash_primea[zenon_Vll]) \\in {TRUE, FALSE}))))])=(a_unlockunde_msga[(CHOOSE zenon_Vll:(~((zenon_Vll \\in Node)=>((a_unlockunde_msghash_primea[zenon_Vll]) \\in {TRUE, FALSE}))))])) ==> FALSE" (is "?z_hrq ==> ?z_hrw ==> ?z_hse ==> ?z_hsh ==> FALSE")
 proof -
  assume z_Hrq:"?z_hrq" (is "\\A x : ?z_hsj(x)")
  assume z_Hrw:"?z_hrw"
  assume z_Hse:"?z_hse" (is "~?z_hsf")
  assume z_Hsh:"?z_hsh" (is "?z_hsg=?z_hsi")
  have z_Hsk: "?z_hsj((CHOOSE zenon_Vll:(~((zenon_Vll \\in Node)=>((a_unlockunde_msghash_primea[zenon_Vll]) \\in {TRUE, FALSE})))))" (is "_=>?z_hsl")
  by (rule zenon_all_0 [of "?z_hsj" "(CHOOSE zenon_Vll:(~((zenon_Vll \\in Node)=>((a_unlockunde_msghash_primea[zenon_Vll]) \\in {TRUE, FALSE}))))", OF z_Hrq])
  show FALSE
  proof (rule zenon_imply [OF z_Hsk])
   assume z_Hsm:"(~?z_hrw)"
   show FALSE
   by (rule notE [OF z_Hsm z_Hrw])
  next
   assume z_Hsl:"?z_hsl"
   show FALSE
   proof (rule notE [OF z_Hse])
    have z_Hsn: "(?z_hsi=?z_hsg)"
    by (rule sym [OF z_Hsh])
    have z_Hsf: "?z_hsf"
    by (rule subst [where P="(\<lambda>zenon_Vr. (zenon_Vr \\in {TRUE, FALSE}))", OF z_Hsn], fact z_Hsl)
    thus "?z_hsf" .
   qed
  qed
 qed
 have zenon_L16_: "(\\A zenon_Vqob:((a_unlockunde_msghash_primea[zenon_Vqob])=(except(a_unlockunde_msga, (CHOOSE x:((x \\in Node)&(((a_lockunde_msghash_primea=except(a_lockunde_msga, x, TRUE))&((a_grantunde_msghash_primea=a_grantunde_msga)&((a_holdsunde_lockhash_primea=a_holdsunde_locka)&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka)))))|((a_serverunde_holdsunde_locka&((a_lockunde_msga[x])&((a_serverunde_holdsunde_lockhash_primea=FALSE)&((a_lockunde_msghash_primea=except(a_lockunde_msga, x, FALSE))&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, TRUE))&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_holdsunde_lockhash_primea=a_holdsunde_locka)))))))|(((a_grantunde_msga[x])&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, FALSE))&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, TRUE))&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|(((a_holdsunde_locka[x])&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, FALSE))&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, TRUE))&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_grantunde_msghash_primea=a_grantunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|((a_unlockunde_msga[x])&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, FALSE))&((a_serverunde_holdsunde_lockhash_primea=TRUE)&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_grantunde_msghash_primea=a_grantunde_msga)&(a_holdsunde_lockhash_primea=a_holdsunde_locka)))))))))))), TRUE)[zenon_Vqob]))) ==> ((CHOOSE x:((x \\in Node)&(((a_lockunde_msghash_primea=except(a_lockunde_msga, x, TRUE))&((a_grantunde_msghash_primea=a_grantunde_msga)&((a_holdsunde_lockhash_primea=a_holdsunde_locka)&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka)))))|((a_serverunde_holdsunde_locka&((a_lockunde_msga[x])&((a_serverunde_holdsunde_lockhash_primea=FALSE)&((a_lockunde_msghash_primea=except(a_lockunde_msga, x, FALSE))&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, TRUE))&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_holdsunde_lockhash_primea=a_holdsunde_locka)))))))|(((a_grantunde_msga[x])&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, FALSE))&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, TRUE))&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|(((a_holdsunde_locka[x])&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, FALSE))&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, TRUE))&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_grantunde_msghash_primea=a_grantunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|((a_unlockunde_msga[x])&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, FALSE))&((a_serverunde_holdsunde_lockhash_primea=TRUE)&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_grantunde_msghash_primea=a_grantunde_msga)&(a_holdsunde_lockhash_primea=a_holdsunde_locka))))))))))))~=(CHOOSE zenon_Vll:(~((zenon_Vll \\in Node)=>((a_unlockunde_msghash_primea[zenon_Vll]) \\in {TRUE, FALSE}))))) ==> (\\A zenon_Vy:((zenon_Vy \\in Node)=>((a_unlockunde_msga[zenon_Vy]) \\in {TRUE, FALSE}))) ==> ((CHOOSE zenon_Vll:(~((zenon_Vll \\in Node)=>((a_unlockunde_msghash_primea[zenon_Vll]) \\in {TRUE, FALSE})))) \\in Node) ==> (~((a_unlockunde_msghash_primea[(CHOOSE zenon_Vll:(~((zenon_Vll \\in Node)=>((a_unlockunde_msghash_primea[zenon_Vll]) \\in {TRUE, FALSE}))))]) \\in {TRUE, FALSE})) ==> ((CHOOSE zenon_Vll:(~((zenon_Vll \\in Node)=>((a_unlockunde_msghash_primea[zenon_Vll]) \\in {TRUE, FALSE})))) \\in DOMAIN(a_unlockunde_msga)) ==> FALSE" (is "?z_hso ==> ?z_hsu ==> ?z_hrq ==> ?z_hrw ==> ?z_hse ==> ?z_hsv ==> FALSE")
 proof -
  assume z_Hso:"?z_hso" (is "\\A x : ?z_hsx(x)")
  assume z_Hsu:"?z_hsu" (is "?z_hhd~=?z_hrx")
  assume z_Hrq:"?z_hrq" (is "\\A x : ?z_hsj(x)")
  assume z_Hrw:"?z_hrw"
  assume z_Hse:"?z_hse" (is "~?z_hsf")
  assume z_Hsv:"?z_hsv"
  have z_Hsy: "?z_hsx(?z_hrx)" (is "?z_hsg=?z_hsz")
  by (rule zenon_all_0 [of "?z_hsx" "?z_hrx", OF z_Hso])
  show FALSE
  proof (rule zenon_fapplyexcept [of "(\<lambda>zenon_Vwu. (?z_hsg=zenon_Vwu))" "a_unlockunde_msga" "?z_hhd" "TRUE" "?z_hrx", OF z_Hsy])
   assume z_Hsv:"?z_hsv"
   assume z_Htd:"(?z_hhd=?z_hrx)"
   assume z_Hte:"(?z_hsg=TRUE)" (is "_=?z_hj")
   show FALSE
   by (rule notE [OF z_Hsu z_Htd])
  next
   assume z_Hsv:"?z_hsv"
   assume z_Hsu:"?z_hsu"
   assume z_Hsh:"(?z_hsg=(a_unlockunde_msga[?z_hrx]))" (is "_=?z_hsi")
   show FALSE
   by (rule zenon_L15_ [OF z_Hrq z_Hrw z_Hse z_Hsh])
  next
   assume z_Htf:"(~?z_hsv)"
   show FALSE
   by (rule notE [OF z_Htf z_Hsv])
  qed
 qed
 have zenon_L17_: "(a_unlockunde_msga \\in FuncSet(Node, {TRUE, FALSE})) ==> (a_holdsunde_lockhash_primea=except(a_holdsunde_locka, (CHOOSE x:((x \\in Node)&(((a_lockunde_msghash_primea=except(a_lockunde_msga, x, TRUE))&((a_grantunde_msghash_primea=a_grantunde_msga)&((a_holdsunde_lockhash_primea=a_holdsunde_locka)&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka)))))|((a_serverunde_holdsunde_locka&((a_lockunde_msga[x])&((a_serverunde_holdsunde_lockhash_primea=FALSE)&((a_lockunde_msghash_primea=except(a_lockunde_msga, x, FALSE))&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, TRUE))&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_holdsunde_lockhash_primea=a_holdsunde_locka)))))))|(((a_grantunde_msga[x])&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, FALSE))&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, TRUE))&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|(((a_holdsunde_locka[x])&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, FALSE))&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, TRUE))&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_grantunde_msghash_primea=a_grantunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|((a_unlockunde_msga[x])&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, FALSE))&((a_serverunde_holdsunde_lockhash_primea=TRUE)&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_grantunde_msghash_primea=a_grantunde_msga)&(a_holdsunde_lockhash_primea=a_holdsunde_locka)))))))))))), FALSE)) ==> (~(a_unlockunde_msghash_primea \\in FuncSet(Node, {TRUE, FALSE}))) ==> (a_unlockunde_msghash_primea=except(a_unlockunde_msga, (CHOOSE x:((x \\in Node)&(((a_lockunde_msghash_primea=except(a_lockunde_msga, x, TRUE))&((a_grantunde_msghash_primea=a_grantunde_msga)&((a_holdsunde_lockhash_primea=a_holdsunde_locka)&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka)))))|((a_serverunde_holdsunde_locka&((a_lockunde_msga[x])&((a_serverunde_holdsunde_lockhash_primea=FALSE)&((a_lockunde_msghash_primea=except(a_lockunde_msga, x, FALSE))&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, TRUE))&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_holdsunde_lockhash_primea=a_holdsunde_locka)))))))|(((a_grantunde_msga[x])&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, FALSE))&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, TRUE))&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|(((a_holdsunde_locka[x])&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, FALSE))&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, TRUE))&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_grantunde_msghash_primea=a_grantunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|((a_unlockunde_msga[x])&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, FALSE))&((a_serverunde_holdsunde_lockhash_primea=TRUE)&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_grantunde_msghash_primea=a_grantunde_msga)&(a_holdsunde_lockhash_primea=a_holdsunde_locka)))))))))))), TRUE)) ==> (a_holdsunde_locka \\in FuncSet(Node, {TRUE, FALSE})) ==> FALSE" (is "?z_hp ==> ?z_htg ==> ?z_hkw ==> ?z_hti ==> ?z_hs ==> FALSE")
 proof -
  assume z_Hp:"?z_hp"
  assume z_Htg:"?z_htg" (is "_=?z_hth")
  assume z_Hkw:"?z_hkw" (is "~?z_hkx")
  assume z_Hti:"?z_hti" (is "_=?z_hst")
  assume z_Hs:"?z_hs"
  have z_Htj: "(DOMAIN(a_unlockunde_msga)=Node)" (is "?z_hsw=_")
  by (rule zenon_in_funcset_1 [of "a_unlockunde_msga" "Node" "{TRUE, FALSE}", OF z_Hp])
  have z_Hnt: "(DOMAIN(a_holdsunde_locka)=Node)" (is "?z_hnu=_")
  by (rule zenon_in_funcset_1 [of "a_holdsunde_locka" "Node" "{TRUE, FALSE}", OF z_Hs])
  have z_Htj: "(?z_hsw=Node)"
  by (rule zenon_in_funcset_1 [of "a_unlockunde_msga" "Node" "{TRUE, FALSE}", OF z_Hp])
  have z_Hrq: "(\\A zenon_Vy:((zenon_Vy \\in Node)=>((a_unlockunde_msga[zenon_Vy]) \\in {TRUE, FALSE})))" (is "\\A x : ?z_hsj(x)")
  by (rule zenon_in_funcset_2 [of "a_unlockunde_msga" "Node" "{TRUE, FALSE}", OF z_Hp])
  have z_Htk: "(((isAFcn(a_unlockunde_msghash_primea)<=>isAFcn(?z_hst))&(DOMAIN(a_unlockunde_msghash_primea)=DOMAIN(?z_hst)))&(\\A zenon_Vqob:((a_unlockunde_msghash_primea[zenon_Vqob])=(?z_hst[zenon_Vqob]))))" (is "?z_htl&?z_hso")
  by (rule zenon_funequal_0 [of "a_unlockunde_msghash_primea" "?z_hst", OF z_Hti])
  have z_Htl: "?z_htl" (is "?z_htm&?z_htp")
  by (rule zenon_and_0 [OF z_Htk])
  have z_Hso: "?z_hso" (is "\\A x : ?z_hsx(x)")
  by (rule zenon_and_1 [OF z_Htk])
  have z_Htm: "?z_htm" (is "?z_htn<=>?z_hto")
  by (rule zenon_and_0 [OF z_Htl])
  show FALSE
  proof (rule zenon_equiv [OF z_Htm])
   assume z_Hts:"(~?z_htn)"
   assume z_Htt:"(~?z_hto)"
   show FALSE
   by (rule zenon_notisafcn_except [of "a_unlockunde_msga" "(CHOOSE x:((x \\in Node)&(((a_lockunde_msghash_primea=except(a_lockunde_msga, x, TRUE))&((a_grantunde_msghash_primea=a_grantunde_msga)&((a_holdsunde_lockhash_primea=a_holdsunde_locka)&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka)))))|((a_serverunde_holdsunde_locka&((a_lockunde_msga[x])&((a_serverunde_holdsunde_lockhash_primea=FALSE)&((a_lockunde_msghash_primea=except(a_lockunde_msga, x, FALSE))&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, TRUE))&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_holdsunde_lockhash_primea=a_holdsunde_locka)))))))|(((a_grantunde_msga[x])&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, FALSE))&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, TRUE))&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|(((a_holdsunde_locka[x])&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, FALSE))&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, TRUE))&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_grantunde_msghash_primea=a_grantunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|((a_unlockunde_msga[x])&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, FALSE))&((a_serverunde_holdsunde_lockhash_primea=TRUE)&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_grantunde_msghash_primea=a_grantunde_msga)&(a_holdsunde_lockhash_primea=a_holdsunde_locka))))))))))))" "TRUE", OF z_Htt])
  next
   assume z_Htn:"?z_htn"
   assume z_Hto:"?z_hto"
   have z_Htu: "(((isAFcn(a_holdsunde_lockhash_primea)<=>isAFcn(?z_hth))&(DOMAIN(a_holdsunde_lockhash_primea)=DOMAIN(?z_hth)))&(\\A zenon_Vsob:((a_holdsunde_lockhash_primea[zenon_Vsob])=(?z_hth[zenon_Vsob]))))" (is "?z_htv&?z_hua")
   by (rule zenon_funequal_0 [of "a_holdsunde_lockhash_primea" "?z_hth", OF z_Htg])
   have z_Hua: "?z_hua" (is "\\A x : ?z_huf(x)")
   by (rule zenon_and_1 [OF z_Htu])
   show FALSE
   proof (rule zenon_notin_funcset [of "a_unlockunde_msghash_primea" "Node" "{TRUE, FALSE}", OF z_Hkw])
    assume z_Hts:"(~?z_htn)"
    show FALSE
    by (rule notE [OF z_Hts z_Htn])
   next
    assume z_Hug:"(DOMAIN(a_unlockunde_msghash_primea)~=Node)" (is "?z_htq~=_")
    have z_Huh: "(DOMAIN(?z_hst)~=Node)" (is "?z_htr~=_")
    by (rule subst [where P="(\<lambda>zenon_Vlw. (DOMAIN(zenon_Vlw)~=Node))", OF z_Hti z_Hug])
    have z_Hui: "(?z_hsw~=Node)"
    by (rule zenon_domain_except_0 [of "(\<lambda>zenon_Vkw. (zenon_Vkw~=Node))" "a_unlockunde_msga" "(CHOOSE x:((x \\in Node)&(((a_lockunde_msghash_primea=except(a_lockunde_msga, x, TRUE))&((a_grantunde_msghash_primea=a_grantunde_msga)&((a_holdsunde_lockhash_primea=a_holdsunde_locka)&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka)))))|((a_serverunde_holdsunde_locka&((a_lockunde_msga[x])&((a_serverunde_holdsunde_lockhash_primea=FALSE)&((a_lockunde_msghash_primea=except(a_lockunde_msga, x, FALSE))&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, TRUE))&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_holdsunde_lockhash_primea=a_holdsunde_locka)))))))|(((a_grantunde_msga[x])&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, FALSE))&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, TRUE))&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|(((a_holdsunde_locka[x])&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, FALSE))&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, TRUE))&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_grantunde_msghash_primea=a_grantunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|((a_unlockunde_msga[x])&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, FALSE))&((a_serverunde_holdsunde_lockhash_primea=TRUE)&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_grantunde_msghash_primea=a_grantunde_msga)&(a_holdsunde_lockhash_primea=a_holdsunde_locka))))))))))))" "TRUE", OF z_Huh])
    show FALSE
    by (rule notE [OF z_Hui z_Htj])
   next
    assume z_Huj:"(~(\\A zenon_Vll:((zenon_Vll \\in Node)=>((a_unlockunde_msghash_primea[zenon_Vll]) \\in {TRUE, FALSE}))))" (is "~(\\A x : ?z_hul(x))")
    have z_Hum: "(\\E zenon_Vll:(~((zenon_Vll \\in Node)=>((a_unlockunde_msghash_primea[zenon_Vll]) \\in {TRUE, FALSE}))))" (is "\\E x : ?z_hun(x)")
    by (rule zenon_notallex_0 [of "?z_hul", OF z_Huj])
    have z_Huo: "?z_hun((CHOOSE zenon_Vll:(~((zenon_Vll \\in Node)=>((a_unlockunde_msghash_primea[zenon_Vll]) \\in {TRUE, FALSE})))))" (is "~(?z_hrw=>?z_hsf)")
    by (rule zenon_ex_choose_0 [of "?z_hun", OF z_Hum])
    have z_Hrw: "?z_hrw"
    by (rule zenon_notimply_0 [OF z_Huo])
    have z_Hse: "(~?z_hsf)"
    by (rule zenon_notimply_1 [OF z_Huo])
    have z_Hup: "((a_unlockunde_msghash_primea[(CHOOSE zenon_Vll:(~((zenon_Vll \\in Node)=>((a_unlockunde_msghash_primea[zenon_Vll]) \\in {TRUE, FALSE}))))])~=TRUE)" (is "?z_hsg~=?z_hj")
    by (rule zenon_notin_addElt_0 [of "?z_hsg" "?z_hj" "{FALSE}", OF z_Hse])
    have z_Hsv: "((CHOOSE zenon_Vll:(~((zenon_Vll \\in Node)=>((a_unlockunde_msghash_primea[zenon_Vll]) \\in {?z_hj, FALSE})))) \\in ?z_hsw)" (is "?z_hsv")
    by (rule ssubst [where P="(\<lambda>zenon_Vjt. ((CHOOSE zenon_Vll:(~((zenon_Vll \\in Node)=>((a_unlockunde_msghash_primea[zenon_Vll]) \\in {?z_hj, FALSE})))) \\in zenon_Vjt))", OF z_Htj z_Hrw])
    have z_Hut: "((CHOOSE zenon_Vll:(~((zenon_Vll \\in Node)=>((a_unlockunde_msghash_primea[zenon_Vll]) \\in {?z_hj, FALSE})))) \\in ?z_hnu)" (is "?z_hut")
    by (rule ssubst [where P="(\<lambda>zenon_Vjt. ((CHOOSE zenon_Vll:(~((zenon_Vll \\in Node)=>((a_unlockunde_msghash_primea[zenon_Vll]) \\in {?z_hj, FALSE})))) \\in zenon_Vjt))", OF z_Hnt z_Hrw])
    have z_Huu: "?z_huf((CHOOSE zenon_Vll:(~((zenon_Vll \\in Node)=>((a_unlockunde_msghash_primea[zenon_Vll]) \\in {?z_hj, FALSE})))))" (is "?z_huv=?z_huw")
    by (rule zenon_all_0 [of "?z_huf" "(CHOOSE zenon_Vll:(~((zenon_Vll \\in Node)=>((a_unlockunde_msghash_primea[zenon_Vll]) \\in {?z_hj, FALSE}))))", OF z_Hua])
    show FALSE
    proof (rule zenon_fapplyexcept [of "(\<lambda>zenon_Vakc. (?z_huv=zenon_Vakc))" "a_holdsunde_locka" "(CHOOSE x:((x \\in Node)&(((a_lockunde_msghash_primea=except(a_lockunde_msga, x, ?z_hj))&((a_grantunde_msghash_primea=a_grantunde_msga)&((a_holdsunde_lockhash_primea=a_holdsunde_locka)&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka)))))|((a_serverunde_holdsunde_locka&((a_lockunde_msga[x])&((a_serverunde_holdsunde_lockhash_primea=FALSE)&((a_lockunde_msghash_primea=except(a_lockunde_msga, x, FALSE))&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, ?z_hj))&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_holdsunde_lockhash_primea=a_holdsunde_locka)))))))|(((a_grantunde_msga[x])&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, FALSE))&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, ?z_hj))&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|(((a_holdsunde_locka[x])&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, FALSE))&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, ?z_hj))&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_grantunde_msghash_primea=a_grantunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|((a_unlockunde_msga[x])&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, FALSE))&((a_serverunde_holdsunde_lockhash_primea=?z_hj)&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_grantunde_msghash_primea=a_grantunde_msga)&(a_holdsunde_lockhash_primea=a_holdsunde_locka))))))))))))" "FALSE" "(CHOOSE zenon_Vll:(~((zenon_Vll \\in Node)=>((a_unlockunde_msghash_primea[zenon_Vll]) \\in {?z_hj, FALSE}))))", OF z_Huu])
     assume z_Hut:"?z_hut"
     assume z_Htd:"((CHOOSE x:((x \\in Node)&(((a_lockunde_msghash_primea=except(a_lockunde_msga, x, ?z_hj))&((a_grantunde_msghash_primea=a_grantunde_msga)&((a_holdsunde_lockhash_primea=a_holdsunde_locka)&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka)))))|((a_serverunde_holdsunde_locka&((a_lockunde_msga[x])&((a_serverunde_holdsunde_lockhash_primea=FALSE)&((a_lockunde_msghash_primea=except(a_lockunde_msga, x, FALSE))&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, ?z_hj))&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_holdsunde_lockhash_primea=a_holdsunde_locka)))))))|(((a_grantunde_msga[x])&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, FALSE))&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, ?z_hj))&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|(((a_holdsunde_locka[x])&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, FALSE))&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, ?z_hj))&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_grantunde_msghash_primea=a_grantunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|((a_unlockunde_msga[x])&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, FALSE))&((a_serverunde_holdsunde_lockhash_primea=?z_hj)&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_grantunde_msghash_primea=a_grantunde_msga)&(a_holdsunde_lockhash_primea=a_holdsunde_locka))))))))))))=(CHOOSE zenon_Vll:(~((zenon_Vll \\in Node)=>((a_unlockunde_msghash_primea[zenon_Vll]) \\in {?z_hj, FALSE})))))" (is "?z_hhd=?z_hrx")
     assume z_Hva:"(?z_huv=FALSE)" (is "_=?z_hk")
     have z_Hsy: "?z_hsx(?z_hrx)" (is "_=?z_hsz")
     by (rule zenon_all_0 [of "?z_hsx" "?z_hrx", OF z_Hso])
     show FALSE
     proof (rule zenon_fapplyexcept [of "(\<lambda>zenon_Vwu. (?z_hsg=zenon_Vwu))" "a_unlockunde_msga" "?z_hhd" "?z_hj" "?z_hrx", OF z_Hsy])
      assume z_Hsv:"?z_hsv"
      assume z_Htd:"(?z_hhd=?z_hrx)"
      assume z_Hte:"(?z_hsg=?z_hj)"
      show FALSE
      by (rule notE [OF z_Hup z_Hte])
     next
      assume z_Hsv:"?z_hsv"
      assume z_Hsu:"(?z_hhd~=?z_hrx)"
      assume z_Hsh:"(?z_hsg=(a_unlockunde_msga[?z_hrx]))" (is "_=?z_hsi")
      show FALSE
      by (rule notE [OF z_Hsu z_Htd])
     next
      assume z_Htf:"(~?z_hsv)"
      show FALSE
      by (rule notE [OF z_Htf z_Hsv])
     qed
    next
     assume z_Hut:"?z_hut"
     assume z_Hsu:"((CHOOSE x:((x \\in Node)&(((a_lockunde_msghash_primea=except(a_lockunde_msga, x, ?z_hj))&((a_grantunde_msghash_primea=a_grantunde_msga)&((a_holdsunde_lockhash_primea=a_holdsunde_locka)&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka)))))|((a_serverunde_holdsunde_locka&((a_lockunde_msga[x])&((a_serverunde_holdsunde_lockhash_primea=FALSE)&((a_lockunde_msghash_primea=except(a_lockunde_msga, x, FALSE))&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, ?z_hj))&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_holdsunde_lockhash_primea=a_holdsunde_locka)))))))|(((a_grantunde_msga[x])&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, FALSE))&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, ?z_hj))&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|(((a_holdsunde_locka[x])&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, FALSE))&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, ?z_hj))&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_grantunde_msghash_primea=a_grantunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|((a_unlockunde_msga[x])&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, FALSE))&((a_serverunde_holdsunde_lockhash_primea=?z_hj)&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_grantunde_msghash_primea=a_grantunde_msga)&(a_holdsunde_lockhash_primea=a_holdsunde_locka))))))))))))~=(CHOOSE zenon_Vll:(~((zenon_Vll \\in Node)=>((a_unlockunde_msghash_primea[zenon_Vll]) \\in {?z_hj, FALSE})))))" (is "?z_hhd~=?z_hrx")
     assume z_Hvb:"(?z_huv=(a_holdsunde_locka[?z_hrx]))" (is "_=?z_hvc")
     show FALSE
     by (rule zenon_L16_ [OF z_Hso z_Hsu z_Hrq z_Hrw z_Hse z_Hsv])
    next
     assume z_Hvd:"(~?z_hut)"
     show FALSE
     by (rule notE [OF z_Hvd z_Hut])
    qed
   qed
  qed
 qed
 have zenon_L18_: "(a_holdsunde_lockhash_primea=except(a_holdsunde_locka, (CHOOSE x:((x \\in Node)&(((a_lockunde_msghash_primea=except(a_lockunde_msga, x, TRUE))&((a_grantunde_msghash_primea=a_grantunde_msga)&((a_holdsunde_lockhash_primea=a_holdsunde_locka)&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka)))))|((a_serverunde_holdsunde_locka&((a_lockunde_msga[x])&((a_serverunde_holdsunde_lockhash_primea=FALSE)&((a_lockunde_msghash_primea=except(a_lockunde_msga, x, FALSE))&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, TRUE))&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_holdsunde_lockhash_primea=a_holdsunde_locka)))))))|(((a_grantunde_msga[x])&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, FALSE))&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, TRUE))&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|(((a_holdsunde_locka[x])&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, FALSE))&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, TRUE))&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_grantunde_msghash_primea=a_grantunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|((a_unlockunde_msga[x])&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, FALSE))&((a_serverunde_holdsunde_lockhash_primea=TRUE)&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_grantunde_msghash_primea=a_grantunde_msga)&(a_holdsunde_lockhash_primea=a_holdsunde_locka)))))))))))), FALSE)) ==> (~(a_holdsunde_lockhash_primea \\in FuncSet(Node, {TRUE, FALSE}))) ==> (a_holdsunde_locka \\in FuncSet(Node, {TRUE, FALSE})) ==> FALSE" (is "?z_htg ==> ?z_hkz ==> ?z_hs ==> FALSE")
 proof -
  assume z_Htg:"?z_htg" (is "_=?z_hth")
  assume z_Hkz:"?z_hkz" (is "~?z_hla")
  assume z_Hs:"?z_hs"
  have z_Hnt: "(DOMAIN(a_holdsunde_locka)=Node)" (is "?z_hnu=_")
  by (rule zenon_in_funcset_1 [of "a_holdsunde_locka" "Node" "{TRUE, FALSE}", OF z_Hs])
  have z_Hnt: "(?z_hnu=Node)"
  by (rule zenon_in_funcset_1 [of "a_holdsunde_locka" "Node" "{TRUE, FALSE}", OF z_Hs])
  have z_Hpt: "(\\A zenon_Vv:((zenon_Vv \\in Node)=>((a_holdsunde_locka[zenon_Vv]) \\in {TRUE, FALSE})))" (is "\\A x : ?z_hqm(x)")
  by (rule zenon_in_funcset_2 [of "a_holdsunde_locka" "Node" "{TRUE, FALSE}", OF z_Hs])
  have z_Htu: "(((isAFcn(a_holdsunde_lockhash_primea)<=>isAFcn(?z_hth))&(DOMAIN(a_holdsunde_lockhash_primea)=DOMAIN(?z_hth)))&(\\A zenon_Vsob:((a_holdsunde_lockhash_primea[zenon_Vsob])=(?z_hth[zenon_Vsob]))))" (is "?z_htv&?z_hua")
  by (rule zenon_funequal_0 [of "a_holdsunde_lockhash_primea" "?z_hth", OF z_Htg])
  have z_Htv: "?z_htv" (is "?z_htw&?z_hty")
  by (rule zenon_and_0 [OF z_Htu])
  have z_Hua: "?z_hua" (is "\\A x : ?z_huf(x)")
  by (rule zenon_and_1 [OF z_Htu])
  have z_Htw: "?z_htw" (is "?z_hny<=>?z_htx")
  by (rule zenon_and_0 [OF z_Htv])
  show FALSE
  proof (rule zenon_equiv [OF z_Htw])
   assume z_Hqr:"(~?z_hny)"
   assume z_Hve:"(~?z_htx)"
   show FALSE
   by (rule zenon_notisafcn_except [of "a_holdsunde_locka" "(CHOOSE x:((x \\in Node)&(((a_lockunde_msghash_primea=except(a_lockunde_msga, x, TRUE))&((a_grantunde_msghash_primea=a_grantunde_msga)&((a_holdsunde_lockhash_primea=a_holdsunde_locka)&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka)))))|((a_serverunde_holdsunde_locka&((a_lockunde_msga[x])&((a_serverunde_holdsunde_lockhash_primea=FALSE)&((a_lockunde_msghash_primea=except(a_lockunde_msga, x, FALSE))&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, TRUE))&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_holdsunde_lockhash_primea=a_holdsunde_locka)))))))|(((a_grantunde_msga[x])&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, FALSE))&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, TRUE))&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|(((a_holdsunde_locka[x])&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, FALSE))&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, TRUE))&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_grantunde_msghash_primea=a_grantunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|((a_unlockunde_msga[x])&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, FALSE))&((a_serverunde_holdsunde_lockhash_primea=TRUE)&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_grantunde_msghash_primea=a_grantunde_msga)&(a_holdsunde_lockhash_primea=a_holdsunde_locka))))))))))))" "FALSE", OF z_Hve])
  next
   assume z_Hny:"?z_hny"
   assume z_Htx:"?z_htx"
   show FALSE
   proof (rule zenon_notin_funcset [of "a_holdsunde_lockhash_primea" "Node" "{TRUE, FALSE}", OF z_Hkz])
    assume z_Hqr:"(~?z_hny)"
    show FALSE
    by (rule notE [OF z_Hqr z_Hny])
   next
    assume z_Hqt:"(DOMAIN(a_holdsunde_lockhash_primea)~=Node)" (is "?z_hob~=_")
    have z_Hvf: "(DOMAIN(?z_hth)~=Node)" (is "?z_htz~=_")
    by (rule subst [where P="(\<lambda>zenon_Vlw. (DOMAIN(zenon_Vlw)~=Node))", OF z_Htg z_Hqt])
    have z_Hqv: "(?z_hnu~=Node)"
    by (rule zenon_domain_except_0 [of "(\<lambda>zenon_Vkw. (zenon_Vkw~=Node))" "a_holdsunde_locka" "(CHOOSE x:((x \\in Node)&(((a_lockunde_msghash_primea=except(a_lockunde_msga, x, TRUE))&((a_grantunde_msghash_primea=a_grantunde_msga)&((a_holdsunde_lockhash_primea=a_holdsunde_locka)&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka)))))|((a_serverunde_holdsunde_locka&((a_lockunde_msga[x])&((a_serverunde_holdsunde_lockhash_primea=FALSE)&((a_lockunde_msghash_primea=except(a_lockunde_msga, x, FALSE))&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, TRUE))&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_holdsunde_lockhash_primea=a_holdsunde_locka)))))))|(((a_grantunde_msga[x])&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, FALSE))&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, TRUE))&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|(((a_holdsunde_locka[x])&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, FALSE))&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, TRUE))&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_grantunde_msghash_primea=a_grantunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|((a_unlockunde_msga[x])&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, FALSE))&((a_serverunde_holdsunde_lockhash_primea=TRUE)&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_grantunde_msghash_primea=a_grantunde_msga)&(a_holdsunde_lockhash_primea=a_holdsunde_locka))))))))))))" "FALSE", OF z_Hvf])
    show FALSE
    by (rule notE [OF z_Hqv z_Hnt])
   next
    assume z_Hqw:"(~(\\A zenon_Vjb:((zenon_Vjb \\in Node)=>((a_holdsunde_lockhash_primea[zenon_Vjb]) \\in {TRUE, FALSE}))))" (is "~(\\A x : ?z_hqy(x))")
    have z_Hqz: "(\\E zenon_Vjb:(~((zenon_Vjb \\in Node)=>((a_holdsunde_lockhash_primea[zenon_Vjb]) \\in {TRUE, FALSE}))))" (is "\\E x : ?z_hra(x)")
    by (rule zenon_notallex_0 [of "?z_hqy", OF z_Hqw])
    have z_Hrb: "?z_hra((CHOOSE zenon_Vjb:(~((zenon_Vjb \\in Node)=>((a_holdsunde_lockhash_primea[zenon_Vjb]) \\in {TRUE, FALSE})))))" (is "~(?z_hpz=>?z_hqi)")
    by (rule zenon_ex_choose_0 [of "?z_hra", OF z_Hqz])
    have z_Hpz: "?z_hpz"
    by (rule zenon_notimply_0 [OF z_Hrb])
    have z_Hqh: "(~?z_hqi)"
    by (rule zenon_notimply_1 [OF z_Hrb])
    have z_Hvg: "(~((a_holdsunde_lockhash_primea[(CHOOSE zenon_Vjb:(~((zenon_Vjb \\in Node)=>((a_holdsunde_lockhash_primea[zenon_Vjb]) \\in {TRUE, FALSE}))))]) \\in {FALSE}))" (is "~?z_hvh")
    by (rule zenon_notin_addElt_1 [of "(a_holdsunde_lockhash_primea[(CHOOSE zenon_Vjb:(~((zenon_Vjb \\in Node)=>((a_holdsunde_lockhash_primea[zenon_Vjb]) \\in {TRUE, FALSE}))))])" "TRUE" "{FALSE}", OF z_Hqh])
    have z_Hvi: "((a_holdsunde_lockhash_primea[(CHOOSE zenon_Vjb:(~((zenon_Vjb \\in Node)=>((a_holdsunde_lockhash_primea[zenon_Vjb]) \\in {TRUE, FALSE}))))])~=FALSE)" (is "?z_hqj~=?z_hk")
    by (rule zenon_notin_addElt_0 [of "?z_hqj" "?z_hk" "{}", OF z_Hvg])
    have z_Hrd: "((CHOOSE zenon_Vjb:(~((zenon_Vjb \\in Node)=>((a_holdsunde_lockhash_primea[zenon_Vjb]) \\in {TRUE, ?z_hk})))) \\in ?z_hnu)" (is "?z_hrd")
    by (rule ssubst [where P="(\<lambda>zenon_Vixb. ((CHOOSE zenon_Vjb:(~((zenon_Vjb \\in Node)=>((a_holdsunde_lockhash_primea[zenon_Vjb]) \\in {TRUE, ?z_hk})))) \\in zenon_Vixb))", OF z_Hnt z_Hpz])
    have z_Hvj: "?z_huf((CHOOSE zenon_Vjb:(~((zenon_Vjb \\in Node)=>((a_holdsunde_lockhash_primea[zenon_Vjb]) \\in {TRUE, ?z_hk})))))" (is "_=?z_hvk")
    by (rule zenon_all_0 [of "?z_huf" "(CHOOSE zenon_Vjb:(~((zenon_Vjb \\in Node)=>((a_holdsunde_lockhash_primea[zenon_Vjb]) \\in {TRUE, ?z_hk}))))", OF z_Hua])
    show FALSE
    proof (rule zenon_fapplyexcept [of "(\<lambda>zenon_Vsyb. (?z_hqj=zenon_Vsyb))" "a_holdsunde_locka" "(CHOOSE x:((x \\in Node)&(((a_lockunde_msghash_primea=except(a_lockunde_msga, x, TRUE))&((a_grantunde_msghash_primea=a_grantunde_msga)&((a_holdsunde_lockhash_primea=a_holdsunde_locka)&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka)))))|((a_serverunde_holdsunde_locka&((a_lockunde_msga[x])&((a_serverunde_holdsunde_lockhash_primea=?z_hk)&((a_lockunde_msghash_primea=except(a_lockunde_msga, x, ?z_hk))&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, TRUE))&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_holdsunde_lockhash_primea=a_holdsunde_locka)))))))|(((a_grantunde_msga[x])&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, ?z_hk))&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, TRUE))&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|(((a_holdsunde_locka[x])&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, ?z_hk))&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, TRUE))&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_grantunde_msghash_primea=a_grantunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|((a_unlockunde_msga[x])&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, ?z_hk))&((a_serverunde_holdsunde_lockhash_primea=TRUE)&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_grantunde_msghash_primea=a_grantunde_msga)&(a_holdsunde_lockhash_primea=a_holdsunde_locka))))))))))))" "?z_hk" "(CHOOSE zenon_Vjb:(~((zenon_Vjb \\in Node)=>((a_holdsunde_lockhash_primea[zenon_Vjb]) \\in {TRUE, ?z_hk}))))", OF z_Hvj])
     assume z_Hrd:"?z_hrd"
     assume z_Hrm:"((CHOOSE x:((x \\in Node)&(((a_lockunde_msghash_primea=except(a_lockunde_msga, x, TRUE))&((a_grantunde_msghash_primea=a_grantunde_msga)&((a_holdsunde_lockhash_primea=a_holdsunde_locka)&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka)))))|((a_serverunde_holdsunde_locka&((a_lockunde_msga[x])&((a_serverunde_holdsunde_lockhash_primea=?z_hk)&((a_lockunde_msghash_primea=except(a_lockunde_msga, x, ?z_hk))&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, TRUE))&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_holdsunde_lockhash_primea=a_holdsunde_locka)))))))|(((a_grantunde_msga[x])&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, ?z_hk))&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, TRUE))&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|(((a_holdsunde_locka[x])&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, ?z_hk))&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, TRUE))&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_grantunde_msghash_primea=a_grantunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|((a_unlockunde_msga[x])&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, ?z_hk))&((a_serverunde_holdsunde_lockhash_primea=TRUE)&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_grantunde_msghash_primea=a_grantunde_msga)&(a_holdsunde_lockhash_primea=a_holdsunde_locka))))))))))))=(CHOOSE zenon_Vjb:(~((zenon_Vjb \\in Node)=>((a_holdsunde_lockhash_primea[zenon_Vjb]) \\in {TRUE, ?z_hk})))))" (is "?z_hhd=?z_hqa")
     assume z_Hvl:"(?z_hqj=?z_hk)"
     show FALSE
     by (rule notE [OF z_Hvi z_Hvl])
    next
     assume z_Hrd:"?z_hrd"
     assume z_Hro:"((CHOOSE x:((x \\in Node)&(((a_lockunde_msghash_primea=except(a_lockunde_msga, x, TRUE))&((a_grantunde_msghash_primea=a_grantunde_msga)&((a_holdsunde_lockhash_primea=a_holdsunde_locka)&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka)))))|((a_serverunde_holdsunde_locka&((a_lockunde_msga[x])&((a_serverunde_holdsunde_lockhash_primea=?z_hk)&((a_lockunde_msghash_primea=except(a_lockunde_msga, x, ?z_hk))&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, TRUE))&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_holdsunde_lockhash_primea=a_holdsunde_locka)))))))|(((a_grantunde_msga[x])&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, ?z_hk))&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, TRUE))&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|(((a_holdsunde_locka[x])&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, ?z_hk))&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, TRUE))&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_grantunde_msghash_primea=a_grantunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|((a_unlockunde_msga[x])&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, ?z_hk))&((a_serverunde_holdsunde_lockhash_primea=TRUE)&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_grantunde_msghash_primea=a_grantunde_msga)&(a_holdsunde_lockhash_primea=a_holdsunde_locka))))))))))))~=(CHOOSE zenon_Vjb:(~((zenon_Vjb \\in Node)=>((a_holdsunde_lockhash_primea[zenon_Vjb]) \\in {TRUE, ?z_hk})))))" (is "?z_hhd~=?z_hqa")
     assume z_Hqk:"(?z_hqj=(a_holdsunde_locka[?z_hqa]))" (is "_=?z_hql")
     show FALSE
     by (rule zenon_L13_ [OF z_Hpt z_Hpz z_Hqh z_Hqk])
    next
     assume z_Hrp:"(~?z_hrd)"
     show FALSE
     by (rule notE [OF z_Hrp z_Hrd])
    qed
   qed
  qed
 qed
 assume z_Hb:"(~((a_lockunde_msghash_primea \\in FuncSet(Node, {TRUE, FALSE}))&((a_grantunde_msghash_primea \\in FuncSet(Node, {TRUE, FALSE}))&((a_unlockunde_msghash_primea \\in FuncSet(Node, {TRUE, FALSE}))&((a_holdsunde_lockhash_primea \\in FuncSet(Node, {TRUE, FALSE}))&(a_serverunde_holdsunde_lockhash_primea \\in {TRUE, FALSE}))))))" (is "~(?z_his&?z_hvn)")
 have z_Hc: "?z_hc" (is "?z_hd&?z_hw")
 by (rule zenon_and_0 [OF z_Ha])
 have z_Hdp: "?z_hdp"
 by (rule zenon_and_1 [OF z_Ha])
 have z_Hd: "?z_hd" (is "?z_he&?z_hl")
 by (rule zenon_and_0 [OF z_Hc])
 have z_He: "?z_he"
 by (rule zenon_and_0 [OF z_Hd])
 have z_Hl: "?z_hl" (is "?z_hm&?z_ho")
 by (rule zenon_and_1 [OF z_Hd])
 have z_Hm: "?z_hm"
 by (rule zenon_and_0 [OF z_Hl])
 have z_Ho: "?z_ho" (is "?z_hp&?z_hr")
 by (rule zenon_and_1 [OF z_Hl])
 have z_Hp: "?z_hp"
 by (rule zenon_and_0 [OF z_Ho])
 have z_Hr: "?z_hr" (is "?z_hs&?z_hu")
 by (rule zenon_and_1 [OF z_Ho])
 have z_Hs: "?z_hs"
 by (rule zenon_and_0 [OF z_Hr])
 have z_Hu: "?z_hu"
 by (rule zenon_and_1 [OF z_Hr])
 have z_Hvq_z_Hdp: "(\\E x:((x \\in Node)&(((a_lockunde_msghash_primea=except(a_lockunde_msga, x, TRUE))&((a_grantunde_msghash_primea=a_grantunde_msga)&((a_holdsunde_lockhash_primea=a_holdsunde_locka)&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka)))))|((a_serverunde_holdsunde_locka&((a_lockunde_msga[x])&((a_serverunde_holdsunde_lockhash_primea=FALSE)&((a_lockunde_msghash_primea=except(a_lockunde_msga, x, FALSE))&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, TRUE))&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_holdsunde_lockhash_primea=a_holdsunde_locka)))))))|(((a_grantunde_msga[x])&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, FALSE))&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, TRUE))&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|(((a_holdsunde_locka[x])&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, FALSE))&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, TRUE))&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_grantunde_msghash_primea=a_grantunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|((a_unlockunde_msga[x])&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, FALSE))&((a_serverunde_holdsunde_lockhash_primea=TRUE)&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_grantunde_msghash_primea=a_grantunde_msga)&(a_holdsunde_lockhash_primea=a_holdsunde_locka)))))))))))) == ?z_hdp" (is "?z_hvq == _")
 by (unfold bEx_def)
 have z_Hvq: "?z_hvq" (is "\\E x : ?z_hvr(x)")
 by (unfold z_Hvq_z_Hdp, fact z_Hdp)
 have z_Hvs: "?z_hvr((CHOOSE x:((x \\in Node)&(((a_lockunde_msghash_primea=except(a_lockunde_msga, x, TRUE))&((a_grantunde_msghash_primea=a_grantunde_msga)&((a_holdsunde_lockhash_primea=a_holdsunde_locka)&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka)))))|((a_serverunde_holdsunde_locka&((a_lockunde_msga[x])&((a_serverunde_holdsunde_lockhash_primea=FALSE)&((a_lockunde_msghash_primea=except(a_lockunde_msga, x, FALSE))&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, TRUE))&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_holdsunde_lockhash_primea=a_holdsunde_locka)))))))|(((a_grantunde_msga[x])&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, FALSE))&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, TRUE))&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|(((a_holdsunde_locka[x])&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, FALSE))&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, TRUE))&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_grantunde_msghash_primea=a_grantunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|((a_unlockunde_msga[x])&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, FALSE))&((a_serverunde_holdsunde_lockhash_primea=TRUE)&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_grantunde_msghash_primea=a_grantunde_msga)&(a_holdsunde_lockhash_primea=a_holdsunde_locka)))))))))))))" (is "?z_hvt&?z_hvu")
 by (rule zenon_ex_choose_0 [of "?z_hvr", OF z_Hvq])
 have z_Hvu: "?z_hvu" (is "?z_hvv|?z_hvw")
 by (rule zenon_and_1 [OF z_Hvs])
 show FALSE
 proof (rule zenon_or [OF z_Hvu])
  assume z_Hvv:"?z_hvv" (is "?z_hhb&?z_hdx")
  have z_Hhb: "?z_hhb" (is "_=?z_hhc")
  by (rule zenon_and_0 [OF z_Hvv])
  have z_Hdx: "?z_hdx" (is "?z_hdy&?z_hea")
  by (rule zenon_and_1 [OF z_Hvv])
  have z_Hdy: "?z_hdy"
  by (rule zenon_and_0 [OF z_Hdx])
  have z_Hea: "?z_hea" (is "?z_heb&?z_hed")
  by (rule zenon_and_1 [OF z_Hdx])
  have z_Heb: "?z_heb"
  by (rule zenon_and_0 [OF z_Hea])
  have z_Hed: "?z_hed" (is "?z_hee&?z_heg")
  by (rule zenon_and_1 [OF z_Hea])
  have z_Hee: "?z_hee"
  by (rule zenon_and_0 [OF z_Hed])
  have z_Heg: "?z_heg"
  by (rule zenon_and_1 [OF z_Hed])
  show FALSE
  proof (rule zenon_in_addElt [of "a_serverunde_holdsunde_locka" "TRUE" "{FALSE}", OF z_Hu])
   assume z_Hle:"(a_serverunde_holdsunde_locka=TRUE)" (is "_=?z_hj")
   show FALSE
   proof (rule zenon_notand [OF z_Hb])
    assume z_Hir:"(~?z_his)"
    show FALSE
    by (rule zenon_L2_ [OF z_Hhb z_Hir z_He])
   next
    assume z_Hvx:"(~?z_hvn)" (is "~(?z_hkr&?z_hvo)")
    show FALSE
    proof (rule zenon_notand [OF z_Hvx])
     assume z_Hkq:"(~?z_hkr)"
     show FALSE
     by (rule zenon_L3_ [OF z_Hkq z_Hm z_Hdy])
    next
     assume z_Hvy:"(~?z_hvo)" (is "~(?z_hkx&?z_hvp)")
     show FALSE
     proof (rule zenon_notand [OF z_Hvy])
      assume z_Hkw:"(~?z_hkx)"
      show FALSE
      by (rule zenon_L4_ [OF z_Hkw z_Hp z_Hee])
     next
      assume z_Hvz:"(~?z_hvp)" (is "~(?z_hla&?z_hld)")
      show FALSE
      proof (rule zenon_notand [OF z_Hvz])
       assume z_Hkz:"(~?z_hla)"
       show FALSE
       by (rule zenon_L5_ [OF z_Hkz z_Hs z_Heb])
      next
       assume z_Hlc:"(~?z_hld)"
       show FALSE
       by (rule zenon_L6_ [OF z_Hlc z_Hle z_Heg])
      qed
     qed
    qed
   qed
  next
   assume z_Hwa:"(a_serverunde_holdsunde_locka \\in {FALSE})" (is "?z_hwa")
   show FALSE
   proof (rule zenon_in_addElt [of "a_serverunde_holdsunde_locka" "FALSE" "{}", OF z_Hwa])
    assume z_Hlj:"(a_serverunde_holdsunde_locka=FALSE)" (is "_=?z_hk")
    show FALSE
    proof (rule zenon_notand [OF z_Hb])
     assume z_Hir:"(~?z_his)"
     show FALSE
     by (rule zenon_L2_ [OF z_Hhb z_Hir z_He])
    next
     assume z_Hvx:"(~?z_hvn)" (is "~(?z_hkr&?z_hvo)")
     show FALSE
     proof (rule zenon_notand [OF z_Hvx])
      assume z_Hkq:"(~?z_hkr)"
      show FALSE
      by (rule zenon_L3_ [OF z_Hkq z_Hm z_Hdy])
     next
      assume z_Hvy:"(~?z_hvo)" (is "~(?z_hkx&?z_hvp)")
      show FALSE
      proof (rule zenon_notand [OF z_Hvy])
       assume z_Hkw:"(~?z_hkx)"
       show FALSE
       by (rule zenon_L4_ [OF z_Hkw z_Hp z_Hee])
      next
       assume z_Hvz:"(~?z_hvp)" (is "~(?z_hla&?z_hld)")
       show FALSE
       proof (rule zenon_notand [OF z_Hvz])
        assume z_Hkz:"(~?z_hla)"
        show FALSE
        by (rule zenon_L5_ [OF z_Hkz z_Hs z_Heb])
       next
        assume z_Hlc:"(~?z_hld)"
        show FALSE
        by (rule zenon_L7_ [OF z_Hlc z_Hlj z_Heg])
       qed
      qed
     qed
    qed
   next
    assume z_Hwb:"(a_serverunde_holdsunde_locka \\in {})" (is "?z_hwb")
    show FALSE
    by (rule zenon_in_emptyset [of "a_serverunde_holdsunde_locka", OF z_Hwb])
   qed
  qed
 next
  assume z_Hvw:"?z_hvw" (is "?z_hwc|?z_hwd")
  show FALSE
  proof (rule zenon_or [OF z_Hvw])
   assume z_Hwc:"?z_hwc" (is "_&?z_hwe")
   have z_Hwe: "?z_hwe" (is "?z_hwf&?z_hwg")
   by (rule zenon_and_1 [OF z_Hwc])
   have z_Hwg: "?z_hwg" (is "?z_hen&?z_hwh")
   by (rule zenon_and_1 [OF z_Hwe])
   have z_Hen: "?z_hen" (is "_=?z_hk")
   by (rule zenon_and_0 [OF z_Hwg])
   have z_Hwh: "?z_hwh" (is "?z_hwi&?z_hwj")
   by (rule zenon_and_1 [OF z_Hwg])
   have z_Hwi: "?z_hwi" (is "_=?z_hwk")
   by (rule zenon_and_0 [OF z_Hwh])
   have z_Hwj: "?z_hwj" (is "?z_hwl&?z_heu")
   by (rule zenon_and_1 [OF z_Hwh])
   have z_Hwl: "?z_hwl" (is "_=?z_hmr")
   by (rule zenon_and_0 [OF z_Hwj])
   have z_Heu: "?z_heu" (is "?z_hee&?z_heb")
   by (rule zenon_and_1 [OF z_Hwj])
   have z_Hee: "?z_hee"
   by (rule zenon_and_0 [OF z_Heu])
   have z_Heb: "?z_heb"
   by (rule zenon_and_1 [OF z_Heu])
   show FALSE
   proof (rule zenon_notand [OF z_Hb])
    assume z_Hir:"(~?z_his)"
    have z_Hit: "(DOMAIN(a_lockunde_msga)=Node)" (is "?z_hiu=_")
    by (rule zenon_in_funcset_1 [of "a_lockunde_msga" "Node" "{TRUE, ?z_hk}", OF z_He])
    have z_Hit: "(?z_hiu=Node)"
    by (rule zenon_in_funcset_1 [of "a_lockunde_msga" "Node" "{TRUE, ?z_hk}", OF z_He])
    have z_Hga: "(\\A zenon_Vea:((zenon_Vea \\in Node)=>((a_lockunde_msga[zenon_Vea]) \\in {TRUE, ?z_hk})))" (is "\\A x : ?z_hgt(x)")
    by (rule zenon_in_funcset_2 [of "a_lockunde_msga" "Node" "{TRUE, ?z_hk}", OF z_He])
    have z_Hwm: "(((isAFcn(a_lockunde_msghash_primea)<=>isAFcn(?z_hwk))&(DOMAIN(a_lockunde_msghash_primea)=DOMAIN(?z_hwk)))&(\\A zenon_Vgkd:((a_lockunde_msghash_primea[zenon_Vgkd])=(?z_hwk[zenon_Vgkd]))))" (is "?z_hwn&?z_hws")
    by (rule zenon_funequal_0 [of "a_lockunde_msghash_primea" "?z_hwk", OF z_Hwi])
    have z_Hwn: "?z_hwn" (is "?z_hwo&?z_hwq")
    by (rule zenon_and_0 [OF z_Hwm])
    have z_Hws: "?z_hws" (is "\\A x : ?z_hwx(x)")
    by (rule zenon_and_1 [OF z_Hwm])
    have z_Hwo: "?z_hwo" (is "?z_hiy<=>?z_hwp")
    by (rule zenon_and_0 [OF z_Hwn])
    show FALSE
    proof (rule zenon_equiv [OF z_Hwo])
     assume z_Hjj:"(~?z_hiy)"
     assume z_Hwy:"(~?z_hwp)"
     show FALSE
     by (rule zenon_notisafcn_except [of "a_lockunde_msga" "(CHOOSE x:((x \\in Node)&(((a_lockunde_msghash_primea=except(a_lockunde_msga, x, TRUE))&((a_grantunde_msghash_primea=a_grantunde_msga)&(?z_heb&(?z_hee&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka)))))|((a_serverunde_holdsunde_locka&((a_lockunde_msga[x])&(?z_hen&((a_lockunde_msghash_primea=except(a_lockunde_msga, x, ?z_hk))&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, TRUE))&?z_heu)))))|(((a_grantunde_msga[x])&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, ?z_hk))&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, TRUE))&((a_lockunde_msghash_primea=a_lockunde_msga)&(?z_hee&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|(((a_holdsunde_locka[x])&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, ?z_hk))&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, TRUE))&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_grantunde_msghash_primea=a_grantunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|((a_unlockunde_msga[x])&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, ?z_hk))&((a_serverunde_holdsunde_lockhash_primea=TRUE)&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_grantunde_msghash_primea=a_grantunde_msga)&?z_heb)))))))))))" "?z_hk", OF z_Hwy])
    next
     assume z_Hiy:"?z_hiy"
     assume z_Hwp:"?z_hwp"
     show FALSE
     proof (rule zenon_notin_funcset [of "a_lockunde_msghash_primea" "Node" "{TRUE, ?z_hk}", OF z_Hir])
      assume z_Hjj:"(~?z_hiy)"
      show FALSE
      by (rule notE [OF z_Hjj z_Hiy])
     next
      assume z_Hjl:"(DOMAIN(a_lockunde_msghash_primea)~=Node)" (is "?z_hjb~=_")
      have z_Hwz: "(DOMAIN(?z_hwk)~=Node)" (is "?z_hwr~=_")
      by (rule subst [where P="(\<lambda>zenon_Vlw. (DOMAIN(zenon_Vlw)~=Node))", OF z_Hwi z_Hjl])
      have z_Hjr: "(?z_hiu~=Node)"
      by (rule zenon_domain_except_0 [of "(\<lambda>zenon_Vkw. (zenon_Vkw~=Node))" "a_lockunde_msga" "(CHOOSE x:((x \\in Node)&(((a_lockunde_msghash_primea=except(a_lockunde_msga, x, TRUE))&((a_grantunde_msghash_primea=a_grantunde_msga)&(?z_heb&(?z_hee&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka)))))|((a_serverunde_holdsunde_locka&((a_lockunde_msga[x])&(?z_hen&((a_lockunde_msghash_primea=except(a_lockunde_msga, x, ?z_hk))&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, TRUE))&?z_heu)))))|(((a_grantunde_msga[x])&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, ?z_hk))&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, TRUE))&((a_lockunde_msghash_primea=a_lockunde_msga)&(?z_hee&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|(((a_holdsunde_locka[x])&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, ?z_hk))&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, TRUE))&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_grantunde_msghash_primea=a_grantunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|((a_unlockunde_msga[x])&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, ?z_hk))&((a_serverunde_holdsunde_lockhash_primea=TRUE)&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_grantunde_msghash_primea=a_grantunde_msga)&?z_heb)))))))))))" "?z_hk", OF z_Hwz])
      show FALSE
      by (rule notE [OF z_Hjr z_Hit])
     next
      assume z_Hjv:"(~(\\A zenon_Vlha:((zenon_Vlha \\in Node)=>((a_lockunde_msghash_primea[zenon_Vlha]) \\in {TRUE, ?z_hk}))))" (is "~(\\A x : ?z_hjx(x))")
      have z_Hjy: "(\\E zenon_Vlha:(~((zenon_Vlha \\in Node)=>((a_lockunde_msghash_primea[zenon_Vlha]) \\in {TRUE, ?z_hk}))))" (is "\\E x : ?z_hjz(x)")
      by (rule zenon_notallex_0 [of "?z_hjx", OF z_Hjv])
      have z_Hka: "?z_hjz((CHOOSE zenon_Vlha:(~((zenon_Vlha \\in Node)=>((a_lockunde_msghash_primea[zenon_Vlha]) \\in {TRUE, ?z_hk})))))" (is "~(?z_hgg=>?z_hgp)")
      by (rule zenon_ex_choose_0 [of "?z_hjz", OF z_Hjy])
      have z_Hgg: "?z_hgg"
      by (rule zenon_notimply_0 [OF z_Hka])
      have z_Hgo: "(~?z_hgp)"
      by (rule zenon_notimply_1 [OF z_Hka])
      have z_Hxa: "(~((a_lockunde_msghash_primea[(CHOOSE zenon_Vlha:(~((zenon_Vlha \\in Node)=>((a_lockunde_msghash_primea[zenon_Vlha]) \\in {TRUE, ?z_hk}))))]) \\in {?z_hk}))" (is "~?z_hxb")
      by (rule zenon_notin_addElt_1 [of "(a_lockunde_msghash_primea[(CHOOSE zenon_Vlha:(~((zenon_Vlha \\in Node)=>((a_lockunde_msghash_primea[zenon_Vlha]) \\in {TRUE, ?z_hk}))))])" "TRUE" "{?z_hk}", OF z_Hgo])
      have z_Hxc: "((a_lockunde_msghash_primea[(CHOOSE zenon_Vlha:(~((zenon_Vlha \\in Node)=>((a_lockunde_msghash_primea[zenon_Vlha]) \\in {TRUE, ?z_hk}))))])~=?z_hk)" (is "?z_hgq~=_")
      by (rule zenon_notin_addElt_0 [of "?z_hgq" "?z_hk" "{}", OF z_Hxa])
      have z_Hkd: "((CHOOSE zenon_Vlha:(~((zenon_Vlha \\in Node)=>((a_lockunde_msghash_primea[zenon_Vlha]) \\in {TRUE, ?z_hk})))) \\in ?z_hiu)" (is "?z_hkd")
      by (rule ssubst [where P="(\<lambda>zenon_Vagb. ((CHOOSE zenon_Vlha:(~((zenon_Vlha \\in Node)=>((a_lockunde_msghash_primea[zenon_Vlha]) \\in {TRUE, ?z_hk})))) \\in zenon_Vagb))", OF z_Hit z_Hgg])
      have z_Hxd: "?z_hwx((CHOOSE zenon_Vlha:(~((zenon_Vlha \\in Node)=>((a_lockunde_msghash_primea[zenon_Vlha]) \\in {TRUE, ?z_hk})))))" (is "_=?z_hxe")
      by (rule zenon_all_0 [of "?z_hwx" "(CHOOSE zenon_Vlha:(~((zenon_Vlha \\in Node)=>((a_lockunde_msghash_primea[zenon_Vlha]) \\in {TRUE, ?z_hk}))))", OF z_Hws])
      show FALSE
      proof (rule zenon_fapplyexcept [of "(\<lambda>zenon_Vqhb. (?z_hgq=zenon_Vqhb))" "a_lockunde_msga" "(CHOOSE x:((x \\in Node)&(((a_lockunde_msghash_primea=except(a_lockunde_msga, x, TRUE))&((a_grantunde_msghash_primea=a_grantunde_msga)&(?z_heb&(?z_hee&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka)))))|((a_serverunde_holdsunde_locka&((a_lockunde_msga[x])&(?z_hen&((a_lockunde_msghash_primea=except(a_lockunde_msga, x, ?z_hk))&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, TRUE))&?z_heu)))))|(((a_grantunde_msga[x])&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, ?z_hk))&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, TRUE))&((a_lockunde_msghash_primea=a_lockunde_msga)&(?z_hee&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|(((a_holdsunde_locka[x])&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, ?z_hk))&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, TRUE))&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_grantunde_msghash_primea=a_grantunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|((a_unlockunde_msga[x])&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, ?z_hk))&((a_serverunde_holdsunde_lockhash_primea=TRUE)&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_grantunde_msghash_primea=a_grantunde_msga)&?z_heb)))))))))))" "?z_hk" "(CHOOSE zenon_Vlha:(~((zenon_Vlha \\in Node)=>((a_lockunde_msghash_primea[zenon_Vlha]) \\in {TRUE, ?z_hk}))))", OF z_Hxd])
       assume z_Hkd:"?z_hkd"
       assume z_Hkm:"((CHOOSE x:((x \\in Node)&(((a_lockunde_msghash_primea=except(a_lockunde_msga, x, TRUE))&((a_grantunde_msghash_primea=a_grantunde_msga)&(?z_heb&(?z_hee&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka)))))|((a_serverunde_holdsunde_locka&((a_lockunde_msga[x])&(?z_hen&((a_lockunde_msghash_primea=except(a_lockunde_msga, x, ?z_hk))&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, TRUE))&?z_heu)))))|(((a_grantunde_msga[x])&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, ?z_hk))&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, TRUE))&((a_lockunde_msghash_primea=a_lockunde_msga)&(?z_hee&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|(((a_holdsunde_locka[x])&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, ?z_hk))&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, TRUE))&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_grantunde_msghash_primea=a_grantunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|((a_unlockunde_msga[x])&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, ?z_hk))&((a_serverunde_holdsunde_lockhash_primea=TRUE)&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_grantunde_msghash_primea=a_grantunde_msga)&?z_heb)))))))))))=(CHOOSE zenon_Vlha:(~((zenon_Vlha \\in Node)=>((a_lockunde_msghash_primea[zenon_Vlha]) \\in {TRUE, ?z_hk})))))" (is "?z_hhd=?z_hgh")
       assume z_Hxf:"(?z_hgq=?z_hk)"
       show FALSE
       by (rule notE [OF z_Hxc z_Hxf])
      next
       assume z_Hkd:"?z_hkd"
       assume z_Hko:"((CHOOSE x:((x \\in Node)&(((a_lockunde_msghash_primea=except(a_lockunde_msga, x, TRUE))&((a_grantunde_msghash_primea=a_grantunde_msga)&(?z_heb&(?z_hee&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka)))))|((a_serverunde_holdsunde_locka&((a_lockunde_msga[x])&(?z_hen&((a_lockunde_msghash_primea=except(a_lockunde_msga, x, ?z_hk))&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, TRUE))&?z_heu)))))|(((a_grantunde_msga[x])&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, ?z_hk))&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, TRUE))&((a_lockunde_msghash_primea=a_lockunde_msga)&(?z_hee&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|(((a_holdsunde_locka[x])&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, ?z_hk))&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, TRUE))&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_grantunde_msghash_primea=a_grantunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|((a_unlockunde_msga[x])&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, ?z_hk))&((a_serverunde_holdsunde_lockhash_primea=TRUE)&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_grantunde_msghash_primea=a_grantunde_msga)&?z_heb)))))))))))~=(CHOOSE zenon_Vlha:(~((zenon_Vlha \\in Node)=>((a_lockunde_msghash_primea[zenon_Vlha]) \\in {TRUE, ?z_hk})))))" (is "?z_hhd~=?z_hgh")
       assume z_Hgr:"(?z_hgq=(a_lockunde_msga[?z_hgh]))" (is "_=?z_hgs")
       show FALSE
       by (rule zenon_L1_ [OF z_Hga z_Hgg z_Hgo z_Hgr])
      next
       assume z_Hkp:"(~?z_hkd)"
       show FALSE
       by (rule notE [OF z_Hkp z_Hkd])
      qed
     qed
    qed
   next
    assume z_Hvx:"(~?z_hvn)" (is "~(?z_hkr&?z_hvo)")
    show FALSE
    proof (rule zenon_notand [OF z_Hvx])
     assume z_Hkq:"(~?z_hkr)"
     have z_Hit: "(DOMAIN(a_lockunde_msga)=Node)" (is "?z_hiu=_")
     by (rule zenon_in_funcset_1 [of "a_lockunde_msga" "Node" "{TRUE, ?z_hk}", OF z_He])
     have z_Hns: "(DOMAIN(a_grantunde_msga)=Node)" (is "?z_hmu=_")
     by (rule zenon_in_funcset_1 [of "a_grantunde_msga" "Node" "{TRUE, ?z_hk}", OF z_Hm])
     have z_Hns: "(?z_hmu=Node)"
     by (rule zenon_in_funcset_1 [of "a_grantunde_msga" "Node" "{TRUE, ?z_hk}", OF z_Hm])
     have z_Hlo: "(\\A zenon_Vba:((zenon_Vba \\in Node)=>((a_grantunde_msga[zenon_Vba]) \\in {TRUE, ?z_hk})))" (is "\\A x : ?z_hmh(x)")
     by (rule zenon_in_funcset_2 [of "a_grantunde_msga" "Node" "{TRUE, ?z_hk}", OF z_Hm])
     have z_Hxg: "(((isAFcn(a_grantunde_msghash_primea)<=>isAFcn(?z_hmr))&(DOMAIN(a_grantunde_msghash_primea)=DOMAIN(?z_hmr)))&(\\A zenon_Vekd:((a_grantunde_msghash_primea[zenon_Vekd])=(?z_hmr[zenon_Vekd]))))" (is "?z_hxh&?z_hmm")
     by (rule zenon_funequal_0 [of "a_grantunde_msghash_primea" "?z_hmr", OF z_Hwl])
     have z_Hxh: "?z_hxh" (is "?z_hxi&?z_hxk")
     by (rule zenon_and_0 [OF z_Hxg])
     have z_Hmm: "?z_hmm" (is "\\A x : ?z_hmv(x)")
     by (rule zenon_and_1 [OF z_Hxg])
     have z_Hxi: "?z_hxi" (is "?z_hom<=>?z_hxj")
     by (rule zenon_and_0 [OF z_Hxh])
     show FALSE
     proof (rule zenon_equiv [OF z_Hxi])
      assume z_Hor:"(~?z_hom)"
      assume z_Hxm:"(~?z_hxj)"
      show FALSE
      by (rule zenon_notisafcn_except [of "a_grantunde_msga" "(CHOOSE x:((x \\in Node)&(((a_lockunde_msghash_primea=except(a_lockunde_msga, x, TRUE))&((a_grantunde_msghash_primea=a_grantunde_msga)&(?z_heb&(?z_hee&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka)))))|((a_serverunde_holdsunde_locka&((a_lockunde_msga[x])&(?z_hen&((a_lockunde_msghash_primea=except(a_lockunde_msga, x, ?z_hk))&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, TRUE))&?z_heu)))))|(((a_grantunde_msga[x])&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, ?z_hk))&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, TRUE))&((a_lockunde_msghash_primea=a_lockunde_msga)&(?z_hee&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|(((a_holdsunde_locka[x])&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, ?z_hk))&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, TRUE))&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_grantunde_msghash_primea=a_grantunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|((a_unlockunde_msga[x])&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, ?z_hk))&((a_serverunde_holdsunde_lockhash_primea=TRUE)&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_grantunde_msghash_primea=a_grantunde_msga)&?z_heb)))))))))))" "TRUE", OF z_Hxm])
     next
      assume z_Hom:"?z_hom"
      assume z_Hxj:"?z_hxj"
      have z_Hwm: "(((isAFcn(a_lockunde_msghash_primea)<=>isAFcn(?z_hwk))&(DOMAIN(a_lockunde_msghash_primea)=DOMAIN(?z_hwk)))&(\\A zenon_Vgkd:((a_lockunde_msghash_primea[zenon_Vgkd])=(?z_hwk[zenon_Vgkd]))))" (is "?z_hwn&?z_hws")
      by (rule zenon_funequal_0 [of "a_lockunde_msghash_primea" "?z_hwk", OF z_Hwi])
      have z_Hws: "?z_hws" (is "\\A x : ?z_hwx(x)")
      by (rule zenon_and_1 [OF z_Hwm])
      show FALSE
      proof (rule zenon_notin_funcset [of "a_grantunde_msghash_primea" "Node" "{TRUE, ?z_hk}", OF z_Hkq])
       assume z_Hor:"(~?z_hom)"
       show FALSE
       by (rule notE [OF z_Hor z_Hom])
      next
       assume z_Hot:"(DOMAIN(a_grantunde_msghash_primea)~=Node)" (is "?z_hop~=_")
       have z_Hxn: "(DOMAIN(?z_hmr)~=Node)" (is "?z_hxl~=_")
       by (rule subst [where P="(\<lambda>zenon_Vlw. (DOMAIN(zenon_Vlw)~=Node))", OF z_Hwl z_Hot])
       have z_Hov: "(?z_hmu~=Node)"
       by (rule zenon_domain_except_0 [of "(\<lambda>zenon_Vkw. (zenon_Vkw~=Node))" "a_grantunde_msga" "(CHOOSE x:((x \\in Node)&(((a_lockunde_msghash_primea=except(a_lockunde_msga, x, TRUE))&((a_grantunde_msghash_primea=a_grantunde_msga)&(?z_heb&(?z_hee&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka)))))|((a_serverunde_holdsunde_locka&((a_lockunde_msga[x])&(?z_hen&((a_lockunde_msghash_primea=except(a_lockunde_msga, x, ?z_hk))&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, TRUE))&?z_heu)))))|(((a_grantunde_msga[x])&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, ?z_hk))&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, TRUE))&((a_lockunde_msghash_primea=a_lockunde_msga)&(?z_hee&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|(((a_holdsunde_locka[x])&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, ?z_hk))&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, TRUE))&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_grantunde_msghash_primea=a_grantunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|((a_unlockunde_msga[x])&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, ?z_hk))&((a_serverunde_holdsunde_lockhash_primea=TRUE)&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_grantunde_msghash_primea=a_grantunde_msga)&?z_heb)))))))))))" "TRUE", OF z_Hxn])
       show FALSE
       by (rule notE [OF z_Hov z_Hns])
      next
       assume z_How:"(~(\\A zenon_Vvw:((zenon_Vvw \\in Node)=>((a_grantunde_msghash_primea[zenon_Vvw]) \\in {TRUE, ?z_hk}))))" (is "~(\\A x : ?z_hoy(x))")
       have z_Hoz: "(\\E zenon_Vvw:(~((zenon_Vvw \\in Node)=>((a_grantunde_msghash_primea[zenon_Vvw]) \\in {TRUE, ?z_hk}))))" (is "\\E x : ?z_hpa(x)")
       by (rule zenon_notallex_0 [of "?z_hoy", OF z_How])
       have z_Hpb: "?z_hpa((CHOOSE zenon_Vvw:(~((zenon_Vvw \\in Node)=>((a_grantunde_msghash_primea[zenon_Vvw]) \\in {TRUE, ?z_hk})))))" (is "~(?z_hlu=>?z_hmd)")
       by (rule zenon_ex_choose_0 [of "?z_hpa", OF z_Hoz])
       have z_Hlu: "?z_hlu"
       by (rule zenon_notimply_0 [OF z_Hpb])
       have z_Hmc: "(~?z_hmd)"
       by (rule zenon_notimply_1 [OF z_Hpb])
       have z_Hxo: "((a_grantunde_msghash_primea[(CHOOSE zenon_Vvw:(~((zenon_Vvw \\in Node)=>((a_grantunde_msghash_primea[zenon_Vvw]) \\in {TRUE, ?z_hk}))))])~=TRUE)" (is "?z_hme~=?z_hj")
       by (rule zenon_notin_addElt_0 [of "?z_hme" "?z_hj" "{?z_hk}", OF z_Hmc])
       have z_Hxp: "((CHOOSE zenon_Vvw:(~((zenon_Vvw \\in Node)=>((a_grantunde_msghash_primea[zenon_Vvw]) \\in {?z_hj, ?z_hk})))) \\in ?z_hiu)" (is "?z_hxp")
       by (rule ssubst [where P="(\<lambda>zenon_Vtea. ((CHOOSE zenon_Vvw:(~((zenon_Vvw \\in Node)=>((a_grantunde_msghash_primea[zenon_Vvw]) \\in {?z_hj, ?z_hk})))) \\in zenon_Vtea))", OF z_Hit z_Hlu])
       have z_Hmt: "((CHOOSE zenon_Vvw:(~((zenon_Vvw \\in Node)=>((a_grantunde_msghash_primea[zenon_Vvw]) \\in {?z_hj, ?z_hk})))) \\in ?z_hmu)" (is "?z_hmt")
       by (rule ssubst [where P="(\<lambda>zenon_Vtea. ((CHOOSE zenon_Vvw:(~((zenon_Vvw \\in Node)=>((a_grantunde_msghash_primea[zenon_Vvw]) \\in {?z_hj, ?z_hk})))) \\in zenon_Vtea))", OF z_Hns z_Hlu])
       have z_Hxq: "?z_hwx((CHOOSE zenon_Vvw:(~((zenon_Vvw \\in Node)=>((a_grantunde_msghash_primea[zenon_Vvw]) \\in {?z_hj, ?z_hk})))))" (is "?z_hxr=?z_hxs")
       by (rule zenon_all_0 [of "?z_hwx" "(CHOOSE zenon_Vvw:(~((zenon_Vvw \\in Node)=>((a_grantunde_msghash_primea[zenon_Vvw]) \\in {?z_hj, ?z_hk}))))", OF z_Hws])
       show FALSE
       proof (rule zenon_fapplyexcept [of "(\<lambda>zenon_Vztd. (?z_hxr=zenon_Vztd))" "a_lockunde_msga" "(CHOOSE x:((x \\in Node)&(((a_lockunde_msghash_primea=except(a_lockunde_msga, x, ?z_hj))&((a_grantunde_msghash_primea=a_grantunde_msga)&(?z_heb&(?z_hee&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka)))))|((a_serverunde_holdsunde_locka&((a_lockunde_msga[x])&(?z_hen&((a_lockunde_msghash_primea=except(a_lockunde_msga, x, ?z_hk))&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, ?z_hj))&?z_heu)))))|(((a_grantunde_msga[x])&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, ?z_hk))&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, ?z_hj))&((a_lockunde_msghash_primea=a_lockunde_msga)&(?z_hee&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|(((a_holdsunde_locka[x])&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, ?z_hk))&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, ?z_hj))&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_grantunde_msghash_primea=a_grantunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|((a_unlockunde_msga[x])&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, ?z_hk))&((a_serverunde_holdsunde_lockhash_primea=?z_hj)&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_grantunde_msghash_primea=a_grantunde_msga)&?z_heb)))))))))))" "?z_hk" "(CHOOSE zenon_Vvw:(~((zenon_Vvw \\in Node)=>((a_grantunde_msghash_primea[zenon_Vvw]) \\in {?z_hj, ?z_hk}))))", OF z_Hxq])
        assume z_Hxp:"?z_hxp"
        assume z_Hnb:"((CHOOSE x:((x \\in Node)&(((a_lockunde_msghash_primea=except(a_lockunde_msga, x, ?z_hj))&((a_grantunde_msghash_primea=a_grantunde_msga)&(?z_heb&(?z_hee&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka)))))|((a_serverunde_holdsunde_locka&((a_lockunde_msga[x])&(?z_hen&((a_lockunde_msghash_primea=except(a_lockunde_msga, x, ?z_hk))&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, ?z_hj))&?z_heu)))))|(((a_grantunde_msga[x])&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, ?z_hk))&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, ?z_hj))&((a_lockunde_msghash_primea=a_lockunde_msga)&(?z_hee&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|(((a_holdsunde_locka[x])&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, ?z_hk))&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, ?z_hj))&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_grantunde_msghash_primea=a_grantunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|((a_unlockunde_msga[x])&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, ?z_hk))&((a_serverunde_holdsunde_lockhash_primea=?z_hj)&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_grantunde_msghash_primea=a_grantunde_msga)&?z_heb)))))))))))=(CHOOSE zenon_Vvw:(~((zenon_Vvw \\in Node)=>((a_grantunde_msghash_primea[zenon_Vvw]) \\in {?z_hj, ?z_hk})))))" (is "?z_hhd=?z_hlv")
        assume z_Hxw:"(?z_hxr=?z_hk)"
        have z_Hmw: "?z_hmv(?z_hlv)" (is "_=?z_hmx")
        by (rule zenon_all_0 [of "?z_hmv" "?z_hlv", OF z_Hmm])
        show FALSE
        proof (rule zenon_fapplyexcept [of "(\<lambda>zenon_Vchd. (?z_hme=zenon_Vchd))" "a_grantunde_msga" "?z_hhd" "?z_hj" "?z_hlv", OF z_Hmw])
         assume z_Hmt:"?z_hmt"
         assume z_Hnb:"(?z_hhd=?z_hlv)"
         assume z_Hnc:"(?z_hme=?z_hj)"
         show FALSE
         by (rule notE [OF z_Hxo z_Hnc])
        next
         assume z_Hmt:"?z_hmt"
         assume z_Hms:"(?z_hhd~=?z_hlv)"
         assume z_Hmf:"(?z_hme=(a_grantunde_msga[?z_hlv]))" (is "_=?z_hmg")
         show FALSE
         by (rule notE [OF z_Hms z_Hnb])
        next
         assume z_Hnd:"(~?z_hmt)"
         show FALSE
         by (rule notE [OF z_Hnd z_Hmt])
        qed
       next
        assume z_Hxp:"?z_hxp"
        assume z_Hms:"((CHOOSE x:((x \\in Node)&(((a_lockunde_msghash_primea=except(a_lockunde_msga, x, ?z_hj))&((a_grantunde_msghash_primea=a_grantunde_msga)&(?z_heb&(?z_hee&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka)))))|((a_serverunde_holdsunde_locka&((a_lockunde_msga[x])&(?z_hen&((a_lockunde_msghash_primea=except(a_lockunde_msga, x, ?z_hk))&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, ?z_hj))&?z_heu)))))|(((a_grantunde_msga[x])&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, ?z_hk))&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, ?z_hj))&((a_lockunde_msghash_primea=a_lockunde_msga)&(?z_hee&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|(((a_holdsunde_locka[x])&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, ?z_hk))&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, ?z_hj))&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_grantunde_msghash_primea=a_grantunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|((a_unlockunde_msga[x])&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, ?z_hk))&((a_serverunde_holdsunde_lockhash_primea=?z_hj)&((a_lockunde_msghash_primea=a_lockunde_msga)&((a_grantunde_msghash_primea=a_grantunde_msga)&?z_heb)))))))))))~=(CHOOSE zenon_Vvw:(~((zenon_Vvw \\in Node)=>((a_grantunde_msghash_primea[zenon_Vvw]) \\in {?z_hj, ?z_hk})))))" (is "?z_hhd~=?z_hlv")
        assume z_Hxx:"(?z_hxr=(a_lockunde_msga[?z_hlv]))" (is "_=?z_hxy")
        show FALSE
        by (rule zenon_L9_ [OF z_Hmm z_Hms z_Hlo z_Hlu z_Hmc z_Hmt])
       next
        assume z_Hxz:"(~?z_hxp)"
        show FALSE
        by (rule notE [OF z_Hxz z_Hxp])
       qed
      qed
     qed
    next
     assume z_Hvy:"(~?z_hvo)" (is "~(?z_hkx&?z_hvp)")
     show FALSE
     proof (rule zenon_notand [OF z_Hvy])
      assume z_Hkw:"(~?z_hkx)"
      show FALSE
      by (rule zenon_L4_ [OF z_Hkw z_Hp z_Hee])
     next
      assume z_Hvz:"(~?z_hvp)" (is "~(?z_hla&?z_hld)")
      show FALSE
      proof (rule zenon_notand [OF z_Hvz])
       assume z_Hkz:"(~?z_hla)"
       show FALSE
       by (rule zenon_L5_ [OF z_Hkz z_Hs z_Heb])
      next
       assume z_Hlc:"(~?z_hld)"
       have z_Hlk: "(~(a_serverunde_holdsunde_lockhash_primea \\in {?z_hk}))" (is "~?z_hll")
       by (rule zenon_notin_addElt_1 [of "a_serverunde_holdsunde_lockhash_primea" "TRUE" "{?z_hk}", OF z_Hlc])
       have z_Hlm: "(a_serverunde_holdsunde_lockhash_primea~=?z_hk)"
       by (rule zenon_notin_addElt_0 [of "a_serverunde_holdsunde_lockhash_primea" "?z_hk" "{}", OF z_Hlk])
       show FALSE
       by (rule notE [OF z_Hlm z_Hen])
      qed
     qed
    qed
   qed
  next
   assume z_Hwd:"?z_hwd" (is "?z_hya|?z_hyb")
   show FALSE
   proof (rule zenon_or [OF z_Hwd])
    assume z_Hya:"?z_hya" (is "?z_hyc&?z_hyd")
    have z_Hyd: "?z_hyd" (is "?z_hnp&?z_hye")
    by (rule zenon_and_1 [OF z_Hya])
    have z_Hnp: "?z_hnp" (is "_=?z_hnk")
    by (rule zenon_and_0 [OF z_Hyd])
    have z_Hye: "?z_hye" (is "?z_hnq&?z_hfe")
    by (rule zenon_and_1 [OF z_Hyd])
    have z_Hnq: "?z_hnq" (is "_=?z_hnr")
    by (rule zenon_and_0 [OF z_Hye])
    have z_Hfe: "?z_hfe" (is "?z_hff&?z_hed")
    by (rule zenon_and_1 [OF z_Hye])
    have z_Hff: "?z_hff"
    by (rule zenon_and_0 [OF z_Hfe])
    have z_Hed: "?z_hed" (is "?z_hee&?z_heg")
    by (rule zenon_and_1 [OF z_Hfe])
    have z_Hee: "?z_hee"
    by (rule zenon_and_0 [OF z_Hed])
    have z_Heg: "?z_heg"
    by (rule zenon_and_1 [OF z_Hed])
    show FALSE
    proof (rule zenon_in_addElt [of "a_serverunde_holdsunde_locka" "TRUE" "{FALSE}", OF z_Hu])
     assume z_Hle:"(a_serverunde_holdsunde_locka=TRUE)" (is "_=?z_hj")
     show FALSE
     proof (rule zenon_notand [OF z_Hb])
      assume z_Hir:"(~?z_his)"
      show FALSE
      by (rule zenon_L10_ [OF z_Hir z_He z_Hff])
     next
      assume z_Hvx:"(~?z_hvn)" (is "~(?z_hkr&?z_hvo)")
      show FALSE
      proof (rule zenon_notand [OF z_Hvx])
       assume z_Hkq:"(~?z_hkr)"
       show FALSE
       by (rule zenon_L12_ [OF z_Hm z_Hkq z_Hnp z_Hnq z_Hs])
      next
       assume z_Hvy:"(~?z_hvo)" (is "~(?z_hkx&?z_hvp)")
       show FALSE
       proof (rule zenon_notand [OF z_Hvy])
        assume z_Hkw:"(~?z_hkx)"
        show FALSE
        by (rule zenon_L4_ [OF z_Hkw z_Hp z_Hee])
       next
        assume z_Hvz:"(~?z_hvp)" (is "~(?z_hla&?z_hld)")
        show FALSE
        proof (rule zenon_notand [OF z_Hvz])
         assume z_Hkz:"(~?z_hla)"
         show FALSE
         by (rule zenon_L14_ [OF z_Hnq z_Hkz z_Hs])
        next
         assume z_Hlc:"(~?z_hld)"
         show FALSE
         by (rule zenon_L6_ [OF z_Hlc z_Hle z_Heg])
        qed
       qed
      qed
     qed
    next
     assume z_Hwa:"(a_serverunde_holdsunde_locka \\in {FALSE})" (is "?z_hwa")
     show FALSE
     proof (rule zenon_in_addElt [of "a_serverunde_holdsunde_locka" "FALSE" "{}", OF z_Hwa])
      assume z_Hlj:"(a_serverunde_holdsunde_locka=FALSE)" (is "_=?z_hk")
      show FALSE
      proof (rule zenon_notand [OF z_Hb])
       assume z_Hir:"(~?z_his)"
       show FALSE
       by (rule zenon_L10_ [OF z_Hir z_He z_Hff])
      next
       assume z_Hvx:"(~?z_hvn)" (is "~(?z_hkr&?z_hvo)")
       show FALSE
       proof (rule zenon_notand [OF z_Hvx])
        assume z_Hkq:"(~?z_hkr)"
        show FALSE
        by (rule zenon_L12_ [OF z_Hm z_Hkq z_Hnp z_Hnq z_Hs])
       next
        assume z_Hvy:"(~?z_hvo)" (is "~(?z_hkx&?z_hvp)")
        show FALSE
        proof (rule zenon_notand [OF z_Hvy])
         assume z_Hkw:"(~?z_hkx)"
         show FALSE
         by (rule zenon_L4_ [OF z_Hkw z_Hp z_Hee])
        next
         assume z_Hvz:"(~?z_hvp)" (is "~(?z_hla&?z_hld)")
         show FALSE
         proof (rule zenon_notand [OF z_Hvz])
          assume z_Hkz:"(~?z_hla)"
          show FALSE
          by (rule zenon_L14_ [OF z_Hnq z_Hkz z_Hs])
         next
          assume z_Hlc:"(~?z_hld)"
          show FALSE
          by (rule zenon_L7_ [OF z_Hlc z_Hlj z_Heg])
         qed
        qed
       qed
      qed
     next
      assume z_Hwb:"(a_serverunde_holdsunde_locka \\in {})" (is "?z_hwb")
      show FALSE
      by (rule zenon_in_emptyset [of "a_serverunde_holdsunde_locka", OF z_Hwb])
     qed
    qed
   next
    assume z_Hyb:"?z_hyb" (is "?z_hyf|?z_hyg")
    show FALSE
    proof (rule zenon_or [OF z_Hyb])
     assume z_Hyf:"?z_hyf" (is "?z_hyh&?z_hyi")
     have z_Hyi: "?z_hyi" (is "?z_htg&?z_hyj")
     by (rule zenon_and_1 [OF z_Hyf])
     have z_Htg: "?z_htg" (is "_=?z_hth")
     by (rule zenon_and_0 [OF z_Hyi])
     have z_Hyj: "?z_hyj" (is "?z_hti&?z_hfp")
     by (rule zenon_and_1 [OF z_Hyi])
     have z_Hti: "?z_hti" (is "_=?z_hst")
     by (rule zenon_and_0 [OF z_Hyj])
     have z_Hfp: "?z_hfp" (is "?z_hff&?z_hfq")
     by (rule zenon_and_1 [OF z_Hyj])
     have z_Hff: "?z_hff"
     by (rule zenon_and_0 [OF z_Hfp])
     have z_Hfq: "?z_hfq" (is "?z_hdy&?z_heg")
     by (rule zenon_and_1 [OF z_Hfp])
     have z_Hdy: "?z_hdy"
     by (rule zenon_and_0 [OF z_Hfq])
     have z_Heg: "?z_heg"
     by (rule zenon_and_1 [OF z_Hfq])
     show FALSE
     proof (rule zenon_in_addElt [of "a_serverunde_holdsunde_locka" "TRUE" "{FALSE}", OF z_Hu])
      assume z_Hle:"(a_serverunde_holdsunde_locka=TRUE)" (is "_=?z_hj")
      show FALSE
      proof (rule zenon_notand [OF z_Hb])
       assume z_Hir:"(~?z_his)"
       show FALSE
       by (rule zenon_L10_ [OF z_Hir z_He z_Hff])
      next
       assume z_Hvx:"(~?z_hvn)" (is "~(?z_hkr&?z_hvo)")
       show FALSE
       proof (rule zenon_notand [OF z_Hvx])
        assume z_Hkq:"(~?z_hkr)"
        show FALSE
        by (rule zenon_L3_ [OF z_Hkq z_Hm z_Hdy])
       next
        assume z_Hvy:"(~?z_hvo)" (is "~(?z_hkx&?z_hvp)")
        show FALSE
        proof (rule zenon_notand [OF z_Hvy])
         assume z_Hkw:"(~?z_hkx)"
         show FALSE
         by (rule zenon_L17_ [OF z_Hp z_Htg z_Hkw z_Hti z_Hs])
        next
         assume z_Hvz:"(~?z_hvp)" (is "~(?z_hla&?z_hld)")
         show FALSE
         proof (rule zenon_notand [OF z_Hvz])
          assume z_Hkz:"(~?z_hla)"
          show FALSE
          by (rule zenon_L18_ [OF z_Htg z_Hkz z_Hs])
         next
          assume z_Hlc:"(~?z_hld)"
          show FALSE
          by (rule zenon_L6_ [OF z_Hlc z_Hle z_Heg])
         qed
        qed
       qed
      qed
     next
      assume z_Hwa:"(a_serverunde_holdsunde_locka \\in {FALSE})" (is "?z_hwa")
      show FALSE
      proof (rule zenon_in_addElt [of "a_serverunde_holdsunde_locka" "FALSE" "{}", OF z_Hwa])
       assume z_Hlj:"(a_serverunde_holdsunde_locka=FALSE)" (is "_=?z_hk")
       show FALSE
       proof (rule zenon_notand [OF z_Hb])
        assume z_Hir:"(~?z_his)"
        show FALSE
        by (rule zenon_L10_ [OF z_Hir z_He z_Hff])
       next
        assume z_Hvx:"(~?z_hvn)" (is "~(?z_hkr&?z_hvo)")
        show FALSE
        proof (rule zenon_notand [OF z_Hvx])
         assume z_Hkq:"(~?z_hkr)"
         show FALSE
         by (rule zenon_L3_ [OF z_Hkq z_Hm z_Hdy])
        next
         assume z_Hvy:"(~?z_hvo)" (is "~(?z_hkx&?z_hvp)")
         show FALSE
         proof (rule zenon_notand [OF z_Hvy])
          assume z_Hkw:"(~?z_hkx)"
          show FALSE
          by (rule zenon_L17_ [OF z_Hp z_Htg z_Hkw z_Hti z_Hs])
         next
          assume z_Hvz:"(~?z_hvp)" (is "~(?z_hla&?z_hld)")
          show FALSE
          proof (rule zenon_notand [OF z_Hvz])
           assume z_Hkz:"(~?z_hla)"
           show FALSE
           by (rule zenon_L18_ [OF z_Htg z_Hkz z_Hs])
          next
           assume z_Hlc:"(~?z_hld)"
           show FALSE
           by (rule zenon_L7_ [OF z_Hlc z_Hlj z_Heg])
          qed
         qed
        qed
       qed
      next
       assume z_Hwb:"(a_serverunde_holdsunde_locka \\in {})" (is "?z_hwb")
       show FALSE
       by (rule zenon_in_emptyset [of "a_serverunde_holdsunde_locka", OF z_Hwb])
      qed
     qed
    next
     assume z_Hyg:"?z_hyg" (is "?z_hyk&?z_hyl")
     have z_Hyl: "?z_hyl" (is "?z_hym&?z_hfw")
     by (rule zenon_and_1 [OF z_Hyg])
     have z_Hym: "?z_hym" (is "_=?z_hyn")
     by (rule zenon_and_0 [OF z_Hyl])
     have z_Hfw: "?z_hfw" (is "?z_hfx&?z_hfy")
     by (rule zenon_and_1 [OF z_Hyl])
     have z_Hfx: "?z_hfx" (is "_=?z_hj")
     by (rule zenon_and_0 [OF z_Hfw])
     have z_Hfy: "?z_hfy" (is "?z_hff&?z_hfz")
     by (rule zenon_and_1 [OF z_Hfw])
     have z_Hff: "?z_hff"
     by (rule zenon_and_0 [OF z_Hfy])
     have z_Hfz: "?z_hfz" (is "?z_hdy&?z_heb")
     by (rule zenon_and_1 [OF z_Hfy])
     have z_Hdy: "?z_hdy"
     by (rule zenon_and_0 [OF z_Hfz])
     have z_Heb: "?z_heb"
     by (rule zenon_and_1 [OF z_Hfz])
     show FALSE
     proof (rule zenon_notand [OF z_Hb])
      assume z_Hir:"(~?z_his)"
      show FALSE
      by (rule zenon_L10_ [OF z_Hir z_He z_Hff])
     next
      assume z_Hvx:"(~?z_hvn)" (is "~(?z_hkr&?z_hvo)")
      show FALSE
      proof (rule zenon_notand [OF z_Hvx])
       assume z_Hkq:"(~?z_hkr)"
       show FALSE
       by (rule zenon_L3_ [OF z_Hkq z_Hm z_Hdy])
      next
       assume z_Hvy:"(~?z_hvo)" (is "~(?z_hkx&?z_hvp)")
       show FALSE
       proof (rule zenon_notand [OF z_Hvy])
        assume z_Hkw:"(~?z_hkx)"
        have z_Htj: "(DOMAIN(a_unlockunde_msga)=Node)" (is "?z_hsw=_")
        by (rule zenon_in_funcset_1 [of "a_unlockunde_msga" "Node" "{?z_hj, FALSE}", OF z_Hp])
        have z_Htj: "(?z_hsw=Node)"
        by (rule zenon_in_funcset_1 [of "a_unlockunde_msga" "Node" "{?z_hj, FALSE}", OF z_Hp])
        have z_Hrq: "(\\A zenon_Vy:((zenon_Vy \\in Node)=>((a_unlockunde_msga[zenon_Vy]) \\in {?z_hj, FALSE})))" (is "\\A x : ?z_hsj(x)")
        by (rule zenon_in_funcset_2 [of "a_unlockunde_msga" "Node" "{?z_hj, FALSE}", OF z_Hp])
        have z_Hyo: "(((isAFcn(a_unlockunde_msghash_primea)<=>isAFcn(?z_hyn))&(DOMAIN(a_unlockunde_msghash_primea)=DOMAIN(?z_hyn)))&(\\A zenon_Vza:((a_unlockunde_msghash_primea[zenon_Vza])=(?z_hyn[zenon_Vza]))))" (is "?z_hyp&?z_hyu")
        by (rule zenon_funequal_0 [of "a_unlockunde_msghash_primea" "?z_hyn", OF z_Hym])
        have z_Hyp: "?z_hyp" (is "?z_hyq&?z_hys")
        by (rule zenon_and_0 [OF z_Hyo])
        have z_Hyu: "?z_hyu" (is "\\A x : ?z_hyz(x)")
        by (rule zenon_and_1 [OF z_Hyo])
        have z_Hyq: "?z_hyq" (is "?z_htn<=>?z_hyr")
        by (rule zenon_and_0 [OF z_Hyp])
        show FALSE
        proof (rule zenon_equiv [OF z_Hyq])
         assume z_Hts:"(~?z_htn)"
         assume z_Hza:"(~?z_hyr)"
         show FALSE
         by (rule zenon_notisafcn_except [of "a_unlockunde_msga" "(CHOOSE x:((x \\in Node)&(((a_lockunde_msghash_primea=except(a_lockunde_msga, x, ?z_hj))&(?z_hdy&(?z_heb&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka)))))|((a_serverunde_holdsunde_locka&((a_lockunde_msga[x])&((a_serverunde_holdsunde_lockhash_primea=FALSE)&((a_lockunde_msghash_primea=except(a_lockunde_msga, x, FALSE))&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, ?z_hj))&((a_unlockunde_msghash_primea=a_unlockunde_msga)&?z_heb))))))|(((a_grantunde_msga[x])&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, FALSE))&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, ?z_hj))&(?z_hff&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|(((a_holdsunde_locka[x])&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, FALSE))&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, ?z_hj))&(?z_hff&(?z_hdy&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|((a_unlockunde_msga[x])&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, FALSE))&?z_hfw))))))))" "FALSE", OF z_Hza])
        next
         assume z_Htn:"?z_htn"
         assume z_Hyr:"?z_hyr"
         show FALSE
         proof (rule zenon_notin_funcset [of "a_unlockunde_msghash_primea" "Node" "{?z_hj, FALSE}", OF z_Hkw])
          assume z_Hts:"(~?z_htn)"
          show FALSE
          by (rule notE [OF z_Hts z_Htn])
         next
          assume z_Hug:"(DOMAIN(a_unlockunde_msghash_primea)~=Node)" (is "?z_htq~=_")
          have z_Hzb: "(DOMAIN(?z_hyn)~=Node)" (is "?z_hyt~=_")
          by (rule subst [where P="(\<lambda>zenon_Vlw. (DOMAIN(zenon_Vlw)~=Node))", OF z_Hym z_Hug])
          have z_Hui: "(?z_hsw~=Node)"
          by (rule zenon_domain_except_0 [of "(\<lambda>zenon_Vkw. (zenon_Vkw~=Node))" "a_unlockunde_msga" "(CHOOSE x:((x \\in Node)&(((a_lockunde_msghash_primea=except(a_lockunde_msga, x, ?z_hj))&(?z_hdy&(?z_heb&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka)))))|((a_serverunde_holdsunde_locka&((a_lockunde_msga[x])&((a_serverunde_holdsunde_lockhash_primea=FALSE)&((a_lockunde_msghash_primea=except(a_lockunde_msga, x, FALSE))&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, ?z_hj))&((a_unlockunde_msghash_primea=a_unlockunde_msga)&?z_heb))))))|(((a_grantunde_msga[x])&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, FALSE))&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, ?z_hj))&(?z_hff&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|(((a_holdsunde_locka[x])&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, FALSE))&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, ?z_hj))&(?z_hff&(?z_hdy&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|((a_unlockunde_msga[x])&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, FALSE))&?z_hfw))))))))" "FALSE", OF z_Hzb])
          show FALSE
          by (rule notE [OF z_Hui z_Htj])
         next
          assume z_Huj:"(~(\\A zenon_Vll:((zenon_Vll \\in Node)=>((a_unlockunde_msghash_primea[zenon_Vll]) \\in {?z_hj, FALSE}))))" (is "~(\\A x : ?z_hul(x))")
          have z_Hum: "(\\E zenon_Vll:(~((zenon_Vll \\in Node)=>((a_unlockunde_msghash_primea[zenon_Vll]) \\in {?z_hj, FALSE}))))" (is "\\E x : ?z_hun(x)")
          by (rule zenon_notallex_0 [of "?z_hul", OF z_Huj])
          have z_Huo: "?z_hun((CHOOSE zenon_Vll:(~((zenon_Vll \\in Node)=>((a_unlockunde_msghash_primea[zenon_Vll]) \\in {?z_hj, FALSE})))))" (is "~(?z_hrw=>?z_hsf)")
          by (rule zenon_ex_choose_0 [of "?z_hun", OF z_Hum])
          have z_Hrw: "?z_hrw"
          by (rule zenon_notimply_0 [OF z_Huo])
          have z_Hse: "(~?z_hsf)"
          by (rule zenon_notimply_1 [OF z_Huo])
          have z_Hzc: "(~((a_unlockunde_msghash_primea[(CHOOSE zenon_Vll:(~((zenon_Vll \\in Node)=>((a_unlockunde_msghash_primea[zenon_Vll]) \\in {?z_hj, FALSE}))))]) \\in {FALSE}))" (is "~?z_hzd")
          by (rule zenon_notin_addElt_1 [of "(a_unlockunde_msghash_primea[(CHOOSE zenon_Vll:(~((zenon_Vll \\in Node)=>((a_unlockunde_msghash_primea[zenon_Vll]) \\in {?z_hj, FALSE}))))])" "?z_hj" "{FALSE}", OF z_Hse])
          have z_Hze: "((a_unlockunde_msghash_primea[(CHOOSE zenon_Vll:(~((zenon_Vll \\in Node)=>((a_unlockunde_msghash_primea[zenon_Vll]) \\in {?z_hj, FALSE}))))])~=FALSE)" (is "?z_hsg~=?z_hk")
          by (rule zenon_notin_addElt_0 [of "?z_hsg" "?z_hk" "{}", OF z_Hzc])
          have z_Hsv: "((CHOOSE zenon_Vll:(~((zenon_Vll \\in Node)=>((a_unlockunde_msghash_primea[zenon_Vll]) \\in {?z_hj, ?z_hk})))) \\in ?z_hsw)" (is "?z_hsv")
          by (rule ssubst [where P="(\<lambda>zenon_Vjt. ((CHOOSE zenon_Vll:(~((zenon_Vll \\in Node)=>((a_unlockunde_msghash_primea[zenon_Vll]) \\in {?z_hj, ?z_hk})))) \\in zenon_Vjt))", OF z_Htj z_Hrw])
          have z_Hzf: "?z_hyz((CHOOSE zenon_Vll:(~((zenon_Vll \\in Node)=>((a_unlockunde_msghash_primea[zenon_Vll]) \\in {?z_hj, ?z_hk})))))" (is "_=?z_hzg")
          by (rule zenon_all_0 [of "?z_hyz" "(CHOOSE zenon_Vll:(~((zenon_Vll \\in Node)=>((a_unlockunde_msghash_primea[zenon_Vll]) \\in {?z_hj, ?z_hk}))))", OF z_Hyu])
          show FALSE
          proof (rule zenon_fapplyexcept [of "(\<lambda>zenon_Vwu. (?z_hsg=zenon_Vwu))" "a_unlockunde_msga" "(CHOOSE x:((x \\in Node)&(((a_lockunde_msghash_primea=except(a_lockunde_msga, x, ?z_hj))&(?z_hdy&(?z_heb&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka)))))|((a_serverunde_holdsunde_locka&((a_lockunde_msga[x])&((a_serverunde_holdsunde_lockhash_primea=?z_hk)&((a_lockunde_msghash_primea=except(a_lockunde_msga, x, ?z_hk))&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, ?z_hj))&((a_unlockunde_msghash_primea=a_unlockunde_msga)&?z_heb))))))|(((a_grantunde_msga[x])&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, ?z_hk))&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, ?z_hj))&(?z_hff&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|(((a_holdsunde_locka[x])&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, ?z_hk))&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, ?z_hj))&(?z_hff&(?z_hdy&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|((a_unlockunde_msga[x])&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, ?z_hk))&?z_hfw))))))))" "?z_hk" "(CHOOSE zenon_Vll:(~((zenon_Vll \\in Node)=>((a_unlockunde_msghash_primea[zenon_Vll]) \\in {?z_hj, ?z_hk}))))", OF z_Hzf])
           assume z_Hsv:"?z_hsv"
           assume z_Htd:"((CHOOSE x:((x \\in Node)&(((a_lockunde_msghash_primea=except(a_lockunde_msga, x, ?z_hj))&(?z_hdy&(?z_heb&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka)))))|((a_serverunde_holdsunde_locka&((a_lockunde_msga[x])&((a_serverunde_holdsunde_lockhash_primea=?z_hk)&((a_lockunde_msghash_primea=except(a_lockunde_msga, x, ?z_hk))&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, ?z_hj))&((a_unlockunde_msghash_primea=a_unlockunde_msga)&?z_heb))))))|(((a_grantunde_msga[x])&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, ?z_hk))&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, ?z_hj))&(?z_hff&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|(((a_holdsunde_locka[x])&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, ?z_hk))&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, ?z_hj))&(?z_hff&(?z_hdy&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|((a_unlockunde_msga[x])&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, ?z_hk))&?z_hfw))))))))=(CHOOSE zenon_Vll:(~((zenon_Vll \\in Node)=>((a_unlockunde_msghash_primea[zenon_Vll]) \\in {?z_hj, ?z_hk})))))" (is "?z_hhd=?z_hrx")
           assume z_Hzh:"(?z_hsg=?z_hk)"
           show FALSE
           by (rule notE [OF z_Hze z_Hzh])
          next
           assume z_Hsv:"?z_hsv"
           assume z_Hsu:"((CHOOSE x:((x \\in Node)&(((a_lockunde_msghash_primea=except(a_lockunde_msga, x, ?z_hj))&(?z_hdy&(?z_heb&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka)))))|((a_serverunde_holdsunde_locka&((a_lockunde_msga[x])&((a_serverunde_holdsunde_lockhash_primea=?z_hk)&((a_lockunde_msghash_primea=except(a_lockunde_msga, x, ?z_hk))&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, ?z_hj))&((a_unlockunde_msghash_primea=a_unlockunde_msga)&?z_heb))))))|(((a_grantunde_msga[x])&((a_grantunde_msghash_primea=except(a_grantunde_msga, x, ?z_hk))&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, ?z_hj))&(?z_hff&((a_unlockunde_msghash_primea=a_unlockunde_msga)&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|(((a_holdsunde_locka[x])&((a_holdsunde_lockhash_primea=except(a_holdsunde_locka, x, ?z_hk))&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, ?z_hj))&(?z_hff&(?z_hdy&(a_serverunde_holdsunde_lockhash_primea=a_serverunde_holdsunde_locka))))))|((a_unlockunde_msga[x])&((a_unlockunde_msghash_primea=except(a_unlockunde_msga, x, ?z_hk))&?z_hfw))))))))~=(CHOOSE zenon_Vll:(~((zenon_Vll \\in Node)=>((a_unlockunde_msghash_primea[zenon_Vll]) \\in {?z_hj, ?z_hk})))))" (is "?z_hhd~=?z_hrx")
           assume z_Hsh:"(?z_hsg=(a_unlockunde_msga[?z_hrx]))" (is "_=?z_hsi")
           show FALSE
           by (rule zenon_L15_ [OF z_Hrq z_Hrw z_Hse z_Hsh])
          next
           assume z_Htf:"(~?z_hsv)"
           show FALSE
           by (rule notE [OF z_Htf z_Hsv])
          qed
         qed
        qed
       next
        assume z_Hvz:"(~?z_hvp)" (is "~(?z_hla&?z_hld)")
        show FALSE
        proof (rule zenon_notand [OF z_Hvz])
         assume z_Hkz:"(~?z_hla)"
         show FALSE
         by (rule zenon_L5_ [OF z_Hkz z_Hs z_Heb])
        next
         assume z_Hlc:"(~?z_hld)"
         have z_Hlf: "(a_serverunde_holdsunde_lockhash_primea~=?z_hj)"
         by (rule zenon_notin_addElt_0 [of "a_serverunde_holdsunde_lockhash_primea" "?z_hj" "{FALSE}", OF z_Hlc])
         show FALSE
         by (rule notE [OF z_Hlf z_Hfx])
        qed
       qed
      qed
     qed
    qed
   qed
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 14"; *} qed
end
