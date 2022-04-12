theory SynchModProof
imports "../HOModel" SynchMod Product_Lexorder
begin


locale execution =
fixes HO k rho xi
constrains k :: nat and
  HO :: "nat => Proc => Proc set" and
  rho :: "nat => Proc => locState proc_state" and
  xi :: Proc
assumes star:"ALL p n. k_mod.path HO xi p n k"
  and loop:"ALL p r. p : HO r p"
  and run: "HORun (k_mod.gen_HOMachine k) rho HO" 
  and k2:"k > 2"
  and complete:"ALL p. EX t. rho t p ~= Asleep"
begin

lemma sending:
assumes s:"rho r p = Active s"
shows "ALL q. HOrcvdMsgs (k_mod.gen_HOMachine k) q (HO (Suc r) q) (rho r) p
    = (if p : HO (Suc r) q then Content s else Void)" using s
unfolding HOrcvdMsgs_def k_mod.gen_HOMachine_def k_mod.gen_sendMsg_def by simp

lemma sending_rec: 
  assumes "(HOrcvdMsgs (k_mod.gen_HOMachine k) p (HO (Suc r) p) (rho r)) q = Content v" (is "?msgs q = _")
  shows "rho r q = Active v"
proof (cases "rho r q")
  case Asleep
  hence "?msgs q = (if q : HO (Suc r) p then Bot else Void)" unfolding HOrcvdMsgs_def by auto
  thus "rho r q = Active v" using `?msgs q = Content v` by auto
next
  case (Active sq)
  hence "k_mod.gen_sendMsg q p sq = v"
  using assms unfolding k_mod.gen_HOMachine_def HOrcvdMsgs_def by auto
  thus "rho r q = Active v" using Active unfolding k_mod.gen_sendMsg_def by auto
qed

lemma starting: 
assumes prev: "0 < n --> rho (n-1) p = Asleep"
  and act: "rho n p = Active s"
  shows "s = k_mod.gen_initState"
proof -
  from act have 1: "~ always_asleep rho p"
    unfolding always_asleep_def by force
  from run prev act have 2: "first_awake rho p = n"
    by (rule first_awake_HO)
  from run have "CHOinitConfig (k_mod.gen_HOMachine k) rho (%_ _. undefined)" (is "CHOinitConfig ?A _ _")
    by (simp add: HORun_def CHORun_def)
  with 1 2 act have "CinitState ?A p s undefined"
    by (auto simp: CHOinitConfig_def)
  thus ?thesis by (simp add:k_mod.gen_HOMachine_def act)
qed

lemma transition : assumes s_def:"rho r p = Active s"
and ss_def:"rho (Suc r) p = Active ss"
shows "k_mod.gen_nextState k p s (HOrcvdMsgs (k_mod.gen_HOMachine k) p (HO (Suc r) p) (rho r)) ss" (is "k_mod.gen_nextState  _ _ _ ?msgs _")
proof -
    have "CHOnextConfig (k_mod.gen_HOMachine k) (rho r) (HO (Suc r)) (%w. undefined) (rho (Suc r))" using run by (simp add:HORun_def CHORun_def)
    then obtain sss where "rho (Suc r) p = Active sss & CnextState (k_mod.gen_HOMachine k) p s ?msgs undefined sss" using s_def 
        unfolding CHOnextConfig_def by presburger
    hence "CnextState (k_mod.gen_HOMachine k) p s ?msgs undefined ss" using ss_def by auto
    thus nxt:"k_mod.gen_nextState k p s ?msgs ss" unfolding k_mod.gen_HOMachine_def by auto
qed

(*this lemma is the induction case of the backward induction used in lemma A1.
If a node p is concordant in round r+2, we can deduce several facts about the incoming neighbours of p.*)
lemma path_conc:
assumes "rho (Suc (Suc r)) p = Active sp"
and "x sp mod k ~= 1"
and conc_ss:"k_mod.isSynch k (HOrcvdMsgs (k_mod.gen_HOMachine k) p (HO (Suc (Suc r)) p) (rho (Suc r)))"
  (is "k_mod.isSynch k ?msgs")
and "q : HO (Suc (Suc r)) p"
shows "k_mod.isSynch k (HOrcvdMsgs (k_mod.gen_HOMachine k) q (HO (Suc r) q) (rho r))" (is "k_mod.isSynch k ?msg")
and "k_mod.isReady (HOrcvdMsgs (k_mod.gen_HOMachine k) p (HO (Suc (Suc r)) p) (rho (Suc r))) -->
     k_mod.isReady (HOrcvdMsgs (k_mod.gen_HOMachine k) q (HO (Suc r) q) (rho r))"
and "EX s. rho (Suc r) q = Active s & (Suc (x s)) mod k = x sp mod k"
proof -
  have "~ rho (Suc r) p = Asleep"
  proof
    assume "rho (Suc r) p = Asleep"
    hence "sp = k_mod.gen_initState" using starting[of "Suc (Suc r)" p sp] assms by auto
    hence "?msgs p ~= Bot" using conc_ss unfolding k_mod.isSynch_def by (metis message.distinct(1) message.distinct(5))
    thus "False" using loop `rho (Suc r) p = Asleep` unfolding HOrcvdMsgs_def by auto
  qed
  then obtain ssp where ssp:"rho (Suc r) p = Active ssp" by (cases "rho (Suc r) p") auto
  hence trans:"k_mod.gen_nextState k p ssp ?msgs sp"
    using transition[of "Suc r" p ssp sp] assms by auto
  have "(EX s. rho (Suc r) q = Active s & (Suc (x s)) mod k = x sp mod k) &
    k_mod.isSynch k ?msg &
    (k_mod.isReady ?msgs --> k_mod.isReady ?msg)"
  proof (cases "rho (Suc r) q")
    case Asleep
    hence "?msgs q = Bot" 
      unfolding HOrcvdMsgs_def using assms by auto
    hence "~ k_mod.isSynch k ?msgs" unfolding k_mod.isSynch_def by (metis message.distinct(1) message.distinct(5))
    hence "False" using assms trans k_mod.gen_nextState_def by auto
    thus ?thesis by auto
  next
    case (Active sq)
    from sending have "?msgs q = Content sq" using assms `rho (Suc r) q = Active sq` by auto 
    moreover from trans assms k_mod.gen_nextState_def have coc:"k_mod.isSynch k ?msgs" by auto
    ultimately have xsq:"x sq mod k = k_mod.minMsgs ?msgs mod k"
      unfolding k_mod.isSynch_def by (metis message.distinct(3) message.inject)
    moreover from trans assms k_mod.gen_nextState_def have sucx:"x sp mod k = Suc (k_mod.minMsgs ?msgs) mod k" 
    proof (cases "k_mod.goto_level1 k ?msgs ssp | k_mod.goto_level2 k ?msgs ssp")
      case levlup:True
      hence "x ssp mod k = k - 1" using trans
        unfolding k_mod.gen_nextState_def k_mod.goto_level2_def k_mod.goto_level1_def k_mod.isSynch_def
        apply (smt ssp conc_ss k_mod.isSynch_def loop message.distinct(3) message.inject sending) done
      moreover have "x sp = 0 | x sp = Suc (k_mod.minMsgs ?msgs)" using levlup trans unfolding k_mod.gen_nextState_def by auto
      ultimately show ?thesis
        by (metis One_nat_def Suc_1 Suc_lessD Suc_pred' bits_mod_0 k2 k_mod.goto_level1_def k_mod.goto_level2_def levlup mod_Suc)
    next
      case False
      thus ?thesis using trans unfolding k_mod.gen_nextState_def by auto
    qed
    ultimately have "EX s. rho (Suc r) q = Active s & (Suc (x s)) mod k = x sp mod k"
      using `rho (Suc r) q = Active sq`
      exI[of "%s. rho (Suc r) q = Active s & Suc (x s) mod k = x sp mod k" sq] by (metis mod_Suc_eq)
    moreover from coc have "conc sq" unfolding k_mod.isSynch_def
      by (metis `?msgs q = Content sq` message.distinct(3) message.inject)
    hence "rho r q ~= Asleep" using starting[of "Suc r" q sq] Active
      unfolding k_mod.gen_initState_def Active by auto
    then obtain ssq where "rho r q = Active ssq" by (cases "rho r q") auto
    hence transq:"k_mod.gen_nextState k q ssq ?msg sq"
      using Active transition[of r q ssq sq] by auto
    from sucx xsq have "x sq mod k > 0" using `x sp mod k ~= 1`
      by (metis One_nat_def gr0I k2 mod_Suc not_numeral_less_one)
    hence "k_mod.isSynch k ?msg" using transq `conc sq`
      unfolding k_mod.gen_nextState_def k_mod.goto_level1_def k_mod.goto_level2_def by auto
    moreover from transq `x sq mod k > 0` have "~ (k_mod.goto_level1 k ?msg ssq | k_mod.goto_level2 k ?msg ssq)" 
      unfolding k_mod.goto_level2_def k_mod.goto_level1_def k_mod.gen_nextState_def
      by (smt (z3) One_nat_def Suc_1 Suc_lessD Suc_pred' k2 mod_Suc mod_less neq0_conv)
    from this transq `x sq mod k > 0` assms k_mod.gen_nextState_def
      have "ready sq --> k_mod.isReady ?msg" by auto 
    hence "k_mod.isReady ?msgs --> k_mod.isReady ?msg"
      unfolding k_mod.isReady_def using `?msgs q = Content sq` by auto 
    ultimately show ?thesis using Active by auto
  qed
  thus "k_mod.isSynch k ?msg"
    and "k_mod.isReady ?msgs --> k_mod.isReady ?msg"
    and "EX s. rho (Suc r) q = Active s & (Suc (x s)) mod k = x sp mod k" by auto
qed

lemma A1:
assumes path:"k_mod.path HO q p (t+i) (k-i)"
and "rho (t+k) p = Active sp"
and "k_mod.isSynch k (HOrcvdMsgs (k_mod.gen_HOMachine k) p (HO (t+k) p) (rho (t+k-1)))" (is "k_mod.isSynch k ?msgs")
and "x sp mod k = 0"
and "i < k"
shows "EX sxi. rho (t+i) q = Active sxi & x sxi mod k = i &
  (k_mod.isReady (HOrcvdMsgs (k_mod.gen_HOMachine k) p (HO (t+k) p) (rho (t+k-1))) --> ready sxi)"
proof -
  from path obtain seq where "seq 0 = q" and "seq (k-i) = p" and
    pat:"ALL j < k-i. seq j : HO (t+i+Suc j) (seq (Suc j))" unfolding k_mod.path_def by auto
  have "ALL j < k-i. let msgs = HOrcvdMsgs (k_mod.gen_HOMachine k) (seq (k-i-j)) (HO (t+k-j) (seq (k-i-j))) (rho (t+k-Suc j)) in
      EX s. rho (t+k-j) (seq (k-i-j)) = Active s & x s mod k = (k - j) mod k & k_mod.isSynch k msgs & (k_mod.isReady ?msgs --> k_mod.isReady msgs)"
      (is "ALL j. ?recurr_path j")
  proof
    fix j
    let ?msg = "%j. HOrcvdMsgs (k_mod.gen_HOMachine k) (seq (k-i-j)) (HO (t+k-j) (seq (k-i-j))) (rho (t+k-Suc j))"
    show "j < k-i --> (let msgs = ?msg j in EX s. rho (t+k-j) (seq (k-i-j)) = Active s &
      x s mod k = (k-j) mod k & k_mod.isSynch k msgs & (k_mod.isReady ?msgs --> k_mod.isReady msgs))"
    proof (induction j)
      case 0
      from assms `seq (k-i) = p` have "rho (t+k) (seq (k-i)) = Active sp &
        x sp mod k = (k-0) mod k & k_mod.isSynch k ?msgs & (k_mod.isReady ?msgs --> k_mod.isReady ?msgs)" by auto
      thus "0 < k-i --> (let msgs = ?msg 0 in EX s. rho (t+k-0) (seq (k-i-0)) = Active s &
        x s mod k = (k-0) mod k & k_mod.isSynch k msgs & (k_mod.isReady ?msgs --> k_mod.isReady msgs))"
        using assms by (simp add:`seq (k-i) = p`)
    next
      case (Suc j)
      show ?case
      proof
        assume "Suc j < k-i"
        hence ineg1:"k-i-Suc j < k-i" and ineg2:"t+i+Suc(k-i-Suc j) = t+k-j" and ineg:"Suc (k-i-Suc j) = k-i-j" and
        ineg3:"t+k >= Suc j" and ineg4:"Suc (t+k-Suc j) = t+k-j" and ineg5:"Suc (k - Suc(i+j)) = k-i-j" by auto
        from this pat have link:"seq (k-i-Suc j) : HO (t+k-j) (seq (k-i-j))" by auto

        from Suc.IH obtain ss where ss:"rho (t+k-j) (seq (k-i-j)) = Active ss"
          and concss:"k_mod.isSynch k (?msg j)" and modss:"x ss mod k = (k-j) mod k" and readyss:"k_mod.isReady ?msgs --> k_mod.isReady (?msg j)"
          using `Suc j < k-i` by (meson Suc_lessD)

        have "x ss mod k ~= 1"
        proof
          assume "x ss mod k = 1"
          hence "j = k - 1" using `x ss mod k = (k-j) mod k`
            by (metis One_nat_def `Suc j < k - i` diff_diff_cancel diff_less diff_zero less_Suc_eq_0_disj
            less_iff_Suc_add less_imp_le_nat mod_less mod_self zero_less_diff zero_neq_one)
          thus "False" using `Suc j < k - i` by auto
        qed
        from assms pat this ss concss modss readyss
          obtain s where "rho (t+k-Suc j) (seq (k-i-Suc j)) = Active s & Suc (x s) mod k = x ss mod k"
          and "k_mod.isReady ?msgs --> k_mod.isReady (?msg (Suc j))" and "k_mod.isSynch k (?msg (Suc j))"
            using path_conc[of "t+k-Suc (Suc j)" "seq (k-i-j)" ss "seq (k-i-Suc j)"] 
            by (smt One_nat_def Suc_diff_Suc ineg4 `Suc j < k - i` `Suc j <= t + k` link ineg2
            diff_self_eq_0 ineg le_eq_less_or_eq less_diff_conv not_add_less2 plus_1_eq_Suc)
        thus "let msgs = ?msg (Suc j) in EX s. rho (t+k-Suc j) (seq (k-i-Suc j)) = Active s &
          x s mod k = (k-Suc j) mod k & k_mod.isSynch k msgs & (k_mod.isReady ?msgs --> k_mod.isReady msgs)"
          by (smt Suc_diff_Suc add_leD2 diff_Suc_1 diff_le_self ineg le_add_diff_inverse2 le_eq_less_or_eq
          less_Suc_eq_0_disj less_numeral_extra(3) linorder_not_less mod_Suc modss zero_less_diff)
      qed
    qed
  qed
  moreover have "k-i-(k-i-1) = 1" and "t+k-(k-i-1) = t+i+1" and "k-(k-i-1) = i+1" using `i < k` by auto
  ultimately have seq1:"let msgs = HOrcvdMsgs (k_mod.gen_HOMachine k) (seq 1) (HO (t+i+1) (seq 1)) (rho (t+i)) in EX ss. 
      rho (t+i+1) (seq 1) = Active ss & x ss mod k = (i+1) mod k & k_mod.isSynch k msgs &
      (k_mod.isReady ?msgs --> k_mod.isReady msgs)" using k2 allE[of ?recurr_path "k-i-1" "?recurr_path (k-i-1)"] by auto
  let ?msgxi = "HOrcvdMsgs (k_mod.gen_HOMachine k) (seq 1) (HO (t+i+1) (seq 1)) (rho (t+i))"
  have seq1link:"q : HO (t+i+1) (seq 1)" using pat `seq 0 = q` `i < k` by fastforce
  from seq1 have concready:"k_mod.isSynch k ?msgxi & (k_mod.isReady ?msgs --> k_mod.isReady ?msgxi)" by meson
  have "rho (t+i) q ~= Asleep"
  proof 
    assume "rho (t+i) q = Asleep"
    hence "?msgxi q = Bot" using seq1link unfolding HOrcvdMsgs_def by auto 
    hence "~ k_mod.isSynch k ?msgxi" unfolding k_mod.isSynch_def by (metis message.distinct(1) message.distinct(5))
    thus "False" using seq1 by auto
  qed
  then obtain sxi where sxi:"rho (t+i) q = Active sxi" by (cases "rho (t+i) q") auto
  hence "?msgxi q = Content sxi" using seq1link unfolding HOrcvdMsgs_def by (simp add: k_mod.gen_HOMachine_def k_mod.gen_sendMsg_def)
  from sxi concready this have "k_mod.isReady ?msgs --> ready sxi" unfolding k_mod.isReady_def by auto
  from concready loop have "rho (t+i) (seq 1) ~= Asleep" unfolding k_mod.isSynch_def HOrcvdMsgs_def by fastforce
  then obtain ss1 where ss1:"rho (t+i) (seq 1) = Active ss1" by (cases "rho (t+i) (seq 1)") auto
  from seq1 obtain s1 where s1:"rho (t+i+1) (seq 1) = Active s1" and suci:"x s1 mod k = (i+1) mod k" by meson
  hence trans1:"k_mod.gen_nextState k (seq 1) ss1 ?msgxi s1" using transition ss1 s1 by auto
  have "x s1 mod k = Suc (k_mod.minMsgs ?msgxi) mod k"
    using trans1 unfolding k_mod.gen_nextState_def
    by (smt (verit, best) Suc_diff_1 assms(5) k_mod.goto_level1_def k_mod.goto_level2_def less_iff_Suc_add mod_Suc mod_mod_trivial zero_less_Suc)
  moreover have "k_mod.minMsgs ?msgxi mod k = x sxi mod k" using concready `?msgxi q = Content sxi` unfolding k_mod.minMsgs_def k_mod.isSynch_def
    by (metis (no_types, lifting) message.distinct(3) message.inject)
  ultimately have "x s1 mod k = Suc (x sxi) mod k" by (metis mod_Suc_eq)
  hence "x sxi mod k = i" using suci by (simp add: assms(5) mod_Suc)
  thus "EX sxi. rho (t+i) q = Active sxi & x sxi mod k = i & (k_mod.isReady ?msgs --> ready sxi)" using sxi `k_mod.isReady ?msgs --> ready sxi` by auto
qed

lemma A2:
assumes "i < k"
and ss:"rho i pp = Active ss"
shows "level ss = 0 & x ss <= i & forc ss = 1" using `i < k` ss
proof (induction i arbitrary: pp ss)
  case 0
  thus ?case using starting[of 0 pp] unfolding k_mod.gen_initState_def by auto
next
case (Suc ii)
  show "level ss = 0 & x ss <= Suc ii & forc ss = 1"
  proof (cases "rho ii pp")
    case Asleep
    thus "level ss = 0 & x ss <= Suc ii & forc ss = 1" using starting[of "Suc ii" pp] Suc
      unfolding k_mod.gen_initState_def by auto
  next
    case (Active sss)
    hence transp:"k_mod.gen_nextState k pp sss (HOrcvdMsgs (k_mod.gen_HOMachine k) pp (HO (Suc ii) pp) (rho ii)) ss"
      (is "k_mod.gen_nextState _ _ _ ?msgp _") using transition Suc by auto
    from Active have "?msgp pp = Content sss" using loop sending by presburger
    have "k_mod.forceMsgs (?msgp pp) : k_mod.forceMsgs ` (range ?msgp)" by blast
    moreover have "k_mod.forceMsgs (?msgp pp) = 1" using Suc.IH[of pp sss] Active `?msgp pp = Content sss` by (simp add: Suc_lessD `Suc ii < k` k_mod.forceMsgs.simps(1))
    ultimately have "k_mod.maxForce ?msgp >= 1" unfolding k_mod.maxForce_def by simp
    moreover have a:"ALL p s. ?msgp p = Content s --> x s <= ii & level s = 0 & forc s = 1" using Suc.IH sending_rec by (meson `Suc ii < k` lessI less_trans run)
    hence "ALL p. k_mod.forceMsgs (?msgp p) <= 1" 
      unfolding k_mod.maxForce_def by (metis One_nat_def diff_Suc_1 diff_is_0_eq k_mod.forceMsgs.elims le_SucI le_zero_eq)
    ultimately have forc0:"k_mod.maxForce ?msgp = 1" unfolding k_mod.maxForce_def by (simp add: le_antisym) 

    moreover have "?msgp pp = Content sss" using Active sending using loop by auto
    ultimately have pp_inf:"?msgp pp = Content sss & forc sss = k_mod.maxForce ?msgp & x sss <= ii" using a by auto
    let ?prop = "%sss pp ii. ?msgp pp = Content sss & forc sss = k_mod.maxForce ?msgp & x sss = ii"
    from pp_inf have "?prop sss pp (x sss)" and "x sss <= ii" by auto
    from pp_inf have "(LEAST i. EX s p. ?prop s p i) <= x sss" using Least_le by (smt (verit, del_insts))
    hence "k_mod.minMsgs ?msgp <= ii" using `x sss <= ii` unfolding k_mod.minMsgs_def by auto
    moreover from this `Suc ii < k` Active have non_levelup:"~ (k_mod.goto_level1 k ?msgp sss | k_mod.goto_level2 k ?msgp sss)"
      unfolding k_mod.goto_level2_def k_mod.goto_level1_def by auto
    ultimately have "x ss <= Suc ii" using transp unfolding k_mod.gen_nextState_def by auto
    moreover from Suc.IH have "level ss = 0" using transp `Suc ii < k` Active unfolding k_mod.gen_nextState_def by (metis non_levelup a pp_inf)
    moreover from forc0 have "forc ss = 1" using non_levelup transp unfolding k_mod.gen_nextState_def by auto
    ultimately show ?thesis by auto
  qed
qed 

lemma A2_bis:
assumes "rho r p = Active s"
shows "forc s >= 1 & level s <= 2 & x s <= r" using `rho r p = Active s`
proof (induction r arbitrary: p s)
  case 0
  thus ?case using starting[of 0 p s] unfolding k_mod.gen_initState_def by auto
next
case (Suc rr)
  show ?case
  proof (cases "rho rr p")
    case Asleep
    thus "forc s >= 1 & level s <= 2 & x s <= Suc rr" using starting[of "Suc rr" p s] Suc unfolding k_mod.gen_initState_def by auto
  next
    case (Active ss)
    define msgp where "msgp = HOrcvdMsgs (k_mod.gen_HOMachine k) p (HO (Suc rr) p) (rho rr)"
    have "msgp p = Content ss" using Active loop sending unfolding msgp_def by presburger
    have "k_mod.forceMsgs (msgp p) : k_mod.forceMsgs ` (range msgp)" by blast
    moreover have "k_mod.forceMsgs (msgp p) >= 1" using Suc.IH[of p ss] Active `msgp p = Content ss` by (simp add: k_mod.forceMsgs.simps(1))
    ultimately have "k_mod.maxForce msgp >= 1" unfolding k_mod.maxForce_def by (meson Max_ge_iff UNIV_not_empty finite finite_imageI image_is_empty)
    moreover have transp:"k_mod.gen_nextState k p ss msgp s" using Active transition Suc unfolding msgp_def by auto
    hence "forc s >= k_mod.maxForce msgp" unfolding k_mod.gen_nextState_def by auto
    obtain q sq where sq:"msgp q = Content sq & forc sq = k_mod.maxForce msgp" (is "?P q sq") using Max_in `1 <= k_mod.maxForce msgp` k_mod.forceMsgs.elims
      unfolding k_mod.maxForce_def by (smt (verit, ccfv_threshold) One_nat_def UNIV_not_empty finite_UNIV finite_imageI image_iff image_is_empty le_zero_eq not_less_eq_eq)
    hence "k_mod.minMsgs msgp <= x sq" using LeastI_ex unfolding k_mod.minMsgs_def by (smt (verit, del_insts) Least_le)
    moreover have "rho rr q = Active sq" using sending_rec sq unfolding msgp_def by auto
    ultimately have "k_mod.minMsgs msgp <= rr" using Suc.IH[of q sq] by simp
    thus "forc s >= 1 & level s <= 2 & x s <= Suc rr" using transp Suc.IH[of p ss] Active `k_mod.maxForce msgp >= 1` unfolding k_mod.gen_nextState_def by auto
  qed
qed

lemma adopt_incoming:
assumes "rho t p = Active sp"
and "msgs = HOrcvdMsgs (k_mod.gen_HOMachine k) p (HO (Suc t) p) (rho t)"
shows "EX q sq. rho t q = Active sq & msgs q = Content sq & q : HO (Suc t) p & forc sq = k_mod.maxForce msgs & x sq = k_mod.minMsgs msgs"
proof -
  have "msgs p = Content sp" using sending[of t p sp] assms loop unfolding HOrcvdMsgs_def by metis
  hence "k_mod.maxForce msgs >= forc sp" using Max_ge[of _ "forc sp"] finite_UNIV unfolding k_mod.maxForce_def
    by (metis finite_imageI k_mod.forceMsgs.simps(1) rangeI rev_image_eqI)
  hence "k_mod.maxForce msgs >= 1" using A2_bis[of t p sp] assms by auto
  from this obtain h sh where "msgs h = Content sh & forc sh = k_mod.maxForce msgs" (is "?P h sh") using Max_in unfolding k_mod.maxForce_def 
    by (smt (verit, ccfv_SIG) empty_not_UNIV finite_UNIV finite_imageI image_iff image_is_empty k_mod.forceMsgs.elims leD less_one)
  from this obtain qq sqq where "msgs qq = Content sqq" and "forc sqq = k_mod.maxForce msgs" and "x sqq = k_mod.minMsgs msgs"
    using LeastI_ex[of "%v. EX sh h. ?P h sh & x sh = v"] unfolding k_mod.minMsgs_def by auto
  moreover from this have "rho t qq = Active sqq & qq : HO (Suc t) p" using sending_rec[of p t qq sqq] assms unfolding HOrcvdMsgs_def by auto
  ultimately show ?thesis using assms by auto
qed
  
lemma A3:
assumes "rho r xi = Active sp"
and "rho (Suc r) xi = Active ssp"
and "level sp = 0"
and "level ssp = 1"
and "rho (r+i) q = Active sq"
and "rho (r+Suc i) q = Active ssq"
and "level sq  < level ssq"
and "i > 0"
shows "i >= k"
proof (rule ccontr)
  assume "~ i >= k"
  have transp:"k_mod.gen_nextState k xi sp (HOrcvdMsgs (k_mod.gen_HOMachine k) xi (HO (Suc r) xi) (rho r)) ssp"
    (is "k_mod.gen_nextState _ _ _ ?msgp _") using assms transition by auto
  have "Suc r >= k"
  proof (rule ccontr)
    assume "~ Suc r >= k"
    thus "False" using assms A2 by (metis not_le zero_neq_one)
  qed
  hence lev1p:"k_mod.goto_level1 k ?msgp sp" using assms transp
    unfolding k_mod.gen_nextState_def k_mod.goto_level1_def by (metis k_mod.goto_level2_def zero_neq_one) 
  hence "k_mod.isSynch k ?msgp" unfolding k_mod.goto_level1_def by auto
  from loop have self_path:"k_mod.path HO xi xi (Suc r-k+i) (k-i)" unfolding k_mod.path_def by auto
  from transp lev1p have "x ssp mod k = 0"
    unfolding k_mod.gen_nextState_def k_mod.goto_level1_def 
    by (metis (no_types, hide_lams) Suc_diff_1 add.right_neutral k2 bits_mod_0 gr_implies_not_zero linorder_neqE_nat mod_Suc_eq mod_add_self1) 
  hence val_xi:"EX sxi. rho (Suc r+i-k) xi = Active sxi & x sxi mod k = i"
    using A1[of xi xi "Suc r-k" i ssp] assms `Suc r >= k` `k_mod.isSynch k ?msgp` `~ i >= k` self_path by auto
  have transq:"k_mod.gen_nextState k q sq (HOrcvdMsgs (k_mod.gen_HOMachine k) q (HO (Suc r+i) q) (rho (r+i))) ssq"
    (is "k_mod.gen_nextState _ _ _ ?msgq _") using assms transition by auto
  hence lev1q:"k_mod.goto_level1 k ?msgq sq | k_mod.goto_level2 k ?msgq sq" using assms transp
    unfolding k_mod.gen_nextState_def k_mod.goto_level1_def k_mod.goto_level2_def zero_neq_one by auto 
  hence "k_mod.isSynch k ?msgq" unfolding k_mod.goto_level1_def k_mod.goto_level2_def by auto
  from transq lev1q have "x ssq mod k = 0" using run k2
    unfolding k_mod.gen_nextState_def k_mod.goto_level1_def k_mod.goto_level2_def
    by (smt (verit, best) Suc_1 Suc_diff_1 Suc_less_eq2 less_Suc_eq_0_disj mod_Suc mod_less) 
  hence "EX sxi. rho (Suc r+i-k) xi = Active sxi & x sxi mod k = 0" using A1[of xi q "Suc r-k+i" 0 ssq] assms k2 star `Suc r >= k` `k_mod.isSynch k ?msgq` by auto
  thus "False" using val_xi `~ i >= k` `i > 0` by auto
qed 

definition active_path where 
"active_path p q n D == EX seq. seq 0 = p & seq D = q &
    (ALL i < D. rho (n+i) (seq (Suc i)) ~= Asleep & seq i : HO (n+Suc i) (seq (Suc i)))"

lemma increasing_force:
assumes sp:"rho t p = Active sp"
shows "active_path p q t r --> rho (t+r) q = Active sq --> forc sp <= forc sq"
proof (induction r arbitrary:sq q)
  case 0
  show "active_path p q t 0 --> rho (t+0) q = Active sq --> forc sp <= forc sq" using sp unfolding active_path_def by fastforce
next
  case (Suc rr)
  show "active_path p q t (Suc rr) --> rho (t+Suc rr) q = Active sq --> forc sp <= forc sq"
  proof (rule impI)+
    assume "active_path p q t (Suc rr)" and sq:"rho (t+Suc rr) q = Active sq"
    then obtain seq where seq0:"seq 0 = p" and "seq (Suc rr) = q" and seqSuc:"ALL j < Suc rr. rho (t+j) (seq (Suc j)) ~= Asleep & seq j : HO (t+Suc j) (seq (Suc j))"
      unfolding active_path_def by auto
    have "rho (t+rr) (seq rr) ~= Asleep"
    proof (cases "rr")
      case 0
      thus "rho (t+rr) (seq rr) ~= Asleep" using seq0 sp by auto
    next
      case (Suc rrr)
      hence "rho (t+rr-1) (seq rr) ~= Asleep" using `seq (Suc rr) = q` seqSuc by auto
      thus "rho (t+rr) (seq rr) ~= Asleep" using run nonAsleepAgain
        unfolding HORun_def by (smt (z3) Suc add.commute add_Suc less_add_Suc2 plus_1_eq_Suc proc_state.simps(3) seqSuc)
    qed
    then obtain sqq where sqq:"rho (t+rr) (seq rr) = Active sqq" using run
      unfolding HORun_def by (cases "rho (t+rr) (seq rr)") auto
    have "seq rr : HO (t+Suc rr) q" using seqSuc `seq (Suc rr) = q` by auto
    hence "active_path p (seq rr) t rr" using seq0 seqSuc unfolding active_path_def by auto
    hence "forc sp <= forc sqq" using sqq Suc.IH by simp
    have "HOrcvdMsgs (k_mod.gen_HOMachine k) q (HO (t+Suc rr) q) (rho (t+rr)) (seq rr) = Content sqq" (is "?msgs (seq rr) = _")
      using sending[of "t+rr" "seq rr" sqq] sqq `seq rr : HO (t+Suc rr) q` by auto
    hence maxf:"k_mod.maxForce ?msgs >= forc sp" using `forc sp <= forc sqq` unfolding k_mod.maxForce_def
      by (smt (verit) Max_ge_iff UNIV_I UNIV_not_empty finite finite_imageI image_eqI image_is_empty k_mod.forceMsgs.simps(1))
    from `seq (Suc rr) = q` seqSuc obtain ssq where "rho (t+rr) q = Active ssq" by (cases "rho (t+rr) q") auto
    hence "k_mod.gen_nextState k q ssq ?msgs sq" using sq transition[of "t+rr" q ssq sq] by auto
    thus "forc sp <= forc sq" using maxf unfolding k_mod.gen_nextState_def by auto
  qed
qed

lemma path_shrink:
assumes "seq 0 = p"
and "seq k = q"
and "ALL j < k. seq j : HO (n+Suc j) (seq (Suc j))"
and "i <= k"
shows "k_mod.path HO (seq i) q (n+i) (k-i)"
proof  -
  have "ALL j < k-i. seq (i+j) : HO (n+i+Suc j) (seq (i+Suc j))" using assms(3) 
      by (smt (z3) add.commute add.left_commute add_Suc_right less_diff_conv)
  thus ?thesis using assms exI[of _ "%l. seq(i+l)"] unfolding k_mod.path_def by auto
qed

lemma path_extend:
assumes "active_path q qq r cc"
and "qq : HO (r+Suc cc) p"
and "rho (r+cc) p ~= Asleep"
shows "active_path q p r (Suc cc)"
proof -
  define msgp where "msgp = HOrcvdMsgs (k_mod.gen_HOMachine k) p (HO (r+Suc cc) p) (rho (r+cc))"
  from assms obtain seq where "seq 0 = q" and "seq cc = qq" and
    pat:"ALL i < cc. rho (r+i) (seq (Suc i)) ~= Asleep & seq i : HO (r+Suc i) (seq (Suc i))"
    using diff_Suc_1 unfolding active_path_def by fastforce
  define seqq where "seqq = (%l. if l = Suc cc then p else seq l)"
  have "rho (r+cc) (seqq (Suc cc)) ~= Asleep & seqq cc : HO (r+Suc cc) (seqq (Suc cc))"
    using assms `seq cc = qq` unfolding seqq_def by simp
  hence "seqq 0 = q & seqq (Suc cc) = p & (ALL i < Suc cc. rho (r+i) (seqq (Suc i)) ~= Asleep & seqq i : HO (r+Suc i) (seqq (Suc i)))"
    using `seq 0 = q` pat unfolding seqq_def by auto
  thus "active_path q p r (Suc cc)" unfolding active_path_def by auto
qed

lemma A5:
assumes sp:"rho r p = Active sp"
and maxf:"k_mod.maxForce (HOrcvdMsgs (k_mod.gen_HOMachine k) p (HO (Suc r) p) (rho r)) = f"
and minc:"Suc (k_mod.minMsgs (HOrcvdMsgs (k_mod.gen_HOMachine k) p (HO (Suc r) p) (rho r))) = c" 
shows "EX q sq sqq. rho (Suc r-c) q = Active sqq & level sqq = f-1 &
  (if f = 1 then c <= r --> rho (r-c) q = Asleep else rho (r-c) q = Active sq & level sq = f-2) &
  active_path q p (Suc r-c) c"
  using minc sp maxf sp
proof (induction c arbitrary:r p sp)
  case 0
  thus ?case by auto
next
  case cc:(Suc cc)
  define msgp where "msgp = HOrcvdMsgs (k_mod.gen_HOMachine k) p (HO (Suc r) p) (rho r)"
  obtain qq sqq where msqq:"msgp qq = Content sqq" and sqq:"rho r qq = Active sqq" and "forc sqq = k_mod.maxForce msgp" and "x sqq = cc"
    using adopt_incoming[of r p sp msgp] cc unfolding msgp_def by auto
  hence "f >= 1" using cc(4) A2_bis unfolding msgp_def by auto
  show ?case
  proof (cases r)
    case rr:(Suc rr)
    show ?thesis
    proof (cases cc)
      case 0
      define seq where "seq = (%l :: nat. (if l = 0 then qq else p))"
      have "qq : HO (Suc r) p" using msqq unfolding msgp_def HOrcvdMsgs_def by auto
      hence actp:"active_path qq p (r-cc) (Suc cc)"
        using exI[of "%s. s 0 = qq & s 1 = p & (ALL i<1. rho (r-cc+i) (s (Suc i)) ~= Asleep) & s i : HO (r-cc+Suc i) (s (Suc i))" seq] 0 sp
        add.commute add_cancel_right_right cc.prems(2) diff_zero less_numeral_extra(3) less_one loop plus_1_eq_Suc proc_state.simps(3) zero_less_Suc
        unfolding seq_def active_path_def by fastforce
      show ?thesis
      proof (cases "rho (r-1) qq")
        case Asleep
        hence "level sqq = 0" and "forc sqq = 1" using starting[of r qq sqq] sqq unfolding k_mod.gen_initState_def by auto
        hence "f = 1" using `forc sqq = k_mod.maxForce msgp` cc(4) unfolding msgp_def by auto
        thus ?thesis using Asleep actp sqq 0 `level sqq = 0` by auto
      next
        case (Active sqqq)
        define msgq where "msgq = HOrcvdMsgs (k_mod.gen_HOMachine k) qq (HO r qq) (rho (r-1))"
        hence transq:"k_mod.gen_nextState k qq sqqq msgq sqq" using 
          transition[of "r-1" qq sqqq sqq] sqq Active rr unfolding msgq_def by auto
        hence "k_mod.goto_level1 k msgq sqqq | k_mod.goto_level2 k msgq sqqq" and "forc sqq = Suc (level sqq)"
          using 0 `x sqq = cc` unfolding k_mod.gen_nextState_def by auto
        hence "level sqq = Suc (level sqqq)" using transq unfolding k_mod.gen_nextState_def k_mod.goto_level1_def k_mod.goto_level2_def by auto
        thus ?thesis using Active 0 sqq `forc sqq = Suc (level sqq)` actp
          by (metis One_nat_def cc.prems(3) Suc_1 `forc sqq = k_mod.maxForce msgp` diff_Suc_1 diff_Suc_Suc msgp_def nat.simps(3))
      qed
    next
      case (Suc ccc)
      define msgq where "msgq = HOrcvdMsgs (k_mod.gen_HOMachine k) qq (HO r qq) (rho (r-1))"
      from Suc obtain sqqq where sqqq:"rho (r-1) qq = Active sqqq" using starting[of r qq sqq] `x sqq = cc`
        sqq unfolding k_mod.gen_initState_def by (cases "rho (r-1) qq") auto
      hence transq:"k_mod.gen_nextState k qq sqqq msgq sqq" using 
        transition[of "r-1" qq sqqq sqq] sqq rr unfolding msgq_def by auto
      hence "x sqq = Suc (k_mod.minMsgs msgq)" using Suc `x sqq = cc` unfolding k_mod.gen_nextState_def by auto
      moreover have "forc sqq = k_mod.maxForce msgq" using transq Suc `x sqq = cc` unfolding k_mod.gen_nextState_def by auto
      hence "k_mod.maxForce msgq = f" using cc(4) `forc sqq = k_mod.maxForce msgp` unfolding msgp_def by auto
      ultimately have postih:"EX tr srr sr. rho (Suc r - Suc cc) tr = Active sr & level sr = f - 1 &
       (if f = 1 then cc <= r - 1 --> rho (r - Suc cc) tr = Asleep else rho (r - Suc cc) tr = Active srr & level srr = f - 2) & 
       active_path tr qq (Suc (r-1)-cc) cc"
        using cc.IH[of qq "r-1" sqqq] `x sqq = cc` rr sqqq unfolding msgq_def by auto
      have "r >= cc" using A2_bis[of r qq sqq] `x sqq = cc` sqq unfolding msgp_def by auto
      moreover from this have "rho (Suc r-Suc cc+cc) p ~= Asleep & qq : HO (Suc r-Suc cc+Suc cc) p"
        using cc.prems(4) msqq unfolding msgp_def HOrcvdMsgs_def by simp
      ultimately have "ALL tr. active_path tr qq (Suc (r-1)-cc) cc --> active_path tr p (Suc r-Suc cc) (Suc cc)"
        using rr path_extend[of _ qq "Suc (r-1)-cc" cc p] by auto
      thus ?thesis using diff_Suc_1 postih rr by fastforce
    qed
  next
    case 0
    hence "level sqq = 0" and "forc sqq = 1" and "x sqq = 0" using starting[of r qq sqq] sqq unfolding k_mod.gen_initState_def by auto
    moreover have "cc = 0" using 0 A2_bis[of r qq sqq] `x sqq = cc` sqq unfolding msgp_def by auto
    define seq where "seq = (%l :: nat. (if l = 0 then qq else p))"
    have "qq : HO (Suc r) p" using msqq unfolding msgp_def HOrcvdMsgs_def by auto
    hence actp:"active_path qq p (r-cc) (Suc cc)"
      using exI[of "%s. s 0 = qq & s 1 = p & (ALL i<1. rho (r-cc+i) (s (Suc i)) ~= Asleep) & s i : HO (r-cc+Suc i) (s (Suc i))" seq] 0 sp `cc = 0`
      add.commute add_cancel_right_right cc.prems(2) diff_zero less_numeral_extra(3) less_one loop plus_1_eq_Suc proc_state.simps(3) zero_less_Suc
      unfolding seq_def active_path_def by fastforce
    ultimately show ?thesis using sqq `x sqq = cc` `forc sqq = k_mod.maxForce msgp` sqq 0 cc(4) unfolding msgp_def by auto
  qed
qed

lemma level_force:
assumes sp:"rho t p = Active sp"
shows "level sp < forc sp" using sp
proof (induction t arbitrary:sp)
  case 0
  thus ?case using starting[of 0 p sp] unfolding k_mod.gen_initState_def by auto 
next
  case (Suc tt)
  show ?case
  proof (cases "rho tt p")
    case Asleep
    thus ?thesis using Suc starting[of "Suc tt" p sp] unfolding k_mod.gen_initState_def by auto 
  next
    case (Active spp)
    define msgp where "msgp = HOrcvdMsgs (k_mod.gen_HOMachine k) p (HO (Suc tt) p) (rho tt)"
    hence "msgp p = Content spp" using sending loop Active by auto
    hence "k_mod.maxForce msgp >= forc spp" unfolding k_mod.maxForce_def by (metis Max_ge finite_UNIV finite_imageI image_eqI k_mod.forceMsgs.simps(1) rangeI)
    moreover have transp:"k_mod.gen_nextState k p spp msgp sp" using Active Suc transition unfolding msgp_def by auto
    ultimately have "forc sp >= forc spp | forc sp = Suc (level sp)" unfolding k_mod.gen_nextState_def by presburger
    thus ?thesis using Suc.IH[of spp] Active transp unfolding k_mod.gen_nextState_def by auto
  qed
qed

lemma A6:
assumes sp:"rho (t+i) p = Active sp"
and lvup:"ALL sqq. t > 0 --> rho (t-1) q = Active sqq --> level sqq < level sq"
and sq:"rho t q = Active sq"
and path:"active_path q p t (Suc i)"
and msgp:"msgp = HOrcvdMsgs (k_mod.gen_HOMachine k) p (HO (Suc t+i) p) (rho (t+i))"
shows "Suc (level sq) < k_mod.maxForce msgp | (Suc (level sq) = k_mod.maxForce msgp & (k_mod.minMsgs msgp) <= i)"
  using path sp msgp
proof (induction i arbitrary:p sp msgp)
  case 0
  hence "q : HO (Suc t) p" unfolding active_path_def by auto
  hence msgq:"msgp q = Content sq" using 0 sending sq by auto
  thus ?case
  proof (cases "Suc (level sq) < k_mod.maxForce msgp")
    case True
    thus ?thesis by auto
  next
    case False
    have "k_mod.maxForce msgp >= forc sq" using msgq unfolding k_mod.maxForce_def
      by (metis Max_ge finite_UNIV finite_imageI image_eqI k_mod.forceMsgs.simps(1) rangeI)
    hence "forc sq = k_mod.maxForce msgp" and eq:"Suc (level sq) = k_mod.maxForce msgp" and "forc sq = Suc (level sq)"
      using False level_force[of t q sq] assms by auto
    hence "k_mod.minMsgs msgp <= x sq" using msgq unfolding k_mod.minMsgs_def by (metis (mono_tags, lifting) Least_le)
    thus ?thesis
    proof (cases "t > 0 --> rho (t-1) q = Asleep")
      case True
      hence "x sq = 0" using sq starting unfolding k_mod.gen_initState_def by (metis locState.select_convs(1))
      thus ?thesis  using eq `k_mod.minMsgs msgp <= x sq` by auto
    next
      case False
      define msgq where "msgq = HOrcvdMsgs (k_mod.gen_HOMachine k) q (HO t q) (rho (t-1))"
      from False obtain sqq where sqq:"rho (t-1) q = Active sqq" by (cases "rho (t-1) q") auto
      hence transq:"k_mod.gen_nextState k q sqq msgq sq"
        using assms transition[of "t-1" q sqq sq] False Suc_diff_1 unfolding msgq_def by fastforce
      hence "level sqq < level sq"  using lvup False sqq by auto
      hence "x sq = 0" using transq `forc sq = Suc (level sq)` unfolding k_mod.gen_nextState_def by auto
      thus ?thesis using `k_mod.minMsgs msgp <= x sq` eq by auto
    qed
  qed
next
  case (Suc ii)
  from Suc(2) obtain seq where "seq 0 = q" and "seq (Suc (Suc ii)) = p" and
    seq:"ALL j < Suc (Suc ii). rho (t+j) (seq (Suc j)) ~= Asleep & seq j : HO (t+Suc j) (seq (Suc j))"
    unfolding active_path_def by auto
  hence "active_path q (seq (Suc ii)) t (Suc ii)" unfolding active_path_def by auto
  define msgs where "msgs = HOrcvdMsgs (k_mod.gen_HOMachine k) (seq (Suc ii)) (HO (t+Suc ii) (seq (Suc ii))) (rho (t+ii))"
  from seq obtain ss where ss:"rho (t+ii) (seq (Suc ii)) = Active ss" and "seq (Suc ii) : HO (t+Suc (Suc ii)) p"
    using `seq (Suc (Suc ii)) = p` by (cases "rho (t+ii) (seq (Suc ii))") auto
  from ss obtain sss where sss:"rho (t+Suc ii) (seq (Suc ii)) = Active sss"
    using nonAsleepAgain[of rho "t+ii" "seq (Suc ii)" _ _ _ 1] run unfolding HORun_def by fastforce
  hence transs:"k_mod.gen_nextState k (seq (Suc ii)) ss msgs sss" using ss transition unfolding msgs_def by auto
  have ih:"Suc (level sq) < k_mod.maxForce msgs | (Suc (level sq) = k_mod.maxForce msgs & k_mod.minMsgs msgs <= ii)"
    using Suc.IH ss `active_path q (seq (Suc ii)) t (Suc ii)` msgs_def by auto
  have "k_mod.maxForce msgs <= forc sss" and "x sss <= Suc (k_mod.minMsgs msgs)" using transs unfolding k_mod.gen_nextState_def by auto


  have send:"msgp (seq (Suc ii)) = Content sss" using `seq (Suc ii) : HO (t+Suc (Suc ii)) p` sss
    sending[of "t+Suc ii" "seq (Suc ii)"] unfolding Suc(4) by auto
  thus ?case
  proof (cases "Suc (level sq) < k_mod.maxForce msgp")
    case True
    thus ?thesis by auto
  next
    case False
    have "Suc (level sq) <= k_mod.maxForce msgs" using ih by auto
    moreover have "k_mod.maxForce msgp >= forc sss" using `msgp (seq (Suc ii)) = Content sss`
      unfolding k_mod.maxForce_def by (metis Max_ge finite_UNIV finite_imageI image_eqI k_mod.forceMsgs.simps(1) rangeI)
    ultimately have "Suc (level sq) = k_mod.maxForce msgp" and "forc sss = k_mod.maxForce msgp"
      using False `k_mod.maxForce msgs <= forc sss` send by auto
    moreover from this have "k_mod.minMsgs msgp <= x sss" using `msgp (seq (Suc ii)) = Content sss`
      unfolding k_mod.minMsgs_def by (metis (mono_tags, lifting) Least_le)
    ultimately show ?thesis using `x sss <= Suc (k_mod.minMsgs msgs)` `k_mod.maxForce msgs <= forc sss` ih by linarith
  qed
qed

lemma extend_path:
assumes sp:"rho (t+i) p = Active sp"
and ssp:"rho (t+Suc i) p = Active ssp"
and "level sp < level ssp"
and ss:"rho (Suc t) xi = Active ss"
and "i >= k"
shows "active_path xi p (Suc t) i"
and "forc ss <= k_mod.maxForce (HOrcvdMsgs (k_mod.gen_HOMachine k) p (HO (t+Suc i) p) (rho (t+i)))"
proof -
  define msgp where "msgp = HOrcvdMsgs (k_mod.gen_HOMachine k) p (HO (t+Suc i) p) (rho (t+i))"
  have transp:"k_mod.gen_nextState k p sp msgp ssp" using sp ssp transition unfolding msgp_def by auto
  hence lev2p:"k_mod.goto_level1 k msgp sp | k_mod.goto_level2 k msgp sp" using assms transp unfolding k_mod.gen_nextState_def by simp 
  hence "k_mod.isSynch k msgp" unfolding k_mod.goto_level1_def k_mod.goto_level2_def by auto
  from star obtain seq where "seq 0 = xi" and "seq k = p" and
    pat:"ALL j < k. seq j : HO (Suc t+i-k+Suc j) (seq (Suc j))" (is "ALL j < _. _ : ?HOseq j") unfolding k_mod.path_def by meson
  have nopass:"ALL j < k. rho (Suc t+i-k+j) (seq (Suc j)) ~= Asleep"
  proof (rule+)
    fix j
    assume "j < k" and "rho (Suc t+i-k+j) (seq (Suc j)) = Asleep"
    show "False"
    proof (cases "Suc j = k")
      case True
      thus "False" using `rho (t+i) p = Active sp` `rho (Suc t+i-k+j) (seq (Suc j)) = Asleep` `i >= k` `seq k = p` by fastforce
    next
      case False
      have "k_mod.path HO (seq (Suc j)) p (Suc t+i - k + Suc j) (k - Suc j)"
        using path_shrink[of seq xi p "Suc t+i - k" "Suc j"] `seq k = p` `seq 0 = xi` pat `j < k` by auto
      moreover from transp lev2p have "x ssp mod k = 0" unfolding k_mod.goto_level1_def k_mod.goto_level2_def k_mod.gen_nextState_def
        by (smt (verit, del_insts) Nat.lessE Suc_diff_1 `j < k` mod_Suc mod_less zero_less_Suc)
      ultimately obtain ss where ss:"rho (Suc t+i-k+Suc j) (seq (Suc j)) = Active ss & x ss mod k = Suc j"
        using assms `i >= k` `k_mod.isSynch k msgp` A1[of "seq (Suc j)" p "Suc t+i-k" "Suc j" ssp] `j < k` False 
        unfolding msgp_def by auto
      hence "ss ~= k_mod.gen_initState" using `rho (Suc t+i-k+j) (seq (Suc j)) = Asleep` starting unfolding k_mod.gen_initState_def by auto
      thus "False" using `rho (Suc t+i-k+j) (seq (Suc j)) = Asleep` starting[of "t+i-k+j"] `i >= k` ss
        by (metis add_Suc_right diff_Suc_1 starting)
    qed
  qed
  hence "rho (t+i-1) (seq (k-1)) ~= Asleep" using k2 `k <= i`
    by (smt (z3) Nat.add_diff_assoc One_nat_def Suc_1 Suc_diff_Suc Suc_lessD diff_Suc_1 group_cancel.add1 le_add1 le_add_diff_inverse2 less_eq_Suc_le plus_1_eq_Suc)
  from this obtain sm where sm:"rho (t+i) (seq (k-1)) = Active sm"
    using nonAsleepAgain[of rho "t+i-1" "seq (k-1)" _ _ _ 1] run k2 `k <= i` unfolding HORun_def by fastforce
  let ?exseq = "%l. if l <= i-k then xi else seq (l - (i-k))"
  have extrem:"?exseq 0 = xi & ?exseq i = p" using `seq k = p` `k <= i` k2 by force 
  moreover have expat:"ALL l < i. rho (Suc t+l) (?exseq (Suc l)) ~= Asleep & ?exseq l : HO (Suc (Suc t)+l) (?exseq (Suc l))"
  proof (rule allI impI)+
    fix l
    assume "l < i"
    show "rho (Suc t+l) (?exseq (Suc l)) ~= Asleep & ?exseq l : HO (Suc (Suc t)+l) (?exseq (Suc l))" 
    proof (cases "l < i-k")
      case True
      hence "rho (Suc t+l) (?exseq (Suc l)) ~= Asleep" using nonAsleepAgain[of rho "Suc t" xi] run
        unfolding HORun_def by (smt (verit) Suc_leI assms(4) proc_state.simps(3))
      thus "rho (Suc t+l) (?exseq (Suc l)) ~= Asleep & ?exseq l : HO (Suc (Suc t)+l) (?exseq (Suc l))" using loop True by auto
    next
      case False
      hence "l-(i-k) < k" using `i >= k` k2 by (metis `l < i` diff_diff_cancel diff_le_self less_diff_iff not_le_imp_less)
      hence "seq (l-(i-k)) : HO (Suc t+i-k+(Suc l-(i-k))) (seq (Suc l-(i-k)))" using pat False Suc_diff_le by auto
      hence "?exseq l : HO (Suc t+Suc l) (?exseq (Suc l))"
        using pat `seq 0 = xi` `l-(i-k) < k` False
        by (smt (z3) Nat.add_diff_assoc `i >= k`  diff_is_0_eq' group_cancel.add1 le_add_diff_inverse nat_less_le not_less_eq)

      moreover have "rho (Suc t+l) (?exseq (Suc l)) ~= Asleep" using `ALL j < k. rho (Suc t+i-k+j) (seq (Suc j)) ~= Asleep` False `l-(i-k) < k` `i >= k`
        by (smt (z3) Nat.add_diff_assoc Suc_eq_plus1 Suc_le_eq add.commute add.left_commute leI le_add_diff_inverse2)
      ultimately show "rho (Suc t+l) (?exseq (Suc l)) ~= Asleep & ?exseq l : HO (Suc (Suc t)+l) (?exseq (Suc l))" by simp
    qed
  qed
  ultimately have patt:"active_path xi p (Suc t) i" using `seq k = p`
    exI[of "%seqq. seqq 0 = xi & seqq i = p & (ALL j < i. rho (Suc t+j) (seqq (Suc j)) ~= Asleep & seqq j : HO (Suc t+Suc j) (seqq (Suc j)))" ?exseq]
    unfolding active_path_def by auto
  have "ALL j < i-1. rho (Suc t+j) (?exseq (Suc j)) ~= Asleep & ?exseq j : HO (Suc t+Suc j) (?exseq (Suc j))" using expat by auto
  hence "active_path xi (seq (k-1)) (Suc t) (i - 1)" using `seq k = p`
    exI[of "%seqq. seqq 0 = xi & seqq (i-1) = seq (k-1) &
    (ALL j < i-1. rho (Suc t+j) (seqq (Suc j)) ~= Asleep & seqq j : HO (Suc t+Suc j) (seqq (Suc j)))" ?exseq] extrem expat `k <= i` `seq 0 = xi`
    unfolding active_path_def by auto
  hence "forc sm >= forc ss" using increasing_force[of "Suc t" xi ss "seq (k-1)" "i-1" sm] sm assms k2 
    by (metis Suc_diff_1 `k <= i` add_Suc_shift dual_order.strict_trans1 less_nat_zero_code neq0_conv)
  have "seq (k-1) : HO (Suc t+i) p" using pat `seq k = p`
    by (smt (verit, del_insts) add_Suc assms(5) k2 diff_Suc_1 le_add_diff_inverse2 lessI less_add_Suc2 less_iff_Suc_add nat_less_le order_trans)
  hence "msgp (seq (k-1)) = Content sm" using sm sending unfolding msgp_def by auto
  hence "k_mod.maxForce msgp >= forc ss" using `forc sm >= forc ss`
    by (metis (mono_tags, hide_lams) Max_ge dual_order.strict_trans1 finite_UNIV
    finite_imageI image_eqI k_mod.forceMsgs.simps(1) k_mod.maxForce_def not_le rangeI)
  thus  "active_path xi p (Suc t) i"
    and "forc ss <= k_mod.maxForce (HOrcvdMsgs (k_mod.gen_HOMachine k) p (HO (t+Suc i) p) (rho (t+i)))"
    using patt unfolding msgp_def by auto
qed

lemma level_growing:
assumes s:"rho r p = Active s"
and "rho (r+i) p = Active ss"
shows "level s <= level ss" using `rho (r+i) p = Active ss`
proof (induction i arbitrary: ss)
  case 0
  thus ?case using starting[of 0 p s] assms unfolding k_mod.gen_initState_def by auto
next
  case (Suc rr)
  obtain sss where sss:"rho (r+rr) p = Active sss" using nonAsleepAgain[of rho r p _ _ _ rr] run s unfolding HORun_def by fastforce
  let ?msgp = "HOrcvdMsgs (k_mod.gen_HOMachine k) p (HO (r+Suc rr) p) (rho (r+rr))"
  have "?msgp p = Content sss" using sss loop sending[of "r+rr" p sss] by simp
  have "k_mod.forceMsgs (?msgp p) : k_mod.forceMsgs ` (range ?msgp)" by blast
  have transp:"k_mod.gen_nextState k p sss ?msgp ss" using sss transition Suc by auto
  hence "level ss >= level sss" unfolding k_mod.goto_level2_def k_mod.goto_level1_def k_mod.gen_nextState_def by auto
  thus "level s <= level ss" using Suc.IH sss by auto
qed

definition levup where
"levup f c p == EX sp ssp. rho c p = Active ssp & level ssp = f & (if f = 0 then c > 0 --> rho (c-1) p = Asleep else rho (c-1) p = Active sp & level sp = f-1)"
definition L where
"L = {(f,c) :: nat * nat | f c p. levup f c p}"
definition ref_lvup where
"ref_lvup p t = (let msgs = HOrcvdMsgs (k_mod.gen_HOMachine k) p (HO (Suc t) p) (rho t) in (k_mod.maxForce msgs-1, t-k_mod.minMsgs msgs))"

lemma in_L:
assumes "rho t p = Active sp"
shows "ref_lvup p t : L"
proof -
  define msgs where "msgs = HOrcvdMsgs (k_mod.gen_HOMachine k) p (HO (Suc t) p) (rho t)"
  hence "msgs p = Content sp" using assms loop sending by auto
  hence "k_mod.forceMsgs (msgs p) > 0" using k_mod.forceMsgs.simps(1)[of sp] assms A2_bis[of t p sp] by auto
  hence "k_mod.maxForce msgs > 0" using Max_ge unfolding k_mod.maxForce_def
    by (smt (z3) finite_UNIV finite_imageI gr_zeroI image_eqI leD rangeI)
  hence "(k_mod.maxForce msgs-1, t-k_mod.minMsgs msgs) : L"
    using A5[of t p sp "k_mod.maxForce msgs" "Suc (k_mod.minMsgs msgs)"]
    assms unfolding L_def levup_def msgs_def by fastforce
  thus ?thesis unfolding ref_lvup_def msgs_def by metis
qed

lemma finite_L: "finite L"
proof (rule ccontr)
  assume "~ finite L"
  define Lf where "Lf = (%f. {(f,c) | c. (f,c) : L})"
  have "ALL f c. (f,c) : L --> f <= 2"
  proof (rule+)
    fix f c
    assume "(f,c) : L"
    from this obtain p ssp where "rho c p = Active ssp" and "level ssp = f" unfolding L_def levup_def by auto
    thus "f <= 2" using A2_bis[of c p ssp] by auto
  qed
  moreover have "ALL f c. (f,c) : L --> (f,c) : Lf f" unfolding Lf_def by auto
  ultimately have "ALL f c. (f,c) : L --> (f,c) : Lf 0 | (f,c) : Lf 1 | (f,c) : Lf 2"
    by (metis (full_types) Suc_1 le_less less_one linorder_neqE_nat not_less_eq)
  hence "L <= (Lf 0) Un (Lf 1) Un (Lf 2)" unfolding Lf_def
    by (smt (verit, ccfv_threshold) L_def Un_iff mem_Collect_eq subsetI)
  hence "(~ finite (Lf 0)) | (~ finite (Lf 1)) | (~ finite (Lf 2))"
    using `~ finite L` finite_subset by auto
  from this obtain f where "~ finite (Lf f)" by auto
  define pLf where "pLf = (%c. SOME p. levup f c p)"
  have inj_ing:"ALL t1 t2. t1 : snd ` Lf f -->  t2 : snd ` Lf f --> pLf t1 = pLf t2 --> ~ t1 < t2"
  proof (rule+)
    fix t1 t2
    assume "t1 : snd ` Lf f" and "t2 : snd ` Lf f" and "pLf t1 = pLf t2" and "t1 < t2"
    hence "(f,t1) : L" and "(f,t2) : L" unfolding Lf_def by auto
    hence "levup f t1 (pLf t1)" and "levup f t2 (pLf t2)"
      using someI_ex[of "%p. levup f t1 p"] someI_ex[of "%p. levup f t2 p"] unfolding pLf_def L_def by auto
    from this obtain sp ssp where "rho t1 (pLf t1) = Active sp" and "level sp = f"
      "rho (t2-1) (pLf t2) = (if f = 0 then Asleep else Active ssp)" and "level ssp = f-1" using `t1 < t2` unfolding levup_def by auto
    moreover from this have "f > 0" using run nonAsleepAgain[of rho t1 "pLf t1" _ _ _ "t2-t1-1"] `t1 < t2` `pLf t1 = pLf t2` unfolding HORun_def by auto
    ultimately show "False" using level_growing[of t1 "pLf t1" sp "t2-t1-1" ssp] `t1 < t2` `pLf t1 = pLf t2` by auto
  qed
  hence "inj_on pLf (snd ` Lf f)" by (metis (mono_tags, hide_lams) inj_on_def linorder_neqE_nat)
  moreover have "inj_on snd (Lf f)" unfolding Lf_def by (simp add: inj_on_def)
  ultimately have "~ finite (pLf ` snd ` Lf f)" using `~ finite (Lf f)` finite_imageD by metis
  thus "False" by auto
qed

lemma growing_L:
assumes "rho t q = Active s"
and "q : HO (Suc (Suc t)) p"
and "rho (Suc t) p = Active sp"
shows "ref_lvup q t <= ref_lvup p (Suc t)"
proof -
  define msgs where "msgs = HOrcvdMsgs (k_mod.gen_HOMachine k) q (HO (Suc t) q) (rho t)"
  define c where "c = Suc (k_mod.minMsgs msgs)"
  define f where "f = k_mod.maxForce msgs"
  define msgss where "msgss = HOrcvdMsgs (k_mod.gen_HOMachine k) p (HO (Suc (Suc t)) p) (rho (Suc t))"
  from this obtain h sh where "msgs h = Content sh" and "forc sh = k_mod.maxForce msgs" and "rho t h = Active sh" and "c = Suc (x sh)"
    using adopt_incoming[of t q s] assms msgs_def unfolding f_def c_def by metis
  hence "f >= 1" and "c <= Suc t" using A2_bis[of t h sh] unfolding f_def by auto
  from this obtain spp where spp:"rho (Suc t-c+c) p = Active spp" using assms by auto
  obtain qq sq sqq where sqq:"rho (Suc t-c) qq = Active sqq" and "level sqq = f-1" and
    "if f = 1 then c <= t --> rho (t-c) qq = Asleep else rho (t-c) qq = Active sq & level sq = f-2" and
    "active_path qq q (Suc t-c) c"
    using A5[of t q s f c] assms f_def c_def unfolding msgs_def c_def f_def by blast
  moreover from this(4) have "active_path qq p (Suc t-c) (Suc c)"
    using path_extend[of qq q "Suc t-c" c p] assms spp by (metis `c <= Suc t` add_Suc_right le_add_diff_inverse2 proc_state.distinct(1))
  ultimately have "Suc (level sqq) < k_mod.maxForce msgss | (Suc (level sqq) = k_mod.maxForce msgss & k_mod.minMsgs msgss <= c)"
    using A6[of "Suc t-c" c p spp qq sqq msgss] run loop star k2 spp sqq `c <= Suc t` c_def `1 <= f`
    unfolding msgs_def by (smt (z3) One_nat_def Suc_1 add_Suc_right add_Suc_shift add_diff_cancel_left' diff_cancel2
    le_SucE le_add_diff_inverse2 less_le msgss_def not_less_eq plus_1_eq_Suc proc_state.inject proc_state.simps(3))
  thus ?thesis unfolding ref_lvup_def msgs_def msgss_def f_def c_def 
    by (metis Suc_pred' `1 <= f` `level sqq = f - 1` diff_Suc_Suc diff_le_mono2 f_def le_add_diff_inverse le_refl
    less_eq_prod_simp less_imp_Suc_add msgs_def msgss_def not_less_eq plus_1_eq_Suc zero_less_Suc)
qed

lemma monovalent_stable:
assumes "ALL p : V. EX sp. rho t p = Active sp & x sp mod k = c mod k"
and "ALL j. ALL p : V. HO (t+j) p <= V"
shows "ALL p : V. EX sp. rho (t+i) p = Active sp & x sp mod k = (c+i) mod k"
proof (induction i)
  case 0
  show ?case using assms by auto
next
  case (Suc ii)
  show ?case
  proof 
    fix p
    assume "p : V"
    define msgs where "msgs = HOrcvdMsgs (k_mod.gen_HOMachine k) p (HO (Suc (t+ii)) p) (rho (t+ii))"
    obtain sp ssp where sp:"rho (t+Suc ii) p = Active sp" and ssp:"rho (t+ii) p = Active ssp"
      using `p : V` assms(1) nonAsleepAgain[of rho t p _ HO _ii] nonAsleepAgain[of rho t p _ HO _ "Suc ii"] run
      unfolding HORun_def by fastforce
    from this obtain q sq where sq:"rho (t+ii) q = Active sq" and "x sq = k_mod.minMsgs msgs" and "q : HO (Suc (t+ii)) p"
      using adopt_incoming[of "t+ii" p ssp msgs] msgs_def by blast
    hence "x sq mod k = (c+ii) mod k" using sq Suc.IH `p : V` assms by (metis add_Suc_right proc_state.inject subsetD)
    moreover have "k_mod.gen_nextState k p ssp msgs sp" using sp ssp 
      transition[of "t+ii" p ssp sp] unfolding msgs_def by auto
    hence "x sp mod k = Suc (k_mod.minMsgs msgs) mod k"
      unfolding k_mod.gen_nextState_def k_mod.goto_level1_def k_mod.goto_level2_def
      by (smt (z3) One_nat_def Suc_1 Suc_diff_1 Suc_lessD k2 mod_Suc mod_less)
    ultimately show "EX sp. rho (t+Suc ii) p = Active sp & x sp mod k = (c+Suc ii) mod k"
      using `x sq = k_mod.minMsgs msgs` sp by (metis add_Suc_right mod_Suc_eq)
  qed
qed

lemma ready_level:
assumes "rho i p = Active sp"
and "ready sp"
shows "level sp > 0" using assms
proof (induction i arbitrary:p sp)
  case 0
  thus ?case using starting[of 0 p sp] unfolding k_mod.gen_initState_def by auto
next 
  case (Suc ii)
  show ?case
  proof (cases "rho ii p")
    case Asleep
    thus "level sp > 0" using starting[of "Suc ii" p sp] Suc(2) 
      unfolding k_mod.gen_initState_def by (smt (z3) Suc.prems(2) diff_Suc_1 locState.select_convs(3))
  next
    case (Active ssp)
    define msgp where "msgp = HOrcvdMsgs (k_mod.gen_HOMachine k) p (HO (Suc ii) p) (rho ii)"
    show "level sp > 0"
    proof (cases "k_mod.isReady msgp")
      case True
      hence "ready ssp" using sending[of ii p ssp] loop Active unfolding msgp_def k_mod.isReady_def by fastforce
      thus "level sp > 0" using Suc(1)[of p ssp] Active level_growing[of ii p ssp 1 sp] 
        by (smt (z3) Suc.prems(1) add.commute gr0I loop not_le plus_1_eq_Suc)
    next
      case False
      moreover have "k_mod.gen_nextState k p ssp msgp sp" using transition Suc(2) Active unfolding msgp_def by fastforce
      ultimately show "level sp > 0" using Suc(3) unfolding k_mod.gen_nextState_def by auto
    qed
  qed
qed

lemma monovalent_termine:
assumes "ALL p : V. EX sp. rho t p = Active sp & x sp mod k = 0"
and "ALL j. ALL p : V. HO (t+j) p <= V"
shows "ALL p : V. ALL sp. rho (t+3*k) p = Active sp --> level sp = 2"
proof -
  define som where "som = (%i p. SOME sp. rho (t+i) p = Active sp)"
  have som:"ALL i p. p :V --> rho (t+i) p = Active (som i p)"
  proof (rule+)
    fix i p
    assume "p : V"
    from this obtain sp where "rho t p = Active sp" using assms(1) by auto
    hence "EX ssp. rho (t+i) p = Active ssp" using nonAsleepAgain[of rho t p _ HO _ i]
      run unfolding HORun_def by fastforce
    thus "rho (t+i) p = Active (som i p)" using someI_ex[of "%sp. rho (t+i) p = Active sp"] unfolding som_def by auto
  qed
  hence mod:"ALL p : V. x (som k p) mod k = 0" using monovalent_stable[of V t 0 k] assms by simp
  let ?op = "%b. if b then conc else ready"
  have forever:"ALL b. ALL lim. ALL i >= lim. (ALL p : V. (?op b) (som lim p)) --> (ALL p : V. (?op b) (som i p))" (is "ALL b. ?P b")
  proof (rule+)
    fix b lim i p
    assume "i >= lim" and "p : V" and "ALL p : V. (?op b) (som lim p)"
    show "(?op b) (som i p)" using `i >= lim` and `p : V`
    proof (induction "i-lim" arbitrary:p i)
      case 0
      thus ?case using `ALL p : V. (?op b) (som lim p)` by auto
    next
      case (Suc ii)
      define msgp where "msgp = HOrcvdMsgs (k_mod.gen_HOMachine k) p (HO (t+i) p) (rho (t+i-1))"
      obtain q sq where "rho (t+i-1) q = Active sq" and "x sq = k_mod.minMsgs msgp" and "q : HO (t+i) p"
        using adopt_incoming[of "t+i-1" p "som (i-1) p" msgp] som Suc k2 msgp_def 
        by (smt (z3) Nat.add_diff_assoc Suc_diff_1 add_gr_0 diff_is_0_eq' le_add_diff_inverse2 nat_le_linear zero_less_Suc)
      hence "k_mod.minMsgs msgp mod k = (i-1) mod k" using monovalent_stable[of V t 0 "i-1"] assms Suc(2) som
        by (smt (verit, del_insts) Nat.add_diff_assoc Suc(3) Suc.prems(2) add.commute add.right_neutral diff_is_0_eq'
        in_mono le_add1 le_add_diff_inverse mod_add_left_eq nat_le_linear plus_1_eq_Suc proc_state.inject)
      hence "ALL p : V. x (som (i-1) p) mod k = k_mod.minMsgs msgp mod k"
        using monovalent_stable[of V t 0 "i-1"] assms som by simp
      moreover have cont:"ALL p. msgp p ~= Void --> msgp p = Content (som (i-1) p)"
      proof (rule+)
        fix qq
        assume "msgp qq ~= Void"
        hence "qq : HO (t+i) p" using assms(2) unfolding HOrcvdMsgs_def msgp_def by auto
        thus "msgp qq = Content (som (i-1) qq)" using som sending[of "t+(i-1)" qq "som (i-1) q"] assms(2) 
          unfolding msgp_def by (smt (z3) Suc(2) Suc.prems(2) add_Suc_right diff_Suc_1 in_mono less_imp_Suc_add sending zero_less_Suc zero_less_diff)
      qed
      ultimately have "b --> k_mod.isSynch k msgp" using Suc(1)[of "i-1"] Suc(2) Suc(3) unfolding k_mod.isSynch_def HOrcvdMsgs_def
        by (smt (z3) HOrcvdMsgs_def One_nat_def Suc.prems(2) assms(2) diff_Suc_1 diff_commute diff_diff_cancel diff_is_0_eq' in_mono msgp_def nat_le_linear)
      moreover have "~ b --> k_mod.isReady msgp" using Suc(1)[of "i-1"] Suc(2) Suc(3) cont unfolding k_mod.isReady_def 
        by (smt (z3) HOrcvdMsgs_def One_nat_def Suc.prems(2) assms(2) diff_Suc_1 diff_commute diff_diff_cancel diff_is_0_eq'
        in_mono message.distinct(3) message.inject msgp_def nat_le_linear)
      moreover have "k_mod.gen_nextState k p (som (i-1) p) msgp (som i p)" 
        using transition[of "t+i-1" p "som i p" "som i p"] som Suc(2) unfolding msgp_def
        by (smt (verit, ccfv_SIG) Nat.add_diff_assoc Suc.prems(2) Suc_diff_1 add.right_neutral
        add_Suc_right diff_is_0_eq less_imp_Suc_add nat_le_linear plus_1_eq_Suc transition zero_less_Suc zero_less_diff)
      moreover have "~ b --> level (som i p) > 0"
        using ready_level som `ALL p : V. (?op b) (som lim p)` Suc.prems(2) 
        level_growing[of "t+lim" p "som lim p" "i-lim" "som i p"] Suc(3) Suc.prems(2) by fastforce
      ultimately show "(?op b) (som i p)" unfolding k_mod.gen_nextState_def by auto
    qed
  qed
  moreover have "ALL p : V. rho (t+k-1) p = Active (som (k-1) p)"
    using k2 som by (metis Nat.diff_add_assoc One_nat_def dual_order.strict_trans1 less_2_cases_iff less_imp_le_nat)
  hence "ALL p : V. k_mod.gen_nextState k p (som (k-1) p) (HOrcvdMsgs (k_mod.gen_HOMachine k) p
    (HO (t+k) p) (rho (t+(k)-1))) (som k p)"
    using transition[of "t+k-1" _ "som (k-1) _" "som k _"] som k2
    by (smt (z3) Suc_pred' add_Suc_right diff_diff_cancel diff_zero less_imp_Suc_add mod_less_divisor zero_less_Suc zero_less_diff)
  hence "ALL p : V. conc (som k p)" using mod unfolding k_mod.gen_nextState_def by meson
  ultimately have conc_forever:"ALL i >= k. ALL p : V. conc (som i p)" (is "ALL i >= k. ?Q i") using allE[of ?P True] by presburger
  hence "ALL p : V. conc (som (k-1+k) p)" using allE[of ?Q "k-1+k"] k2 diff_le_mono le_add2 by presburger
  have "ALL p : V. ready (som (k+k) p)"
  proof (rule+)
    fix p
    assume "p : V"
    define msgp where "msgp = HOrcvdMsgs (k_mod.gen_HOMachine k) p (HO (t+k+k) p) (rho (t+k-1+k))"
    have msgp:"msgp = HOrcvdMsgs (k_mod.gen_HOMachine k) p (HO (Suc (t + k + k - 1)) p) (rho (t + k + k - 1))"
      using k2 unfolding msgp_def by fastforce
    moreover have "rho (t + k + k - 1) p = Active (som (k + k - 1) p)" using som `p : V`
      by (metis Nat.add_diff_assoc add.assoc k2 le_add1 less_imp_Suc_add plus_1_eq_Suc)
    ultimately obtain q sq where sq:"rho (t+k+k-1) q = Active sq" and "x sq = k_mod.minMsgs msgp" and "q : HO (Suc (t+k+k-1)) p"
      using adopt_incoming[of "t+k+k-1" p "som (k+k-1) p" msgp] by auto
    hence "q : V" using assms k2 by (smt (z3) Nat.diff_add_assoc2 Suc_1 Suc_lessD Suc_pred' `p \<in> V` add.commute
      add.left_commute add.right_neutral mod_le_divisor plus_1_eq_Suc subsetD trans_less_add2)
    hence "rho (t+(k+k-1)) q = Active sq" using som k2 sq by (smt (z3) One_nat_def Suc_1 Suc_lessD Suc_pred' add_Suc_right diff_Suc_1 group_cancel.add1)
    hence "x sq mod k = (k+k-1) mod k" using monovalent_stable[of V t 0 "k+k-1"] assms `q : V` k2 by auto
    hence "k_mod.minMsgs msgp mod k = k - 1" using sq som `q : V` `x sq = k_mod.minMsgs msgp`
      by (metis Nat.add_diff_assoc diff_less dual_order.strict_trans k2 le_add1 less_2_cases_iff less_imp_Suc_add mod_add_self1 mod_less plus_1_eq_Suc zero_less_one)
    moreover have cont:"ALL p. msgp p ~= Void --> msgp p = Content (som (k+k-1) p)"
    proof (rule+)
      fix qq
      assume "msgp qq ~= Void"
      hence "qq : HO (t+k+k) p" using assms(2) unfolding HOrcvdMsgs_def msgp_def by auto
      thus "msgp qq = Content (som (k+k-1) qq)" using som sending[of "t+(k+k-1)" qq "som (k+k-1) q"] assms(2) unfolding msgp_def
        by (smt (z3) Nat.add_diff_assoc2 Suc_diff_1 `p \<in> V` add.commute add.left_commute k2 le_add1 less_imp_Suc_add plus_1_eq_Suc sending subsetD zero_less_Suc)
    qed
    have "ALL p : V. x (som (k+k-1) p) mod k = k_mod.minMsgs msgp mod k"
      using `k_mod.minMsgs msgp mod k = k - 1` monovalent_stable[of V t 0 "k+k-1"] assms
      by (smt (verit, best) Nat.add_diff_assoc add.commute add.right_neutral add_diff_inverse_nat diff_is_0_eq'
      le_add1 less_imp_Suc_add mod_0 mod_add_left_eq mod_add_self2 nat_le_linear plus_1_eq_Suc proc_state.inject som zero_less_diff)
    hence "k_mod.isSynch k msgp" using `q : V` som `ALL p : V. conc (som (k - 1 + k) p)` cont unfolding k_mod.isSynch_def
      by (smt (z3) HOrcvdMsgs_def Suc_diff_1 msgp `p : V` ab_semigroup_add_class.add_ac(1)
      add_gr_0 assms(2) conc_forever dual_order.strict_trans k2 le_add1 le_add_diff less_2_cases_iff plus_1_eq_Suc subsetD)
    moreover have "k_mod.gen_nextState k p (som (k+k-1) p) msgp (som (k+k) p)"
      using transition[of "t+(k+k-1)" p "som (k+k-1) p" "som (k+k) p"] `p : V` k2 som
      by (smt (z3) Suc_diff_1 msgp ab_semigroup_add_class.add_ac(1) add_Suc_right diff_Suc_1 dual_order.strict_trans less_2_cases_iff)
    ultimately show "ready (som (k+k) p)" using `k_mod.minMsgs msgp mod k = k - 1` unfolding k_mod.gen_nextState_def
      by (smt (z3) Suc_1 Suc_diff_1 `k_mod.isSynch k msgp` add_gr_0 k2 k_mod.goto_level1_def less_trans mod_Suc neq0_conv plus_1_eq_Suc zero_less_one)
  qed
  hence "ALL i >= k+k. ALL p : V. ready (som i p)" (is "ALL i >= k+k. ?Q i") using allE[of ?P False] forever by (smt (z3))
  hence ready_forever:"ALL p : V. ready (som (k+k-1+k) p)" using allE[of ?Q "k+k-1+k"] k2 diff_le_mono le_add2
    by (metis Nat.add_diff_assoc Suc_1 Suc_lessD add.commute add_le_cancel_left less_imp_le_nat)
  have "ALL p : V. level (som (k+k+k) p) = 2"
  proof (rule+)
    fix p
    assume "p : V"
    define msgp where "msgp = HOrcvdMsgs (k_mod.gen_HOMachine k) p (HO (t+k+k+k) p) (rho (t+k+k-1+k))"
    have msgp:"msgp = HOrcvdMsgs (k_mod.gen_HOMachine k) p (HO (Suc (t + k + k + k - 1)) p) (rho (t + k + k + k - 1))"
      using k2 unfolding msgp_def by fastforce
    moreover have "rho (t + k + k + k - 1) p = Active (som (k + k + k - 1) p)" using som `p : V`
      by (metis Nat.add_diff_assoc add.assoc k2 le_add1 less_imp_Suc_add plus_1_eq_Suc)
    ultimately obtain q sq where sq:"rho (t+k+k+k-1) q = Active sq" and "x sq = k_mod.minMsgs msgp" and "q : HO (Suc (t+k+k+k-1)) p"
      using adopt_incoming[of "t+k+k+k-1" p "som (k+k+k-1) p" msgp] by auto
    hence "q : V" using assms k2 by (smt (z3) Nat.diff_add_assoc2 Suc_1 Suc_lessD Suc_pred' `p \<in> V` add.commute
      add.left_commute add.right_neutral mod_le_divisor plus_1_eq_Suc subsetD trans_less_add2)
    hence "rho (t+(k+k+k-1)) q = Active sq" using som k2 sq by (smt (z3) One_nat_def Suc_1 Suc_lessD Suc_pred' add_Suc_right diff_Suc_1 group_cancel.add1)
    hence "x sq mod k = (k+k+k-1) mod k" using monovalent_stable[of V t 0 "k+k+k-1"] assms `q : V` k2 by auto
    hence "k_mod.minMsgs msgp mod k = k - 1" using sq som `q : V` `x sq = k_mod.minMsgs msgp`
      by (smt (verit, ccfv_threshold) add.assoc add_diff_cancel_left' add_leD1 assms(1) diff_is_0_eq' le_add1 mod_Suc mod_add_self2
      mod_mod_trivial not_less_eq_eq ordered_cancel_comm_monoid_diff_class.add_diff_inverse plus_1_eq_Suc)
    moreover have cont:"ALL p. msgp p ~= Void --> msgp p = Content (som (k+k+k-1) p)"
    proof (rule+)
      fix qq
      assume "msgp qq ~= Void"
      hence "qq : HO (t+k+k+k) p" using assms(2) unfolding HOrcvdMsgs_def msgp_def by auto
      moreover have "Suc (t+(k+k+k-1)) = t+k+k+k" using k2 by fastforce
      moreover have "t+(k+k+k-1) = t+k+k+k-1" using k2 by fastforce
      moreover have "rho (t + (k + k + k - 1)) qq = Active (som (k + k + k - 1) qq)" using som k2
        by (metis `p \<in> V` add_Suc_right assms(2) calculation(1) calculation(2) subsetD)
      ultimately show "msgp qq = Content (som (k+k+k-1) qq)" using som sending[of "t+(k+k+k-1)" qq "som (k+k+k-1) qq"]
        assms(2) unfolding msgp_def by auto
    qed 
    have "ALL p : V. x (som (k+k+k-1) p) mod k = k_mod.minMsgs msgp mod k"
      using `k_mod.minMsgs msgp mod k = k - 1` monovalent_stable[of V t 0 "k+k+k-1"] assms
      by (smt (verit, best) Nat.add_diff_assoc add.commute add.right_neutral add_diff_inverse_nat diff_is_0_eq'
      le_add1 less_imp_Suc_add mod_0 mod_add_left_eq mod_add_self2 nat_le_linear plus_1_eq_Suc proc_state.inject som zero_less_diff)
    hence "k_mod.isSynch k msgp" using `q : V` som `ALL p : V. conc (som (k - 1 + k) p)` cont unfolding k_mod.isSynch_def
      by (smt (z3) HOrcvdMsgs_def Suc_diff_1 msgp `p : V` ab_semigroup_add_class.add_ac(1)
      add_gr_0 assms(2) conc_forever dual_order.strict_trans k2 le_add1 le_add_diff less_2_cases_iff plus_1_eq_Suc subsetD)
    moreover have "ALL h. msgp h ~= Void --> h : V" using cont assms(2) unfolding msgp_def HOrcvdMsgs_def
      by (metis `p \<in> V` ab_semigroup_add_class.add_ac(1) subsetD)
    have "k+k-1+k = k+k+k-1" by fastforce
    hence "k_mod.isReady msgp" using ready_forever cont `ALL h. msgp h ~= Void --> h : V`
      unfolding k_mod.isReady_def by (metis message.distinct(3) message.inject)
    ultimately have "level (som (k+k+k-1) p) = 1 --> k_mod.goto_level2 k msgp (som (k+k+k-1) p)" unfolding k_mod.goto_level2_def by auto
    moreover have "k_mod.gen_nextState k p (som (k+k+k-1) p) msgp (som (k+k+k) p)"
      using transition[of "t+(k+k+k-1)" p "som (k+k+k-1) p" "som (k+k+k) p"] `p : V` som k2
      by (smt (z3) Suc_diff_1 msgp ab_semigroup_add_class.add_ac(1) add_Suc_right diff_Suc_1 dual_order.strict_trans less_2_cases_iff)
    moreover have "level (som (k+k+k-1) p) > 0" using ready_forever ready_level[of "k+k+k-1" p "som (k+k+k-1) p"]
      `p : V` `k+k-1+k = k+k+k-1` som by (metis execution.ready_level execution_axioms)
    ultimately have "level (som (k+k+k) p) >= 2" using `k_mod.minMsgs msgp mod k = k - 1` unfolding k_mod.gen_nextState_def
      by (metis (no_types, lifting) One_nat_def k_mod.goto_level1_def less_2_cases_iff less_numeral_extra(3) nat_le_linear not_le_imp_less)
    thus "level (som (k+k+k) p) = 2" using A2_bis[of "t+(k+k+k)" p "som (k+k+k) p"] som `p : V` le_antisym by presburger
  qed
  thus ?thesis by (simp add: som add.commute numeral_3_eq_3)
qed
    
definition zmax where
"zmax p = Max ((ref_lvup p) ` {t. rho t p ~= Asleep})"

lemma zset_in_L: "(ref_lvup p) ` {t. rho t p ~= Asleep} <= L"
proof
  fix zz
  assume "zz : (ref_lvup p) ` {t. rho t p ~= Asleep}"
  from this obtain t where "rho t p ~= Asleep" and "zz = ref_lvup p t" by auto
  thus "zz : L" using in_L[of t p] by (cases "rho t p") auto
qed

lemma zmax_in_L: "zmax p : L"
proof -
  have "(ref_lvup p) ` {t. rho t p ~= Asleep} ~= {}" (is "?set ~= _") using complete by auto
  thus ?thesis using zset_in_L finite_L Max_in[of ?set] finite_subset unfolding zmax_def by blast
qed

lemma zset_non_empty: "(ref_lvup p) ` {t. rho t p ~= Asleep} ~= {}"
using complete by simp

lemma zmax_lim:
assumes "ref_lvup p t = zmax p"
and "rho t p ~= Asleep"
shows "ref_lvup p (t+i) = zmax p"
proof (induction i)
  case 0
  show ?case using assms by auto
next
  case (Suc ii)
  let ?set = "(ref_lvup p) ` {t. rho t p ~= Asleep}"
  obtain ssp where "rho (t+Suc ii) p = Active ssp"  using nonAsleepAgain[of rho t p] assms(2) run unfolding HORun_def by fastforce
  moreover obtain sp where "rho (t+ii) p = Active sp" using nonAsleepAgain assms(2) run unfolding HORun_def by fastforce
  ultimately have "ref_lvup p (t+Suc ii) >= zmax p" using Suc.IH loop growing_L[of "t+ii" p sp p ssp] unfolding zmax_def by auto
  moreover have "ref_lvup p (t+Suc ii) : ?set" using `rho (t+Suc ii) p = Active ssp` by auto
  ultimately show ?case using Max_ge[of ?set "ref_lvup p (t+Suc ii)"] zset_in_L finite_subset[of ?set L]
    finite_L unfolding zmax_def by (metis le_less not_le)
qed

definition stab where
"stab = (SOME t. ALL p. rho t p ~= Asleep & ref_lvup p t = zmax p)"

lemma stab_exists: "ALL p. rho stab p ~= Asleep & ref_lvup p stab = zmax p"
proof -
  let ?set = "%p. (ref_lvup p) ` {t. rho t p ~= Asleep}"
  define pmax where "pmax = (%p. SOME t. rho t p ~= Asleep & ref_lvup p t = zmax p)" (is "_ = (%p. SOME t. ?P p t)")
  have "ALL p. Max (?set p) : ?set p" using Max_in[of "?set _"] finite_L zset_in_L finite_subset zset_non_empty by metis
  hence "ALL p. EX t. ?P p t" unfolding zmax_def by fastforce
  hence Ppmax:"ALL p. ?P p (pmax p)" using someI_ex[of "?P _"] unfolding pmax_def by auto
  define pMax where "pMax = Max (range pmax)"
  have "ALL p. pMax >= pmax p" using Max_ge unfolding pMax_def by auto
  hence "ALL p. ?P p pMax" using nonAsleepAgain[of rho "pmax _" _ _ HO _ "pMax - pmax _"] zmax_lim[of _ "pmax _"]
    by (smt (verit, best) HORun_def Ppmax add.commute le_add_diff_inverse2 proc_state.simps(3) run)
  thus ?thesis using someI_ex[of "%t. ALL p. ?P p t"] unfolding stab_def by auto
qed

definition zmin where
"zmin = (LEAST zz. EX p. zmax p = zz)"
definition Vmin where
"Vmin = {p. zmax p = zmin}"

lemma Vmin_non_empty: "EX p : Vmin. True"
proof -
  have "EX p. zmax p = zmin" using LeastI_ex unfolding zmin_def by (smt (z3))
  thus ?thesis unfolding Vmin_def by auto
qed

lemma Vmin_insulated: "ALL p : Vmin. ALL i > stab. HO (Suc i) p <= Vmin"
proof 
  fix p
  assume "p : Vmin"
  show "ALL i > stab. HO (Suc i) p <= Vmin"
  proof (rule allI impI subsetI)+
    fix i x
    assume "i > stab" and "x : HO (Suc i) p"
    obtain sp where sp:"rho i p = Active sp"
      using stab_exists nonAsleepAgain[of rho stab p _ HO _ "i - stab"] `i > stab` run unfolding HORun_def by fastforce
    obtain sx where sx:"rho (i-1) x = Active sx"
      using stab_exists nonAsleepAgain[of rho stab x _ HO _ "i - 1 - stab"] `i > stab` run unfolding HORun_def by fastforce
    have "ref_lvup x (i-1) <= ref_lvup p i"
      using growing_L[of "i-1" x sx p sp] sx sp `x : HO (Suc i) p` `stab < i` by auto
    hence "zmax x = zmin" using `p : Vmin` stab_exists zmax_lim[of p stab "i - stab"] `i > stab` 
      Least_le[of "%zz. EX p. zmax p = zz" "zmax x"] 
      zmax_lim[of x stab "i - 1 - stab"] `i > stab` unfolding Vmin_def zmin_def by fastforce
    thus "x : Vmin" unfolding Vmin_def by auto
  qed
qed

lemma Vmin_monovalent: "ALL p : Vmin. EX sp. rho (Suc (Suc stab)) p = Active sp & x sp mod k = (Suc (Suc stab) - snd zmin) mod k"
proof 
  fix p
  assume "p : Vmin"
  define msgp where "msgp = HOrcvdMsgs (k_mod.gen_HOMachine k) p (HO (Suc (Suc stab)) p) (rho (Suc stab))"
  obtain sp where sp:"rho (Suc stab) p = Active sp"
    using stab_exists nonAsleepAgain[of rho stab p _ HO _ 1] run unfolding HORun_def by fastforce
  moreover from this obtain ssp where ssp:"rho (Suc (Suc stab)) p = Active ssp" using nonAsleepAgain[of rho "Suc stab" p _ HO _ 1]
    run unfolding HORun_def by fastforce
  ultimately have "k_mod.gen_nextState k p sp msgp ssp" using transition unfolding msgp_def by auto
  hence equivmod:"Suc (k_mod.minMsgs msgp) mod k = x ssp mod k" unfolding k_mod.gen_nextState_def
    by (metis Suc_diff_1 bits_mod_0 k2 k_mod.goto_level1_def k_mod.goto_level2_def less_imp_Suc_add mod_Suc zero_less_Suc)
  have "Suc stab - k_mod.minMsgs msgp = snd (ref_lvup p (Suc stab))" using `p : Vmin` unfolding ref_lvup_def msgp_def by (meson eq_snd_iff)
  hence "Suc stab - k_mod.minMsgs msgp = snd zmin" using stab_exists zmax_lim[of p stab 1] `p : Vmin` unfolding Vmin_def by auto
  moreover obtain h sh where "rho (Suc stab) h = Active sh" and "x sh = k_mod.minMsgs msgp" 
    using adopt_incoming[of "Suc stab" p sp msgp] sp msgp_def by auto
  hence "k_mod.minMsgs msgp <= Suc stab" using A2_bis[of "Suc stab" h sh] by auto
  ultimately have "Suc stab - snd zmin = k_mod.minMsgs msgp" by (metis diff_diff_cancel)
  hence "x ssp mod k = (Suc (Suc stab) - snd zmin) mod k" using equivmod
    by (metis Suc_diff_le `Suc stab - k_mod.minMsgs msgp = snd zmin` diff_le_self)
  thus "EX sp. rho (Suc (Suc stab)) p = Active sp & x sp mod k = (Suc (Suc stab) - snd zmin) mod k"
    using ssp by auto
qed

lemma Vmin_fired:"fst zmin = 2"
proof -
  define t where "t = Suc (Suc stab) + (k - (Suc (Suc stab) - snd zmin) mod k)"
  have "(Suc (Suc stab) - snd zmin + (k - (Suc (Suc stab) - snd zmin) mod k)) mod k = 0"
    by (smt (z3) add.commute dual_order.strict_trans k2 le_add_diff_inverse2 less_2_cases_iff mod_add_right_eq mod_le_divisor mod_self)
  hence "ALL p : Vmin. EX sp. rho t p = Active sp & x sp mod k = 0"
    using monovalent_stable[of Vmin "Suc (Suc stab)" "Suc (Suc stab) - snd zmin" "k - (Suc (Suc stab) - snd zmin) mod k"]
    Vmin_monovalent Vmin_insulated unfolding t_def by auto
  moreover have "t >= stab" unfolding t_def by linarith
  ultimately have "ALL p : Vmin. ALL sp. rho (t+3*k) p = Active sp --> level sp = 2"
    using monovalent_termine[of Vmin t] Vmin_insulated unfolding t_def by auto
  from this obtain p sp where "p : Vmin" and sp:"rho (t+3*k) p = Active sp" and "level sp = 2"
    using Vmin_non_empty `t >= stab` nonAsleepAgain[of rho stab _ _ HO _ "t+3*k-stab"] run stab_exists unfolding HORun_def by fastforce
  hence "forc sp >= 3" using level_force[of "t+3*k" p sp] by auto
  define msgp where "msgp = HOrcvdMsgs (k_mod.gen_HOMachine k) p (HO (Suc (t+3*k)) p) (rho (t+3*k))"
  obtain h sh ttt where "rho ttt h = Active sh" and "level sh = k_mod.maxForce msgp - 1"
    using A5[of "t+3*k" p sp] sp msgp_def by blast
  hence "k_mod.maxForce msgp <= 3" using A2_bis[of ttt h sh] by auto
  moreover have "msgp p = Content sp" using sending[of "t+3*k" p sp] sp loop unfolding msgp_def by auto
  ultimately have "k_mod.maxForce msgp = 3" using `forc sp >= 3` finite_UNIV Max_ge[of "k_mod.forceMsgs ` (range msgp)" "forc sp"]
    unfolding k_mod.maxForce_def by (metis finite_imageI image_eqI k_mod.forceMsgs.simps(1) le_antisym order_trans rangeI)
  hence "fst (ref_lvup p (t+3*k)) = 2" unfolding ref_lvup_def msgp_def by auto
  thus ?thesis using `p : Vmin` zmax_lim[of p stab] stab_exists `t >= stab` unfolding Vmin_def
    by (smt (verit, ccfv_threshold) add.commute add.left_commute less_eqE mem_Collect_eq)
qed

lemma A4:
assumes sp:"rho (t+i) p = Active sp"
and ssp:"rho (t+Suc i) p = Active ssp"
and "level sp = 1"
and "level ssp = 2"
and s:"rho t xi = Active s"
and ss:"rho (Suc t) xi = Active ss"
and "level s = 0"
and "level ss = 1"
shows "i mod k = 0"
proof (rule ccontr)
  assume "~ i mod k = 0"
  have "level sp < level ssp" using assms by auto
  let ?n = "LEAST nn. EX s. rho nn xi = Active s & level s > 0"
  define j where "j = (LEAST jj. EX q sq ssq. rho (t+jj) q = Active sq &
    rho (t+Suc jj) q = Active ssq & level sq < level ssq & jj mod k ~= 0)" (is "j = (LEAST jj. EX qj sj sjj. ?P jj qj sj sjj)")
  hence "EX i q sq ssq. rho (t+ i) q = Active sq & rho (t+Suc i) q = Active ssq & level sq < level ssq & i mod k ~= 0"
    using `~ i mod k = 0` assms(3) assms(4) sp ssp by fastforce
  from this obtain q sq ssq where sq:"rho (t+j) q = Active sq" and ssq:"rho (t+Suc j) q = Active ssq"
    and levsq:"level sq < level ssq" and "j mod k ~= 0"
    using LeastI_ex[of "%jj. EX qj sj sjj. ?P jj qj sj sjj"] unfolding j_def by blast
  define msgq where "msgq = HOrcvdMsgs (k_mod.gen_HOMachine k) q (HO (t+Suc j) q) (rho (t+j))"
  hence transq:"k_mod.gen_nextState k q sq msgq ssq" using transition[of "t+j" q sq ssq] 
      sq ssq unfolding msgq_def by auto
  define f where "f = k_mod.maxForce msgq"
  define c where "c = k_mod.minMsgs msgq"
  have "c mod k = k-1" using levsq sq ssq transq
    unfolding c_def msgq_def k_mod.gen_nextState_def k_mod.goto_level1_def k_mod.goto_level2_def by auto
  hence "j-Suc c mod k ~= 0"
    using `j mod k ~= 0` by (smt (z3) One_nat_def Suc_1 add_diff_inverse_nat diff_Suc_1 diff_zero k2 less_nat_zero_code mod_Suc mod_by_Suc_0 mod_if)

  have "i >= k" using assms A3[of t s ss i p sp ssp] by (metis Suc_1 `i mod k ~= 0` bits_mod_0 lessI neq0_conv)
  have "j >= k" using assms sq ssq levsq A3[of t s ss j q sq ssq] by (metis `j mod k ~= 0` bits_mod_0 neq0_conv)



  obtain h sh shh where shh:"rho (t+j-c) h = Active shh" and "level shh = f-1" and
    sh_pre:"if f = 1 then Suc c <= t+j --> rho (t+j-Suc c) h = Asleep else rho (t+j-Suc c) h = Active sh & level sh = f-2"
    using A5[of "t+j" q sq f "Suc c"] sq unfolding f_def c_def msgq_def by fastforce
  define msgh where "msgh = HOrcvdMsgs (k_mod.gen_HOMachine k) h (HO (t+j-c) h) (rho (t+j-Suc c))"
  have "forc ss <= f" and "active_path xi q (Suc t) j" using extend_path[of t j q sq ssq ss]
    assms sq ssq levsq `j >= k` unfolding msgq_def f_def by auto
  hence "1 < f" using level_force[of "Suc t" xi ss] sq assms by auto
  hence "t+j >= Suc c" using sh_pre
    `level shh = f-1` by (metis (mono_tags, lifting) One_nat_def Suc_1 Suc_diff_Suc diff_is_0_eq' diff_zero nat_le_linear not_less_eq_eq proc_state.inject shh)
  hence transh:"k_mod.gen_nextState k h sh msgh shh" using transition[of "t+j-Suc c" h sh shh] sh_pre
    `level shh = f-1` unfolding msgh_def by (metis Suc_diff_le `1 < f` diff_Suc_Suc less_not_refl2 shh)
  hence "k_mod.goto_level1 k msgh sh | k_mod.goto_level2 k msgh sh" using `level shh = f-1` sh_pre `1 < f` transh
    unfolding k_mod.gen_nextState_def by auto
  hence "k_mod.isSynch k msgh" and "k_mod.minMsgs msgh mod k = k - 1" and "x shh = 0 | x shh = Suc (k_mod.minMsgs msgh)" using transh
    unfolding k_mod.goto_level1_def k_mod.goto_level2_def k_mod.gen_nextState_def by auto
  hence "x shh mod k = 0" by (metis k2 bits_mod_0 diff_Suc_1 less_iff_Suc_add mod_Suc)
  show "False"
  proof (cases "f = 2")
    case True
    have "j-1 >= c" using A6[of "Suc t" "j-1" q sq xi ss msgq] assms k2 True
      sq `active_path xi q (Suc t) j` `j >= k` unfolding c_def f_def msgq_def by fastforce
    hence "?P (j-Suc c) h sh shh" using sh_pre True shh `level shh = f-1` `j-Suc c mod k ~= 0`
      by (smt (verit, ccfv_SIG) Nat.add_diff_assoc Suc_diff_1 `1 < f` `c mod k = k - 1` `j mod k \<noteq> 0`
      add_Suc_shift k2 cancel_comm_monoid_add_class.diff_cancel diff_diff_left le_add_diff_inverse2
      less_numeral_extra(4) less_trans mod_Suc mod_add_left_eq neq0_conv not_less_eq_eq plus_1_eq_Suc zero_less_one)
    hence "EX qj sj sjj. ?P (j-Suc c) qj sj sjj" by auto
    thus "False" using Least_le[of "%jj. EX qj sj sjj. ?P jj qj sj sjj" "j-Suc c"] by (simp add: j_def)
  next
    case False
    hence "t+j-Suc c >= k" using sh_pre A2[of "t+j-Suc c" h sh] 
      by (metis One_nat_def Suc_1 Suc_diff_1 Suc_diff_Suc Suc_lessD `1 < f` less_numeral_extra(4) not_le_imp_less)
    hence "EX sss. rho (t+j-c-k) xi = Active sss & (k_mod.isReady msgh --> ready sss) & x sss mod k = 0"
      using `k_mod.isSynch k msgh` A1[of xi h "t+j-c-k" 0 shh] star shh k2 unfolding msgh_def
      by (smt (z3) Nat.add_0_right Suc_1 Suc_diff_Suc Suc_le_lessD Suc_lessD `Suc c \<le> t + j` `x shh mod k = 0`
      add.commute add_diff_inverse_nat diff_Suc_1 diff_zero less_trans not_le)
    moreover have "level shh = 2" using `level shh = f-1` A2_bis[of "t+j-c" h shh] shh False `1 < f` by auto
    hence "k_mod.isReady msgh" using `k_mod.goto_level1 k msgh sh | k_mod.goto_level2 k msgh sh` transh
      unfolding k_mod.gen_nextState_def k_mod.goto_level2_def by auto
    ultimately obtain sss where sss:"rho (t+j-c-k) xi = Active sss" and "x sss mod k = 0" and "ready sss" by auto
    hence "rho (t+j-Suc c-k) xi ~= Asleep" using starting[of "t+j-c-k" xi sss] `t+j-Suc c >= k`
      unfolding k_mod.gen_initState_def by (metis Nat.add_0_right One_nat_def add_Suc_shift diff_diff_left locState.select_convs(3))
    from this obtain ssss where "rho (t+j-Suc c-k) xi = Active ssss" by (cases "rho (t+j-Suc c-k) xi") auto
    hence transx:"k_mod.gen_nextState k xi ssss (HOrcvdMsgs (k_mod.gen_HOMachine k) xi (HO (t+j-c-k) xi) (rho (t+j-Suc c-k))) sss"
      using sss assms transition[of "t+j-Suc c-k" xi ssss sss]
      by (metis Suc_diff_Suc Suc_diff_le Suc_le_lessD `Suc c <= t + j` `k <= t + j - Suc c`)
    hence "level sss > 0" using `x sss mod k = 0` `ready sss` unfolding k_mod.gen_nextState_def by auto
    hence "t+j-c-k >= t" using `level s = 0` level_growing[of "t+j-c-k" xi sss _s] s sss
      by (metis add_diff_inverse_nat nat_less_le not_le)
    hence "j-Suc c > 0" using k2 Suc_le_lessD `j mod k \<noteq> 0` `k \<le> t + j - Suc c` diff_add_inverse2 diff_le_self by linarith
    hence "?P (j-Suc c) h sh shh" using sh_pre `1 < f` shh `level shh = f-1` `j-Suc c mod k ~= 0`
      by (smt (verit, best) Nat.add_diff_assoc Suc_1 Suc_lessD `c mod k = k - 1` `j mod k \<noteq> 0` `level shh = 2`
      add_Suc_shift diff_Suc_1 diff_is_0_eq' le_add_diff_inverse2 less_iff_Suc_add less_numeral_extra(4)
      mod_Suc mod_add_left_eq nat_le_linear zero_less_diff)
    hence "EX qj sj sjj. ?P (j-Suc c) qj sj sjj" by auto
    thus "False" using Least_le[of "%jj. EX qj sj sjj. ?P jj qj sj sjj" "j-Suc c"] unfolding j_def by auto
  qed
qed


lemma safety: "k_mod.safety k rho"
proof -
  define tt where "tt = (SOME t. EX s ss. rho t xi = Active s & rho (Suc t) xi = Active ss & level s = 0 & level ss = 1)"
    (is "tt = (SOME t. EX s ss. ?P t s ss)")
  have "ALL p r sp ssp. rho r p = Active sp --> level sp < 2 --> rho (Suc r) p = Active ssp --> level ssp = 2 --> r mod k = tt mod k"
  proof (rule+)
    fix p r sp ssp
    assume sp:"rho r p = Active sp" and "level sp < 2" and ssp:"rho (Suc r) p = Active ssp" and "level ssp = 2" 
    define msgs where "msgs = HOrcvdMsgs (k_mod.gen_HOMachine k) xi (HO (Suc r-k) xi) (rho (r-k))"
    define msgp where "msgp = HOrcvdMsgs (k_mod.gen_HOMachine k) p (HO (Suc r) p) (rho r)"
    hence transp:"k_mod.gen_nextState k p sp msgp ssp" using transition sp ssp by auto
    hence lev2:"k_mod.goto_level2 k msgp sp" using `level sp < 2` `level ssp = 2`
      unfolding k_mod.goto_level2_def k_mod.gen_nextState_def by auto
    hence "x ssp mod k = 0" using ssp transp unfolding k_mod.goto_level2_def k_mod.gen_nextState_def
      by (metis One_nat_def Suc_diff_1 Suc_lessD `level sp < 2` k2 less_trans mod_Suc mod_less)
    moreover have "r >= k" using A2[of r p sp] lev2 leI sp unfolding k_mod.goto_level2_def by auto
    ultimately obtain sss where sss:"rho (Suc r-k) xi = Active sss" and "ready sss" and "x sss mod k = 0"
      using A1[of xi p "Suc r-k" 0 ssp] star lev2 ssp k2 unfolding msgp_def k_mod.goto_level2_def by auto
    hence "rho (r-k) xi ~= Asleep" using starting[of "Suc r-k" xi] `r >= k` unfolding k_mod.gen_initState_def by fastforce
    from this obtain ss where "rho (r-k) xi = Active ss" by (cases "rho (r-k) xi") auto
    hence trans:"k_mod.gen_nextState k xi ss msgs sss" using transition
      `r >= k` sss Suc_diff_le unfolding msgs_def by fastforce
    hence "level sss > 0" using `ready sss` `x sss mod k = 0` unfolding k_mod.gen_nextState_def by auto
    thus "r mod k = tt mod k"
    proof (cases "EX t s ss. rho t xi = Active s & rho (Suc t) xi = Active ss & level s = 0 & level ss = 1")
      case True
      obtain t sxt ssxt where "?P t sxt ssxt" using True by auto
      from this obtain sx ssx where "?P tt sx ssx" using someI_ex[of "%t. EX s ss. ?P t s ss"] unfolding tt_def by auto
      hence "Suc r-k >= tt" using level_growing[of "Suc r-k" xi sss "tt-(Suc r-k)" sx] `level sss > 0`
        sss `?P tt sx ssx` by (metis add_diff_inverse_nat le_less not_le)
      hence "(r-tt) mod k = 0" using A4[of tt "r-tt" p sp ssp sx ssx] sp ssp
        `?P tt sx ssx` k2 `level ssp = 2` lev2 unfolding k_mod.goto_level2_def by auto
      thus "r mod k = tt mod k" using `Suc r-k >= tt` mod_add_left_eq[of "r-tt" k tt] 
        by (metis Suc_1 Suc_diff_le `k <= r` add.commute add_cancel_right_left add_diff_inverse_nat k2
        diff_less dual_order.strict_trans dual_order.strict_trans1 less_trans_Suc not_le zero_less_Suc)
    next
      case False
      define jj where "jj = (LEAST j. EX s. rho j xi = Active s & level s > 0)" (is "_ = (LEAST j. EX s. ?Q j s)")
      have "?Q (Suc r-k) sss" using sss `level sss > 0` by auto
      from this obtain s where s:"rho jj xi = Active s" and "level s > 0" using LeastI_ex[of "%j. EX s. ?Q j s"] unfolding jj_def by auto
      hence "rho (jj-1) xi ~= Asleep" using starting[of jj xi s] unfolding k_mod.gen_initState_def by auto
      from this obtain sx where sx:"rho (jj-1) xi = Active sx" by (cases "rho (jj-1) xi") auto
      have "jj > 0" using starting[of jj xi s] `level s > 0` s unfolding k_mod.gen_initState_def by fastforce
      hence transj:"k_mod.gen_nextState k xi sx (HOrcvdMsgs (k_mod.gen_HOMachine k) xi (HO jj xi) (rho (jj-1))) s"
        using transition s sx `jj > 0` by fastforce
      have "level sx = 0" using Least_le[of "%j. EX s. ?Q j s" "jj-1"] `jj > 0` sx
        unfolding jj_def by (meson diff_less neq0_conv not_le zero_less_one)
      hence "level s = 1" using transj `0 < level s` unfolding k_mod.goto_level2_def k_mod.gen_nextState_def by auto
      thus "r mod k = tt mod k" using False `level sx = 0` s `jj > 0` sx by fastforce
    qed
  qed
  thus ?thesis unfolding k_mod.safety_def by auto
qed

lemma all_level2: "ALL p. fst (zmax p) = 2 & snd (zmax p) > 0"
proof 
  fix p
  have "fst (zmax p) >= 2" using Vmin_fired Least_le unfolding Vmin_def zmin_def by (metis (mono_tags) less_prod_def not_le)
  obtain sp where sp:"rho stab p = Active sp" using stab_exists by (cases "rho stab p") auto
  define msgp where "msgp = HOrcvdMsgs (k_mod.gen_HOMachine k) p (HO (Suc stab) p) (rho stab)"
  have "k_mod.maxForce msgp >= 3" using `fst (zmax p) >= 2` stab_exists unfolding ref_lvup_def msgp_def
    by (metis One_nat_def Suc_1 diff_Suc_1 diff_le_mono not_less_eq_eq numeral_3_eq_3 prod.sel(1))
  from this obtain h sh ssh where "rho (Suc stab - Suc (k_mod.minMsgs msgp)) h = Active sh" and "level sh = k_mod.maxForce msgp - 1"
    and "rho (stab - Suc (k_mod.minMsgs msgp)) h = Active ssh" and "level ssh = k_mod.maxForce msgp - 2"
    using A5[of stab p sp] sp msgp_def by (metis numeral_le_one_iff semiring_norm(70))
  moreover from this have "k_mod.maxForce msgp = 3" using A2_bis[of _ h sh] `k_mod.maxForce msgp >= 3`
    by (metis Suc_1 add_2_eq_Suc' eval_nat_numeral(3) le_antisym le_diff_conv one_plus_numeral_commute)
  ultimately have "stab > k_mod.minMsgs msgp"
    using Suc_1 diff_Suc_1 diff_Suc_Suc diff_is_0_eq' not_le by fastforce
  show "fst (zmax p) = 2 & snd (zmax p) > 0" using stab_exists `k_mod.maxForce msgp = 3` unfolding ref_lvup_def
    by (metis One_nat_def Suc_1 `k_mod.minMsgs msgp < stab` diff_Suc_1 fst_conv msgp_def numeral_3_eq_3 snd_conv zero_less_diff)
qed

lemma all_monovalent: "EX c. ALL p. EX s. rho (Suc stab) p = Active s & x s mod k = c mod k"
proof -
  obtain c where "ALL t p sp ssp. rho t p = Active sp --> level sp < 2 --> rho (Suc t) p = Active ssp --> level ssp = 2 --> t mod k = c"
    using safety star loop run k2 unfolding k_mod.safety_def by fastforce
  hence "ALL t p. levup 2 (Suc t) p --> t mod k = c" unfolding levup_def by (metis Suc_1 Zero_not_Suc diff_Suc_1 lessI)
  have "ALL p. EX s. rho (Suc stab) p = Active s & x s mod k = (stab + (k - c mod k)) mod k"
  proof
    fix p
    obtain sp where sp:"rho stab p = Active sp" using stab_exists by (cases "rho stab p") auto
    from this obtain ssp where ssp:"rho (Suc stab) p = Active ssp"
      using nonAsleepAgain[of rho stab p _ HO _ 1] run k2 unfolding HORun_def by fastforce
    define msgp where "msgp = HOrcvdMsgs (k_mod.gen_HOMachine k) p (HO (Suc stab) p) (rho stab)"
    hence zmax:"stab - k_mod.minMsgs msgp = snd (zmax p)" using stab_exists snd_conv unfolding ref_lvup_def by metis
    moreover have "k_mod.maxForce msgp = 3" using all_level2 stab_exists unfolding ref_lvup_def msgp_def
      by (smt (z3) One_nat_def Suc_1 diff_le_self fst_conv le_add1 le_add_diff_inverse le_trans numeral_3_eq_3 plus_1_eq_Suc)
    moreover have "EX q. levup (fst (ref_lvup p stab)) (snd (ref_lvup p stab)) q"
      using in_L[of stab p sp] sp unfolding L_def by fastforce
    ultimately have "EX q. levup 2 (stab - k_mod.minMsgs msgp) q" using stab_exists unfolding ref_lvup_def msgp_def by auto
    hence "(stab - k_mod.minMsgs msgp - 1) mod k = c"
      using zmax all_level2 `ALL t p. levup 2 (Suc t) p --> t mod k = c` by auto
    hence "(stab - k_mod.minMsgs msgp) mod k = (Suc c) mod k"
      using zmax all_level2
      by (metis Suc_diff_1 mod_Suc_eq)
    moreover have "k_mod.gen_nextState k p sp msgp ssp" using sp ssp transition unfolding msgp_def by auto
    hence e2:"x ssp mod k = Suc (k_mod.minMsgs msgp) mod k" unfolding k_mod.gen_nextState_def
      by (metis One_nat_def Suc_diff_1 `k_mod.maxForce msgp = 3` k2 k_mod.goto_level2_def lessI less_iff_Suc_add mod_Suc mod_less numeral_3_eq_3 zero_less_Suc)
    ultimately have "(stab - k_mod.minMsgs msgp + Suc (k_mod.minMsgs msgp)) mod k = (Suc c + x ssp) mod k"
      using mod_add_eq by metis
    hence "stab mod k = (c + x ssp) mod k"
      by (metis Suc_eq_plus1 `(stab - k_mod.minMsgs msgp - 1) mod k = c` zmax e2 add.commute all_level2 diff_diff_left diff_is_0_eq'
      le_add_diff_inverse mod_add_right_eq not_less_eq not_less_eq_eq zero_less_Suc)
    hence "(c + x ssp + (k - c mod k)) mod k = (stab + (k - c mod k)) mod k"
      using mod_add_right_eq[of "x ssp" "k-c mod k" k] mod_add_eq by metis
    hence "x ssp mod k = (stab + (k - c mod k)) mod k"
      by (smt (z3) `(stab - k_mod.minMsgs msgp - 1) mod k = c` add.commute add.left_commute dual_order.strict_trans
      k2 le_add_diff_inverse2 less_2_cases_iff mod_add_self2 mod_le_divisor mod_less mod_less_divisor)
    thus "EX s. rho (Suc stab) p = Active s & x s mod k = (stab + (k - c mod k)) mod k" using ssp by auto
  qed
  thus  "EX c. ALL p. EX s. rho (Suc stab) p = Active s & x s mod k = c mod k" by auto
qed

lemma liveness: "k_mod.liveness rho"
proof -
  obtain c where c:"ALL p. EX s. rho (Suc stab) p = Active s & x s mod k = c mod k"
    using all_monovalent by auto
  define t where "t = Suc stab + (k - c mod k)"
  have "ALL p. EX s. rho t p = Active s & x s mod k = (c + (k - c mod k)) mod k"
    using monovalent_stable[of UNIV "Suc stab" c "k-c mod k"] c unfolding t_def by auto
  hence "ALL p. EX s. rho t p = Active s & x s mod k = 0"
    by (metis add_diff_inverse_nat k2 less_imp_Suc_add mod_add_left_eq mod_le_divisor mod_self not_le zero_less_Suc)
  hence "ALL p. ALL sp. rho (t+3*k) p = Active sp --> level sp = 2"
    using monovalent_termine[of UNIV t] by auto
  moreover have "ALL p. EX s. rho (t+3*k) p = Active s"
  proof
    fix p
    show "EX s. rho (t+3*k) p = Active s"
      using stab_exists nonAsleepAgain[of rho stab p _ HO _ "t+3*k-stab"] run unfolding t_def HORun_def
      by (smt (z3) add_Suc_shift le_add1 le_add_diff_inverse le_trans t_def)
  qed
  ultimately show "k_mod.liveness rho"
    unfolding k_mod.liveness_def by meson
qed


end
