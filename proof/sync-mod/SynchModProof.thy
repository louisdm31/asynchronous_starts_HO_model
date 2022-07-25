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
  and complete:"EX t. ALL p. rho t p ~= Asleep"
begin

lemma nonAsleepAgain2:
assumes "rho t p ~= Asleep"
shows "EX s. rho (t+i) p = Active s"
using nonAsleepAgain[of rho t p _ _ _ i] run assms unfolding HORun_def by auto

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
and "level ssp > 0"
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
    thus "False" using assms A2 by (metis neq0_conv not_le_imp_less)
  qed
  hence lev1p:"k_mod.goto_level1 k ?msgp sp" using assms transp
    unfolding k_mod.gen_nextState_def k_mod.goto_level1_def by (metis k_mod.goto_level2_def less_numeral_extra(3)) 
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
  show "active_path p q t 0 --> rho (t+0) q = Active sq --> forc sp <= forc sq"
    using sp unfolding active_path_def by fastforce
next
  case (Suc rr)
  show "active_path p q t (Suc rr) --> rho (t+Suc rr) q = Active sq --> forc sp <= forc sq"
  proof (rule impI)+
    assume "active_path p q t (Suc rr)" and sq:"rho (t+Suc rr) q = Active sq"
    then obtain seq where seq0:"seq 0 = p" and "seq (Suc rr) = q"
      and seqSuc:"ALL j < Suc rr. rho (t+j) (seq (Suc j)) ~= Asleep & seq j : HO (t+Suc j) (seq (Suc j))"
      unfolding active_path_def by auto
    have "rho (t+rr) (seq rr) ~= Asleep"
    proof (cases "rr")
      case 0
      thus "rho (t+rr) (seq rr) ~= Asleep" using seq0 sp by auto
    next
      case (Suc rrr)
      hence "rho (t+rr-1) (seq rr) ~= Asleep" using `seq (Suc rr) = q` seqSuc by auto
      thus "rho (t+rr) (seq rr) ~= Asleep" using run nonAsleepAgain2
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
    using nonAsleepAgain2[of "t+ii" "seq (Suc ii)" 1] run by auto
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
    using nonAsleepAgain2[of "t+i-1" "seq (k-1)" 1] run k2 `k <= i` by auto
  let ?exseq = "%l. if l <= i-k then xi else seq (l - (i-k))"
  have extrem:"?exseq 0 = xi & ?exseq i = p" using `seq k = p` `k <= i` k2 by force 
  moreover have expat:"ALL l < i. rho (Suc t+l) (?exseq (Suc l)) ~= Asleep & ?exseq l : HO (Suc (Suc t)+l) (?exseq (Suc l))"
  proof (rule allI impI)+
    fix l
    assume "l < i"
    show "rho (Suc t+l) (?exseq (Suc l)) ~= Asleep & ?exseq l : HO (Suc (Suc t)+l) (?exseq (Suc l))" 
    proof (cases "l < i-k")
      case True
      hence "rho (Suc t+l) (?exseq (Suc l)) ~= Asleep" using nonAsleepAgain2[of "Suc t" xi] run
        by (smt (verit) Suc_leI assms(4) proc_state.simps(3))
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
  obtain sss where sss:"rho (r+rr) p = Active sss" using nonAsleepAgain2[of r p rr] run s by auto
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
definition L_minus_xi where
"L_minus_xi = {(f,c) :: nat * nat | f c p. p ~= xi & levup f c p}"
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
    moreover from this have "f > 0" using run nonAsleepAgain2[of t1 "pLf t1" "t2-t1-1"] `t1 < t2` `pLf t1 = pLf t2` by auto
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

lemma growing_path:
assumes "active_path p q (Suc t) i"
and "rho t p ~= Asleep"
shows "ref_lvup p t <= ref_lvup q (t+i)" using assms
proof (induction i arbitrary:q)
  case 0
  thus ?case unfolding active_path_def by auto
next
  case (Suc ii)
  from Suc.prems obtain seq where "seq 0 = p" and "seq (Suc ii) = q" and
    "ALL i < Suc ii. rho (Suc t + i) (seq (Suc i)) ~= Asleep & seq i : HO (Suc t + Suc i) (seq (Suc i))"
    unfolding active_path_def by auto
  hence pat:"active_path p (seq ii) (Suc t) ii" and link:"seq ii : HO (Suc t+Suc ii) q" and
    awak:"rho (Suc t+(ii - 1)) (seq (Suc (ii - 1))) ~= Asleep" and
    awaq:"rho (Suc t+ii) q ~= Asleep"
    unfolding active_path_def by auto
  hence "ref_lvup p t <= ref_lvup (seq ii) (t+ii)" using Suc by auto
  moreover have "ref_lvup (seq ii) (t+ii) <= ref_lvup q (t+Suc ii)"
    using awaq awak link assms(2) growing_L[of "t+ii" "seq ii" _ q] 
    by (metis (no_types, hide_lams) Suc_pred' `seq 0 = p` add.commute add_Suc_right add_cancel_right_left neq0_conv the_state.cases) 
  ultimately show "ref_lvup p t <= ref_lvup q (t+Suc ii)" by auto
qed

lemma monovalent_stable:
assumes "ALL p sp. rho t p = Active sp --> x sp mod k = c mod k"
and "ALL p. rho t p ~= Asleep"
shows "ALL p sp. rho (t+i) p = Active sp --> x sp mod k = (c+i) mod k"
proof (induction i)
  case 0
  show ?case using assms by auto
next
  case (Suc ii)
  show ?case
  proof 
    fix p
    define msgs where "msgs = HOrcvdMsgs (k_mod.gen_HOMachine k) p (HO (Suc (t+ii)) p) (rho (t+ii))"
    obtain sp ssp where sp:"rho (t+Suc ii) p = Active sp" and ssp:"rho (t+ii) p = Active ssp"
      using assms(2) nonAsleepAgain2[of t p ii] nonAsleepAgain2[of t p "Suc ii"] by metis
    from this obtain q sq where sq:"rho (t+ii) q = Active sq" and "x sq = k_mod.minMsgs msgs" and "q : HO (Suc (t+ii)) p"
      using adopt_incoming[of "t+ii" p ssp msgs] msgs_def by blast
    hence "x sq mod k = (c+ii) mod k" using sq Suc.IH assms by metis
    moreover have "k_mod.gen_nextState k p ssp msgs sp" using sp ssp 
      transition[of "t+ii" p ssp sp] unfolding msgs_def by auto
    hence "x sp mod k = Suc (k_mod.minMsgs msgs) mod k"
      unfolding k_mod.gen_nextState_def k_mod.goto_level1_def k_mod.goto_level2_def
      by (smt (z3) One_nat_def Suc_1 Suc_diff_1 Suc_lessD k2 mod_Suc mod_less)
    ultimately show "ALL sp. rho (t+Suc ii) p = Active sp --> x sp mod k = (c+Suc ii) mod k"
      using `x sq = k_mod.minMsgs msgs` sp by (metis add_Suc_right mod_Suc_eq proc_state.inject)
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
assumes "ALL p sp. rho t p = Active sp --> x sp mod k = 0"
and "ALL p. rho (t-1) p ~= Asleep"
and "t > 0"
shows "ALL p. ALL sp. rho (t+2*k) p = Active sp --> level sp = 2"
proof -
  have act:"ALL p. rho t p ~= Asleep" using assms nonAsleepAgain2[of "t-1" _ 1]
    by (metis add.right_neutral dual_order.strict_trans1 le_add_diff_inverse2 less_nat_zero_code not_less_eq_eq plus_1_eq_Suc proc_state.simps(3))
  define som where "som = (%i p. SOME sp. rho (t+i) p = Active sp)"
  have som:"ALL i p. rho (t+i) p = Active (som i p)"
  proof (rule+)
    fix i p
    obtain sp where "rho t p = Active sp" using act by (cases "rho t p") auto
    hence "EX ssp. rho (t+i) p = Active ssp" using nonAsleepAgain2 run by auto
    thus "rho (t+i) p = Active (som i p)" using someI_ex[of "%sp. rho (t+i) p = Active sp"] unfolding som_def by auto
  qed

  hence mod:"ALL p. x (som 0 p) mod k = 0" using assms som by (metis add.right_neutral)
  let ?op = "%b. if b then conc else ready"
  have forever:"ALL b lim p. ALL i >= lim. (ALL p. ?op b (som lim p)) --> ?op b (som i p)" (is "ALL b. ?P b")
  proof (rule+)
    fix b lim i p
    assume "i >= lim" and "ALL p. (?op b) (som lim p)"
    show "(?op b) (som i p)" using `i >= lim`
    proof (induction "i-lim" arbitrary:p i)
      case 0
      thus ?case using `ALL p. (?op b) (som lim p)` by auto
    next
      case (Suc ii)
      define msgp where "msgp = HOrcvdMsgs (k_mod.gen_HOMachine k) p (HO (t+i) p) (rho (t+i-1))"
      obtain q sq where "rho (t+i-1) q = Active sq" and "x sq = k_mod.minMsgs msgp" and "q : HO (t+i) p"
        using adopt_incoming[of "t+i-1" p "som (i-1) p" msgp] som Suc k2 msgp_def
        by (smt (verit, ccfv_threshold) Nat.add_diff_assoc le_add1 le_add2 le_trans ordered_cancel_comm_monoid_diff_class.add_diff_inverse plus_1_eq_Suc)
      hence "x sq mod k = (i-1) mod k"
        using monovalent_stable[of t 0 "i-1"] assms(1) 
        by (metis (no_types, lifting) Nat.add_diff_assoc One_nat_def Suc.hyps(2) Suc.prems Suc_leI add.left_neutral add_gr_0 act
        bits_mod_0 le_add_diff_inverse2 plus_1_eq_Suc zero_less_one)
      hence "ALL p. x (som (i-1) p) mod k = k_mod.minMsgs msgp mod k"
        using monovalent_stable[of "t" 0 "i-1"] assms act som `x sq = k_mod.minMsgs msgp` by auto
      moreover have cont:"ALL p. msgp p ~= Void --> msgp p = Content (som (i-1) p)"
      proof (rule+)
        fix qq
        assume "msgp qq ~= Void"
        hence "qq : HO (t+i) p" using assms(2) unfolding HOrcvdMsgs_def msgp_def by auto
        thus "msgp qq = Content (som (i-1) qq)" using som sending[of "t+(i-1)" qq "som (i-1) q"] assms(2) 
          unfolding msgp_def by (smt (z3) Suc(2) Suc_diff_1 add_Suc_right diff_Suc_1 diff_le_self dual_order.strict_trans1 sending zero_less_Suc)
      qed
      ultimately have "b --> k_mod.isSynch k msgp" using Suc(1)[of "i-1"] Suc(2) Suc(3)
        unfolding k_mod.isSynch_def HOrcvdMsgs_def by auto
      moreover have "~ b --> k_mod.isReady msgp" using Suc(1)[of "i-1"] Suc(2) Suc(3) cont unfolding k_mod.isReady_def 
        by (metis (mono_tags, lifting) Suc_diff_1 Zero_not_Suc diff_Suc_1 diff_commute diff_is_0_eq'
        dual_order.strict_trans1 message.distinct(3) message.inject not_less_eq_eq zero_less_Suc)
      moreover have "k_mod.gen_nextState k p (som (i-1) p) msgp (som i p)" 
        using transition[of "t+i-1" p "som i p" "som i p"] som Suc(2) unfolding msgp_def
        by (smt (z3) Nat.add_diff_assoc One_nat_def Suc_diff_1 Suc_leI add_gr_0 diff_le_self
        dual_order.strict_trans1 execution.transition execution_axioms zero_less_Suc)
      moreover have "~ b --> level (som i p) > 0"
        using ready_level som `ALL p. (?op b) (som lim p)`
        level_growing[of "t+lim" p "som lim p" "i-lim" "som i p"] Suc(3)
        by (metis (mono_tags, lifting) add.assoc dual_order.strict_trans1 le_add_diff_inverse)
      ultimately show "(?op b) (som i p)" unfolding k_mod.gen_nextState_def by auto
    qed
  qed
  moreover define som_minus_1 where "som_minus_1 = (%p. (SOME sp. rho (t-1) p = Active sp))"
  have "ALL p. rho (t-1) p = Active (som_minus_1 p)"
  proof 
    fix p
    have "EX sp. rho (t-1) p = Active sp" (is "EX sp. ?P sp") using assms(2) by (cases "rho (t-1) p") auto
    thus "rho (t-1) p = Active (som_minus_1 p)" using someI_ex[of ?P] unfolding som_minus_1_def by auto
  qed
  hence "ALL p. k_mod.gen_nextState k p (som_minus_1 p) (HOrcvdMsgs (k_mod.gen_HOMachine k) p
    (HO t p) (rho (t-1))) (som 0 p)"
    using transition[of "t-1" _ "som_minus_1 _" "som 0 _"] som assms(3)
    by (metis Suc_pred' add.right_neutral)
  hence "ALL p. conc (som 0 p)" using mod monovalent_stable[of t 0 0] assms bits_mod_0 mod_add_self2 som act unfolding k_mod.gen_nextState_def by auto
  ultimately have conc_forever:"ALL i >= 0. ALL p. conc (som i p)" (is "ALL i >= 0. ?Q i") using allE[of ?P True] by presburger
  hence "ALL p. conc (som (k-1) p)" using le0 by presburger
  have "ALL p. ready (som k p)"
  proof (rule+)
    fix p
    define msgp where "msgp = HOrcvdMsgs (k_mod.gen_HOMachine k) p (HO (t+k) p) (rho (t-1+k))"
    have msgp:"msgp = HOrcvdMsgs (k_mod.gen_HOMachine k) p (HO (Suc (t + k - 1)) p) (rho (t + k - 1))"
      using k2 assms(3) unfolding msgp_def by fastforce
    moreover have "rho (t + k - 1) p = Active (som (k - 1) p)" using som
      by (metis Nat.add_diff_assoc k2 le_add1 less_imp_Suc_add plus_1_eq_Suc)
    ultimately obtain q sq where sq:"rho (t+k-1) q = Active sq" and "x sq = k_mod.minMsgs msgp" and "q : HO (Suc (t+k-1)) p"
      using adopt_incoming[of "t+k-1" p "som (k-1) p" msgp] by auto
    hence "rho (t+(k-1)) q = Active sq" using som k2 sq by (smt (z3) One_nat_def Suc_1 Suc_lessD Suc_pred' add_Suc_right diff_Suc_1 group_cancel.add1)
    moreover have k_k_1:"ALL q. EX sq. rho (t+(k-1)) q = Active sq & x sq mod k = (k-1) mod k"
      using monovalent_stable[of t 0 "k-1"] assms act k2 by (metis add.left_neutral bits_mod_0 som)
    ultimately have "x sq mod k = (k-1) mod k" by (metis proc_state.inject)
    hence "k_mod.minMsgs msgp mod k = k - 1" using sq som `x sq = k_mod.minMsgs msgp`
      by (metis diff_less dual_order.strict_trans k2 less_2_cases_iff mod_less zero_less_one)
    moreover have cont:"ALL p. msgp p ~= Void --> msgp p = Content (som (k-1) p)"
    proof (rule+)
      fix qq
      assume "msgp qq ~= Void"
      hence "qq : HO (t+k) p" using assms(2) unfolding HOrcvdMsgs_def msgp_def by auto
      thus "msgp qq = Content (som (k-1) qq)" using som sending[of "t+(k-1)" qq "som (k-1) qq"] assms(2) unfolding msgp_def
        by (smt (z3) Suc_diff_1 add_Suc_right diff_Suc_1 dual_order.strict_trans k2 less_2_cases_iff msgp msgp_def)
    qed
    have "ALL p. x (som (k-1) p) mod k = k_mod.minMsgs msgp mod k"
      using `k_mod.minMsgs msgp mod k = k - 1` k_k_1 som
      by (metis `x sq = k_mod.minMsgs msgp` `x sq mod k = (k - 1) mod k` proc_state.inject)
    hence "k_mod.isSynch k msgp" using som `ALL p. conc (som (k - 1) p)` cont unfolding k_mod.isSynch_def
      by (smt (z3) HOrcvdMsgs_def Suc_diff_1 msgp ab_semigroup_add_class.add_ac(1)
      add_gr_0 assms(2) conc_forever dual_order.strict_trans k2 le_add1 le_add_diff less_2_cases_iff plus_1_eq_Suc subsetD)
    moreover have "k_mod.gen_nextState k p (som (k-1) p) msgp (som k p)"
      using transition[of "t+(k-1)" p "som (k-1) p" "som (k) p"] k2 som
      by (smt (z3) Suc_diff_1 msgp ab_semigroup_add_class.add_ac(1) add_Suc_right diff_Suc_1 dual_order.strict_trans less_2_cases_iff)
    ultimately show "ready (som (k) p)" using `k_mod.minMsgs msgp mod k = k - 1` unfolding k_mod.gen_nextState_def
      by (smt (z3) Suc_1 Suc_diff_1 `k_mod.isSynch k msgp` add_gr_0 k2 k_mod.goto_level1_def less_trans mod_Suc neq0_conv plus_1_eq_Suc zero_less_one)
  qed
  hence "ALL i >= k. ALL p. ready (som i p)" (is "ALL i >= k. ?Q i") using allE[of ?P False] forever by (smt (z3))
  hence ready_forever:"ALL p. ready (som (k-1+k) p)" using allE[of ?Q "k-1+k"] k2 diff_le_mono le_add2 by auto
  have "ALL p. level (som (k+k) p) = 2"
  proof (rule+)
    fix p
    define msgp where "msgp = HOrcvdMsgs (k_mod.gen_HOMachine k) p (HO (t+k+k) p) (rho (t+k-1+k))"
    have msgp:"msgp = HOrcvdMsgs (k_mod.gen_HOMachine k) p (HO (Suc (t + k + k - 1)) p) (rho (t + k + k - 1))"
      using k2 unfolding msgp_def by fastforce
    moreover have "rho (t + k + k - 1) p = Active (som (k + k - 1) p)" using som
      by (metis Nat.add_diff_assoc add.assoc k2 le_add1 less_imp_Suc_add plus_1_eq_Suc)
    ultimately obtain q sq where sq:"rho (t+k+k-1) q = Active sq" and "x sq = k_mod.minMsgs msgp" and "q : HO (Suc (t+k+k-1)) p"
      using adopt_incoming[of "t+k+k-1" p "som (k+k-1) p" msgp] by auto
    hence "rho (t+(k+k-1)) q = Active sq" using som k2 sq by (smt (z3) One_nat_def Suc_1 Suc_lessD Suc_pred' add_Suc_right diff_Suc_1 group_cancel.add1)
    moreover have k_k_k_1:"ALL q. EX sq. rho (t+(k+k-1)) q = Active sq & x sq mod k = (k+k-1) mod k"
      using monovalent_stable[of t 0 "k+k-1"] assms(1) by (metis add.left_neutral act bits_mod_0 som)
    ultimately have "x sq mod k = (k+k-1) mod k" by (metis proc_state.inject)
    hence "k_mod.minMsgs msgp mod k = k - 1" using sq som `x sq = k_mod.minMsgs msgp`
      by (smt (z3) One_nat_def Suc_diff_1 add_gr_0 diff_Suc_1 diff_is_0_eq' dual_order.strict_trans k2 less_2_cases_iff mod_Suc mod_add_self2 mod_self zero_le_one zero_neq_one)
    moreover have cont:"ALL p. msgp p ~= Void --> msgp p = Content (som (k+k-1) p)"
    proof (rule+)
      fix qq
      assume "msgp qq ~= Void"
      hence "qq : HO (t+k+k) p" using assms(2) unfolding HOrcvdMsgs_def msgp_def by auto
      moreover have "Suc (t+(k+k-1)) = t+k+k" using k2 by fastforce
      moreover have "t+(k+k-1) = t+k+k-1" using k2 by fastforce
      moreover have "rho (t + (k + k - 1)) qq = Active (som (k + k - 1) qq)" using som k2
        by metis
      ultimately show "msgp qq = Content (som (k+k-1) qq)" using som sending[of "t+(k+k-1)" qq "som (k+k-1) qq"]
        assms(2) unfolding msgp_def by auto
    qed 
    have "ALL p. x (som (k+k-1) p) mod k = k_mod.minMsgs msgp mod k"
      using `k_mod.minMsgs msgp mod k = k - 1` k_k_k_1
      by (metis `x sq = k_mod.minMsgs msgp` `x sq mod k = (k + k - 1) mod k` proc_state.inject som)
    hence "k_mod.isSynch k msgp" using som cont unfolding k_mod.isSynch_def by (meson conc_forever zero_le)
    moreover have "k-1+k = k+k-1" by fastforce
    hence "k_mod.isReady msgp" using ready_forever cont
      unfolding k_mod.isReady_def by (metis message.distinct(3) message.inject)
    ultimately have "level (som (k+k-1) p) = 1 --> k_mod.goto_level2 k msgp (som (k+k-1) p)" unfolding k_mod.goto_level2_def by auto
    moreover have "k_mod.gen_nextState k p (som (k+k-1) p) msgp (som (k+k) p)"
      using transition[of "t+(k+k-1)" p "som (k+k-1) p" "som (k+k) p"] som k2
      by (smt (z3) Suc_diff_1 msgp ab_semigroup_add_class.add_ac(1) add_Suc_right diff_Suc_1 dual_order.strict_trans less_2_cases_iff)
    moreover have "level (som (k+k-1) p) > 0" using ready_forever ready_level[of "k+k-1" p "som (k+k-1) p"]
      `k-1+k = k+k-1` som by (metis execution.ready_level execution_axioms)
    ultimately have "level (som (k+k) p) >= 2" using `k_mod.minMsgs msgp mod k = k - 1` unfolding k_mod.gen_nextState_def
      by (metis (no_types, lifting) One_nat_def k_mod.goto_level1_def less_2_cases_iff less_numeral_extra(3) nat_le_linear not_le_imp_less)
    thus "level (som (k+k) p) = 2" using A2_bis[of "t+(k+k)" p "som (k+k) p"] som le_antisym by presburger
  qed
  thus ?thesis by (simp add: som add.commute numeral_2_eq_2)
qed
    
lemma zset_in_L: "(ref_lvup p) ` {t. rho t p ~= Asleep} <= L"
proof
  fix zz
  assume "zz : (ref_lvup p) ` {t. rho t p ~= Asleep}"
  from this obtain t where "rho t p ~= Asleep" and "zz = ref_lvup p t" by auto
  thus "zz : L" using in_L[of t p] by (cases "rho t p") auto
qed

lemma zset_non_empty: "(ref_lvup p) ` {t. rho t p ~= Asleep} ~= {}"
using complete by auto

lemma A4:
assumes sp:"rho (t+i) p = Active sp"
and ssp:"rho (t+Suc i) p = Active ssp"
and "level sp < level ssp"
and s:"rho t xi = Active s"
and ss:"rho (Suc t) xi = Active ss"
and "level s = 0"
and "level ss > 0"
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

  have "i >= k" using assms A3[of t s ss i p sp ssp] by (metis `i mod k ~= 0` bits_mod_0 neq0_conv)
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

lemma mod_sub: assumes "a >= c"
shows  "(a - c) mod k = (a - c mod k) mod k" using assms
proof -
  obtain q where decomp:"c = q * k + (c mod k)" using div_mod_decomp by blast
  hence "(a - c) mod k = (a - q * k - (c mod k)) mod k" using assms by auto
  thus ?thesis by (metis decomp add_le_imp_le_diff assms diff_commute le_add_diff_inverse mod_mult_self4 mult.commute)
qed

lemma ref_inf_t: assumes "rho t p = Active sp"
shows "t >= snd (ref_lvup p t)"
proof -
  define msg where "msg = HOrcvdMsgs (k_mod.gen_HOMachine k) p (HO (Suc t) p) (rho t)"
  obtain q sq where "msg q = Content sq" and "rho t q = Active sq" and "k_mod.maxForce msg = forc sq"
    using adopt_incoming[of t p sp msg] assms unfolding k_mod.minMsgs_def msg_def by auto
  hence "t >= k_mod.minMsgs msg"
    using Least_le[of "%v. EX m p. msg p = Content m & forc m = k_mod.maxForce msg & x m = v" "x sq"] 
    A2_bis[of t q sq] assms `rho t q = Active sq` unfolding k_mod.minMsgs_def by fastforce
  thus ?thesis unfolding ref_lvup_def by (metis diff_le_self snd_conv)
qed

lemma minMsgs_inf:
assumes "rho t p ~= Asleep"
shows "k_mod.minMsgs (HOrcvdMsgs (k_mod.gen_HOMachine k) p (HO (t+1) p) (rho t)) <= t"
proof -
  define msg where "msg = HOrcvdMsgs (k_mod.gen_HOMachine k) p (HO (t+1) p) (rho t)"
  obtain sp where sp:"rho t p = Active sp" using assms by (cases "rho t p") auto
  obtain q sq where "rho t q = Active sq" and "x sq = k_mod.minMsgs msg"
    using adopt_incoming[of t p sp] sp unfolding msg_def by auto
  thus ?thesis using A2_bis[of t q sq] unfolding msg_def by auto
qed

lemma ref_cong_x: assumes "rho t p ~= Asleep"
and "rho (Suc t) p = Active sp"
shows "x sp mod k = Suc (t - snd (ref_lvup p t)) mod k"
proof -
  obtain ssp where ssp:"rho t p = Active ssp" using assms(1) by (cases "rho t p") auto
  define msg where "msg = HOrcvdMsgs (k_mod.gen_HOMachine k) p (HO (Suc t) p) (rho t)"
  have "k_mod.gen_nextState k p ssp msg sp" using transition run ssp assms(2) unfolding msg_def by auto
  hence "x sp mod k = Suc (k_mod.minMsgs msg) mod k" unfolding k_mod.gen_nextState_def k_mod.goto_level1_def k_mod.goto_level2_def
    by (smt (z3) One_nat_def Suc_1 Suc_diff_1 Suc_lessD k2 mod_Suc mod_less)
  thus ?thesis using snd_conv minMsgs_inf unfolding k_mod.gen_nextState_def ref_lvup_def by (metis Suc_eq_plus1 assms(1) diff_diff_cancel msg_def)
qed


lemma xi_lev1:
assumes "ALL p. rho t p ~= Asleep"
and "t > 0"
and "ref_lvup xi t = ref_lvup xi (t+3*k)"
shows "EX s. rho (t+3*k) xi = Active s & level s > 0"
proof -
  obtain s where s:"rho t xi = Active s" using nonAsleepAgain2[of "t-1" xi 1] assms by (cases "rho t xi") auto
  have same_ref:"ALL i <= 3*k. ref_lvup xi (t+i) = ref_lvup xi t"
  proof (rule ccontr)
    assume "~ (ALL i <= 3*k. ref_lvup xi (t+i) = ref_lvup xi t)"
    then obtain ii where "ii <= 3*k" and differ:"~ (ref_lvup xi (t+ii) = ref_lvup xi t)" by blast
    let "?active_path" =
      "% seq t D. seq 0 = xi & seq D = xi & (ALL i < D. rho (Suc t+i) (seq (Suc i)) ~= Asleep & seq i : HO (Suc t+Suc i) (seq (Suc i)))"
    have "?active_path (%_. xi) t ii"
      using loop nonAsleepAgain2 s by (metis add_Suc_shift proc_state.simps(3)) 
    hence "active_path xi xi (Suc t) ii" unfolding active_path_def by auto
    hence "ref_lvup xi t <= ref_lvup xi (t+ii)"
      using growing_path s nonAsleepAgain2 by auto
    moreover have "?active_path (%_. xi) (t+ii) (3*k - ii)"
      using loop s nonAsleepAgain2 by (metis add_Suc_shift proc_state.simps(3)) 
    hence "active_path xi xi (Suc t+ii) (3*k - ii)" unfolding active_path_def by auto
    hence "ref_lvup xi (t+ii) <= ref_lvup xi (t+3*k)"
      using growing_path[of _ _ "t+ii" "3*k-ii"] `ii <= 3*k` s nonAsleepAgain2[of t xi ii] by auto
    ultimately show "False"
      using differ assms(3) by auto
  qed
  obtain sxi where sxi:"ALL i. rho (t+i) xi = Active (sxi i)"
    using s nonAsleepAgain2[of t] by (meson assms(1))
  (*define c where "c = ((k-1) * t + x (sxi 0))"*)
  define c where "c = Suc k - (snd(ref_lvup xi t)) mod k"
  have suite:"ALL i <= 3*k. x (sxi (Suc i)) mod k = (t + i + c) mod k"
  proof (rule+)
    fix i
    assume "i <= 3*k"
    define msg where "msg = HOrcvdMsgs (k_mod.gen_HOMachine k) xi (HO (t+Suc i) xi) (rho (t+i))"
    have "(t + i - k_mod.minMsgs msg) mod k = snd (ref_lvup xi (t+i)) mod k"
      using assms(2) unfolding ref_lvup_def msg_def by (metis add_Suc_right snd_conv)
    hence "(k_mod.minMsgs msg + snd (ref_lvup xi (t+i))) mod k = (t + i) mod k"
      using minMsgs_inf[of "t+i" xi] nonAsleepAgain2[of t xi i] assms
      by (smt (z3) One_nat_def add.commute add.right_neutral add_Suc_right le_add_diff_inverse2 mod_add_cong msg_def proc_state.simps(3))
    hence "k_mod.minMsgs msg mod k = (t + i - snd (ref_lvup xi (t+i))) mod k"
      using ref_inf_t[of "t+i" xi "sxi i"] sxi
      by (smt (z3) add.commute add.right_neutral add_Suc_right diff_add_inverse2 diff_is_0_eq'
      execution.ref_lvup_def execution_axioms le_add_diff_inverse2 msg_def nat_le_linear snd_conv)
    moreover have "k_mod.gen_nextState k xi (sxi i) msg (sxi (Suc i))"
      using transition[of "t+i" xi "sxi i" "sxi (Suc i)"] sxi `t > 0` unfolding msg_def
      by (smt (verit, ccfv_threshold) Nat.add_diff_assoc2 One_nat_def Suc_leI Suc_pred' add.commute add_Suc_right)
    hence "x (sxi (Suc i)) mod k = Suc (k_mod.minMsgs msg) mod k"
      unfolding k_mod.gen_nextState_def k_mod.goto_level1_def k_mod.goto_level2_def
      by (smt (z3) One_nat_def Suc_1 Suc_diff_1 Suc_lessD k2 mod_Suc mod_less)
    ultimately have "x (sxi (Suc i)) mod k = Suc (t + i - snd (ref_lvup xi (t+i))) mod k"
      by (metis mod_Suc_eq)


    hence "x (sxi (Suc i)) mod k = (t + i + Suc k - snd (ref_lvup xi t)) mod k"
      using same_ref `i <= 3*k` ref_inf_t[of t xi "sxi 0"] sxi
      by (smt (z3) Nat.add_diff_assoc2 add.assoc add.commute add.right_neutral add_Suc_shift mod_add_self1)
    hence "x (sxi (Suc i)) mod k = (t + i + Suc k - snd (ref_lvup xi t) mod k) mod k"
      using ref_inf_t[of t xi "sxi 0"] sxi mod_sub[of "snd (ref_lvup xi t)" "t + i + Suc k"]
      by (metis `i <= 3 * k` ref_inf_t same_ref trans_le_add1)
    thus "x (sxi (Suc i)) mod k = (t + i + c) mod k"
      unfolding c_def 
      by (metis Nat.add_diff_assoc dual_order.strict_trans k2 le_add2 le_trans less_2_cases_iff mod_le_divisor plus_1_eq_Suc)
  qed
    
  define tt where "tt = (if (t+c) mod k = 0 then 0 else k - (t+c) mod k)"
  have xi0:"x (sxi (Suc tt)) mod k = 0"
  proof (cases "(t+c) mod k = 0")
    case False
    thus "x (sxi (Suc tt)) mod k = 0" using suite unfolding tt_def
      by (smt (verit, del_insts) add.assoc add.commute k2 le_add1 le_add_diff_inverse less_iff_Suc_add
      mod_add_right_eq mod_le_divisor mod_self mult_Suc numeral_3_eq_3 zero_less_Suc)
  next
    case True
    thus "x (sxi (Suc tt)) mod k = 0" using suite unfolding tt_def by simp
  qed
  have "ALL p. active_path xi p (Suc (t + tt)) k"
  proof
    fix p
    obtain seq where "seq 0 = xi & seq k = p & (ALL i < k. seq i : HO (Suc (t + tt) + Suc i) (seq (Suc i)))"
      using star unfolding k_mod.path_def by presburger
    thus "active_path xi p (Suc (t + tt)) k"
      using assms(1) nonAsleepAgain2 unfolding active_path_def by (metis add.left_commute plus_1_eq_Suc proc_state.simps(3))
  qed
  hence all_larger:"ALL p. ref_lvup p (t+tt+k) >= ref_lvup xi (t+tt)"
    using growing_path[of xi _ "t+tt" k] assms(1) nonAsleepAgain2[of t xi tt] by auto
  
  define cong_xi where "cong_xi = (%i. {p. ref_lvup p (t+tt+k+i) = ref_lvup xi t})"
  have vue_incluse:"ALL i < k. Union ((HO (t+tt+k+Suc (Suc i))) ` cong_xi (Suc i)) <= cong_xi i"
  proof 
    fix i
    show  "i < k --> Union ((HO (t+tt+k+Suc (Suc i))) ` cong_xi (Suc i)) <= cong_xi i"
    proof 
      assume "i < k"
      show  "Union ((HO (t+tt+k+Suc (Suc i))) ` cong_xi (Suc i)) <= cong_xi i"
      proof
        fix p
        assume "p : Union ((HO (t+tt+k+Suc (Suc i))) ` cong_xi (Suc i))"
        then obtain q where q_cong_xi:"q : cong_xi (Suc i)" and lien:"p : HO (t+tt+k+Suc (Suc i)) q" by auto
        have "rho (t+tt+k+Suc i) q ~= Asleep" using nonAsleepAgain2[of t q "tt+k+Suc i"] assms(1) by (metis add.commute add.left_commute proc_state.simps(3))
        hence "active_path p q (t+tt+k+Suc i) 1"
          using exI[of "%seq. seq 0 = p & seq 1 = q & _" "%w. if w = 0 then p else q"]
          unfolding active_path_def
          by (smt (verit, ccfv_threshold) lien add.left_commute add.right_neutral less_one plus_1_eq_Suc zero_neq_one)
        moreover have "rho (t + tt + k + i) p ~= Asleep"
          using nonAsleepAgain2[of t p "tt+k+i"] assms(1)
          by (metis add.assoc proc_state.simps(3))
        ultimately have "ref_lvup p (t+tt+k+i) <= ref_lvup q (t+tt+k+i+1)"
          using growing_path[of p q "t+tt+k+i" 1] k2 by simp
        hence "ref_lvup p (t+tt+k+i) <= ref_lvup xi t" using q_cong_xi unfolding cong_xi_def by auto
        moreover have "ALL i. rho (Suc t + tt + k + i) p ~= Asleep"
          using nonAsleepAgain2[of t p] assms(1) by (metis add.commute add.left_commute plus_1_eq_Suc proc_state.simps(3))
        hence "active_path p p (Suc t+tt+k) i"
          using loop exI[of "%seq. seq 0 = p & seq i = p & _" "%_.p"] unfolding active_path_def by auto
        hence ref_grow:"ref_lvup p (t+tt+k+i) >= ref_lvup p (t+tt+k)"
          using growing_path[of p p "t+tt+k" i] nonAsleepAgain2[of t p "tt+k"] assms(1) k2
          by (metis add.assoc plus_1_eq_Suc proc_state.simps(3))
        have "ref_lvup p (t+tt+k+i) >= ref_lvup xi t"
        proof (cases "(t+c) mod k = 0")
          case False
          thus "ref_lvup p (t+tt+k+i) >= ref_lvup xi t"
            using all_larger same_ref ref_grow unfolding tt_def
            by (smt (z3) diff_le_self dual_order.strict_trans1 le_add1 mult_Suc not_le numeral_3_eq_3)
        next
          case True

          thus "ref_lvup p (t+tt+k+i) >= ref_lvup xi t"
            using all_larger same_ref ref_grow unfolding tt_def
            by (smt (z3) add.right_neutral dual_order.strict_trans1 not_le)
        qed
        ultimately show "p : cong_xi i" unfolding cong_xi_def by auto
      qed
    qed
  qed

  have monoval:"ALL i <= k. ALL sp. ALL p : cong_xi i. rho (Suc t+tt+k+i) p = Active sp --> conc sp & x sp mod k = i mod k"
  proof (rule+)
    fix i sp p
    assume "i <= k" and in_cong:"p : cong_xi i" and sp:"rho (Suc t+tt+k+i) p = Active sp"
    have "conc sp & x sp mod k = i mod k" using sp in_cong `i <= k`
    proof (induction i arbitrary: p sp)
      case 0
      hence eq1:"x sp mod k = Suc (t + tt + k - snd (ref_lvup xi t)) mod k"
        using ref_cong_x[of "t+tt+k" p sp] nonAsleepAgain2[of t p "tt+k"] assms(1)
        unfolding cong_xi_def by (smt (verit, del_insts) add.left_commute add.right_neutral mem_Collect_eq plus_1_eq_Suc proc_state.simps(3))
      have eq2:"Suc (t+tt - snd (ref_lvup xi (t+tt))) mod k = 0"
        using xi0 ref_cong_x[of "t+tt" xi "sxi (Suc tt)"] nonAsleepAgain2[of t xi tt] sxi
        by (metis add_Suc_right proc_state.simps(3))
      have "x sp mod k = 0"
      proof (cases "(t+c) mod k = 0")
        case False
        thus "x sp mod k = 0" using eq1 eq2
          by (smt (z3) Nat.add_diff_assoc2 diff_le_self le_add1 le_trans mod_Suc mod_add_self2 mult_Suc numeral_3_eq_3 ref_inf_t s same_ref tt_def)
      next
        case True
        thus "x sp mod k = 0" using eq1 eq2 by (metis add_cancel_right_right mod_Suc mod_add_self2 ordered_cancel_comm_monoid_diff_class.add_diff_assoc2 ref_inf_t s tt_def)
      qed


      moreover define msg where "msg = HOrcvdMsgs (k_mod.gen_HOMachine k) p (HO (Suc (t+tt+k)) p) (rho (t+tt+k))"
      obtain ssp where "rho (t+tt+k) p = Active ssp" using nonAsleepAgain2[of t p "tt+k"] assms(1) by (metis add.assoc)
      hence "k_mod.gen_nextState k p ssp msg sp" using transition run sp assms(2) `rho (Suc t+tt+k+0) p = Active sp` unfolding msg_def by auto
      ultimately show ?case unfolding k_mod.gen_nextState_def by auto
    next
      case (Suc i) 
      define msg where "msg = HOrcvdMsgs (k_mod.gen_HOMachine k) p (HO (Suc (t+tt+k+Suc i)) p) (rho (t+tt+k+Suc i))"
      have inc:"ALL q : {p. msg p ~= Void}. EX s. msg q = Content s & conc s & x s mod k = i"
      proof 
        fix q
        assume "q : {p. msg p ~= Void}"
        hence q_in_HO:"q : HO (Suc t+tt+k+Suc i) p" unfolding msg_def HOrcvdMsgs_def by auto
        hence "q : cong_xi i" using `Suc i <= k` vue_incluse `p : cong_xi (Suc i)` by (smt (z3) Suc_le_lessD UN_I add.commute add_Suc subsetD)
        moreover obtain sq where sq:"rho (t+tt+k+Suc i) q = Active sq" using assms(1) nonAsleepAgain2[of t q "tt+k+Suc i"] by (metis add.assoc)
        ultimately have "x sq mod k = i & conc sq" using Suc.IH `Suc i <= k` by auto
        moreover have "msg q = Content sq" using q_in_HO unfolding msg_def HOrcvdMsgs_def by (metis HOrcvdMsgs_def add_Suc sending sq)
        ultimately show "EX s. msg q = Content s & conc s & x s mod k = i" by auto
      qed
      obtain spp where spp:"rho (t+tt+k+Suc i) p = Active spp" using assms(1) nonAsleepAgain2[of t p "tt+k+Suc i"] by (metis add.assoc)
      obtain q sq where "msg q = Content sq" and "k_mod.minMsgs msg = x sq" and "rho (t+tt+k+Suc i) q = Active sq" 
        using adopt_incoming[of "t+tt+k+Suc i" p _ msg] spp unfolding msg_def by auto
      obtain sq2 where "msg q = Content sq2" and "x sq2 mod k = i" using inc `msg q = Content sq` by (metis (mono_tags, lifting) mem_Collect_eq message.distinct(3))
      hence "x sq mod k = i" using `msg q = Content sq` by auto
      hence min_i:"k_mod.minMsgs msg mod k = i" using `k_mod.minMsgs msg = x sq` by auto
      hence "k_mod.isSynch k msg" using inc unfolding k_mod.isSynch_def by auto
      moreover have "k_mod.gen_nextState k p spp msg sp" using transition[of "t+tt+k+Suc i" p spp sp] Suc.prems(1) spp unfolding msg_def by auto
      ultimately show "conc sp & x sp mod k = (Suc i) mod k" using min_i `Suc i <= k` unfolding k_mod.gen_nextState_def
        by (metis Suc_diff_1 dual_order.strict_trans1 k_mod.goto_level1_def k_mod.goto_level2_def mod_Suc mod_mod_trivial zero_less_Suc)
    qed
    thus "conc sp " and " x sp mod k = i mod k"  by auto
  qed
  define msg where "msg = HOrcvdMsgs (k_mod.gen_HOMachine k) xi (HO (Suc (t+tt+k+k)) xi) (rho (t+tt+k+k))"
  have inc_ho:"ALL p sp. msg p = Content sp --> conc sp & x sp mod k = k - 1"
  proof -
    { 
      fix p sp
      assume sp:"msg p = Content sp"
      hence ho_xi:"p : HO (t+tt+k+Suc k) xi" unfolding msg_def HOrcvdMsgs_def by simp
      moreover have "ref_lvup xi (t+(tt+k+k)) = ref_lvup xi t" using same_ref unfolding tt_def by auto 
      hence "ref_lvup xi (t+tt+k+k) = ref_lvup xi t" by (simp add:add.assoc)
      hence "xi : cong_xi (Suc (k-1))" using k2 unfolding cong_xi_def by auto
      hence "p : cong_xi (k-1)" using vue_incluse ho_xi by (smt (z3) Suc_diff_1 UN_I diff_less dual_order.strict_trans k2 less_2_cases_iff subsetD zero_less_one)
      moreover have "rho (t+tt+k+k) p = Active sp" using sending_rec[of xi "t+tt+k+k" p sp] using sp unfolding msg_def by auto
      ultimately have "conc sp  & x sp mod k = (k - 1) mod k"
        using monoval sp k2 by (smt (z3) Suc_1 Suc_diff_1 Suc_lessD add.assoc add.right_neutral add_Suc_right diff_le_self plus_1_eq_Suc)
      hence "conc sp  & x sp mod k = k - 1" by (metis diff_less dual_order.strict_trans k2 less_2_cases_iff mod_less zero_less_one)
    }
    thus ?thesis by blast
  qed
  hence minmsg:"k_mod.minMsgs msg mod k = k - 1" using adopt_incoming[of "t+tt+k+k" xi "sxi (tt+k+k)" msg]
    using sxi unfolding msg_def by (smt (z3) add.commute add.left_commute)
  have "k_mod.isSynch k msg"
  proof -
    {
      fix p
      assume non_void:"msg p ~= Void"
      obtain sp where "rho (t+tt+k+k) p = Active sp" using nonAsleepAgain2[of t p "tt+k+k"] assms(1) by (metis add.assoc)
      hence "msg p = Content sp" using sending using non_void unfolding msg_def by auto
      hence "EX sp. msg p = Content sp & conc sp & x sp mod k = k_mod.minMsgs msg mod k" using inc_ho minmsg by auto
    }
    thus "k_mod.isSynch k msg" unfolding k_mod.isSynch_def by blast
  qed
  hence "level (sxi (tt+k+k)) = 0 --> k_mod.goto_level1 k msg (sxi (tt+k+k))" using sxi minmsg unfolding k_mod.goto_level1_def by auto
  moreover have "k_mod.gen_nextState k xi (sxi (tt+k+k)) msg (sxi (tt+k+Suc k))"
    using transition[of "t+tt+k+k" xi "sxi (tt+k+k)" "sxi (tt+k+Suc k)"] sxi unfolding msg_def by (metis add.assoc add_Suc_right)
  ultimately have "level (sxi (tt+k+Suc k)) > 0" unfolding k_mod.gen_nextState_def by auto
  moreover have "tt < k" using k2 unfolding tt_def by auto
  hence "3 * k >= tt + k + Suc k" by linarith
  hence "rho (t+tt+k+Suc k+(3*k - (tt+k+Suc k))) xi = Active (sxi (3*k))"
    using sxi by (smt (verit, best) Suc_leI add.assoc add.commute add_diff_inverse_nat diff_add_inverse2 not_less_eq_eq numeral_3_eq_3)
  ultimately show ?thesis using level_growing[of "t+tt+k+Suc k" xi "sxi (tt+k+Suc k)" "(3 * k) - (tt+k+Suc k)" "sxi (3*k)"] sxi
    by (metis add.commute add.left_commute neq0_conv not_le)
qed

definition early_lvup_non_xi where
"early_lvup_non_xi = {lv. lv : L_minus_xi & (let (f,t) = lv in  (ALL s. rho t xi = Active s --> level s = 0))}"
definition early_lvup where
"early_lvup = {lv. lv : L & (let (f,t) = lv in  (ALL s. rho t xi = Active s --> level s = 0))}"
lemma non_xi_in_all_early: "early_lvup_non_xi <= early_lvup" unfolding early_lvup_def early_lvup_non_xi_def L_def L_minus_xi_def by auto

lemma no_early_fire:
assumes "(f,t) : early_lvup"
shows "f < 2"
proof (rule ccontr)
  assume "~ (f < 2)"
  obtain p sp ssp where 
    ssp:"rho t p = Active ssp" and fssp:"level ssp = f" and newf:"if f = 0 then t > 0 --> rho (t-1) p = Asleep else rho (t-1) p = Active sp & level sp = f-1"
    using assms unfolding early_lvup_def L_def levup_def by blast
  hence sp:"rho (t-1) p = Active sp" and fsp:"level sp = f-1" using `~ (f < 2)` by auto
  hence t:"t > 0" using fsp fssp sp ssp `~ (f < 2)` by (metis A2 dual_order.strict_trans gr0I k2 zero_less_numeral)
  define msg where "msg = HOrcvdMsgs (k_mod.gen_HOMachine k) p (HO t p) (rho (t-1))" 
  have trans:"k_mod.gen_nextState k p sp msg ssp"
    using t ssp sp transition[of "t-1"]  unfolding msg_def by (metis Suc_diff_1)
  show "False"
  proof (cases "f = 2")
    case True
    hence goto2:"k_mod.goto_level2 k msg sp" and "x ssp = 0 | x ssp = Suc (k_mod.minMsgs msg)" using trans fsp fssp unfolding k_mod.gen_nextState_def by auto
    hence "x ssp mod k = 0" using mod_Suc_eq[of "k_mod.minMsgs msg" k]
      unfolding k_mod.goto_level2_def by (metis Suc_diff_1 dual_order.strict_trans k2 less_2_cases_iff mod_less mod_self)
    have "k_mod.isSynch k msg & k_mod.isReady msg" using goto2 unfolding k_mod.goto_level2_def by simp
    moreover have t:"t >= k" using True fsp fssp sp ssp by (metis A2 less_one not_le_imp_less not_numeral_less_one)
    ultimately obtain s where s:"rho (t-k) xi = Active s" and "ready s" and "x s mod k = 0"
      using A1[of xi p "t-k" 0 ssp] t k2 ssp star `x ssp mod k = 0` unfolding msg_def by auto
    hence "t > k & rho (t-k-1) xi ~= Asleep" using starting[of "t-k"] unfolding k_mod.gen_initState_def by (metis locState.select_convs(3) zero_less_diff)
    then obtain ss where ss:"rho (t-k-1) xi = Active ss" and "t > k" by (cases "rho (t-k-1) xi") auto
    define msgx where "msgx = HOrcvdMsgs (k_mod.gen_HOMachine k) xi (HO (t-k) xi) (rho (t-k-1))" 
    have "k_mod.gen_nextState k xi ss msgx s"
      using t s ss transition[of "t-k-1" xi ss s] `t > k` unfolding msgx_def by (metis Suc_diff_1 zero_less_diff)
    hence "level s > 0" using `ready s` `x s mod k = 0` unfolding k_mod.gen_nextState_def  by auto
    moreover obtain st where st:"rho t xi = Active st" using nonAsleepAgain2[of "t-k" xi k] `t >= k` s by auto
    ultimately have "level st > 0" using level_growing[of "t-k" xi s k st] s `t >= k` by auto
    thus "False" using assms st unfolding early_lvup_def by auto
  next
    case False
    thus "False" using ssp `level ssp = f` `~ (f < 2)` sp `level sp = f - 1` trans unfolding k_mod.gen_nextState_def by auto
  qed
qed

lemma lvup_unique:
assumes "levup f t p"
and "levup f t2 p"
and "t <= t2"
shows "t = t2"
proof (rule ccontr)
  assume "t ~= t2"
  hence "t < t2" using assms(3) by auto
  obtain ssp where 
    ssp:"rho t p = Active ssp" and fssp:"level ssp = f" 
    using assms(1) unfolding early_lvup_def L_def levup_def by blast
  then obtain sp2 where 
    newf2:"if f = 0 then t2 > 0 --> rho (t2-1) p = Asleep else rho (t2-1) p = Active sp2 & level sp2 = f-1"
    using assms(2) unfolding levup_def by blast
  show "False"
  proof (cases f)
    case 0
    hence "rho (t2 - 1) p = Asleep" using newf2 `t < t2` by auto
    thus "False" using nonAsleepAgain2[of t p "t2-1-t"] ssp `t < t2` by auto
  next
    case (Suc ff)
    hence "rho (t2-1) p = Active sp2 & level sp2 = f - 1" using newf2 by auto
    thus "False" using level_growing[of t p ssp "t2-1-t"] `t < t2` ssp fssp Suc by auto
  qed
qed

lemma card_union:
assumes "card e1 <= (N :: nat) - 1"
and "card e2 <= N - 1"
shows "card (e1 Un e2) <= 2 * (N - 1)"
using Finite_Set.card_Un_le by (smt (z3) add.assoc add.left_commute assms(1) assms(2) mult_2 nat_le_iff_add)

lemma max_lvup:
"card early_lvup_non_xi <= 2 * (N - 1)"
proof -
  define get_lvup where "get_lvup = (%f p. SOME t. levup f t p)"
  have "ALL tup : early_lvup_non_xi. EX p ~= xi. (let (f,t) = tup in get_lvup f p = t)"
  proof -
    {
      fix f t
      assume early:"(f,t) : early_lvup_non_xi"
      then obtain p where lvt:"levup f t p" and "p ~= xi"
        unfolding early_lvup_non_xi_def L_minus_xi_def levup_def by blast
      define t2 where "t2 = get_lvup f p"
      hence lvt2:"levup f t2 p" using someI_ex[of "%t. levup f t p"] lvt unfolding get_lvup_def by auto
      hence "t = t2" using lvup_unique lvt by (metis nat_le_linear)
      hence "EX p. p ~= xi & get_lvup f p = t" using `p ~= xi` unfolding t2_def by auto
    }
    thus  "ALL tup : early_lvup_non_xi. EX p ~= xi. (let (f,t) = tup in get_lvup f p = t)" by fastforce
  qed
  hence "ALL tup : early_lvup_non_xi. EX p ~= xi. get_lvup (fst tup) p = snd tup & (fst tup = 0 | fst tup = 1)"
    using no_early_fire less_2_cases_iff non_xi_in_all_early by fastforce
  hence "early_lvup_non_xi <= ((%t. (0,t)) ` (get_lvup 0) ` {p. p ~= xi}) Un ((%t. (1,t)) ` (get_lvup 1) ` {p. p ~= xi})" (is "_ <= ?e1 Un ?e2")
    by fastforce
  moreover have "card {p. p ~= xi} <= N - 1"
    using finite_UNIV
    by (metis (mono_tags, lifting) Suc_leI UNIV_I card_Diff_singleton card_Suc_Diff1 card_seteq mem_Collect_eq not_le subset_UNIV)
  hence "card ?e1 <= N - 1 & card ?e2 <= N - 1" 
    by (smt (z3) card_image_le finite image_image le_trans)
  moreover have "finite ?e1 & finite ?e2" by auto
  ultimately show ?thesis by (meson card_mono card_union finite_UnI le_trans)
qed

lemma inj_strict:
assumes "ALL i < b. (f :: nat => nat * nat) (Suc i) > f (i :: nat)"
shows "inj_on f {i. i <= b}"
proof -
  {
    fix i j 
    assume "i <= b" and "j <= b" 
    hence "i < j --> f i < f j"
    proof (induction "j - i" arbitrary: i j)
      case 0
      thus ?case by simp
    next
      case (Suc d)
      hence ind:"i < j - 1 --> f i < f (j - 1)" by auto
      thus ?case using Suc by (smt (verit, ccfv_threshold) Suc_diff_Suc Suc_leI assms diff_Suc_1 dual_order.strict_trans less_le_trans linorder_neqE_nat not_less_eq)
    qed
  }
  hence "ALL i j. i <= b --> j <= b --> i < j --> f i < f j" by blast
  thus "inj_on f {i. i <= b}" by (metis (mono_tags, lifting) less_le linorder_inj_onI mem_Collect_eq nat_le_linear)
qed

lemma xi_reaches_lv1:
assumes "ALL p. rho t p ~= Asleep"
and "rho (t + (2 * N - 1) * (3 * k)) xi = Active s" (is "rho (t+?t) _ = _")
and "t > 0"
shows "level s > 0"
proof (rule ccontr)
  assume "~ (level s > 0)"
  define h where "h = 3 * k"
  define z_incr where "z_incr = (%i. ref_lvup xi (t + i * h))"
  obtain sxi where sxi:"ALL i. rho (t+i) xi = Active (sxi i)"
    using nonAsleepAgain2[of t] by (meson assms(1))
  have "ALL i. z_incr (Suc i) >= z_incr i"  
  proof 
    fix i
    have "ALL j. rho (Suc t+i*h+j) xi ~= Asleep" using sxi by (metis add.assoc add_Suc_shift proc_state.simps(3))
    hence "active_path xi xi (Suc t+i*h) h"
      using loop exI[of "%s. _ & _ & (ALL j < h. _ & s j : _ (s (Suc j)))" "%_. xi"]
      unfolding active_path_def by auto
    thus "z_incr (Suc i) >= z_incr i" using growing_path[of xi xi "t+i*h"] sxi unfolding z_incr_def
      by (smt (z3) Suc_eq_plus1 add.commute add.left_commute mult.commute mult_Suc_right proc_state.simps(3))
  qed
  moreover have "ALL i < 2 * N - 1. z_incr (Suc i) ~= z_incr i"
  proof (rule+)
    fix i
    assume "i < 2 * N - 1" and "z_incr (Suc i) = z_incr i"
    hence same_r:"ref_lvup xi (t+i*h) = ref_lvup xi (t+i*h+h)"
      unfolding z_incr_def by (metis add.assoc add.commute mult_Suc)
    hence "?t >= Suc i * h" using Suc_leI h_def mult_le_mono1 `i < 2 * N - 1` by presburger
    hence "level (sxi (i*h+h)) = 0"
      using level_growing[of "t+Suc i*h" xi "sxi (Suc i*h)" "?t - (Suc i)*h" "sxi ((2*N-1)*h)"] sxi `~ (level s > 0)` assms(2)
      unfolding h_def
      by (smt (z3) add.assoc add.commute gr0I le_0_eq le_add_diff_inverse mult.assoc mult_Suc proc_state.inject)
    moreover have "ALL p. rho (t+i*h) p ~= Asleep"
      using assms(1) nonAsleepAgain2[of _ _ "i*h"] by (metis proc_state.simps(3))
    ultimately show "False"
      using xi_lev1[of "t+i*h"] `t > 0` sxi same_r unfolding h_def by (simp add: ab_semigroup_add_class.add_ac(1))
  qed
  ultimately have "ALL i < 2 * N - 1. z_incr (Suc i) > z_incr i" by (metis less_le)
  hence "inj_on z_incr {i. i <= 2 * N - 1}" using inj_strict by auto
  moreover have "N > 0" by (simp add: finite_UNIV_card_ge_0)
  hence "card {i. i <= 2 * N - 1} = 2 * N" using card_Collect_less_nat by auto
  ultimately have "card (z_incr ` {i. i <= 2 * N - 1}) = 2 * N" (is "card ?range_xi = _") using card_image by metis

  have "?range_xi <= early_lvup_non_xi Un (%t. (0,t)) ` {t. levup 0 t xi}"
  proof -
    {
      fix i
      assume "i <= 2 * N - 1" and non_xi:"~ (z_incr i) : (Pair 0) ` {t. levup 0 t xi}"
      obtain f tt where ft:"(f,tt) = z_incr i" by (metis prod.exhaust_sel)
      then obtain p where "levup f tt p"
        using in_L[of "t+i*h" xi "sxi (i*h)"] sxi unfolding z_incr_def L_def by auto
      have "tt <= t + i * h" using ref_inf_t[of "t+i*h" xi "sxi (i*h)"] sxi ft snd_conv unfolding z_incr_def by metis
      hence "tt <= t + (2 * N - 1) * (3 * k)" using `i <= 2 * N - 1` h_def by (smt (z3) add.commute comm_semiring_class.distrib le_diff_conv less_eqE trans_le_add1)
      hence "ALL ss. rho tt xi = Active ss --> level ss = 0"
        using level_growing[of tt xi _ "t + (2 * N - 1) * (3 * k) - tt" s] assms `~ (level s > 0)` by auto
      moreover from this have "ALL f. levup f tt xi --> f = 0" unfolding levup_def by auto
      hence "p ~= xi" using non_xi `levup f tt p` ft unfolding z_incr_def by (metis image_eqI mem_Collect_eq)
      hence "(f,tt) : L_minus_xi" using `levup f tt p` unfolding L_minus_xi_def by auto
      ultimately have "z_incr i : early_lvup_non_xi" using `(f,tt) : L_minus_xi` ft unfolding early_lvup_non_xi_def by auto
    }
    thus "?range_xi <= early_lvup_non_xi Un (Pair 0) ` {t. levup 0 t xi}" by fastforce
  qed
  moreover have card0_or_1:"{t. levup 0 t xi} ~= {} --> card {t. levup 0 t xi} = 1" (is "_ --> card ?lev0_xi = _")
  proof 
    assume "{t. levup 0 t xi} ~= {}"
    moreover from this obtain tt where tt:"levup 0 tt xi" by auto
    moreover have "ALL ttt. levup 0 ttt xi --> ttt = tt"
      using lvup_unique[of 0 _ xi] tt by (metis linear)
    moreover from this have "finite ?lev0_xi" using finite_nat_set_iff_bounded_le by auto
    ultimately show "card ?lev0_xi = 1" using card_Diff_singleton[of _ tt] tt
    by (metis (no_types, lifting) One_nat_def Suc_leI card_gt_0_iff card_le_Suc0_iff_eq diff_diff_cancel diff_is_0_eq diff_zero mem_Collect_eq)
  qed
  hence fin_lev0:"finite ?lev0_xi" by (metis card_eq_0_iff infinite_imp_nonempty zero_neq_one)
  hence "finite (early_lvup_non_xi Un Pair 0 ` ?lev0_xi)" using finite_L finite_subset[of early_lvup_non_xi L] unfolding early_lvup_non_xi_def L_minus_xi_def L_def by auto
  ultimately have "card ?range_xi <= card early_lvup_non_xi + 1"
    using card_Un_le[of early_lvup_non_xi] card_image_le[of ?lev0_xi "Pair 0"] card_mono[of "early_lvup_non_xi Un Pair 0 ` ?lev0_xi"]
    by (smt (z3) Nat.add_0_right One_nat_def Suc_pred fin_lev0 card0_or_1 card.empty card_gt_0_iff diff_is_0_eq' finite_imageI le_0_eq le_trans trans_le_add1)
  thus "False"
    using max_lvup `N > 0` `card ?range_xi = 2 * N` by auto
qed

lemma no_fire_before_xi_lev1:
assumes "rho t xi = Active s"
and "level s = 0"
shows "fst (ref_lvup xi t) < 2"
proof (rule ccontr)
  assume ccontr:"~ fst (ref_lvup xi t) < 2"
  define msg where "msg = HOrcvdMsgs (k_mod.gen_HOMachine k) xi (HO (Suc t) xi) (rho t)" 
  have "k_mod.maxForce msg >= 3" (is "?f >= 3") using ccontr unfolding ref_lvup_def msg_def
    by (metis A2_bis One_nat_def Suc_1 Suc_leI adopt_incoming assms(1) fst_conv le_add_diff_inverse not_less_eq numeral_3_eq_3 plus_1_eq_Suc)
  from this obtain q sq sqq where sqq:"rho (t - k_mod.minMsgs msg) q = Active sqq" and "level sqq = ?f - 1"
    and sq:"rho (t - Suc (k_mod.minMsgs msg)) q = Active sq" and "level sq = ?f - 2"
    using assms A5[of t xi s ?f "Suc (k_mod.minMsgs msg)"] unfolding msg_def by auto
  hence tq:"t >= Suc (k_mod.minMsgs msg)" using `?f >= 3`
    by (metis A2 One_nat_def diff_is_0_eq dual_order.strict_trans k2 less_2_cases_iff nat_le_linear not_less_eq_eq numeral_3_eq_3)
  define tq where "tq = t - Suc (k_mod.minMsgs msg)"
  define msgq where "msgq = HOrcvdMsgs (k_mod.gen_HOMachine k) q (HO (Suc tq) q) (rho tq)" 
  have trans:"k_mod.gen_nextState k q sq msgq sqq"  
    using sq sqq tq transition[of "t - Suc (k_mod.minMsgs msg)" q sq sqq]
    unfolding msgq_def tq_def by (simp add: Suc_diff_Suc Suc_le_lessD)
  hence "k_mod.goto_level2 k msgq sq" 
    using `?f >= 3` `level sq = ?f - 2` `level sqq = ?f - 1` unfolding k_mod.gen_nextState_def by auto
  hence "x sqq mod k = 0" using trans unfolding k_mod.goto_level2_def k_mod.gen_nextState_def
    by (metis Suc_diff_1 k2 less_trans mod_Suc mod_less zero_less_numeral)
  have "tq >= k" using sq `level sq = ?f - 2` `?f >= 3` A2[of tq q sq]
    unfolding tq_def by (metis `k_mod.goto_level2 k msgq sq` k_mod.goto_level2_def not_le zero_neq_one) 
  hence "EX sx. rho (Suc tq-k) xi = Active sx & (k_mod.isReady msgq --> ready sx)"
    using A1[of xi q "Suc tq-k" 0 sqq] sqq `k_mod.goto_level2 k msgq sq` `x sqq mod k = 0` star k2
    unfolding tq_def k_mod.goto_level2_def msgq_def
    by (smt (verit, ccfv_SIG) A2 Suc_diff_Suc Suc_le_lessD Zero_not_Suc `?f >= 3` `level sq = ?f - 2` `level sqq = ?f - 1`
    add.commute add.right_neutral add_diff_inverse_nat diff_Suc_1 diff_zero dual_order.strict_trans less_add_Suc1 numeral_3_eq_3 plus_1_eq_Suc tq)
  then obtain sx where sx:"rho (Suc tq-k) xi = Active sx & ready sx"
    using `k_mod.goto_level2 k msgq sq` unfolding k_mod.goto_level2_def by auto
  hence "level sx > 0" using ready_level by auto
  thus "False"
    using assms level_growing[of "Suc tq - k" xi sx "t - (Suc tq - k)" s] sx tq unfolding tq_def by fastforce
qed

lemma merge_path:
assumes "active_path p q t i"
and "active_path q r (t+i) j"
shows "active_path p r t (i+j)"
proof -
  obtain seq where seq:"seq 0 = p & seq i = q & (ALL h < i. rho (t+h) (seq (Suc h)) ~= Asleep & seq h : HO (t + Suc h) (seq (Suc h)))"
    using assms(1) unfolding active_path_def by presburger
  obtain seq2 where seq2:"seq2 0 = q & seq2 j = r & (ALL h < j. rho (t+i+h) (seq2 (Suc h)) ~= Asleep & seq2 h : HO (t + i + Suc h) (seq2 (Suc h)))"
    using assms(2) unfolding active_path_def by presburger
  define seq3 where "seq3 = (%h. if h <= i then seq h else seq2 (h - i))"
  have "seq3 0 = p & seq3 (i+j) = r"
    using seq seq2 unfolding seq3_def by auto
  moreover have "ALL h < i+j. rho (t+h) (seq3 (Suc h)) ~= Asleep & seq3 h : HO (t + Suc h) (seq3 (Suc h))"
  proof -
    {
      fix h
      assume "h < i + j"
      have "rho (t+h) (seq3 (Suc h)) ~= Asleep & seq3 h : HO (t + Suc h) (seq3 (Suc h))"
      proof (cases "h < i")
        case True
        thus "rho (t+h) (seq3 (Suc h)) ~= Asleep & seq3 h : HO (t + Suc h) (seq3 (Suc h))"
          using seq seq2 unfolding seq3_def by auto
      next
        case False
        hence "rho (t+i+(h-i)) (seq2 (Suc (h-i))) ~= Asleep & seq2 (h-i) : HO (t + i + Suc (h-i)) (seq2 (Suc (h-i)))"
          using seq2 `h < i + j` by (metis add_diff_cancel_left' le_add_diff_inverse2 less_diff_conv not_le_imp_less)
        thus "rho (t+h) (seq3 (Suc h)) ~= Asleep & seq3 h : HO (t + Suc h) (seq3 (Suc h))"
          using `h < i + j` False Suc_diff_le seq seq2 unfolding seq3_def by fastforce
      qed
    }
    thus "ALL h < i+j. rho (t+h) (seq3 (Suc h)) ~= Asleep & seq3 h : HO (t + Suc h) (seq3 (Suc h))" by blast
  qed
  ultimately show ?thesis using exI[of _ seq3] unfolding active_path_def by auto
qed

definition txi where "txi = (LEAST t. EX s. rho t xi = Active s & level s > 0)"
definition txi2 where "txi2 = (LEAST tt. (ALL p. rho tt p ~= Asleep) & tt >= txi & (tt - txi) mod k = 0)"

lemma txi_props:
assumes "t > 0"
and "ALL p. rho t p ~= Asleep"
shows "ALL p. rho txi2 p ~= Asleep"
and "txi2 >= txi"
and "(txi2 - txi) mod k = 0"
and "EX ss. rho txi xi = Active ss & level ss > 0"
and "txi2 <= t + (2 * N - 1) * (3 * k)"
proof -
  have "txi + t * k >= t" using k2
    by (metis Suc_leI le_add1 le_trans mult.right_neutral mult_le_mono order_refl plus_1_eq_Suc trans_le_add2)
  hence "ALL p. rho (txi + t * k) p ~= Asleep" using nonAsleepAgain2[of t _ "txi + t * k - t"] k2 assms(2)
    by (metis le_add_diff_inverse proc_state.simps(3)) 
  hence "(ALL p. rho txi2 p ~= Asleep) & txi2 >= txi & (txi2 - txi) mod k = 0"
    using Least_le unfolding txi2_def by (smt (verit, del_insts) LeastI_ex add.commute diff_add_inverse2 le_add2 mod_mult_self1_is_0 mult.commute)
  thus act:"ALL p. rho txi2 p ~= Asleep" and "txi2 >= txi" and "(txi2 - txi) mod k = 0" by auto
  define txi3 where "txi3 = t + (2 * N - 1) * (3 * k)"
  obtain ss3 where ss3:"rho txi3 xi = Active ss3"
    using nonAsleepAgain2 assms(2) unfolding txi3_def by presburger
  hence "level ss3 > 0" using xi_reaches_lv1[of t ss3] assms unfolding txi3_def by auto
  hence txi3:"EX s. rho txi3 xi = Active s & level s > 0" using ss3 by auto
  thus "EX ss. rho txi xi = Active ss & level ss > 0" (is "?P txi")
    using LeastI_ex[of "%t. EX s. rho t xi = Active s & level s > 0"]
    LeastI_ex[of "%t. EX s. rho t xi = Active s & level s > 0"]
    exI[of "%t. EX s. rho t xi = Active s & level s > 0" txi2] unfolding txi_def by auto
  show "txi2 <= t + (2 * N - 1) * (3 * k)"
  proof (cases "txi < t")
    case False
    moreover from this have "ALL p. rho txi p ~= Asleep" using assms nonAsleepAgain2[of t _ "txi - t"]
      by (metis add_diff_inverse_nat proc_state.simps(3))
    ultimately have "txi >= txi2"
      using Least_le[of "%t. (ALL p. rho t p ~= Asleep) & t >= txi & (t - txi) mod k = 0" txi]
      unfolding txi2_def by auto
    moreover have "txi3 >= txi"
      using Least_le[of _ txi3] `EX ss. rho txi3 xi = Active ss & level ss > 0` unfolding txi_def by auto
    ultimately show "txi2 <= t + (2 * N - 1) * (3 * k)" unfolding txi3_def by auto
  next
    case True
    define txi4 where "txi4 = t + (k - (t - txi) mod k)"
    have "(txi4 - txi) mod k = 0" unfolding txi4_def
      by (smt (z3) Nat.add_diff_assoc2 Suc_1 Suc_lessD True add.commute add_diff_inverse_nat k2 less_or_eq_imp_le
      mod_add_right_eq mod_le_divisor mod_self not_le plus_1_eq_Suc zero_less_Suc)
    hence "(ALL p. rho txi4 p ~= Asleep) & txi4 >= txi & (txi4 - txi) mod k = 0"
      using nonAsleepAgain2[of t _ "txi4 - t"] assms(2) True unfolding txi4_def
      by (metis le_add1 le_add_diff_inverse le_trans less_or_eq_imp_le proc_state.simps(3))
    hence "txi2 <= txi4" using Least_le[of _ txi4] unfolding txi2_def by auto
    hence "txi2 <= t + 1 * (3 * k) + (2 * N - 2) * (3 * k)" unfolding txi4_def by linarith
    moreover have "2 * N >= 2" using not_less_eq_eq by fastforce
    ultimately show "txi2 <= t + (2 * N - 1) * (3 * k)"
      by (smt (z3) add.assoc add_diff_cancel_left' le_add_diff_inverse mult_Suc nat_mult_1 one_add_one plus_1_eq_Suc)
  qed
qed

lemma txi_props2:
shows "ALL p. rho txi2 p ~= Asleep"
and "txi2 >= txi"
and "(txi2 - txi) mod k = 0"
and "EX ss. rho txi xi = Active ss & level ss > 0"
and "txi2 > 0"
proof -
  obtain t where "ALL p. rho t p ~= Asleep" using complete by auto
  hence "ALL p. rho (Suc t) p ~= Asleep" using nonAsleepAgain2[of t _ 1] by (metis Suc_eq_plus1 proc_state.simps(3))
  thus "ALL p. rho txi2 p ~= Asleep"
    and "txi2 >= txi"
    and "(txi2 - txi) mod k = 0"
    and "EX ss. rho txi xi = Active ss & level ss > 0"
    using txi_props[of "Suc t"] by auto
  hence "txi > 0" using starting[of txi xi] k_mod.gen_initState_def by (metis less_numeral_extra(3) locState.select_convs(5))
  thus "txi2 > 0" using `txi2 >= txi` by auto
qed

lemma xi_lev1_monovalent:
assumes "rho (txi2 + k) p = Active sp"
and "txi2 > 0"
shows "x sp mod k = 0"
proof -
  obtain ss where ss:"rho txi xi = Active ss" and "level ss > 0" using txi_props2(4) by auto
  have txi_init:"txi > 0 & rho (txi-1) xi ~= Asleep"
    using starting[of txi xi ss] ss `level ss > 0` unfolding k_mod.gen_initState_def by fastforce
  then obtain sss where sss:"rho (txi-1) xi = Active sss" by (cases "rho (txi-1) xi") auto
  hence "level sss = 0" using Least_le[of _ "txi-1"] txi_init unfolding txi_def by (metis (mono_tags, lifting) Suc_n_not_le_n Suc_pred' zero_order(5))
  define msg where "msg = HOrcvdMsgs (k_mod.gen_HOMachine k) xi (HO txi xi) (rho (txi-1))" 
  have "k_mod.maxForce msg < 3" using no_fire_before_xi_lev1 sss txi_init `level sss = 0`
    unfolding ref_lvup_def msg_def by (metis One_nat_def Suc_leI Suc_pred' add_diff_inverse_nat fst_conv le_imp_less_Suc less_SucI numeral_2_eq_2 numeral_3_eq_3 plus_1_eq_Suc)
  moreover have "k_mod.gen_nextState k xi sss msg ss"
    using sss ss transition[of _ xi sss ss] txi_init unfolding msg_def by (metis Suc_diff_1)
  ultimately have "x ss = 0 & forc ss = 2" using `level ss > 0` `level sss = 0` sss ss txi_init
    unfolding k_mod.gen_nextState_def by (metis One_nat_def Suc_1 gr_implies_not0 k_mod.goto_level2_def not_less_eq numeral_3_eq_3)


  have inc_link:"ALL q. rho txi q ~= Asleep --> xi : HO (Suc txi) q --> ref_lvup q txi >= (1, txi)"
  proof (rule+)
    fix q
    assume "rho txi q ~= Asleep" and "xi : HO (Suc txi) q"
    define msgq where "msgq = HOrcvdMsgs (k_mod.gen_HOMachine k) q (HO (Suc txi) q) (rho (txi))" 
    have "msgq xi = Content ss" using sending ss `xi : HO (Suc txi) q` unfolding msgq_def by auto
    thus "ref_lvup q txi >= (1, txi)"
    proof (cases "k_mod.maxForce msgq = 2")
      case True
      hence "k_mod.minMsgs msgq = 0"
        using Least_le[of "%v. EX s p. msgq p = Content s & forc s = k_mod.maxForce msgq & x s = v" 0]
        `x ss = 0 & forc ss = 2` `msgq xi = Content ss`
        unfolding k_mod.minMsgs_def msgq_def by fastforce
      thus "ref_lvup q txi >= (1, txi)" using True
        unfolding ref_lvup_def msgq_def by fastforce
    next
      case False
      hence "k_mod.maxForce msgq > 2"
        using `msgq xi = Content ss` `x ss = 0 & forc ss = 2` Max_ge[of _ 2] finite_UNIV
        unfolding k_mod.maxForce_def by (smt (z3) finite_imageI image_eqI k_mod.forceMsgs.simps(1) le_neq_implies_less rangeI)
      thus "ref_lvup q txi >= (1, txi)" 
        unfolding ref_lvup_def msgq_def by (metis Suc_1 less_diff_conv less_eq_prod_simp plus_1_eq_Suc)
    qed
  qed

  define len where "len = txi2-txi+k"
  have "ALL i. rho (txi+i) xi ~= Asleep" using ss nonAsleepAgain2[of txi xi] by (metis proc_state.simps(3))
  hence "active_path xi xi txi (txi2 - txi)"
    using loop exI[of "%s. _ & _ & (ALL j < txi2 - txi. _ & s j : _ (s (Suc j)))" "%_. xi"]
    unfolding active_path_def by auto

  moreover obtain seq4 where seq4:"seq4 0 = xi & seq4 k = p & (ALL i < k. seq4 i : HO (txi2 + Suc i) (seq4 (Suc i)))"
    using star unfolding k_mod.path_def by presburger
  hence "xi : HO (Suc txi2) (seq4 1)" using k2 by auto
  hence "ALL i < k. rho (txi2+i) (seq4 (Suc i)) ~= Asleep & seq4 i : HO (txi2 + Suc i) (seq4 (Suc i))"
    using assms(1) nonAsleepAgain2 by (metis txi_props2(1) proc_state.simps(3) seq4)
  hence "active_path xi p txi2 k" using exI[of _ seq4] seq4 unfolding active_path_def by auto

  ultimately have "active_path xi p txi len" 
    using merge_path[of xi xi txi "txi2 - txi" p k] txi_props2(2) unfolding len_def by auto


  then obtain seq where seq:"seq 0 = xi & seq len = p & (ALL i < len. rho (txi+i) (seq (Suc i)) ~= Asleep & seq i : HO (txi + Suc i) (seq (Suc i)))"
    unfolding active_path_def by presburger
  define ref_p where "ref_p = ref_lvup p (txi2+k-1)"
  define seq2 where "seq2 = (%i. seq (Suc i))"
  hence "ALL i < len-1. rho (Suc txi+i) (seq2 (Suc i)) ~= Asleep & seq2 i : HO (Suc txi + Suc i) (seq2 (Suc i))"
    using seq k2 less_diff_conv unfolding seq2_def by auto
  hence "seq2 0 = seq 1 & seq2 (len-1) = p & (ALL i < len-1. rho (Suc txi+i) (seq2 (Suc i)) ~= Asleep & seq2 i : HO (Suc txi + Suc i) (seq2 (Suc i)))"
    using assms(1) nonAsleepAgain2 unfolding seq2_def
    by (metis One_nat_def Suc_diff_1 add_gr_0 dual_order.strict_trans k2 len_def less_2_cases_iff seq)
  hence "active_path (seq 1) p (Suc txi) (len-1)" using exI[of _ seq2] unfolding active_path_def by auto
  moreover have "rho txi (seq 1) ~= Asleep & xi : HO (Suc txi) (seq 1)"
    using k2 seq by (metis add.commute add.right_neutral add_gr_0 dual_order.strict_trans len_def less_2_cases_iff plus_1_eq_Suc)
  hence "ref_lvup (seq 1) txi >= (1, txi)" and "rho txi (seq 1) ~= Asleep" using inc_link seq by auto
  ultimately have "(1, txi) <= ref_p" 
    using growing_path[of "seq 1" p txi "len-1"] txi_props2(2) k2 unfolding len_def ref_p_def by fastforce

  obtain ssp where ssp:"rho (txi2+k-1) p = Active ssp"
    using nonAsleepAgain2[of txi2 p "k-1"] k2 txi_props2(1) 
    by (metis Nat.add_diff_assoc Suc_diff_1 dual_order.strict_trans le_add1 plus_1_eq_Suc zero_less_numeral)
  then obtain q where "levup (fst ref_p) (snd ref_p) q"
    using in_L[of "txi2+k-1" p] unfolding L_def ref_p_def by auto
  then obtain sq ssq where "rho (snd ref_p) q = Active sq" and "level sq = fst ref_p" and "rho (snd ref_p - 1) q = Active ssq" and "level ssq = fst ref_p - 1"
    using `(1, txi) <= ref_p` unfolding levup_def by (metis fst_conv less_one not_le prod_less_def)

  moreover have ref_p_1:"fst ref_p = 1 --> txi <= snd ref_p" using `(1, txi) <= ref_p` by (metis fst_conv less_eq_prod_def nat_less_le snd_conv)
  have "fst ref_p >= 2 --> txi > snd ref_p --> ref_p : early_lvup"  
    using sss `level sss = 0` level_growing[of "snd ref_p" xi _ "txi - 1 - snd ref_p" sss] `levup (fst ref_p) (snd ref_p) q` unfolding early_lvup_def L_def by auto
  hence "txi <= snd ref_p"  
    using ref_p_1 no_early_fire[of "fst ref_p"] by (metis Suc_1 `(1, txi) <= ref_p` fst_conv less_eq_prod_def not_le not_less_eq prod.collapse snd_conv)


  ultimately have "(snd ref_p - txi) mod k = 0"
    using A4[of "txi-1" "snd ref_p - txi" q ssq sq sss ss] sss ss `level sss = 0` `level ss > 0` `(1, txi) <= ref_p`
    by (smt (z3) Nat.add_diff_assoc2 Suc_n_not_le_n Suc_pred' add_Suc_shift add_diff_inverse_nat gr_implies_not0 less_eq_prod_simp less_one nat_less_le not_le prod.collapse txi_init)

  define msgp where "msgp = HOrcvdMsgs (k_mod.gen_HOMachine k) p (HO (txi2+k) p) (rho (txi2+k-1))" 
  have "k_mod.gen_nextState k p ssp msgp sp"
    using ssp assms k2 transition[of "txi2+k-1" p ssp sp] unfolding txi2_def msgp_def by auto
  hence "x sp mod k = Suc (k_mod.minMsgs msgp) mod k"
    unfolding k_mod.gen_nextState_def k_mod.goto_level1_def k_mod.goto_level2_def
    by (smt (z3) One_nat_def Suc_1 Suc_diff_1 Suc_lessD k2 mod_Suc mod_less)
  moreover have "k_mod.minMsgs msgp = txi2 + k - 1 - snd ref_p"
    using k2 minMsgs_inf[of "txi2+k-1" p] ssp unfolding ref_p_def ref_lvup_def msgp_def txi_props(2) 
    by (metis Suc_diff_1 add.commute add_gr_0 assms(2) diff_diff_cancel plus_1_eq_Suc proc_state.simps(3) snd_conv)
  ultimately have "x sp mod k = Suc (txi2 + k - 1 - snd ref_p) mod k"
    using k2 minMsgs_inf[of "txi2+k-1" p] ssp unfolding ref_p_def ref_lvup_def msgp_def by presburger
  hence "x sp mod k = (txi2 + k - (snd ref_p - txi) - txi) mod k"
    using `snd ref_p >= txi` txi_props(2) assms(2)
    by (metis (no_types, lifting) Nat.add_diff_assoc Suc_diff_1 add_gr_0 diff_diff_left
    le_add_diff_inverse2 plus_1_eq_Suc ref_inf_t ref_p_def ssp)
  hence "x sp mod k = (txi2 + k - txi) mod k"
    using `(snd ref_p - txi) mod k = 0` 
    by (smt (z3) One_nat_def Suc_diff_Suc Suc_eq_plus1 `txi <= snd ref_p`
    `x sp mod k = Suc (txi2 + k - 1 - snd ref_p) mod k` add.commute diff_diff_cancel diff_le_self
    diff_zero k2 le_add1 le_trans mod_sub ordered_cancel_comm_monoid_diff_class.add_diff_assoc ref_inf_t ref_p_def ssp)
  thus "x sp mod k = 0" using txi_props2 by (metis Nat.add_diff_assoc2 mod_add_self2)
qed

theorem liveness:
assumes "ALL p. rho t p ~= Asleep"
shows "k_mod.liveness rho (t + 6 * N * k)"
proof -
  define tt where "tt = (LEAST t. ALL p. rho t p ~= Asleep)"
  have smax:"ALL p. rho tt p ~= Asleep" using LeastI_ex assms unfolding tt_def by (smt (verit, del_insts))
  have "ALL p sp. rho (txi2 + k) p = Active sp --> x sp mod k = 0"
    using xi_lev1_monovalent txi_props2(5) by auto
  moreover have "ALL p. rho (txi2+k-1) p ~= Asleep"
    using txi_props2(1) nonAsleepAgain2[of txi2 _ "k-1"] k2
    by (metis Nat.add_diff_assoc2 Suc_1 Suc_lessD add.commute less_or_eq_imp_le proc_state.simps(3))
  moreover have "ALL p. EX s. rho (txi2 + k + 2 * k) p = Active s"
    using nonAsleepAgain2[of tt _ "txi2+k+2*k-tt"] smax txi_props2(1)
    Least_le[of "%t. ALL p. rho t p ~= Asleep" txi2] unfolding tt_def by auto
  ultimately have lev2:"ALL p. EX sp. rho (txi2 + k + 2 * k) p = Active sp & level sp = 2"
    using monovalent_termine[of "txi2+k"] k2 by blast
  show "k_mod.liveness rho (t + 6 * N * k)" 
  proof (cases t)
    case (Suc tt)
    hence "txi2 + k + 2 * k <= t + (2 * N - 1) * (3 * k) + k + 2 * k"
      using assms txi_props(5)[of t] by fastforce
    hence "txi2 + k + 2 * k <= t + (2 * N - 1 + 1) * (3 * k)" by simp
    moreover have "2 * N >= 1" using not_less_eq_eq by fastforce
    ultimately have "txi2 + k + 2 * k <= t + (2 * N) * (3 * k)" by simp
    hence txi2:"txi2 + k + 2 * k <= t + 6 * N * k" by simp
    have "ALL p. EX sp. rho (t + 6 * N * k) p = Active sp & level sp = 2"
    proof
      fix p
      obtain sp where "rho (txi2+k+2*k) p = Active sp" using lev2 by auto
      hence "EX sp. rho (t + 6 * N * k) p = Active sp & level sp >= 2"
        using level_growing[of "txi2+k+2*k" p sp "t+6*N*k-(txi2+k+2*k)"]
        by (metis txi2 assms le_add_diff_inverse lev2 nonAsleepAgain2 proc_state.inject)
      thus "EX sp. rho (t + 6 * N * k) p = Active sp & level sp = 2"
        using A2_bis[of "t+6*N*k" p sp] by (meson A2_bis le_antisym)
    qed
    thus "k_mod.liveness rho (t + 6 * N * k)" unfolding k_mod.liveness_def by auto
  next
    case 0
    hence "ALL p sp. rho k p = Active sp --> x sp mod k = 0"
      using nonAsleepAgain2[of 0 _ k] assms monovalent_stable[of 0 0 k]
      by (metis A2 add.left_neutral diff_0_eq_0 diff_is_0_eq k2 mod_self neq0_conv not_le)
    moreover have act:"ALL tt p. rho tt p ~= Asleep"
      using nonAsleepAgain2[of 0] assms 0 by (metis add.left_neutral proc_state.simps(3))
    hence "ALL p sp. rho (k+2*k) p = Active sp --> level sp = 2" using monovalent_termine[of k] k2 calculation by blast
    moreover have "2 * N >= 1" using not_less_eq_eq by fastforce
    hence "t+6*N*k >= k+2*k" using 0
      by (smt (verit, ccfv_threshold) One_nat_def Suc_1 add_cancel_right_left le_add1 le_trans mult.commute mult_Suc
      mult_le_cancel2 mult_le_mono1 mult_numeral_1_right numeral_3_eq_3 numeral_Bit0 numerals(1) one_le_mult_iff plus_1_eq_Suc)
    moreover have "ALL p. rho (k+2*k) p ~= Asleep"
      using nonAsleepAgain2[of 0 _ "k+2*k"] assms 0 by (metis add.left_neutral proc_state.simps(3))
    have "ALL p sp. rho (t+6*N*k) p = Active sp --> level sp = 2"
    proof
      fix p
      obtain sp where "rho (k+2*k) p = Active sp" using act by (cases "rho (k+2*k) p") auto
      hence "ALL sp. rho (t+6*N*k) p = Active sp --> level sp >= 2"
        using level_growing[of "k+2*k" _ _ "t+6*N*k-(k+2*k)"]
        by (metis calculation(2) calculation(3) le_add_diff_inverse)
      thus "ALL sp. rho (t+6*N*k) p = Active sp --> level sp = 2"
        using A2_bis[of "t+6*N*k" p] by auto
    qed
    thus "k_mod.liveness rho (t + 6 * N * k)" using act unfolding k_mod.liveness_def by (meson nonAsleepAgain2)
  qed
qed



end