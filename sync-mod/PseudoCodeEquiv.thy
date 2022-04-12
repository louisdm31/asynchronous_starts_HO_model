theory PseudoCodeEquiv
imports "../HOModel" GenSynchMod
begin

definition nextState :: "nat => locState => (Proc => locState message) => locState" where
"nextState k s msgs == 
    let synch_a = (ALL p. msgs p ~= Void --> (EX m. msgs p = Content m & conc m & x m mod k = x s mod k)) in
    let ready_a = (ALL p m. msgs p = Content m --> ready m) in
    let force_a = (Max (k_mod.forceMsgs ` range msgs)) in
    let x_a = Suc (LEAST v. EX m p. msgs p = Content m & forc m = force_a & x m = v) in
    if x_a mod k = 0 then
        if level s = 0 & synch_a then
            if force_a <= 2 then
                (| x = 0, conc = True, ready = True, forc = 2, level = 1 |)
            else
                (| x = x_a, conc = True, ready = True, forc = force_a, level = 1 |)
        else
            if level s = 1 & synch_a & ready_a then
                (| x = 0, conc = True, ready = True, forc = 3, level = 2 |)
            else
                (| x = x_a, conc = True, ready = level s > 0, forc = force_a, level = level s |)
    else
        (| x = x_a, conc = synch_a, ready = ready_a, forc = force_a, level = level s |)"

lemma minMsgs_eq:
assumes "msgs p = Content s"
shows "(ALL p :: Proc. msgs p ~= Void --> (EX m. msgs p = Content m & conc m & x m mod k = x s mod k)) = k_mod.isSynch k msgs"
proof 
    assume asm:"ALL p. msgs p ~= Void --> (EX m. msgs p = Content m & conc m & x m mod k = x s mod k)"
    show "k_mod.isSynch k msgs" unfolding k_mod.isSynch_def
    proof (rule allI impI)+
        fix p
        assume "msgs p ~= Void"
        from this obtain m where "msgs p = Content m" and "conc m" and "x m mod k = x s mod k" using asm by auto
        moreover from this obtain q sq where "msgs q = Content sq" and "forc sq = k_mod.maxForce msgs"
            using Max_in[of "k_mod.forceMsgs ` range msgs"] finite_UNIV unfolding k_mod.maxForce_def
            by (smt (verit, ccfv_SIG) Max_ge asm empty_iff finite finite_imageI imageE imageI k_mod.forceMsgs.simps(1)
            k_mod.forceMsgs.simps(3) k_mod.maxForce_def le_neq_implies_less less_nat_zero_code neq0_conv rangeI)
        from this obtain qq sqq where "msgs qq = Content sqq" and "forc sqq = k_mod.maxForce msgs" and "x sqq = k_mod.minMsgs msgs"
            using LeastI_ex unfolding k_mod.minMsgs_def by (smt (verit, del_insts))
        hence "k_mod.minMsgs msgs mod k = x s mod k" using asm by (metis message.inject message.simps(5))
        ultimately show "EX m. msgs p = Content m & conc m & x m mod k = k_mod.minMsgs msgs mod k" by auto
    qed
next
    assume asm:"k_mod.isSynch k msgs"
    show "ALL p. msgs p ~= Void --> (EX m. msgs p = Content m & conc m & x m mod k = x s mod k)"
    proof (rule allI impI)+
        fix p
        assume "msgs p ~= Void"
        from this obtain m where "msgs p = Content m" and "conc m" and "x m mod k = k_mod.minMsgs msgs mod k"
            using asm unfolding k_mod.isSynch_def by auto
        moreover have "x s mod k = k_mod.minMsgs msgs mod k" using asm assms unfolding k_mod.isSynch_def by (metis message.inject message.simps(5))
        ultimately show "EX m. msgs p = Content m & conc m & x m mod k = x s mod k" by auto
    qed
qed


lemma equiv_pseudocode:
assumes "msgs p = Content s"
and k2:"k > 2"
and "k_mod.maxForce msgs <= 3"
shows "k_mod.gen_nextState k p s msgs (nextState k s msgs)"
proof -
    have nxt:"nextState k s msgs = 
        (let synch_a = k_mod.isSynch k msgs in
        let ready_a = k_mod.isReady msgs in
        let force_a = k_mod.maxForce msgs in
        let x_a = Suc (k_mod.minMsgs msgs) in
        if x_a mod k = 0 then
            if level s = 0 & synch_a then
                if force_a <= 2 then
                    (| x = 0, conc = True, ready = True, forc = 2, level = 1 |)
                else
                    (| x = x_a, conc = True, ready = True, forc = force_a, level = 1 |)
            else
                if level s = 1 & synch_a & ready_a then
                    (| x = 0, conc = True, ready = True, forc = 3, level = 2 |)
                else
                    (| x = x_a, conc = True, ready = level s > 0, forc = force_a, level = level s |)
        else
            (| x = x_a, conc = synch_a, ready = ready_a, forc = force_a, level = level s |))"
        using minMsgs_eq[of msgs p s k] assms
        unfolding k_mod.minMsgs_def k_mod.maxForce_def k_mod.isReady_def nextState_def
        by presburger
    thus ?thesis
    proof (cases "k_mod.goto_level1 k msgs s | k_mod.goto_level2 k msgs s")
        case goto:True
        hence mod0:"Suc (k_mod.minMsgs msgs) mod k = 0" using k2
            unfolding k_mod.goto_level1_def k_mod.goto_level2_def by (metis Suc_diff_1 dual_order.strict_trans less_2_cases_iff mod_Suc)
        thus ?thesis 
        proof (cases "level s = 0 & k_mod.maxForce msgs > 2")
            case True
            hence "nextState k s msgs = (| x = Suc (k_mod.minMsgs msgs), conc = True, ready = True, forc = k_mod.maxForce msgs, level = 1 |)"
                using nxt mod0 goto 
                unfolding k_mod.goto_level1_def k_mod.goto_level2_def by auto
            thus ?thesis unfolding k_mod.gen_nextState_def by (smt (z3) Suc_1 True diff_Suc_1 k_mod.goto_level1_def less_Suc_eq_0_disj
                less_numeral_extra(1) less_numeral_extra(3) locState.select_convs(1) locState.select_convs(2)
                locState.select_convs(3) locState.select_convs(4) locState.select_convs(5) mod_Suc nxt)
        next
            case False
            hence "nextState k s msgs = (| x = 0, conc = True, ready = True, forc = Suc (Suc (level s)), level = Suc (level s) |)"
                using nxt mod0 goto 
                unfolding k_mod.goto_level1_def k_mod.goto_level2_def by auto
            moreover have "k_mod.maxForce msgs <= Suc (if k_mod.goto_level1 k msgs s then 1 else 2)"
                using goto False assms(3)
                unfolding k_mod.goto_level1_def k_mod.goto_level2_def by fastforce
            ultimately show ?thesis unfolding k_mod.gen_nextState_def
                using goto False
                by (smt (z3) One_nat_def Suc_1 k_mod.goto_level1_def k_mod.goto_level2_def less_2_cases_iff
                less_le locState.select_convs(1) locState.select_convs(2) locState.select_convs(3) locState.select_convs(4)
                locState.select_convs(5) not_le zero_less_one)
        qed
    next
        case False
        moreover from this have "nextState k s msgs = (let x_a = Suc (k_mod.minMsgs msgs) in
             (| x = x_a, conc = x_a mod k = 0 | k_mod.isSynch k msgs,
            ready = if x_a mod k = 0 then level s > 0 else k_mod.isReady msgs, forc = k_mod.maxForce msgs, level = level s |))"
            using nxt unfolding k_mod.goto_level1_def k_mod.goto_level2_def
            by (smt (z3) One_nat_def diff_Suc_1 diff_is_0_eq' mod_Suc one_neq_zero zero_le_one)
        ultimately show ?thesis unfolding k_mod.gen_nextState_def by simp
    qed
qed