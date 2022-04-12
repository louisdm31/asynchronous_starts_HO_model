theory GenSynchMod
imports "../HOModel"
begin

typedecl Proc
axiomatization where Proc_finite: "OFCLASS(Proc, finite_class)"
instance Proc :: finite by (rule Proc_finite)

abbreviation "N == card (UNIV :: Proc set)"

record locState = 
     x :: nat
     conc :: bool
     ready :: bool
     forc :: nat
     level :: nat
    
locale k_mod = fixes k :: nat
begin

definition gen_initState where
"gen_initState = (| x = 0, conc = False, ready = False, forc = 1, level = 0 |)"

fun forceMsgs where
  "forceMsgs (Content m) = forc m"
| "forceMsgs _ = 0"

definition maxForce where
"maxForce msgs == Max (forceMsgs ` (range msgs))"

definition isReady where
"isReady msgs == ALL p m. msgs p = Content m --> ready m"

definition minMsgs where
"minMsgs msgs == LEAST v. EX m p. msgs p = Content m & forc m = maxForce msgs & x m = v"

definition isSynch where
"isSynch msgs == ALL p. msgs p ~= Void --> (EX m. msgs p = Content m & conc m & x m mod k = minMsgs msgs mod k)"

definition goto_level1 where
"goto_level1 msgs s == isSynch msgs & minMsgs msgs mod k = k - 1 & level s = 0"

definition goto_level2 where
"goto_level2 msgs s == isSynch msgs & isReady msgs
    & minMsgs msgs mod k = k - 1 & level s = 1"

definition gen_nextState :: "Proc => locState => (Proc => locState message) => locState => bool" where
"gen_nextState p s msgs ss ==
    if goto_level1 msgs s | goto_level2 msgs s then
        conc ss &
        ready ss = (level ss > 0) &
        level ss = (if goto_level1 msgs s then 1 else 2) &
        (if maxForce msgs > Suc (level ss) then
            x ss = Suc (minMsgs msgs) &
            forc ss = maxForce msgs
        else
            x ss = 0 &
            forc ss = Suc (level ss))
    else
        x ss = Suc (minMsgs msgs) &
        forc ss = maxForce msgs &
        level s = level ss & (
        if x ss mod k = 0 then
            conc ss &
            ready ss = (level ss > 0)
        else
            conc ss = isSynch msgs &
            ready ss = isReady msgs)"

definition gen_sendMsg where
"gen_sendMsg p q st == st"

definition gen_commPerRd where
"gen_commPerRd HO == True"

(*existence of a path from xi to any node, between any round interval [t+1, t+k]*)
definition path where 
"path HO p q t D == EX seq. seq 0 = p & seq D = q &
    (ALL i < D. seq i : HO (t+Suc i) (seq (Suc i)))"

definition gen_commGlobal where
"gen_commGlobal HO == EX xi. ALL p n. path HO xi p n (k div 2)"

definition gen_commSchedule where
"gen_commSchedule sched == EX n. sched n = UNIV"

definition gen_HOMachine where
"gen_HOMachine == (|
    CinitState = (%_ st _. gen_initState = st),
    sendMsg = gen_sendMsg,
    CnextState = (%p st msgs _. gen_nextState p st msgs)
|)"

definition liveness where
"liveness rho == ALL p. EX t s. rho t p = Active s & level s = 2"

definition safety where
"safety rho == EX c. ALL p rf s ss. rho rf p = Active s -->
                (level s < 2) --> rho (Suc rf) p = Active ss --> level ss = 2 --> rf mod k = c"

 text ‹
 \DefineSnippet{modksynch}{
    @{thm [display] safety}
    @{thm [display] (concl) liveness}
 }%EndSnippet
 ›
end
end
