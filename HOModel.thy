theory HOModel
imports Main
begin

declare if_split_asm [split] 

section "Heard-Of Algorithms"

subsection "The Consensus Problem"

text \<open>
  We are interested in the verification of fault-tolerant distributed algorithms.
  The Consensus problem is paradigmatic in this area. Stated
  informally, it assumes that all processes participating in the algorithm
  initially propose some value, and that they may at some point decide some value.
  It is required that every process eventually decides, and that all processes
  must decide the same value.

  More formally, we represent runs of algorithms as `\<omega>`-sequences of
  configurations (vectors of process states). Hence, a run is modeled as
  a function of type `nat => 'proc => 'pst` where type variables 
  `'proc` and `'pst` represent types of processes and process
  states, respectively.
\<close>

datatype 'msg message = Content "'msg" | Bot | Void
datatype 'pst proc_state = Active "'pst" | Asleep

fun the_state where
  "the_state (Active s) = s"
| "the_state Asleep = undefined"

text \<open>Predicate that holds if process @{text p} always sleeps in run @{text rho}.\<close>
definition always_asleep where
  "always_asleep rho p == ALL n. rho n p = Asleep"

text \<open>Round in which a process that is not always asleep wakes up.\<close>
definition first_awake where
  "first_awake rho p == LEAST n. rho n p ~= Asleep"

definition get_init_state :: "(nat => 'proc => 'pst proc_state) => 'proc => 'pst proc_state" where
  "get_init_state rho p == 
    if always_asleep rho p then Asleep 
    else rho (first_awake rho p) p"
(* rho (Max ({n + 1 | n. rho n p = Asleep } \<union> {0})) p" *)

text \<open>
  The Consensus property is expressed with respect
  to a collection `val` of initially proposed values (one per process) 
  and an observer function `dec::'pst => val option` that retrieves the decision
  (if any) from a process state. The Consensus problem is stated as the conjunction
  of the following properties:
  \begin{description}
  \item[Integrity.] Processes can only decide initially proposed values.
  \item[Agreement.] Whenever processes `p` and `q` decide,
    their decision values must be the same. (In particular, process `p`
    may never change the value it decides, which is referred to as Irrevocability.)
  \item[Termination.] Every process decides eventually.
  \end{description}

  The above properties are sometimes only required of non-faulty processes, since
  nothing can be required of a faulty process.
  The Heard-Of model does not attribute faults to processes, and therefore the
  above formulation is appropriate in this framework.
\<close>
definition
  consensus :: "('proc => 'val) => ('pst => 'val option) => (nat => 'proc => 'pst proc_state) => bool"
where
  "consensus vals dec rho ==
     (ALL n p v s. rho n p = Active s --> dec s = Some v --> v : range vals)
   & (ALL m n p q v w sp sq. rho m p = Active sp --> dec sp = Some v 
         --> rho n q = Active sq --> dec sq = Some w --> v = w)
   & (ALL p. ~always_asleep rho p --> (EX n s. rho n p = Active s & dec s ~= None))"

text \<open>
  A variant of the Consensus problem replaces the Integrity requirement by
  \begin{description}
  \item[Validity.] If all processes initially propose the same value `v`
    then every process may only decide `v`.
  \end{description}
\<close>

definition weak_consensus where
  "weak_consensus vals dec rho ==
     (ALL v. (ALL p. vals p = v) --> (ALL n p w s. rho n p = Active s --> dec s = Some w --> w = v))
   & (ALL m n p q v w sp sq. rho m p = Active sp --> dec sp = Some v 
         --> rho n q = Active sq --> dec sq = Some w --> v = w)
   & (ALL p. ~always_asleep rho p --> (EX n s. rho n p = Active s & dec s ~= None))"

text \<open>
  Clearly, `consensus` implies `weak_consensus`.
\<close>

lemma consensus_then_weak_consensus:
  assumes "consensus vals dec rho"
  shows "weak_consensus vals dec rho" 
  using assms unfolding consensus_def weak_consensus_def
  by (smt rangeE)

text \<open>
  Over Boolean values (``binary Consensus''), `weak_consensus`
  implies `consensus`, hence the two problems are equivalent.
  In fact, this theorem holds more generally whenever at most two
  different values are proposed initially (i.e., `card (range vals) \<le> 2`).
\<close>

lemma binary_weak_consensus_then_consensus:
  assumes bc: "weak_consensus (vals::'proc => bool) dec rho"
  shows "consensus vals dec rho"
proof -
  text \<open>Show the Integrity property, the other conjuncts are the same.\<close>
  {
    fix n p v s
    assume act: "rho n p = Active s" and dec: "dec s = Some v"
    have "v : range vals"
    proof (cases "EX b. ALL p. vals p = b")
      case True with bc act dec show ?thesis
        unfolding weak_consensus_def by (smt range_eqI)
    next
      case False
      text \<open>In this case both possible values occur in @{text "vals"}, and the result is trivial.\<close>
      thus ?thesis by (auto simp: image_def)
    qed
  }
  with bc show ?thesis
    unfolding consensus_def weak_consensus_def by meson
qed

text \<open>
  The algorithms that we are going to verify solve the Consensus or weak Consensus
  problem, under different hypotheses about the kinds and number of faults.
\<close>


subsection "A Generic Representation of Heard-Of Algorithms"

text \<open>
  Charron-Bost and Schiper~\cite{charron:heardof} introduce
  the Heard-Of (HO) model for representing fault-tolerant
  distributed algorithms. In this model, algorithms execute in communication-closed
  rounds: at any round~$r$, processes only receive messages that were sent for
  that round. For every process~$p$ and round~$r$, the ``heard-of set'' $HO(p,r)$
  denotes the set of processes from which~$p$ receives a message in round~$r$.
  Since every process is assumed to send a message to all processes in each round,
  the complement of $HO(p,r)$ represents the set of faults that may affect~$p$ in
  round~$r$ (messages that were not received, e.g. because the sender crashed,
  because of a network problem etc.).

  The HO model expresses hypotheses on the faults tolerated by an algorithm
  through ``communication predicates'' that constrain the sets $HO(p,r)$
  that may occur during an execution. Charron-Bost and Schiper show that
  standard fault models can be represented in this form.

  The original HO model is sufficient for representing algorithms
  tolerating benign failures such as process crashes or message loss. A later
  extension for algorithms tolerating Byzantine (or value) failures~\cite{biely:tolerating} 
  adds a second collection of sets $SHO(p,r) \subseteq HO(p,r)$ that contain those
  processes $q$ from which process $p$ receives the message that $q$ was indeed
  supposed to send for round $r$ according to the algorithm. In other words, 
  messages from processes in $HO(p,r) \setminus SHO(p,r)$ were corrupted, be it
  due to errors during message transmission or because of the sender was faulty or
  lied deliberately. For both benign and Byzantine errors, the HO model registers
  the fault but does not try to identify the faulty component (i.e., designate the
  sending or receiving process, or the communication channel as the ``culprit'').

  Executions of HO algorithms are defined with respect to collections
  $HO(p,r)$ and $SHO(p,r)$. However, the code of a process does not have
  access to these sets. In particular, process $p$ has no way of determining
  if a message it received from another process $q$ corresponds to what $q$
  should have sent or if it has been corrupted.

  Certain algorithms rely on the assignment of ``coordinator'' processes for
  each round. Just as the collections $HO(p,r)$, the definitions assume an
  external coordinator assignment such that $coord(p,r)$ denotes the coordinator
  of process $p$ and round $r$. Again, the correctness of algorithms may depend
  on hypotheses about coordinator assignments -- e.g., it may be assumed that
  processes agree sufficiently often on who the current coordinator is.

  The following definitions provide a generic representation of HO and SHO algorithms
  in Isabelle/HOL. A (coordinated) HO algorithm is described by the following parameters:
  \begin{itemize}
  \item a finite type `'proc` of processes,
  \item a type `'pst` of local process states,
  \item a type `'msg` of messages sent in the course of the algorithm,
  \item a predicate `CinitState` such that `CinitState p st crd` is
    true precisely of the initial states `st` of process `p`, assuming
    that `crd` is the initial coordinator of `p`,
  \item a function `sendMsg` where `sendMsg r p q st` yields
    the message that process `p` sends to process `q` at round
    `r`, given its local state `st`, and
  \item a predicate `CnextState` where `CnextState r p st msgs crd st'`
    characterizes the successor states `st'` of process `p` at round
    `r`, given current state `st`, the vector
    `msgs :: 'proc => 'msg option` of messages that `p` received at
    round `r` (`msgs q = None` indicates that no message has been
    received from process `q`),
    and process `crd` as the coordinator for the following round.
  \end{itemize}
  Note that every process can store the coordinator for the current round in its
  local state, and it is therefore not necessary to make the coordinator a parameter
  of the message sending function `sendMsg`.

  We represent an algorithm by a record as follows.
\<close>


record ('proc, 'pst, 'msg) CHOAlgorithm =
  CinitState ::  "'proc => 'pst => 'proc => bool"
  sendMsg ::   "'proc => 'proc => 'pst => 'msg"
  CnextState :: "'proc => 'pst => ('proc => 'msg message) => 'proc => 'pst => bool"

text \<open>
  For non-coordinated HO algorithms, the coordinator argument of functions
  `CinitState` and `CnextState` is irrelevant, and we
  define utility functions that trivialize that argument.
\<close>

definition isNCAlgorithm where
  "isNCAlgorithm alg ==
     (ALL p st crd crd'. CinitState alg p st crd = CinitState alg p st crd')
   & (ALL p st msgs crd crd' st'. CnextState alg p st msgs crd st'
                               = CnextState alg p st msgs crd' st')"

definition initState where
  "initState alg p st == CinitState alg p st undefined"

definition nextState where
  "nextState alg p st msgs st' == CnextState alg p st msgs undefined st'"

text \<open>
  A \emph{heard-of assignment} associates a set of processes with each
  process. The following type is used to represent the collections $HO(p,r)$
  and $SHO(p,r)$ for fixed round $r$.
%
  Similarly, a \emph{coordinator assignment} associates a process (its coordinator)
  to each process.
\<close>

type_synonym
  'proc HO = "'proc => 'proc set"

type_synonym
  'proc coord = "'proc => 'proc"

text \<open>
  An execution of an HO algorithm is defined with respect to HO and SHO
  assignments that indicate, for every round `r` and every process `p`,
  from which sender processes `p` receives messages (resp., uncorrupted
  messages) at round `r`.

%% That's the intention, but we don't enforce this in the definitions.
%  Obviously, SHO sets are always included in HO sets, for the same process and round.

  The following definitions formalize this idea. We define ``coarse-grained''
  executions whose unit of atomicity is the round of execution. At each round,
  the entire collection of processes performs a transition according to the
  `CnextState` function of the algorithm. Consequently, a system state is
  simply described by a configuration, i.e. a function assigning a process state
  to every process. This definition of executions may appear surprising for an
  asynchronous distributed system, but it simplifies system verification,
  compared to a ``fine-grained'' execution model that records individual events
  such as message sending and reception or local transitions. We will justify
  later why the ``coarse-grained'' model is sufficient for verifying interesting
  correctness properties of HO algorithms.

  The predicate `CSHOinitConfig` describes the possible initial configurations
  for algorithm `A` (remember that a configuration is a function that assigns
  local states to every process).
\<close>

text \<open>
  Given the current configuration `cfg` and the HO and SHO sets `HOp`
  and `SHOp` for process `p` at round `r`, the function
  `SHOmsgVectors` computes the set of possible vectors of messages that
  process `p` may receive. For processes `q \<notin> HOp`, `p` 
  receives no message (represented as value `None`). For processes
  `q : SHOp`, `p` receives the message that `q` computed
  according to the `sendMsg` function of the algorithm. For the remaining
  processes `q : HOp - SHOp`, `p` may receive some arbitrary value.
\<close>

text \<open>
  Predicate `CSHOnextConfig` uses the preceding function and the algorithm's
  `CnextState` function to characterize the possible successor configurations
  in a coarse-grained step, and predicate `CSHORun` defines (coarse-grained)
  executions `rho` of an HO algorithm.
\<close>

fun HOrcvMsgs_q :: "'proc => ('proc, 'pst, 'msg) CHOAlgorithm  => 'proc =>
                         'pst proc_state => 'msg message" where
  "HOrcvMsgs_q q A p (Active s) = Content (sendMsg A q p s)"
| "HOrcvMsgs_q q A p Asleep = Bot"

definition HOrcvdMsgs :: "('proc, 'pst, 'msg) CHOAlgorithm => 'proc =>
                          'proc set => ('proc => 'pst proc_state)
                          => 'proc => 'msg message" where
  "HOrcvdMsgs A p HO cfg ==
   %q. if q : HO then HOrcvMsgs_q q A p (cfg q) else Void"

definition CHOnextConfig where
  "CHOnextConfig A cfg HO coord cfg' ==
   ALL p s.       cfg  p = Active s -->
         (EX s'. cfg' p = Active s' & CnextState A p s (HOrcvdMsgs A p (HO p) cfg) (coord p) s')"

definition CHOinitConfig where
  "CHOinitConfig A rho coord ==
   ALL p. (always_asleep rho p) |
       (let k = first_awake rho p
        in  CinitState A p (the_state (rho k p)) (coord k p))"
(*  ALL p (n::nat) s. (n > 0 --> rho (n-1) p = Asleep) --> rho n p = Active s --> CinitState A p s (coord n p)" *)


definition CHORun where
  "CHORun A rho HOs coords == 
     CHOinitConfig A rho coords
  & (ALL p n. p : HOs n p)
  & (ALL r. CHOnextConfig A (rho r) (HOs (Suc r)) (coords (Suc r)) (rho (Suc r)))"

lemma nonAsleepAgain : 
  assumes "rho n p ~= Asleep" and "CHORun A rho HO coord"
  shows "EX s. rho (n+(m::nat)) p = Active s"
proof (induction m)
  case 0
  show ?case using assms by (cases "rho n p") auto
next
  case (Suc x)
  hence "EX s. rho (n + x) p = Active s" by (cases "rho (n+x) p") auto
  thus "EX s. rho (n + Suc x) p = Active s" 
    using assms CHORun_def CHORun_def CHOnextConfig_def by (metis add_Suc_right)
qed

lemma first_awake:
  assumes run: "CHORun A rho HO coord" 
    and prev: "0 < n --> rho (n-1) p = Asleep" 
    and act: "rho n p = Active s"
  shows "first_awake rho p = n"
  unfolding first_awake_def
proof  (rule Least_equality)
  from act show "rho n p ~= Asleep" by simp
next
  fix m
  assume m: "rho m p ~= Asleep"
  show "n \<le> m"
  proof (rule ccontr)
    assume "~(n \<le> m)"
    hence "m < n" by simp
    then obtain k where k: "n-1 = m+k"
      by (metis Suc_eq_plus1_left add_diff_cancel_left' less_imp_Suc_add) 
    with m run have "EX s'. rho (n-1) p = Active s'" by (auto dest: nonAsleepAgain)
    with `m < n` prev show "False" by simp
  qed
qed

text \<open>
  For non-coordinated algorithms. the `coord` arguments of the above functions
  are irrelevant. We define similar functions that omit that argument, and relate
  them to the above utility functions for these algorithms.
\<close>
definition HOinitConfig where
  "HOinitConfig A cfg == CHOinitConfig A cfg (%_ _. undefined)"

lemma HOinitConfig_eq:
  "HOinitConfig A rho =
   (ALL p. always_asleep rho p |
        initState A p (the_state (rho (first_awake rho p) p)))"
  by (auto simp: HOinitConfig_def CHOinitConfig_def initState_def Let_def)
   
(*
lemma HOinitConfig_eq:
  "HOinitConfig A rho = (ALL p (n::nat) s. (n > 0 --> rho (n-1) p = Asleep) -->
                                        rho n p = Active s --> initState A p s)"
  by (auto simp: HOinitConfig_def CHOinitConfig_def initState_def)
*)

definition HOnextConfig where
  "HOnextConfig A cfg HO cfg' ==
   CHOnextConfig A cfg HO (%_. undefined) cfg'"

definition HORun :: "('proc, 'pst, 'msg) CHOAlgorithm =>
                      (nat => 'proc => 'pst proc_state) => (nat => 'proc => 'proc set) => bool" where
  "HORun A rho HOs ==
   CHORun A rho HOs (%_ _. undefined)"

lemma HORun_eq:
  "HORun A rho HOs =
   (HOinitConfig A rho 
    & (ALL p n. p : HOs n p)
    & (ALL r. HOnextConfig A (rho r) (HOs (Suc r)) (rho (Suc r))))"
  by (auto simp: HORun_def CHORun_def HOinitConfig_def HOnextConfig_def)

lemma first_awake_HO:
  assumes run: "HORun A rho HO" 
    and prev: "0 < n --> rho (n-1) p = Asleep" 
    and act: "rho n p = Active s"
  shows "first_awake rho p = n"
  using assms unfolding HORun_def by (rule first_awake)

(*
text `
  The following derived proof rules are immediate consequences of
  the definition of `CHORun`; they simplify automatic reasoning.
`

lemma CHORun_0:
  assumes "CHORun A rho HOs coords" 
      and "\<And>cfg. CHOinitConfig A cfg (coords 0) ==> P cfg"
  shows "P (rho 0)"
using assms unfolding CHORun_eq by blast

lemma CHORun_Suc:
  assumes "CHORun A rho HOs coords"
  and "\<And>r. CHOnextConfig A r (rho r) (HOs r) (coords (Suc r)) (rho (Suc r))
            ==> P r"
  shows "P n"
using assms unfolding CHORun_eq by blast

lemma CHORun_induct:
  assumes run: "CHORun A rho HOs coords"
  and init: "CHOinitConfig A (rho 0) (coords 0) ==> P 0"
  and step: "\<And>r. \<lbrakk> P r; CHOnextConfig A r (rho r) (HOs r) (coords (Suc r)) 
                                      (rho (Suc r)) \<rbrakk> ==> P (Suc r)"
  shows "P n"
using run unfolding CHORun_eq by (induct n, auto elim: init step)
*)

text \<open>
  Because algorithms will not operate for arbitrary HO, SHO, and coordinator
  assignments, these are constrained by a \emph{communication predicate}.
  For convenience, we split this predicate into a \emph{per Round} part that
  is expected to hold at every round and a \emph{global} part that must hold
  of the sequence of (S)HO assignments and may thus express liveness assumptions.

  In the parlance of~\cite{charron:heardof}, a \emph{HO machine} is an HO algorithm
  augmented with a communication predicate. We therefore define (C)(S)HO machines as
  the corresponding extensions of the record defining an HO algorithm.
\<close>

definition Schedule :: "(nat => 'proc => 'pst proc_state) => nat => 'proc set" where
  "Schedule rho n == {p. rho n p ~= Asleep}"

record ('proc, 'pst, 'msg) HOMachine = "('proc, 'pst, 'msg) CHOAlgorithm" +
  HOcommPerRd :: "'proc HO => bool"
  HOcommGlobal :: "(nat => 'proc HO) => bool"
  HOcommSchedule :: "(nat => 'proc set) => bool"

(* should probably also add a "Schedule" predicate here *)
record ('proc, 'pst, 'msg) CHOMachine = "('proc, 'pst, 'msg) CHOAlgorithm" +
  CHOcommPerRd :: "nat => 'proc HO => 'proc coord => bool"
  CHOcommGlobal::"(nat => 'proc HO) => (nat => 'proc coord) => bool"


end 
