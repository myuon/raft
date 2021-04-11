theory Transition
  imports Main "./Definitions" "./Log"
begin

datatype message_payload
  = append_entry
    (* leaderId *) node
    (* leaderCommit *) log_index
    (* leaderLog *) log
  | request_vote
    (* candidateid *) node
    (* lastLogIndex *) log_index
    (* lastLogTerm *) election_term
  | append_entry_response
    (* success *) bool
  | request_vote_response
    (* voteGranted *) bool

primrec is_response where
  "is_response (append_entry _ _ _) = False"
| "is_response (request_vote _ _ _) = False"
| "is_response (append_entry_response _) = True"
| "is_response (request_vote_response _) = True"

fun is_request where
  "is_request r = (\<not> is_response r)"

datatype message
  = message (sender: node) (receiver: node) (payload: message_payload) (sender_term: election_term)

fun payload_respond_to where
  "payload_respond_to (append_entry_response _) (append_entry _ _ _) = True"
| "payload_respond_to (request_vote_response _) (request_vote _ _ _) = True"
| "payload_respond_to _ _ = False"

definition respond_to where
  "respond_to resp req \<equiv>
    (is_response (payload resp)
    \<and> is_request (payload req)
    \<and> sender req = receiver resp
    \<and> sender resp = receiver req
    \<and> payload_respond_to (payload resp) (payload req)
    \<and> sender_term resp = sender_term req)"

datatype node_state = follower | candidate | leader

record server_state =
  state :: node_state

  (* Persistent state *)
  currentTerm :: election_term
  votedFor :: "node option"
  log :: log
  
  (* Volatile state *)
  commitIndex :: nat
  lastApplied :: nat

  (* Volatile state on leaders *)
  nextIndex :: "log_index list"
  matchIndex :: "log_index list"

definition initial_server_state where
  "initial_server_state n = \<lparr>
    state = follower,
    currentTerm = election_term 0,
    votedFor = None,
    log = [],
    commitIndex = 0,
    lastApplied = 0,
    nextIndex = repeat (log_index 0) n,
    matchIndex = repeat (log_index 0) n
  \<rparr>"

definition ExReqProps where
  "ExReqProps resp P req \<equiv> P req \<and> respond_to resp req"

definition ExReq where
  "ExReq resp P \<equiv> Ex (ExReqProps resp P)"

definition majority where
  "majority n t \<equiv> 2 * card t > n"

lemma majority_pigeonhole: "\<lbrakk> finite u; card u = n; x \<subseteq> u; y \<subseteq> u; majority n x; majority n y \<rbrakk> \<Longrightarrow> x \<inter> y \<noteq> {}"
proof-
  assume "finite u" "card u = n" "x \<subseteq> u" "y \<subseteq> u" "majority n x" "majority n y"

  have "2 * card x > n"
    using \<open>majority n x\<close> majority_def by blast
  moreover have "2 * card y > n"
    using \<open>majority n y\<close> majority_def by auto
  ultimately have "card x + card y > n"
    by simp

  { assume "x \<inter> y = {}"
    have "card (x \<union> y) = card x + card y"
      by (meson \<open>finite u\<close> \<open>x \<inter> y = {}\<close> \<open>x \<subseteq> u\<close> \<open>y \<subseteq> u\<close> card_Un_disjoint finite_subset)
    also have "\<dots> > n"
      by (simp add: \<open>n < card x + card y\<close>)
    finally have "card (x \<union> y) > n"
      by simp

    have "x \<union> y \<subseteq> u"
      by (simp add: \<open>x \<subseteq> u\<close> \<open>y \<subseteq> u\<close>)

    have False
      by (metis \<open>card u = n\<close> \<open>finite u\<close> \<open>n < card (x \<union> y)\<close> \<open>x \<union> y \<subseteq> u\<close> card_mono not_le)
  }
  thus "x \<inter> y \<noteq> {}"
    by auto
qed

(* Assumption: all RequestVote messages to followers are sent at once. Is it appropriate to assume this? *)
definition TR_condition_start_election where
  "TR_condition_start_election \<sigma> \<sigma>' ms ms' target \<equiv>
     let (index, term) = get_last_log_info (log (\<sigma>' ! target)) in
     target < length \<sigma>
     \<and> \<sigma>' = update target ((\<sigma> ! target) \<lparr>
       currentTerm := increment_election_term (currentTerm (\<sigma> ! target)),
       votedFor := Some (node target)
     \<rparr>) \<sigma>
     \<and> ms' = ms \<union> {message (node target) (node i) (request_vote (node target) index term) (currentTerm (\<sigma>' ! target)) | i. i \<in> {0..length \<sigma> - 1} \<and> i \<noteq> target}"

definition TR_condition_request_vote_resp where
  "TR_condition_request_vote_resp \<sigma> \<sigma>' ms ms' m r s t vg \<equiv>
     let resp = message (node m) (node r) (request_vote_response vg) t in
     (ExReq resp (\<lambda>req. \<exists>candidateId lastLogIndex lastLogTerm. payload req = request_vote candidateId lastLogIndex lastLogTerm
       \<and> req \<in> ms
       \<and> vg = (if sender_term req < currentTerm (\<sigma> ! r) then False
               else (votedFor (\<sigma> ! r) = None \<or> votedFor (\<sigma> ! r) = Some candidateId) \<and> log_up_to_date (log (\<sigma> ! r)) lastLogIndex lastLogTerm)
       \<and> (votedFor (\<sigma> ! m) = Some s \<or> votedFor (\<sigma> ! m) = None)))
     \<and> m < length \<sigma>
     \<and> r < length \<sigma>
     \<and> \<sigma>' = update m ((\<sigma> ! m) \<lparr> votedFor := Some s \<rparr>) \<sigma>
     \<and> ms' = ms \<union> {resp}"

definition TR_condition_promote_to_leader where
  "TR_condition_promote_to_leader \<sigma> \<sigma>' ms ms' target \<equiv>
    majority (length \<sigma>) {s. \<exists>m \<in> ms. m = message s (node target) (request_vote_response True) (currentTerm (\<sigma> ! target))}
    \<and> target < length \<sigma>
    \<and> \<sigma>' = update target ((\<sigma> ! target) \<lparr> state := leader \<rparr>) \<sigma>
    \<and> ms' = ms"

definition TR_condition_append_entry where
  "TR_condition_append_entry \<sigma> \<sigma>' ms ms' s r \<equiv>
    let m = message (node s) (node r) (append_entry (node s) (log_index (length (log (\<sigma> ! s)) - 1)) (log (\<sigma> ! s))) (currentTerm (\<sigma> ! s)) in
    state (\<sigma> ! s) = leader
    \<and> s < length \<sigma>
    \<and> r < length \<sigma>
    \<and> \<sigma>' = \<sigma>
    \<and> ms' = ms \<union> {m}"

(* 
   This algorithm for AppendEntry is different from the original paper;
   leader is supposed to send all logs in the state for the simplicity (no need to calculate diffs for merging and leader retries)
 *)
definition TR_condition_append_entry_resp where
  "TR_condition_append_entry_resp \<sigma> \<sigma>' ms ms' leadersLog prevLogTerm prevLogIndex t success r s \<equiv>
    let resp = message (node s) (node r) (append_entry_response success) t in
    ExReq resp (\<lambda>req. \<exists>leaderId leaderCommit. payload req = append_entry leaderId leaderCommit leadersLog
      \<and> req \<in> ms
      \<and> success = (if sender_term req < currentTerm (\<sigma> ! r) then False
                 else if \<not> log_up_to_date (log (\<sigma> ! r)) prevLogIndex prevLogTerm then False
                 else True))
    \<and> s < length \<sigma>
    \<and> r < length \<sigma>
    \<and> \<sigma>' = update s ((\<sigma> ! s) \<lparr> log := leadersLog \<rparr>) \<sigma>
    \<and> ms' = ms \<union> {resp}"

inductive transition :: "server_state list \<times> message set \<Rightarrow> server_state list \<times> message set \<Rightarrow> bool" (infix "\<rightarrow>" 50) where
TR_start_election: "TR_condition_start_election \<sigma> \<sigma>' ms ms' target \<Longrightarrow> transition (\<sigma>, ms) (\<sigma>', ms')"
| TR_request_vote_resp: "TR_condition_request_vote_resp \<sigma> \<sigma>' ms ms' m r s t vg \<Longrightarrow> transition (\<sigma>, ms) (\<sigma>', ms')"
| TR_promote_to_leader: "TR_condition_promote_to_leader \<sigma> \<sigma>' ms ms' target \<Longrightarrow> transition (\<sigma>, ms) (\<sigma>', ms')"
| TR_append_entry: "TR_condition_append_entry \<sigma> \<sigma>' ms ms' s r \<Longrightarrow> transition (\<sigma>, ms) (\<sigma>', ms')"
| TR_append_entry_resp: "TR_condition_append_entry_resp \<sigma> \<sigma>' ms ms' leadersLog prevLogTerm prevLogIndex t success r s \<Longrightarrow> transition (\<sigma>, ms) (\<sigma>', ms')"

lemma leader_promote_inversion_for_transition:
  "\<lbrakk> i < length \<sigma>; transition (\<sigma>, ms) (\<sigma>', ms'); state (\<sigma> ! i) \<noteq> leader; state (\<sigma>' ! i) = leader \<rbrakk> \<Longrightarrow> majority (length \<sigma>) {s. \<exists>m \<in> ms. m = message s (node i) (request_vote_response True) (currentTerm (\<sigma> ! i))}"
  apply (cases rule: transition.cases)
  apply simp_all
proof-
  fix \<sigma>'' \<sigma>''' msa ms'a target
  show "i < length \<sigma> \<Longrightarrow>
       (\<sigma>, ms) \<rightarrow> (\<sigma>', ms') \<Longrightarrow>
       state (\<sigma> ! i) \<noteq> leader \<Longrightarrow>
       state (\<sigma>' ! i) = leader \<Longrightarrow>
       (\<sigma>, ms) = (\<sigma>'', msa) \<Longrightarrow>
       (\<sigma>', ms') = (\<sigma>''', ms'a) \<Longrightarrow>
       TR_condition_start_election \<sigma>'' \<sigma>''' msa ms'a target \<Longrightarrow>
       majority (length \<sigma>) {s. message s (node i) (request_vote_response True) (currentTerm (\<sigma> ! i)) \<in> ms}"
    apply (simp add: TR_condition_start_election_def)
    apply (cases "\<sigma>'' ! target")
    apply simp
    by (metis select_convs(1) update_nth_nonupdated update_nth_updated)
next
  fix \<sigma>'' \<sigma>''' msa ms'a m r s t vg
  show "i < length \<sigma> \<Longrightarrow>
       (\<sigma>, ms) \<rightarrow> (\<sigma>', ms') \<Longrightarrow>
       state (\<sigma> ! i) \<noteq> leader \<Longrightarrow>
       state (\<sigma>' ! i) = leader \<Longrightarrow>
       (\<sigma>, ms) = (\<sigma>'', msa) \<Longrightarrow>
       (\<sigma>', ms') = (\<sigma>''', ms'a) \<Longrightarrow>
       TR_condition_request_vote_resp \<sigma>'' \<sigma>''' msa ms'a m r s t vg \<Longrightarrow>
       majority (length \<sigma>) {s. message s (node i) (request_vote_response True) (currentTerm (\<sigma> ! i)) \<in> ms}"
    apply (simp add: TR_condition_request_vote_resp_def)
    apply (cases "\<sigma>'' ! m")
    apply simp
    by (metis select_convs(1) update_nth_nonupdated update_nth_updated)
next
  fix \<sigma>'' \<sigma>''' msa ms'a target
  show "i < length \<sigma> \<Longrightarrow>
       (\<sigma>, ms) \<rightarrow> (\<sigma>', ms') \<Longrightarrow>
       state (\<sigma> ! i) \<noteq> leader \<Longrightarrow>
       state (\<sigma>' ! i) = leader \<Longrightarrow>
       (\<sigma>, ms) = (\<sigma>'', msa) \<Longrightarrow>
       (\<sigma>', ms') = (\<sigma>''', ms'a) \<Longrightarrow>
       TR_condition_promote_to_leader \<sigma>'' \<sigma>''' msa ms'a target \<Longrightarrow>
       majority (length \<sigma>) {s. message s (node i) (request_vote_response True) (currentTerm (\<sigma> ! i)) \<in> ms}"
    apply (simp add: TR_condition_promote_to_leader_def)
    apply (cases "\<sigma>'' ! target")
    apply simp
    by (metis select_convs(2) update_nth_nonupdated)
next
  fix \<sigma>'' \<sigma>''' msa ms'a s r
  show "i < length \<sigma> \<Longrightarrow>
       (\<sigma>, ms) \<rightarrow> (\<sigma>', ms') \<Longrightarrow>
       state (\<sigma> ! i) \<noteq> leader \<Longrightarrow>
       state (\<sigma>' ! i) = leader \<Longrightarrow>
       (\<sigma>, ms) = (\<sigma>'', msa) \<Longrightarrow>
       (\<sigma>', ms') = (\<sigma>''', ms'a) \<Longrightarrow>
       TR_condition_append_entry \<sigma>'' \<sigma>''' msa ms'a s r \<Longrightarrow>
       majority (length \<sigma>) {s. message s (node i) (request_vote_response True) (currentTerm (\<sigma> ! i)) \<in> ms}"
    apply (simp add: TR_condition_append_entry_def)
    done
next
  fix \<sigma>'' \<sigma>''' msa ms'a leadersLog prevLogTerm prevLogIndex t success r s
  show "i < length \<sigma> \<Longrightarrow>
       (\<sigma>, ms) \<rightarrow> (\<sigma>', ms') \<Longrightarrow>
       state (\<sigma> ! i) \<noteq> leader \<Longrightarrow>
       state (\<sigma>' ! i) = leader \<Longrightarrow>
       (\<sigma>, ms) = (\<sigma>'', msa) \<Longrightarrow>
       (\<sigma>', ms') = (\<sigma>''', ms'a) \<Longrightarrow>
       TR_condition_append_entry_resp \<sigma>'' \<sigma>''' msa ms'a leadersLog prevLogTerm prevLogIndex t success r s \<Longrightarrow>
       majority (length \<sigma>) {s. message s (node i) (request_vote_response True) (currentTerm (\<sigma> ! i)) \<in> ms}"
    apply (simp add: TR_condition_append_entry_resp_def)
    apply (cases "\<sigma>''' ! s")
    by (metis (no_types, lifting) select_convs(1) surjective update_convs(4) update_nth_nonupdated update_nth_updated)
qed

lemma state_length_invariant_for_transition: "transition (\<sigma>, m) (\<sigma>', m') \<Longrightarrow> length \<sigma> = length \<sigma>'"
  apply (cases rule: transition.cases)
  apply simp_all
  apply (simp add: TR_condition_start_election_def)
  apply (simp add: TR_condition_request_vote_resp_def)
     apply (metis update_length)
  apply (simp add: TR_condition_promote_to_leader_def)
  apply (simp add: TR_condition_append_entry_def)
  apply (simp add: TR_condition_append_entry_resp_def)
  by (metis update_length)

lemma transition_message_monotonicity: "(\<sigma>, m) \<rightarrow> (\<sigma>', m') \<Longrightarrow> m \<subseteq> m'"
proof-
  assume hyp: "transition (\<sigma>,m) (\<sigma>',m')"

  have "(\<lambda>(_, m). \<lambda>(_, m'). m \<subseteq> m') (\<sigma>,m) (\<sigma>', m')"
    apply (induct rule: transition.induct [OF hyp])
    apply (auto simp add: TR_condition_append_entry_def TR_condition_start_election_def TR_condition_promote_to_leader_def TR_condition_append_entry_resp_def TR_condition_request_vote_resp_def)
    apply (metis insertCI)
    apply (metis insertCI)
    done
  thus "m \<subseteq> m'"
    by simp
qed

lemma transition_message_preserves_finite: "\<lbrakk> (\<sigma>,m) \<rightarrow> (\<sigma>',m'); finite m \<rbrakk> \<Longrightarrow> finite m'"
  apply (cases rule: transition.cases)
  apply simp_all
  apply (simp add: TR_condition_start_election_def)
  apply auto[1]
  apply (simp add: TR_condition_request_vote_resp_def)
  apply (metis finite_insert)
  apply (simp add: TR_condition_promote_to_leader_def)
  apply (simp add: TR_condition_append_entry_def)
  apply (simp add: TR_condition_append_entry_resp_def)
  by (metis finite_insert)

lemma transition_currentTerm_monotonicity: "\<lbrakk> i < length \<sigma>; (\<sigma>,m) \<rightarrow> (\<sigma>',m') \<rbrakk> \<Longrightarrow> currentTerm (\<sigma> ! i) \<le> currentTerm (\<sigma>' ! i)"
  apply (cases rule: transition.cases)
  apply simp_all
proof-
  fix \<sigma>'' \<sigma>''' ms ms' target
  show "i < length \<sigma> \<Longrightarrow>
       (\<sigma>, m) \<rightarrow> (\<sigma>', m') \<Longrightarrow>
       (\<sigma>, m) = (\<sigma>'', ms) \<Longrightarrow> (\<sigma>', m') = (\<sigma>''', ms') \<Longrightarrow> TR_condition_start_election \<sigma>'' \<sigma>''' ms ms' target \<Longrightarrow> currentTerm (\<sigma> ! i) \<le> currentTerm (\<sigma>' ! i)"
    apply (simp add: TR_condition_start_election_def)
    apply (cases "i = target")
    apply simp
    apply (cases "\<sigma>'' ! target")
    apply simp
    apply (simp add: increment_election_term_greater update_nth_updated)
    by (simp add: less_eq_election_term_def update_nth_nonupdated)
next
  fix \<sigma>'' \<sigma>''' ms ms' ma r s t vg
  show "i < length \<sigma> \<Longrightarrow>
       (\<sigma>, m) \<rightarrow> (\<sigma>', m') \<Longrightarrow>
       (\<sigma>, m) = (\<sigma>'', ms) \<Longrightarrow>
       (\<sigma>', m') = (\<sigma>''', ms') \<Longrightarrow> TR_condition_request_vote_resp \<sigma>'' \<sigma>''' ms ms' ma r s t vg \<Longrightarrow> currentTerm (\<sigma> ! i) \<le> currentTerm (\<sigma>' ! i)"
    apply (simp add: TR_condition_request_vote_resp_def)
    by (metis eq_iff less_eq_election_term_def select_convs(2) simps(12) surjective update_nth_nonupdated update_nth_updated)
next
  fix \<sigma>'' \<sigma>''' ms ms' target
  show "i < length \<sigma> \<Longrightarrow>
       (\<sigma>, m) \<rightarrow> (\<sigma>', m') \<Longrightarrow>
       (\<sigma>, m) = (\<sigma>'', ms) \<Longrightarrow> (\<sigma>', m') = (\<sigma>''', ms') \<Longrightarrow> TR_condition_promote_to_leader \<sigma>'' \<sigma>''' ms ms' target \<Longrightarrow> currentTerm (\<sigma> ! i) \<le> currentTerm (\<sigma>' ! i)"
    apply (simp add: TR_condition_promote_to_leader_def)
    by (metis eq_iff less_eq_election_term_def select_convs(2) surjective update_convs(1) update_nth_nonupdated update_nth_updated)
next
  fix \<sigma>'' \<sigma>''' ms ms' s r
  show "i < length \<sigma> \<Longrightarrow>
       (\<sigma>, m) \<rightarrow> (\<sigma>', m') \<Longrightarrow>
       (\<sigma>, m) = (\<sigma>'', ms) \<Longrightarrow> (\<sigma>', m') = (\<sigma>''', ms') \<Longrightarrow> TR_condition_append_entry \<sigma>'' \<sigma>''' ms ms' s r \<Longrightarrow> currentTerm (\<sigma> ! i) \<le> currentTerm (\<sigma>' ! i)"
    apply (simp add: TR_condition_append_entry_def)
    using less_eq_election_term_def by presburger
next
  fix \<sigma>'' \<sigma>''' ms ms' leadersLog prevLogTerm prevLogIndex t success r s
  show "i < length \<sigma> \<Longrightarrow>
       (\<sigma>, m) \<rightarrow> (\<sigma>', m') \<Longrightarrow>
       (\<sigma>, m) = (\<sigma>'', ms) \<Longrightarrow>
       (\<sigma>', m') = (\<sigma>''', ms') \<Longrightarrow>
       TR_condition_append_entry_resp \<sigma>'' \<sigma>''' ms ms' leadersLog prevLogTerm prevLogIndex t success r s \<Longrightarrow> currentTerm (\<sigma> ! i) \<le> currentTerm (\<sigma>' ! i)"
    apply (simp add: TR_condition_append_entry_resp_def)
    by (metis (mono_tags, lifting) eq_iff less_eq_election_term_def select_convs(2) surjective update_convs(4) update_nth_nonupdated update_nth_updated)
qed

definition transitions (infix "\<rightarrow>*" 50) where
  "transitions \<equiv> rtranclp transition"

lemma transitions_one: "a \<rightarrow> b \<Longrightarrow> a \<rightarrow>* b"
  by (simp add: transitions_def)

lemma transisions_trans [trans]: "a \<rightarrow>* b \<Longrightarrow> b \<rightarrow>* c \<Longrightarrow> a \<rightarrow>* c"
  using transitions_def
  by (metis rtranclp_trans)

end
