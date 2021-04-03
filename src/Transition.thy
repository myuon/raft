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

definition ExReq where
  "ExReq resp P \<equiv> Ex (\<lambda>req. P req \<and> respond_to resp req)"

definition majority where
  "majority n t \<equiv> 2 * t > n"

inductive transition :: "server_state list \<times> message set \<Rightarrow> server_state list \<times> message set \<Rightarrow> bool" (infix "\<rightarrow>" 50) where
(* Assumption: all RequestVote messages to followers are sent at once. Is it appropriate to assume this? *)
TR_start_election: 
  "\<lbrakk> \<sigma>' = update target ((\<sigma> ! target) \<lparr>
    currentTerm := increment_election_term (currentTerm (\<sigma> ! target)),
    votedFor := Some (node target)
   \<rparr>) \<sigma>
   ; (index, term) = get_last_log_info (log (\<sigma>' ! target))
   ; target < length \<sigma>
   ; messages = {message (node target) (node i) (request_vote (node target) index term) (currentTerm (\<sigma>' ! target)) | i. i \<in> {0..length \<sigma> - 1} \<and> i \<noteq> target}
   \<rbrakk>
  \<Longrightarrow> transition (\<sigma>, ms) (\<sigma>', ms \<union> messages)"
| TR_request_vote_resp:
  "\<lbrakk> resp = message (node m) (node r) (request_vote_response vg) t
  ; ExReq resp (\<lambda>req. \<exists>candidateId lastLogIndex lastLogTerm. payload req = request_vote candidateId lastLogIndex lastLogTerm 
    \<and> req \<in> ms
    \<and> vg = (if sender_term req < currentTerm (\<sigma> ! r) then False
            else (votedFor (\<sigma> ! r) = None \<or> votedFor (\<sigma> ! r) = Some candidateId) \<and> log_up_to_date (log (\<sigma> ! r)) lastLogIndex lastLogTerm)
    \<and> (votedFor (\<sigma> ! m) = Some s \<or> votedFor (\<sigma> ! m) = None)) 
  ; \<sigma>' = update m ((\<sigma> ! m) \<lparr> votedFor := Some s \<rparr>) \<sigma>
  ; m < length \<sigma>
  \<rbrakk>
  \<Longrightarrow> transition (\<sigma>, ms) (\<sigma>', ms \<union> {resp})"
| TR_promote_to_leader:
  "\<lbrakk> \<sigma>' = update target ((\<sigma> ! target) \<lparr> state := leader \<rparr>) \<sigma>
  ; majority (length \<sigma>) (card {s. \<exists>m \<in> ms. m = message s (node target) (request_vote_response True) (currentTerm (\<sigma> ! target))})
  ; target < length \<sigma>
  \<rbrakk>
  \<Longrightarrow> transition (\<sigma>, ms) (\<sigma>', ms)"
| TR_append_entry:
  "\<lbrakk> m = message (node s) r (append_entry (node s) (log_index (length (log (\<sigma> ! s)) - 1)) (log (\<sigma> ! s))) (currentTerm (\<sigma> ! s))
  ; state (\<sigma> ! s) = leader
  ; s < length \<sigma>
  \<rbrakk> \<Longrightarrow> transition (\<sigma>, ms) (\<sigma>, ms \<union> {m})"
(* 
   This algorithm for AppendEntry is different from the original paper;
   leader is supposed to send all logs in the state for the simplicity (no need to calculate diffs for merging and leader retries)
 *)
| TR_append_entry_resp:
  "\<lbrakk> resp = message (node s) (node r) (append_entry_response success) t
  ; ExReq resp (\<lambda>req. \<exists>leadersLog. payload req = append_entry _ _ leadersLog
    \<and> req \<in> ms
    \<and> success = (if sender_term req < currentTerm (\<sigma> ! r) then False
                 else if \<not> log_up_to_date (log (\<sigma> ! r)) prevLogIndex prevLogTerm then False
                 else True))
  ; \<sigma>' = update s ((\<sigma> ! s) \<lparr> log := leadersLog \<rparr>) \<sigma>
  ; s < length \<sigma>
  \<rbrakk>
  \<Longrightarrow> transition (\<sigma>, ms) (\<sigma>', ms \<union> {resp})"

lemma transition_message_monotonicity: "(\<sigma>, m) \<rightarrow> (\<sigma>', m') \<Longrightarrow> m \<subseteq> m'"
proof-
  assume hyp: "transition (\<sigma>,m) (\<sigma>',m')"

  have "(\<lambda>(_, m). \<lambda>(_, m'). m \<subseteq> m') (\<sigma>,m) (\<sigma>', m')"
    apply (induct rule: transition.induct [OF hyp])
    apply auto
    done
  thus "m \<subseteq> m'"
    by simp
qed

definition transitions (infix "\<rightarrow>*" 50) where
  "transitions \<equiv> rtranclp transition"

lemma transitions_one: "a \<rightarrow> b \<Longrightarrow> a \<rightarrow>* b"
  by (simp add: transitions_def)

lemma transisions_trans [trans]: "a \<rightarrow>* b \<Longrightarrow> b \<rightarrow>* c \<Longrightarrow> a \<rightarrow>* c"
  using transitions_def
  by (metis rtranclp_trans)

end
