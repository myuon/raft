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
  "ExReq resp P \<equiv> Ex (\<lambda>req. P req \<and> respond_to req resp)"

inductive transition :: "server_state list \<times> message set \<Rightarrow> server_state list \<times> message set \<Rightarrow> bool" where
TR_request_vote_resp:
  "\<lbrakk> resp = message s (node r) (request_vote_response vg) t
  ; ExReq resp (\<lambda>req. \<exists>candidateId lastLogIndex lastLogTerm. payload req = request_vote candidateId lastLogIndex lastLogTerm 
    \<and> req \<in> ms
    \<and> vg = (if sender_term req < currentTerm (\<sigma> ! r) then False
            else (votedFor (\<sigma> ! r) = None \<or> votedFor (\<sigma> ! r) = Some candidateId) \<and> log_up_to_date (log (\<sigma> ! r)) lastLogIndex lastLogTerm)
    \<and> \<sigma>' ! r = (\<sigma> ! m) \<lparr> votedFor := Some s \<rparr>) \<rbrakk>
  \<Longrightarrow> transition (\<sigma>, ms) (\<sigma>', ms \<union> {resp})"
(* 
   This algorithm for AppendEntry is different from the original paper;
   leader is supposed to send all logs in the state for the simplicity (no need to calculate diffs for merging and leader retries)
 *)
| TR_append_entry_resp:
  "\<lbrakk> resp = message s (node r) (append_entry_response success) t
  ; ExReq resp (\<lambda>req. \<exists>leadersLog. payload req = append_entry _ _ leadersLog
    \<and> req \<in> ms
    \<and> success = (if sender_term req < currentTerm (\<sigma> ! r) then False
                 else if \<not> log_up_to_date (log (\<sigma> ! r)) prevLogIndex prevLogTerm then False
                 else True)
    \<and> \<sigma>' ! r = (\<sigma> ! m) \<lparr> log := leadersLog \<rparr>) \<rbrakk>
  \<Longrightarrow> transition (\<sigma>, ms) (\<sigma>', ms \<union> {resp})"

end
