theory Raft
  imports Main
begin

datatype election_term = election_term nat

instantiation election_term :: ord
begin

definition
  "i < j \<longleftrightarrow> (case (i,j) of (election_term x, election_term y) \<Rightarrow> x < y)"

instance ..

end

typedecl entry
datatype log_index = log_index nat

datatype node = node nat

datatype message_payload
  = append_entry
  | request_vote
    (* candidateid *) node
    (* lastLogIndex *) log_index
    (* lastLogTerm *) election_term
  | append_entry_response
  | request_vote_response
    (* voteGranted *) bool

primrec is_response where
  "is_response append_entry = False"
| "is_response (request_vote _ _ _) = False"
| "is_response append_entry_response = True"
| "is_response (request_vote_response _) = True"

fun is_request where
  "is_request r = (\<not> is_response r)"

datatype message
  = message (sender: node) (receiver: node) (payload: message_payload) (election_term: election_term)

fun payload_respond_to where
  "payload_respond_to append_entry_response append_entry = True"
| "payload_respond_to (request_vote_response _) (request_vote _ _ _) = True"
| "payload_respond_to _ _ = False"

definition respond_to where
  "respond_to resp req \<equiv>
    (is_response (payload resp)
    \<and> is_request (payload req)
    \<and> sender req = receiver resp
    \<and> sender resp = receiver req
    \<and> payload_respond_to (payload resp) (payload req)
    \<and> election_term resp = election_term req)"

datatype node_state = follower | candidate | leader

record server_state =
  state :: node_state

  (* Persistent state *)
  currentTerm :: election_term
  votedFor :: "node option"
  log :: "entry list"
  
  (* Volatile state *)
  commitIndex :: nat
  lastApplied :: nat

  (* Volatile state on leaders *)
  nextIndex :: "nat list"
  matchIndex :: "nat list"

definition ExReq where
  "ExReq resp P \<equiv> Ex (\<lambda>req. P req \<and> respond_to req resp)"

inductive transition :: "server_state list \<times> message set \<Rightarrow> server_state list \<times> message set \<Rightarrow> bool" where
TR_request_vote_resp: "\<lbrakk> resp = message s (node r) (request_vote_response vg) t; ExReq resp (\<lambda>req. req \<in> ms \<and> vg = (election_term req < currentTerm (\<sigma> ! r))) \<rbrakk> \<Longrightarrow> transition (\<sigma>, ms) (\<sigma>', ms \<union> {resp})"

locale raft =
  (* The history of states and messages *)
  fixes all_states :: "server_state list list"
    and all_messages :: "message set list"

  (* Transition for raft algorithm *)
  assumes transition: "\<lbrakk> \<sigma> = all_states ! i; \<sigma>' = all_states ! (i + 1); m = all_messages ! i; m' = all_messages ! (i + 1) \<rbrakk> \<Longrightarrow> transition (\<sigma>,m) (\<sigma>',m')"
end
