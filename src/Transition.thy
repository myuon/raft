theory Transition
  imports Main
begin

datatype election_term = election_term (election_term_of: nat)

instantiation election_term :: ord
begin

definition
  "i < j \<longleftrightarrow> election_term_of i < election_term_of j"

instance ..

end

typedecl entry
datatype log_index = log_index (log_index_of: nat)

datatype node = node (node_of: nat)

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

type_synonym log = "(entry \<times> election_term) list"

definition log_up_to_date where
  "log_up_to_date log index trm \<equiv> length log \<ge> (log_index_of index) \<and> snd (log ! (log_index_of index)) = trm"

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
  nextIndex :: "nat list"
  matchIndex :: "nat list"

definition ExReq where
  "ExReq resp P \<equiv> Ex (\<lambda>req. P req \<and> respond_to req resp)"

inductive transition :: "server_state list \<times> message set \<Rightarrow> server_state list \<times> message set \<Rightarrow> bool" where
TR_request_vote_resp:
  "\<lbrakk> resp = message s (node r) (request_vote_response vg) t
  ; ExReq resp (\<lambda>req. \<exists>candidateId lastLogIndex lastLogTerm. payload req = request_vote candidateId lastLogIndex lastLogTerm 
    \<and> req \<in> ms
    \<and> vg = (if election_term req < currentTerm (\<sigma> ! r) then False
            else (votedFor (\<sigma> ! r) = None \<or> votedFor (\<sigma> ! r) = Some candidateId) \<and> log_up_to_date (log (\<sigma> ! r)) lastLogIndex lastLogTerm)) \<rbrakk>
  \<Longrightarrow> transition (\<sigma>, ms) (\<sigma>', ms \<union> {resp})"

end
