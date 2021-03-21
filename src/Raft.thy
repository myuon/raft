theory Raft
  imports Main
begin

typedecl entry
datatype election_term = election_term nat

datatype node = node nat

datatype message_payload
  = AppendEntry
  | RequestVote
  | AppendEntryResponse
  | RequestVoteResponse bool

primrec is_response where
  "is_response AppendEntry = False"
| "is_response RequestVote = False"
| "is_response AppendEntryResponse = True"
| "is_response (RequestVoteResponse _) = True"

fun is_request where
  "is_request r = (\<not> is_response r)"

datatype message
  = message (sender: node) (receiver: node) (payload: message_payload) (election_term: election_term)

fun payload_respond_to where
  "payload_respond_to AppendEntryResponse AppendEntry = True"
| "payload_respond_to (RequestVoteResponse _) RequestVote = True"
| "payload_respond_to _ _ = False"

definition respond_to where
  "respond_to resp req \<equiv>
    (is_response (payload resp)
    \<and> is_request (payload req)
    \<and> sender req = receiver resp
    \<and> sender resp = receiver req
    \<and> payload_respond_to (payload resp) (payload req)
    \<and> election_term resp = election_term req)"

datatype NodeState = Follower | Candidate | Leader

record server_state =
  state :: NodeState

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

locale raft =
  (* We assume this message list is topologically sorted.
     The indices for messages and states represents "time" (which is NOT election_term here).
   *)
  fixes messages :: "message list"
    and states :: "server_state list list"

  (* If we have a response, then we must have the corresponding request. *)
  assumes rpc_way: "\<lbrakk> messages ! i = resp; is_response (payload resp) \<rbrakk> \<Longrightarrow> Ex (\<lambda>j. j < i \<and> respond_to (messages ! j) (messages ! i))"
end
