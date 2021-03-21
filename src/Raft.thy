theory Raft
  imports Main "./Transition"
begin

locale raft =
  (* The history of states and messages *)
  fixes all_states :: "server_state list list"
    and all_messages :: "message set list"

  (* Transition for raft algorithm *)
  assumes transition: "\<lbrakk> \<sigma> = all_states ! i; \<sigma>' = all_states ! (i + 1); m = all_messages ! i; m' = all_messages ! (i + 1) \<rbrakk> \<Longrightarrow> transition (\<sigma>,m) (\<sigma>',m')"
end
