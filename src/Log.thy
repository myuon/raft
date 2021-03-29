theory Log
  imports Main "./Definitions"
begin

typedecl entry
datatype log_index = log_index (log_index_of: nat)

type_synonym log = "(entry \<times> election_term) list"

definition log_up_to_date where
  "log_up_to_date log index trm \<equiv> length log \<ge> (log_index_of index) \<and> (log_index_of index > 0 \<longrightarrow> snd (log ! (log_index_of index)) = trm)"

fun get_last_log_info :: "log \<Rightarrow> log_index \<times> election_term" where
  "get_last_log_info log = (case log of [] \<Rightarrow> (log_index 0, election_term 0) | _ \<Rightarrow> let (i,_,t) = last (enumerate 1 log) in (log_index i,t))"

end
