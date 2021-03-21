theory Log
  imports Main "./Definitions"
begin

typedecl entry
datatype log_index = log_index (log_index_of: nat)

type_synonym log = "(entry \<times> election_term) list"

definition log_up_to_date where
  "log_up_to_date log index trm \<equiv> length log \<ge> (log_index_of index) \<and> snd (log ! (log_index_of index)) = trm"

end
