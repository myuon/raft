theory Definitions
  imports Main
begin

datatype election_term = election_term (election_term_of: nat)

instantiation election_term :: ord
begin

definition
  "i < j \<longleftrightarrow> election_term_of i < election_term_of j"

instance ..

end

datatype node = node (node_of: nat)

end
