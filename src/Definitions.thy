theory Definitions
  imports Main
begin

primrec repeat :: "'a \<Rightarrow> nat \<Rightarrow> 'a list" where
  "repeat a 0 = []"
| "repeat a (Suc n) = a # repeat a n"


datatype election_term = election_term (election_term_of: nat)

instantiation election_term :: ord
begin

definition
  "i < j \<longleftrightarrow> election_term_of i < election_term_of j"

instance ..

end

datatype node = node (node_of: nat)

end
