theory Definitions
  imports Main
begin

primrec repeat :: "'a \<Rightarrow> nat \<Rightarrow> 'a list" where
  "repeat a 0 = []"
| "repeat a (Suc n) = a # repeat a n"

fun update :: "nat \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "update 0 x (y # ys) = x # ys"
| "update (Suc n) x (y # ys) = y # update n x ys"
| "update _ _ _ = undefined"

datatype election_term = election_term (election_term_of: nat)

instantiation election_term :: ord
begin

definition
  "i < j \<longleftrightarrow> election_term_of i < election_term_of j"

instance ..

end

fun increment_election_term where
  "increment_election_term t = election_term (election_term_of t + 1)"

datatype node = node (node_of: nat)

end
