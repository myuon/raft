theory Definitions
  imports Main
begin

primrec repeat :: "'a \<Rightarrow> nat \<Rightarrow> 'a list" where
  "repeat a 0 = []"
| "repeat a (Suc n) = a # repeat a n"

lemma repeat_nth: "i < n \<Longrightarrow> repeat a n ! i = a"
  apply (induct n arbitrary: i)
  apply simp
  apply simp
  using less_Suc_eq_0_disj by fastforce

lemma repeat_length: "length (repeat a n) = n"
  apply (induct n)
  apply simp
  apply simp
  done

fun update :: "nat \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "update 0 x (y # ys) = x # ys"
| "update (Suc n) x (y # ys) = y # update n x ys"
| "update _ _ _ = undefined"

lemma update_nth_updated: "length xs > i \<Longrightarrow> update i a xs ! i = a"
  apply (induct xs arbitrary: i)
  apply simp
  apply simp
  using less_Suc_eq_0_disj by fastforce

lemma update_nth_nonupdated: "\<lbrakk> length xs > i; length xs > j; i \<noteq> j \<rbrakk> \<Longrightarrow> update i a xs ! j = xs ! j"
  apply (induct xs arbitrary: i j)
  apply simp
proof-
  fix aa xs i j
  assume "(\<And>i j. i < length xs \<Longrightarrow> j < length xs \<Longrightarrow> i \<noteq> j \<Longrightarrow> update i a xs ! j = xs ! j)" "i < length (aa # xs)" "j < length (aa # xs)" "i \<noteq> j"

  show "update i a (aa # xs) ! j = (aa # xs) ! j"
    apply (cases i)
    apply simp
    using \<open>i \<noteq> j\<close> apply force
    apply simp
    apply (cases j)
    apply simp
    using \<open>\<And>j i. \<lbrakk>i < length xs; j < length xs; i \<noteq> j\<rbrakk> \<Longrightarrow> update i a xs ! j = xs ! j\<close> \<open>i < length (aa # xs)\<close> \<open>i \<noteq> j\<close> \<open>j < length (aa # xs)\<close> by auto
qed

lemma update_length [simp]: "i < length xs \<Longrightarrow> length (update i a xs) = length xs"
  apply (induct xs arbitrary: i)
  apply simp_all
proof-
  fix aa xs i
  assume "(\<And>i. i < length xs \<Longrightarrow> length (update i a xs) = length xs)" "i < Suc (length xs)"

  show "length (update i a (aa # xs)) = Suc (length xs)"
    apply (cases i)
    apply simp_all
    using \<open>\<And>i. i < length xs \<Longrightarrow> length (update i a xs) = length xs\<close> \<open>i < Suc (length xs)\<close> by auto
qed

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
