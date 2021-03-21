theory Raft
  imports Main "./Transition"
begin

locale raft =
  (* The history of states and messages *)
  fixes all_states :: "server_state list list"
    and all_messages :: "message set list"
    and number_of_nodes :: nat

  (* Transition for raft algorithm *)
  assumes transition: "\<lbrakk> \<sigma> = all_states ! i; \<sigma>' = all_states ! (i + 1); m = all_messages ! i; m' = all_messages ! (i + 1) \<rbrakk> \<Longrightarrow> transition (\<sigma>,m) (\<sigma>',m')"
  and initial_state: "hd all_states = repeat (initial_server_state number_of_nodes) number_of_nodes"
  and initial_message: "hd all_messages = {}"

lemma (in raft) message_monotonicity: "i \<le> j \<Longrightarrow> all_messages ! i \<subseteq> all_messages ! j"
proof-
  assume "i \<le> j"

  { fix n
    have "\<lbrakk> n = j - i; i \<le> j \<rbrakk> \<Longrightarrow> all_messages ! i \<subseteq> all_messages ! j"
      apply (induct n arbitrary: i j rule: less_induct)
    proof-
      fix x i j
      assume "(\<And>y i j. y < x \<Longrightarrow> y = j - i \<Longrightarrow> i \<le> j \<Longrightarrow> all_messages ! i \<subseteq> all_messages ! j)"
        and "x = j - i" "i \<le> j"
      show "all_messages ! i \<subseteq> all_messages ! j"
        apply (cases x)
        using \<open>i \<le> j\<close> \<open>x = j - i\<close> apply auto[1]
      proof-
        fix x'
        assume "x = Suc x'"
        have "x' = (j - 1) - i"
          by (metis \<open>x = Suc x'\<close> \<open>x = j - i\<close> diff_Suc_1 diff_commute)
        moreover have "i \<le> j - 1"
          by (metis One_nat_def \<open>i \<le> j\<close> \<open>x = Suc x'\<close> \<open>x = j - i\<close> \<open>x' = j - 1 - i\<close> diff_diff_cancel diff_is_0_eq le_cases)
        ultimately have "all_messages ! i \<subseteq> all_messages ! (j - 1)"
          using \<open>\<And>y j i. \<lbrakk>y < x; y = j - i; i \<le> j\<rbrakk> \<Longrightarrow> all_messages ! i \<subseteq> all_messages ! j\<close> \<open>x = Suc x'\<close> by blast

        have "transition (all_states ! (j - 1), all_messages ! (j - 1)) (all_states ! j, all_messages ! j)"
          by (metis One_nat_def \<open>i \<le> j - 1\<close> \<open>x = Suc x'\<close> \<open>x = j - i\<close> diff_Suc_1 diff_is_0_eq diff_zero le_add_diff_inverse2 le_cases raft.transition raft_axioms)
        hence "all_messages ! (j - 1) \<subseteq> all_messages ! j"
          by (simp add: transition_message_monotonicity)

        show ?thesis
          using \<open>all_messages ! (j - 1) \<subseteq> all_messages ! j\<close> \<open>all_messages ! i \<subseteq> all_messages ! (j - 1)\<close> by blast
      qed
    qed
  }
  hence "\<And>n. \<lbrakk> n = j - i; i < j \<rbrakk> \<Longrightarrow> all_messages ! i \<subseteq> all_messages ! j"
    by simp

  thus ?thesis
    by (simp add: \<open>\<And>n. \<lbrakk>n = j - i; i \<le> j\<rbrakk> \<Longrightarrow> all_messages ! i \<subseteq> all_messages ! j\<close> \<open>i \<le> j\<close>)
qed

end
