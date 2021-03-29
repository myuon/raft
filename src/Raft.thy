theory Raft
  imports Main "./Transition"
begin

locale raft =
  (* The history of states and messages *)
  fixes all_states :: "server_state list list"
    and all_messages :: "message set list"
    and number_of_nodes :: nat

  (* Transition for raft algorithm *)
  assumes transition: "\<lbrakk> \<sigma> = all_states ! i; \<sigma>' = all_states ! (i + 1); m = all_messages ! i; m' = all_messages ! (i + 1) \<rbrakk> \<Longrightarrow> transition number_of_nodes (\<sigma>,m) (\<sigma>',m')"
  and initial_state: "hd all_states = repeat (initial_server_state number_of_nodes) number_of_nodes"
  and initial_message: "hd all_messages = {}"

abbreviation (in raft) transition_arrow (infix "\<rightarrow>" 50) where
  "transition_arrow \<equiv> transition number_of_nodes"

definition (in raft) transitions (infix "\<rightarrow>*" 50) where
  "transitions \<equiv> rtranclp (transition number_of_nodes)"

inductive (in raft) transitions_trace where
TRT_empty: "transitions_trace (\<sigma>,m) (\<sigma>,m) [(\<sigma>,m)]"
| TRT_step: "\<lbrakk> transitions_trace (\<sigma>,m) (\<sigma>',m') ts; transition number_of_nodes (\<sigma>',m') (\<sigma>'',m'') \<rbrakk> \<Longrightarrow> transitions_trace (\<sigma>,m) (\<sigma>'',m'') ((\<sigma>'',m'')#ts)"

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

        have "transition number_of_nodes (all_states ! (j - 1), all_messages ! (j - 1)) (all_states ! j, all_messages ! j)"
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

lemma (in raft)
  assumes "number_of_nodes = 3"
  obtains \<sigma> ms where "(hd all_states, hd all_messages) \<rightarrow>* (\<sigma>, ms)" "state (\<sigma> ! 0) = leader"
proof-
  have "([initial_server_state 3, initial_server_state 3, initial_server_state 3], hd all_messages)
    \<rightarrow> ([initial_server_state 3 \<lparr>currentTerm := increment_election_term (currentTerm (hd all_states ! 0)), votedFor := Some (node 0)\<rparr>, initial_server_state 3, initial_server_state 3],
    {
      message (node 0) (node 1) (request_vote (node 0) (log_index 0) (election_term 0)) (election_term 1),
      message (node 0) (node 2) (request_vote (node 0) (log_index 0) (election_term 0)) (election_term 1)
    })"
  proof-
    have "([initial_server_state 3, initial_server_state 3, initial_server_state 3], hd all_messages) = (hd all_states, hd all_messages)"
      apply (simp add: initial_state assms)
      by (simp add: numeral_3_eq_3)
    also have "\<dots> \<rightarrow> (let \<sigma>' = update 0 ((hd all_states ! 0)\<lparr>currentTerm := increment_election_term (currentTerm (hd all_states ! 0)), votedFor := Some (node 0)\<rparr>) (hd all_states);
      messages = {message (node 0) (node i) (request_vote (node 0) (log_index 0) (election_term 0)) (currentTerm (\<sigma>' ! 0)) |i. i \<in> {0..length (hd all_states) - 1} \<and> i \<noteq> 0} in
    (\<sigma>', hd all_messages \<union> messages))"
      using TR_start_election [of _ 0 "hd all_states" _ _ _ number_of_nodes "hd all_messages"]
      by (simp add: initial_state initial_message assms repeat_nth update_nth_updated repeat_length initial_server_state_def)
    also have "\<dots> = (let \<sigma>' = update 0 ((hd all_states ! 0)\<lparr>currentTerm := increment_election_term (currentTerm (hd all_states ! 0)), votedFor := Some (node 0)\<rparr>) (hd all_states) in
    (\<sigma>', hd all_messages \<union> {
      message (node 0) (node 1) (request_vote (node 0) (log_index 0) (election_term 0)) (election_term 1),
      message (node 0) (node 2) (request_vote (node 0) (log_index 0) (election_term 0)) (election_term 1)
    }))"
      apply (simp add: initial_state initial_message assms repeat_nth update_nth_updated repeat_length initial_server_state_def)
      apply auto
      done
    also have "\<dots> = ([initial_server_state 3 \<lparr>currentTerm := increment_election_term (currentTerm (hd all_states ! 0)), votedFor := Some (node 0)\<rparr>, initial_server_state 3, initial_server_state 3], {
      message (node 0) (node 1) (request_vote (node 0) (log_index 0) (election_term 0)) (election_term 1),
      message (node 0) (node 2) (request_vote (node 0) (log_index 0) (election_term 0)) (election_term 1)
    })"
      by (simp add: initial_state initial_message assms repeat_nth numeral_3_eq_3)
    finally show ?thesis
      by simp
  qed
  moreover have "\<dots> \<rightarrow> (
    [initial_server_state 3 \<lparr>currentTerm := increment_election_term (currentTerm (hd all_states ! 0)), votedFor := Some (node 0)\<rparr>,
     initial_server_state 3 \<lparr>votedFor := Some (node 0)\<rparr>, initial_server_state 3],
    {
      message (node 0) (node 1) (request_vote (node 0) (log_index 0) (election_term 0)) (election_term 1),
      message (node 0) (node 2) (request_vote (node 0) (log_index 0) (election_term 0)) (election_term 1),
      message (node 1) (node 0) (request_vote_response True) (election_term 1)
    })"
    sorry

  show ?thesis
    sorry
qed

end
