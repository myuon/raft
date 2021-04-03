theory Safety
  imports Main "./Raft"
begin

lemma (in raft) majority_vote_for_leader:
  "\<lbrakk> valid_params n i; state (all_states ! n ! i) = leader \<rbrakk>
  \<Longrightarrow> majority number_of_nodes {s. \<exists>m \<in> all_messages ! (n - 1). m = message s (node i) (request_vote_response True) (currentTerm (all_states ! (n - 1) ! i))}"
  apply (induct n)
  apply (metis hd_0th initial_server_state_def initial_state node_state.distinct(3) raft.valid_params_def raft_axioms repeat_nth select_convs(1))
proof-
  fix n
  assume "(valid_params n i \<Longrightarrow>
          state (all_states ! n ! i) = leader \<Longrightarrow>
          majority number_of_nodes
           {s. \<exists>m\<in>all_messages ! (n - 1). m = message s (node i) (request_vote_response True) (currentTerm (all_states ! (n - 1) ! i))})"
    "valid_params (Suc n) i"
    "state (all_states ! Suc n ! i) = leader"

  have "(all_states ! n, all_messages ! n) \<rightarrow> (all_states ! Suc n, all_messages ! Suc n)"
    using transition_previous by force

  show "majority number_of_nodes
          ({s. \<exists>m\<in>all_messages ! (Suc n - 1). m = message s (node i) (request_vote_response True) (currentTerm (all_states ! (Suc n - 1) ! i))})"
    apply (cases "state (all_states ! n ! i) = leader")
    sorry
qed

lemma (in raft) leader_has_promotion_point_in_past:
  assumes "state (all_states ! n ! i) = leader" "valid_params n i"
  obtains m where "m < n" "state (all_states ! m ! i) \<noteq> leader" "state (all_states ! (m + 1) ! i) = leader"
  using assms
  apply (induct n)
  apply simp
  apply (metis ext_inject hd_0th initial_server_state_def initial_state node_state.simps(4) raft.valid_params_def raft_axioms repeat_nth surjective)
  by (metis Suc_eq_plus1 add.right_neutral add_strict_mono lessI valid_params_length_smaller zero_less_one)

theorem (in raft) election_safety: "
  \<lbrakk> valid_params n i
  ; valid_params n j
  ; state (all_states ! n ! i) = leader
  ; state (all_states ! n ! j) = leader
  ; currentTerm (all_states ! n ! i) = currentTerm (all_states ! n ! j) \<rbrakk> \<Longrightarrow> i = j"
proof-
  assume "valid_params n i" "valid_params n j" "state (all_states ! n ! i) = leader" "state (all_states ! n ! j) = leader" "currentTerm (all_states ! n ! i) = currentTerm (all_states ! n ! j)"
  obtain ni where "ni < n" "state (all_states ! ni ! i) \<noteq> leader" "state (all_states ! (ni + 1) ! i) = leader"
    using \<open>state (all_states ! n ! i) = leader\<close> \<open>valid_params n i\<close> raft.leader_has_promotion_point_in_past raft_axioms by blast
  obtain nj where "nj < n" "state (all_states ! nj ! j) \<noteq> leader" "state (all_states ! (nj + 1) ! j) = leader"
    using \<open>state (all_states ! n ! j) = leader\<close> \<open>valid_params n j\<close> leader_has_promotion_point_in_past by blast

  have "valid_params ni i"
    using \<open>ni < n\<close> \<open>valid_params n i\<close> raft.valid_params_length_smaller raft_axioms by blast
  have "majority (length (all_states ! ni)) ({s. \<exists>m \<in> all_messages ! ni. m = message s (node i) (request_vote_response True) (currentTerm (all_states ! ni ! i))})"
    apply (rule leader_promote_inversion_for_transition [where \<sigma>' = "all_states ! (ni + 1)", where ms' = "all_messages ! (ni + 1)"])
    using \<open>valid_params ni i\<close> raft.state_length_invariant raft.valid_params_def raft_axioms apply blast
    apply (simp add: transition)
    apply (simp add: \<open>state (all_states ! ni ! i) \<noteq> leader\<close>)
    using \<open>state (all_states ! (ni + 1) ! i) = leader\<close> by auto

  have "valid_params nj j"
    using \<open>nj < n\<close> \<open>valid_params n j\<close> valid_params_length_smaller by auto
  have "majority (length (all_states ! nj)) ({s. \<exists>m \<in> all_messages ! nj. m = message s (node j) (request_vote_response True) (currentTerm (all_states ! nj ! j))})"
    apply (rule leader_promote_inversion_for_transition [where \<sigma>' = "all_states ! (nj + 1)", where ms' = "all_messages ! (nj + 1)"])
    using \<open>valid_params nj j\<close> state_length_invariant valid_params_def apply blast
    apply (simp add: transition)
    apply (simp add: \<open>state (all_states ! nj ! j) \<noteq> leader\<close>)
    using \<open>state (all_states ! (nj + 1) ! j) = leader\<close> by auto

  have "length (all_states ! ni) = number_of_nodes"
    using \<open>valid_params ni i\<close> state_length_invariant by auto
  have "length (all_states ! nj) = number_of_nodes"
    using \<open>valid_params nj j\<close> state_length_invariant by auto

  have "all_messages ! ni \<subseteq> all_messages ! n"
    by (simp add: \<open>ni < n\<close> less_or_eq_imp_le message_monotonicity)
  have "all_messages ! nj \<subseteq> all_messages ! n"
    by (simp add: \<open>nj < n\<close> less_imp_le_nat message_monotonicity)
  have "{s. \<exists>m \<in> all_messages ! ni. m = message s (node i) (request_vote_response True) (currentTerm (all_states ! ni ! i))} \<inter> {s. \<exists>m \<in> all_messages ! nj. m = message s (node j) (request_vote_response True) (currentTerm (all_states ! nj ! j))} \<noteq> {}"
    apply (rule majority_pigeonhole [where u = "node ` {0..number_of_nodes}"])
    apply simp
    apply simp

  show "i = j"

end
