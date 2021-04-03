theory Safety
  imports Main "./Raft"
begin

lemma hd_0th: "length xs > 0 \<Longrightarrow> hd xs = xs ! 0"
  by (simp add: hd_conv_nth)

definition (in raft) valid_params where
  "valid_params n i \<equiv> (n < length all_states \<and> i < number_of_nodes)"

lemma (in raft) valid_params_length_previous: "valid_params (n + 1) i \<Longrightarrow> valid_params n i"
  by (meson add_lessD1 valid_params_def)

lemma (in raft) transition_previous: "n > 0 \<Longrightarrow> (all_states ! (n - 1), all_messages ! (n - 1)) \<rightarrow> (all_states ! n, all_messages ! n)"
  by (simp add: transition)

lemma state_length_invariant_for_transition: "transition N (\<sigma>, m) (\<sigma>', m') \<Longrightarrow> length \<sigma> = length \<sigma>'"
  apply (cases rule: transition.cases)
  apply simp
  apply simp
  sorry

lemma leader_promote_inversion_for_transition:
  "\<lbrakk> i < length \<sigma>; transition N (\<sigma>, ms) (\<sigma>', ms'); state (\<sigma> ! i) \<noteq> leader; state (\<sigma>' ! i) = leader \<rbrakk> \<Longrightarrow> majority N (card {s. \<exists>m \<in> ms. m = message s (node i) (request_vote_response True) (currentTerm (\<sigma> ! i))})"
  apply (cases rule: transition.cases)
  apply simp_all
  apply (simp add: update_nth_nonupdated)
  sorry

lemma (in raft) majority_vote_for_leader:
  "\<lbrakk> valid_params n i; state (all_states ! n ! i) = leader \<rbrakk>
  \<Longrightarrow> majority number_of_nodes (card {s. \<exists>m \<in> all_messages ! (n - 1). m = message s (node i) (request_vote_response True) (currentTerm (all_states ! (n - 1) ! i))})"
  apply (induct n)
  apply (metis hd_0th initial_server_state_def initial_state node_state.distinct(3) raft.valid_params_def raft_axioms repeat_nth select_convs(1))
proof-
  fix n
  assume "(valid_params n i \<Longrightarrow>
          state (all_states ! n ! i) = leader \<Longrightarrow>
          majority number_of_nodes
           (card {s. \<exists>m\<in>all_messages ! (n - 1). m = message s (node i) (request_vote_response True) (currentTerm (all_states ! (n - 1) ! i))}))"
    "valid_params (Suc n) i"
    "state (all_states ! Suc n ! i) = leader"

  have "(all_states ! n, all_messages ! n) \<rightarrow> (all_states ! Suc n, all_messages ! Suc n)"
    using transition_previous by force

  show "majority number_of_nodes
          (card {s. \<exists>m\<in>all_messages ! (Suc n - 1). m = message s (node i) (request_vote_response True) (currentTerm (all_states ! (Suc n - 1) ! i))})"
    apply (cases "state (all_states ! n ! i) = leader")
    sorry
qed

theorem (in raft) election_safety: "
  \<lbrakk> state (all_states ! n ! i) = leader
  ; state (all_states ! n ! j) = leader
  ; currentTerm (all_states ! n ! i) = currentTerm (all_states ! n ! j) \<rbrakk> \<Longrightarrow> i = j"
  sorry

end
