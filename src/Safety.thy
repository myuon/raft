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
  obtains m where "m < n" "state (all_states ! m ! i) \<noteq> leader" "state (all_states ! (m + 1) ! i) = leader" "currentTerm (all_states ! m ! i) = currentTerm (all_states ! n ! i)"
  using assms
  apply (induct n)
  apply simp
  apply (metis hd_conv_nth initial_server_state_def initial_state less_numeral_extra(3) list.size(3) node_state.simps(4) repeat_nth select_convs(1) valid_params_def)
  sorry

lemma (in raft) vote_twice_same_term_is_not_allowed:
  "\<lbrakk> m \<in> all_messages ! n; m' \<in> all_messages ! n
  ; payload m = request_vote_response True; payload m' = request_vote_response True
  ; sender m = sender m'
  ; sender_term m = sender_term m'
  \<rbrakk> \<Longrightarrow> m = m'"
  sorry

theorem (in raft) election_safety: "
  \<lbrakk> valid_params n i
  ; valid_params n j
  ; state (all_states ! n ! i) = leader
  ; state (all_states ! n ! j) = leader
  ; currentTerm (all_states ! n ! i) = currentTerm (all_states ! n ! j) \<rbrakk> \<Longrightarrow> i = j"
proof-
  assume "valid_params n i" "valid_params n j" "state (all_states ! n ! i) = leader" "state (all_states ! n ! j) = leader" "currentTerm (all_states ! n ! i) = currentTerm (all_states ! n ! j)"
  obtain ni where "ni < n" "state (all_states ! ni ! i) \<noteq> leader" "state (all_states ! (ni + 1) ! i) = leader" "currentTerm (all_states ! ni ! i) = currentTerm (all_states ! n ! i)"
    using \<open>state (all_states ! n ! i) = leader\<close> \<open>valid_params n i\<close> raft.leader_has_promotion_point_in_past raft_axioms by blast
  obtain nj where "nj < n" "state (all_states ! nj ! j) \<noteq> leader" "state (all_states ! (nj + 1) ! j) = leader" "currentTerm (all_states ! nj ! j) = currentTerm (all_states ! n ! j)"
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

  have "\<And>s. node_of s < number_of_nodes \<Longrightarrow> s \<in> node ` {0..<number_of_nodes}"
    by force
  have card_of_u: "(card (node ` {0..<number_of_nodes})) = number_of_nodes"
  proof-
    have "inj_on node {0..<number_of_nodes}"
      by (meson inj_onI node.inject)
    show "card (node ` {0..<number_of_nodes}) = number_of_nodes"
      by (simp add: \<open>inj_on node {0..<number_of_nodes}\<close> card_image)
  qed

  have "all_messages ! ni \<subseteq> all_messages ! n"
    by (simp add: \<open>ni < n\<close> less_or_eq_imp_le message_monotonicity)
  have "all_messages ! nj \<subseteq> all_messages ! n"
    by (simp add: \<open>nj < n\<close> less_imp_le_nat message_monotonicity)
  have "{s. \<exists>m \<in> all_messages ! ni. m = message s (node i) (request_vote_response True) (currentTerm (all_states ! ni ! i))} \<inter> {s. \<exists>m \<in> all_messages ! nj. m = message s (node j) (request_vote_response True) (currentTerm (all_states ! nj ! j))} \<noteq> {}"
    apply (rule majority_pigeonhole [where u = "node ` {0..<number_of_nodes}"])
    apply simp_all
  proof-
    show "{s. message s (node i) (request_vote_response True) (currentTerm (all_states ! ni ! i)) \<in> all_messages ! ni} \<subseteq> node ` {0..<number_of_nodes}"
      apply auto
      by (metis \<open>\<And>s. node_of s < number_of_nodes \<Longrightarrow> s \<in> node ` {0..<number_of_nodes}\<close> \<open>valid_params ni i\<close> all_messages_contains_valid_sender message.sel(1) raft.valid_params_def raft_axioms)
  next
    show "{s. message s (node j) (request_vote_response True) (currentTerm (all_states ! nj ! j)) \<in> all_messages ! nj} \<subseteq> node ` {0..<number_of_nodes}"
      apply auto
      by (metis \<open>\<And>s. node_of s < number_of_nodes \<Longrightarrow> s \<in> node ` {0..<number_of_nodes}\<close> \<open>valid_params nj j\<close> all_messages_contains_valid_sender message.sel(1) raft.valid_params_def raft_axioms)
  next
    show "majority (card (node ` {0..<number_of_nodes})) {s. message s (node i) (request_vote_response True) (currentTerm (all_states ! ni ! i)) \<in> all_messages ! ni}"
      apply (simp add: card_of_u)
      using \<open>length (all_states ! ni) = number_of_nodes\<close> \<open>majority (length (all_states ! ni)) {s. \<exists>m\<in>all_messages ! ni. m = message s (node i) (request_vote_response True) (currentTerm (all_states ! ni ! i))}\<close> by auto
  next
    show "majority (card (node ` {0..<number_of_nodes})) {s. message s (node j) (request_vote_response True) (currentTerm (all_states ! nj ! j)) \<in> all_messages ! nj}"
      apply (simp add: card_of_u)
      using \<open>length (all_states ! nj) = number_of_nodes\<close> \<open>majority (length (all_states ! nj)) {s. \<exists>m\<in>all_messages ! nj. m = message s (node j) (request_vote_response True) (currentTerm (all_states ! nj ! j))}\<close> by auto
  qed

  then obtain z where "z \<in> {s. \<exists>m \<in> all_messages ! ni. m = message s (node i) (request_vote_response True) (currentTerm (all_states ! ni ! i))} \<inter> {s. \<exists>m \<in> all_messages ! nj. m = message s (node j) (request_vote_response True) (currentTerm (all_states ! nj ! j))}"
    by auto
  obtain m1 where "m1 \<in> all_messages ! ni" "m1 = message z (node i) (request_vote_response True) (currentTerm (all_states ! ni ! i))"
    using \<open>z \<in> {s. \<exists>m\<in>all_messages ! ni. m = message s (node i) (request_vote_response True) (currentTerm (all_states ! ni ! i))} \<inter> {s. \<exists>m\<in>all_messages ! nj. m = message s (node j) (request_vote_response True) (currentTerm (all_states ! nj ! j))}\<close> by blast
  obtain m2 where "m2 \<in> all_messages ! nj" "m2 = message z (node j) (request_vote_response True) (currentTerm (all_states ! nj ! j))"
    using \<open>z \<in> {s. \<exists>m\<in>all_messages ! ni. m = message s (node i) (request_vote_response True) (currentTerm (all_states ! ni ! i))} \<inter> {s. \<exists>m\<in>all_messages ! nj. m = message s (node j) (request_vote_response True) (currentTerm (all_states ! nj ! j))}\<close> by blast

  have "m1 = m2"
    apply (rule vote_twice_same_term_is_not_allowed [where n = n])
    using \<open>all_messages ! ni \<subseteq> all_messages ! n\<close> \<open>m1 \<in> all_messages ! ni\<close> apply blast
    using \<open>all_messages ! nj \<subseteq> all_messages ! n\<close> \<open>m2 \<in> all_messages ! nj\<close> apply auto[1]
    using \<open>m1 = message z (node i) (request_vote_response True) (currentTerm (all_states ! ni ! i))\<close> apply auto[1]
    apply (simp add: \<open>m2 = message z (node j) (request_vote_response True) (currentTerm (all_states ! nj ! j))\<close>)
    apply (simp add: \<open>m1 = message z (node i) (request_vote_response True) (currentTerm (all_states ! ni ! i))\<close> \<open>m2 = message z (node j) (request_vote_response True) (currentTerm (all_states ! nj ! j))\<close>)
    by (simp add: \<open>currentTerm (all_states ! n ! i) = currentTerm (all_states ! n ! j)\<close> \<open>currentTerm (all_states ! ni ! i) = currentTerm (all_states ! n ! i)\<close> \<open>currentTerm (all_states ! nj ! j) = currentTerm (all_states ! n ! j)\<close> \<open>m1 = message z (node i) (request_vote_response True) (currentTerm (all_states ! ni ! i))\<close> \<open>m2 = message z (node j) (request_vote_response True) (currentTerm (all_states ! nj ! j))\<close>)

  show "i = j"
    using \<open>m1 = m2\<close> \<open>m1 = message z (node i) (request_vote_response True) (currentTerm (all_states ! ni ! i))\<close> \<open>m2 = message z (node j) (request_vote_response True) (currentTerm (all_states ! nj ! j))\<close> by fastforce
qed

end
