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
  and state_message_sync: "length all_states = length all_messages"

lemma (in raft) transition_previous: "n > 0 \<Longrightarrow> (all_states ! (n - 1), all_messages ! (n - 1)) \<rightarrow> (all_states ! n, all_messages ! n)"
  by (simp add: transition)

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

definition (in raft) valid_params where
  "valid_params n i \<equiv> (n < length all_states \<and> i < number_of_nodes)"

lemma (in raft) valid_params_length_smaller: "\<lbrakk> n > m; valid_params n i \<rbrakk> \<Longrightarrow> valid_params m i"
  by (metis add_lessD1 less_imp_add_positive valid_params_def)

lemma (in raft) state_length_invariant: "valid_params n i \<Longrightarrow> length (all_states ! n) = number_of_nodes"
  apply (induct n)
  apply (metis hd_0th initial_state raft.valid_params_def raft_axioms repeat_length)
  by (metis Suc_eq_plus1 lessI raft.valid_params_length_smaller raft_axioms state_length_invariant_for_transition transition)

lemma (in raft) message_is_finite: "valid_params n i \<Longrightarrow> finite (all_messages ! n)"
  apply (induct n)
  apply (simp add: valid_params_def)
  apply (metis finite.intros(1) hd_0th initial_message length_greater_0_conv state_message_sync)
  by (metis Suc_eq_plus1 lessI raft.valid_params_length_smaller raft_axioms transition transition_message_preserves_finite)

lemma (in raft) transision_preserves_valid_sender_and_receiver:
  "\<lbrakk> (\<sigma>,m) \<rightarrow> (\<sigma>',m'); x \<in> m'; length \<sigma> > 0 \<rbrakk>
  \<Longrightarrow> x \<in> m \<or> ((node_of (sender x)) < length \<sigma> \<and> (node_of (receiver x)) < length \<sigma>)"
  apply (cases rule: transition.cases)
  apply simp
proof-
  fix \<sigma>'' \<sigma>''' ms ms' target
  assume "(\<sigma>, m) \<rightarrow> (\<sigma>', m')" "x \<in> m'" "length \<sigma> > 0" "(\<sigma>, m) = (\<sigma>'', ms)" "(\<sigma>', m') = (\<sigma>''', ms')" "TR_condition_start_election \<sigma>'' \<sigma>''' ms ms' target"

  have "\<exists>index term. ms' = ms \<union> {message (node target) (node i) (request_vote (node target) index term) (currentTerm (\<sigma>''' ! target)) |i. i \<le> length \<sigma>'' - Suc 0 \<and> i \<noteq> target}"
    using \<open>TR_condition_start_election \<sigma>'' \<sigma>''' ms ms' target\<close>
    by (auto simp add: TR_condition_start_election_def)
  hence "\<exists>index term. x \<in> ms \<union> {message (node target) (node i) (request_vote (node target) index term) (currentTerm (\<sigma>''' ! target)) |i. i \<le> length \<sigma>'' - Suc 0 \<and> i \<noteq> target}"
    using \<open>(\<sigma>', m') = (\<sigma>''', ms')\<close> \<open>x \<in> m'\<close> by blast
  hence "x \<in> ms \<or> node_of (sender x) = target \<and> node_of (receiver x) \<le> length \<sigma>'' - 1"
    by auto
  hence "x \<in> ms \<or> node_of (sender x) = target \<and> node_of (receiver x) < length \<sigma>''"
    by (metis Suc_diff_1 \<open>(\<sigma>, m) = (\<sigma>'', ms)\<close> \<open>0 < length \<sigma>\<close> less_Suc_eq_le old.prod.inject)

  have "target < length \<sigma>''"
    using \<open>TR_condition_start_election \<sigma>'' \<sigma>''' ms ms' target\<close>
    by (simp add: TR_condition_start_election_def)

  show "x \<in> m \<or> node_of (sender x) < length \<sigma> \<and> node_of (receiver x) < length \<sigma>"
    using \<open>(\<sigma>, m) = (\<sigma>'', ms)\<close> \<open>target < length \<sigma>''\<close> \<open>x \<in> ms \<or> node_of (sender x) = target \<and> node_of (receiver x) < length \<sigma>''\<close> le_less by blast
next
  fix \<sigma>'' \<sigma>''' ms ms' ma r s t vg
  show "(\<sigma>, m) \<rightarrow> (\<sigma>', m') \<Longrightarrow>
       x \<in> m' \<Longrightarrow>
       0 < length \<sigma> \<Longrightarrow>
       (\<sigma>, m) = (\<sigma>'', ms) \<Longrightarrow>
       (\<sigma>', m') = (\<sigma>''', ms') \<Longrightarrow>
       TR_condition_request_vote_resp \<sigma>'' \<sigma>''' ms ms' ma r s t vg \<Longrightarrow> x \<in> m \<or> node_of (sender x) < length \<sigma> \<and> node_of (receiver x) < length \<sigma>"
    apply (simp add: TR_condition_request_vote_resp_def)
    by (metis insertE message.sel(1) message.sel(2) node.sel)
next
  show "\<And>\<sigma>'' \<sigma>''' ms ms' target.
       (\<sigma>, m) \<rightarrow> (\<sigma>', m') \<Longrightarrow>
       x \<in> m' \<Longrightarrow>
       0 < length \<sigma> \<Longrightarrow>
       (\<sigma>, m) = (\<sigma>'', ms) \<Longrightarrow>
       (\<sigma>', m') = (\<sigma>''', ms') \<Longrightarrow>
       TR_condition_promote_to_leader \<sigma>'' \<sigma>''' ms ms' target \<Longrightarrow> x \<in> m \<or> node_of (sender x) < length \<sigma> \<and> node_of (receiver x) < length \<sigma>"
    by (simp add: TR_condition_promote_to_leader_def)
next
  show "\<And>\<sigma>'' \<sigma>''' ms ms' s r.
       (\<sigma>, m) \<rightarrow> (\<sigma>', m') \<Longrightarrow>
       x \<in> m' \<Longrightarrow>
       0 < length \<sigma> \<Longrightarrow>
       (\<sigma>, m) = (\<sigma>'', ms) \<Longrightarrow>
       (\<sigma>', m') = (\<sigma>''', ms') \<Longrightarrow> TR_condition_append_entry \<sigma>'' \<sigma>''' ms ms' s r \<Longrightarrow> x \<in> m \<or> node_of (sender x) < length \<sigma> \<and> node_of (receiver x) < length \<sigma>"
    apply (simp add: TR_condition_append_entry_def)
    apply auto
    done
next
  show "\<And>\<sigma>'' \<sigma>''' ms ms' leadersLog prevLogTerm prevLogIndex t success r s.
       (\<sigma>, m) \<rightarrow> (\<sigma>', m') \<Longrightarrow>
       x \<in> m' \<Longrightarrow>
       0 < length \<sigma> \<Longrightarrow>
       (\<sigma>, m) = (\<sigma>'', ms) \<Longrightarrow>
       (\<sigma>', m') = (\<sigma>''', ms') \<Longrightarrow>
       TR_condition_append_entry_resp \<sigma>'' \<sigma>''' ms ms' leadersLog prevLogTerm prevLogIndex t success r s \<Longrightarrow>
       x \<in> m \<or> node_of (sender x) < length \<sigma> \<and> node_of (receiver x) < length \<sigma>"
    apply (simp add: TR_condition_append_entry_resp_def)
    by (metis insertE message.sel(1) message.sel(2) node.sel)
qed

lemma (in raft) all_messages_contains_valid_messages: "\<lbrakk> valid_params n i; m \<in> all_messages ! n \<rbrakk> \<Longrightarrow> valid_params n (node_of (sender m)) &&& valid_params n (node_of (receiver m))"
  apply (induct n arbitrary: m)
  using hd_conv_nth initial_message state_message_sync valid_params_def apply auto[1]
  using hd_conv_nth initial_message state_message_sync valid_params_def apply auto[1]
proof-
  fix n m
  assume "(\<And>m. valid_params n i \<Longrightarrow> m \<in> all_messages ! n \<Longrightarrow> valid_params n (node_of (sender m)))"
    "(\<And>m. valid_params n i \<Longrightarrow> m \<in> all_messages ! n \<Longrightarrow> valid_params n (node_of (receiver m)))"
    "valid_params (Suc n) i" "m \<in> all_messages ! Suc n"
  have "(all_states ! n, all_messages ! n) \<rightarrow> (all_states ! (n + 1), all_messages ! (n + 1))"
    by (simp add: transition)

  hence "m \<in> all_messages ! n \<or> node_of (sender m) < length (all_states ! n) \<and> node_of (receiver m) < length (all_states ! n)"
    apply (rule transision_preserves_valid_sender_and_receiver)
    using \<open>m \<in> all_messages ! Suc n\<close> apply auto
    by (metis Suc_eq_plus1 \<open>(all_states ! n, all_messages ! n) \<rightarrow> (all_states ! (n + 1), all_messages ! (n + 1))\<close> \<open>valid_params (Suc n) i\<close> gr_implies_not0 list.size(3) state_length_invariant state_length_invariant_for_transition valid_params_def)

  have "m \<in> all_messages ! n \<Longrightarrow> valid_params n (node_of (sender m)) \<and> valid_params n (node_of (receiver m))"
    using \<open>\<And>m. \<lbrakk>valid_params n i; m \<in> all_messages ! n\<rbrakk> \<Longrightarrow> valid_params n (node_of (receiver m))\<close> \<open>\<And>m. \<lbrakk>valid_params n i; m \<in> all_messages ! n\<rbrakk> \<Longrightarrow> valid_params n (node_of (sender m))\<close> \<open>valid_params (Suc n) i\<close> valid_params_length_smaller by blast

  have "length (all_states ! n) = number_of_nodes"
    using \<open>(all_states ! n, all_messages ! n) \<rightarrow> (all_states ! (n + 1), all_messages ! (n + 1))\<close> \<open>valid_params (Suc n) i\<close> state_length_invariant state_length_invariant_for_transition by force
  have "node_of (sender m) \<le> length (all_states ! n) \<and> node_of (receiver m) \<le> length (all_states ! n) \<Longrightarrow> valid_params (Suc n) (node_of (sender m)) \<and> valid_params (Suc n) (node_of (receiver m))"
    apply (auto simp add: valid_params_def)
    using \<open>valid_params (Suc n) i\<close> valid_params_def apply blast
    using \<open>length (all_states ! n) = number_of_nodes\<close> \<open>m \<in> all_messages ! n \<Longrightarrow> valid_params n (node_of (sender m)) \<and> valid_params n (node_of (receiver m))\<close> \<open>m \<in> all_messages ! n \<or> node_of (sender m) < length (all_states ! n) \<and> node_of (receiver m) < length (all_states ! n)\<close> valid_params_def apply blast
    using \<open>valid_params (Suc n) i\<close> raft.valid_params_def raft_axioms apply blast
    using \<open>length (all_states ! n) = number_of_nodes\<close> \<open>m \<in> all_messages ! n \<Longrightarrow> valid_params n (node_of (sender m)) \<and> valid_params n (node_of (receiver m))\<close> \<open>m \<in> all_messages ! n \<or> node_of (sender m) < length (all_states ! n) \<and> node_of (receiver m) < length (all_states ! n)\<close> valid_params_def by blast

  show "valid_params (Suc n) (node_of (sender m))" "valid_params (Suc n) (node_of (receiver m))"
    apply (metis \<open>length (all_states ! n) = number_of_nodes\<close> \<open>m \<in> all_messages ! n \<Longrightarrow> valid_params n (node_of (sender m)) \<and> valid_params n (node_of (receiver m))\<close> \<open>m \<in> all_messages ! n \<or> node_of (sender m) < length (all_states ! n) \<and> node_of (receiver m) < length (all_states ! n)\<close> \<open>node_of (sender m) \<le> length (all_states ! n) \<and> node_of (receiver m) \<le> length (all_states ! n) \<Longrightarrow> valid_params (Suc n) (node_of (sender m)) \<and> valid_params (Suc n) (node_of (receiver m))\<close> nat_less_le valid_params_def)
    by (metis \<open>length (all_states ! n) = number_of_nodes\<close> \<open>m \<in> all_messages ! n \<Longrightarrow> valid_params n (node_of (sender m)) \<and> valid_params n (node_of (receiver m))\<close> \<open>m \<in> all_messages ! n \<or> node_of (sender m) < length (all_states ! n) \<and> node_of (receiver m) < length (all_states ! n)\<close> \<open>node_of (sender m) \<le> length (all_states ! n) \<and> node_of (receiver m) \<le> length (all_states ! n) \<Longrightarrow> valid_params (Suc n) (node_of (sender m)) \<and> valid_params (Suc n) (node_of (receiver m))\<close> nat_less_le valid_params_def)
qed

lemma (in raft) all_messages_contains_valid_sender: "\<lbrakk> valid_params n i; m \<in> all_messages ! n \<rbrakk> \<Longrightarrow> valid_params n (node_of (sender m))"
  using all_messages_contains_valid_messages
  by auto

lemma (in raft) all_messages_contains_valid_receiver: "\<lbrakk> valid_params n i; m \<in> all_messages ! n \<rbrakk> \<Longrightarrow> valid_params n (node_of (receiver m))"
  using all_messages_contains_valid_messages
  by auto

lemma (in raft)
  assumes "number_of_nodes = 3"
  obtains \<sigma> ms where "(hd all_states, hd all_messages) \<rightarrow>* (\<sigma>, ms)" "state (\<sigma> ! 0) = leader"
proof-
  have "(hd all_states, hd all_messages) = (repeat (initial_server_state 3) 3, {})"
    by (simp add: assms initial_state initial_message)
  also have "\<dots> \<rightarrow>*
    ([initial_server_state 3 \<lparr>currentTerm := increment_election_term (currentTerm (initial_server_state 3)), votedFor := Some (node 0)\<rparr>, initial_server_state 3, initial_server_state 3],
    {message (node 0) (node 1) (request_vote (node 0) (log_index 0) (election_term 0)) (election_term 1),message (node 0) (node 2) (request_vote (node 0) (log_index 0) (election_term 0)) (election_term 1)})"
    apply (rule transitions_one)
    apply (rule TR_start_election [where target = 0])
    apply (simp add: TR_condition_start_election_def)
    apply (auto simp add: initial_server_state_def repeat_length numeral_3_eq_3)
    done
  also have "\<dots> \<rightarrow>* (
    [initial_server_state 3 \<lparr>currentTerm := increment_election_term (currentTerm (initial_server_state 3)), votedFor := Some (node 0)\<rparr>,initial_server_state 3 \<lparr>votedFor := Some (node 0)\<rparr>, initial_server_state 3],
    {message (node 1) (node 0) (request_vote_response True) (election_term 1),message (node 0) (node 1) (request_vote (node 0) (log_index 0) (election_term 0)) (election_term 1),message (node 0) (node 2) (request_vote (node 0) (log_index 0) (election_term 0)) (election_term 1)})"
    apply (rule transitions_one)
    apply (rule TR_request_vote_resp [where m = 1, where r = 0, where vg = True, where t = "election_term 1", where s = "node 0"])
    apply (simp add: TR_condition_request_vote_resp_def)
  proof-
    have "ExReqProps (message (node (Suc 0)) (node 0) (request_vote_response True) (election_term (Suc 0)))
        (\<lambda>req. \<not> sender_term req < election_term (Suc (election_term_of (currentTerm (initial_server_state 3)))) \<and>
                (\<not> sender_term req < election_term (Suc (election_term_of (currentTerm (initial_server_state 3)))) \<longrightarrow>
                 (\<exists>lastLogIndex lastLogTerm.
                     payload req = request_vote (node 0) lastLogIndex lastLogTerm \<and>
                     (req = message (node 0) (node (Suc 0)) (request_vote (node 0) (log_index 0) (election_term 0)) (election_term (Suc 0)) \<or>
                      req = message (node 0) (node 2) (request_vote (node 0) (log_index 0) (election_term 0)) (election_term (Suc 0))) \<and>
                     log_up_to_date (log (initial_server_state 3)) lastLogIndex lastLogTerm \<and>
                     (votedFor (initial_server_state 3) = Some (node 0) \<or> votedFor (initial_server_state 3) = None))))
        (message (node 0) (node 1) (request_vote (node 0) (log_index 0) (election_term 0)) (election_term 1))"
      apply (simp add: ExReqProps_def initial_server_state_def respond_to_def log_up_to_date_def)
      by (simp add: less_election_term_def)

    show "ExReq (message (node (Suc 0)) (node 0) (request_vote_response True) (election_term (Suc 0)))
     (\<lambda>req. \<not> sender_term req < election_term (Suc (election_term_of (currentTerm (initial_server_state 3)))) \<and>
             (\<not> sender_term req < election_term (Suc (election_term_of (currentTerm (initial_server_state 3)))) \<longrightarrow>
              (\<exists>lastLogIndex lastLogTerm.
                  payload req = request_vote (node 0) lastLogIndex lastLogTerm \<and>
                  (req = message (node 0) (node (Suc 0)) (request_vote (node 0) (log_index 0) (election_term 0)) (election_term (Suc 0)) \<or>
                   req = message (node 0) (node 2) (request_vote (node 0) (log_index 0) (election_term 0)) (election_term (Suc 0))) \<and>
                  log_up_to_date (log (initial_server_state 3)) lastLogIndex lastLogTerm \<and>
                  (votedFor (initial_server_state 3) = Some (node 0) \<or> votedFor (initial_server_state 3) = None))))"
      apply (simp add: ExReq_def)
      using \<open>ExReqProps (message (node (Suc 0)) (node 0) (request_vote_response True) (election_term (Suc 0))) (\<lambda>req. \<not> sender_term req < election_term (Suc (election_term_of (currentTerm (initial_server_state 3)))) \<and> (\<not> sender_term req < election_term (Suc (election_term_of (currentTerm (initial_server_state 3)))) \<longrightarrow> (\<exists>lastLogIndex lastLogTerm. payload req = request_vote (node 0) lastLogIndex lastLogTerm \<and> (req = message (node 0) (node (Suc 0)) (request_vote (node 0) (log_index 0) (election_term 0)) (election_term (Suc 0)) \<or> req = message (node 0) (node 2) (request_vote (node 0) (log_index 0) (election_term 0)) (election_term (Suc 0))) \<and> log_up_to_date (log (initial_server_state 3)) lastLogIndex lastLogTerm \<and> (votedFor (initial_server_state 3) = Some (node 0) \<or> votedFor (initial_server_state 3) = None)))) (message (node 0) (node 1) (request_vote (node 0) (log_index 0) (election_term 0)) (election_term 1))\<close> by blast
  qed
  also have "\<dots> \<rightarrow>* (
    [initial_server_state 3 \<lparr>currentTerm := increment_election_term (currentTerm (initial_server_state 3)), votedFor := Some (node 0)\<rparr>,initial_server_state 3 \<lparr>votedFor := Some (node 0)\<rparr>,initial_server_state 3 \<lparr>votedFor := Some (node 0)\<rparr>],
    {message (node 2) (node 0) (request_vote_response True) (election_term 1),message (node 1) (node 0) (request_vote_response True) (election_term 1),message (node 0) (node 1) (request_vote (node 0) (log_index 0) (election_term 0)) (election_term 1),message (node 0) (node 2) (request_vote (node 0) (log_index 0) (election_term 0)) (election_term 1)})"
    apply (rule transitions_one)
    apply (rule TR_request_vote_resp [where m = 2, where r = 0, where vg = True, where t = "election_term 1", where s = "node 0"])
    apply (simp add: TR_condition_request_vote_resp_def)
  proof-
    have "ExReqProps (message (node 2) (node 0) (request_vote_response True) (election_term (Suc 0)))
     (\<lambda>req. \<not> sender_term req < election_term (Suc (election_term_of (currentTerm (initial_server_state 3)))) \<and>
             (\<not> sender_term req < election_term (Suc (election_term_of (currentTerm (initial_server_state 3)))) \<longrightarrow>
              (\<exists>lastLogIndex lastLogTerm.
                  payload req = request_vote (node 0) lastLogIndex lastLogTerm \<and>
                  (req = message (node (Suc 0)) (node 0) (request_vote_response True) (election_term (Suc 0)) \<or>
                   req = message (node 0) (node (Suc 0)) (request_vote (node 0) (log_index 0) (election_term 0)) (election_term (Suc 0)) \<or>
                   req = message (node 0) (node 2) (request_vote (node 0) (log_index 0) (election_term 0)) (election_term (Suc 0))) \<and>
                  log_up_to_date (log (initial_server_state 3)) lastLogIndex lastLogTerm \<and>
                  (votedFor (initial_server_state 3) = Some (node 0) \<or> votedFor (initial_server_state 3) = None))))
     (message (node 0) (node 2) (request_vote (node 0) (log_index 0) (election_term 0)) (election_term 1))"
      apply (simp add: ExReqProps_def initial_server_state_def respond_to_def log_up_to_date_def)
      by (simp add: less_election_term_def)

    show "ExReq (message (node 2) (node 0) (request_vote_response True) (election_term (Suc 0)))
     (\<lambda>req. \<not> sender_term req < election_term (Suc (election_term_of (currentTerm (initial_server_state 3)))) \<and>
             (\<not> sender_term req < election_term (Suc (election_term_of (currentTerm (initial_server_state 3)))) \<longrightarrow>
              (\<exists>lastLogIndex lastLogTerm.
                  payload req = request_vote (node 0) lastLogIndex lastLogTerm \<and>
                  (req = message (node (Suc 0)) (node 0) (request_vote_response True) (election_term (Suc 0)) \<or>
                   req = message (node 0) (node (Suc 0)) (request_vote (node 0) (log_index 0) (election_term 0)) (election_term (Suc 0)) \<or>
                   req = message (node 0) (node 2) (request_vote (node 0) (log_index 0) (election_term 0)) (election_term (Suc 0))) \<and>
                  log_up_to_date (log (initial_server_state 3)) lastLogIndex lastLogTerm \<and>
                  (votedFor (initial_server_state 3) = Some (node 0) \<or> votedFor (initial_server_state 3) = None)))) \<and>
    [initial_server_state 3\<lparr>currentTerm := election_term (Suc (election_term_of (currentTerm (initial_server_state 3)))), votedFor := Some (node 0)\<rparr>,
     initial_server_state 3\<lparr>votedFor := Some (node 0)\<rparr>, initial_server_state 3\<lparr>votedFor := Some (node 0)\<rparr>] =
    update 2 (initial_server_state 3\<lparr>votedFor := Some (node 0)\<rparr>)
     [initial_server_state 3\<lparr>currentTerm := election_term (Suc (election_term_of (currentTerm (initial_server_state 3)))), votedFor := Some (node 0)\<rparr>,
      initial_server_state 3\<lparr>votedFor := Some (node 0)\<rparr>, initial_server_state 3]"
      apply auto
      using ExReq_def \<open>ExReqProps (message (node 2) (node 0) (request_vote_response True) (election_term (Suc 0))) (\<lambda>req. \<not> sender_term req < election_term (Suc (election_term_of (currentTerm (initial_server_state 3)))) \<and> (\<not> sender_term req < election_term (Suc (election_term_of (currentTerm (initial_server_state 3)))) \<longrightarrow> (\<exists>lastLogIndex lastLogTerm. payload req = request_vote (node 0) lastLogIndex lastLogTerm \<and> (req = message (node (Suc 0)) (node 0) (request_vote_response True) (election_term (Suc 0)) \<or> req = message (node 0) (node (Suc 0)) (request_vote (node 0) (log_index 0) (election_term 0)) (election_term (Suc 0)) \<or> req = message (node 0) (node 2) (request_vote (node 0) (log_index 0) (election_term 0)) (election_term (Suc 0))) \<and> log_up_to_date (log (initial_server_state 3)) lastLogIndex lastLogTerm \<and> (votedFor (initial_server_state 3) = Some (node 0) \<or> votedFor (initial_server_state 3) = None)))) (message (node 0) (node 2) (request_vote (node 0) (log_index 0) (election_term 0)) (election_term 1))\<close> apply blast
      by (simp add: numeral_2_eq_2)
  qed
  also have "\<dots> \<rightarrow>* (
    [initial_server_state 3 \<lparr>currentTerm := increment_election_term (currentTerm (initial_server_state 3)), votedFor := Some (node 0), state := leader\<rparr>,initial_server_state 3 \<lparr>votedFor := Some (node 0)\<rparr>,initial_server_state 3 \<lparr>votedFor := Some (node 0)\<rparr>],
    {message (node 2) (node 0) (request_vote_response True) (election_term 1),message (node 1) (node 0) (request_vote_response True) (election_term 1),message (node 0) (node 1) (request_vote (node 0) (log_index 0) (election_term 0)) (election_term 1),message (node 0) (node 2) (request_vote (node 0) (log_index 0) (election_term 0)) (election_term 1)})"
    (is "\<dots> \<rightarrow>* (?state, ?messages)")
    apply (rule transitions_one)
    apply (rule TR_promote_to_leader [where target = 0])
    apply (simp add: TR_condition_promote_to_leader_def)
    apply (simp add: majority_def initial_server_state_def)
  proof-
    have "{s. s = node 2 \<or> s = node (Suc 0)} = {node 1, node 2}"
      by auto
    moreover have "node 1 \<noteq> node 2"
      by simp
    ultimately have "card {s. s = node 2 \<or> s = node (Suc 0)} = 2"
      by simp
    thus "Suc (Suc (Suc 0)) < 2 * card {s. s = node 2 \<or> s = node (Suc 0)}"
      by simp
  qed
  finally have "(hd all_states, hd all_messages) \<rightarrow>* (?state, ?messages)" "state (?state ! 0) = leader"
    apply (simp add: initial_state assms numeral_3_eq_3)
    apply simp
    done

  thus ?thesis
    using that by blast
qed

end
