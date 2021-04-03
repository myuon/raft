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
