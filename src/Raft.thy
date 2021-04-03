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
  and state_message_sync: "length all_states = length all_messages"

abbreviation (in raft) transition_arrow (infix "\<rightarrow>" 50) where
  "transition_arrow \<equiv> transition number_of_nodes"

definition (in raft) transitions (infix "\<rightarrow>*" 50) where
  "transitions \<equiv> rtranclp (transition number_of_nodes)"

lemma (in raft) transitions_one: "a \<rightarrow> b \<Longrightarrow> a \<rightarrow>* b"
  by (simp add: transitions_def)

lemma (in raft) transisions_trans [trans]: "a \<rightarrow>* b \<Longrightarrow> b \<rightarrow>* c \<Longrightarrow> a \<rightarrow>* c"
  using transitions_def by auto

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
    \<rightarrow>* ([initial_server_state 3 \<lparr>currentTerm := increment_election_term (currentTerm (hd all_states ! 0)), votedFor := Some (node 0)\<rparr>, initial_server_state 3, initial_server_state 3],
    {
      message (node 0) (node 1) (request_vote (node 0) (log_index 0) (election_term 0)) (election_term 1),
      message (node 0) (node 2) (request_vote (node 0) (log_index 0) (election_term 0)) (election_term 1)
    })"
    apply (rule transitions_one)
    apply (cut_tac TR_start_election
        [where N = number_of_nodes
          , where ms = "hd all_messages"
          , where \<sigma> = "[initial_server_state 3, initial_server_state 3, initial_server_state 3]"
          , where target = "0"
          , where index = "log_index 0"
          , where ?term = "election_term 0"])
    apply simp_all
    defer
    apply (simp add: initial_server_state_def)
  proof-
    assume "([initial_server_state 3, initial_server_state 3, initial_server_state 3], hd all_messages) \<rightarrow>
    ([initial_server_state 3\<lparr>currentTerm := election_term (Suc (election_term_of (currentTerm (initial_server_state 3)))), votedFor := Some (node 0)\<rparr>,
      initial_server_state 3, initial_server_state 3],
     hd all_messages \<union>
     {message (node 0) (node i) (request_vote (node 0) (log_index 0) (election_term 0))
       (election_term (Suc (election_term_of (currentTerm (initial_server_state 3))))) |
      i. i \<le> Suc (Suc 0) \<and> 0 < i})"

    have "[initial_server_state 3\<lparr>currentTerm := election_term (Suc (election_term_of (currentTerm (initial_server_state 3)))), votedFor := Some (node 0)\<rparr>, initial_server_state 3, initial_server_state 3]
      = [initial_server_state 3\<lparr>currentTerm := election_term (Suc (election_term_of (currentTerm (hd all_states ! 0)))), votedFor := Some (node 0)\<rparr>, initial_server_state 3, initial_server_state 3]"
      by (simp add: initial_state assms initial_server_state_def repeat_nth)
    moreover have "hd all_messages \<union> {message (node 0) (node i) (request_vote (node 0) (log_index 0) (election_term 0)) (election_term (Suc (election_term_of (currentTerm (initial_server_state 3))))) | i. i \<le> Suc (Suc 0) \<and> 0 < i}
      = {message (node 0) (node (Suc 0)) (request_vote (node 0) (log_index 0) (election_term 0)) (election_term (Suc 0)), message (node 0) (node 2) (request_vote (node 0) (log_index 0) (election_term 0)) (election_term (Suc 0))}"
      apply (simp add: initial_message initial_server_state_def)
      apply auto
      done
    ultimately show "([initial_server_state 3, initial_server_state 3, initial_server_state 3], hd all_messages) \<rightarrow>
    ([initial_server_state 3\<lparr>currentTerm := election_term (Suc (election_term_of (currentTerm (hd all_states ! 0)))), votedFor := Some (node 0)\<rparr>,
      initial_server_state 3, initial_server_state 3],
     {message (node 0) (node (Suc 0)) (request_vote (node 0) (log_index 0) (election_term 0)) (election_term (Suc 0)),
      message (node 0) (node 2) (request_vote (node 0) (log_index 0) (election_term 0)) (election_term (Suc 0))})"
      using \<open>([initial_server_state 3, initial_server_state 3, initial_server_state 3], hd all_messages) \<rightarrow> ([initial_server_state 3 \<lparr>currentTerm := election_term (Suc (election_term_of (currentTerm (initial_server_state 3)))), votedFor := Some (node 0)\<rparr>, initial_server_state 3, initial_server_state 3], hd all_messages \<union> {message (node 0) (node i) (request_vote (node 0) (log_index 0) (election_term 0)) (election_term (Suc (election_term_of (currentTerm (initial_server_state 3))))) | i. i \<le> Suc (Suc 0) \<and> 0 < i})\<close> by force
  qed
  also have "\<dots> \<rightarrow>* (
    [initial_server_state 3 \<lparr>currentTerm := increment_election_term (currentTerm (hd all_states ! 0)), votedFor := Some (node 0)\<rparr>,
     initial_server_state 3 \<lparr>votedFor := Some (node 0)\<rparr>, initial_server_state 3],
    {
      message (node 0) (node 1) (request_vote (node 0) (log_index 0) (election_term 0)) (election_term 1),
      message (node 0) (node 2) (request_vote (node 0) (log_index 0) (election_term 0)) (election_term 1),
      message (node 1) (node 0) (request_vote_response True) (election_term 1)
    })"
    apply (rule transitions_one)
    apply (cut_tac TR_request_vote_resp
        [where N = number_of_nodes 
          , where \<sigma> = "[initial_server_state 3\<lparr>currentTerm := election_term (Suc (election_term_of (currentTerm (initial_server_state 3)))), votedFor := Some (node 0)\<rparr>, initial_server_state 3, initial_server_state 3]"
          , where ms = "{ message (node 0) (node 1) (request_vote (node 0) (log_index 0) (election_term 0)) (election_term 1), message (node 0) (node 2) (request_vote (node 0) (log_index 0) (election_term 0)) (election_term 1) }"
          , where \<sigma>' = "[initial_server_state 3 \<lparr>currentTerm := increment_election_term (currentTerm (hd all_states ! 0)), votedFor := Some (node 0)\<rparr>, initial_server_state 3 \<lparr>votedFor := Some (node 0)\<rparr>, initial_server_state 3]"
          , where resp = "message (node 1) (node 0) (request_vote_response True) (election_term 1)"
          , where s = "node 0"
          ])
    apply simp_all
    apply (simp add: assms initial_state insert_commute numeral_3_eq_3)
    defer
    apply (simp add: initial_state assms initial_server_state_def repeat_nth)
    apply (simp add: ExReq_def initial_state initial_server_state_def)
  proof-
    have "\<And>req. req = message (node 0) (node 1) (request_vote (node 0) (log_index 0) (election_term 0)) (election_term 1)
      \<Longrightarrow> \<not> sender_term req < election_term (Suc 0) \<and>
          (\<not> sender_term req < election_term (Suc 0) \<longrightarrow>
           (\<exists>lastLogIndex lastLogTerm.
               payload req = request_vote (node 0) lastLogIndex lastLogTerm \<and>
               (req = message (node 0) (node (Suc 0)) (request_vote (node 0) (log_index 0) (election_term 0)) (election_term (Suc 0)) \<or>
                req = message (node 0) (node 2) (request_vote (node 0) (log_index 0) (election_term 0)) (election_term (Suc 0))) \<and>
               log_up_to_date [] lastLogIndex lastLogTerm)) \<and>
          respond_to (message (node (Suc 0)) (node 0) (request_vote_response True) (election_term (Suc 0))) req"
      apply (auto simp add: respond_to_def)
      using less_election_term_def apply force
      apply (simp add: log_up_to_date_def)
      done
    show "\<exists>req. \<not> sender_term req < election_term (Suc 0) \<and>
          (\<not> sender_term req < election_term (Suc 0) \<longrightarrow>
           (\<exists>lastLogIndex lastLogTerm.
               payload req = request_vote (node 0) lastLogIndex lastLogTerm \<and>
               (req = message (node 0) (node (Suc 0)) (request_vote (node 0) (log_index 0) (election_term 0)) (election_term (Suc 0)) \<or>
                req = message (node 0) (node 2) (request_vote (node 0) (log_index 0) (election_term 0)) (election_term (Suc 0))) \<and>
               log_up_to_date [] lastLogIndex lastLogTerm)) \<and>
          respond_to (message (node (Suc 0)) (node 0) (request_vote_response True) (election_term (Suc 0))) req"
      by (meson \<open>\<And>req. req = message (node 0) (node 1) (request_vote (node 0) (log_index 0) (election_term 0)) (election_term 1) \<Longrightarrow> \<not> sender_term req < election_term (Suc 0) \<and> (\<not> sender_term req < election_term (Suc 0) \<longrightarrow> (\<exists>lastLogIndex lastLogTerm. payload req = request_vote (node 0) lastLogIndex lastLogTerm \<and> (req = message (node 0) (node (Suc 0)) (request_vote (node 0) (log_index 0) (election_term 0)) (election_term (Suc 0)) \<or> req = message (node 0) (node 2) (request_vote (node 0) (log_index 0) (election_term 0)) (election_term (Suc 0))) \<and> log_up_to_date [] lastLogIndex lastLogTerm)) \<and> respond_to (message (node (Suc 0)) (node 0) (request_vote_response True) (election_term (Suc 0))) req\<close>)
  qed
  also have "\<dots> \<rightarrow>* (
    [initial_server_state 3 \<lparr>currentTerm := increment_election_term (currentTerm (hd all_states ! 0)), votedFor := Some (node 0)\<rparr>,
     initial_server_state 3 \<lparr>votedFor := Some (node 0)\<rparr>,
     initial_server_state 3 \<lparr>votedFor := Some (node 0)\<rparr>],
    {
      message (node 0) (node 1) (request_vote (node 0) (log_index 0) (election_term 0)) (election_term 1),
      message (node 0) (node 2) (request_vote (node 0) (log_index 0) (election_term 0)) (election_term 1),
      message (node 1) (node 0) (request_vote_response True) (election_term 1),
      message (node 2) (node 0) (request_vote_response True) (election_term 1)
    })"
    apply (rule transitions_one)
    apply (cut_tac TR_request_vote_resp
        [where N = number_of_nodes 
          , where \<sigma> = "[initial_server_state 3 \<lparr>currentTerm := increment_election_term (currentTerm (hd all_states ! 0)), votedFor := Some (node 0)\<rparr>, initial_server_state 3 \<lparr>votedFor := Some (node 0)\<rparr>, initial_server_state 3]"
          , where ms = "{message (node 0) (node 1) (request_vote (node 0) (log_index 0) (election_term 0)) (election_term 1),message (node 0) (node 2) (request_vote (node 0) (log_index 0) (election_term 0)) (election_term 1),message (node 1) (node 0) (request_vote_response True) (election_term 1)}"
          , where \<sigma>' = "[initial_server_state 3 \<lparr>currentTerm := increment_election_term (currentTerm (hd all_states ! 0)), votedFor := Some (node 0)\<rparr>,initial_server_state 3 \<lparr>votedFor := Some (node 0)\<rparr>,initial_server_state 3 \<lparr>votedFor := Some (node 0)\<rparr>]"
          , where resp = "message (node 2) (node 0) (request_vote_response True) (election_term 1)"
          , where s = "node 0"
          ])
    apply simp_all
    apply (simp add: assms initial_state insert_commute numeral_3_eq_3)
    defer
    apply (simp add: initial_state assms initial_server_state_def repeat_nth numeral_2_eq_2)
    apply (simp add: ExReq_def initial_state initial_server_state_def)
  proof-
    have "\<And>req. req = message (node 0) (node 2) (request_vote (node 0) (log_index 0) (election_term 0)) (election_term 1)
      \<Longrightarrow>\<not> sender_term req
             < election_term
                (Suc (election_term_of
                       (currentTerm
                         (repeat
                           \<lparr>state = follower, currentTerm = election_term 0, votedFor = None, log = [], commitIndex = 0, lastApplied = 0,
                              nextIndex = repeat (log_index 0) number_of_nodes, matchIndex = repeat (log_index 0) number_of_nodes\<rparr>
                           number_of_nodes !
                          0)))) \<and>
          (\<not> sender_term req
              < election_term
                 (Suc (election_term_of
                        (currentTerm
                          (repeat
                            \<lparr>state = follower, currentTerm = election_term 0, votedFor = None, log = [], commitIndex = 0, lastApplied = 0,
                               nextIndex = repeat (log_index 0) number_of_nodes, matchIndex = repeat (log_index 0) number_of_nodes\<rparr>
                            number_of_nodes !
                           0)))) \<longrightarrow>
           (\<exists>lastLogIndex lastLogTerm.
               payload req = request_vote (node 0) lastLogIndex lastLogTerm \<and>
               (req = message (node 0) (node (Suc 0)) (request_vote (node 0) (log_index 0) (election_term 0)) (election_term (Suc 0)) \<or>
                req = message (node 0) (node 2) (request_vote (node 0) (log_index 0) (election_term 0)) (election_term (Suc 0)) \<or>
                req = message (node (Suc 0)) (node 0) (request_vote_response True) (election_term (Suc 0))) \<and>
               log_up_to_date [] lastLogIndex lastLogTerm)) \<and>
          respond_to (message (node 2) (node 0) (request_vote_response True) (election_term (Suc 0))) req"
      apply (auto simp add: respond_to_def assms repeat_nth)
      using less_election_term_def apply force
      apply (simp add: log_up_to_date_def)
      done
    show "\<exists>req. \<not> sender_term req
             < election_term
                (Suc (election_term_of
                       (currentTerm
                         (repeat
                           \<lparr>state = follower, currentTerm = election_term 0, votedFor = None, log = [], commitIndex = 0, lastApplied = 0,
                              nextIndex = repeat (log_index 0) number_of_nodes, matchIndex = repeat (log_index 0) number_of_nodes\<rparr>
                           number_of_nodes !
                          0)))) \<and>
          (\<not> sender_term req
              < election_term
                 (Suc (election_term_of
                        (currentTerm
                          (repeat
                            \<lparr>state = follower, currentTerm = election_term 0, votedFor = None, log = [], commitIndex = 0, lastApplied = 0,
                               nextIndex = repeat (log_index 0) number_of_nodes, matchIndex = repeat (log_index 0) number_of_nodes\<rparr>
                            number_of_nodes !
                           0)))) \<longrightarrow>
           (\<exists>lastLogIndex lastLogTerm.
               payload req = request_vote (node 0) lastLogIndex lastLogTerm \<and>
               (req = message (node 0) (node (Suc 0)) (request_vote (node 0) (log_index 0) (election_term 0)) (election_term (Suc 0)) \<or>
                req = message (node 0) (node 2) (request_vote (node 0) (log_index 0) (election_term 0)) (election_term (Suc 0)) \<or>
                req = message (node (Suc 0)) (node 0) (request_vote_response True) (election_term (Suc 0))) \<and>
               log_up_to_date [] lastLogIndex lastLogTerm)) \<and>
          respond_to (message (node 2) (node 0) (request_vote_response True) (election_term (Suc 0))) req"
      by (meson \<open>\<And>req. req = message (node 0) (node 2) (request_vote (node 0) (log_index 0) (election_term 0)) (election_term 1) \<Longrightarrow> \<not> sender_term req < election_term (Suc (election_term_of (currentTerm (repeat \<lparr>state = follower, currentTerm = election_term 0, votedFor = None, log = [], commitIndex = 0, lastApplied = 0, nextIndex = repeat (log_index 0) number_of_nodes, matchIndex = repeat (log_index 0) number_of_nodes\<rparr> number_of_nodes ! 0)))) \<and> (\<not> sender_term req < election_term (Suc (election_term_of (currentTerm (repeat \<lparr>state = follower, currentTerm = election_term 0, votedFor = None, log = [], commitIndex = 0, lastApplied = 0, nextIndex = repeat (log_index 0) number_of_nodes, matchIndex = repeat (log_index 0) number_of_nodes\<rparr> number_of_nodes ! 0)))) \<longrightarrow> (\<exists>lastLogIndex lastLogTerm. payload req = request_vote (node 0) lastLogIndex lastLogTerm \<and> (req = message (node 0) (node (Suc 0)) (request_vote (node 0) (log_index 0) (election_term 0)) (election_term (Suc 0)) \<or> req = message (node 0) (node 2) (request_vote (node 0) (log_index 0) (election_term 0)) (election_term (Suc 0)) \<or> req = message (node (Suc 0)) (node 0) (request_vote_response True) (election_term (Suc 0))) \<and> log_up_to_date [] lastLogIndex lastLogTerm)) \<and> respond_to (message (node 2) (node 0) (request_vote_response True) (election_term (Suc 0))) req\<close>)
  qed
  also have "\<dots> \<rightarrow>* (
    [initial_server_state 3 \<lparr>currentTerm := increment_election_term (currentTerm (hd all_states ! 0)), votedFor := Some (node 0), state := leader\<rparr>,
     initial_server_state 3 \<lparr>votedFor := Some (node 0)\<rparr>,
     initial_server_state 3 \<lparr>votedFor := Some (node 0)\<rparr>],
    {
      message (node 0) (node 1) (request_vote (node 0) (log_index 0) (election_term 0)) (election_term 1),
      message (node 0) (node 2) (request_vote (node 0) (log_index 0) (election_term 0)) (election_term 1),
      message (node 1) (node 0) (request_vote_response True) (election_term 1),
      message (node 2) (node 0) (request_vote_response True) (election_term 1)
    })" (is "\<dots> \<rightarrow>* (?state, ?messages)")
    apply (rule transitions_one)
    apply (cut_tac TR_promote_to_leader
        [where N = number_of_nodes
          , where \<sigma> = "[initial_server_state 3 \<lparr>currentTerm := increment_election_term (currentTerm (hd all_states ! 0)), votedFor := Some (node 0)\<rparr>,initial_server_state 3 \<lparr>votedFor := Some (node 0)\<rparr>,initial_server_state 3 \<lparr>votedFor := Some (node 0)\<rparr>]"
          , where ms = "{message (node 0) (node 1) (request_vote (node 0) (log_index 0) (election_term 0)) (election_term 1),message (node 0) (node 2) (request_vote (node 0) (log_index 0) (election_term 0)) (election_term 1),message (node 1) (node 0) (request_vote_response True) (election_term 1),message (node 2) (node 0) (request_vote_response True) (election_term 1)}"
          , where target = "0"
          , where \<sigma>' = "[initial_server_state 3 \<lparr>currentTerm := increment_election_term (currentTerm (hd all_states ! 0)), votedFor := Some (node 0), state := leader\<rparr>,initial_server_state 3 \<lparr>votedFor := Some (node 0)\<rparr>,initial_server_state 3 \<lparr>votedFor := Some (node 0)\<rparr>]"
          ])
    apply simp_all
    apply (simp add: assms majority_def initial_state initial_server_state_def repeat_nth)
  proof-
    have "{s. s = node 1 \<or> s = node 2} = {node 1, node 2}"
      by auto
    moreover have "node 1 \<noteq> node 2"
      by simp
    ultimately have "card {s. s = node 1 \<or> s = node 2} = 2"
      by simp
    thus "3 < 2 * card {s. s = node (Suc 0) \<or> s = node 2}"
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
