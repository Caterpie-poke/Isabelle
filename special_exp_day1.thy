theory special_exp_day1
  imports Main
begin
  lemma name : "\<And>P. P \<Longrightarrow> P"
  proof-
    fix P
    assume 1:"P"
    show "P" by (rule 1)
  qed(*comment*)
    
  lemma name2 : "\<And>P .P \<Longrightarrow> P"
  proof-
    show "\<And>P. P \<Longrightarrow> P" by auto
  qed(*auto version*)
  
  lemma cont1 : "\<And>P .(A \<equiv> \<not>A) \<Longrightarrow> P"
  proof-
    show "\<And>P .(A \<equiv> \<not>A) \<Longrightarrow> P" by auto
  qed(*What's the purpose of your visit?*)
    
  lemma mul : "\<And>A B. A \<Longrightarrow> B \<Longrightarrow> A\<and>B"
  proof-
    fix "A"
    fix "B"
    assume 1: "A"
    assume 2: "B"
    show "\<And>A B. A \<Longrightarrow> B \<Longrightarrow> A\<and>B" by (rule conjI)
  qed(*contents of auto*)
    
  lemma adjd : "\<And>A B.  A \<Longrightarrow> (A \<Longrightarrow> B) \<Longrightarrow> B"
    proof-
      fix "A"
      fix "B"
      assume 1: "A"
      assume 2: "A \<Longrightarrow> B"
      show "B" by (rule 2 ,rule 1)
    qed
        
  lemma nat_unit : "\<And>n::nat. n+0=n"
  proof-
    fix n :: "nat"
    show "n+0=n"
    proof (cases n)
      case 0
      then show ?thesis by auto
    next
      case (Suc nat)
      then show ?thesis by auto
    qed
  qed
  
  lemma "\<And>n :: nat. n\<ge>5 \<Longrightarrow> n^2 < 2^n"
  proof-
    fix n :: "nat"
    assume 1: "n\<ge>5"
    show  "n^2 < 2^n"
      proof (cases n)
        case 0
        then show ?thesis by auto
      next
        case (Suc nat)
        then show ?thesis by auto
      qed
  qed
    
  
  (*homework*)
  (*flow
    assume (())
    (()) \<Longrightarrow> A
    proof (())
    () \<Longrightarrow> A
  *)

  lemma parse : "\<And> A B. ((A\<Longrightarrow>B) \<Longrightarrow> A) \<Longrightarrow> A"
  proof-
    (*show "\<And> A B. ((A\<Longrightarrow>B) \<Longrightarrow> A) \<Longrightarrow> A" by auto*)
    fix "A"
    fix "B"
    assume 1: "(A\<Longrightarrow>B)"
    show "A\<open>\<close>
  qed  
  
end