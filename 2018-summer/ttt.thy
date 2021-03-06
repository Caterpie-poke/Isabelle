theory ttt
  imports Main
begin
  (*theory begin*)
theorem "P \<longrightarrow> P"
proof
  assume 1: "P"
  show "P" by (rule 1)
qed

lemma "((P \<longrightarrow> Q) \<and> P) \<Longrightarrow> Q"
proof-
  show "((P \<longrightarrow> Q) \<and> P) \<Longrightarrow> Q" by auto
qed

theorem "((P \<longrightarrow> Q) \<and> P) \<Longrightarrow> Q"
  sledgehammer
  by simp
  
    

end
  