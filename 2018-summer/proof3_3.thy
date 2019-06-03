theory proof3_3
  imports Main
begin
lemma "A \<le> B \<inter> C \<Longrightarrow> A \<le> B \<union> C"
  apply(auto)
  done
    
lemma "((P x \<longrightarrow> Q x) \<and> P x) \<longrightarrow> Q x"
  by auto
    
lemma "\<lbrakk> (a::nat)\<le>b; b\<le>c; c\<le>d; d\<le>e \<rbrakk> \<Longrightarrow> a \<le> e"
  apply(simp)
  done
    
lemma peirce: "(((P\<longrightarrow>Q)\<longrightarrow>P)\<longrightarrow>P)"
  apply(blast)
  done
    
lemma peirce2: "(((P\<longrightarrow>Q)\<longrightarrow>P)\<longrightarrow>P)"
proof
  assume 1: "(P\<longrightarrow>Q)\<longrightarrow>P"
  show P
  proof (rule classical)
    assume 2: "\<not>P"
    have "P\<longrightarrow>Q"
    proof
      assume P
      with 2 show Q by contradiction
    qed
    with 1 show P ..
  qed
qed
  
      

    
    
end
  