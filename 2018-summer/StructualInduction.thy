theory StructualInduction
  imports Main
begin
  
lemma "\<Sum>{0..(n::nat)} = n * (n + 1) div 2"
proof (induction n)
  case 0
  show ?case by simp
next
  case (Suc n)
  thus ?case by simp
qed
  
  
end
  