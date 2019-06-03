theory ex_sort
  imports Main
begin
  
value "[1::nat, 3,2]"

(*
fun my_sort::"nat list \<Rightarrow> nat list" where
  "my_sort [] = []"|
  "my_sort [x] = [x]"|
  "my_sort [x1,x2] = (if (x1 < x2) then ([x1,x2]) else ([x2,x1]))"|
  "my_sort (x1#x2#xs) = (if (x1 < x2) then (x1#(my_sort (x2#xs))) else (my_sort (x2#x1#xs)))"
*)
    
fun myInsert::"nat \<Rightarrow> nat list \<Rightarrow> nat list" where
  "myInsert x [] = [x]"|
  "myInsert x (y#ys) = (if (x\<le>y) then (x#y#ys) else (y#(myInsert x ys)))"
  
fun mySort::"nat list \<Rightarrow> nat list" where
  "mySort [] = []"|
  "mySort (x#xs) = myInsert x (mySort xs)"
  
value "mySort [3,2,1]"
  
lemma ms: "\<forall>i j. i<j \<longrightarrow> j<length xs \<longrightarrow> \<not>(mySort xs) ! 1 > (mySort xs) ! 1"
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case by blast
qed
  
lemma subls: "Suc (length xs) = length (myInsert a xs)"
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case by simp
qed
  
lemma ls: "length xs = length (mySort xs)"
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case by (simp add:subls)
qed
    
(*export_code mySort in OCaml*)

  
end
  