theory ex210
  imports Main
begin
datatype tree0 = Leaf | Node "tree0" "tree0"
  
value "Node Leaf Leaf"
  
fun nodes::"tree0 \<Rightarrow> nat" where
  "nodes Leaf = 1"|
  "nodes (Node l r) = Suc(nodes l + nodes r)"
  
fun explode::"nat \<Rightarrow> tree0 \<Rightarrow> tree0" where
  "explode 0 t = t"|
  "explode (Suc n) t = explode n (Node t t)"
  
value "nodes (explode (Suc (Suc 0)) (Node Leaf Leaf))"
value "2^(Suc (Suc 0)) * (nodes (Node Leaf Leaf)) + 2^(Suc (Suc 0)) -1"
  
lemma ex210: "(nodes (explode n t)) = 2^n * (nodes t) + 2^n -1"
  apply(induction n arbitrary: t)
   apply(auto simp add:algebra_simps)
  done
    
    
   
  
end