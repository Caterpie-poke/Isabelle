theory ex301
  imports Main
begin
datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"
  
value "Node Tip True Tip"
  
fun set::"'a tree \<Rightarrow> 'a set" where
  "set Tip = {}"|
  "set (Node l v r) = (set l) \<union> {v} \<union> (set r)"
  
value "set (Node (Node (Node Tip 4 Tip) 1 (Node Tip 5 Tip)) (2::int) (Node Tip 3 Tip))"
  
fun get::"int tree \<Rightarrow> int" where
  "get Tip = 0"|
  "get (Node l v r) = v"
  
value "get (Node Tip 7 Tip)"
  
fun ord::"int tree \<Rightarrow> bool" where
  "ord Tip = True"|
  "ord (Node Tip v Tip) = True"|
  "ord (Node l v Tip) = (if (ord l)\<and>((get l) < v) then True else False)"|
  "ord (Node Tip v r) = (if (ord r)\<and>(v < (get r)) then True else False)"|
  "ord (Node l v r) = (if (ord l)\<and>(ord r)\<and>((get l)<v)\<and>(v<(get r)) then True else False)"
  
value "ord (Node (Node Tip 2 Tip) 4 Tip)"
value "ord (Node (Node (Node Tip 1 Tip) 2 (Node Tip 6 Tip)) 5 (Node Tip 6 Tip))"
 
fun ins::"int \<Rightarrow> int tree \<Rightarrow> int tree" where
  "ins x Tip = Node Tip x Tip"|
  "ins x (Node l v r) = (if (x=v) then (Node l v r) else (if (x<v) then (Node (ins x l) v r) else (Node l v (ins x r))))"

value "ins 3 (Node (Node Tip 2 Tip) 4 Tip)"
  
lemma ex301a: "set (ins x t) = {x} \<union> set t"
  apply(induction t arbitrary: x)
   apply(auto simp add:algebra_simps)
  done
    
    
lemma ex301b: "ord t \<Longrightarrow> ord (ins i t)"
  apply(induction t arbitrary: i)
   apply(auto simp add:algebra_simps)
  sorry
    

    
    
  
  
end
  