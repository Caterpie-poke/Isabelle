theory day1
  imports Main
begin
(*datatype bool = True | False*)
fun nnot :: "bool \<Rightarrow> bool" where
  "nnot True = False" |
  "nnot False = True"
value "nnot True"

fun conj :: "bool \<Rightarrow> bool \<Rightarrow> bool" where
  "conj True True = True"|
  "conj _ _ = False"
value "conj True False"

(*datatype nat = Zero | Suc nat*)
(*self make is harm*)
value "Zero"
fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "add 0 n = n"|
  "add (Suc m) n = Suc(add m n)"
value "add (Suc (Suc 0))(Suc 0)"

lemma add_02[simp]: "add m 0 = m"
  apply(induction m)
  apply(auto)
  done
    
thm add_02(*you can check theorem*)
  
lemma add_inc[simp]: "add n (Suc m) = Suc (add n m)"
  apply(induction n)
   apply(auto)
  done
    
(*ex2.2*)
lemma add_comm[simp]: "add m n = add n m"
  apply(induction n)
    apply(simp)
  apply(auto)
  done
    
lemma add_exch[simp]: "add (add x y) z = add x (add y z)"
  apply(induction x)
   apply(auto)
  done
    
fun double::"nat \<Rightarrow> nat" where
  "double 0 = 0"|
  "double (Suc n) = Suc(Suc (double n))"
  value "double (Suc (Suc 0))"
    
lemma double_add: "double m = add m m"
  apply(induction m)
   apply(auto)
  done
    
(*datatype 'a list = Nil | Cons 'a "'a list"*)
value "Cons (Suc Zero) (Cons Zero Nil)"
value "Cons True (Cons False (Cons True Nil))"
  
fun app::"'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "app Nil ys = ys"|
  "app (Cons x xs) ys = Cons x (app xs ys)"
  
value "app (Cons True (Cons True Nil))(Cons False Nil)"
  
fun rev::"'a list \<Rightarrow> 'a list" where
  "rev Nil = Nil"|
  "rev (Cons x xs) = app (rev xs) (Cons x Nil)"
  
value "rev (Cons True (Cons False (Cons True (Cons False Nil))))"
  
lemma revrev_rev[simp]: "rev (app left right) = app (rev left)(rev right)"
  sorry
  
lemma rev_def[simp]: "rev (rev m) = m"
  sorry
  
(*Exercise 2.3*)
fun count::"'a \<Rightarrow> 'a list \<Rightarrow> nat" where
  "count v Nil = 0"|
  "count v (Cons x xs) = (if (v = x) then (Suc (count v xs)) else (count v xs))"
  
value "count True (Cons True (Cons False (Cons True Nil)))"
  value "length (Cons True (Cons True Nil))"
  
lemma count_less[simp]: "count x xs \<le> length xs"
  apply(induction xs)
   apply(auto)
  done
    
(*Exercise 2.5*)
fun sum_upto::"nat \<Rightarrow> nat" where
  "sum_upto 0 = 0"|
  "sum_upto (Suc x) = (Suc x) + (sum_upto x)"
  
value "sum_upto (Suc (Suc (Suc 0)))"
  value "(Suc 0)*2"
  
lemma summer: "sum_upto n = n * (n + 1) div 2"
  apply(induction n)
   apply(auto)
  done
    
fun even::"nat \<Rightarrow> bool" where
  "even 0 = True"|
  "even (Suc x) = (if (even x) then False else True)"
 
fun match::"bool \<Rightarrow> bool \<Rightarrow> bool" where
  "match True True = True"|
  "match False False = True"|
  "match _ _ = False"
 
lemma mid[simp]: "even (a + b) = match (even a)(even b)"
  apply(induction a)
    apply(induction b)
    apply(auto)
  sorry
    
  
lemma winter: "even (Suc(Suc(Suc(Suc 0))) * n) = True"
  apply(induction n)
   apply(auto)
  done
    
(*2.8*)
fun intersperse::" 'a \<Rightarrow> 'a list \<Rightarrow> 'a list " where
  "intersperse _ [] = []"|
  "intersperse a [x] = [x]"|
  "intersperse a (x # xs) = x # a # (intersperse a xs)"
    

    

    
end
  