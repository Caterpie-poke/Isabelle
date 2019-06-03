theory ex211
  imports Main
begin
datatype exp = Var | Const "int" | Add "exp" "exp" | Mult "exp" "exp"
  
value "Const 2"
value "Add (Var) (Const 3)"
  
fun eval::"exp \<Rightarrow> int \<Rightarrow> int" where
  "eval Var n = n"|
  "eval (Const i) n = i"|
  "eval (Add l r) n = (eval l n) + (eval r n)"|
  "eval (Mult l r) n = (eval l n) * (eval r n)"
  
value "eval (Var) 2"
value "eval (Const 1) 3"
value "eval (Add Var (Mult Var (Const 2))) 4"
  
fun evalp::"int list \<Rightarrow> int \<Rightarrow> int" where
  "evalp [] n = 0"|
  "evalp [x] n = x"|
  "evalp (x#xs) n = x + n * (evalp xs n)"
  
value "evalp [1,2,3] 2"
  
fun adlist::"int list \<Rightarrow> int list \<Rightarrow> int list" where
  "adlist [] [] = []"|
  "adlist [] (y#ys) = (y#ys)"|
  "adlist (x#xs) [] = (x#xs)"|
  "adlist [x] [y] = [x+y]"|
  "adlist [x] (y#ys) = ((x+y)#ys)"|
  "adlist (x#xs) [y] = ((x+y)#xs)"|
  "adlist (x#xs) (y#ys) = ((x+y)#(adlist xs ys))"
  
value "adlist [0,1,2] [3,4,5]"
  
fun lm::"int list \<Rightarrow> int \<Rightarrow> int list" where
  "lm [] n = []"|
  "lm (x#xs) n = (x*n)#(lm xs n)"
  
value "lm [1,2,3] 2"
  
fun mllist::"int list \<Rightarrow> int list \<Rightarrow> int list" where
  "mllist [] [] = []"|
  "mllist [] y = []"|
  "mllist x [] = []"|  
  "mllist x (y#ys) = adlist (lm x y)(mllist (0#x)(ys))"
  
value "mllist [1,2,1][3,1]"
  
fun coeffs::"exp \<Rightarrow> int list" where
  "coeffs (Const i) = [i]"|
  "coeffs Var = [0,1]"|
  "coeffs (Add l r) = adlist (coeffs l) (coeffs r)"|
  "coeffs (Mult l r) = mllist (coeffs l) (coeffs r)"
  
value "evalp (coeffs (Add Var (Mult Var (Const 2)))) 6"
value "eval (Add Var (Mult Var (Const 2))) 6"
  
lemma ex210: "evalp (coeffs e) x = eval e x"
  apply(induction x arbitrary: e)
   apply(auto simp add: algebra_simps)
    sorry
    
    
  
end
  