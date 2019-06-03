theory special_exp_day2
  imports Main
begin

fun sum :: "nat => nat"
  where "sum 0 = 0"
  | "sum (Suc n) = Suc n + sum n"
    
value "sum 2"
value "sum (Suc (Suc 0))"
value "sum (Suc (Suc (Suc 0)))"
value "sum 3"
  
theorem "\<forall>n  :: nat. 2 * sum n = n * ( n + 1 )"
proof
  fix n :: nat
  show "2 * special_exp_day2.sum n = n * ( n + 1 )"
  proof (induction n)
    case 0
    then show "2 * special_exp_day2.sum 0 = 0 * ( 0 + 1 )" by simp
  next
  case (Suc n)
  then show "2 *special_exp_day2.sum (Suc n) = Suc n * ( (Suc n) + 1 )" 
    by (smt Suc_eq_plus1 add_mult_distrib2 crossproduct_noteq mult_2 nat_mult_1_right semiring_normalization_rules(22) semiring_normalization_rules(3) special_exp_day2.sum.simps(2))
qed
qed
    
  export_code special_exp_day2.sum in Scala
  
end