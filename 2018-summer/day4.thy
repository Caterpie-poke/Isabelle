theory day4
  imports Main
begin
lemma IsarTest: "((P\<longrightarrow>Q) \<and> P) \<longrightarrow> Q"
proof
  assume 0: "((P\<longrightarrow>Q) \<and> P)"
  then have 1: "P\<longrightarrow>Q" by (simp)
  from 0 have 2: "P" ..
  from 1 2 show "Q" ..
qed
  (*
from this = then
then show = thus
then have = hence
from 0 = by (simp add:0)
    *)
  
end
  