theory valueTest
  imports Main
begin
value "[1,1,(1::int)]"
value "1+(1::int)"
value "True"
value "(\<lambda> x. x) (2::int)"
value "(\<lambda> x. \<not>x) (True)"
value "let f = (\<lambda> x. x) in f (4::nat)"
value "let inc = (\<lambda> x. x+1) in (inc \<circ> inc) (1::int)"
end
  