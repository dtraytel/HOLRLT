(*  Title:      HOL/ex/PresburgerEx.thy
    Author:     Amine Chaieb, TU Muenchen
*)

section \<open>Some examples for Presburger Arithmetic\<close>

theory PresburgerEx
imports MainRLT
begin

lemma "\<And>m n ja ia. \<lbrakk>\<not> m \<le> j; \<not> (n::nat) \<le> i; (e::nat) \<noteq> 0; Suc j \<le> ja\<rbrakk> \<Longrightarrow> \<exists>m. \<forall>ja ia. m \<le> ja \<longrightarrow> (if j = ja \<and> i = ia then e else 0) = 0" by presburger
lemma "(0::nat) < emBits mod 8 \<Longrightarrow> 8 + emBits div 8 * 8 - emBits = 8 - emBits mod 8" 
by presburger
lemma "(0::nat) < emBits mod 8 \<Longrightarrow> 8 + emBits div 8 * 8 - emBits = 8 - emBits mod 8" 
by presburger

theorem "(\<forall>(y::int). 3 dvd y) ==> \<forall>(x::int). b < x --> a \<le> x"
  by presburger

theorem "!! (y::int) (z::int) (n::int). 3 dvd z ==> 2 dvd (y::int) ==>
  (\<exists>(x::int).  2*x =  y) & (\<exists>(k::int). 3*k = z)"
  by presburger

theorem "!! (y::int) (z::int) n. Suc(n::nat) < 6 ==>  3 dvd z ==>
  2 dvd (y::int) ==> (\<exists>(x::int).  2*x =  y) & (\<exists>(k::int). 3*k = z)"
  by presburger

theorem "\<forall>(x::nat). \<exists>(y::nat). (0::nat) \<le> 5 --> y = 5 + x "
  by presburger

text\<open>Slow: about 7 seconds on a 1.6GHz machine.\<close>
theorem "\<forall>(x::nat). \<exists>(y::nat). y = 5 + x | x div 6 + 1= 2"
  by presburger

theorem "\<exists>(x::int). 0 < x"
  by presburger

theorem "\<forall>(x::int) y. x < y --> 2 * x + 1 < 2 * y"
  by presburger
 
theorem "\<forall>(x::int) y. 2 * x + 1 \<noteq> 2 * y"
  by presburger
 
theorem "\<exists>(x::int) y. 0 < x  & 0 \<le> y  & 3 * x - 5 * y = 1"
  by presburger

theorem "~ (\<exists>(x::int) (y::int) (z::int). 4*x + (-6::int)*y = 1)"
  by presburger

theorem "\<forall>(x::int). b < x --> a \<le> x"
  apply (presburger elim)
  oops

theorem "~ (\<exists>(x::int). False)"
  by presburger

theorem "\<forall>(x::int). (a::int) < 3 * x --> b < 3 * x"
  apply (presburger elim)
  oops

theorem "\<forall>(x::int). (2 dvd x) --> (\<exists>(y::int). x = 2*y)"
  by presburger 

theorem "\<forall>(x::int). (2 dvd x) --> (\<exists>(y::int). x = 2*y)"
  by presburger 

theorem "\<forall>(x::int). (2 dvd x) = (\<exists>(y::int). x = 2*y)"
  by presburger 

theorem "\<forall>(x::int). ((2 dvd x) = (\<forall>(y::int). x \<noteq> 2*y + 1))"
  by presburger 

theorem "~ (\<forall>(x::int). 
            ((2 dvd x) = (\<forall>(y::int). x \<noteq> 2*y+1) | 
             (\<exists>(q::int) (u::int) i. 3*i + 2*q - u < 17)
             --> 0 < x | ((~ 3 dvd x) &(x + 8 = 0))))"
  by presburger
 
theorem "~ (\<forall>(i::int). 4 \<le> i --> (\<exists>x y. 0 \<le> x & 0 \<le> y & 3 * x + 5 * y = i))"
  by presburger

theorem "\<forall>(i::int). 8 \<le> i --> (\<exists>x y. 0 \<le> x & 0 \<le> y & 3 * x + 5 * y = i)"
  by presburger

theorem "\<exists>(j::int). \<forall>i. j \<le> i --> (\<exists>x y. 0 \<le> x & 0 \<le> y & 3 * x + 5 * y = i)"
  by presburger

theorem "~ (\<forall>j (i::int). j \<le> i --> (\<exists>x y. 0 \<le> x & 0 \<le> y & 3 * x + 5 * y = i))"
  by presburger

theorem "(\<exists>m::nat. n = 2 * m) --> (n + 1) div 2 = n div 2"
  by presburger

text\<open>This following theorem proves that all solutions to the
recurrence relation $x_{i+2} = |x_{i+1}| - x_i$ are periodic with
period 9.  The example was brought to our attention by John
Harrison. It does does not require Presburger arithmetic but merely
quantifier-free linear arithmetic and holds for the rationals as well.

Warning: it takes (in 2006) over 4.2 minutes!\<close>

lemma "\<lbrakk> x3 = \<bar>x2\<bar> - x1; x4 = \<bar>x3\<bar> - x2; x5 = \<bar>x4\<bar> - x3;
         x6 = \<bar>x5\<bar> - x4; x7 = \<bar>x6\<bar> - x5; x8 = \<bar>x7\<bar> - x6;
         x9 = \<bar>x8\<bar> - x7; x10 = \<bar>x9\<bar> - x8; x11 = \<bar>x10\<bar> - x9 \<rbrakk>
 \<Longrightarrow> x1 = x10 & x2 = (x11::int)"
by arith

end
