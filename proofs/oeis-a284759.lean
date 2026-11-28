import OMAStatements.S_oeis_a284759
import Mathlib

/-! Counterexample to Meštrović's cubic conjecture, OEIS A284759.
The witness 409407431 has three coprime factors. The complete even-power
sum for each factor vanishes modulo its square. All three finite
computations use kernel-checked natural-number arithmetic. -/

namespace OMA.CubicBridge284759
open Finset Nat

private theorem blocks {R : Type*} [AddCommMonoid R] (f : ℕ→R) (m k : ℕ) :
    (∑i∈range (m*k),f i)=∑j∈range k,∑i∈range m,f (m*j+i) := by
  induction k with
  | zero=>simp
  | succ k ih=>rw [Nat.mul_succ,sum_range_succ,sum_range_add,ih]

private theorem quad {R : Type*} [CommRing R] (x y:R) (hy:y^3=0) (e:ℕ) :
    (x+y)^e=x^e+e*x^(e-1)*y+(e.choose 2:R)*x^(e-2)*y^2 := by
  cases e with
  | zero=>simp
  | succ e=>
    cases e with
    | zero=>simp
    | succ a=>
      induction a with
      | zero=>norm_num [pow_two];ring
      | succ a ih=>
        rw [pow_succ (x+y),ih,Nat.choose_succ_succ (a+2) 1]
        simp only [Nat.choose_one_right,Nat.cast_add,Nat.cast_one,Nat.succ_sub_succ_eq_sub,
          Nat.sub_zero,Nat.cast_ofNat,pow_succ]
        linear_combination ((a+2).choose 2:R)*x^a*hy

private theorem mirror {R : Type*} [AddCommMonoid R] (n:ℕ) (f:ℕ→R) :
    (∑i∈Ico 1 n,f (n-i))=∑i∈Ico 1 n,f i := by
  apply sum_bij' (fun i _=>n-i) (fun i _=>n-i)
  all_goals intro i hi;obtain ⟨lo,hi⟩:=mem_Ico.mp hi
  all_goals first | exact mem_Ico.mpr ⟨by omega,by omega⟩ | omega | rfl

private theorem ico_range {f:ℕ→ℕ} {n:ℕ} (np:0<n) (z:f 0=0) :
    (∑i∈Ico 1 n,f i)=∑i∈range n,f i := by
  simpa [z] using sum_range_add_sum_Ico f np

private theorem odd_sum {n e:ℕ} (on:Odd n) (oe:Odd e) : n∣∑i∈Ico 1 n,i^e := by
  have ref:=mirror n (fun i:ℕ=>(i:ZMod n)^e)
  have rev (i) (hi:i∈Ico 1 n) : ((n-i:ℕ):ZMod n)^e = -(i:ZMod n)^e := by
    rw [Nat.cast_sub (mem_Ico.mp hi).2.le,ZMod.natCast_self,zero_sub,oe.neg_pow]
  rw [sum_congr rfl rev,sum_neg_distrib] at ref
  have two : 2*(∑i∈Ico 1 n,(i:ZMod n)^e)=0 := by linear_combination -ref
  apply (Nat.coprime_two_right.mpr on).dvd_of_dvd_mul_left
  exact (ZMod.natCast_eq_zero_iff _ _).mp (by push_cast;exact two)

private theorem reflect3 {n e : ℕ} (on:Odd n) (oe:Odd e) (big:3≤e) :
    2*(∑i∈Ico 1 n,(i:ZMod (n^3))^e)=
      (n:ZMod (n^3))*e*(∑i∈Ico 1 n,(i:ZMod (n^3))^(e-1)) := by
  let R:=ZMod (n^3)
  have z : (n:R)^3=0 := by rw [←Nat.cast_pow];exact ZMod.natCast_self _
  have ev : Even (e-1) := by obtain ⟨b,hb⟩:=oe;exact ⟨b,by omega⟩
  have od : Odd (e-2) := by obtain ⟨b,hb⟩:=oe;exact ⟨b-1,by omega⟩
  have vanish : (n:R)^2*(∑i∈Ico 1 n,(i:R)^(e-2))=0 := by
    simp only [←Nat.cast_pow,←Nat.cast_sum,←Nat.cast_mul]
    apply (ZMod.natCast_eq_zero_iff _ _).mpr
    rw [show (3:ℕ)=2+1 by decide,pow_succ]
    exact Nat.mul_dvd_mul_left _ (odd_sum on od)
  rw [two_mul]
  nth_rw 1 [←mirror n (fun i=>(i:R)^e)]
  rw [←sum_add_distrib]
  calc
    _=∑i∈Ico 1 n, ((n:R)*e*(i:R)^(e-1) - (e.choose 2:R)*n^2*(i:R)^(e-2)) := by
      apply sum_congr rfl;intro i hi
      rw [Nat.cast_sub (mem_Ico.mp hi).2.le,sub_eq_neg_add,quad _ _ z,
        oe.neg_pow,ev.neg_pow,od.neg_pow];ring
    _=_ := by rw [sum_sub_distrib,←mul_sum,←mul_sum,mul_assoc _ ((n:R)^2),vanish,mul_zero,sub_zero]

/-- Sum the second-order expansion over a rectangle of complete blocks. -/
private theorem moments {R:Type*} [CommRing R] (m k e:ℕ) (zero:(m:R)^3=0) :
    (∑i∈range (m*k),(i:R)^e)=
    k*(∑i∈range m,(i:R)^e) +
    (e:R)*(m:R)*(∑j∈range k,(j:R))*(∑i∈range m,(i:R)^(e-1))+
    (e.choose 2:R)*(m:R)^2*(∑j∈range k,(j:R)^2)*(∑i∈range m,(i:R)^(e-2)) := by
  rw [blocks,sum_comm]
  calc
    _ = ∑i∈range m, ∑j∈range k, ((i:R)^e +
          ((e:R)*m*(i:R)^(e-1))*j + ((e.choose 2:R)*(m:R)^2*(i:R)^(e-2))*j^2) := by
      apply sum_congr rfl;intro i _
      apply sum_congr rfl;intro j _
      push_cast
      rw [add_comm,quad (i:R) (_*_) (by rw [mul_pow,zero,zero_mul])]
      ring
    _ = ∑i∈range m, ((k:R)*(i:R)^e +
         ((e:R)*m*(∑j∈range k,(j:R)))*(i:R)^(e-1)+
         ((e.choose 2:R)*(m:R)^2*(∑j∈range k,(j:R)^2))*(i:R)^(e-2)) := by
      apply sum_congr rfl;intro i _
      simp only [sum_add_distrib,←mul_sum,sum_const,card_range,nsmul_eq_mul]
      ring
    _ = _ := by simp only [sum_add_distrib,←mul_sum]

private theorem odd_range {n e:ℕ} (on:Odd n) (oe:Odd e) : n∣∑i∈range n,i^e := by
  rw [←ico_range on.pos (by exact zero_pow oe.pos.ne')]
  exact odd_sum on oe

private theorem first_block {p m e : ℕ} (op:Odd p) (od:Odd (e-1)) :
    (∑i∈range (p*m),(i:ZMod (p^2))^e)=(m:ZMod (p^2))*∑i∈range p,(i:ZMod (p^2))^e := by
  let R:=ZMod (p^2)
  have sq : (p:R)^2=0 := by rw [←Nat.cast_pow];exact ZMod.natCast_self _
  have lin : (p:R)*(∑i∈range p,(i:R)^(e-1))=0 := by
    have h : p^2 ∣ p*(∑i∈range p,i^(e-1)) := by
      rw [pow_two];exact Nat.mul_dvd_mul_left _ (odd_range op od)
    simpa only [Nat.cast_mul,Nat.cast_sum,Nat.cast_pow] using (ZMod.natCast_eq_zero_iff _ _).mpr h
  rw [moments (R:=R) p m e (by rw [pow_succ,sq,zero_mul]),sq];simp only [mul_zero,zero_mul,add_zero]
  linear_combination (e:R)*(∑j∈range m,(j:R))*lin

private theorem lift {n p e:ℕ} (pn:p∣n) (op:Odd p) (prev:Odd (e-1))
    (localSum:(∑i∈range p,(i:ZMod (p^2))^e)=0) : p^2∣∑i∈range n,i^e := by
  obtain ⟨m,rfl⟩:=pn
  apply (ZMod.natCast_eq_zero_iff _ _).mp
  rw [Nat.cast_sum]
  simp only [Nat.cast_pow]
  rw [first_block op prev,localSum,mul_zero]

private theorem omit_zero {m e n:ℕ} (nn:0<n) (ep:0<e)
    (h:m∣∑i∈range n,i^e) : m∣∑i∈Ico 1 n,i^e := by
  rwa [ico_range nn (by exact zero_pow ep.ne')]

/-- The three complete even-power rows imply the original cubic congruence:
lift each row in blocks, combine by coprimality, then reflect the odd sum. -/
theorem witness
    (first:(∑i∈range 59,(i:ZMod (59^2))^409407428)=0)
    (second:(∑i∈range 1559,(i:ZMod (1559^2))^409407428)=0)
    (third:(∑i∈range 4451,(i:ZMod (4451^2))^409407428)=0) :
    409407431^3∣∑i∈Icc 1 (409407431-1),i^(409407431-2) := by
  let n : ℕ := 409407431
  have nn:0<n:=by decide
  have no:Odd n:=by decide
  have rem₁:=lift (n:=n) (by decide : 59∣n) (by decide) (by decide) first
  have rem₂:=lift (n:=n) (by decide : 1559∣n) (by decide) (by decide) second
  have rem₃:=lift (n:=n) (by decide : 4451∣n) (by decide) (by decide) third
  have cq : (59^2*1559^2).Coprime (4451^2):=by decide
  have cp : (59^2).Coprime (1559^2):=by decide
  have sq:n^2∣∑i∈range n,i^409407428 := by
    rw [show n^2=59^2*1559^2*4451^2 by decide]
    exact cq.mul_dvd_of_dvd_of_dvd (cp.mul_dvd_of_dvd_of_dvd rem₁ rem₂) rem₃
  have sqI:=omit_zero nn (by decide : 0<409407428) sq
  have cube:n^3∣n*(∑i∈Ico 1 n,i^409407428) := by
    rw [pow_succ'];exact Nat.mul_dvd_mul_left _ sqI
  have zero : (n:ZMod (n^3))*(∑i∈Ico 1 n,(i:ZMod (n^3))^409407428)=0 := by
    simpa only [Nat.cast_mul,Nat.cast_sum,Nat.cast_pow] using (ZMod.natCast_eq_zero_iff _ _).mpr cube
  have ref:=reflect3 (e:=409407429) no (by decide) (by decide)
  have result : 2*(∑i∈Ico 1 n,(i:ZMod (n^3))^409407429)=0 := by
    rw [ref,show 409407429-1=409407428 by decide,mul_right_comm,zero,zero_mul]
  have two:n^3∣2*(∑i∈Ico 1 n,i^409407429) :=
    (ZMod.natCast_eq_zero_iff _ _).mp (by push_cast;exact result)
  have endpts : Icc 1 (409407431-1)=Ico 1 n := by ext x; simp [n];omega
  rw [endpts]
  exact ((Nat.coprime_two_right.mpr no).pow_left 3).dvd_of_dvd_mul_left two

end OMA.CubicBridge284759

namespace OMA.CubicCertificate284759
open Finset

private def step (m x a b:ℕ) : ℕ := (a^16 * x^b) % m

private def value (m x:ℕ) : ℕ :=
  let a := x
  let b := step m x a 8
  let c := step m x b 6
  let d := step m x c 7
  let e := step m x d 0
  let f := step m x e 15
  let g := step m x f 12
  step m x g 4

private theorem step_cast (m x a b t:ℕ) (h:(a:ZMod m)=(x:ZMod m)^t) :
    (step m x a b:ZMod m)=(x:ZMod m)^(t*16+b) := by
  simp only [step,ZMod.natCast_mod,Nat.cast_mul,Nat.cast_pow,pow_add,pow_mul,h]

private theorem value_cast (m x:ℕ) : (value m x:ZMod m)=(x:ZMod m)^409407428 := by
  unfold value
  apply step_cast _ _ _ 4 25587964
  apply step_cast _ _ _ 12 1599247
  apply step_cast _ _ _ 15 99952
  apply step_cast _ _ _ 0 6247
  apply step_cast _ _ _ 7 390
  apply step_cast _ _ _ 6 24
  apply step_cast _ _ _ 8 1
  simp

private def batch (m a:ℕ) : ℕ → ℕ
  | 0 => 0
  | n+1 => batch m a n + value m (a+n)

private theorem batch_cast (m a n:ℕ) :
    (batch m a n:ZMod m) = ∑i∈range n, ((a+i:ℕ):ZMod m)^409407428 := by
  induction n with
  | zero=>simp [batch]
  | succ n ih=>rw [batch,Nat.cast_add,ih,value_cast,sum_range_succ]

def tree (m:ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0,a,n => batch m a n % m
  | f+1,a,n =>
      (tree m f a (n/2) + tree m f (a+n/2) (n-n/2)) % m

private theorem tree_cast (m f a n:ℕ) :
    (tree m f a n:ZMod m) = ∑i∈range n, ((a+i:ℕ):ZMod m)^409407428 := by
  induction f generalizing a n with
  | zero => simp only [tree,ZMod.natCast_mod,batch_cast]
  | succ f ih =>
    rw [tree,ZMod.natCast_mod,Nat.cast_add,ih,ih]
    conv_rhs => arg 1;rw [show n=n/2+(n-n/2) by omega]
    rw [sum_range_add]
    simp only [add_assoc]

theorem finish {p f:ℕ} (check:tree (p^2) f 0 p=0) :
    (∑i∈range p,(i:ZMod (p^2))^409407428)=0 := by
  simpa only [tree_cast,zero_add,Nat.cast_zero] using congrArg (fun t:ℕ=>(t:ZMod (p^2))) check

end OMA.CubicCertificate284759

namespace OMA.CubicRows284759
open Finset OMA.CubicCertificate284759

set_option maxRecDepth 8192 in
private theorem r59_0_0 : tree 3481 0 0 59=0 := by decide +kernel

theorem row59 : (∑i∈range 59,(i:ZMod (59^2))^409407428)=0 := finish r59_0_0

set_option maxRecDepth 8192 in
private theorem r1559_0_0 : tree 2430481 0 0 389=1089229 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem r1559_0_389 : tree 2430481 0 389 390=1794150 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem r1559_1_0 : tree 2430481 1 0 779=452898 := by rw [tree,r1559_0_0,r1559_0_389]

set_option maxRecDepth 8192 in
private theorem r1559_0_779 : tree 2430481 0 779 390=940282 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem r1559_0_1169 : tree 2430481 0 1169 390=1037301 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem r1559_1_779 : tree 2430481 1 779 780=1977583 := by rw [tree,r1559_0_779,r1559_0_1169]

set_option maxRecDepth 8192 in
private theorem r1559_2_0 : tree 2430481 2 0 1559=0 := by rw [tree,r1559_1_0,r1559_1_779]

theorem row1559 : (∑i∈range 1559,(i:ZMod (1559^2))^409407428)=0 := finish r1559_2_0

set_option maxRecDepth 8192 in
private theorem r4451_0_0 : tree 19811401 0 0 278=13569437 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem r4451_0_278 : tree 19811401 0 278 278=8576304 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem r4451_1_0 : tree 19811401 1 0 556=2334340 := by rw [tree,r4451_0_0,r4451_0_278]

set_option maxRecDepth 8192 in
private theorem r4451_0_556 : tree 19811401 0 556 278=1501239 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem r4451_0_834 : tree 19811401 0 834 278=8091446 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem r4451_1_556 : tree 19811401 1 556 556=9592685 := by rw [tree,r4451_0_556,r4451_0_834]

set_option maxRecDepth 8192 in
private theorem r4451_2_0 : tree 19811401 2 0 1112=11927025 := by rw [tree,r4451_1_0,r4451_1_556]

set_option maxRecDepth 8192 in
private theorem r4451_0_1112 : tree 19811401 0 1112 278=16427160 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem r4451_0_1390 : tree 19811401 0 1390 278=1979117 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem r4451_1_1112 : tree 19811401 1 1112 556=18406277 := by rw [tree,r4451_0_1112,r4451_0_1390]

set_option maxRecDepth 8192 in
private theorem r4451_0_1668 : tree 19811401 0 1668 278=11573378 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem r4451_0_1946 : tree 19811401 0 1946 279=7204327 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem r4451_1_1668 : tree 19811401 1 1668 557=18777705 := by rw [tree,r4451_0_1668,r4451_0_1946]

set_option maxRecDepth 8192 in
private theorem r4451_2_1112 : tree 19811401 2 1112 1113=17372581 := by rw [tree,r4451_1_1112,r4451_1_1668]

set_option maxRecDepth 8192 in
private theorem r4451_3_0 : tree 19811401 3 0 2225=9488205 := by rw [tree,r4451_2_0,r4451_2_1112]

set_option maxRecDepth 8192 in
private theorem r4451_0_2225 : tree 19811401 0 2225 278=14813253 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem r4451_0_2503 : tree 19811401 0 2503 278=1184437 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem r4451_1_2225 : tree 19811401 1 2225 556=15997690 := by rw [tree,r4451_0_2225,r4451_0_2503]

set_option maxRecDepth 8192 in
private theorem r4451_0_2781 : tree 19811401 0 2781 278=11590021 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem r4451_0_3059 : tree 19811401 0 3059 279=8721160 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem r4451_1_2781 : tree 19811401 1 2781 557=499780 := by rw [tree,r4451_0_2781,r4451_0_3059]

set_option maxRecDepth 8192 in
private theorem r4451_2_2225 : tree 19811401 2 2225 1113=16497470 := by rw [tree,r4451_1_2225,r4451_1_2781]

set_option maxRecDepth 8192 in
private theorem r4451_0_3338 : tree 19811401 0 3338 278=19636521 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem r4451_0_3616 : tree 19811401 0 3616 278=18643185 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem r4451_1_3338 : tree 19811401 1 3338 556=18468305 := by rw [tree,r4451_0_3338,r4451_0_3616]

set_option maxRecDepth 8192 in
private theorem r4451_0_3894 : tree 19811401 0 3894 278=14008953 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem r4451_0_4172 : tree 19811401 0 4172 279=971270 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem r4451_1_3894 : tree 19811401 1 3894 557=14980223 := by rw [tree,r4451_0_3894,r4451_0_4172]

set_option maxRecDepth 8192 in
private theorem r4451_2_3338 : tree 19811401 2 3338 1113=13637127 := by rw [tree,r4451_1_3338,r4451_1_3894]

set_option maxRecDepth 8192 in
private theorem r4451_3_2225 : tree 19811401 3 2225 2226=10323196 := by rw [tree,r4451_2_2225,r4451_2_3338]

set_option maxRecDepth 8192 in
private theorem r4451_4_0 : tree 19811401 4 0 4451=0 := by rw [tree,r4451_3_0,r4451_3_2225]

theorem row4451 : (∑i∈range 4451,(i:ZMod (4451^2))^409407428)=0 := finish r4451_4_0

end OMA.CubicRows284759

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a284759.main) := by
  intro conjecture
  have witness := OMA.CubicBridge284759.witness OMA.CubicRows284759.row59
    OMA.CubicRows284759.row1559 OMA.CubicRows284759.row4451
  have prime := ((conjecture 409407431 (by decide)).mp witness).1
  exact Nat.not_prime_of_dvd_of_lt (m:=59) (by decide) (by decide) (by decide) prime
