import OMAReductions.R_OeisA245212_conjecture_R1_H1_R2

import Mathlib.Data.Nat.Totient



/-! Effective first resonance for the odd case of A245212. -/

section

/- An explicit uniform distance from a rational target to Euler products
of bounded length, provided none of their subproducts hits the target. -/
namespace OMA.CofactorEulerSeparation245212
open Finset Nat

def num (s : Finset ℕ) := ∏p∈s,p
def den (s : Finset ℕ) := ∏p∈s,(p-1)
def gap (A H : ℕ) (s : Finset ℕ) := ((A:ℤ)*num s-(H:ℤ)*den s).natAbs
def miss (A H : ℕ) (s : Finset ℕ) := ∀t⊆s,A*num t≠H*den t

def budget (A : ℕ) : ℕ→ℕ
  | 0=>1
  | r+1=>let b:=budget A r;max (2*b) ((2+2*A*2^r*b)^(r+1))

private theorem budget_pos (A r : ℕ) : 0<budget A r := by
  induction r with
  | zero=>simp [budget]
  | succ r ih=>exact (Nat.mul_pos (by decide) ih).trans_le (le_max_left _ _)

private theorem gap_pos {A H : ℕ} {s : Finset ℕ} (m : A*num s≠H*den s) : 0<gap A H s := by
  apply Int.natAbs_pos.mpr
  intro z
  exact m (by exact_mod_cast sub_eq_zero.mp z)

private theorem size {s : Finset ℕ} (positive : ∀p∈s,2≤p) : num s≤2^s.card*den s := by
  calc
    num s ≤ ∏p∈s,(2*(p-1)) := by
      apply prod_le_prod'
      intro p mem;have:=positive p mem;omega
    _ = _ := by simp [den,prod_mul_distrib]

private theorem spread {u x z : ℤ} (u0 : 0≤u) (x0 : 0≤x) (large : 2*x≤u*|z|) :
    u*|z|≤2*|u*z+x| := by
  have tri:=abs_add_le (u*z+x) (-x)
  rw [add_neg_cancel_right,abs_mul,abs_of_nonneg u0,abs_neg,abs_of_nonneg x0] at tri
  linarith

theorem separated (A H K : ℕ) (s : Finset ℕ) (card : s.card≤K)
    (positive : ∀p∈s,2≤p) (apart : miss A H s) : den s≤budget A K*gap A H s := by
  classical
  induction K generalizing s with
  | zero=>
    have empty : s=∅:=card_eq_zero.mp (by omega)
    subst s
    simpa [den,budget] using Nat.succ_le_of_lt (gap_pos (apart ∅ (by simp)))
  | succ K ih=>
    by_cases empty : s=∅
    · subst s
      simpa [den] using Nat.succ_le_of_lt (Nat.mul_pos (budget_pos A (K+1)) (gap_pos (apart ∅ (by simp))))
    have nonempty:=nonempty_iff_ne_empty.mpr empty
    let q:=s.max' nonempty
    have mem : q∈s:=s.max'_mem _
    have qp:=positive q mem
    let t:=s.erase q
    have sub : t⊆s:=erase_subset _ _
    have oldBound:=ih t (by dsimp [t];rw [card_erase_of_mem mem];omega)
      (fun p hp=>positive p (sub hp)) (fun z hz=>apart z (hz.trans sub))
    have scale:=size (s:=t) (fun p hp=>positive p (sub hp))
    have tc : t.card≤K := by dsimp [t];rw [card_erase_of_mem mem];omega
    let B:=budget A K
    have U : num s=q*num t := (mul_prod_erase s (fun p=>p) mem).symm
    have V : den s=(q-1)*den t := (mul_prod_erase s (fun p=>p-1) mem).symm
    by_cases large : 2*A*2^K*B≤q-1
    · have twice : 2*A*num t≤(q-1)*gap A H t := by
        calc
          _ ≤ 2*A*(2^K*(B*gap A H t)) := Nat.mul_le_mul_left _ (scale.trans
            (Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) tc) oldBound))
          _ = (2*A*2^K*B)*gap A H t := by ring
          _ ≤ _ := Nat.mul_le_mul_right _ large
      have twiceInt : 2*((A:ℤ)*num t)≤((q-1:ℕ):ℤ)*|(A:ℤ)*num t-(H:ℤ)*den t| := by
        have cast:=Int.ofNat_le.mpr twice
        simpa only [gap,Nat.cast_mul,Nat.cast_ofNat,Int.natCast_natAbs,mul_assoc] using cast
      have pre:=spread (u:=((q-1:ℕ):ℤ)) (x:=(A:ℤ)*num t) (z:=(A:ℤ)*num t-(H:ℤ)*den t)
        (by positivity) (by positivity) twiceInt
      have id : ((q-1:ℕ):ℤ)*((A:ℤ)*num t-(H:ℤ)*den t)+A*num t=(A:ℤ)*num s-(H:ℤ)*den s := by
        rw [U,V];push_cast [Nat.cast_sub (show 1≤q by omega)];ring
      rw [id] at pre
      have control : (q-1)*gap A H t≤2*gap A H s := by
        apply Int.ofNat_le.mp
        simpa [gap,Int.natCast_natAbs] using pre
      calc
        den s ≤ (q-1)*(B*gap A H t) := V ▸ Nat.mul_le_mul_left _ oldBound
        _ = B*((q-1)*gap A H t) := by ring
        _ ≤ B*(2*gap A H s) := Nat.mul_le_mul_left _ control
        _ = (2*B)*gap A H s := by ring
        _ ≤ _ := Nat.mul_le_mul_right _ (le_max_left _ _)
    · let J:=2+2*A*2^K*B
      have lo : 0<J := by dsimp [J];omega
      have modest : den s≤J^(K+1) := by
        refine (prod_le_pow_card s (fun p=>p-1) J ?_).trans (Nat.pow_le_pow_right lo card)
        intro p hp
        have below : p≤q:=s.le_max' p hp
        dsimp [J];omega
      have nonzero := gap_pos (apart s (Subset.rfl))
      exact modest.trans ((le_max_right _ _).trans (Nat.le_mul_of_pos_right _ nonzero))


theorem miss_odd {A H : ℕ} {s : Finset ℕ} (oa : Odd A) (eh : Even H)
    (pr : ∀p∈s,Odd p) : miss A H s := by
  intro t ht eqn
  have all (u : Finset ℕ) (ho : ∀p∈u,Odd p) : Odd (num u) := by
    induction u using Finset.induction_on with
    | empty=>simp [num]
    | @insert p u fresh ih=>
      rw [num,prod_insert fresh]
      exact (ho p (mem_insert_self ..)).mul (ih (fun q hq=>ho q (mem_insert_of_mem hq)))
  have left:=oa.mul (all t (fun p hp=>pr p (ht hp)))
  rw [eqn] at left
  exact (Nat.not_even_iff_odd.mpr left) (eh.mul_right _)

theorem miss_avoids {A H : ℕ} {s : Finset ℕ} (different : A≠H)
    (pr : ∀p∈s,p.Prime) (avoid : ∀p∈s,¬p∣H) : miss A H s := by
  intro t ht eqn
  by_cases empty : t=∅
  · exact different (by simpa [empty,num,den] using eqn)
  have nonempty:=nonempty_iff_ne_empty.mpr empty
  let q:=t.max' nonempty
  have mq : q∈t:=t.max'_mem _
  have pq:=pr q (ht mq)
  have dvd : q∣H*den t := eqn ▸ dvd_mul_of_dvd_right (dvd_prod_of_mem (fun p=>p) mq) A
  rcases pq.dvd_mul.mp dvd with bad|denom
  · exact avoid q (ht mq) bad
  obtain ⟨p,mp,dv⟩:=(pq.prime.dvd_finsetProd_iff (fun j=>j-1)).mp denom
  have upper : p≤q:=t.le_max' _ mp
  have lower:=(pr p (ht mp)).one_lt
  have:=Nat.le_of_dvd (show 0<p-1 by omega) dv
  omega

/-- A computable absolute gap, uniform over all allowed support sets. -/
theorem rational_gap {A H K : ℕ} {s : Finset ℕ} (card : s.card≤K)
    (positive : ∀p∈s,2≤p) (apart : miss A H s) :
    1 ≤ (budget A K:ℚ)*|(A:ℚ)*((num s:ℚ)/den s)-H| := by
  have n:=separated A H K s card positive apart
  have dp : 0<den s := prod_pos (fun p hp=>by have:=positive p hp;omega)
  have v : (0:ℚ)<den s := by exact_mod_cast dp
  let u : ℤ:=(A:ℤ)*num s-(H:ℤ)*den s
  have cast : (den s:ℚ)≤(budget A K:ℚ)*|(u:ℚ)| := by
    have intBound:=Int.ofNat_le.mpr n
    simp only [gap,Nat.cast_mul,Int.natCast_natAbs] at intBound
    dsimp [u]
    exact_mod_cast intBound
  have eqn : ((A:ℚ)*((num s:ℚ)/den s)-H)*(den s:ℚ)=(u:ℚ) := by
    dsimp [u];push_cast;field_simp
  apply (mul_le_mul_iff_of_pos_right v).mp
  have ab:=congrArg (fun z:ℚ=>|z|) eqn
  rw [abs_mul,abs_of_pos v] at ab
  simpa only [one_mul,mul_assoc,ab] using cast

end OMA.CofactorEulerSeparation245212

end

section

/- Exact interval certificates for the mixed 7-smooth A245212 family.
An absent upper endpoint represents the limit at an unbounded exponent. -/
namespace OMA.Smooth245212
open Finset

def Y (p : ℕ) : Option ℕ → ℚ
  | none => 0
  | some e => (((p:ℚ)⁻¹^(e+1)-1)/((p:ℚ)⁻¹-1))/(e+1)

def X (p : ℕ) (e : Option ℕ) : ℚ := 1+(1-Y p e)/((p:ℚ)-1)

theorem y_avg {p : ℕ} (hp : 1<p) (e : ℕ) :
    Y p (some e)=(∑ i ∈ range (e+1), (p:ℚ)⁻¹^i)/((e:ℚ)+1) := by
  rw [geom_sum_eq (x := (p:ℚ)⁻¹) (by
    have : (1:ℚ)<p := by exact_mod_cast hp
    exact (inv_lt_one_of_one_lt₀ this).ne)]; rfl

theorem y_nonneg {p : ℕ} (hp : 1<p) (e : Option ℕ) : 0≤Y p e := by
  cases e with
  | none => rfl
  | some e => rw [y_avg hp]; positivity

theorem y_anti {p : ℕ} (hp : 1<p) : Antitone (fun e : ℕ => Y p (some e)) := by
  have pr : (1:ℚ)<p := by exact_mod_cast hp
  have lp := (inv_lt_one_of_one_lt₀ pr).le
  have pos : 0≤(p:ℚ)⁻¹ := by positivity
  apply antitone_nat_of_succ_le
  intro e
  simp only [y_avg hp,Nat.cast_add,Nat.cast_one]
  rw [sum_range_succ _ (e+1),div_le_div_iff₀ (by positivity) (by positivity)]
  have small : (∑ _i ∈ range (e+1), (p:ℚ)⁻¹^(e+1)) ≤ ∑ i∈range (e+1), (p:ℚ)⁻¹^i :=
    sum_le_sum (fun i hi => pow_le_pow_of_le_one pos lp (mem_range.mp hi).le)
  simp only [sum_const,card_range,nsmul_eq_mul,Nat.cast_add,Nat.cast_one] at small
  nlinarith only [small]

theorem y_one {p : ℕ} (hp : 1<p) (e : Option ℕ) : Y p e ≤ 1 := by
  cases e with
  | none => norm_num [Y]
  | some e =>
    have h := y_anti hp (Nat.zero_le e)
    simpa [y_avg hp] using h

theorem x_nonneg {p : ℕ} (hp : 1<p) (e : Option ℕ) : 0≤X p e := by
  have pr : (1:ℚ)<p := by exact_mod_cast hp
  have := sub_nonneg.mpr (y_one hp e)
  unfold X; positivity


end OMA.Smooth245212

end

section

/- Identification of the interval score with the original weighted sum. -/
namespace OMA.Smooth245212
open Finset ArithmeticFunction Nat
open scoped ArithmeticFunction.sigma Function

def W : ArithmeticFunction ℕ := (ArithmeticFunction.id.pmul (σ 0)) * ArithmeticFunction.zeta
lemma w_mult : W.IsMultiplicative :=
  (isMultiplicative_id.pmul isMultiplicative_sigma).mul isMultiplicative_zeta
lemma w_apply (n : ℕ) : W n = ∑ d∈n.divisors, d*d.divisors.card := by
  rw [W,mul_zeta_apply]
  simp only [pmul_apply,id_apply,sigma_zero_apply]
lemma w_pow {p : ℕ} (hp : Nat.Prime p) (e : ℕ) :
    W (p^e) = ∑ j ∈ range (e+1), p^j*(j+1) := by
  rw [w_apply,Nat.sum_divisors_prime_pow hp]
  simp [Nat.divisors_prime_pow hp]

private lemma weighted (p : ℚ) (e : ℕ) :
    (p-1)*(∑ j ∈ range (e+1), p^j*((j:ℚ)+1)) =
      ((e:ℚ)+1)*p^(e+1)-∑ j ∈ range (e+1), p^j := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [sum_range_succ _ (e+1),sum_range_succ _ (e+1),mul_add,ih,pow_succ p (e+1)]
    push_cast; ring

theorem y_factor {p : ℕ} (hp : Nat.Prime p) (e : ℕ) :
    Y p (some e)*(((e:ℚ)+1)*(p:ℚ)^e) = (σ 1 (p^e) : ℚ) := by
  have pn : (p:ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [y_avg hp.one_lt,sigma_one_apply_prime_pow hp]
  push_cast
  calc
    _ = ∑ j ∈ range (e+1), (p:ℚ)⁻¹^j*(p:ℚ)^e := by rw [←sum_mul]; field_simp
    _ = ∑ j ∈ range (e+1), (p:ℚ)^(e-j) := by
      refine sum_congr rfl fun j hj => ?_
      have add : j+(e-j)=e := by have := mem_range.mp hj; omega
      calc
        _ = (p:ℚ)⁻¹^j*((p:ℚ)^j*(p:ℚ)^(e-j)) := by rw [←pow_add,add]
        _ = _ := by rw [inv_pow,←mul_assoc,inv_mul_cancel₀ (pow_ne_zero _ pn),one_mul]
    _ = _ := by simpa using sum_range_reflect (fun j => (p:ℚ)^j) (e+1)

theorem x_factor {p : ℕ} (hp : Nat.Prime p) (e : ℕ) :
    X p (some e)*(((e:ℚ)+1)*(p:ℚ)^e) = (W (p^e) : ℚ) := by
  have y := y_factor hp e
  rw [sigma_one_apply_prime_pow hp] at y
  push_cast at y
  rw [w_pow hp]; push_cast
  have pp : (1:ℚ)<p := by exact_mod_cast hp.one_lt
  have h := weighted (p:ℚ) e
  rw [pow_succ] at h
  dsimp [X]
  field_simp [sub_ne_zero.mpr pp.ne']
  linear_combination -h - y

section General
variable {ι : Type*} [Fintype ι] (p : ι → ℕ)
def total (e : ι → ℕ) : ℕ := ∏ i, p i^(e i)

end General
end OMA.Smooth245212

end

section

/- A uniform abundancy obstruction and the exclusion of constant
prime-exponent families in the A245212 divisor equality. -/
namespace OMA.Abundance245212
open OMA.Smooth245212 Finset ArithmeticFunction Nat
open scoped ArithmeticFunction.sigma

theorem balance {n : ℕ} (hn : n≠0)
    (eq : OeisA245212.a n=(σ 1 n:ℤ)) : W n+σ 1 n=2*n*(σ 0 n) := by
  have total : W n = n*n.divisors.card+∑ d∈n.properDivisors,d*d.divisors.card := by
    calc
      _ = ∑ d∈insert n n.properDivisors,d*d.divisors.card := by
        rw [Nat.insert_self_properDivisors hn,w_apply]
      _ = _ := sum_insert Nat.self_notMem_properDivisors
  unfold OeisA245212.a at eq
  zify at total ⊢
  simp only [sigma_zero_apply]
  linarith


end OMA.Abundance245212

end

section

/- The divisor score strictly increases in one prime exponent as soon as
one other prime exponent is sufficiently large. -/
namespace OMA.CapOrder245212
open Finset OMA.Smooth245212 OMA.Abundance245212

private theorem geom (p : ℕ) (hp : 1<p) (e : ℕ) :
    (∑ i∈range (e+1),p^i)<2*p^e := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [sum_range_succ _ (e+1),pow_succ]
    have := Nat.mul_le_mul_left (p^e) (show 2≤p from hp)
    omega

theorem y_short {q : ℕ} (hq : Nat.Prime q) (e : ℕ) :
    Y q (some e)*((e:ℚ)+1)<2 := by
  have h := y_factor hq e
  have l : (ArithmeticFunction.sigma 1 (q^e):ℚ)<2*(q:ℚ)^e := by
    exact_mod_cast (show ArithmeticFunction.sigma 1 (q^e)<2*q^e by
      rw [ArithmeticFunction.sigma_one_apply_prime_pow hq]; exact geom q hq.one_lt e)
  apply lt_of_mul_lt_mul_right (a:= (q:ℚ)^e)
  · linarith only [h,l]
  · positivity


end OMA.CapOrder245212

end

section

namespace OMA.CofactorCrossOriginal245212
open Nat Finset ArithmeticFunction OMA.Smooth245212
open scoped ArithmeticFunction.sigma
theorem normalized_extension {ι : Type*} [Fintype ι] {h : ℕ} {p e : ι→ℕ} (hh : 0<h) (pr : ∀i,(p i).Prime)
    (unique : Function.Injective p) (cop : ∀i,h.Coprime (p i))
    (eqn : OeisA245212.a (h*total p e)=(σ 1 (h*total p e):ℤ)) :
    ((W h:ℚ)/(h*σ 0 h:ℕ))*(∏i,X (p i) (some (e i)))+
      ((σ 1 h:ℚ)/(h*σ 0 h:ℕ))*(∏i,Y (p i) (some (e i)))=2 := by
  classical
  let z (i : ι):=p i^e i
  have pair : (↑(univ : Finset ι) : Set ι).Pairwise (fun i j=>(z i).Coprime (z j)) := by
    intro i _ j _ different
    exact (((coprime_primes (pr i) (pr j)).mpr (fun same=>different (unique same))).pow_left _).pow_right _
  have hc : h.Coprime (total p e) := coprime_prod_right_iff.mpr (fun i _=>(cop i).pow_right _)
  have nz : total p e≠0 := prod_ne_zero_iff.mpr (fun i _=>pow_ne_zero _ (pr i).ne_zero)
  have bal:=OMA.Abundance245212.balance (mul_ne_zero hh.ne' nz) eqn
  rw [w_mult.map_mul_of_coprime hc,isMultiplicative_sigma.map_mul_of_coprime hc,
    isMultiplicative_sigma.map_mul_of_coprime hc] at bal
  have wp:=IsMultiplicative.map_prod z w_mult univ pair
  have sp:=IsMultiplicative.map_prod z (isMultiplicative_sigma (k:=1)) univ pair
  have tp:=IsMultiplicative.map_prod z (isMultiplicative_sigma (k:=0)) univ pair
  change W (total p e)=_ at wp
  change σ 1 (total p e)=_ at sp
  change σ 0 (total p e)=_ at tp
  simp only [z,sigma_zero_apply_prime_pow (pr _)] at tp
  let mass : ℚ:=∏ i,(((e i:ℕ):ℚ)+1)*(p i:ℚ)^e i
  have tax : mass = (total p e:ℚ)*(σ 0 (total p e):ℚ) := by
    rw [tp,total];push_cast;dsimp [mass];rw [prod_mul_distrib];ring
  have positive : 0 < mass := by
    apply prod_pos
    intro i _
    have := (pr i).pos
    positivity
  have wprod : (∏ i,X (p i) (some (e i)))*mass=(W (total p e):ℚ) := by
    rw [wp,←prod_mul_distrib];push_cast
    exact prod_congr rfl (fun i _=>x_factor (pr i) (e i))
  have sprod : (∏ i,Y (p i) (some (e i)))*mass=(σ 1 (total p e):ℚ) := by
    rw [sp,←prod_mul_distrib];push_cast
    exact prod_congr rfl (fun i _=>y_factor (pr i) (e i))
  have D : 0<h*σ 0 h := Nat.mul_pos hh (sigma_pos 0 h hh.ne')
  have rat:=congrArg ((↑):ℕ→ℚ) bal
  push_cast at rat
  apply mul_right_cancel₀ (b:=mass) positive.ne'
  rw [add_mul,mul_assoc,mul_assoc,wprod,sprod,tax]
  field_simp [show ((h*σ 0 h:ℕ):ℚ)≠0 by exact_mod_cast D.ne']
  push_cast
  linear_combination rat


end OMA.CofactorCrossOriginal245212

end

section

/- An explicit whole-prime-power bound in the nonresonant case.
Replace large bases by 1 and small bases with large exponents by their
Euler limits. The explicitly separated subproduct cannot approximate a
solution this closely. -/
namespace OMA.CofactorEffectiveAtom245212
open Finset Nat OMA.Smooth245212 OMA.CofactorEulerSeparation245212

private theorem product_error {ι : Type*} [DecidableEq ι] (s : Finset ι) (x z : ι→ℚ)
    {w : ℚ} (wp : 0≤w) (bounds : ∀i∈s,0≤x i ∧ x i≤2 ∧ 0≤z i ∧ z i≤2 ∧ |x i-z i|≤w) :
    |(∏i∈s,x i)-(∏i∈s,z i)| ≤ s.card*(2:ℚ)^s.card*w := by
  induction s using Finset.induction_on with
  | empty=>simp
  | @insert i s fresh ih=>
    let X:=∏j∈s,x j
    let Z:=∏j∈s,z j
    have b:=bounds i (mem_insert_self ..)
    have bs (j) (hj:j∈s):=bounds j (mem_insert_of_mem hj)
    have z0 : 0≤Z:=prod_nonneg (fun j hj=>(bs j hj).2.2.1)
    have z2 : Z≤(2:ℚ)^s.card := by
      simpa [Z] using prod_le_prod (fun j hj=>(bs j hj).2.2.1) (fun j hj=>(bs j hj).2.2.2.1)
    have old:=ih bs
    change |X-Z|≤_ at old
    rw [prod_insert fresh,prod_insert fresh,card_insert_of_notMem fresh,Nat.cast_add,Nat.cast_one,pow_succ]
    change |x i*X-z i*Z|≤_
    have tri:=abs_add_le (x i*(X-Z)) ((x i-z i)*Z)
    rw [show x i*(X-Z)+(x i-z i)*Z=x i*X-z i*Z by ring,abs_mul,abs_of_nonneg b.1,
      abs_mul,abs_of_nonneg z0] at tri
    have l:=mul_le_mul b.2.1 old (abs_nonneg _) (by decide : (0:ℚ)≤2)
    have r:=mul_le_mul b.2.2.2.2 z2 z0 wp
    nlinarith only [tri,l,r,mul_nonneg (pow_nonneg (by decide : (0:ℚ)≤2) s.card) wp]

private def factor (p : ℕ) : ℚ := (p:ℚ)/(p-1:ℕ)

private theorem local_factor {p e : ℕ} (hp : p.Prime) :
    1≤X p (some e) ∧ X p (some e)≤factor p ∧ factor p≤2 ∧
    factor p-X p (some e)=Y p (some e)/((p:ℚ)-1) := by
  have hi : (1:ℚ)<p := by exact_mod_cast hp.one_lt
  have den : (0:ℚ)<p-1 := by linarith
  have two : (2:ℚ)≤p := by exact_mod_cast hp.two_le
  have y0:=y_nonneg hp.one_lt (some e)
  have y1:=y_one hp.one_lt (some e)
  have diff : factor p-X p (some e)=Y p (some e)/((p:ℚ)-1) := by
    unfold factor X;push_cast [Nat.cast_sub hp.one_le];field_simp;ring
  refine ⟨le_add_of_nonneg_right (div_nonneg (sub_nonneg.mpr y1) den.le),?_,?_,diff⟩
  · linarith only [diff,div_nonneg y0 den.le]
  · unfold factor;push_cast [Nat.cast_sub hp.one_le];apply (div_le_iff₀ den).mpr;linarith

private theorem near {p e M : ℕ} (hp : p.Prime) (avoid : p≤M+1 → M<e) :
    |X p (some e)-(if p≤M+1 then factor p else 1)|≤2/((M:ℚ)+1) := by
  obtain ⟨low,hi,_,diff⟩:=local_factor (e:=e) hp
  have h2 : (2:ℚ)≤p:=by exact_mod_cast hp.two_le
  have den : (0:ℚ)<p-1:=by linarith
  split
  next small=>
    rw [abs_of_nonpos (sub_nonpos.mpr hi),neg_sub,diff]
    have ye:=OMA.CapOrder245212.y_short hp e
    have big : (M:ℚ)+1≤e+1 := by exact_mod_cast (by have:=avoid small;omega : M+1≤e+1)
    have y0:=y_nonneg hp.one_lt (some e)
    calc
      Y p (some e)/((p:ℚ)-1) ≤ Y p (some e) := div_le_self y0 (by linarith)
      _ ≤ _ := (le_div_iff₀ (by positivity)).mpr ((mul_le_mul_of_nonneg_left big y0).trans ye.le)
  next large=>
    rw [abs_of_nonneg (sub_nonneg.mpr low)]
    unfold X
    have bound : (M:ℚ)+1≤p-1 := by
      have strong : (M:ℚ)+2≤p:=by exact_mod_cast (show M+2≤p by omega)
      linarith
    have y0:=y_nonneg hp.one_lt (some e)
    rw [add_sub_cancel_left]
    calc
      _ ≤ 1/((p:ℚ)-1) := div_le_div_of_nonneg_right (sub_le_self _ y0) den.le
      _ ≤ 1/((M:ℚ)+1) := one_div_le_one_div_of_le (by positivity) bound
      _ ≤ _ := by gcongr; norm_num

def threshold (A S K : ℕ) := budget A K*(2*A*K*2^K+2*S)

theorem alternative (A S H : ℕ) (s : Finset ℕ) (e : ℕ→ℕ) (pr : ∀p∈s,p.Prime)
    (apart : miss A H s)
    (bal : (A:ℚ)*(∏p∈s,X p (some (e p)))+S*(∏p∈s,Y p (some (e p)))=H) :
    let M:=threshold A S s.card
    (∀p∈s,e p≤M) ∨ ∃p∈s,p≤M+1 ∧ e p≤M := by
  classical
  let K:=s.card
  let M:=threshold A S K
  change (∀p∈s,e p≤M) ∨ ∃p∈s,p≤M+1 ∧ e p≤M
  by_cases allSmall : ∀p∈s,e p≤M
  · exact Or.inl allSmall
  right
  by_contra no
  push Not at allSmall
  obtain ⟨j,hj,large⟩:=allSmall
  have avoid (p) (hp:p∈s) (low:p≤M+1) : M<e p := by
    by_contra! short
    exact no ⟨p,hp,low,short⟩
  let z (p : ℕ) : ℚ:=if p≤M+1 then factor p else 1
  let t:=s.filter (fun p=>p≤M+1)
  have sub : t⊆s:=filter_subset _ _
  have proxy : (∏p∈s,z p)=(num t:ℚ)/den t := by
    rw [show (∏p∈s,z p)=∏p∈t,factor p by simp [z,t,prod_filter]]
    unfold factor num den
    push_cast
    rw [prod_div_distrib]
  have sep:=rational_gap (A:=A) (H:=H) (K:=K) (s:=t) (card_le_card sub)
    (fun p hp=>(pr p (sub hp)).two_le) (fun u hu=>apart u (hu.trans sub))
  rw [←proxy] at sep
  have feat:=product_error s (fun p=>X p (some (e p))) z (w:=2/((M:ℚ)+1)) (by positivity)
    (fun p hp=>by
      have loc:=local_factor (e:=e p) (pr p hp)
      refine ⟨zero_le_one.trans loc.1,loc.2.1.trans loc.2.2.1,?_,?_,near (pr p hp) (avoid p hp)⟩
      · dsimp [z];split <;> first | exact (zero_le_one.trans loc.1).trans loc.2.1 | norm_num
      · dsimp [z];split <;> first | exact loc.2.2.1 | norm_num)
  let PX:=∏p∈s,X p (some (e p))
  let PY:=∏p∈s,Y p (some (e p))
  let Z:=∏p∈s,z p
  have y0 : 0≤PY:=prod_nonneg (fun p hp=>y_nonneg (pr p hp).one_lt _)
  have ylow : PY≤Y j (some (e j)) := by
    dsimp [PY];rw [←prod_erase_mul _ _ hj]
    exact mul_le_of_le_one_left (y_nonneg (pr j hj).one_lt _) (prod_le_one
      (fun p hp=>y_nonneg (pr p (mem_of_mem_erase hp)).one_lt _)
      (fun p hp=>y_one (pr p (mem_of_mem_erase hp)).one_lt _))
  have ycut := OMA.CapOrder245212.y_short (pr j hj) (e j)
  let L:ℚ:=M+1
  have lp : 0<L:=by dsimp [L];positivity
  have yl : PY*L≤2 := (mul_le_mul ylow (show L≤(e j:ℚ)+1 by dsimp [L];exact_mod_cast Nat.succ_le_succ large.le)
    lp.le (y_nonneg (pr j hj).one_lt _)).trans ycut.le
  change |PX-Z|≤K*(2:ℚ)^K*(2/L) at feat
  have xl : |PX-Z| * L≤K*2^K*2 := by
    apply (le_div_iff₀ lp).mp
    simpa [div_eq_mul_inv,mul_assoc] using feat
  change (A:ℚ)*PX+S*PY=H at bal
  change 1≤(budget A K:ℚ)*|(A:ℚ)*Z-H| at sep
  have tri:=abs_add_le ((A:ℚ)*(PX-Z)) ((S:ℚ)*PY)
  rw [show (A:ℚ)*(PX-Z)+S*PY=H-A*Z by linarith only [bal],abs_sub_comm (H:ℚ)] at tri
  simp only [abs_mul,abs_of_nonneg (Nat.cast_nonneg A : (0:ℚ)≤A),
    abs_of_nonneg (Nat.cast_nonneg S : (0:ℚ)≤S),abs_of_nonneg y0] at tri
  have distance : |(A:ℚ)*Z-H| * L≤2*A*K*2^K+2*S := by
    nlinarith only [mul_le_mul_of_nonneg_right tri lp.le,
      mul_le_mul_of_nonneg_left xl (Nat.cast_nonneg A : (0:ℚ)≤A),
      mul_le_mul_of_nonneg_left yl (Nat.cast_nonneg S : (0:ℚ)≤S)]
  have bad : L≤(budget A K:ℚ)*(2*A*K*2^K+2*S) := by
    nlinarith only [mul_le_mul_of_nonneg_right sep lp.le,
      mul_le_mul_of_nonneg_left distance (Nat.cast_nonneg (budget A K) : (0:ℚ)≤_)]
  change ((threshold A S K:ℕ):ℚ)+1≤_ at bad
  unfold threshold at bad
  push_cast at bad
  linarith

end OMA.CofactorEffectiveAtom245212

end

section

/- Effective recovery of the only possible last prime from its cofactor
and exponent, by bounding the lower digits in the divisor identity. -/
namespace OMA.LastDigit245212
open Finset ArithmeticFunction OMA.Smooth245212 OMA.Abundance245212
open scoped ArithmeticFunction.sigma

theorem geom (p e : ℕ) (hp : 1≤p) :
    (∑ j∈range e,p^j)*(p-1)+1=p^e := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [sum_range_succ,add_mul,pow_succ]
    have v := congrArg (fun x : ℕ => p^e*x) (Nat.sub_add_cancel hp)
    simp only [Nat.mul_add,Nat.mul_one] at v
    nlinarith only [ih,v]


end OMA.LastDigit245212

end

section

/- A uniform effective restriction on every coprime part of a putative
solution, without assuming that its prime bases or exponents are fixed. -/
namespace OMA.CofactorHarmonic245212
open Nat Finset ArithmeticFunction OMA.Smooth245212
open scoped ArithmeticFunction.sigma
open OMA.LastDigit245212 (geom)

theorem phi_sigma (m : ℕ) : m.totient * σ 1 m ≤ m^2 := by
  induction m using Nat.recOnPrimeCoprime with
  | zero => simp
  | prime_pow p e hp =>
    cases e with
    | zero => simp
    | succ e =>
      rw [totient_prime_pow_succ hp,sigma_one_apply_prime_pow hp]
      have g := OMA.LastDigit245212.geom p (e+2) hp.pos
      have z := Nat.mul_le_mul_left (p^e)
        (show (∑ j∈range (e+2),p^j)*(p-1)≤p^(e+2) by omega)
      calc
        _ = p^e*((∑ j∈range (e+2),p^j)*(p-1)) := by ring
        _ ≤ _ := z
        _ = _ := by simp only [pow_succ];ring
  | coprime a b _ _ cop ia ib =>
    rw [totient_mul cop,isMultiplicative_sigma.map_mul_of_coprime cop,mul_pow]
    simpa only [mul_assoc,mul_left_comm,mul_comm] using Nat.mul_le_mul ia ib

private theorem divisor_bounds {m : ℕ} (hm : 1 < m) :
    m*(σ 0 m)≤W m ∧ m<σ 1 m ∧ W m≤(σ 0 m)*(σ 1 m) := by
  have nz : m≠0 := by omega
  constructor
  · rw [w_apply,sigma_zero_apply]
    exact single_le_sum (f:=fun d : ℕ => d*d.divisors.card)
      (fun _ _ => Nat.zero_le _) (Nat.mem_divisors_self _ nz)
  constructor
  · rw [sigma_one_apply,←Nat.insert_self_properDivisors nz,sum_insert Nat.self_notMem_properDivisors]
    have h := single_le_sum (f:=fun d : ℕ => d) (fun _ _ => Nat.zero_le _)
      (Nat.one_mem_properDivisors_iff_one_lt.mpr hm)
    omega
  · rw [w_apply,sigma_zero_apply,sigma_one_apply,mul_sum]
    exact sum_le_sum fun d hd => by
      rw [mul_comm m.divisors.card d]
      exact Nat.mul_le_mul_left d (Finset.card_le_card
        (Nat.divisors_subset_of_dvd nz (Nat.mem_divisors.mp hd).1))

/-- If h·m is a solution, the gap at the largest divisor of m is a
positive integer. The totient bound limits how much its other divisors
can contribute. -/
theorem gap {h m : ℕ} (hh : 0<h) (hm : 1 < m) (cop : h.Coprime m)
    (eqn : OeisA245212.a (h*m)=(σ 1 (h*m):ℤ)) :
    W h*(σ 0 m)+σ 1 h < 2*(h*σ 0 h)*(σ 0 m) ∧
    2*(h*σ 0 h)*(σ 0 m)*m.totient ≤ (W h*σ 0 m+σ 1 h)*m := by
  have mp : 0 < m := by omega
  have s := sigma_pos 1 h hh.ne'
  have b := OMA.Abundance245212.balance (mul_ne_zero hh.ne' mp.ne') eqn
  rw [w_mult.map_mul_of_coprime cop,isMultiplicative_sigma.map_mul_of_coprime cop,
    isMultiplicative_sigma.map_mul_of_coprime cop] at b
  obtain ⟨l,r,u⟩ := divisor_bounds hm
  constructor
  · apply Nat.lt_of_mul_lt_mul_right (a:=m)
    nlinarith only [b,Nat.mul_le_mul_left (W h) l,Nat.mul_lt_mul_of_pos_left r s]
  · apply Nat.le_of_mul_le_mul_right _ mp
    have v := Nat.mul_le_mul_right m.totient (Nat.mul_le_mul_left (W h) u)
    have w := Nat.mul_le_mul_left (W h*σ 0 m+σ 1 h) (phi_sigma m)
    nlinarith only [congrArg (fun t : ℕ => t*m.totient) b,v,w]

/-- Uniform bound independent of the prime exponents inside m. -/
theorem totient_gap {h m : ℕ} (hh : 0<h) (hm : 1 < m) (cop : h.Coprime m)
    (eqn : OeisA245212.a (h*m)=(σ 1 (h*m):ℤ)) :
    (2*(h*σ 0 h)-W h)*m ≤ 2*(h*σ 0 h)*(σ 1 h+1)*(m-m.totient) := by
  obtain ⟨strict,cap⟩ := gap hh hm cop eqn
  let H := 2*(h*σ 0 h)
  let A := W h
  let S := σ 1 h
  let L := σ 0 m
  change A*L+S < H*L at strict
  change H*L*m.totient ≤ (A*L+S)*m at cap
  change (H-A)*m ≤ H*(S+1)*(m-m.totient)
  have al : A≤H := by
    by_contra! no
    exact (not_le_of_gt strict) ((Nat.mul_le_mul_right L no.le).trans (Nat.le_add_right _ _))
  have D := Nat.sub_add_cancel al
  have E : S+1≤(H-A)*L := by nlinarith only [strict,congrArg (·*L) D]
  have mu := Nat.sub_add_cancel m.totient_le
  have bound : ((H-A)*L-S)*m≤H*L*(m-m.totient) := by
    have diff := Nat.sub_add_cancel (show S≤(H-A)*L by omega)
    nlinarith only [cap,congrArg (·*m*L) D,congrArg (·*m) diff,congrArg (H*L*·) mu]
  have low : (H-A)*L ≤ (S+1)*((H-A)*L-S) := by
    have diff := Nat.sub_add_cancel (show S≤(H-A)*L by omega)
    have one : 1≤(H-A)*L-S := by omega
    nlinarith only [diff,Nat.mul_le_mul_left S one]
  apply Nat.le_of_mul_le_mul_right _ (sigma_pos 0 m (by omega : m≠0))
  nlinarith only [Nat.mul_le_mul_right m low,Nat.mul_le_mul_left (S+1) bound]

private theorem union_bound (s : Finset ℕ) (hp : ∀ p∈s,0 < p) :
    1-(∏ p∈s,(1-(p:ℚ)⁻¹)) ≤ ∑ p∈s,(p:ℚ)⁻¹ := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s out ih =>
    have pp : 0<p := hp p (mem_insert_self ..)
    have tail (q : ℕ) (hq : q∈s) := hp q (mem_insert_of_mem hq)
    have unit (q : ℕ) (hq : q∈s) : 0≤1-(q:ℚ)⁻¹ := by
      have pos : (1:ℚ)≤q := by exact_mod_cast tail q hq
      have v := (inv_le_one₀ (by linarith : (0:ℚ)<q)).mpr pos
      linarith
    have bound : (∏ q∈s,(1-(q:ℚ)⁻¹))≤1 :=
      prod_le_one (fun q hq => unit q hq) (fun _ _ => by simp)
    have p0 : (0:ℚ)≤(p:ℚ)⁻¹ := by positivity
    rw [prod_insert out,sum_insert out]
    nlinarith only [ih tail,mul_le_mul_of_nonneg_left bound p0]

private theorem to_mass {m D scale : ℕ} (hm : 0 < m) (gap : D*m ≤ scale*(m-m.totient)) :
    (D:ℚ) ≤ (scale:ℚ) * ∑ p∈m.primeFactors,(p:ℚ)⁻¹ := by
  have rat : (D:ℚ)*m≤(scale:ℚ)*((m:ℚ)-(m.totient:ℚ)) := by
    rw [←Nat.cast_sub m.totient_le]
    exact_mod_cast gap
  rw [Nat.totient_eq_mul_prod_factors m] at rat
  have mass := union_bound m.primeFactors (fun _ hp => Nat.pos_of_mem_primeFactors hp)
  change (D:ℚ)≤(scale:ℚ)*_
  apply le_of_mul_le_mul_left (a:=(m:ℚ)) _ (by exact_mod_cast (show 0 < m by omega))
  nlinarith only [rat,mul_le_mul_of_nonneg_left mass (by positivity : 0≤(m:ℚ)*scale)]

/-- The distinct new primes must contribute a positive, explicit total
reciprocal mass determined solely by the known factor h. -/
theorem reciprocals {h m : ℕ} (hh : 0<h) (hm : 1 < m) (cop : h.Coprime m)
    (eqn : OeisA245212.a (h*m)=(σ 1 (h*m):ℤ)) :
    ((2*(h*σ 0 h)-W h:ℕ):ℚ) ≤
      (2*(h*σ 0 h)*(σ 1 h+1):ℕ) * ∑ p∈m.primeFactors,(p:ℚ)⁻¹ :=
  to_mass (by omega) (totient_gap hh hm cop eqn)

/-- If the remaining exponents are prescribed, use their actual divisor
count to sharpen the lower bound. Its numerator is a positive integer. -/
theorem count_sensitive {h m : ℕ} (hh : 0<h) (hm : 1 < m) (cop : h.Coprime m)
    (eqn : OeisA245212.a (h*m)=(σ 1 (h*m):ℤ)) :
    let H := 2*(h*σ 0 h)*(σ 0 m)
    let A := W h*σ 0 m+σ 1 h
    0<H-A ∧ ((H-A:ℕ):ℚ) ≤ (H:ℚ)*∑ p∈m.primeFactors,(p:ℚ)⁻¹ := by
  obtain ⟨l,c⟩:=gap hh hm cop eqn
  dsimp only
  refine ⟨by omega,to_mass (by omega) ?_⟩
  have d := Nat.sub_add_cancel l.le
  have f := Nat.sub_add_cancel m.totient_le
  nlinarith only [c,congrArg (·*m) d,congrArg ((2*(h*σ 0 h)*(σ 0 m))*·) f]

private theorem from_mass {r H D m : ℕ} (lower : ∀ p∈m.primeFactors,r≤p)
    (mass : (D:ℚ)≤(H:ℚ)*∑ p∈m.primeFactors,(p:ℚ)⁻¹) : r*D ≤ m.primeFactors.card*H := by
  have per (p : ℕ) (hp : p∈m.primeFactors) : (r:ℚ)*(p:ℚ)⁻¹≤1 := by
    rw [←div_eq_mul_inv,div_le_one (by exact_mod_cast Nat.pos_of_mem_primeFactors hp : (0:ℚ)<p)]
    exact_mod_cast lower p hp
  have cap := sum_le_sum per
  simp only [←mul_sum,sum_const,nsmul_eq_mul,mul_one] at cap
  exact_mod_cast (show (r:ℚ)*D≤(m.primeFactors.card:ℚ)*H by
    nlinarith only [mul_le_mul_of_nonneg_left mass (Nat.cast_nonneg r),
      mul_le_mul_of_nonneg_left cap (Nat.cast_nonneg H)])

/-- Taking r to be the least new prime gives an integer bound linear
in the number of remaining prime factors and independent of all exponents. -/
theorem least_prime {h m r : ℕ} (hh : 0<h) (hm : 1 < m) (cop : h.Coprime m)
    (lower : ∀ p∈m.primeFactors,r≤p) (eqn : OeisA245212.a (h*m)=(σ 1 (h*m):ℤ)) :
    r*(2*(h*σ 0 h)-W h) ≤ m.primeFactors.card*(2*(h*σ 0 h)*(σ 1 h+1)) :=
  from_mass lower (reciprocals hh hm cop eqn)

end OMA.CofactorHarmonic245212

end

section

/- Explicit simultaneous base and exponent bounds for at least one
odd prime power of any solution with fixed dyadic exponent and rank. -/
namespace OMA.CofactorEffectiveOriginal245212
open Nat Finset ArithmeticFunction OMA.Smooth245212 OMA.CofactorEulerSeparation245212
open OMA.CofactorEffectiveAtom245212
open scoped ArithmeticFunction.sigma

def height (h r : ℕ) := threshold (W h) (σ 1 h) r
def primeHeight (h r : ℕ) :=
  let H:=2*(h*σ 0 h)
  max (height h r+1) (r*H*(σ 1 h+1)/(H-W h))

theorem original {h m : ℕ} (hh : 0<h) (hm : 1 < m) (cop : h.Coprime m)
    (apart : miss (W h) (2*(h*σ 0 h)) m.primeFactors)
    (eqn : OeisA245212.a (h*m)=(σ 1 (h*m):ℤ)) :
    ∃p∈m.primeFactors,p≤primeHeight h m.primeFactors.card ∧ m.factorization p≤height h m.primeFactors.card := by
  classical
  let t:=m.primeFactors
  let p : t→ℕ:=Subtype.val
  let e (i : t):=m.factorization (p i)
  have mn : m≠0:=by omega
  have pr (i:t) : (p i).Prime:=prime_of_mem_primeFactors i.property
  have localCop (i:t) : h.Coprime (p i):=cop.of_dvd_right (dvd_of_mem_primeFactors i.property)
  have repr : total p e=m := (Nat.prod_primeFactors_coe_pow_factorization mn).symm
  let D:=h*σ 0 h
  have d0 : 0<D:=mul_pos hh (sigma_pos 0 h hh.ne')
  have sc:=OMA.CofactorCrossOriginal245212.normalized_extension (p:=p) (e:=e) hh pr
    Subtype.val_injective localCop (repr ▸ eqn)
  have sx : (∏i,X (p i) (some (e i)))=∏x∈t,X x (some (m.factorization x)) :=
    t.prod_coe_sort (fun x=>X x (some (m.factorization x)))
  have sy : (∏i,Y (p i) (some (e i)))=∏x∈t,Y x (some (m.factorization x)) :=
    t.prod_coe_sort (fun x=>Y x (some (m.factorization x)))
  rw [sx,sy] at sc
  change ((W h:ℚ)/D)*_+((σ 1 h:ℚ)/D)*_=2 at sc
  field_simp [show (D:ℚ)≠0 by exact_mod_cast d0.ne'] at sc
  have mass : (W h:ℚ)*(∏x∈t,X x (some (m.factorization x)))+
      (σ 1 h:ℚ)*(∏x∈t,Y x (some (m.factorization x)))=((2*D:ℕ):ℚ) := by push_cast;linarith only [sc]
  rcases alternative (W h) (σ 1 h) (2*D) t m.factorization (fun _ hp=>prime_of_mem_primeFactors hp) apart mass with
    short|⟨q,hq,pq,eq⟩
  · have ne : t.Nonempty := by
      exact ⟨m.minFac,(Nat.mem_primeFactors_of_ne_zero mn).mpr ⟨Nat.minFac_prime (by omega),Nat.minFac_dvd _⟩⟩
    let q:=t.min' ne
    have mem : q∈t:=t.min'_mem ne
    have bound:=OMA.CofactorHarmonic245212.least_prime (r:=q) hh hm cop (fun r hr=>t.min'_le r hr) eqn
    have g:=(OMA.CofactorHarmonic245212.gap hh hm cop eqn).1
    have below : W h<2*D := by
      by_contra! no
      have bad:=Nat.mul_le_mul_right (σ 0 m) no
      change W h*σ 0 m+σ 1 h<2*D*σ 0 m at g
      omega
    have qp : q≤t.card*(2*D)*(σ 1 h+1)/(2*D-W h) := by
      apply (Nat.le_div_iff_mul_le (Nat.sub_pos_of_lt below)).mpr
      simpa only [D,mul_assoc] using bound
    exact ⟨q,mem,qp.trans (le_max_right _ _),short q mem⟩
  · exact ⟨q,hq,pq.trans (le_max_left _ _),eq⟩


end OMA.CofactorEffectiveOriginal245212

end

section

/- A computable bound on an entire cross-divisibility-free solution, by
absorbing a bounded whole prime power at each successive cofactor. -/
namespace OMA.CofactorEffectiveTree245212
open Nat Finset ArithmeticFunction OMA.Smooth245212
open OMA.CofactorEffectiveOriginal245212 OMA.CofactorEulerSeparation245212
open scoped ArithmeticFunction.sigma

/-- Every branch removes one distinct prime. The enlarged finite boxes
include nonprime bases; these are harmless upper bounds. -/
def ceiling : ℕ → ℕ → ℕ
  | 0,h => h
  | k+1,h => ((range (primeHeight h (k+1)+1)).product (range (height h (k+1)+1))).sup
      (fun t => ceiling k (h*t.1^t.2))

theorem support_rest (m p : ℕ) : (ordCompl[p] m).primeFactors=m.primeFactors.erase p := by
  rw [←Nat.support_factorization, Nat.factorization_ordCompl, Finsupp.support_erase,
    Nat.support_factorization]


end OMA.CofactorEffectiveTree245212

end

section

/- At fixed prime-support rank, a search either finishes below its explicit
ceiling or reaches a bounded prefix at which a nonempty Euler subproduct
hits the exact limiting ratio. -/
namespace OMA.CofactorFrontier245212
open Nat Finset ArithmeticFunction OMA.Smooth245212
open OMA.CofactorEffectiveOriginal245212 OMA.CofactorEffectiveTree245212
open OMA.CofactorEulerSeparation245212
open scoped ArithmeticFunction.sigma

private theorem ceiling_ge (r h : ℕ) : h≤ceiling r h := by
  induction r with
  | zero => rfl
  | succ r ih =>
    let box:=(range (primeHeight h (r+1)+1)).product (range (height h (r+1)+1))
    have mem : (0,0)∈box := mem_product.mpr ⟨mem_range.mpr (by omega),mem_range.mpr (by omega)⟩
    have le:=le_sup (f:=fun t : ℕ×ℕ => ceiling r (h*t.1^t.2)) mem
    exact ih.trans (by simpa [ceiling,box] using le)

private theorem largest_divides {h m : ℕ} (cop : h.Coprime m) (odd : Odd m)
    {T : Finset ℕ} (non : T.Nonempty) (sub : T⊆m.primeFactors)
    (hit : W h*num T=2*(h*σ 0 h)*den T) : T.max' non ∣ σ 0 h := by
  let q:=T.max' non
  have mq : q∈T := T.max'_mem _
  have mem:=sub mq
  have pr:=prime_of_mem_primeFactors mem
  have dvd : q∣2*(h*σ 0 h)*den T := hit ▸ dvd_mul_of_dvd_right (dvd_prod_of_mem (fun p=>p) mq) _
  rcases pr.dvd_mul.mp dvd with left|right
  · rcases pr.dvd_mul.mp left with two|left
    · have hq := (prime_dvd_prime_iff_eq pr prime_two).mp two
      exact False.elim (odd.not_two_dvd_nat (hq ▸ dvd_of_mem_primeFactors mem))
    rcases pr.dvd_mul.mp left with abs|concl
    · exact False.elim ((pr.coprime_iff_not_dvd.mp (cop.of_dvd_right (dvd_of_mem_primeFactors mem)).symm) abs)
    exact concl
  · obtain ⟨p,mp,dv⟩:=(pr.prime.dvd_finsetProd_iff (fun j=>j-1)).mp right
    have lp : p≤q := T.le_max' _ mp
    have p1:=(prime_of_mem_primeFactors (sub mp)).one_lt
    have lq:=Nat.le_of_dvd (show 0<p-1 by omega) dv
    omega

/-- The residual prefix itself is bounded, not only the size of a complete
nonresonant solution. Every prime of the exceptional set is at most its
largest element, which divides the prefix's divisor count. -/
theorem frontier (r : ℕ) {h m : ℕ} (hh : 0 < h) (hm : 0 < m) (cop : h.Coprime m)
    (odd : Odd m) (rank : m.primeFactors.card=r)
    (eqn : OeisA245212.a (h*m)=(σ 1 (h*m):ℤ)) :
    h*m≤ceiling r h ∨ ∃ u v : ℕ, ∃ T : Finset ℕ, ∃ non : T.Nonempty,
      u*v=h*m ∧ 1<u ∧ 1<v ∧ u≤ceiling r h ∧ u.Coprime v ∧ T⊆v.primeFactors ∧
      W u*num T=2*(u*σ 0 u)*den T ∧ T.max' non∣σ 0 u := by
  classical
  induction r generalizing h m with
  | zero =>
    have emp:=Nat.primeFactors_eq_empty.mp (card_eq_zero.mp rank)
    have one : m=1:=by omega
    exact Or.inl (by simp [one,ceiling])
  | succ k ih =>
    have big : 1 < m := by
      by_contra! small
      have one : m=1:=by omega
      simp [one] at rank
    have g:=(OMA.CofactorHarmonic245212.gap hh big cop eqn).1
    have below : W h<2*(h*σ 0 h) := by
      by_contra! no
      have b:=Nat.mul_le_mul_right (σ 0 m) no
      omega
    by_cases apart : miss (W h) (2*(h*σ 0 h)) m.primeFactors
    · obtain ⟨p,mem,ps,es⟩:=original hh big cop apart eqn
      rw [rank] at ps es
      let e:=m.factorization p
      let v:=ordCompl[p] m
      have pr:=prime_of_mem_primeFactors mem
      have vp : 0<v := Nat.ordCompl_pos p hm.ne'
      have id : h*p^e*v=h*m := by rw [mul_assoc,Nat.ordProj_mul_ordCompl_eq_self]
      have vd : v∣m := Nat.ordCompl_dvd m p
      have cv : (h*p^e).Coprime v :=
        (cop.of_dvd_right vd).mul_left ((Nat.coprime_ordCompl pr hm.ne').pow_left e)
      have rv : v.primeFactors.card=k := by
        rw [show v.primeFactors=m.primeFactors.erase p from support_rest m p,card_erase_of_mem mem,rank];omega
      have box : (p,e)∈(range (primeHeight h (k+1)+1)).product (range (height h (k+1)+1)) :=
        mem_product.mpr ⟨mem_range.mpr (by omega),mem_range.mpr (Nat.lt_succ_of_le es)⟩
      have child : ceiling k (h*p^e)≤ceiling (k+1) h :=
        le_sup (f:=fun t : ℕ×ℕ=>ceiling k (h*t.1^t.2)) box
      rcases ih (Nat.mul_pos hh (pow_pos pr.pos e)) vp cv
        (Nat.coprime_two_left.mp ((Nat.coprime_two_left.mpr odd).of_dvd_right vd))
        rv (id ▸ eqn) with done|⟨u,w,T,non,uw,u1,w1,bound,c,sub,hit,dvd⟩
      · exact Or.inl (id ▸ done.trans child)
      · exact Or.inr ⟨u,w,T,non,uw.trans id,u1,w1,bound.trans child,c,sub,hit,dvd⟩
    · unfold miss at apart
      push Not at apart
      obtain ⟨T,sub,hit⟩:=apart
      have non : T.Nonempty := by
        by_contra! empty
        exact below.ne (by simpa [empty,num,den] using hit)
      have h1 : 1<h := by
        by_contra! small
        have one : h=1 := by omega
        have oa : Odd (W h) := by simp [one,W]
        apply miss_odd oa (even_two_mul _) (s:=m.primeFactors) _ T sub hit
        intro p mem
        exact Nat.coprime_two_left.mp ((Nat.coprime_two_left.mpr odd).of_dvd_right (dvd_of_mem_primeFactors mem))
      exact Or.inr ⟨h,m,T,non,rfl,h1,big,ceiling_ge _ _,cop,sub,hit,largest_divides cop odd non sub hit⟩

end OMA.CofactorFrontier245212

end

section

/- A cofactor has at most one resonant Euler support, even without a rank
cutoff. The largest prime in the reduced numerator identifies the next factor. -/
namespace OMA.EulerSupportUnique245212
open Finset Nat ArithmeticFunction OMA.Smooth245212 OMA.CofactorEulerSeparation245212
open scoped ArithmeticFunction.sigma

theorem cofactor_divides {h : ℕ} {s : Finset ℕ} (cop : ∀p∈s,h.Coprime p)
    (hit : W h*num s=2*(h*σ 0 h)*den s) : h∣W h := by
  have cp : h.Coprime (num s) := coprime_prod_right_iff.mpr cop
  apply cp.dvd_of_dvd_mul_right
  rw [hit]
  exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (dvd_mul_right _ _) _) _


end OMA.EulerSupportUnique245212

end

section

/- The explicit recursion written in the project step agrees with the
whole-prime-power bound, including at the first resonant prefix. -/
namespace OMA.CofactorFrontier245212
open Finset ArithmeticFunction OMA.Smooth245212 OMA.CofactorEffectiveTree245212
open OMA.CofactorEffectiveOriginal245212 OMA.CofactorEulerSeparation245212
open scoped ArithmeticFunction.sigma

private def writtenBudget (A : ℕ) := Nat.rec (motive := fun _ => ℕ) 1
  (fun j b => max (2*b) ((2 + 2*A*2^j*b)^(j+1)))

private def writtenBox (k h : ℕ) :=
  let r := k+1
  let A := ∑ d ∈ h.divisors, d*d.divisors.card
  let D := 2*(h*σ 0 h)
  let E := writtenBudget A r * (2*A*r*2^r + 2*σ 1 h)
  let P := max (E+1) (r*D*(σ 1 h+1)/(D-A))
  (range (P+1)).product (range (E+1))

private def writtenCeiling := Nat.rec (motive := fun _ => ℕ → ℕ) (fun h => h) (fun k next h =>
  (writtenBox k h).sup (fun b => next (h*b.1^b.2)))

private theorem budget_eq (A r : ℕ) : writtenBudget A r=budget A r := by
  induction r with
  | zero => rfl
  | succ r ih =>
    exact congrArg (fun b : ℕ => max (2*b) ((2+2*A*2^r*b)^(r+1))) ih

private theorem ceiling_eq (r h : ℕ) : writtenCeiling r h=ceiling r h := by
  induction r generalizing h with
  | zero => rfl
  | succ r ih =>
    change (writtenBox r h).sup (fun b => writtenCeiling r (h*b.1^b.2))=_
    rw [show writtenBox r h=(range (primeHeight h (r+1)+1)).product (range (height h (r+1)+1)) by
      simp only [writtenBox,←w_apply,budget_eq,primeHeight,height,CofactorEffectiveAtom245212.threshold]]
    rw [ceiling]
    exact Finset.sup_congr rfl (fun t _ => ih _)

end OMA.CofactorFrontier245212

open Finset ArithmeticFunction OMA.Smooth245212 OMA.CofactorFrontier245212
open OMA.CofactorEffectiveTree245212 OMA.CofactorEulerSeparation245212
open scoped ArithmeticFunction.sigma

theorem OMA.solution : OMA.R_OeisA245212_conjecture_R1_H1_R2.H1 := by
  unfold OMA.R_OeisA245212_conjecture_R1_H1_R2.H1
  intro moment bud cap n big odd eqn B
  have rb : B=ceiling n.primeFactors.card 1 := by
    exact OMA.CofactorFrontier245212.ceiling_eq _ _
  have mw (u : ℕ) : moment u=W u := (w_apply u).symm
  by_cases small : n≤B
  · exact Or.inl small
  · have start := frontier n.primeFactors.card (h:=1) (m:=n) (by decide) (by omega)
      (Nat.coprime_one_left n) odd rfl (by simpa using eqn)
    rw [one_mul] at start
    rcases start with absurd|⟨u,v,T,non,factor,u1,v1,bound,cop,sub,hit,dvd⟩
    · exact False.elim (small (rb ▸ absurd))
    · have divides:=OMA.EulerSupportUnique245212.cofactor_divides
          (fun p hp=>cop.of_dvd_right (Nat.dvd_of_mem_primeFactors (sub hp))) hit
      have gap:=(OMA.CofactorHarmonic245212.gap (by omega : 0<u) v1 cop (factor ▸ eqn)).1
      have below : W u < 2*(u*σ 0 u) := by
        by_contra! no
        have b:=Nat.mul_le_mul_right (σ 0 v) no
        omega
      exact Or.inr ⟨u,v,T,non,factor,u1,v1,rb ▸ bound,Nat.lt_of_not_ge small,cop,
        mw u ▸ divides,mw u ▸ below,sub,by simpa only [mw,num,den] using hit,dvd⟩

end
