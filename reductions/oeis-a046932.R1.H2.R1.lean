import OMAReductions.R_oeis_a046932_R1

/-! For k = 2, the period of the trinomial is divisible by q² + q + 1, where q = 2ᵐ.
Bartholdi proved this row in Proposition 2.3 of Lamps, Factorizations and Finite Fields,
https://arxiv.org/pdf/math/9910056 . The lower bound here uses the Singer difference-set description of the roots:
Mészáros, Rónyai and Szabó, "Singer difference sets and the projective norm graph", https://page.mi.fu-berlin.de/szabo/PDF/singer.pdf.
Here the two roots whose quotient is primitive are given explicitly. -/
-- Credit: @jiyongparkphysics

namespace OMA.R_oeis_a046932_R1_H2_R1

open Polynomial
open scoped Polynomial
private lemma two_vanish {R : Type*} [CommRing R] [Algebra (ZMod 2) R] (z : R) : z + z = 0 := by
  have h : (2 : R) = 0 := by
    simpa only [map_ofNat, map_zero] using congrArg (algebraMap (ZMod 2) R) (show (2:ZMod 2) = 0 by decide)
  rw [← two_mul, h, zero_mul]

private lemma plus_one_zero {R : Type*} [CommRing R] [Algebra (ZMod 2) R] (z : R) :
    z + 1 = 0 ↔ z = 1 := by
  have h := two_vanish (1:R)
  constructor
  · intro h'
    linear_combination h' - h
  · rintro rfl
    exact h

private lemma dv_iff (n i : ℕ) : (X^n + X + 1 : (ZMod 2)[X]) ∣ (X^i+1 : (ZMod 2)[X]) ↔
    AdjoinRoot.root ((X^n + X + 1 : (ZMod 2)[X])) ^ i = 1 := by
  rw [← AdjoinRoot.mk_eq_zero]
  simp only [map_add, map_pow, AdjoinRoot.mk_X, map_one, plus_one_zero]

private lemma inf_order (n : ℕ) :
    sInf {m : ℕ | 0 < m ∧ (X^n + X + 1 : (ZMod 2)[X]) ∣ (X^m+1 : (ZMod 2)[X])} = orderOf (AdjoinRoot.root ((X^n + X + 1 : (ZMod 2)[X]))) := by
  classical
  let x := AdjoinRoot.root ((X^n + X + 1 : (ZMod 2)[X]))
  simp_rw [dv_iff]
  change sInf {m : ℕ | 0 < m ∧ x^m=1} = orderOf x
  by_cases hx : orderOf x = 0
  · have he : {m : ℕ | 0 < m ∧ x^m=1} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro m hm
      exact orderOf_eq_zero_iff'.mp hx m hm.1 hm.2
    rw [he, Nat.sInf_empty, hx]
  · have hmem : orderOf x ∈ {m : ℕ | 0 < m ∧ x^m=1} := ⟨Nat.pos_of_ne_zero hx,pow_orderOf_eq_one x⟩
    apply le_antisymm (Nat.sInf_le hmem)
    have hs := Nat.sInf_mem ⟨_,hmem⟩
    exact Nat.le_of_dvd hs.1 (orderOf_dvd_of_pow_eq_one hs.2)

private lemma root_per (n : ℕ) (x : (AlgebraicClosure (ZMod 2))) (hx : x^n+x+1=0) : x^OMA.S_oeis_a046932.a n = 1 := by
  have hh : (X^n + X + 1 : (ZMod 2)[X]) ∣ (X^OMA.S_oeis_a046932.a n+1 : (ZMod 2)[X]) := by
    apply (dv_iff _ _).mpr
    rw [OMA.S_oeis_a046932.a,inf_order]
    exact pow_orderOf_eq_one _
  obtain ⟨g,hg⟩ := hh
  have h := congrArg (Polynomial.aeval x) hg
  apply (plus_one_zero _).mp
  simpa only [map_mul,map_add,map_pow,aeval_X,map_one,hx,zero_mul] using h

private lemma singer (m : ℕ) : let q:=2^m; q*q+q+1 ∣ OMA.S_oeis_a046932.a (q+1) := by
  intro q
  let M := q*q+q+1
  have hq : 0 < q := pow_pos (by decide) _
  have hM : M ≠ 0 := by dsimp [M]; omega
  have hodd : ¬ 2 ∣ M := by
    dsimp [M]
    rcases (show q%2=0 ∨ q%2=1 by omega) with he | he <;>
      simp [Nat.dvd_iff_mod_eq_zero,Nat.add_mod,Nat.mul_mod,he]
  let _ : NeZero (M : (AlgebraicClosure (ZMod 2))) := ⟨fun h => hodd ((CharP.cast_eq_zero_iff (AlgebraicClosure (ZMod 2)) 2 M).mp h)⟩
  obtain ⟨a,ha⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure (ZMod 2)) M
  have ha0 := ha.ne_zero hM
  let b := a^q
  let c := b^q
  have hb0 : b ≠ 0 := pow_ne_zero _ ha0
  have hbc : b+1 ≠ 0 := fun h => ha.pow_ne_one_of_pos_of_lt hq.ne' (by dsimp [M]; omega) ((plus_one_zero b).mp h)
  have hcc : c+1 ≠ 0 := by
    intro hc
    have hpow := (plus_one_zero c).mp hc
    change (a^q)^q=1 at hpow
    rw [← pow_mul] at hpow
    exact ha.pow_ne_one_of_pos_of_lt (Nat.mul_pos hq hq).ne' (by dsimp[M];omega) hpow
  have habc : a*b*c=1 := by
    change a * a^q * (a^q)^q = 1
    rw [← pow_mul, ← pow_succ', ← pow_add]
    convert ha.pow_eq_one using 2
    dsimp [M]
    omega
  let x := (a*b+1)/(b+1)
  let y := (a*b+1)/(a*(b+1))
  have abq : (a*b+1)^q=b*c+1 := by
    dsimp [q,b,c]
    rw [add_pow_expChar_pow, mul_pow, one_pow]
  have b1q : (b+1)^q=c+1 := by
    dsimp [q,c]
    rw [add_pow_expChar_pow,one_pow]
  have hxq : x^q=(b*c+1)/(c+1) := by dsimp [x]; rw [div_pow,abq,b1q]
  have hyq : y^q=(b*c+1)/(b*(c+1)) := by dsimp [y]; rw [div_pow,mul_pow,abq,b1q]
  have hbridge : (a*b+1)*(b*c+1)=b*(a+1)*(c+1) := by linear_combination (b-1)*habc
  have hxplus : x+1=b*(a+1)/(b+1) := by
    dsimp [x]
    field_simp [hbc]
    linear_combination two_vanish (1:(AlgebraicClosure (ZMod 2)))
  have hyplus : y+1=(a+1)/(a*(b+1)) := by
    dsimp [y]
    field_simp [ha0,hbc]
    linear_combination two_vanish (a*b)
  have hxmul : x*x^q=x+1 := by
    rw [hxq,hxplus]
    dsimp [x]
    rw [div_mul_div_comm,hbridge]
    field_simp [hbc,hcc]
  have hymul : y*y^q=y+1 := by
    rw [hyq,hyplus]
    dsimp [y]
    rw [div_mul_div_comm,hbridge]
    field_simp [ha0,hb0,hbc,hcc]
  have rt (z : (AlgebraicClosure (ZMod 2))) (hz : z*z^q=z+1) : z^OMA.S_oeis_a046932.a (q+1)=1 := by
    apply root_per
    rw [pow_succ',hz]
    linear_combination two_vanish (z+1)
  have hx := rt x hxmul
  have hy := rt y hymul
  have eq : a*y=x := by dsimp [x,y]; field_simp [ha0,hbc]
  rw [← eq,mul_pow,hy,mul_one] at hx
  exact ha.dvd_of_pow_eq_one _ hx

private lemma period_two : OMA.S_oeis_a046932.a 2 = 3 := by
  apply Nat.dvd_antisymm
  · rw [OMA.S_oeis_a046932.a,inf_order]
    apply orderOf_dvd_of_pow_eq_one
    apply (dv_iff 2 3).mp
    use X+1
    have h2 := two_vanish (X^2:(ZMod 2)[X])
    have h1 := two_vanish (X:(ZMod 2)[X])
    change X ^ 3 + 1 = (X ^ 2 + X + 1) * (X + 1)
    linear_combination -h2 - h1
  · simpa using singer 0

private lemma second_row (m : ℕ) (hm : 1 ≤ m) :
    (2^(OMA.S_oeis_a046932.a 2*m)-1)/(2^m-1) ∣ OMA.S_oeis_a046932.a ((2^(2*m)-1)/(2^m-1)) := by
  have hq : 1 < (2:ℕ)^m := one_lt_pow₀ (by decide) (by omega)
  let q := 2^m
  have e2 : (q^2-1)/(q-1) = q+1 := by
    apply Nat.div_eq_of_eq_mul_left (by dsimp [q]; omega)
    have hq1 : q-1+1 = q := by dsimp [q]; omega
    generalize q-1 = t at hq1 ⊢
    rw [← hq1]
    have eq : (t+1)^2 = (t+1+1)*t+1 := by ring
    omega
  have e3 : (q^3-1)/(q-1) = q*q+q+1 := by
    apply Nat.div_eq_of_eq_mul_left (by dsimp [q]; omega)
    have hq1 : q-1+1 = q := by dsimp [q]; omega
    generalize q-1 = t at hq1 ⊢
    rw [← hq1]
    have eq : (t+1)^3 = ((t+1)*(t+1)+(t+1)+1)*t+1 := by ring
    omega
  rw [period_two,Nat.mul_comm 3 m,pow_mul,Nat.mul_comm 2 m,pow_mul]
  change (q^3-1)/(q-1) ∣ OMA.S_oeis_a046932.a ((q^2-1)/(q-1))
  rw [e2,e3]
  exact singer m


/-- Bartholdi’s original m = 1 case, after discharging k = 2. -/
def H1 : Prop :=
  ∀ k : ℕ, 3 ≤ k →
    (2 ^ (OMA.S_oeis_a046932.a k) - 1) ∣ OMA.S_oeis_a046932.a (2 ^ k - 1)

/-- The complementary extension-degree family, with both parameters nontrivial. -/
def H2 : Prop :=
  ∀ k m : ℕ, 3 ≤ k → 2 ≤ m →
    (2^(OMA.S_oeis_a046932.a k*m)-1)/(2^m-1) ∣ OMA.S_oeis_a046932.a ((2^(k*m)-1)/(2^m-1))

theorem main : H1 → H2 → OMA.R_oeis_a046932_R1.H2 := by
  intro h1 h2 k m hk hm
  by_cases htwo : k = 2
  · subst k
    exact second_row m hm
  by_cases hone : m = 1
  · subst m
    simpa using h1 k (by omega)
  · exact h2 k m (by omega) (by omega)

end OMA.R_oeis_a046932_R1_H2_R1
