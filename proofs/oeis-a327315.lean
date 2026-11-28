import OMAStatements.S_oeis_a327315
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic

/-!
# Irreducible derivative numerators of (x−2)/(x²−x+1)

Clark Kimberling conjectured the criterion in OEIS A327315 in 2019.
Credit: @Aryan-Poonacha.

After d−1 derivatives, the numerator is a rational unit times the monic
polynomial P d. For a primitive (6d)-th root ξ and z=ξ^d, its root
x=(ξz−(1−z))/(ξ−1) generates a real field with ℚ(x,z)=ℚ(ξ).
Thus x has degree φ(6d)/2. This equals d precisely for the 2,3-smooth degrees.
-/

noncomputable section
open Polynomial OMA.S_oeis_a327315 IntermediateField Complex
open scoped ComplexConjugate IntermediateField

namespace A327315Work


theorem smooth_of_phi (d : ℕ) (hd : 0 < d) (hp : (6*d).totient = 2*d) :
    ∃ a b : ℕ, d = 2^a * 3^b := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    by_cases h2 : 2 ∣ d
    · obtain ⟨k, rfl⟩ := h2
      rw [show 6*(2*k)=2*(6*k) by ring,
        Nat.totient_mul_of_prime_of_dvd Nat.prime_two (by exact ⟨3*k, by ring⟩)] at hp
      obtain ⟨a,b,hab⟩ := ih k (by omega) (by omega) (by omega)
      exact ⟨a+1,b,by rw [hab, pow_succ]; ring⟩
    by_cases h3 : 3 ∣ d
    · obtain ⟨k, rfl⟩ := h3
      rw [show 6*(3*k)=3*(6*k) by ring,
        Nat.totient_mul_of_prime_of_dvd (by decide : Nat.Prime 3) (by exact ⟨2*k, by ring⟩)] at hp
      obtain ⟨a,b,hab⟩ := ih k (by omega) (by omega) (by omega)
      exact ⟨a,b+1,by rw [hab, pow_succ]; ring⟩
    have hc : Nat.Coprime 6 d := by
      change Nat.Coprime (2*3) d
      exact Nat.Coprime.mul_left (Nat.prime_two.coprime_iff_not_dvd.mpr h2)
        ((by decide : Nat.Prime 3).coprime_iff_not_dvd.mpr h3)
    rw [Nat.totient_mul hc, show (6:ℕ).totient=2 by decide] at hp
    by_cases h1 : d=1
    · exact ⟨0,0,by simpa⟩
    · have hlt := Nat.totient_lt d (by omega : 1 < d)
      omega

theorem phi_smooth (a b : ℕ) : (6*(2^a*3^b)).totient = 2*(2^a*3^b) := by
  induction a with
  | zero =>
    simp only [pow_zero, one_mul]
    induction b with
    | zero => decide
    | succ b ih =>
      rw [pow_succ, show 6*(3^b*3) = 3*(6*3^b) by ring,
        Nat.totient_mul_of_prime_of_dvd (by decide : Nat.Prime 3) (by exact ⟨2*3^b, by ring⟩), ih]
      ring
  | succ a ih =>
    rw [pow_succ, show 6*(2^a*2*3^b) = 2*(6*(2^a*3^b)) by ring,
      Nat.totient_mul_of_prime_of_dvd Nat.prime_two (by exact ⟨3*(2^a*3^b),by ring⟩), ih]
    ring



private abbrev Q : ℚ[X] := X^2-X+1
private abbrev V : ℚ[X] := 2*X-1

/-- Monic rational numerator before multiplication by the derivative's scalar. -/
def P : ℕ → ℚ[X]
  | 0 => 1
  | 1 => X-2
  | n+2 => V * P (n+1) - Q * P n

private theorem Q_monic : Q.Monic := by
  rw [show Q = cyclotomic 6 ℚ from (cyclotomic_six _).symm]
  exact cyclotomic.monic _ _

private theorem coprime_P (d : ℕ) : IsCoprime (P d) Q := by
  have third : (C (1/3) : ℚ[X]) * 3 = 1 := by
    simpa only [← C_ofNat, ← C_mul, ← C_1] using congrArg (C : ℚ → ℚ[X]) (by norm_num : (1/3 : ℚ)*3 = 1)
  have hV : IsCoprime V Q := by
    refine ⟨-C (1/3)*V,4*C (1/3),?_⟩
    apply Eq.trans _ third
    dsimp [V,Q]
    ring
  induction d using Nat.twoStepInduction with
  | zero => exact isCoprime_one_left
  | one =>
    refine ⟨-C (1/3)*(X+1),C (1/3),?_⟩
    simp only [P]
    apply Eq.trans _ third
    dsimp [Q]
    ring
  | more n ih0 ih1 =>
    obtain ⟨a,b,h⟩ := hV.mul_left ih1
    exact ⟨a,b+a*P n,by simp only [P]; linear_combination h⟩

private lemma reduced {r : RatFunc ℚ} {p q : ℚ[X]} (hq : q.Monic) (hc : IsCoprime p q)
    (hr : r = algebraMap _ _ p / algebraMap _ _ q) :
    r.num = p ∧ r.denom = q := by
  have cross := (RatFunc.num_mul_eq_mul_denom_iff hq.ne_zero).mpr hr
  have hqd : q ∣ r.denom := hc.symm.dvd_of_dvd_mul_left (cross ▸ dvd_mul_left q r.num)
  have hdq : r.denom ∣ q := by
    rw [hr]
    exact RatFunc.denom_div_dvd p q
  have he : r.denom = q := eq_of_dvd_of_natDegree_le_of_leadingCoeff hdq
    (natDegree_le_of_dvd hqd (RatFunc.denom_ne_zero _))
    ((RatFunc.monic_denom _).trans hq.symm)
  exact ⟨mul_right_cancel₀ hq.ne_zero (he ▸ cross), he⟩

private theorem dQ : Polynomial.derivative Q = V := by simp [Q,V]; ring
private theorem dV : Polynomial.derivative V = 2 := by simp [V]

/-- These polynomials form an Appell sequence. -/
private theorem dP (n : ℕ) : Polynomial.derivative (P (n+1)) = (n+1 : ℕ) * P n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [P]
  | one => simp [P, Polynomial.derivative_mul]; ring
  | more n ih0 ih1 =>
    change Polynomial.derivative (V * P (n+2) - Q * P (n+1)) = _
    rw [map_sub, Polynomial.derivative_mul, Polynomial.derivative_mul, ih0, ih1, dV, dQ]
    have hr := P.eq_3 n
    push_cast
    linear_combination -((n:ℚ[X])+1)*hr

private theorem degree_P (d : ℕ) : (P d).natDegree = d := by
  induction d with
  | zero => simp [P]
  | succ d ih =>
    cases d with
    | zero => exact natDegree_X_sub_C (2:ℚ)
    | succ d =>
      have h := congrArg natDegree (dP (d+1))
      rw [Polynomial.natDegree_derivative] at h
      have hh : (((d+1+1 : ℕ) : ℚ[X]) * P (d+1)).natDegree = (P (d+1)).natDegree := by
        change (C (((d+1+1 : ℕ) : ℚ)) * P (d+1)).natDegree = _
        exact Polynomial.natDegree_C_mul (by positivity)
      rw [hh, ih] at h
      omega

private def scale (n : ℕ) : ℚ := (-1)^n * n.factorial

private lemma scale_ne (n : ℕ) : scale n ≠ 0 := by
  exact mul_ne_zero (pow_ne_zero n (by norm_num)) (by exact_mod_cast n.factorial_ne_zero)

private lemma scale_succ (n : ℕ) : scale (n+1) = - (n+1 : ℕ) * scale n := by
  simp [scale, pow_succ, Nat.factorial_succ]
  ring

private lemma fraction (n : ℕ) :
    (OMA.S_oeis_a327315.derivative^[n]) f =
      algebraMap ℚ[X] (RatFunc ℚ) (C (scale n) * P (n+1)) /
      algebraMap ℚ[X] (RatFunc ℚ) (Q^(n+1)) := by
  induction n with
  | zero => simp [f, P, Q, scale]
  | succ n ih =>
    let φ := algebraMap ℚ[X] (RatFunc ℚ)
    have hcop : IsCoprime (C (scale n) * P (n+1)) (Q^(n+1)) :=
      (isCoprime_mul_unit_left_left ((scale_ne n).isUnit.map C) _ _).mpr
        ((coprime_P (n+1)).pow_right)
    obtain ⟨hnum,hden⟩ := reduced (Q_monic.pow _) hcop ih
    rw [Function.iterate_succ_apply', OMA.S_oeis_a327315.derivative, hnum, hden,
      Polynomial.derivative_C_mul, dP, Polynomial.derivative_pow_succ, dQ]
    rw [div_eq_div_iff (pow_ne_zero 2 (RatFunc.algebraMap_ne_zero (pow_ne_zero _ Q_monic.ne_zero)))
      (RatFunc.algebraMap_ne_zero (pow_ne_zero _ Q_monic.ne_zero))]
    rw [← map_pow, ← map_mul, ← map_mul]
    apply congrArg φ
    rw [scale_succ, P.eq_3 n]
    simp only [map_mul, map_neg, C_eq_natCast]
    push_cast
    simp only [pow_succ]
    simp only [map_add, C_eq_natCast, map_one]
    ring

private lemma row_formula (n : ℕ) :
    row n = C (((n.factorial : ℚ)⁻¹) * scale n) * P (n+1) := by
  have hcop : IsCoprime (C (scale n) * P (n+1)) (Q^(n+1)) :=
    (isCoprime_mul_unit_left_left ((scale_ne n).isUnit.map C) _ _).mpr
      ((coprime_P (n+1)).pow_right)
  rw [row, (reduced (Q_monic.pow _) hcop (fraction n)).1, C_mul, mul_assoc]

private lemma evaluate_P (x z : ℂ) (hz : z^2-z+1=0) (d : ℕ) :
    aeval x (P d) = z*(x-(1-z))^d + (1-z)*(x-z)^d := by
  have h2 : aeval x (2:ℚ[X]) = (2:ℂ) := map_ofNat _ _
  induction d using Nat.twoStepInduction with
  | zero => simp [P]
  | one =>
    simp [P, h2]
    linear_combination -2*hz
  | more d ih0 ih1 =>
    change aeval x (V * P (d+1) - Q * P d) = _
    rw [map_sub, map_mul, map_mul, ih0, ih1]
    have hv : aeval x V = (x-(1-z)) + (x-z) := by simp [V, h2]; ring
    have hq : aeval x Q = (x-(1-z)) * (x-z) := by
      simp [Q]
      linear_combination hz
    rw [hv,hq]
    simp only [pow_succ]
    ring

theorem row_properties (n : ℕ) (ξ : ℂ) (hξ : IsPrimitiveRoot ξ (6*(n+1))) :
    (row n).natDegree = n+1 ∧
    Polynomial.aeval ((ξ * ξ^(n+1) - (1-ξ^(n+1))) / (ξ-1)) (row n) = 0 := by
  let d := n+1
  let z := ξ^d
  let x := (ξ*z-(1-z))/(ξ-1)
  have hz : IsPrimitiveRoot z 6 := hξ.pow (by omega) (by dsimp [d]; omega)
  have hq : z^2-z+1=0 := by
    simpa [cyclotomic_six, IsRoot.def] using hz.isRoot_cyclotomic (by decide)
  have hξ1 := hξ.ne_one (by omega)
  have hx : x*(ξ-1) = ξ*z-(1-z) := div_mul_cancel₀ _ (sub_ne_zero.mpr hξ1)
  have hrel : x-(1-z) = ξ*(x-z) := by linear_combination -hx
  rw [row_formula]
  constructor
  · rw [natDegree_C_mul (mul_ne_zero (inv_ne_zero (by exact_mod_cast n.factorial_ne_zero))
      (scale_ne n)), degree_P]
  · change aeval x (C _ * P d) = 0
    rw [map_mul, evaluate_P x z hq, hrel, mul_pow]
    have hp : z*ξ^d + (1-z) = 0 := by change z*z + (1-z) = 0; linear_combination hq
    rw [show z*(ξ^d*(x-z)^d)+(1-z)*(x-z)^d = (z*ξ^d+(1-z))*(x-z)^d by ring, hp]
    simp



theorem point_degree (d : ℕ) (ξ : ℂ) (hd : 0 < d) (hξ : IsPrimitiveRoot ξ (6*d)) :
    2 * (minpoly ℚ ((ξ * ξ^d - (1-ξ^d)) / (ξ-1))).natDegree = (6*d).totient := by
  let z := ξ^d
  let x := (ξ*z - (1-z))/(ξ-1)
  have hn : 0 < 6*d := by omega
  have hξ0 := hξ.ne_zero hn.ne'
  have hξ1 := hξ.ne_one (by omega)
  have hz : IsPrimitiveRoot z 6 := hξ.pow hn (by omega : 6*d = d*6)
  have hz0 := hz.ne_zero (by decide)
  have hquad : z^2-z+1=0 := by
    have h := hz.isRoot_cyclotomic (by decide)
    simpa [cyclotomic_six, IsRoot.def] using h
  have hzhalf : 2*z ≠ 1 := by
    intro h
    suffices (3:ℂ) = 0 by norm_num at this
    linear_combination 4*hquad - (2*z-1)*h
  have hξbar : conj ξ = ξ⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    simpa [Complex.norm_eq_one_of_pow_eq_one hξ.pow_eq_one hn.ne'] using Complex.conj_mul' ξ
  have hzbar : conj z = 1-z := by
    apply mul_right_cancel₀ hz0
    rw [Complex.conj_mul', Complex.norm_eq_one_of_pow_eq_one hz.pow_eq_one (by decide)]
    push_cast
    linear_combination hquad
  have hxreal : conj x = x := by
    dsimp [x]
    rw [map_div₀, map_sub, map_mul, map_sub, map_sub, map_one, hξbar, hzbar]
    field_simp
    ring
  let R := (IsScalarTower.toAlgHom ℚ ℝ ℂ).fieldRange
  let F := ℚ⟮x⟯
  have hFR : F ≤ R := by
    apply adjoin_simple_le_iff.mpr
    exact ⟨x.re, Complex.conj_eq_iff_re.mp hxreal⟩
  have hzF : z ∉ F := by
    intro h
    obtain ⟨r, hr⟩ := hFR h
    change (r : ℂ) = z at hr
    have h : r^2-r+1=0 := by exact_mod_cast hr ▸ hquad
    nlinarith [sq_nonneg (r-1/2)]
  let K := ℚ⟮ξ⟯
  let E := F⟮z⟯
  have hξK : ξ ∈ K := mem_adjoin_simple_self _ _
  have hzK : z ∈ K := K.pow_mem hξK d
  have hxK : x ∈ K := K.div_mem (K.sub_mem (K.mul_mem hξK hzK) (K.sub_mem K.one_mem hzK))
    (K.sub_mem hξK K.one_mem)
  have hE : E.restrictScalars ℚ = K := by
    change (F⟮z⟯).restrictScalars ℚ = K
    refine (restrictScalars_adjoin_eq_sup ℚ F {z}).trans ?_
    apply le_antisymm (sup_le (adjoin_simple_le_iff.mpr hxK) (adjoin_simple_le_iff.mpr hzK))
    apply adjoin_simple_le_iff.mpr
    let L := F ⊔ ℚ⟮z⟯
    have hxL : x ∈ L := (show F ≤ L from le_sup_left) (mem_adjoin_simple_self _ _)
    have hzL : z ∈ L := (show ℚ⟮z⟯ ≤ L from le_sup_right) (mem_adjoin_simple_self _ _)
    have he : x*(ξ-1)=ξ*z-(1-z) := by
      exact div_mul_cancel₀ _ (sub_ne_zero.mpr hξ1)
    have hdiff : x ≠ z := by
      intro heq
      rw [heq] at he
      apply hzhalf
      linear_combination -he
    have hfrac : ξ = (x-(1-z))/(x-z) := by
      apply (eq_div_iff (sub_ne_zero.mpr hdiff)).mpr
      linear_combination he
    rw [hfrac]
    exact L.div_mem (L.sub_mem hxL (L.sub_mem L.one_mem hzL)) (L.sub_mem hxL hzL)
  have hξint : IsIntegral ℚ ξ := (hξ.isIntegral hn).tower_top
  have hzint : IsIntegral ℚ z := hξint.pow d
  have hxint : IsIntegral ℚ x := by
    dsimp [x, div_eq_mul_inv]
    exact ((hξint.mul hzint).sub ((isIntegral_one : IsIntegral ℚ (1:ℂ)).sub hzint)).mul
      ((hξint.sub isIntegral_one).inv)
  have hzf : IsIntegral F z := hzint.tower_top
  have hdegz : (minpoly F z).natDegree = 2 := by
    have hroot : (aeval z) (X^2-X+1 : Polynomial F) = 0 := by simpa using hquad
    have hdd := natDegree_le_of_dvd (minpoly.dvd F z hroot)
      (show (X^2-X+1 : Polynomial F) ≠ 0 by rw [← cyclotomic_six]; exact cyclotomic_ne_zero _ _)
    rw [← cyclotomic_six, natDegree_cyclotomic, show (6:ℕ).totient=2 by decide] at hdd
    have h1 : (minpoly F z).natDegree ≠ 1 := by
      intro h
      obtain ⟨y,hy⟩ := minpoly.natDegree_eq_one_iff.mp h
      exact hzF (hy ▸ y.property)
    have hp := minpoly.natDegree_pos hzf
    omega
  have hK : Module.finrank ℚ K = (6*d).totient := by
    have : NeZero (6*d : ℕ) := ⟨hn.ne'⟩
    rw [show Module.finrank ℚ K = (minpoly ℚ ξ).natDegree from adjoin.finrank hξint,
      ← hξ.minpoly_eq_cyclotomic_of_irreducible (cyclotomic.irreducible_rat hn), natDegree_cyclotomic]
  have hmult := Module.finrank_mul_finrank ℚ F E
  have heq : Module.finrank ℚ E = Module.finrank ℚ K := by
    change Module.finrank ℚ (E.restrictScalars ℚ) = _
    rw [hE]
  change 2 * (minpoly ℚ x).natDegree = _
  rw [← adjoin.finrank hxint]
  rw [← hK, ← heq, ← hmult]
  rw [show Module.finrank F E = 2 from (adjoin.finrank hzf).trans hdegz, mul_comm]


end A327315Work

open A327315Work

theorem OMA.solution : type_of% @OMA.S_oeis_a327315.main := by
  intro n
  let d := n+1
  have hd : 0 < d := Nat.succ_pos n
  have hp := Complex.isPrimitiveRoot_exp (6*d) (by positivity)
  let ξ := Complex.exp (2 * Real.pi * Complex.I / (6*d : ℕ))
  have hξ : IsPrimitiveRoot ξ (6*d) := hp
  let x := (ξ * ξ^d - (1-ξ^d)) / (ξ-1)
  obtain ⟨hdegree,hroot⟩ := row_properties n ξ hξ
  have hz : (row n) ≠ 0 := ne_zero_of_natDegree_gt (by rw [hdegree]; omega : 0 < (row n).natDegree)
  have hx : IsIntegral ℚ x := IsAlgebraic.isIntegral ⟨row n, hz, hroot⟩
  have hφ : 2 * (minpoly ℚ x).natDegree = (6*d).totient := point_degree d ξ hd hξ
  constructor
  · intro hi
    have h := congrArg Polynomial.natDegree (minpoly.eq_of_irreducible hi hroot)
    rw [Polynomial.natDegree_mul_C (inv_ne_zero (leadingCoeff_ne_zero.mpr hz)), hdegree] at h
    exact smooth_of_phi d hd (by change d = (minpoly ℚ x).natDegree at h; omega)
  · rintro ⟨a,b,hab⟩
    change d = 2^a * 3^b at hab
    have heq : (6*d).totient = 2*d := hab.symm ▸ phi_smooth a b
    have hle : (row n).natDegree ≤ (minpoly ℚ x).natDegree := by
      change (row n).natDegree = d at hdegree
      omega
    exact (associated_of_dvd_of_natDegree_le (minpoly.dvd ℚ x hroot) hz hle).irreducible
      (minpoly.irreducible hx)
