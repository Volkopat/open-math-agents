import OMAReductions.R_Erdos940_erdos_940_variants_large_integers_R1
import Mathlib

-- Credit: @kumagi

/-!
Formalization of Basile Beyer de Ryke, A density deficit for sums of
three cube-full numbers, Corollary 1.2 and its local estimates.
https://arxiv.org/abs/2609.35772

The counting argument uses coordinate boxes for the progression upper
bound. The reciprocal-prime divergence follows from the ideal-counting
asymptotic in Mathlib and degree-one prime ideals, using no Chebotarev
density theorem.
-/

/- Cubic finite-field counts for Erdős 940. -/

namespace Erdos940CubicLocal

open Finset Polynomial

private abbrev Triple (F : Type) := F × F × F

private def equation {F : Type} [Field F] (a b c u : F) (v : Triple F) : Prop :=
  a * v.1 ^ 3 + b * v.2.1 ^ 3 + c * v.2.2 ^ 3 = u

/-- Ordered solutions of a weighted cubic equation over a finite field. -/
noncomputable def count {F : Type} [Field F] (a b c u : F) : ℕ :=
  Nat.card {v : Triple F // equation a b c u v}

/-- Nonzero cubic coefficients can be removed by rescaling the variables. -/
theorem count_cube_coefficients {F : Type} [Field F] {a b c : F}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (u : F) :
    count (a ^ 3) (b ^ 3) (c ^ 3) u = count 1 1 1 u := by
  let e : Triple F ≃ Triple F :=
    { toFun := fun v => (a * v.1, b * v.2.1, c * v.2.2)
      invFun := fun v => (a⁻¹ * v.1, b⁻¹ * v.2.1, c⁻¹ * v.2.2)
      left_inv := by
        rintro ⟨x, y, z⟩
        simp [ha, hb, hc]
      right_inv := by
        rintro ⟨x, y, z⟩
        simp [ha, hb, hc] }
  apply Nat.card_congr (e.subtypeEquiv ?_)
  intro v
  simp [equation, e, mul_pow]

private lemma cube_fiber_card_le {F : Type} [Field F] [Fintype F] (d : F) :
    Nat.card {x : F // x ^ 3 = d} ≤ 3 := by
  classical
  let P : F[X] := X ^ 3 - C d
  have hp : P ≠ 0 := Polynomial.X_pow_sub_C_ne_zero (by decide) d
  have hP : P.natDegree = 3 := Polynomial.natDegree_X_pow_sub_C
  have hmem : (univ.filter (fun x : F => x ^ 3 = d)).val ⊆ P.roots := by
    intro x hx
    apply (Polynomial.mem_roots hp).2
    have hx' := (mem_filter.mp (Finset.mem_def.mpr hx)).2
    simp [P, hx']
  simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype, hP] using
    (Polynomial.card_le_degree_of_subset_roots hmem)

private lemma fiber_equation {F : Type} [Field F] {a b c u : F}
    (ha : a ≠ 0) (x y z : F) :
    equation a b c u (x, y, z) ↔ x ^ 3 = (u - (b * y ^ 3 + c * z ^ 3)) / a := by
  unfold equation
  simp only
  rw [eq_div_iff ha]
  constructor <;> intro h <;> linear_combination h

private def sliceEquiv {F : Type} [Field F] {a b c u : F} (ha : a ≠ 0) :
    {v : Triple F // equation a b c u v} ≃
      Σ p : F × F, {x : F // x ^ 3 = (u - (b * p.1 ^ 3 + c * p.2 ^ 3)) / a} where
  toFun v := ⟨v.val.2, ⟨v.val.1, (fiber_equation ha _ _ _).mp v.property⟩⟩
  invFun v := ⟨(v.2.val, v.1), (fiber_equation ha _ _ _).mpr v.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem count_le_of_first_ne {F : Type} [Field F] [Fintype F] {a b c u : F} (ha : a ≠ 0) :
    count a b c u ≤ 3 * (Fintype.card F) ^ 2 := by
  classical
  unfold count
  rw [Nat.card_congr (sliceEquiv ha), Nat.card_sigma]
  calc
    _ ≤ ∑ _ : F × F, (3 : ℕ) := Finset.sum_le_sum fun _ _ => cube_fiber_card_le _
    _ = _ := by simp [pow_two, mul_comm]

private theorem count_swap {F : Type} [Field F] (a b c u : F) :
    count a b c u = count b a c u := by
  let e : Triple F ≃ Triple F :=
    { toFun := fun v => (v.2.1, v.1, v.2.2)
      invFun := fun v => (v.2.1, v.1, v.2.2)
      left_inv _ := rfl
      right_inv _ := rfl }
  apply Nat.card_congr (e.subtypeEquiv ?_)
  intro v
  simp [equation, e, add_comm (a * v.1 ^ 3)]

private theorem count_rotate {F : Type} [Field F] (a b c u : F) :
    count a b c u = count c a b u := by
  let e : Triple F ≃ Triple F :=
    { toFun := fun v => (v.2.2, v.1, v.2.1)
      invFun := fun v => (v.2.1, v.2.2, v.1)
      left_inv _ := rfl
      right_inv _ := rfl }
  apply Nat.card_congr (e.subtypeEquiv ?_)
  intro v
  simp [equation, e, add_left_comm, add_comm, add_assoc]

/-- The elementary 3q² bound for arbitrary coefficients and a nonzero target. -/
theorem count_le_three_times_card_sq {F : Type} [Field F] [Fintype F]
    (a b c u : F) (hu : u ≠ 0) : count a b c u ≤ 3 * (Fintype.card F) ^ 2 := by
  classical
  by_cases ha : a = 0
  · by_cases hb : b = 0
    · by_cases hc : c = 0
      · subst a; subst b; subst c
        have : IsEmpty {v : Triple F // equation (0 : F) 0 0 u v} :=
          ⟨fun v => hu (by simpa [equation] using v.property.symm)⟩
        unfold count
        simp
      · rw [count_rotate]
        exact count_le_of_first_ne hc
    · rw [count_swap]
      exact count_le_of_first_ne hb
  · exact count_le_of_first_ne ha


open Finset

private noncomputable def exponentialSum {F : Type} [Field F] [Fintype F]
    (ψ : AddChar F ℂ) (a t : F) : ℂ := ∑ x : F, ψ (t * (a * x^3))

/-- Orthogonality expresses the local count as a finite Fourier expansion. -/
theorem count_times_card_eq_fourier {F : Type} [Field F] [Fintype F]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (a b c u : F) :
    (Fintype.card F : ℂ) * (count a b c u : ℂ) =
      ∑ t : F, ψ (-(t * u)) * exponentialSum ψ a t *
        exponentialSum ψ b t * exponentialSum ψ c t := by
  classical
  let f (v : Triple F) := a * v.1 ^ 3 + b * v.2.1 ^ 3 + c * v.2.2 ^ 3 - u
  have hOrth (v : Triple F) : (∑ t : F, ψ (t * f v)) =
      if f v = 0 then (Fintype.card F : ℂ) else 0 := by
    simpa only [Nat.cast_ite, Nat.cast_zero] using AddChar.sum_mulShift (f v) hψ
  have hZero : (univ.filter (fun v : Triple F => f v = 0)).card = count a b c u := by
    unfold count equation
    simp only [Nat.card_eq_fintype_card, Fintype.card_subtype, f, sub_eq_zero]
  have hFact (t : F) : (∑ v : Triple F, ψ (t * f v)) =
      ψ (-(t * u)) * exponentialSum ψ a t * exponentialSum ψ b t * exponentialSum ψ c t := by
    have hterm (x y z : F) :
        ψ (t * f (x, y, z)) =
          ((ψ (-(t * u)) * ψ (t * (a * x^3))) * ψ (t * (b * y^3))) * ψ (t * (c * z^3)) := by
      have he : t * f (x, y, z) =
        -(t*u) + t*(a*x^3) + t*(b*y^3) + t*(c*z^3) := by dsimp [f]; ring
      rw [he, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul]
    simp only [Fintype.sum_prod_type, hterm, exponentialSum, Finset.sum_mul, Finset.mul_sum]
    let E (x y z : F) := ψ (-(t * u)) * ψ (t * (a * x^3)) *
      ψ (t * (b * y^3)) * ψ (t * (c * z^3))
    change (∑ x : F, ∑ y : F, ∑ z : F, E x y z) = ∑ z : F, ∑ y : F, ∑ x : F, E x y z
    calc
      _ = ∑ x : F, ∑ z : F, ∑ y : F, E x y z :=
        Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
      _ = ∑ z : F, ∑ x : F, ∑ y : F, E x y z := Finset.sum_comm
      _ = _ := Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
  calc
    _ = ∑ v : Triple F, (if f v = 0 then (Fintype.card F : ℂ) else 0) := by
      rw [← Finset.sum_filter, sum_const, nsmul_eq_mul, hZero, mul_comm]
    _ = ∑ v : Triple F, ∑ t : F, ψ (t * f v) := by simp [hOrth]
    _ = ∑ t : F, ∑ v : Triple F, ψ (t * f v) := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun t _ => hFact t

end Erdos940CubicLocal


namespace Erdos940CubicLocal

/-- A finite field whose multiplicative group has order divisible by three
has a complex-valued multiplicative character of exact order three. -/
theorem exists_cubic_character (F : Type) [Field F] [Finite F] (h : 3 ∣ Nat.card Fˣ) :
    ∃ χ : MulChar F ℂ, orderOf χ = 3 := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  apply exists_prime_orderOf_dvd_card' 3
  simpa only [MulChar.card_eq_card_units_of_hasEnoughRootsOfUnity] using h

private lemma char_pow_three {F : Type} [Field F] {χ : MulChar F ℂ} (hχ : orderOf χ = 3) :
    χ ^ 3 = 1 := orderOf_dvd_iff_pow_eq_one.mp (by rw [hχ])

private lemma char_val_pow_three {F : Type} [Field F] {χ : MulChar F ℂ} (hχ : orderOf χ = 3)
    {u : F} (hu : u ≠ 0) : χ u ^ 3 = 1 := by
  rw [← χ.pow_apply' (by decide : (3 : ℕ) ≠ 0), char_pow_three hχ,
    MulChar.one_apply (isUnit_iff_ne_zero.mpr hu)]

private theorem char_eq_one_iff_cube {F : Type} [Field F] [Finite F]
    {χ : MulChar F ℂ} (hχ : orderOf χ = 3) {u : F} (hu : u ≠ 0) :
    χ u = 1 ↔ ∃ x : F, x ^ 3 = u := by
  constructor
  · intro huχ
    let : Fact (Nat.Prime 3) := ⟨by decide⟩
    obtain ⟨g, hg⟩ := IsCyclic.exists_monoid_generator (α := Fˣ)
    have hgχ : χ (g : F) ≠ 1 := by
      intro hh
      have he : χ = 1 := by
        ext1 v
        obtain ⟨m, hm⟩ := hg v
        rw [← hm]
        have hR := MulChar.one_apply_coe (R' := ℂ) (g ^ m)
        rw [hR, Units.val_pow_eq_pow_val, map_pow, hh, one_pow]
      rw [he, orderOf_one] at hχ
      omega
    have hOrd : orderOf (χ (g : F)) = 3 := orderOf_eq_prime (char_val_pow_three hχ g.ne_zero) hgχ
    obtain ⟨m, hm⟩ := hg (Units.mk0 u hu)
    have hval := congrArg (fun v : Fˣ => (v : F)) hm
    change (g : F) ^ m = u at hval
    have hpow : χ (g : F) ^ m = 1 := by rw [← map_pow, hval, huχ]
    have hd : 3 ∣ m := by simpa only [hOrd] using (orderOf_dvd_iff_pow_eq_one.mpr hpow)
    obtain ⟨k, rfl⟩ := hd
    refine ⟨(g : F) ^ k, ?_⟩
    rw [← pow_mul, mul_comm k 3, hval]
  · rintro ⟨x, rfl⟩
    have hx : x ≠ 0 := fun h => hu (by simp [h])
    rw [map_pow, char_val_pow_three hχ hx]

private theorem card_cube_fiber_of_root {F : Type} [Field F] [Finite F]
    {u x : F} (hx : x ^ 3 = u) (hu : u ≠ 0) (hd : 3 ∣ Nat.card Fˣ) :
    Nat.card {v : F // v ^ 3 = u} = 3 := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hx' : x ≠ 0 := fun he => hu (by simpa [he] using hx.symm)
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' 3 hd
  have hroot : Nat.card (rootsOfUnity 3 F) = 3 :=
    (IsPrimitiveRoot.iff_orderOf.mpr hζ).card_rootsOfUnity'
  let e : F ≃ F :=
    { toFun := fun a => a * x
      invFun := fun a => a / x
      left_inv := fun a => mul_div_cancel_right₀ a hx'
      right_inv := fun a => div_mul_cancel₀ a hx' }
  let h : {v : F // v ∈ Polynomial.nthRoots 3 (1 : F)} ≃ {v : F // v ^ 3 = u} :=
    e.subtypeEquiv (fun v => by
      rw [Polynomial.mem_nthRoots (by decide : 0 < (3 : ℕ))]
      change v ^ 3 = 1 ↔ (v * x) ^ 3 = u
      rw [mul_pow, hx]
      constructor
      · intro hv
        rw [hv, one_mul]
      · intro hv
        apply mul_right_cancel₀ hu
        simpa only [one_mul] using hv)
  exact (Nat.card_congr ((rootsOfUnityEquivNthRoots F 3).trans h).symm).trans hroot

/-- Cube-root multiplicity over a finite field in terms of an order-three
character. The formula also includes the zero fiber. -/
theorem cube_fiber_character {F : Type} [Field F] [Finite F]
    {χ : MulChar F ℂ} (hχ : orderOf χ = 3) (u : F) :
    (Nat.card {x : F // x ^ 3 = u} : ℂ) = 1 + χ u + χ u ^ 2 := by
  by_cases hu : u = 0
  · subst u
    have hE : {x : F // x ^ 3 = 0} ≃ Unit :=
      { toFun := fun _ => ()
        invFun := fun _ => ⟨0, by norm_num⟩
        left_inv := by
          intro x
          apply Subtype.ext
          change (0 : F) = x.val
          by_contra! h
          exact (pow_ne_zero 3 (Ne.symm h)) x.property
        right_inv := fun _ => rfl }
    rw [Nat.card_congr hE]
    simp [MulChar.map_zero]
  · by_cases hcu : ∃ x : F, x ^ 3 = u
    · obtain ⟨x, hx⟩ := hcu
      have hd : 3 ∣ Nat.card Fˣ := by
        rw [← MulChar.card_eq_card_units_of_hasEnoughRootsOfUnity F ℂ, ← hχ]
        exact orderOf_dvd_natCard χ
      rw [card_cube_fiber_of_root hx hu hd, (char_eq_one_iff_cube hχ hu).mpr ⟨x, hx⟩]
      norm_num
    · have : IsEmpty {x : F // x ^ 3 = u} := ⟨fun v => hcu ⟨v.val, v.property⟩⟩
      have hne : χ u ≠ 1 := fun h => hcu ((char_eq_one_iff_cube hχ hu).mp h)
      have hp := char_val_pow_three hχ hu
      have hh : (χ u - 1) * (1 + χ u + χ u ^ 2) = 0 := by linear_combination hp
      have hz := (mul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr hne)
      simpa using hz.symm

end Erdos940CubicLocal


namespace Erdos940CubicLocal

open scoped ComplexConjugate

/-- The two nontrivial cubic roots of unity have sum minus one. -/
theorem nontrivial_cubic_conj_add {z : ℂ} (hc : z ^ 3 = 1) (hn : z ≠ 1) :
    z + conj z = -1 := by
  have hz : z ≠ 0 := by
    intro h
    simp [h] at hc
  have hunit : ‖z‖ = 1 := by
    have hn := congrArg norm hc
    rw [norm_pow, norm_one, ← one_pow (n := 3)] at hn
    exact (pow_left_inj₀ (norm_nonneg _) zero_le_one (by decide : (3 : ℕ) ≠ 0)).mp hn
  have hInv : conj z = z ^ 2 := by
    apply mul_left_cancel₀ hz
    calc
      z * conj z = 1 := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hunit, one_pow, Complex.ofReal_one]
      _ = z * z ^ 2 := by rw [← pow_succ', hc]
  rw [hInv]
  have hx : (z - 1) * (z ^ 2 + z + 1) = 0 := by linear_combination hc
  have hs := (mul_eq_zero.mp hx).resolve_left (sub_ne_zero.mpr hn)
  linear_combination hs

/-- After the cubic character values have sum minus one, the normalized
Gauss-sum identity implies the bound q²-2q for q≥4. -/
theorem noncube_bound_of_gauss_identity {q N : ℕ} (hq : 4 ≤ q) {τ υ : ℂ}
    (hτ : ‖τ‖ = Real.sqrt q) (hυ : ‖υ‖ = Real.sqrt q)
    (hN : (N : ℂ) = (q : ℂ) ^ 2 - 3 * (q : ℂ) - (τ ^ 3 + υ ^ 3) / (q : ℂ)) :
    N ≤ q ^ 2 - 2 * q := by
  have hQ : (4 : ℝ) ≤ q := by exact_mod_cast hq
  have hqpos : 0 < (q : ℝ) := by linarith
  have hs : (Real.sqrt q) ^ 2 = (q : ℝ) := Real.sq_sqrt hqpos.le
  have hsn : 0 ≤ Real.sqrt q := Real.sqrt_nonneg _
  have h2s : 2 * Real.sqrt q ≤ (q : ℝ) := by
    have h2 : 2 ≤ Real.sqrt q := by
      by_contra! h
      nlinarith [mul_nonneg hsn (sub_nonneg.mpr (show Real.sqrt q ≤ 2 from h.le))]
    nlinarith [mul_nonneg hsn (sub_nonneg.mpr h2)]
  have herror : ‖(τ ^ 3 + υ ^ 3) / (q : ℂ)‖ ≤ (q : ℝ) := by
    rw [norm_div, Complex.norm_natCast]
    apply (div_le_iff₀ hqpos).mpr
    calc
      _ ≤ ‖τ ^ 3‖ + ‖υ ^ 3‖ := norm_add_le _ _
      _ = (q : ℝ) * (2 * Real.sqrt q) := by rw [norm_pow, norm_pow, hτ, hυ]; nlinarith [congrArg (fun x => x * Real.sqrt q) hs]
      _ ≤ _ := mul_le_mul_of_nonneg_left h2s hqpos.le
  have hR := congrArg Complex.re hN
  have hqZ : ((q : ℂ) ^ 2).re = (q : ℝ) ^ 2 := by norm_cast
  have hqL : (3 * (q : ℂ)).re = 3 * (q : ℝ) := by norm_cast
  simp only [Complex.sub_re, Complex.natCast_re, hqZ, hqL] at hR
  have habs := Complex.abs_re_le_norm ((τ ^ 3 + υ ^ 3) / (q : ℂ))
  have hbound : (N : ℝ) ≤ (q : ℝ) ^ 2 - 2 * (q : ℝ) := by
    linarith [neg_le_abs (((τ ^ 3 + υ ^ 3) / (q : ℂ)).re)]
  have hsq : 2 * q ≤ q ^ 2 := by nlinarith
  apply (Nat.cast_le (α := ℝ)).mp
  simpa only [Nat.cast_sub hsq, Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat] using hbound

end Erdos940CubicLocal


namespace Erdos940CubicLocal

open Finset
open scoped ComplexConjugate

private lemma char_ne_one_of_order_three {F : Type} [Field F] {χ : MulChar F ℂ}
    (hχ : orderOf χ = 3) : χ ≠ 1 := by
  intro h
  rw [h, orderOf_one] at hχ
  omega

private lemma char_square_inv {F : Type} [Field F] {χ : MulChar F ℂ}
    (hχ : orderOf χ = 3) : χ ^ 2 = χ⁻¹ := by
  apply (inv_eq_of_mul_eq_one_right ?_).symm
  simpa only [← pow_succ'] using char_pow_three hχ

private lemma char_at_neg_one {F : Type} [Field F] {χ : MulChar F ℂ}
    (hχ : orderOf χ = 3) : χ (-1) = 1 := by
  have h2 : χ (-1) ^ 2 = 1 := by rw [← map_pow]; simp
  have h3 := char_val_pow_three hχ (neg_ne_zero.mpr (one_ne_zero : (1 : F) ≠ 0))
  rw [pow_succ, h2, one_mul] at h3
  exact h3

private theorem gaussSum_cubic_pair {F : Type} [Field F] [Fintype F]
    {χ : MulChar F ℂ} (hχ : orderOf χ = 3) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) :
    gaussSum χ ψ * gaussSum (χ ^ 2) ψ = Fintype.card F := by
  have h := gaussSum_mul_gaussSum_pow_orderOf_sub_one (char_ne_one_of_order_three hχ) hψ
  simpa only [hχ, show (3 : ℕ) - 1 = 2 by decide, char_at_neg_one hχ, one_mul] using h

private theorem weighted_sum_cubes {F : Type} [Field F] [Fintype F]
    {χ : MulChar F ℂ} (hχ : orderOf χ = 3) (ψ : AddChar F ℂ) (s : F) :
    exponentialSum ψ 1 s =
      ∑ y : F, (1 + χ y + χ y ^ 2) * ψ (s * y) := by
  classical
  unfold exponentialSum
  simp only [one_mul]
  rw [← Finset.sum_fiberwise' univ (fun v : F => v ^ 3) (fun y => ψ (s * y))]
  apply Finset.sum_congr rfl
  intro y _
  have hf := cube_fiber_character hχ y
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype] at hf
  rw [Finset.sum_const, nsmul_eq_mul, hf]

private theorem gaussExpansion {F : Type} [Field F] [Fintype F]
    {χ : MulChar F ℂ} (hχ : orderOf χ = 3) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {s : F} (hs : s ≠ 0) :
    exponentialSum ψ 1 s = gaussSum χ ψ * χ s ^ 2 + gaussSum (χ ^ 2) ψ * χ s := by
  classical
  let a := Units.mk0 s hs
  have h₁ : (∑ y : F, ψ (s * y)) = 0 := by
    simpa only [mul_comm s, if_neg hs, Nat.cast_zero] using AddChar.sum_mulShift s hψ
  have h₂ : (∑ y : F, χ y * ψ (s * y)) = χ s ^ 2 * gaussSum χ ψ := by
    have h := gaussSum_mulShift_eq χ ψ a
    rw [← char_square_inv hχ, χ.pow_apply' (by decide : (2 : ℕ) ≠ 0)] at h
    simpa only [gaussSum, AddChar.mulShift_apply, a, Units.val_mk0, mul_comm s] using h
  have h₃ : (∑ y : F, χ y ^ 2 * ψ (s * y)) = χ s * gaussSum (χ ^ 2) ψ := by
    have h := gaussSum_mulShift_eq (χ ^ 2) ψ a
    simp only [char_square_inv hχ, inv_inv] at h
    simpa only [gaussSum, AddChar.mulShift_apply, a, Units.val_mk0, mul_comm s, ← char_square_inv hχ,
      χ.pow_apply' (by decide : (2 : ℕ) ≠ 0)] using h
  rw [weighted_sum_cubes hχ ψ s]
  simp only [add_mul, one_mul, Finset.sum_add_distrib, h₁, h₂, h₃, zero_add]
  ring

private lemma cubic_expansion {τ υ z q : ℂ} (hz : z ^ 3 = 1) (hτ : τ * υ = q) :
    (τ * z ^ 2 + υ * z) ^ 3 = τ ^ 3 + υ ^ 3 + 3 * q * τ * z ^ 2 + 3 * q * υ * z := by
  calc
    _ = τ ^ 3 * (z ^ 3) ^ 2 + υ ^ 3 * z ^ 3 +
      3 * (τ * υ) * τ * z ^ 3 * z ^ 2 + 3 * (τ * υ) * υ * z ^ 3 * z := by ring
    _ = _ := by rw [hz, hτ]; ring

private theorem erased_fourier_sums {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {χ : MulChar F ℂ} (hχ : orderOf χ = 3) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {u : F} (hu : u ≠ 0) :
    let T : Finset F := univ.erase 0
    let e (s : F) := ψ (-(s*u))
    (∑ s ∈ T, e s) = -1 ∧
    (∑ s ∈ T, e s * χ s) = χ u ^ 2 * gaussSum χ ψ ∧
    (∑ s ∈ T, e s * χ s ^ 2) = χ u * gaussSum (χ ^ 2) ψ := by
  classical
  let τ := gaussSum χ ψ
  let υ := gaussSum (χ ^ 2) ψ
  let T : Finset F := univ.erase 0
  let e (s : F) := ψ (-(s*u))
  have hTot : (∑ s : F, e s) = 0 := by
    have he : Neg.neg u ≠ 0 := neg_ne_zero.mpr hu
    simpa only [e, mul_neg, if_neg he, Nat.cast_zero] using AddChar.sum_mulShift (-u) hψ
  have hEzero : e 0 = 1 := by simp [e]
  have hEsum : (∑ s ∈ T, e s) = -1 := by
    have h := Finset.sum_erase_add univ e (mem_univ (0 : F))
    change (∑ s ∈ T, e s) + e 0 = ∑ s : F, e s at h
    rw [hEzero, hTot] at h
    linear_combination h
  have hP (j : ℕ) (hj : j ≠ 0) :
      (∑ s ∈ T, e s * χ s ^ j) = gaussSum (χ ^ j) (ψ.mulShift (-(Units.mk0 u hu) : Fˣ)) := by
    have h := Finset.sum_erase_add univ (fun s => e s * χ s ^ j) (mem_univ (0 : F))
    change (∑ s ∈ T, e s * χ s ^ j) + e 0 * χ 0 ^ j = ∑ s : F, e s * χ s ^ j at h
    rw [MulChar.map_zero, zero_pow hj, mul_zero, add_zero] at h
    rw [h, gaussSum]
    apply Finset.sum_congr rfl
    intro s _
    simp only [χ.pow_apply' hj, AddChar.mulShift_apply, Units.val_neg, Units.val_mk0,
      e, neg_mul, mul_comm u s, mul_comm (ψ _)]
  have hNeg : χ (-u) = χ u := by
    calc
      _ = χ ((-1) * u) := by rw [neg_one_mul]
      _ = _ := by rw [map_mul, char_at_neg_one hχ, one_mul]
  have h₁ : (∑ s ∈ T, e s * χ s) = χ u ^ 2 * τ := by
    have h := hP 1 one_ne_zero
    simp only [pow_one] at h
    rw [gaussSum_mulShift_eq, ← char_square_inv hχ,
      χ.pow_apply' (by decide : (2 : ℕ) ≠ 0)] at h
    simpa only [Units.val_neg, Units.val_mk0, hNeg, τ] using h
  have h₂ : (∑ s ∈ T, e s * χ s ^ 2) = χ u * υ := by
    have h := hP 2 (by decide)
    rw [gaussSum_mulShift_eq, char_square_inv hχ, inv_inv] at h
    simpa only [Units.val_neg, Units.val_mk0, hNeg, ← char_square_inv hχ, υ] using h
  exact ⟨hEsum, h₁, h₂⟩

/-- The three-cube local count, with the Gauss-sum term retained exactly. -/
theorem three_cubes_gauss_identity {F : Type} [Field F] [Fintype F]
    {χ : MulChar F ℂ} (hχ : orderOf χ = 3) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {u : F} (hu : u ≠ 0) :
    let q : ℂ := Fintype.card F
    let τ := gaussSum χ ψ
    let υ := gaussSum (χ ^ 2) ψ
    (count (1 : F) 1 1 u : ℂ) =
      q ^ 2 + 3 * q * (χ u + χ u ^ 2) - (τ ^ 3 + υ ^ 3) / q := by
  classical
  let q : ℂ := Fintype.card F
  let τ := gaussSum χ ψ
  let υ := gaussSum (χ ^ 2) ψ
  let T : Finset F := univ.erase 0
  let e (s : F) := ψ (-(s*u))
  have hτu : τ * υ = q := gaussSum_cubic_pair hχ hψ
  have hq : q ≠ 0 := by
    change ((Fintype.card F : ℕ) : ℂ) ≠ 0
    exact_mod_cast Fintype.card_ne_zero
  obtain ⟨hEsum, h₁, h₂⟩ := erased_fourier_sums hχ hψ hu
  have hEzero : e 0 = 1 := by simp [e]
  have hZero : exponentialSum ψ 1 (0 : F) = q := by simp [exponentialSum, q]
  let A (s : F) := e s * exponentialSum ψ 1 s * exponentialSum ψ 1 s * exponentialSum ψ 1 s
  have hA (s : F) (hs : s ∈ T) :
      A s = e s * (τ^3 + υ^3) + (3*q*τ) * (e s * χ s^2) + (3*q*υ) * (e s * χ s) := by
    have hs' := (mem_erase.mp hs).1
    have hx := gaussExpansion hχ hψ hs'
    unfold A
    rw [show e s * exponentialSum ψ 1 s * exponentialSum ψ 1 s * exponentialSum ψ 1 s =
      e s * (exponentialSum ψ 1 s)^3 by ring,
      hx, cubic_expansion (char_val_pow_three hχ hs') hτu]
    ring
  have hf := count_times_card_eq_fourier hψ (1 : F) 1 1 u
  change q * (count (1 : F) 1 1 u : ℂ) = ∑ s, A s at hf
  have hsplit := Finset.sum_erase_add univ A (mem_univ (0 : F))
  change (∑ s ∈ T, A s) + A 0 = ∑ s : F, A s at hsplit
  rw [← hsplit, Finset.sum_congr rfl hA] at hf
  have hqcube : A 0 = q ^ 3 := by simp [A, hEzero, hZero]; ring
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
    ← Finset.mul_sum, hEsum, h₂, h₁, hqcube] at hf
  change (count (1 : F) 1 1 u : ℂ) = q ^ 2 + 3 * q * (χ u + χ u ^ 2) - (τ ^ 3 + υ ^ 3) / q
  apply mul_left_cancel₀ hq
  rw [hf]
  field_simp [hq]
  linear_combination (3 * q * (χ u + χ u ^ 2)) * hτu

end Erdos940CubicLocal

namespace Erdos940CubicLocal

open scoped ComplexConjugate

private theorem gauss_norm_pair {F : Type} [Field F] [Fintype F]
    {χ : MulChar F ℂ} (hχ : orderOf χ = 3) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) :
    ‖gaussSum χ ψ‖ = Real.sqrt (Fintype.card F) ∧
      ‖gaussSum (χ ^ 2) ψ‖ = Real.sqrt (Fintype.card F) := by
  let τ := gaussSum χ ψ
  let υ := gaussSum (χ ^ 2) ψ
  have he : conj τ = υ := by
    change star (gaussSum χ ψ) = gaussSum (χ ^ 2) ψ
    rw [star_gaussSum_eq, ← char_square_inv hχ]
    have h := mul_gaussSum_inv_eq_gaussSum (χ ^ 2) ψ
    simpa only [χ.pow_apply' (by decide : (2 : ℕ) ≠ 0), char_at_neg_one hχ, one_pow, one_mul]
      using h
  have hNorm : ‖υ‖ = ‖τ‖ := by rw [← he, Complex.norm_conj]
  have hSq := congrArg norm (gaussSum_cubic_pair hχ hψ)
  change ‖τ * υ‖ = ‖(Fintype.card F : ℂ)‖ at hSq
  rw [norm_mul, hNorm, ← pow_two, Complex.norm_natCast] at hSq
  have hEq : ‖τ‖ = Real.sqrt (Fintype.card F) := by
    rw [← hSq, Real.sqrt_sq (norm_nonneg _)]
  exact ⟨hEq, hNorm.trans hEq⟩

/-- The saving for a noncube target in the uniform cubic local count. -/
theorem three_cubes_noncube_saving {F : Type} [Field F] [Fintype F]
    (hsize : 4 ≤ Fintype.card F) (hdiv : 3 ∣ Nat.card Fˣ)
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {u : F} (hu : ¬ ∃ x : F, x ^ 3 = u) :
    count (1 : F) 1 1 u ≤ Fintype.card F ^ 2 - 2 * Fintype.card F := by
  obtain ⟨χ, hχ⟩ := exists_cubic_character F hdiv
  have hu0 : u ≠ 0 := fun hh => hu ⟨0, by simp [hh]⟩
  have hc : χ u + χ u ^ 2 = -1 := by
    have hcub := char_val_pow_three hχ hu0
    have hn : χ u ≠ 1 := fun he => hu ((char_eq_one_iff_cube hχ hu0).mp he)
    have ha : (χ u - 1) * (χ u + χ u ^ 2 + 1) = 0 := by linear_combination hcub
    linear_combination (mul_eq_zero.mp ha).resolve_left (sub_ne_zero.mpr hn)
  obtain ⟨hτ, hυ⟩ := gauss_norm_pair hχ hψ
  refine noncube_bound_of_gauss_identity hsize hτ hυ ?_
  have he := three_cubes_gauss_identity hχ hψ hu0
  dsimp only at he
  rw [hc] at he
  linear_combination he

end Erdos940CubicLocal

namespace Erdos940CubicLocal

open Finset

private theorem norm_char_nonzero {F : Type} [Field F] {χ : MulChar F ℂ}
    (hχ : orderOf χ = 3) {y : F} (hy : y ≠ 0) : ‖χ y‖ = 1 := by
  have h := congrArg norm (char_val_pow_three hχ hy)
  rw [norm_pow, norm_one, ← one_pow (n := 3)] at h
  exact (pow_left_inj₀ (norm_nonneg _) zero_le_one (by decide : (3 : ℕ) ≠ 0)).mp h

private lemma weighted_expansion {z a b c d e f : ℂ} (hz : z ^ 3 = 1) :
    (a * z^2 + d*z) * (b*z^2 + e*z) * (c*z^2 + f*z) =
      (a*b*c + d*e*f) + (a*b*f + a*e*c + d*b*c)*z^2 +
        (a*e*f + d*b*f + d*e*c)*z := by
  calc
    _ = a*b*c*(z^3)^2 + d*e*f*z^3 +
      (a*b*f + a*e*c + d*b*c)*z^3*z^2 +
      (a*e*f + d*b*f + d*e*c)*z^3*z := by ring
    _ = _ := by rw [hz]; ring

/-- The weighted local error bound with all three coefficients nonzero. -/
theorem weighted_error_bound {F : Type} [Field F] [Fintype F]
    (hsize : 4 ≤ Fintype.card F) (hdiv : 3 ∣ Nat.card Fˣ)
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {a b c u : F}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hu : u ≠ 0) :
    ‖(count a b c u : ℂ) - (Fintype.card F : ℂ)^2‖ ≤ 8 * (Fintype.card F : ℝ) := by
  classical
  obtain ⟨χ, hχ⟩ := exists_cubic_character F hdiv
  let q : ℂ := Fintype.card F
  let Q : ℝ := Fintype.card F
  let R := Real.sqrt Q
  let τ := gaussSum χ ψ
  let υ := gaussSum (χ ^ 2) ψ
  let X (a : F) := τ * χ a ^ 2
  let Y (a : F) := υ * χ a
  let U := X a * X b * X c + Y a * Y b * Y c
  let V := X a * X b * Y c + X a * Y b * X c + Y a * X b * X c
  let W := X a * Y b * Y c + Y a * X b * Y c + Y a * Y b * X c
  let T : Finset F := univ.erase 0
  let e (s : F) := ψ (-(s*u))
  have hS (v s : F) (hv : v ≠ 0) (hs : s ≠ 0) :
      exponentialSum ψ v s = X v * χ s ^ 2 + Y v * χ s := by
    have he : exponentialSum ψ v s = exponentialSum ψ 1 (v * s) := by
      unfold exponentialSum
      apply Finset.sum_congr rfl
      intro x _
      simp only [one_mul]
      congr 1
      ring
    rw [he, gaussExpansion hχ hψ (mul_ne_zero hv hs), map_mul]
    dsimp [X, Y, τ, υ]
    ring
  have hZero (v : F) : exponentialSum ψ v (0 : F) = q := by simp [exponentialSum, q]
  have hEzero : e 0 = 1 := by simp [e]
  let A (s : F) := e s * exponentialSum ψ a s * exponentialSum ψ b s * exponentialSum ψ c s
  have hA (s : F) (hs : s ∈ T) :
      A s = e s * U + V * (e s * χ s^2) + W * (e s * χ s) := by
    have hs' := (mem_erase.mp hs).1
    unfold A
    rw [show e s * exponentialSum ψ a s * exponentialSum ψ b s * exponentialSum ψ c s =
      e s * (exponentialSum ψ a s * exponentialSum ψ b s * exponentialSum ψ c s) by ring,
      hS a s ha hs', hS b s hb hs', hS c s hc hs',
      weighted_expansion (char_val_pow_three hχ hs')]
    dsimp [U, V, W]
    ring
  have hf := count_times_card_eq_fourier hψ a b c u
  change q * (count a b c u : ℂ) = ∑ s, A s at hf
  have hsplit := Finset.sum_erase_add univ A (mem_univ (0 : F))
  change (∑ s ∈ T, A s) + A 0 = ∑ s : F, A s at hsplit
  rw [← hsplit, Finset.sum_congr rfl hA] at hf
  have hqcube : A 0 = q ^ 3 := by simp [A, hEzero, hZero]; ring
  obtain ⟨hEsum, h₁, h₂⟩ := erased_fourier_sums hχ hψ hu
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
    ← Finset.mul_sum, hEsum, h₂, h₁, hqcube] at hf
  have hIdent : q * ((count a b c u : ℂ) - q^2) =
      -U + V * (χ u * υ) + W * (χ u^2 * τ) := by
    dsimp [τ, υ] at hf ⊢
    linear_combination hf
  obtain ⟨hτ, hυ⟩ := gauss_norm_pair hχ hψ
  have hX (v : F) (hv : v ≠ 0) : ‖X v‖ = R := by
    simp only [X, τ, norm_mul, norm_pow, hτ, norm_char_nonzero hχ hv, one_pow, mul_one, R, Q]
  have hY (v : F) (hv : v ≠ 0) : ‖Y v‖ = R := by
    simp only [Y, υ, norm_mul, hυ, norm_char_nonzero hχ hv, mul_one, R, Q]
  have boundU : ‖U‖ ≤ 2 * R^3 := by
    have h := norm_add_le (X a * X b * X c) (Y a * Y b * Y c)
    simp only [norm_mul, hX a ha, hX b hb, hX c hc, hY a ha, hY b hb, hY c hc] at h
    change ‖U‖ ≤ _
    nlinarith only [h]
  have boundV : ‖V‖ ≤ 3 * R^3 := by
    have h := (norm_add_le (X a * X b * Y c + X a * Y b * X c) (Y a * X b * X c)).trans
      (add_le_add (norm_add_le (X a * X b * Y c) (X a * Y b * X c)) le_rfl)
    simp only [norm_mul, hX a ha, hX b hb, hX c hc, hY a ha, hY b hb, hY c hc] at h
    change ‖V‖ ≤ _
    nlinarith only [h]
  have boundW : ‖W‖ ≤ 3 * R^3 := by
    have h := (norm_add_le (X a * Y b * Y c + Y a * X b * Y c) (Y a * Y b * X c)).trans
      (add_le_add (norm_add_le (X a * Y b * Y c) (Y a * X b * Y c)) le_rfl)
    simp only [norm_mul, hX a ha, hX b hb, hX c hc, hY a ha, hY b hb, hY c hc] at h
    change ‖W‖ ≤ _
    nlinarith only [h]
  have hM₁ : ‖χ u * υ‖ = R := by
    simp only [norm_mul, norm_char_nonzero hχ hu, one_mul, υ, hυ, R, Q]
  have hM₂ : ‖χ u ^ 2 * τ‖ = R := by
    simp only [norm_mul, norm_pow, norm_char_nonzero hχ hu, one_pow, one_mul, τ, hτ, R, Q]
  have hQ : (4 : ℝ) ≤ Q := by
    change (4 : ℝ) ≤ (Fintype.card F : ℝ)
    exact_mod_cast hsize
  have hQpos : 0 < Q := by linarith
  have hR : 0 ≤ R := Real.sqrt_nonneg _
  have hsq : R^2 = Q := Real.sq_sqrt hQpos.le
  have hR₁ : 1 ≤ R := by by_contra! h; nlinarith
  have h₃₄ : R^3 ≤ R^4 := by
    have hh := mul_le_mul_of_nonneg_left hR₁ (pow_nonneg hR 3)
    simpa only [mul_one, ← pow_succ] using hh
  have hBound : ‖-U + V * (χ u * υ) + W * (χ u^2 * τ)‖ ≤ 8 * Q^2 := by
    calc
      _ ≤ ‖U‖ + ‖V‖ * R + ‖W‖ * R := by
        have hh := (norm_add_le (-U + V * (χ u * υ)) (W * (χ u^2 * τ))).trans
          (add_le_add (norm_add_le (-U) (V * (χ u * υ))) le_rfl)
        simpa only [norm_neg, norm_mul, hM₁, hM₂] using hh
      _ ≤ 2 * R^3 + (3 * R^3) * R + (3 * R^3) * R := by
        exact add_le_add (add_le_add boundU (mul_le_mul_of_nonneg_right boundV hR))
          (mul_le_mul_of_nonneg_right boundW hR)
      _ ≤ 8 * Q^2 := by nlinarith [congrArg (fun y : ℝ => y^2) hsq]
  have hh := congrArg norm hIdent
  rw [norm_mul] at hh
  have hqN : ‖q‖ = Q := by simp [q, Q]
  rw [hqN] at hh
  change ‖(count a b c u : ℂ) - q^2‖ ≤ 8*Q
  apply (mul_le_mul_iff_right₀ hQpos).mp
  rw [hh]
  calc
    _ ≤ 8 * Q^2 := hBound
    _ = _ := by ring

end Erdos940CubicLocal



/- Multiplicativity of the cubic congruence count under coprime products. -/

namespace Erdos940CubicCRT

open Finset

private abbrev Triple (R : Type) := R × R × R

private abbrev Solutions {R : Type} [CommRing R] (a b c u : R) :=
  {v : Triple R // a * v.1 ^ 3 + b * v.2.1 ^ 3 + c * v.2.2 ^ 3 = u}

private theorem card_via_equiv {R S : Type} [CommRing R] [CommRing S] (e : R ≃+* S)
    (a b c u : R) :
    Nat.card (Solutions a b c u) = Nat.card (Solutions (e a) (e b) (e c) (e u)) := by
  let E := Equiv.prodCongr e.toEquiv (Equiv.prodCongr e.toEquiv e.toEquiv)
  apply Nat.card_congr (E.subtypeEquiv ?_)
  intro x
  change a * x.1^3 + b * x.2.1^3 + c * x.2.2^3 = u ↔
    e a * e x.1^3 + e b * e x.2.1^3 + e c * e x.2.2^3 = e u
  rw [← map_pow, ← map_pow, ← map_pow, ← map_mul, ← map_mul, ← map_mul,
    ← map_add, ← map_add, e.injective.eq_iff]

private def splitProd {R S : Type} [CommRing R] [CommRing S] (a b c u : R × S) :
    Solutions a b c u ≃ Solutions a.1 b.1 c.1 u.1 × Solutions a.2 b.2 c.2 u.2 where
  toFun v :=
    (⟨(v.val.1.1, v.val.2.1.1, v.val.2.2.1), congrArg Prod.fst v.property⟩,
     ⟨(v.val.1.2, v.val.2.1.2, v.val.2.2.2), congrArg Prod.snd v.property⟩)
  invFun v :=
    ⟨((v.1.val.1, v.2.val.1), (v.1.val.2.1, v.2.val.2.1), (v.1.val.2.2, v.2.val.2.2)),
      Prod.ext v.1.property v.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The number of solutions of a weighted cubic congruence modulo M. -/
noncomputable def localCount (M a b c u : ℕ) : ℕ :=
  Nat.card (Solutions (a : ZMod M) (b : ZMod M) (c : ZMod M) (u : ZMod M))

/-- CRT factors the ordered representation count over a product of coprime moduli. -/
theorem count_mul {m n : ℕ} (h : m.Coprime n) (a b c u : ℕ) :
    localCount (m * n) a b c u = localCount m a b c u * localCount n a b c u := by
  let e := ZMod.chineseRemainder h
  unfold localCount
  rw [card_via_equiv e, map_natCast, map_natCast, map_natCast, map_natCast]
  rw [Nat.card_congr (splitProd _ _ _ _), Nat.card_prod]
  rfl

private theorem count_one (a b c u : ℕ) : localCount 1 a b c u = 1 := by
  unfold localCount
  let v : Solutions (a : ZMod 1) (b : ZMod 1) (c : ZMod 1) (u : ZMod 1) :=
    ⟨(0, 0, 0), Subsingleton.elim _ _⟩
  let : Unique (Solutions (a : ZMod 1) (b : ZMod 1) (c : ZMod 1) (u : ZMod 1)) :=
    ⟨⟨v⟩, fun _ => Subsingleton.elim _ _⟩
  exact Nat.card_unique

/-- The full residue count factorizes over any finite pairwise-coprime
family of moduli, in particular over the distinct primes of a squarefree M. -/
theorem count_prod {ι : Type} (P : Finset ι) (m : ι → ℕ)
    (hm : ∀ i ∈ P, ∀ j ∈ P, i ≠ j → (m i).Coprime (m j)) (a b c u : ℕ) :
    localCount (∏ i ∈ P, m i) a b c u = ∏ i ∈ P, localCount (m i) a b c u := by
  classical
  induction P using Finset.induction_on with
  | empty => simp [count_one]
  | insert i P hi ih =>
    have hp : (m i).Coprime (∏ j ∈ P, m j) :=
      Nat.Coprime.prod_right fun j hj => hm i (mem_insert_self _ _) j (mem_insert_of_mem hj)
        (fun h => hi (h ▸ hj))
    have hm' : ∀ v ∈ P, ∀ w ∈ P, v ≠ w → (m v).Coprime (m w) :=
      fun v hv w hw h => hm v (mem_insert_of_mem hv) w (mem_insert_of_mem hw) h
    rw [prod_insert hi, prod_insert hi, count_mul hp, ih hm']

end Erdos940CubicCRT


namespace Erdos940CubicCRT

open Filter
open scoped Topology

private def BoxSolutions (M a b c u X : ℕ) :=
  {v : ℕ × ℕ × ℕ // 0 < v.1 ∧ 0 < v.2.1 ∧ 0 < v.2.2 ∧
    a * v.1^3 + b * v.2.1^3 + c * v.2.2^3 ≤ X ∧
    (a : ZMod M) * (v.1 : ZMod M)^3 + (b : ZMod M) * (v.2.1 : ZMod M)^3 +
      (c : ZMod M) * (v.2.2 : ZMod M)^3 = u}

/-- Count positive solutions up to a weighted cubic cutoff in one progression. -/
noncomputable def boxCount (M a b c u X : ℕ) : ℕ :=
  Nat.card (BoxSolutions M a b c u X)

private noncomputable def scale (d : ℕ) : ℝ := (d : ℝ) ^ (-(1 / 3) : ℝ)
private noncomputable def cubeRoot (X : ℕ) : ℝ := (X : ℝ) ^ (1 / 3 : ℝ)
private noncomputable def coordCap (X d : ℕ) : ℕ := ⌊cubeRoot X * scale d⌋₊

private lemma coordinate_bound {d x X : ℕ} (hd : 0 < d) (h : d * x^3 ≤ X) :
    x ≤ coordCap X d := by
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hR : (d : ℝ) * (x : ℝ)^3 ≤ (X : ℝ) := by exact_mod_cast h
  have hp := Real.rpow_le_rpow (by positivity) hR (by norm_num : (0 : ℝ) ≤ 1 / 3)
  rw [Real.mul_rpow (by positivity) (by positivity),
    ← Real.rpow_natCast_mul (by positivity : (0 : ℝ) ≤ x)] at hp
  norm_num at hp
  have hd' : 0 < (d : ℝ) ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hdR _
  apply (Nat.le_floor_iff (by unfold cubeRoot scale; positivity)).mpr
  change (x : ℝ) ≤ cubeRoot X * (d : ℝ) ^ (-(1 / 3) : ℝ)
  rw [Real.rpow_neg hdR.le, ← div_eq_mul_inv]
  apply (le_div_iff₀ hd').mpr
  simpa [cubeRoot, mul_comm, div_eq_mul_inv] using hp

private lemma nat_eq_of_residue_quotient {M x y : ℕ} [NeZero M]
    (hmod : (x : ZMod M) = (y : ZMod M)) (hdiv : x / M = y / M) : x = y := by
  have he := congrArg ZMod.val hmod
  rw [ZMod.val_natCast, ZMod.val_natCast] at he
  calc
    x = M * (x / M) + x % M := (Nat.div_add_mod x M).symm
    _ = M * (y / M) + y % M := by rw [he, hdiv]
    _ = y := Nat.div_add_mod y M

private lemma cap_div_real (X d M : ℕ) :
    ((coordCap X d / M + 1 : ℕ) : ℝ) ≤ cubeRoot X * scale d / M + 1 := by
  push_cast
  have hnon : 0 ≤ cubeRoot X * scale d := by unfold cubeRoot scale; positivity
  have hcap : (coordCap X d : ℝ) ≤ cubeRoot X * scale d := Nat.floor_le hnon
  exact add_le_add (Nat.cast_div_le.trans (div_le_div_of_nonneg_right hcap (by positivity))) le_rfl

/-- A simple residue-class box gives an upper bound for the cubic solution count. -/
theorem box_count_le {M a b c u X : ℕ} [NeZero M] (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (boxCount M a b c u X : ℝ) ≤ (localCount M a b c u : ℝ) *
      (cubeRoot X * scale a / M + 1) * (cubeRoot X * scale b / M + 1) *
      (cubeRoot X * scale c / M + 1) := by
  classical
  let L := Solutions (a : ZMod M) (b : ZMod M) (c : ZMod M) (u : ZMod M)
  let A := coordCap X a / M + 1
  let B := coordCap X b / M + 1
  let C := coordCap X c / M + 1
  let f (x : BoxSolutions M a b c u X) : L × Fin A × Fin B × Fin C := by
    have hx := x.property.2.2.2.1
    have h₁ : x.val.1 ≤ coordCap X a := coordinate_bound ha (by omega)
    have h₂ : x.val.2.1 ≤ coordCap X b := coordinate_bound hb (by omega)
    have h₃ : x.val.2.2 ≤ coordCap X c := coordinate_bound hc (by omega)
    exact ⟨⟨(x.val.1, x.val.2.1, x.val.2.2), x.property.2.2.2.2⟩,
      ⟨x.val.1 / M, (Nat.div_le_div_right h₁).trans_lt (Nat.lt_succ_self _)⟩,
      ⟨x.val.2.1 / M, (Nat.div_le_div_right h₂).trans_lt (Nat.lt_succ_self _)⟩,
      ⟨x.val.2.2 / M, (Nat.div_le_div_right h₃).trans_lt (Nat.lt_succ_self _)⟩⟩
  have hf : Function.Injective f := by
    intro x y he
    apply Subtype.ext
    apply Prod.ext
    · exact nat_eq_of_residue_quotient
        (congrArg (fun v => v.1.val.1) he) (congrArg (fun v => v.2.1.val) he)
    · apply Prod.ext
      · exact nat_eq_of_residue_quotient
          (congrArg (fun v => v.1.val.2.1) he) (congrArg (fun v => v.2.2.1.val) he)
      · exact nat_eq_of_residue_quotient
          (congrArg (fun v => v.1.val.2.2) he) (congrArg (fun v => v.2.2.2.val) he)
  have hn := Nat.card_le_card_of_injective f hf
  simp only [Nat.card_prod, Nat.card_fin] at hn
  have hnR : (boxCount M a b c u X : ℝ) ≤ (localCount M a b c u : ℝ) * (A : ℝ) * B * C := by
    unfold localCount boxCount
    rw [mul_assoc, mul_assoc]
    exact_mod_cast hn
  refine hnR.trans ?_
  have hA : (A : ℝ) ≤ cubeRoot X * scale a / M + 1 := cap_div_real X a M
  have hB : (B : ℝ) ≤ cubeRoot X * scale b / M + 1 := cap_div_real X b M
  have hC : (C : ℝ) ≤ cubeRoot X * scale c / M + 1 := cap_div_real X c M
  gcongr <;> unfold cubeRoot scale <;> positivity

/-- The normalized count has an eventual upper bound of the required scale.
A coordinate box suffices for the upper bound, with a constant of one. -/
theorem eventual_box_density_upper {M a b c u : ℕ} [NeZero M]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop, (boxCount M a b c u X : ℝ) / X ≤
      (localCount M a b c u : ℝ) * (scale a / M) * (scale b / M) * (scale c / M) + ε := by
  let limit := (localCount M a b c u : ℝ) * (scale a / M) * (scale b / M) * (scale c / M)
  have h0 : Tendsto (fun X : ℕ => (X : ℝ)^(-(1 / 3) : ℝ)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp tendsto_natCast_atTop_atTop
  let H (d X : ℕ) : ℝ := scale d / M + (X : ℝ)^(-(1 / 3) : ℝ)
  have hH (d : ℕ) : Tendsto (H d) atTop (𝓝 (scale d / M)) := by
    simpa only [add_zero] using h0.const_add (scale d / M)
  have hL : Tendsto (fun X : ℕ => (localCount M a b c u : ℝ) * H a X * H b X * H c X)
      atTop (𝓝 limit) := (((hH a).const_mul _).mul (hH b)).mul (hH c)
  have hev := hL.eventually (gt_mem_nhds (show limit < limit + ε by linarith))
  filter_upwards [eventually_gt_atTop (0 : ℕ), hev] with X hX hXlim
  have hXR : 0 < (X : ℝ) := by exact_mod_cast hX
  have hRoot : 0 < cubeRoot X := Real.rpow_pos_of_pos hXR _
  have hcub : (cubeRoot X)^3 = (X : ℝ) := by
    unfold cubeRoot
    rw [← Real.rpow_mul_natCast hXR.le]
    norm_num
  have ht : (X : ℝ)^(-(1 / 3) : ℝ) = (cubeRoot X)⁻¹ := Real.rpow_neg hXR.le _
  have he (d : ℕ) : cubeRoot X * scale d / M + 1 = cubeRoot X * H d X := by
    dsimp [H]
    rw [ht]
    field_simp [hRoot.ne']
  have hp := box_count_le (X := X) (M := M) (u := u) ha hb hc
  rw [he, he, he] at hp
  have hR : (boxCount M a b c u X : ℝ) / X ≤
      (localCount M a b c u : ℝ) * H a X * H b X * H c X := by
    apply (div_le_iff₀ hXR).mpr
    calc
      _ ≤ (localCount M a b c u : ℝ) * (cubeRoot X * H a X) * (cubeRoot X * H b X) *
          (cubeRoot X * H c X) := hp
      _ = _ := by rw [← hcub]; ring
  exact hR.trans hXlim.le

end Erdos940CubicCRT


namespace Erdos940CubicCRT

private theorem box_finite {M a b c u X : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    Finite (BoxSolutions M a b c u X) := by
  let g (v : BoxSolutions M a b c u X) : Fin (coordCap X a + 1) ×
      Fin (coordCap X b + 1) × Fin (coordCap X c + 1) := by
    have hx := v.property.2.2.2.1
    exact ⟨⟨v.val.1, Nat.lt_succ_of_le (coordinate_bound ha (by omega))⟩,
      ⟨v.val.2.1, Nat.lt_succ_of_le (coordinate_bound hb (by omega))⟩,
      ⟨v.val.2.2, Nat.lt_succ_of_le (coordinate_bound hc (by omega))⟩⟩
  apply Finite.of_injective g
  intro x y h
  exact Subtype.ext (Prod.ext (congrArg (fun t => t.1.val) h)
    (Prod.ext (congrArg (fun t => t.2.1.val) h) (congrArg (fun t => t.2.2.val) h)))

private theorem box_forget {M a b c u X : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    boxCount M a b c u X ≤ boxCount 1 a b c 0 X := by
  let f (v : BoxSolutions M a b c u X) : BoxSolutions 1 a b c 0 X :=
    ⟨v.val, ⟨v.property.1, v.property.2.1, v.property.2.2.1, v.property.2.2.2.1,
      Subsingleton.elim _ _⟩⟩
  let := box_finite (M := 1) (X := X) (u := 0) ha hb hc
  exact Nat.card_le_card_of_injective f (fun _ _ h => Subtype.ext (congrArg (fun v => v.val) h))

private lemma one_le_root_scale {X d : ℕ} (hd : 0 < d) (h : d ≤ X) :
    1 ≤ cubeRoot X * scale d := by
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  unfold cubeRoot scale
  rw [Real.rpow_neg hdR.le, ← div_eq_mul_inv]
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hdR _)).mpr
  rw [one_mul]
  exact Real.rpow_le_rpow hdR.le (by exact_mod_cast h) (by norm_num)

private lemma nonnegative_root_scale (X d : ℕ) : 0 ≤ cubeRoot X * scale d := by
  unfold cubeRoot scale
  positivity

/-- A uniform upper bound on the normalized count, independent of the modulus. -/
theorem box_ratio_le_scale {M a b c u X : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (boxCount M a b c u X : ℝ) / X ≤ 8 * scale a * scale b * scale c := by
  classical
  by_cases h : Nonempty (BoxSolutions M a b c u X)
  · obtain ⟨v⟩ := h
    have hsum := v.property.2.2.2.1
    have hXa : a ≤ X := (Nat.le_mul_of_pos_right _ (pow_pos v.property.1 3)).trans (by omega)
    have hXb : b ≤ X := (Nat.le_mul_of_pos_right _ (pow_pos v.property.2.1 3)).trans (by omega)
    have hXc : c ≤ X := (Nat.le_mul_of_pos_right _ (pow_pos v.property.2.2.1 3)).trans (by omega)
    have hX : 0 < (X : ℝ) := by exact_mod_cast ha.trans_le hXa
    have hR (d : ℕ) (hd : 0 < d) (h : d ≤ X) :
        cubeRoot X * scale d + 1 ≤ 2 * (cubeRoot X * scale d) := by
      linarith [one_le_root_scale hd h]
    have hh := box_count_le (M := 1) (u := 0) (X := X) ha hb hc
    simp only [count_one, Nat.cast_one, div_one, one_mul] at hh
    have hforget : (boxCount M a b c u X : ℝ) ≤ boxCount 1 a b c 0 X := by
      exact_mod_cast box_forget (M := M) (u := u) (X := X) ha hb hc
    have hcub : (cubeRoot X)^3 = (X : ℝ) := by
      unfold cubeRoot
      rw [← Real.rpow_mul_natCast hX.le]
      norm_num
    apply (div_le_iff₀ hX).mpr
    calc
      _ ≤ (cubeRoot X * scale a + 1) * (cubeRoot X * scale b + 1) * (cubeRoot X * scale c + 1) :=
        hforget.trans hh
      _ ≤ (2 * (cubeRoot X * scale a)) * (2 * (cubeRoot X * scale b)) * (2 * (cubeRoot X * scale c)) := by
        gcongr <;> first
          | exact hR a ha hXa
          | exact hR b hb hXb
          | exact hR c hc hXc
          | unfold cubeRoot scale; positivity
      _ = _ := by rw [← hcub]; ring
  · have : IsEmpty (BoxSolutions M a b c u X) := not_nonempty_iff.mp h
    unfold boxCount
    rw [Nat.card_of_isEmpty]
    simp only [Nat.cast_zero, zero_div]
    unfold scale
    positivity

private lemma count_le_cube_modulus {M : ℕ} [NeZero M] (a b c u : ℕ) :
    localCount M a b c u ≤ M^3 := by
  unfold localCount
  have hn := Nat.card_le_card_of_injective
    (Subtype.val : Solutions (a : ZMod M) (b : ZMod M) (c : ZMod M) (u : ZMod M) → Triple (ZMod M))
    Subtype.val_injective
  rw [Nat.card_prod, Nat.card_prod] at hn
  have hcard : Nat.card (ZMod M) = M := by
    rw [Nat.card_eq_fintype_card, ZMod.card]
  rw [hcard] at hn
  calc
    _ ≤ M * (M * M) := hn
    _ = M^3 := by ring

end Erdos940CubicCRT



namespace Erdos940CubicKernels

/-- The coefficient set can include every positive b^4 c^5.
The squarefree restriction in the canonical decomposition is unnecessary
for these upper bounds. -/
def IsKernel (d : ℕ) : Prop :=
  0 < d ∧ ∃ b c : ℕ, 0 < b ∧ 0 < c ∧ d = b^4 * c^5

theorem exists_kernel_of_full {n : ℕ} (hn : 0 < n) (hfull : (3 : ℕ).Full n) :
    ∃ x d : ℕ, 0 < x ∧ IsKernel d ∧ n = x^3 * d := by
  obtain ⟨⟨x, b, c⟩, ⟨hx, hb, hc, _, he⟩, _⟩ :=
    Erdos940FullDecomposition.cube_full_unique_factorization hn hfull
  exact ⟨x, b^4 * c^5, hx, ⟨by positivity, b, c, hb, hc, rfl⟩, he⟩

end Erdos940CubicKernels



namespace Erdos940CubicKernels

open Finset Filter
open scoped Topology

/-- For every positive ε, the factor 3^ω(n) is O(n^ε).
The proof isolates finitely many small primes. -/
theorem three_prime_factor_count_le_rpow (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n → (3 : ℝ) ^ n.primeFactors.card ≤ C * (n : ℝ) ^ ε := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ) ^ ε) atTop atTop :=
    (tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop
  obtain ⟨K, hK⟩ := eventually_atTop.mp (ht.eventually_ge_atTop (3 : ℝ))
  refine ⟨(3 : ℝ)^K, by positivity, ?_⟩
  intro n hn
  let P := n.primeFactors
  let A := P.filter (fun p => p < K)
  let B := P.filter (fun p => ¬ p < K)
  have hcard : A.card + B.card = P.card := Finset.card_filter_add_card_filter_not (s := P) (fun p => p < K)
  have hA : A.card ≤ K := by
    have hh : A ⊆ range K := fun x hx => mem_range.mpr (mem_filter.mp hx).2
    simpa using card_le_card hh
  have hSmall : (3 : ℝ)^A.card ≤ 3^K := pow_le_pow_right₀ (by norm_num) hA
  have hBig : (3 : ℝ)^B.card ≤ ∏ p ∈ B, (p : ℝ)^ε := by
    rw [← Finset.prod_const]
    apply Finset.prod_le_prod (fun _ _ => by norm_num)
    intro p hp
    exact hK p (le_of_not_gt (mem_filter.mp hp).2)
  have hProd : (∏ p ∈ B, p) ≤ n := by
    have hP : ∏ p ∈ P, p ∣ n := Nat.prod_primeFactors_dvd n
    have hsub : B ⊆ P := Finset.filter_subset _ _
    have hD : (∏ p ∈ B, p) ∣ ∏ p ∈ P, p :=
      Finset.prod_dvd_prod_of_subset _ _ _ hsub
    exact Nat.le_of_dvd hn (hD.trans hP)
  have hBig' : (3 : ℝ)^B.card ≤ (n : ℝ)^ε := by
    refine hBig.trans ?_
    rw [Real.finsetProd_rpow _ _ (fun _ _ => by positivity), ← Nat.cast_prod]
    exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hProd) hε.le
  change (3 : ℝ)^P.card ≤ (3 : ℝ)^K * (n : ℝ)^ε
  rw [← hcard, pow_add]
  exact mul_le_mul hSmall hBig' (by positivity) (by positivity)

private theorem summable_weighted_rpow {s : ℝ} (hs : 1 < s) :
    Summable (fun n : ℕ => (3 : ℝ) ^ n.primeFactors.card * (n : ℝ) ^ (-s)) := by
  let ε := (s - 1) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨C, hC, hL⟩ := three_prime_factor_count_le_rpow ε hε
  have hSum : Summable (fun n : ℕ => C * (n : ℝ) ^ (ε - s)) :=
    (Real.summable_nat_rpow.mpr (by dsimp [ε]; linarith)).mul_left C
  apply hSum.of_nonneg_of_le (fun _ => by positivity)
  intro n
  by_cases hn : n = 0
  · subst n
    have h1 : -s ≠ 0 := by linarith
    have h2 : ε - s ≠ 0 := by dsimp [ε]; linarith
    simp [Real.zero_rpow h1, Real.zero_rpow h2]
  · have hR : 0 < (n : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hn)
    have hB := mul_le_mul_of_nonneg_right (hL n (Nat.pos_of_ne_zero hn))
      (show 0 ≤ (n : ℝ)^(-s) by positivity)
    rwa [mul_assoc, ← Real.rpow_add hR, ← sub_eq_add_neg] at hB

/-- Absolute summability of the weighted cubic kernels used for the tail. -/
theorem summable_cubic_kernel_weight :
    Summable (fun d : {d : ℕ // IsKernel d} =>
      (3 : ℝ) ^ d.val.primeFactors.card * (d.val : ℝ) ^ (-(1 / 3) : ℝ)) := by
  classical
  let wt (s : ℝ) (n : ℕ) := (3 : ℝ)^n.primeFactors.card * (n : ℝ)^(-s)
  have h4 : Summable (wt (4 / 3)) := summable_weighted_rpow (by norm_num)
  have h5 : Summable (wt (5 / 3)) := summable_weighted_rpow (by norm_num)
  let S := {d : ℕ // IsKernel d}
  choose b c hb hc he using fun d : S => d.property.2
  let e (d : S) : ℕ × ℕ := (b d, c d)
  have heInj : Function.Injective e := by
    intro x y hxy
    have h₁ : b x = b y := congrArg Prod.fst hxy
    have h₂ : c x = c y := congrArg Prod.snd hxy
    apply Subtype.ext
    rw [he x, he y, h₁, h₂]
  have hsProd : Summable (fun p : ℕ × ℕ => wt (4 / 3) p.1 * wt (5 / 3) p.2) :=
    summable_mul_of_summable_norm h4.norm h5.norm
  apply (hsProd.comp_injective heInj).of_nonneg_of_le (fun _ => by positivity)
  intro d
  change (3 : ℝ)^d.val.primeFactors.card * (d.val : ℝ)^(-(1 / 3) : ℝ) ≤
    wt (4 / 3) (b d) * wt (5 / 3) (c d)
  have hf : d.val.primeFactors.card ≤ (b d).primeFactors.card + (c d).primeFactors.card := by
    rw [he d, Nat.primeFactors_mul (pow_ne_zero _ (hb d).ne') (pow_ne_zero _ (hc d).ne'),
      Nat.primeFactors_pow _ (by decide), Nat.primeFactors_pow _ (by decide)]
    exact Finset.card_union_le _ _
  have hpow : (3 : ℝ)^d.val.primeFactors.card ≤
      3^(b d).primeFactors.card * 3^(c d).primeFactors.card := by
    rw [← pow_add]
    exact pow_le_pow_right₀ (by norm_num) hf
  have hm : (d.val : ℝ)^(-(1 / 3) : ℝ) =
      (b d : ℝ)^(-(4 / 3) : ℝ) * (c d : ℝ)^(-(5 / 3) : ℝ) := by
    rw [he d, Nat.cast_mul, Nat.cast_pow, Nat.cast_pow, Real.mul_rpow (by positivity) (by positivity),
      ← Real.rpow_natCast_mul (by positivity), ← Real.rpow_natCast_mul (by positivity)]
    norm_num
  rw [hm]
  calc
    _ ≤ 3^(b d).primeFactors.card * 3^(c d).primeFactors.card *
        ((b d : ℝ)^(-(4 / 3) : ℝ) * (c d : ℝ)^(-(5 / 3) : ℝ)) :=
      mul_le_mul_of_nonneg_right hpow (by positivity)
    _ = _ := by dsimp [wt]; ring

end Erdos940CubicKernels



/- An eventual upper bound for a series of normalized representation counts. -/

namespace Erdos940DominatedUpper

open Filter
open scoped Topology

/-- Termwise eventual upper estimates can be summed under a common
summable upper bound. The excess over the termwise bound tends to zero. -/
theorem eventually_tsum_le {α ι : Type} {l : Filter α}
    (f : α → ι → ℝ) (bound limit : ι → ℝ)
    (hbound : Summable bound) (hlimit : Summable limit)
    (hlim_nonneg : ∀ i, 0 ≤ limit i)
    (hmajor : ∀ x i, 0 ≤ f x i ∧ f x i ≤ bound i)
    (hpoint : ∀ i ε, 0 < ε → ∀ᶠ x in l, f x i ≤ limit i + ε)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in l, (∑' i, f x i) ≤ (∑' i, limit i) + ε := by
  let E (x : α) (i : ι) := max (f x i - limit i) 0
  have hEn (x : α) (i : ι) : 0 ≤ E x i := le_max_right _ _
  have hEb (x : α) (i : ι) : E x i ≤ bound i := by
    apply max_le
    · linarith [(hmajor x i).2, hlim_nonneg i]
    · exact (hmajor x i).1.trans (hmajor x i).2
  have hEt (i : ι) : Tendsto (fun x => E x i) l (𝓝 0) := by
    refine tendsto_order.2 ⟨?_, ?_⟩
    · intro a ha
      exact Eventually.of_forall fun x => ha.trans_le (hEn x i)
    · intro a ha
      filter_upwards [hpoint i (a / 2) (by linarith)] with x hx
      apply max_lt
      · linarith
      · exact ha
  have hT : Tendsto (fun x => ∑' i, E x i) l (𝓝 0) := by
    simpa only [tsum_zero] using
      tendsto_tsum_of_dominated_convergence hbound hEt
        (Eventually.of_forall fun x i => by
          rw [Real.norm_eq_abs, abs_of_nonneg (hEn x i)]
          exact hEb x i)
  filter_upwards [hT.eventually (gt_mem_nhds hε)] with x hx
  have hS : Summable (E x) := hbound.of_nonneg_of_le (hEn x) (hEb x)
  have hf : Summable (f x) := hbound.of_nonneg_of_le (fun i => (hmajor x i).1)
    (fun i => (hmajor x i).2)
  have hle (i : ι) : f x i ≤ limit i + E x i := by
    have hh := le_max_left (f x i - limit i) 0
    change f x i - limit i ≤ E x i at hh
    linarith
  calc
    _ ≤ ∑' i, (limit i + E x i) := hf.tsum_le_tsum hle (hlimit.add hS)
    _ = (∑' i, limit i) + ∑' i, E x i := hlimit.tsum_add hS
    _ ≤ _ := add_le_add le_rfl hx.le

end Erdos940DominatedUpper



namespace Erdos940CubicCRT

open Filter
open scoped Topology

abbrev CubicKernel := {d : ℕ // Erdos940CubicKernels.IsKernel d}
abbrev KernelTriple := CubicKernel × CubicKernel × CubicKernel

private theorem summable_triple_product {g : CubicKernel → ℝ} (hg : Summable g) :
    Summable (fun d : KernelTriple => g d.1 * g d.2.1 * g d.2.2) := by
  have hpair : Summable (fun d : CubicKernel × CubicKernel => g d.1 * g d.2) :=
    summable_mul_of_summable_norm hg.norm hg.norm
  simpa only [mul_assoc] using summable_mul_of_summable_norm hg.norm hpair.norm

private noncomputable def tripleScale (d : KernelTriple) : ℝ :=
  scale d.1.val * scale d.2.1.val * scale d.2.2.val

private noncomputable def tripleBox (M u X : ℕ) (d : KernelTriple) : ℝ :=
  (boxCount M d.1.val d.2.1.val d.2.2.val u X : ℝ) / X

/-- The local congruence density multiplied by the product of the three coefficient scales. -/
noncomputable def tripleLocal (M u : ℕ) (d : KernelTriple) : ℝ :=
  (localCount M d.1.val d.2.1.val d.2.2.val u : ℝ) *
    (scale d.1.val / M) * (scale d.2.1.val / M) * (scale d.2.2.val / M)

private theorem tripleLocal_nonneg (M u : ℕ) (d : KernelTriple) :
    0 ≤ tripleLocal M u d := by
  unfold tripleLocal scale
  positivity

private theorem tripleLocal_le {M : ℕ} [NeZero M] (u : ℕ) (d : KernelTriple) :
    tripleLocal M u d ≤ tripleScale d := by
  have hM : (M : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne M)
  have hC : (localCount M d.1.val d.2.1.val d.2.2.val u : ℝ) ≤ (M : ℝ)^3 := by
    exact_mod_cast count_le_cube_modulus (M := M) d.1.val d.2.1.val d.2.2.val u
  unfold tripleLocal tripleScale
  calc
    _ ≤ (M : ℝ)^3 * (scale d.1.val / M) * (scale d.2.1.val / M) *
        (scale d.2.2.val / M) := by
      gcongr <;> unfold scale <;> positivity
    _ = _ := by field_simp [hM]

private theorem summable_scale : Summable (fun d : CubicKernel => scale d.val) := by
  apply Erdos940CubicKernels.summable_cubic_kernel_weight.of_nonneg_of_le
  · intro d
    unfold scale
    positivity
  · intro d
    change scale d.val ≤ (3 : ℝ)^d.val.primeFactors.card * scale d.val
    exact le_mul_of_one_le_left (by unfold scale; positivity)
      (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 3))

private theorem summable_triple_scale : Summable tripleScale :=
  summable_triple_product (g := fun d : CubicKernel => scale d.val) summable_scale

private theorem tripleBox_bound (M u X : ℕ) (d : KernelTriple) :
    0 ≤ tripleBox M u X d ∧ tripleBox M u X d ≤ 8 * tripleScale d := by
  constructor
  · unfold tripleBox
    positivity
  · simpa only [tripleBox, tripleScale, mul_assoc] using box_ratio_le_scale (M := M)
      (X := X) (u := u) d.1.property.1 d.2.1.property.1 d.2.2.property.1

private theorem summable_tripleBox (M u X : ℕ) : Summable (tripleBox M u X) :=
  (summable_triple_scale.mul_left 8).of_nonneg_of_le
    (fun d => (tripleBox_bound M u X d).1) (fun d => (tripleBox_bound M u X d).2)

/-- Pass the fixed-triple congruence estimates to all coefficient triples. -/
theorem eventual_weighted_box_sum {M : ℕ} [NeZero M] (u : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop, (∑' d, tripleBox M u X d) ≤ (∑' d, tripleLocal M u d) + ε := by
  have hL : Summable (tripleLocal M u) :=
    summable_triple_scale.of_nonneg_of_le (tripleLocal_nonneg M u) (tripleLocal_le u)
  apply Erdos940DominatedUpper.eventually_tsum_le (tripleBox M u)
    (fun d => 8 * tripleScale d) (tripleLocal M u) (summable_triple_scale.mul_left 8)
    hL (tripleLocal_nonneg M u) (tripleBox_bound M u) ?_ hε
  intro d δ hδ
  exact eventual_box_density_upper (M := M) (u := u)
    d.1.property.1 d.2.1.property.1 d.2.2.property.1 hδ

end Erdos940CubicCRT

namespace Erdos940CubicCRT

open Filter Finset

/-- Integers that are sums of exactly three positive cube-full numbers. -/
def ThreePositive : Set ℕ := {n | ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧
  (3 : ℕ).Full a ∧ (3 : ℕ).Full b ∧ (3 : ℕ).Full c ∧ n = a + b + c}

private def valueSet (M u X : ℕ) : Set ℕ :=
  {n | n ∈ ThreePositive ∧ n ≤ X ∧ (n : ZMod M) = u}

private theorem valueSet_finite (M u X : ℕ) : (valueSet M u X).Finite :=
  (Set.finite_Iic X).subset fun _ h => h.2.1

private abbrev KernelBox (M u X : ℕ) (d : KernelTriple) :=
  BoxSolutions M d.1.val d.2.1.val d.2.2.val u X

private def boxValue {M u X : ℕ} {d : KernelTriple} (v : KernelBox M u X d) : ℕ :=
  d.1.val * v.val.1^3 + d.2.1.val * v.val.2.1^3 + d.2.2.val * v.val.2.2^3

private theorem exists_box_of_value {M u X n : ℕ} (hn : n ∈ valueSet M u X) :
    ∃ (d : KernelTriple) (v : KernelBox M u X d), boxValue v = n := by
  rcases hn with ⟨⟨a, b, c, ha, hb, hc, hfa, hfb, hfc, he⟩, hX, hmod⟩
  obtain ⟨x, d, hx, hd, hd_eq⟩ :=
    Erdos940CubicKernels.exists_kernel_of_full ha hfa
  obtain ⟨y, e, hy, hd', he_eq⟩ :=
    Erdos940CubicKernels.exists_kernel_of_full hb hfb
  obtain ⟨z, f, hz, hd'', hf_eq⟩ :=
    Erdos940CubicKernels.exists_kernel_of_full hc hfc
  have hsum : d * x^3 + e * y^3 + f * z^3 = n := by
    rw [mul_comm d, mul_comm e, mul_comm f, ← hd_eq, ← he_eq, ← hf_eq, ← he]
  have hres : (d : ZMod M) * (x : ZMod M)^3 + (e : ZMod M) * (y : ZMod M)^3 +
      (f : ZMod M) * (z : ZMod M)^3 = u := by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow] using
      (congrArg (fun n : ℕ => (n : ZMod M)) hsum).trans hmod
  exact ⟨(⟨d, hd⟩, ⟨e, hd'⟩, ⟨f, hd''⟩),
    ⟨(x, y, z), hx, hy, hz, hsum.trans_le hX, hres⟩, hsum⟩

private theorem value_ratio_le_box_sum (M u X : ℕ) :
    ((valueSet M u X).ncard : ℝ) / X ≤ ∑' d, tripleBox M u X d := by
  classical
  let V := valueSet M u X
  let : Fintype V := (valueSet_finite M u X).fintype
  choose d v hval using fun n : V => exists_box_of_value n.property
  let S : Finset KernelTriple := Finset.univ.image d
  let F (p : S) := KernelBox M u X p.val
  have hfin (p : S) : Finite (F p) :=
    box_finite p.val.1.property.1 p.val.2.1.property.1 p.val.2.2.property.1
  let := hfin
  let input (n : V) : Sigma F :=
    ⟨⟨d n, mem_image.mpr ⟨n, mem_univ _, rfl⟩⟩, v n⟩
  let output (p : Sigma F) : ℕ := boxValue p.2
  have hinj : Function.Injective input := by
    intro x y h
    apply Subtype.ext
    exact (hval x).symm.trans ((congrArg output h).trans (hval y))
  have hcard := Nat.card_le_card_of_injective input hinj
  rw [Nat.card_sigma] at hcard
  have hNat : V.ncard ≤ ∑ p ∈ S, boxCount M p.1.val p.2.1.val p.2.2.val u X := by
    rw [Set.ncard_def]
    exact hcard.trans_eq (Finset.sum_attach S
      (fun p : KernelTriple => boxCount M p.1.val p.2.1.val p.2.2.val u X))
  calc
    _ ≤ (↑(∑ p ∈ S, boxCount M p.1.val p.2.1.val p.2.2.val u X) : ℝ) / X :=
      div_le_div_of_nonneg_right (by exact_mod_cast hNat) (by positivity)
    _ = ∑ p ∈ S, tripleBox M u X p := by
      rw [Nat.cast_sum, sum_div]
      rfl
    _ ≤ _ := (summable_tripleBox M u X).sum_le_tsum S fun p _ => (tripleBox_bound M u X p).1

/-- Upper bound on the proportion of integers up to a cutoff that are both
represented by three positive cube-full numbers and in the given residue class. -/
theorem eventual_cubic_value_density_upper {M : ℕ} [NeZero M] (u : ℕ) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop, ((valueSet M u X).ncard : ℝ) / X ≤
      (∑' d, tripleLocal M u d) + ε := by
  filter_upwards [eventual_weighted_box_sum (M := M) u hε] with X hX
  exact (value_ratio_le_box_sum M u X).trans hX

end Erdos940CubicCRT



namespace Erdos940CubicCRT

open Finset

/-- The local density used in the three-summand counting argument. -/
noncomputable def density (M a b c u : ℕ) : ℝ :=
  (localCount M a b c u : ℝ) / (M : ℝ)^2

theorem density_prod {ι : Type} (P : Finset ι) (m : ι → ℕ)
    (hm : ∀ i ∈ P, ∀ j ∈ P, i ≠ j → (m i).Coprime (m j)) (a b c u : ℕ) :
    density (∏ i ∈ P, m i) a b c u = ∏ i ∈ P, density (m i) a b c u := by
  unfold density
  rw [count_prod P m hm, Nat.cast_prod, Nat.cast_prod, Finset.prod_div_distrib]
  simp [Finset.prod_pow]

private lemma cubic_prime_size {p : ℕ} [Fact p.Prime] (hp : p % 3 = 1) : 4 ≤ p := by
  have hprime : p.Prime := Fact.out
  have h := hprime.two_le
  omega

private lemma cubic_prime_units {p : ℕ} [Fact p.Prime] (hp : p % 3 = 1) : 3 ∣ Nat.card (ZMod p)ˣ := by
  rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime Fact.out, Nat.dvd_iff_mod_eq_zero]
  have hprime : p.Prime := Fact.out
  have := hprime.two_le
  omega

private theorem eq_localCount {p : ℕ} [Fact p.Prime] (a b c u : ℕ) :
    localCount p a b c u =
      Erdos940CubicLocal.count (a : ZMod p) (b : ZMod p) (c : ZMod p) (u : ZMod p) :=
  rfl

/-- At a cubic splitting prime where the three coefficients are nonzero cubes,
a noncube target gives the saving 2/p in the local density. -/
theorem density_le_one_sub_two_div {p a b c u : ℕ} [Fact p.Prime] (hp : p % 3 = 1)
    (ha : ∃ a' : ZMod p, a' ≠ 0 ∧ a'^3 = (a : ZMod p))
    (hb : ∃ b' : ZMod p, b' ≠ 0 ∧ b'^3 = (b : ZMod p))
    (hc : ∃ c' : ZMod p, c' ≠ 0 ∧ c'^3 = (c : ZMod p))
    (hu : ¬ ∃ t : ZMod p, t^3 = (u : ZMod p)) :
    density p a b c u ≤ 1 - 2 / (p : ℝ) := by
  obtain ⟨a', hna, ha⟩ := ha
  obtain ⟨b', hnb, hb⟩ := hb
  obtain ⟨c', hnc, hc⟩ := hc
  have hsize : 4 ≤ Fintype.card (ZMod p) := by simpa only [ZMod.card] using cubic_prime_size hp
  have hh := Erdos940CubicLocal.three_cubes_noncube_saving hsize (cubic_prime_units hp)
    (ZMod.isPrimitive_stdAddChar p) hu
  rw [ZMod.card] at hh
  have hCount : localCount p a b c u ≤ p^2 - 2*p := by
    rw [eq_localCount, ← ha, ← hb, ← hc, Erdos940CubicLocal.count_cube_coefficients hna hnb hnc]
    exact hh
  have hP : 0 < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  have hsub : 2 * p ≤ p^2 := by have := cubic_prime_size hp; nlinarith
  have hcR : (localCount p a b c u : ℝ) ≤ (p : ℝ)^2 - 2*(p : ℝ) := by
    exact_mod_cast (Nat.cast_sub hsub (R := ℝ) ▸ (Nat.cast_le.mpr hCount))
  unfold density
  apply (div_le_iff₀ (by positivity : 0 < (p : ℝ)^2)).mpr
  calc
    _ ≤ (p : ℝ)^2 - 2 * p := hcR
    _ = (1 - 2 / (p : ℝ)) * (p : ℝ)^2 := by field_simp

/-- Uniform local upper bound, including vanishing coefficients. -/
theorem density_le_uniform {p a b c u : ℕ} [Fact p.Prime] (hp : p % 3 = 1)
    (hu : (u : ZMod p) ≠ 0) :
    density p a b c u ≤ (1 + 8 / (p : ℝ)) *
      3 ^ ((if (a : ZMod p) = 0 then 1 else 0) +
           (if (b : ZMod p) = 0 then 1 else 0) +
           (if (c : ZMod p) = 0 then 1 else 0) : ℕ) := by
  let k : ℕ := (if (a : ZMod p) = 0 then 1 else 0) +
    (if (b : ZMod p) = 0 then 1 else 0) + (if (c : ZMod p) = 0 then 1 else 0)
  have hP : 0 < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  change density p a b c u ≤ (1 + 8 / (p : ℝ)) * 3^k
  by_cases he : (a : ZMod p) ≠ 0 ∧ (b : ZMod p) ≠ 0 ∧ (c : ZMod p) ≠ 0
  · obtain ⟨ha, hb, hc⟩ := he
    have hsize : 4 ≤ Fintype.card (ZMod p) := by simpa only [ZMod.card] using cubic_prime_size hp
    have hh := Erdos940CubicLocal.weighted_error_bound hsize (cubic_prime_units hp)
      (ZMod.isPrimitive_stdAddChar p) ha hb hc hu
    rw [← eq_localCount, ZMod.card] at hh
    have hRe := (Complex.re_le_norm ((localCount p a b c u : ℂ) - (p : ℂ)^2)).trans hh
    have heRe : (((p : ℂ)^2).re) = (p : ℝ)^2 := by norm_cast
    simp only [Complex.sub_re, Complex.natCast_re, heRe] at hRe
    have hk : k = 0 := by simp [k, ha, hb, hc]
    rw [hk, pow_zero, mul_one]
    unfold density
    apply (div_le_iff₀ (by positivity : 0 < (p : ℝ)^2)).mpr
    calc
      _ ≤ (p : ℝ)^2 + 8 * p := by linarith
      _ = (1 + 8 / (p : ℝ)) * (p : ℝ)^2 := by field_simp
  · have hk : 1 ≤ k := by
      by_cases ha : (a : ZMod p) = 0
      · simp [k, ha]; omega
      by_cases hb : (b : ZMod p) = 0
      · simp [k, ha, hb]
      have hc : (c : ZMod p) = 0 := by by_contra hh; exact he ⟨ha, hb, hh⟩
      simp [k, ha, hb, hc]
    have hCount := Erdos940CubicLocal.count_le_three_times_card_sq
      (a : ZMod p) (b : ZMod p) (c : ZMod p) (u : ZMod p) hu
    rw [← eq_localCount, ZMod.card] at hCount
    have hD : density p a b c u ≤ 3 := by
      unfold density
      apply (div_le_iff₀ (by positivity : 0 < (p : ℝ)^2)).mpr
      exact_mod_cast hCount
    calc
      _ ≤ 3 := hD
      _ ≤ 3 ^ k := by
        simpa using (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) hk)
      _ ≤ (1 + 8 / (p : ℝ)) * 3 ^ k := by
        apply le_mul_of_one_le_left (by positivity)
        linarith [show 0 ≤ 8 / (p : ℝ) by positivity]

end Erdos940CubicCRT


/- Finite selection with a bounded reciprocal mass in the cubic density argument. -/

namespace Erdos940PrimeWindow

open Finset

/-- A divergent nonnegative series with terms at most one has a finite
partial sum in every interval [T,T+1] for T nonnegative. -/
theorem sum_window {ι : Type} (w : ι → ℝ) (h0 : ∀ i, 0 ≤ w i) (h1 : ∀ i, w i ≤ 1)
    (hns : ¬ Summable w) (T : ℝ) (hT : 0 ≤ T) :
    ∃ S : Finset ι, T ≤ ∑ i ∈ S, w i ∧ ∑ i ∈ S, w i ≤ T + 1 := by
  classical
  have hSome : ∃ n : ℕ, ∃ S : Finset ι, S.card = n ∧ T ≤ ∑ i ∈ S, w i := by
    by_contra! h
    apply hns
    exact summable_of_sum_le h0 (fun S => (h S.card S rfl).le)
  obtain ⟨S, hn, hlo⟩ := Nat.find_spec hSome
  refine ⟨S, hlo, ?_⟩
  by_cases hs : S = ∅
  · simp [hs]
    linarith
  · obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hs
    have hsmall : (∑ j ∈ S.erase i, w j) < T := by
      by_contra! hh
      have hmin := Nat.find_min' hSome ⟨S.erase i, rfl, hh⟩
      have hl := Finset.card_erase_lt_of_mem hi
      omega
    have he := Finset.sum_erase_add S w hi
    linarith [h1 i]

/-- Select the primes after fixing the allowed tail loss, using the reciprocal
sum as the simultaneous control on the saving and on the uniform error. -/
theorem prime_product_window (P : Set ℕ) (hp : ∀ p ∈ P, 2 ≤ p)
    (hns : ¬ Summable (fun p : P => (1 : ℝ) / p.val)) (T : ℝ) (hT : 0 ≤ T) :
    ∃ Q : Finset P,
      (∏ p ∈ Q, (1 - 2 / (p.val : ℝ))) ≤ Real.exp (-2 * T) ∧
      (∏ p ∈ Q, (1 + 8 / (p.val : ℝ))) ≤ Real.exp (8 * (T + 1)) := by
  have hpR (p : P) : (2 : ℝ) ≤ p.val := by exact_mod_cast hp p.val p.property
  have hpPos (p : P) : 0 < (p.val : ℝ) := by linarith [hpR p]
  obtain ⟨Q, hLow, hHigh⟩ := sum_window (fun p : P => (1 : ℝ) / p.val)
    (fun p => by positivity)
    (fun p => (div_le_one (hpPos p)).mpr (by linarith [hpR p])) hns T hT
  refine ⟨Q, ?_, ?_⟩
  · calc
      _ ≤ ∏ p ∈ Q, Real.exp (-2 / (p.val : ℝ)) := by
        apply Finset.prod_le_prod
        · intro p _
          apply sub_nonneg.mpr
          exact (div_le_one (hpPos p)).mpr (hpR p)
        · intro p _
          simpa [sub_eq_add_neg, neg_div, add_comm] using Real.add_one_le_exp (-2 / (p.val : ℝ))
      _ = Real.exp (-2 * ∑ p ∈ Q, (1 : ℝ) / p.val) := by
        rw [← Real.exp_sum, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro p _
        ring
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  · calc
      _ ≤ ∏ p ∈ Q, Real.exp (8 / (p.val : ℝ)) := by
        apply Finset.prod_le_prod
        · intro p _
          positivity
        · intro p _
          simpa only [add_comm] using Real.add_one_le_exp (8 / (p.val : ℝ))
      _ = Real.exp (8 * ∑ p ∈ Q, (1 : ℝ) / p.val) := by
        rw [← Real.exp_sum, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro p _
        ring
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

end Erdos940PrimeWindow



namespace Erdos940CubicCRT

open Finset Filter
open scoped Topology

private def IsNonzeroCube (p a : ℕ) : Prop :=
  ∃ t : ZMod p, t ≠ 0 ∧ t^3 = (a : ZMod p)

/-- Splitting conditions for the coefficients in a finite set of triples.
Away from finitely many ramified primes these are implied by complete
splitting in the compositum generated by their cube roots and a cube root of unity. -/
def SplittingPrimes (D : Finset KernelTriple) : Set ℕ :=
  {p | p.Prime ∧ p % 3 = 1 ∧ ∀ d ∈ D, IsNonzeroCube p d.1.val ∧
    IsNonzeroCube p d.2.1.val ∧ IsNonzeroCube p d.2.2.val}

private lemma exists_noncube_nat {p : ℕ} [Fact p.Prime] (hp : p % 3 = 1) :
    ∃ u : ℕ, ¬ ∃ t : ZMod p, t^3 = (u : ZMod p) := by
  obtain ⟨χ, hχ⟩ := Erdos940CubicLocal.exists_cubic_character (ZMod p) (cubic_prime_units hp)
  have hnon : ∃ z : ZMod p, ¬ ∃ t : ZMod p, t^3 = z := by
    by_contra! hall
    apply Erdos940CubicLocal.char_ne_one_of_order_three hχ
    apply MulChar.ext'
    intro z
    by_cases hz : z = 0
    · rw [hz, MulChar.map_zero, MulChar.map_zero]
    · rw [(Erdos940CubicLocal.char_eq_one_iff_cube hχ hz).mpr (hall z),
        MulChar.one_apply (isUnit_iff_ne_zero.mpr hz)]
  obtain ⟨z, hz⟩ := hnon
  exact ⟨z.val, by simpa only [ZMod.natCast_zmod_val]⟩

private theorem simultaneous_modEq {ι : Type} (Q : Finset ι) (m r : ι → ℕ)
    (hm : ∀ i ∈ Q, ∀ j ∈ Q, i ≠ j → (m i).Coprime (m j)) :
    ∃ u : ℕ, ∀ i ∈ Q, u ≡ r i [MOD m i] := by
  classical
  induction Q using Finset.induction_on with
  | empty => exact ⟨0, fun _ hi => (notMem_empty _ hi).elim⟩
  | insert i Q hi ih =>
    have hSub : ∀ j ∈ Q, ∀ k ∈ Q, j ≠ k → (m j).Coprime (m k) :=
      fun j hj k hk hne => hm j (mem_insert_of_mem hj) k (mem_insert_of_mem hk) hne
    obtain ⟨uQ, huQ⟩ := ih hSub
    have hcop : (m i).Coprime (∏ j ∈ Q, m j) :=
      Nat.Coprime.prod_right fun j hj => hm i (mem_insert_self _ _) j (mem_insert_of_mem hj)
        (fun h => hi (h ▸ hj))
    let U := Nat.chineseRemainder hcop (r i) uQ
    refine ⟨U.val, fun j hj => ?_⟩
    rcases mem_insert.mp hj with rfl | hj
    · exact U.property.1
    · exact (U.property.2.of_dvd (Finset.dvd_prod_of_mem m hj)).trans (huQ j hj)

private theorem splitting_pairwise_coprime {D : Finset KernelTriple} {p q : SplittingPrimes D}
    (h : p ≠ q) : p.val.Coprime q.val :=
  p.property.1.coprime_iff_not_dvd.mpr fun hd =>
    h (Subtype.ext ((Nat.prime_dvd_prime_iff_eq p.property.1 q.property.1).mp hd))

private theorem noncube_target_exists {D : Finset KernelTriple} (Q : Finset (SplittingPrimes D)) :
    ∃ u : ℕ, ∀ p ∈ Q, ¬ ∃ t : ZMod p.val, t^3 = (u : ZMod p.val) := by
  classical
  choose r hr using fun p : SplittingPrimes D => by
    let : Fact p.val.Prime := ⟨p.property.1⟩
    exact exists_noncube_nat p.property.2.1
  obtain ⟨u, hu⟩ := simultaneous_modEq Q Subtype.val r
    (fun _ _ _ _ h => splitting_pairwise_coprime h)
  refine ⟨u, fun p hp => ?_⟩
  have he : (u : ZMod p.val) = (r p : ZMod p.val) :=
    (ZMod.natCast_eq_natCast_iff u (r p) p.val).mpr (hu p hp)
  rw [he]
  exact hr p

private theorem sum_divisibility_le_primeFactors {D : Finset KernelTriple}
    (Q : Finset (SplittingPrimes D)) (a : ℕ) (ha : 0 < a) :
    (∑ p ∈ Q, if p.val ∣ a then 1 else 0) ≤ a.primeFactors.card := by
  rw [sum_ite, sum_const_zero, add_zero, sum_const, smul_eq_mul, mul_one]
  apply card_le_card_of_injOn Subtype.val ?_ (fun p _ q _ h => Subtype.ext h)
  intro p hp
  have hd := (mem_filter.mp hp).2
  exact Nat.mem_primeFactors.mpr ⟨p.property.1, hd, ha.ne'⟩

private noncomputable def weightedScale (d : CubicKernel) : ℝ :=
  (3 : ℝ)^d.val.primeFactors.card * scale d.val

private noncomputable def tripleWeight (d : KernelTriple) : ℝ :=
  weightedScale d.1 * weightedScale d.2.1 * weightedScale d.2.2

private theorem summable_tripleWeight : Summable tripleWeight :=
  summable_triple_product (g := weightedScale) Erdos940CubicKernels.summable_cubic_kernel_weight

private theorem tripleLocal_eq_density {M : ℕ} [NeZero M] (u : ℕ) (d : KernelTriple) :
    (M : ℝ) * tripleLocal M u d =
      density M d.1.val d.2.1.val d.2.2.val u * tripleScale d := by
  have hM : (M : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne M)
  unfold tripleLocal density tripleScale
  field_simp

private theorem split_density_le_saving {D : Finset KernelTriple}
    (Q : Finset (SplittingPrimes D)) {u : ℕ}
    (hu : ∀ p ∈ Q, ¬ ∃ t : ZMod p.val, t^3 = (u : ZMod p.val)) {d : KernelTriple}
    (hd : d ∈ D) :
    density (∏ p ∈ Q, p.val) d.1.val d.2.1.val d.2.2.val u ≤
      ∏ p ∈ Q, (1 - 2 / (p.val : ℝ)) := by
  rw [density_prod Q Subtype.val (fun _ _ _ _ h => splitting_pairwise_coprime h)]
  apply Finset.prod_le_prod
  · intro p _
    unfold density
    positivity
  · intro p hp
    let : Fact p.val.Prime := ⟨p.property.1⟩
    obtain ⟨ha, hb, hc⟩ := p.property.2.2 d hd
    exact density_le_one_sub_two_div p.property.2.1 ha hb hc (hu p hp)

private theorem split_density_le_uniform {D : Finset KernelTriple}
    (Q : Finset (SplittingPrimes D)) {u : ℕ}
    (hu : ∀ p ∈ Q, ¬ ∃ t : ZMod p.val, t^3 = (u : ZMod p.val))
    (d : KernelTriple) :
    density (∏ p ∈ Q, p.val) d.1.val d.2.1.val d.2.2.val u ≤
      (∏ p ∈ Q, (1 + 8 / (p.val : ℝ))) *
        (3 : ℝ)^(d.1.val.primeFactors.card + d.2.1.val.primeFactors.card + d.2.2.val.primeFactors.card) := by
  let e (a p : ℕ) : ℕ := if p ∣ a then 1 else 0
  let k (p : SplittingPrimes D) :=
    e d.1.val p.val + e d.2.1.val p.val + e d.2.2.val p.val
  have hk : (∑ p ∈ Q, k p) ≤ d.1.val.primeFactors.card + d.2.1.val.primeFactors.card +
      d.2.2.val.primeFactors.card := by
    simp only [k, sum_add_distrib]
    exact add_le_add (add_le_add (sum_divisibility_le_primeFactors Q _ d.1.property.1)
      (sum_divisibility_le_primeFactors Q _ d.2.1.property.1))
      (sum_divisibility_le_primeFactors Q _ d.2.2.property.1)
  rw [density_prod Q Subtype.val (fun _ _ _ _ h => splitting_pairwise_coprime h)]
  calc
    _ ≤ ∏ p ∈ Q, (1 + 8 / (p.val : ℝ)) * (3 : ℝ)^k p := by
      apply Finset.prod_le_prod
      · intro p _
        unfold density
        positivity
      · intro p hp
        let : Fact p.val.Prime := ⟨p.property.1⟩
        have hnu : (u : ZMod p.val) ≠ 0 := by
          intro hz
          exact hu p hp ⟨0, by simpa using hz.symm⟩
        simpa only [k, e, ZMod.natCast_eq_zero_iff] using
          density_le_uniform (a := d.1.val) (b := d.2.1.val) (c := d.2.2.val) p.property.2.1 hnu
    _ = (∏ p ∈ Q, (1 + 8 / (p.val : ℝ))) * (3 : ℝ)^(∑ p ∈ Q, k p) := by
      rw [prod_mul_distrib, prod_pow_eq_pow_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hk)
      (prod_nonneg fun _ _ => by positivity)

end Erdos940CubicCRT

namespace Erdos940CubicCRT

open Finset Filter
open scoped Topology

private theorem tripleScale_nonneg (d : KernelTriple) : 0 ≤ tripleScale d := by
  unfold tripleScale scale
  positivity

private theorem tripleWeight_nonneg (d : KernelTriple) : 0 ≤ tripleWeight d := by
  unfold tripleWeight weightedScale scale
  positivity

private theorem exists_small_tail {δ : ℝ} (hδ : 0 < δ) :
    ∃ D : Finset KernelTriple, (∑' d : {d // d ∉ D}, tripleWeight d.val) < δ := by
  let W := ∑' d, tripleWeight d
  have hW : Tendsto (fun D : Finset KernelTriple => ∑ d ∈ D, tripleWeight d) atTop (𝓝 W) :=
    summable_tripleWeight.hasSum
  obtain ⟨D, hD⟩ := (hW.eventually (lt_mem_nhds (show W - δ < W by linarith))).exists
  have hsum := summable_tripleWeight.sum_add_tsum_subtype_compl D
  change (∑ d ∈ D, tripleWeight d) + (∑' d : {d // d ∉ D}, tripleWeight d.val) = W at hsum
  exact ⟨D, by linarith⟩

private theorem exists_large_exponential_saving (W : ℝ) :
    ∃ T : ℝ, 0 ≤ T ∧ Real.exp (-2 * T) * W ≤ 1 / 8 := by
  have hf : Tendsto (fun T : ℝ => Real.exp (-2 * T) * W) atTop (𝓝 0) := by
    have hneg : Tendsto (fun T : ℝ => -2 * T) atTop atBot :=
      (tendsto_const_mul_atBot_of_neg (by norm_num : (-2 : ℝ) < 0)).mpr tendsto_id
    simpa only [zero_mul, Function.comp_apply] using (Real.tendsto_exp_atBot.comp hneg).mul_const W
  obtain ⟨T, hT, hS⟩ :=
    ((eventually_ge_atTop (0 : ℝ)).and (hf.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 8)))).exists
  exact ⟨T, hT, hS.le⟩

/-- Separate the finite core from the weighted tail and use the same modulus for both. -/
theorem exists_small_total_local_density
    (hsplit : ∀ D : Finset KernelTriple,
      ¬ Summable (fun p : SplittingPrimes D => (1 : ℝ) / p.val)) :
    ∃ M u : ℕ, 0 < M ∧ (M : ℝ) * (∑' d, tripleLocal M u d) ≤ 1 / 4 := by
  classical
  let W := ∑' d, tripleScale d
  obtain ⟨T, hT, hS⟩ := exists_large_exponential_saving W
  let B := Real.exp (8 * (T + 1))
  have hB : 0 < B := Real.exp_pos _
  obtain ⟨D, hD⟩ := exists_small_tail (δ := 1 / (8 * B)) (by positivity)
  obtain ⟨Q, hQsmall, hQlarge⟩ := Erdos940PrimeWindow.prime_product_window
    (SplittingPrimes D) (fun p hp => hp.1.two_le) (hsplit D) T hT
  obtain ⟨u, hu⟩ := noncube_target_exists Q
  let M := ∏ p ∈ Q, p.val
  have hM : 0 < M := Finset.prod_pos fun p _ => p.property.1.pos
  let : NeZero M := ⟨hM.ne'⟩
  have hL : Summable (tripleLocal M u) :=
    summable_triple_scale.of_nonneg_of_le (tripleLocal_nonneg M u) (tripleLocal_le u)
  let F (d : KernelTriple) := (M : ℝ) * tripleLocal M u d
  have hF : Summable F := hL.mul_left _
  have hCore (d : KernelTriple) (hd : d ∈ D) : F d ≤ Real.exp (-2 * T) * tripleScale d := by
    dsimp [F]
    rw [tripleLocal_eq_density]
    exact mul_le_mul_of_nonneg_right ((split_density_le_saving Q hu hd).trans hQsmall) (tripleScale_nonneg d)
  have hTail (d : KernelTriple) : F d ≤ B * tripleWeight d := by
    dsimp [F]
    rw [tripleLocal_eq_density]
    have hp := split_density_le_uniform Q hu d
    have hs := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hQlarge
      (show 0 ≤ (3 : ℝ)^(d.1.val.primeFactors.card + d.2.1.val.primeFactors.card +
        d.2.2.val.primeFactors.card) by positivity)) (tripleScale_nonneg d)
    calc
      _ ≤ _ := (mul_le_mul_of_nonneg_right hp (tripleScale_nonneg d)).trans hs
      _ = _ := by unfold tripleWeight weightedScale tripleScale B; rw [pow_add, pow_add]; ring
  have hCoreSum : (∑ d ∈ D, F d) ≤ 1 / 8 := by
    calc
      _ ≤ ∑ d ∈ D, Real.exp (-2 * T) * tripleScale d := Finset.sum_le_sum hCore
      _ ≤ Real.exp (-2 * T) * W := by
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (summable_triple_scale.sum_le_tsum D
          (fun d _ => tripleScale_nonneg d)) (Real.exp_pos _).le
      _ ≤ _ := hS
  have hTailSum : (∑' d : {d // d ∉ D}, F d.val) ≤ 1 / 8 := by
    calc
      _ ≤ ∑' d : {d // d ∉ D}, B * tripleWeight d.val :=
        (hF.subtype _).tsum_le_tsum (fun d => hTail d.val) ((summable_tripleWeight.mul_left B).subtype _)
      _ = B * (∑' d : {d // d ∉ D}, tripleWeight d.val) := tsum_mul_left
      _ ≤ B * (1 / (8 * B)) := mul_le_mul_of_nonneg_left hD.le hB.le
      _ = _ := by field_simp
  refine ⟨M, u, hM, ?_⟩
  rw [← tsum_mul_left, ← hF.sum_add_tsum_subtype_compl D]
  linarith

end Erdos940CubicCRT

namespace Erdos940CubicCRT

open Filter Finset
open scoped Topology

private def progression (M u X : ℕ) : Set ℕ := {n | n < X ∧ (n : ZMod M) = u}

private theorem progression_card_lower {M : ℕ} [NeZero M] (u X : ℕ) :
    X / M ≤ (progression M u X).ncard := by
  have hfin : (progression M u X).Finite := (Set.finite_Iio X).subset fun _ h => h.1
  let := hfin.to_subtype
  let v := (u : ZMod M).val
  have hv : v < M := ZMod.val_lt _
  let f (k : Fin (X / M)) : progression M u X :=
    ⟨v + M * k.val, by
      constructor
      · calc
          _ < M + M * k.val := Nat.add_lt_add_right hv _
          _ = M * (k.val + 1) := by ring
          _ ≤ M * (X / M) := Nat.mul_le_mul_left M k.isLt
          _ ≤ X := by simpa only [Nat.mul_comm] using Nat.div_mul_le_self X M
      · simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, add_zero]
        exact ZMod.natCast_zmod_val _⟩
  have hf : Function.Injective f := by
    intro a b h
    have he : v + M * a.val = v + M * b.val := congrArg Subtype.val h
    exact Fin.ext (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (NeZero.ne M))
      (Nat.add_left_cancel he))
  simpa only [Nat.card_fin, Nat.card_coe_set_eq] using Nat.card_le_card_of_injective f hf

private theorem progression_density_lower {M u X : ℕ} [NeZero M] (hX : 2 * M ≤ X) :
    1 / (2 * (M : ℝ)) ≤ ((progression M u X).ncard : ℝ) / X := by
  have hM : 0 < (M : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
  have hXR : 2 * (M : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hXpos : 0 < (X : ℝ) := by linarith
  have hrem : ((X % M : ℕ) : ℝ) < (M : ℝ) := by exact_mod_cast Nat.mod_lt X (Nat.pos_of_ne_zero (NeZero.ne M))
  have hdiv : (M : ℝ) * ((X / M : ℕ) : ℝ) + ((X % M : ℕ) : ℝ) = X := by
    exact_mod_cast Nat.div_add_mod X M
  have hCount : ((X / M : ℕ) : ℝ) ≤ (progression M u X).ncard := by
    exact_mod_cast progression_card_lower (M := M) u X
  apply (le_div_iff₀ hXpos).mpr
  have h : (X : ℝ) ≤ (2 * (M : ℝ)) * (progression M u X).ncard := by
    nlinarith [mul_le_mul_of_nonneg_left hCount hM.le]
  rw [div_mul_eq_mul_div, one_mul]
  exact (div_le_iff₀ (by positivity : 0 < 2 * (M : ℝ))).mpr
    (by simpa only [mul_comm] using h)

private theorem progression_partition_bound (M u X : ℕ) :
    (progression M u X).ncard ≤ (valueSet M u X).ncard + (ThreePositiveᶜ ∩ Set.Iio X).ncard := by
  have hsub : progression M u X ⊆ valueSet M u X ∪ (ThreePositiveᶜ ∩ Set.Iio X) := by
    intro n hn
    by_cases h : n ∈ ThreePositive
    · exact Or.inl ⟨h, hn.1.le, hn.2⟩
    · exact Or.inr ⟨h, hn.1⟩
  exact (Set.ncard_le_ncard hsub ((valueSet_finite M u X).union
    ((Set.finite_Iio X).inter_of_right _))).trans (Set.ncard_union_le _ _)

private lemma partial_density_nat_univ (S : Set ℕ) (X : ℕ) :
    S.partialDensity Set.univ X = ((S ∩ Set.Iio X).ncard : ℝ) / X := by
  simp [Set.partialDensity]

/-- Conditional form of the positive lower density theorem for the complement
of the sums of three positive cube-full numbers. The remaining input is the
divergence of the prime reciprocal sum for each finite splitting problem. -/
theorem positive_lower_density_of_splitting_primes
    (hsplit : ∀ D : Finset KernelTriple,
      ¬ Summable (fun p : SplittingPrimes D => (1 : ℝ) / p.val)) :
    0 < ThreePositiveᶜ.lowerDensity Set.univ := by
  obtain ⟨M, u, hM, hMW⟩ := exists_small_total_local_density hsplit
  let : NeZero M := ⟨hM.ne'⟩
  have hMR : 0 < (M : ℝ) := by exact_mod_cast hM
  have hW : (∑' d, tripleLocal M u d) ≤ 1 / (4 * (M : ℝ)) := by
    apply (le_div_iff₀ (by positivity : 0 < 4 * (M : ℝ))).mpr
    nlinarith
  have hEvent := eventual_cubic_value_density_upper (M := M) u
    (ε := 1 / (8 * (M : ℝ))) (by positivity)
  have hFinal : ∀ᶠ X : ℕ in atTop, 1 / (8 * (M : ℝ)) ≤
      ThreePositiveᶜ.partialDensity Set.univ X := by
    filter_upwards [hEvent, eventually_ge_atTop (2 * M)] with X hXV hX
    have hA := progression_density_lower (M := M) (u := u) hX
    have hCX : ((progression M u X).ncard : ℝ) / X ≤
        ((valueSet M u X).ncard : ℝ) / X +
          ((ThreePositiveᶜ ∩ Set.Iio X).ncard : ℝ) / X := by
      rw [← add_div]
      exact div_le_div_of_nonneg_right (by exact_mod_cast progression_partition_bound M u X)
        (by positivity)
    rw [partial_density_nat_univ]
    have he : 1 / (2 * (M : ℝ)) = 1 / (4 * (M : ℝ)) + 2 * (1 / (8 * (M : ℝ))) := by ring
    linarith
  have hb : IsCoboundedUnder (fun x y : ℝ => x ≥ y) atTop
      (fun X : ℕ => ThreePositiveᶜ.partialDensity Set.univ X) :=
    (isBoundedUnder_of_eventually_le (Eventually.of_forall fun X =>
      Set.partialDensity_le_one _ _ X)).isCoboundedUnder_ge
  exact (by positivity : 0 < 1 / (8 * (M : ℝ))).trans_le (le_liminf_of_le hb hFinal)

end Erdos940CubicCRT



namespace Erdos940PrimeIdeals

open Filter Finset Ideal NumberField UniqueFactorizationMonoid
open scoped NumberField nonZeroDivisors Topology

variable (K : Type) [Field K] [NumberField K]

private abbrev NonzeroIdeal := (Ideal (𝓞 K))⁰
private abbrev NonzeroPrimeIdeal := {P : Ideal (𝓞 K) // Prime P}

private theorem not_summable_ideal_reciprocals :
    ¬ Summable (fun I : NonzeroIdeal K => (1 : ℝ) / absNorm (I : Ideal (𝓞 K))) := by
  classical
  intro hs
  let w (I : NonzeroIdeal K) := (1 : ℝ) / absNorm (I : Ideal (𝓞 K))
  let f (X : ℕ) (I : NonzeroIdeal K) : ℝ :=
    if absNorm (I : Ideal (𝓞 K)) ≤ X then 1 / (X : ℝ) else 0
  have hmajor (X : ℕ) (I : NonzeroIdeal K) : 0 ≤ f X I ∧ f X I ≤ w I := by
    constructor
    · unfold f; split_ifs <;> positivity
    · unfold f w
      split_ifs with h
      · exact one_div_le_one_div_of_le (by
          exact_mod_cast absNorm_pos_of_nonZeroDivisors I) (by exact_mod_cast h)
      · positivity
  have hOne : Tendsto (fun X : ℕ => (1 : ℝ) / X) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat 1
  have hPoint (I : NonzeroIdeal K) (ε : ℝ) (hε : 0 < ε) :
      ∀ᶠ X : ℕ in atTop, f X I ≤ (0 : ℝ) + ε := by
    filter_upwards [hOne.eventually (gt_mem_nhds hε)] with X hX
    simp only [f, zero_add]
    split_ifs
    · exact hX.le
    · exact hε.le
  let C := NumberField.dedekindZeta_residue K
  have hC : 0 < C := NumberField.dedekindZeta_residue_pos K
  have hSmall : ∀ᶠ X : ℕ in atTop, (∑' I, f X I) ≤ C / 4 := by
    simpa only [tsum_zero, zero_add] using Erdos940DominatedUpper.eventually_tsum_le
      f w (fun _ => 0) hs summable_zero (fun _ => le_rfl) hmajor hPoint (ε := C / 4) (by positivity)
  have hsum (X : ℕ) :
      (∑' I, f X I) =
        (Nat.card {I : NonzeroIdeal K // absNorm (I : Ideal (𝓞 K)) ≤ X} : ℝ) / X := by
    let U : Set (NonzeroIdeal K) := {I | absNorm (I : Ideal (𝓞 K)) ≤ X}
    have hU : U.Finite := Ideal.finite_setOfPred_absNorm_le₀ X
    let S := hU.toFinset
    have hzero (I : NonzeroIdeal K) (hI : I ∉ S) : f X I = 0 := by
      have hn : ¬ absNorm (I : Ideal (𝓞 K)) ≤ X := by
        simpa only [S, U, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using hI
      simp [f, hn]
    rw [tsum_eq_sum hzero]
    have hconst (I : NonzeroIdeal K) (hI : I ∈ S) : f X I = 1 / (X : ℝ) := by
      have hn : absNorm (I : Ideal (𝓞 K)) ≤ X := by
        simpa only [S, U, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using hI
      simp [f, hn]
    rw [Finset.sum_congr rfl hconst, sum_const, nsmul_eq_mul, mul_one_div,
      ← Set.ncard_eq_toFinset_card U hU]
    rfl
  have hAsym : Tendsto (fun X : ℕ => (∑' I, f X I)) atTop (𝓝 C) := by
    have h := (Ideal.tendsto_norm_le_div_atTop₀ K).comp tendsto_natCast_atTop_atTop
    have he (X : ℕ) : {I : NonzeroIdeal K // (absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ (X : ℝ)} =
        {I : NonzeroIdeal K // absNorm (I : Ideal (𝓞 K)) ≤ X} := by
      congr 1
      funext I
      exact propext Nat.cast_le
    change Tendsto (fun X : ℕ =>
      (Nat.card {I : NonzeroIdeal K // (absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ (X : ℝ)} : ℝ) /
        (X : ℝ)) atTop (𝓝 C) at h
    simpa only [he, ← hsum] using h
  obtain ⟨X, hXlow, hXhi⟩ :=
    ((hAsym.eventually (lt_mem_nhds (show C / 2 < C by linarith))).and hSmall).exists
  linarith

private theorem prime_norm_ge_two (P : NonzeroPrimeIdeal K) : 2 ≤ absNorm P.val := by
  have hz : absNorm P.val ≠ 0 := by
    exact absNorm_eq_zero_iff.not.mpr P.property.ne_zero
  have ho : absNorm P.val ≠ 1 := by
    exact absNorm_eq_one_iff.not.mpr
      ((Ideal.prime_iff_isPrime P.property.ne_zero).mp P.property).ne_top
  omega

private theorem summable_prime_powers
    (hP : Summable (fun P : NonzeroPrimeIdeal K => (1 : ℝ) / absNorm P.val)) :
    Summable (fun p : NonzeroPrimeIdeal K × ℕ => ((1 : ℝ) / absNorm p.1.val) ^ (p.2 + 1)) := by
  let r (P : NonzeroPrimeIdeal K) := (1 : ℝ) / absNorm P.val
  have hr₀ (P : NonzeroPrimeIdeal K) : 0 ≤ r P := by unfold r; positivity
  have hr₁ (P : NonzeroPrimeIdeal K) : r P ≤ 1 / 2 := by
    unfold r
    exact one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast prime_norm_ge_two K P)
  refine (summable_prod_of_nonneg (fun _ => by positivity)).mpr ⟨?_, ?_⟩
  · intro P
    simp only [← show r P = (1 : ℝ) / absNorm P.val from rfl, pow_succ']
    exact (summable_geometric_of_lt_one (hr₀ P) (by linarith [hr₁ P])).mul_left (r P)
  · apply (hP.mul_left 2).of_nonneg_of_le (fun _ => tsum_nonneg fun _ => by positivity)
    intro P
    change (∑' n : ℕ, r P ^ (n + 1)) ≤ 2 * r P
    rw [show (fun n : ℕ => r P ^ (n + 1)) = (fun n : ℕ => r P * r P ^ n) by
      funext n; rw [pow_succ'], tsum_mul_left,
      tsum_geometric_of_lt_one (hr₀ P) (by linarith [hr₁ P])]
    rw [← div_eq_mul_inv]
    apply (div_le_iff₀ (by linarith [hr₁ P] : 0 < 1 - r P)).mpr
    nlinarith [mul_nonneg (hr₀ P) (show 0 ≤ 1 - 2 * r P by linarith [hr₁ P])]

private noncomputable def primePowerCode (I : NonzeroIdeal K) : Finset (NonzeroPrimeIdeal K × ℕ) := by
  classical
  let m := normalizedFactors I.val
  exact m.toFinset.attach.image fun p =>
    (⟨p.val, prime_of_normalized_factor p.val (Multiset.mem_toFinset.mp p.property)⟩,
      m.count p.val - 1)

private theorem code_product {I : NonzeroIdeal K} :
    (∏ p ∈ primePowerCode K I, p.1.val ^ (p.2 + 1)) = I.val := by
  classical
  let m := normalizedFactors I.val
  unfold primePowerCode
  rw [Finset.prod_image]
  · have hTerm (p : m.toFinset) : (p.val : Ideal (𝓞 K)) ^ (m.count p.val - 1 + 1) =
        p.val ^ m.count p.val := by
      rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Multiset.count_ne_zero.mpr
        (Multiset.mem_toFinset.mp p.property)))]
    rw [Finset.prod_congr rfl (fun p _ => hTerm p)]
    calc
      _ = ∏ p ∈ m.toFinset, p ^ m.count p := Finset.prod_attach m.toFinset (fun p => p ^ m.count p)
      _ = m.prod := (Finset.prod_multiset_count m).symm
      _ = I.val := Ideal.prod_normalizedFactors_eq_self (by simpa only [ne_eq, Submodule.zero_eq_bot] using
        (mem_nonZeroDivisors_iff_ne_zero.mp I.property))
  · intro p _ q _ he
    exact Subtype.ext (congrArg (fun r : NonzeroPrimeIdeal K × ℕ => r.1.val) he)

private theorem primePowerCode_injective : Function.Injective (primePowerCode K) := by
  intro I J h
  apply Subtype.ext
  rw [← code_product K (I := I), ← code_product K (I := J), h]

/-- Prime ideals of a number field have a divergent sum of reciprocal absolute norms. -/
theorem not_summable_prime_ideal_reciprocals :
    ¬ Summable (fun P : NonzeroPrimeIdeal K => (1 : ℝ) / absNorm P.val) := by
  intro h
  let w (p : NonzeroPrimeIdeal K × ℕ) := ((1 : ℝ) / absNorm p.1.val) ^ (p.2 + 1)
  have hw : Summable w := summable_prime_powers K h
  have hFin := summable_finsetProd_of_summable_nonneg (f := w) (fun p => by unfold w; positivity) hw
  have hCode := hFin.comp_injective (primePowerCode_injective K)
  apply not_summable_ideal_reciprocals K
  refine hCode.congr fun I => ?_
  change (∏ p ∈ primePowerCode K I, w p) = 1 / (absNorm I.val : ℝ)
  rw [← code_product K (I := I), map_prod, Nat.cast_prod, one_div, ← Finset.prod_inv_distrib]
  apply Finset.prod_congr rfl
  intro p _
  simp only [w, map_pow, Nat.cast_pow, one_div, inv_pow]

end Erdos940PrimeIdeals


namespace Erdos940PrimeIdeals

open Finset Ideal NumberField
open scoped NumberField

variable (K : Type) [Field K] [NumberField K]

private noncomputable def basePrime (P : NonzeroPrimeIdeal K) : ℕ :=
  absNorm (P.val.under ℤ)

private lemma prime_basePrime (P : NonzeroPrimeIdeal K) : (basePrime K P).Prime := by
  let : NeZero P.val := ⟨P.property.ne_zero⟩
  let : P.val.IsPrime := (Ideal.prime_iff_isPrime P.property.ne_zero).mp P.property
  exact Nat.absNorm_under_prime P.val

private lemma isPrime_ideal (P : NonzeroPrimeIdeal K) : P.val.IsPrime :=
  (Ideal.prime_iff_isPrime P.property.ne_zero).mp P.property

private lemma basePrime_pow_eq_norm (P : NonzeroPrimeIdeal K) :
    (basePrime K P)^P.val.inertiaDeg ℤ = absNorm P.val := by
  let : P.val.IsPrime := isPrime_ideal K P
  let : P.val.LiesOver (P.val.under ℤ) := (Ideal.liesOver_iff _ _).mpr rfl
  exact Ideal.absNorm_pow_inertiaDeg _ _

private lemma basePrime_sq_le_of_ne (P : NonzeroPrimeIdeal K)
    (h : absNorm P.val ≠ basePrime K P) : (basePrime K P)^2 ≤ absNorm P.val := by
  have hn (e : ℕ) (he : P.val.inertiaDeg ℤ = e) :
      (basePrime K P)^e = absNorm P.val := by simpa only [he] using basePrime_pow_eq_norm K P
  have h2 : 2 ≤ P.val.inertiaDeg ℤ := by
    by_contra! hh
    interval_cases P.val.inertiaDeg ℤ
    · have hh' := hn 0 rfl
      have hlo := prime_norm_ge_two K P
      simp only [pow_zero] at hh'
      omega
    · exact h (by simpa only [pow_one] using (hn 1 rfl).symm)
  rw [← basePrime_pow_eq_norm K P]
  exact pow_le_pow_right₀ (prime_basePrime K P).one_lt.le h2

private theorem base_fiber_finite_and_card_le (p : ℕ) :
    Finite {P : NonzeroPrimeIdeal K // basePrime K P = p} ∧
    Nat.card {P : NonzeroPrimeIdeal K // basePrime K P = p} ≤ Module.finrank ℚ K := by
  classical
  by_cases hp : p.Prime
  · let I : Ideal ℤ := Ideal.span {(p : ℤ)}
    have hI : I ≠ ⊥ := Ideal.span_singleton_eq_bot.not.mpr (by exact_mod_cast hp.ne_zero)
    let : I.IsMaximal :=
      ((Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr
        (Nat.prime_iff_prime_int.mp hp)).isMaximal hI
    let : I.IsPrime := (inferInstance : I.IsMaximal).isPrime
    let S := I.primesOver (𝓞 K)
    let : Finite S := (IsDedekindDomain.primesOver_finite I (𝓞 K)).to_subtype
    let : Fintype S := Fintype.ofFinite _
    let f (P : {P : NonzeroPrimeIdeal K // basePrime K P = p}) : S :=
      ⟨P.val.val, isPrime_ideal K P.val, (Ideal.liesOver_iff _ _).mpr (by
        rw [← Int.ideal_span_absNorm_eq_self (P.val.val.under ℤ)]
        exact congrArg (fun n : ℕ => Ideal.span ({(n : ℤ)} : Set ℤ)) P.property.symm)⟩
    have hInj : Function.Injective f := fun _ _ h =>
      Subtype.ext (Subtype.ext (congrArg (fun P : S => P.val) h))
    have hcard : Nat.card S ≤ Module.finrank ℚ K := by
      rw [Nat.card_eq_fintype_card, ← RingOfIntegers.rank, ← Ideal.sum_ramification_inertia_eq_finrank I (𝓞 K)]
      rw [← Finset.card_univ, Finset.card_eq_sum_ones]
      apply Finset.sum_le_sum
      intro P _
      let : P.val.IsPrime := P.property.1
      exact Nat.one_le_iff_ne_zero.mpr
        (Nat.mul_pos (Ideal.ramificationIdx_pos P.val ℤ) (Ideal.inertiaDeg_pos P.val ℤ)).ne'
    exact ⟨Finite.of_injective f hInj, (Nat.card_le_card_of_injective f hInj).trans hcard⟩
  · have : IsEmpty {P : NonzeroPrimeIdeal K // basePrime K P = p} :=
      ⟨fun P => hp (P.property ▸ prime_basePrime K P.val)⟩
    exact ⟨inferInstance, by simp⟩

private lemma summable_nat_inv_sq : Summable (fun p : ℕ => (1 : ℝ) / (p : ℝ)^2) := by
  exact Real.summable_one_div_nat_pow.mpr (by decide : 1 < (2 : ℕ))

/-- A set of rational primes containing all degree-one prime ideal norms
outside finitely many exceptions has divergent reciprocal sum. -/
theorem not_summable_of_prime_norms_cover (S : Set ℕ) (B : ℕ) (hB : 0 < B)
    (hcover : ∀ P : NonzeroPrimeIdeal K, absNorm P.val = basePrime K P →
      ¬ basePrime K P ∣ B → basePrime K P ∈ S) :
    ¬ Summable (fun p : S => (1 : ℝ) / p.val) := by
  classical
  intro hs
  let w (p : ℕ) := (1 : ℝ) / p
  let bad : Set ℕ := (B.primeFactors : Set ℕ)
  have hgood : Summable (S.indicator w) := summable_subtype_iff_indicator.mp hs
  have hbad : Summable (bad.indicator w) :=
    summable_of_ne_finset_zero (s := B.primeFactors) (fun p hp => Set.indicator_of_notMem hp _)
  let G (p : ℕ) := S.indicator w p + bad.indicator w p + 1 / (p : ℝ)^2
  have hG : Summable G := (hgood.add hbad).add summable_nat_inv_sq
  have hInd (A : Set ℕ) (p : ℕ) : 0 ≤ A.indicator w p :=
    Set.indicator_nonneg (s := A) (f := w) (fun n _ => by unfold w; positivity) p
  have hGn (p : ℕ) : 0 ≤ G p := by
    exact add_nonneg (add_nonneg (hInd S p) (hInd bad p)) (show 0 ≤ 1 / (p : ℝ)^2 by positivity)
  let F := fun p : ℕ => {P : NonzeroPrimeIdeal K // basePrime K P = p}
  let f (P : Σ p, F p) := (1 : ℝ) / absNorm P.2.val.val
  have hbound (p : ℕ) (P : F p) : f ⟨p, P⟩ ≤ G p := by
    have hp : p.Prime := P.property ▸ prime_basePrime K P.val
    have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
    by_cases hr : absNorm P.val.val = basePrime K P.val
    · have he : absNorm P.val.val = p := hr.trans P.property
      by_cases hb : p ∣ B
      · have hb' : p ∈ bad := Nat.mem_primeFactors.mpr ⟨hp, hb, hB.ne'⟩
        have hng : 0 ≤ S.indicator w p := hInd S p
        unfold G f
        dsimp only
        rw [he, Set.indicator_of_mem hb']
        dsimp [w]
        linarith [show 0 ≤ 1 / (p : ℝ)^2 by positivity]
      · have hpS : p ∈ S := P.property ▸ hcover P.val hr (by rwa [P.property])
        have hnb : 0 ≤ bad.indicator w p := hInd bad p
        unfold G f
        dsimp only
        rw [he, Set.indicator_of_mem hpS]
        dsimp [w]
        linarith [show 0 ≤ 1 / (p : ℝ)^2 by positivity]
    · have hn := basePrime_sq_le_of_ne K P.val hr
      rw [P.property] at hn
      have hRec : f ⟨p, P⟩ ≤ 1 / (p : ℝ)^2 := by
        unfold f
        exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast hn)
      have hBoth : 0 ≤ S.indicator w p + bad.indicator w p :=
        add_nonneg (hInd S p) (hInd bad p)
      exact hRec.trans (by unfold G; linarith)
  have hFinite (p : ℕ) : Finite (F p) := (base_fiber_finite_and_card_le K p).1
  have hbyFiber : Summable f := by
    apply (summable_sigma_of_nonneg (fun _ => by unfold f; positivity)).mpr
    refine ⟨fun p => ?_, ?_⟩
    · let : Finite (F p) := hFinite p
      exact Summable.of_finite
    · apply (hG.mul_left (Module.finrank ℚ K : ℝ)).of_nonneg_of_le
        (fun p => tsum_nonneg fun _ => by unfold f; positivity)
      intro p
      let : Finite (F p) := hFinite p
      let : Fintype (F p) := Fintype.ofFinite _
      calc
        _ ≤ ∑' (_ : F p), G p := by
          simp only [tsum_fintype]
          exact Finset.sum_le_sum fun P _ => hbound p P
        _ = (Nat.card (F p) : ℝ) * G p := by rw [tsum_const, nsmul_eq_mul]
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (by exact_mod_cast (base_fiber_finite_and_card_le K p).2) (hGn p)
  exact not_summable_prime_ideal_reciprocals K ((Equiv.sigmaFiberEquiv (basePrime K)).summable_iff.mp hbyFiber)

end Erdos940PrimeIdeals


namespace Erdos940PrimeIdeals

open Finset Ideal NumberField Polynomial
open scoped NumberField Polynomial

variable (K : Type) [Field K] [NumberField K]

omit [NumberField K] in
private theorem charP_quotient_base (P : NonzeroPrimeIdeal K) :
    CharP (𝓞 K ⧸ P.val) (basePrime K P) := by
  rw [show basePrime K P = ringChar (𝓞 K ⧸ P.val) from (Ideal.ringChar_quot P.val).symm]
  infer_instance

private noncomputable def degreeOneEquiv (P : NonzeroPrimeIdeal K)
    (h : absNorm P.val = basePrime K P) : ZMod (basePrime K P) ≃+* (𝓞 K ⧸ P.val) := by
  let : CharP (𝓞 K ⧸ P.val) (basePrime K P) := charP_quotient_base K P
  have hn : Nat.card (𝓞 K ⧸ P.val) = basePrime K P := by
    rw [Ideal.absNorm_apply] at h
    exact h
  let : Finite (𝓞 K ⧸ P.val) := (Nat.finite_of_card_ne_zero
    (by rw [hn]; exact (prime_basePrime K P).ne_zero))
  let : Fintype (𝓞 K ⧸ P.val) := Fintype.ofFinite _
  exact RingEquiv.ofBijective (ZMod.castHom (dvd_refl (basePrime K P)) _)
    (ZMod.castHom_bijective _ ((Nat.card_eq_fintype_card).symm.trans hn))

private noncomputable def degreeOneReduce (P : NonzeroPrimeIdeal K)
    (h : absNorm P.val = basePrime K P) : 𝓞 K →+* ZMod (basePrime K P) :=
  (degreeOneEquiv K P h).symm.toRingHom.comp (Ideal.Quotient.mk P.val)

private lemma pow_three_of_quad {R : Type} [CommRing R] {z : R} (h : z^2 + z + 1 = 0) :
    z^3 = 1 := by
  linear_combination (z - 1) * h

private theorem prime_mod_three_of_quad {p : ℕ} [Fact p.Prime] (hp3 : ¬ p ∣ 3)
    {z : ZMod p} (hz : z^2 + z + 1 = 0) : p % 3 = 1 := by
  have hzpow := pow_three_of_quad hz
  have hz0 : z ≠ 0 := by
    intro h
    rw [h] at hzpow
    simp at hzpow
  have hz1 : z ≠ 1 := by
    intro h
    apply hp3
    apply (ZMod.natCast_eq_zero_iff 3 p).mp
    rw [h] at hz
    linear_combination hz
  let zU := Units.mk0 z hz0
  have hzU : zU ^ 3 = 1 := Units.ext (by simpa only [Units.val_pow_eq_pow_val, Units.val_mk0,
    Units.val_one, zU] using hzpow)
  have hzU1 : zU ≠ 1 := fun hh => hz1 (congrArg Units.val hh)
  have horder : orderOf zU = 3 :=
    ((Nat.dvd_prime (by decide : Nat.Prime 3)).mp (orderOf_dvd_of_pow_eq_one hzU)).resolve_left
      (fun h => hzU1 (orderOf_eq_one_iff.mp h))
  have hdvd : 3 ∣ p - 1 := by
    rw [← horder, ← Nat.totient_prime (Fact.out : p.Prime), ← ZMod.card_units_eq_totient,
      ← Nat.card_eq_fintype_card]
    exact orderOf_dvd_natCard zU
  have hd := Nat.dvd_iff_mod_eq_zero.mp hdvd
  have hpos := (Fact.out : p.Prime).two_le
  omega

private noncomputable def cubicPoly (a : ℕ) : ℚ[X] := X^3 - C (a : ℚ)
private noncomputable def quadPoly : ℚ[X] := X^2 + X + 1
private noncomputable def definingPoly (A : Finset ℕ) : ℚ[X] := quadPoly * ∏ a ∈ A, cubicPoly a

private theorem cubicPoly_natDegree (a : ℕ) : (cubicPoly a).natDegree = 3 :=
  Polynomial.natDegree_X_pow_sub_C

private theorem quadPoly_natDegree : quadPoly.natDegree = 2 := by
  simpa only [quadPoly, Polynomial.C_1, one_mul] using
    (Polynomial.natDegree_quadratic (a := (1 : ℚ)) (b := 1) (c := 1) one_ne_zero)

private theorem definingPoly_ne_zero (A : Finset ℕ) : definingPoly A ≠ 0 := by
  unfold definingPoly
  apply mul_ne_zero
  · intro h
    have hd := quadPoly_natDegree
    rw [h, Polynomial.natDegree_zero] at hd
    omega
  · exact Finset.prod_ne_zero_iff.mpr (fun a _ => by
      intro h
      have hd := cubicPoly_natDegree a
      rw [h, Polynomial.natDegree_zero] at hd
      omega)

private theorem integral_cube_in_splitting_field (A : Finset ℕ) {a : ℕ} (ha : a ∈ A) :
    ∃ x : 𝓞 (definingPoly A).SplittingField, x^3 = (a : 𝓞 (definingPoly A).SplittingField) := by
  let L := (definingPoly A).SplittingField
  let φ : ℚ →+* L := algebraMap ℚ L
  have hSplit : ((cubicPoly a).map φ).Splits := by
    apply (Polynomial.SplittingField.splits (definingPoly A)).of_dvd
      ((Polynomial.map_ne_zero_iff φ.injective).mpr (definingPoly_ne_zero A))
    apply Polynomial.map_dvd
    exact (Finset.dvd_prod_of_mem cubicPoly ha).trans (dvd_mul_left _ _)
  have hDegree : ((cubicPoly a).map φ).degree ≠ 0 := by
    have h := cubicPoly_natDegree a
    rw [Polynomial.degree_map_eq_of_injective φ.injective, Polynomial.degree_eq_natDegree
      (fun hz => by simp [hz] at h), h]
    decide
  obtain ⟨x, hx⟩ := hSplit.exists_eval_eq_zero hDegree
  have hxpow : x^3 = (a : L) := by
    exact sub_eq_zero.mp (by simpa [cubicPoly] using hx)
  have hxInt : IsIntegral ℤ x := IsIntegral.of_pow (by decide : 0 < (3 : ℕ)) (by
    rw [hxpow]
    exact isIntegral_natCast a)
  refine ⟨⟨x, hxInt⟩, ?_⟩
  exact Subtype.ext hxpow

private theorem integral_quad_in_splitting_field (A : Finset ℕ) :
    ∃ z : 𝓞 (definingPoly A).SplittingField, z^2 + z + 1 = 0 := by
  let L := (definingPoly A).SplittingField
  let φ : ℚ →+* L := algebraMap ℚ L
  have hSplit : (quadPoly.map φ).Splits := by
    apply (Polynomial.SplittingField.splits (definingPoly A)).of_dvd
      ((Polynomial.map_ne_zero_iff φ.injective).mpr (definingPoly_ne_zero A))
    apply Polynomial.map_dvd
    exact dvd_mul_right _ _
  have hDegree : (quadPoly.map φ).degree ≠ 0 := by
    have h := quadPoly_natDegree
    rw [Polynomial.degree_map_eq_of_injective φ.injective, Polynomial.degree_eq_natDegree
      (fun hz => by simp [hz] at h), h]
    decide
  obtain ⟨z, hz⟩ := hSplit.exists_eval_eq_zero hDegree
  have hz' : z^2 + z + 1 = 0 := by simpa [quadPoly] using hz
  have hzInt : IsIntegral ℤ z := IsIntegral.of_pow (by decide : 0 < (3 : ℕ)) (by
    rw [pow_three_of_quad hz']
    exact isIntegral_one)
  refine ⟨⟨z, hzInt⟩, ?_⟩
  exact Subtype.ext hz'

end Erdos940PrimeIdeals


namespace Erdos940PrimeIdeals

open Erdos940CubicCRT Finset Ideal NumberField
open scoped NumberField

private def coefficientSet (D : Finset KernelTriple) : Finset ℕ :=
  D.biUnion fun d => {d.1.val, d.2.1.val, d.2.2.val}

private theorem coefficient_pos (D : Finset KernelTriple) {a : ℕ} (ha : a ∈ coefficientSet D) :
    0 < a := by
  obtain ⟨d, _, hd⟩ := mem_biUnion.mp ha
  simp only [mem_insert, mem_singleton] at hd
  rcases hd with rfl | rfl | rfl
  · exact d.1.property.1
  · exact d.2.1.property.1
  · exact d.2.2.property.1

/-- Divergence for the required simultaneous cubic splitting conditions.
Degree-one prime ideals in a suitable number field suffice. -/
theorem splitting_primes_not_summable (D : Finset KernelTriple) :
    ¬ Summable (fun p : SplittingPrimes D => (1 : ℝ) / p.val) := by
  let A := coefficientSet D
  let L := (definingPoly A).SplittingField
  let : NumberField L := { to_charZero := inferInstance, to_finiteDimensional := inferInstance }
  let B := 3 * ∏ a ∈ A, a
  have hB : 0 < B := Nat.mul_pos (by decide) (Finset.prod_pos fun _ ha => coefficient_pos D ha)
  apply not_summable_of_prime_norms_cover L (SplittingPrimes D) B hB
  intro P hdeg hbad
  let p := basePrime L P
  have hp : p.Prime := prime_basePrime L P
  let : Fact p.Prime := ⟨hp⟩
  let φ := degreeOneReduce L P hdeg
  obtain ⟨z, hz⟩ := integral_quad_in_splitting_field A
  have hquad : (φ z)^2 + φ z + 1 = 0 := by
    simpa only [map_add, map_pow, map_one, map_zero] using congrArg φ hz
  have hp3 : ¬ p ∣ 3 := fun h => hbad (dvd_mul_of_dvd_left h _)
  have hpmod : p % 3 = 1 := prime_mod_three_of_quad hp3 hquad
  have hA (a : ℕ) (ha : a ∈ A) : Erdos940CubicCRT.IsNonzeroCube p a := by
    obtain ⟨x, hx⟩ := integral_cube_in_splitting_field A ha
    have hxe : (φ x)^3 = (a : ZMod p) := by
      simpa only [map_pow, map_natCast] using congrArg φ hx
    refine ⟨φ x, ?_, hxe⟩
    intro hz
    apply hbad
    have hza : (a : ZMod p) = 0 := by
      rw [hz, zero_pow (by decide : (3 : ℕ) ≠ 0)] at hxe
      exact hxe.symm
    have hpdvd : p ∣ a := (ZMod.natCast_eq_zero_iff a p).mp hza
    exact dvd_mul_of_dvd_right (hpdvd.trans (Finset.dvd_prod_of_mem id ha)) _
  refine ⟨hp, hpmod, fun d hd => ⟨?_, ?_, ?_⟩⟩
  · exact hA d.1.val (mem_biUnion.mpr ⟨d, hd, by simp only [mem_insert, true_or]⟩)
  · exact hA d.2.1.val (mem_biUnion.mpr ⟨d, hd, by simp only [mem_insert, true_or, or_true]⟩)
  · exact hA d.2.2.val (mem_biUnion.mpr ⟨d, hd, by simp only [mem_insert, mem_singleton, or_true]⟩)

end Erdos940PrimeIdeals

namespace Erdos940CubicCRT

/-- Unconditional positive lower density of the integers that are not sums
of three positive cube-full numbers. -/
theorem positive_lower_density_cube_full_complement :
    0 < ThreePositiveᶜ.lowerDensity Set.univ :=
  positive_lower_density_of_splitting_primes Erdos940PrimeIdeals.splitting_primes_not_summable

end Erdos940CubicCRT

theorem OMA.solution : OMA.R_Erdos940_erdos_940_variants_large_integers_R1.H1 :=
  Erdos940CubicCRT.positive_lower_density_cube_full_complement
