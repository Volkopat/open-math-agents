import OMAReductions.R_ERH_extended_riemann_hypothesis_R1_H2_R1_H2_R1
import Mathlib

/-! Truncate the ideal Möbius coefficients at m. At m² their signed sum is twice the
short sum minus a bilinear Dirichlet convolution. The short sum and the entire
range r ≥ 1 follow from counting ideals. -/
namespace OMA.R_ERH_extended_riemann_hypothesis_R1_H2_R1_H2_R1_H2_R1
open Finset Filter Asymptotics NumberField UniqueFactorizationMonoid
open scoped NumberField Topology
noncomputable section


lemma hyp_square (a z b : ArithmeticFunction ℂ) (az : a*z = 1) (m : ℕ)
    (hb : ∀ n, b n = if n ≤ m then a n else 0) (n : ℕ) (hn : n ≤ m^2) :
    a n = b n + b n - (b*b*z) n := by
  let e := a-b
  have small (k : ℕ) (hk : k ≤ m) : e k = 0 := by
    change a k - b k = 0
    rw [hb, if_pos hk, sub_self]
  have van (k : ℕ) (hk : k ≤ m^2) : (e*e) k = 0 := by
    rw [ArithmeticFunction.mul_apply]
    apply sum_eq_zero
    intro q hq
    have prod := (Nat.mem_divisorsAntidiagonal.mp hq).1
    by_cases hl : q.1 ≤ m
    · simp [small _ hl]
    · have hr : q.2 ≤ m := by
        by_contra! large
        have := Nat.mul_le_mul (show m+1 ≤ q.1 by omega) (show m+1 ≤ q.2 by omega)
        nlinarith
      simp [small _ hr]
  have empty : (e*e*z) n = 0 := by
    rw [ArithmeticFunction.mul_apply]
    apply sum_eq_zero
    intro q hq
    have prod := Nat.mem_divisorsAntidiagonal.mp hq
    have le : q.1 ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero prod.2) ⟨q.2,prod.1.symm⟩
    simp [van q.1 (le.trans hn)]
  have identity : e*e*z = a-b-b+b*b*z := by
    dsimp [e]
    calc
      _ = (a-b-b)*(a*z)+b*b*z := by ring
      _ = _ := by rw [az,mul_one]
  rw [identity] at empty
  change a n - b n - b n + (b*b*z) n = 0 at empty
  linear_combination empty

lemma cutoff_sum (a b : ArithmeticFunction ℂ) (m : ℕ)
    (hb : ∀ n, b n = if n ≤ m then a n else 0) :
    (∑ k ∈ Icc 1 (m^2), b k) = ∑ k ∈ Icc 1 m, a k := by
  have h : (Icc 1 (m^2)).filter (fun k => k ≤ m) = Icc 1 m := by
    ext k
    simp only [mem_filter, mem_Icc]
    have : m ≤ m^2 := by cases m <;> nlinarith
    omega
  simp_rw [hb]
  rw [← sum_filter, h]

/-- The total variation up to n is bounded by the count of ideals of norm ≤ n. -/
lemma total_variation (K : Type) [Field K] [NumberField K] :
    let P := {I : Ideal (𝓞 K) // I.IsPrime ∧ I ≠ ⊥}
    let N (S : Finset P) : ℕ := ∏ p ∈ S, Ideal.absNorm p.1
    let a (n : ℕ) : ℂ := ∑' S : N ⁻¹' {n}, (-1 : ℂ)^S.1.card
    (fun n : ℕ => ∑ k ∈ Icc 1 n, ‖a k‖) =O[atTop] fun n => (n : ℝ) := by
  classical
  intro P N a
  let prodIdeal (S : Finset P) : Ideal (𝓞 K) := ∏ p ∈ S, p.val
  have product_injective : Function.Injective prodIdeal := by
    have factors (S : Finset P) :
        normalizedFactors (prodIdeal S) = S.val.map Subtype.val := by
      apply normalizedFactors_prod_of_prime
      intro I h
      obtain ⟨p, _, rfl⟩ := Multiset.mem_map.mp h
      exact (Ideal.prime_iff_isPrime p.property.2).mpr p.property.1
    intro S T eq
    exact Finset.val_inj.mp (Multiset.map_injective Subtype.val_injective
      ((factors S).symm.trans ((congrArg normalizedFactors eq).trans (factors T))))
  have norm_product (S : Finset P) : Ideal.absNorm (prodIdeal S) = N S := by
    simp [prodIdeal, N, map_prod]
  have coeff_le (k : ℕ) : ‖a k‖ ≤ (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = k} : ℝ) := by
    let A := N ⁻¹' {k}
    let B := {I : Ideal (𝓞 K) // Ideal.absNorm I = k}
    have : Finite B := Ideal.finite_setOfPred_absNorm_eq k
    let f (s : A) : B := ⟨prodIdeal s.val, (norm_product s.val).trans s.property⟩
    have inj : Function.Injective f := fun _ _ e => Subtype.ext (product_injective (congrArg Subtype.val e))
    let : Fintype A := @Fintype.ofFinite A (Finite.of_injective f inj)
    dsimp only [a]
    rw [tsum_fintype]
    refine (norm_sum_le _ _).trans ?_
    simpa [A, B, Nat.card_eq_fintype_card (α := A)] using (show
      (Fintype.card A : ℝ) ≤ (Nat.card B : ℝ) by
        exact_mod_cast (show Fintype.card A ≤ Nat.card B by
          simpa only [Nat.card_eq_fintype_card (α := A)] using Nat.card_le_card_of_injective f inj))
  have mass_le (n : ℕ) : ∑ k ∈ Icc 1 n, ‖a k‖ ≤
      (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I ≤ n} : ℝ) := by
    refine (Finset.sum_le_sum (fun k _ => coeff_le k)).trans ?_
    rw [← Nat.cast_sum, Nat.cast_le]
    rw [← Finset.card_preimage_eq_sum_card_image_eq (fun k _ => Ideal.finite_setOfPred_absNorm_eq k)]
    let B := {I : Ideal (𝓞 K) // Ideal.absNorm I ≤ n}
    have : Finite B := Ideal.finite_setOfPred_absNorm_le n
    let f (I : (Ideal.absNorm : Ideal (𝓞 K) → ℕ) ⁻¹' (↑(Finset.Icc 1 n) : Set ℕ)) : B :=
      ⟨I.val, (Finset.mem_Icc.mp I.property).2⟩
    exact Nat.card_le_card_of_injective f (fun _ _ e => Subtype.ext (congrArg (fun x : B => x.val) e))
  have growth := (NumberField.Ideal.tendsto_norm_le_div_atTop K).comp tendsto_natCast_atTop_atTop
  have bound : (fun n : ℕ => (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I ≤ (n : ℝ)} : ℝ))
      =O[atTop] fun n => (n : ℝ) := by
    apply isBigO_of_div_tendsto_nhds _ _ growth
    filter_upwards [eventually_ge_atTop 1] with n hn eq
    exact False.elim ((by exact_mod_cast (show n ≠ 0 by omega) : (n : ℝ) ≠ 0) eq)
  apply IsBigO.trans _ bound
  apply isBigO_of_le
  intro n
  simp only [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _)),
    Nat.cast_le, Nat.abs_cast]
  exact mass_le n

/-- A Möbius factor times the full ideal-counting factor is the Dirichlet unit. -/
def H1 : Prop :=
  ∀ (K : Type) [Field K] [NumberField K],
    let P := {I : Ideal (𝓞 K) // I.IsPrime ∧ I ≠ ⊥}
    let N (S : Finset P) : ℕ := ∏ p ∈ S, Ideal.absNorm p.1
    let a (n : ℕ) : ℂ := ∑' S : N ⁻¹' {n}, (-1 : ℂ)^S.1.card
    let f : ArithmeticFunction ℂ := ⟨fun n => if n = 0 then 0 else a n, by simp⟩
    let z : ArithmeticFunction ℂ := ⟨fun n => if n = 0 then 0 else
      (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℂ), by simp⟩
    f * z = 1

/-- The two Möbius factors are supported on norms up to the square-root cutoff. -/
def H2 : Prop :=
  ∀ (K : Type) [Field K] [NumberField K],
    let P := {I : Ideal (𝓞 K) // I.IsPrime ∧ I ≠ ⊥}
    let N (S : Finset P) : ℕ := ∏ p ∈ S, Ideal.absNorm p.1
    let a (n : ℕ) : ℂ := ∑' S : N ⁻¹' {n}, (-1 : ℂ)^S.1.card
    let f : ArithmeticFunction ℂ := ⟨fun n => if n = 0 then 0 else a n, by simp⟩
    let z : ArithmeticFunction ℂ := ⟨fun n => if n = 0 then 0 else
      (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℂ), by simp⟩
    let b (m : ℕ) : ArithmeticFunction ℂ := ⟨fun n => if n ≤ m then f n else 0, by simp⟩
    ∀ r : ℝ, 1/2 < r → r < 1 →
      (fun m : ℕ => ∑ k ∈ Icc 1 (m^2), (b m * b m * z) k) =O[atTop]
        fun m : ℕ => ((m^2 : ℕ) : ℝ)^r

theorem main : H1 → H2 → OMA.R_ERH_extended_riemann_hypothesis_R1_H2_R1_H2_R1.H2 := by
  classical
  intro inv remainder K _ _ P N a r hr
  let f : ArithmeticFunction ℂ := ⟨fun n => if n = 0 then 0 else a n, by simp⟩
  let z : ArithmeticFunction ℂ := ⟨fun n => if n = 0 then 0 else
      (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℂ), by simp⟩
  let b (m : ℕ) : ArithmeticFunction ℂ := ⟨fun n => if n ≤ m then f n else 0, by simp⟩
  let S (m : ℕ) := ∑ k ∈ Icc 1 m, a k
  let V (m : ℕ) := ∑ k ∈ Icc 1 m, ‖a k‖
  have var : V =O[atTop] fun n : ℕ => (n : ℝ) := total_variation K
  have raw : S =O[atTop] fun n : ℕ => (n : ℝ) := by
    apply IsBigO.trans _ var
    apply isBigO_of_le
    intro n
    exact (norm_sum_le _ _).trans (le_abs_self (V n))
  have large (n : ℕ) (hn : 1 ≤ n) (t : ℝ) (ht : 1 ≤ t) : (n : ℝ) ≤ (n : ℝ)^t :=
    Real.self_le_rpow_of_one_le (by exact_mod_cast hn) ht
  by_cases h : 1 ≤ r
  · have sq := raw.comp_tendsto (tendsto_pow_atTop (by decide : 2 ≠ 0))
    apply IsBigO.trans sq
    apply IsBigO.of_bound 1
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
    simp only [Function.comp_apply, Nat.abs_cast, Real.norm_eq_abs, one_mul,
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
    exact large (m^2) (pow_pos (show 0 < m from hm) 2) r h
  have short : S =O[atTop] fun m : ℕ => ((m^2 : ℕ) : ℝ)^r := by
    apply raw.trans
    apply IsBigO.of_bound 1
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
    simp only [Real.norm_eq_abs, Nat.abs_cast, one_mul, Nat.cast_pow,
      abs_of_nonneg (Real.rpow_nonneg (sq_nonneg _) _)]
    rw [← Real.rpow_natCast_mul (Nat.cast_nonneg _) 2 r]
    exact large m hm _ (by push_cast; linarith)
  have bil : (fun m : ℕ => ∑ k ∈ Icc 1 (m^2), (b m*b m*z) k) =O[atTop]
      fun m : ℕ => ((m^2 : ℕ) : ℝ)^r := remainder K r hr (lt_of_not_ge h)
  have agree (n : ℕ) : (∑ k ∈ Icc 1 n, f k) = S n := by
    apply sum_congr rfl
    intro k hk
    have hk' := (mem_Icc.mp hk).1
    exact if_neg (by omega : k ≠ 0)
  have eq (m : ℕ) : S (m^2) = S m + S m - ∑ k ∈ Icc 1 (m^2), (b m*b m*z) k := by
    rw [← agree (m^2)]
    calc
      _ = ∑ k ∈ Icc 1 (m^2), (b m k + b m k - (b m*b m*z) k) := by
        apply sum_congr rfl
        intro k hk
        exact hyp_square f z (b m) (inv K) m (fun _ => rfl) k (mem_Icc.mp hk).2
      _ = _ := by rw [sum_sub_distrib, sum_add_distrib, cutoff_sum f (b m) m (fun _ => rfl), agree]
  simpa only [← eq] using (short.add short).sub bil

end
end OMA.R_ERH_extended_riemann_hypothesis_R1_H2_R1_H2_R1_H2_R1
