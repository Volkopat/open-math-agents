import OMAReductions.R_Erdos929_erdos_929_variants_rosser_R1

-- Reduction Erdos929.erdos_929.variants.rosser.R1.H1.R1 of step Erdos929.erdos_929.variants.rosser.R1.H1
-- Credit: @JamesSlash

/-!
# Iwaniec's Jacobsthal bound from the strong prime number theorem

* `H1`: the prime number theorem with the de la Vallée Poussin error term, in the form
  `StrongPNT` of the PrimeNumberTheoremAnd project: `ψ(x) - x = O(x exp(-c √(log x)))`.
* `H2`: Iwaniec's theorem ([I78, Corollary], H. Iwaniec, *On the problem of Jacobsthal*,
  Demonstratio Math. 11 (1978)) conditional on the strong prime number theorem: if `m` consecutive
  integers are each divisible by one of `r ≥ 2` given primes, then `m ≤ C (r log r)²`.
  The Lean development jasondavies/iwaniec-linear-sieve derives it from `StrongPNT` through
  Iwaniec's linear sieve [I71].
* `main`: sets of at most one prime cover at most one integer of a block; for `r ≥ 2` primes
  apply `H2` (with `log r ≤ log (r + 1)`).
-/

namespace OMA.R_Erdos929_erdos_929_variants_rosser_R1_H1_R1

open Finset

/-- The strong prime number theorem (`StrongPNT` in PrimeNumberTheoremAnd). -/
def H1 : Prop :=
  ∃ c > 0, Asymptotics.IsBigO Filter.atTop (Chebyshev.psi - id)
    (fun x : ℝ ↦ x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 2)))

/-- Iwaniec's bound for Jacobsthal's problem, assuming the strong prime number theorem. -/
def H2 : Prop :=
  (∃ c > 0, Asymptotics.IsBigO Filter.atTop (Chebyshev.psi - id)
    (fun x : ℝ ↦ x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 2)))) →
  ∃ C : ℝ, ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) → 2 ≤ S.card →
    ∀ (x : ℤ) (m : ℕ), (∀ k < m, ∃ p ∈ S, (p : ℤ) ∣ x + k) →
      (m : ℝ) ≤ C * ((S.card : ℝ) * Real.log S.card) ^ 2

lemma small_block {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hcard : P.card ≤ 1) {k n : ℕ}
    (hcov : ∀ i ∈ Icc 1 k, ∃ p ∈ P, p ∣ n + i) : k ≤ 1 := by
  by_contra hk
  push_neg at hk
  obtain ⟨p, hp, hd1⟩ := hcov 1 (mem_Icc.mpr ⟨le_refl _, by omega⟩)
  obtain ⟨q, hq, hd2⟩ := hcov 2 (mem_Icc.mpr ⟨by norm_num, by omega⟩)
  have hpq : p = q := Finset.card_le_one.mp hcard p hp q hq
  subst hpq
  have h2 : p ∣ (n + 1) + 1 := by simpa [add_assoc] using hd2
  have h1 : p ∣ 1 := (Nat.dvd_add_right hd1).mp h2
  exact (hP p hp).one_lt.ne' (Nat.dvd_one.mp h1)

theorem main : H1 → H2 → OMA.R_Erdos929_erdos_929_variants_rosser_R1.H1 := by
  intro h1 h2
  obtain ⟨C, hC⟩ := h2 h1
  refine ⟨max C 0 + 4, by positivity, ?_⟩
  intro P hP k n hcov
  have hlog2 : (1 : ℝ) / 2 < Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  by_cases h2P : 2 ≤ P.card
  · have hm := hC P hP h2P ((n : ℤ) + 1) k (fun j hj => by
      obtain ⟨p, hp, hd⟩ := hcov (j + 1) (mem_Icc.mpr ⟨by omega, by omega⟩)
      refine ⟨p, hp, ?_⟩
      have hd' : ((p : ℕ) : ℤ) ∣ ((n + (j + 1) : ℕ) : ℤ) := Int.natCast_dvd_natCast.mpr hd
      have he : ((n + (j + 1) : ℕ) : ℤ) = (n : ℤ) + 1 + (j : ℤ) := by push_cast; ring
      rwa [he] at hd')
    have hr : (2 : ℝ) ≤ (P.card : ℝ) := by exact_mod_cast h2P
    have hl0 : 0 ≤ Real.log (P.card : ℝ) := Real.log_nonneg (by linarith)
    have hl1 : Real.log (P.card : ℝ) ≤ Real.log ((P.card : ℝ) + 1) :=
      Real.log_le_log (by linarith) (by linarith)
    have hsq : ((P.card : ℝ) * Real.log P.card) ^ 2 ≤
        ((P.card : ℝ) * Real.log ((P.card : ℝ) + 1)) ^ 2 := by
      have : (P.card : ℝ) * Real.log P.card ≤ (P.card : ℝ) * Real.log ((P.card : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left hl1 (by linarith)
      exact pow_le_pow_left₀ (mul_nonneg (by linarith) hl0) this 2
    have hC0 : C * ((P.card : ℝ) * Real.log P.card) ^ 2 ≤
        max C 0 * ((P.card : ℝ) * Real.log P.card) ^ 2 :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)
    have hC1 : max C 0 * ((P.card : ℝ) * Real.log P.card) ^ 2 ≤
        (max C 0 + 4) * ((P.card : ℝ) * Real.log ((P.card : ℝ) + 1)) ^ 2 := by
      have h4 : 0 ≤ 4 * ((P.card : ℝ) * Real.log ((P.card : ℝ) + 1)) ^ 2 := by positivity
      have := mul_le_mul_of_nonneg_left hsq (le_max_right C 0)
      nlinarith
    linarith
  · push_neg at h2P
    have hk := small_block hP (by omega) hcov
    rcases Nat.lt_or_ge k 1 with hk0 | hk1
    · have : k = 0 := by omega
      subst this
      simp only [Nat.cast_zero]
      positivity
    · have hk1' : k = 1 := by omega
      subst hk1'
      obtain ⟨p, hp, -⟩ := hcov 1 (mem_Icc.mpr ⟨le_refl _, le_refl _⟩)
      have hc1 : P.card = 1 := by
        have := Finset.card_pos.mpr ⟨p, hp⟩
        omega
      rw [hc1]
      simp only [Nat.cast_one, one_mul]
      have h1 : (1 : ℝ) + 1 = 2 := by norm_num
      rw [h1]
      have hsq : (1 : ℝ) / 4 ≤ Real.log 2 ^ 2 := by nlinarith
      have hC0 : 0 ≤ max C 0 := le_max_right _ _
      nlinarith [sq_nonneg (Real.log 2)]

end OMA.R_Erdos929_erdos_929_variants_rosser_R1_H1_R1
