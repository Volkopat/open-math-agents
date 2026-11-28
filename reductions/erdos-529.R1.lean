import OMAStatements.S_erdos_529

-- Reduction erdos-529.R1 of Erdős Problem 529
-- Credit: @sntntHb
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- Sketch. The target is the conjunction of the planar question (H1) with the bound
-- d_k(n) = O(n^(1/2)) for every k ≥ 3. This file separates the dimensions:
-- * H1: the planar question d_2(n)/n^(1/2) → ∞ (open).
-- * H2: d_3(n) = O(n^(1/2)) (open).
-- * H3: d_4(n) = O(n^(1/2)) (open; the conjectured behaviour in dimension 4 has an extra
--   (log n)^(1/8) factor, so this is where the expected answer to the source question lies).
-- * H4: for k ≥ 5 the mean square endpoint displacement of a uniform n-step self-avoiding walk
--   is O(n). This is the theorem of Hara and Slade (lace expansion, 1992: the mean square
--   displacement is asymptotic to D n in five or more dimensions), not yet in Mathlib.
-- The main theorem derives the high-dimensional part of the target from H4 by the
-- Cauchy–Schwarz inequality (mean distance ≤ square root of the mean square distance).

namespace OMA.R_erdos_529_R1

open Filter OMA.S_erdos_529

/-- The planar question: `d₂(n)/√n → ∞`. -/
def H1 : Prop :=
  Tendsto (fun n : ℕ ↦ d 2 n / Real.sqrt n) atTop atTop

/-- Dimension three: `d₃(n) = O(√n)`. -/
def H2 : Prop :=
  (fun n : ℕ ↦ d 3 n) =O[atTop] (fun n : ℕ ↦ Real.sqrt n)

/-- Dimension four: `d₄(n) = O(√n)`. -/
def H3 : Prop :=
  (fun n : ℕ ↦ d 4 n) =O[atTop] (fun n : ℕ ↦ Real.sqrt n)

/-- Hara–Slade: in dimension `k ≥ 5` the mean square endpoint displacement of a uniformly
random `n`-step self-avoiding walk is `O(n)`. -/
def H4 : Prop :=
  ∀ k ≥ 5, (fun n : ℕ ↦ (∑ w ∈ selfAvoidingWalks k n, ∑ i, ((position w n i : ℝ)) ^ 2) /
    (selfAvoidingWalks k n).card) =O[atTop] (fun n : ℕ ↦ (n : ℝ))

/-- Mean of square roots is at most the square root of the mean (Cauchy–Schwarz). -/
lemma mean_sqrt_le {α : Type*} (S : Finset α) (g : α → ℝ) (hg : ∀ a, 0 ≤ g a) :
    (∑ a ∈ S, Real.sqrt (g a)) / S.card ≤ Real.sqrt ((∑ a ∈ S, g a) / S.card) := by
  rcases Nat.eq_zero_or_pos S.card with h0 | hpos
  · simp [h0]
  have hc : (0 : ℝ) < S.card := by exact_mod_cast hpos
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq S (fun _ ↦ (1 : ℝ)) (fun a ↦ Real.sqrt (g a))
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one,
    Real.sq_sqrt (hg _)] at hcs
  refine le_trans (le_abs_self _) (Real.abs_le_sqrt ?_)
  rw [div_pow, div_le_div_iff₀ (by positivity) hc]
  nlinarith

lemma d_nonneg (k n : ℕ) : 0 ≤ d k n := by
  unfold d
  apply div_nonneg
  · exact Finset.sum_nonneg (fun _ _ ↦ Real.sqrt_nonneg _)
  · exact Nat.cast_nonneg _

lemma d_le (k n : ℕ) : d k n ≤ Real.sqrt ((∑ w ∈ selfAvoidingWalks k n,
    ∑ i, ((position w n i : ℝ)) ^ 2) / (selfAvoidingWalks k n).card) := by
  unfold d dist0
  exact mean_sqrt_le _ _ (fun _ ↦ Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _))

theorem main : H1 → H2 → H3 → H4 → type_of% @OMA.S_erdos_529.main := by
  intro h1 h2 h3 h4
  refine ⟨h1, fun k hk ↦ ?_⟩
  rcases (by omega : k = 3 ∨ k = 4 ∨ 5 ≤ k) with rfl | rfl | h5
  · exact h2
  · exact h3
  · obtain ⟨c, hc⟩ := Asymptotics.isBigO_iff.mp (h4 k h5)
    refine Asymptotics.isBigO_iff.mpr ⟨Real.sqrt (max c 0), ?_⟩
    filter_upwards [hc] with n hn
    rw [Real.norm_of_nonneg (d_nonneg k n), Real.norm_of_nonneg (Real.sqrt_nonneg _),
      ← Real.sqrt_mul (le_max_right _ _)]
    refine le_trans (d_le k n) (Real.sqrt_le_sqrt ?_)
    have hm : 0 ≤ (∑ w ∈ selfAvoidingWalks k n, ∑ i, ((position w n i : ℝ)) ^ 2) /
        (selfAvoidingWalks k n).card :=
      div_nonneg (Finset.sum_nonneg (fun _ _ ↦ Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)))
        (Nat.cast_nonneg _)
    rw [Real.norm_of_nonneg hm, Real.norm_of_nonneg (Nat.cast_nonneg _)] at hn
    exact le_trans hn (mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _))

end OMA.R_erdos_529_R1
