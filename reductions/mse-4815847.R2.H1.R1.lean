import OMAReductions.R_mse_4815847_R2

/-!
A simultaneous sign reversal normalizes both coefficients to positive. A separate
argument for the steeper directions only needs binomial sums in the final two rows.
The second subgoal confines the remaining positive directions to `2a < (N - 5)b`.

Source: https://mathoverflow.net/questions/514243
Credit: @studer
-/

namespace OMA.R_mse_4815847_R2_H1_R1

open OMA.S_mse_4815847 Finset

/-- The direction range in which every putative balanced cut reduces to two rows. -/
def H1 : Prop :=
  ∀ N : ℕ, 2 ≤ N → ∀ a b c : ℝ, 0 < a → 0 < b → ((N : ℝ) - 5) * b ≤ 2 * a →
    (∀ p ∈ entries N, side a b c p ≠ 0) →
    ∑ p ∈ (entries N).filter (fun p => 0 < side a b c p), p.1.choose p.2 ≠
      ∑ p ∈ (entries N).filter (fun p => side a b c p < 0), p.1.choose p.2

/-- The remaining positive directions. -/
def H2 : Prop :=
  ∀ N : ℕ, 2 ≤ N → ∀ a b c : ℝ, 0 < a → 0 < b → 2 * a < ((N : ℝ) - 5) * b →
    (∀ p ∈ entries N, side a b c p ≠ 0) →
    ∑ p ∈ (entries N).filter (fun p => 0 < side a b c p), p.1.choose p.2 ≠
      ∑ p ∈ (entries N).filter (fun p => side a b c p < 0), p.1.choose p.2

theorem main : H1 → H2 → OMA.R_mse_4815847_R2.H1 := by
  intro steep shallow N hN a b c hab avoid
  have positive (x y z : ℝ) (hx : 0 < x) (hy : 0 < y)
      (hne : ∀ p ∈ entries N, side x y z p ≠ 0) :
      ∑ p ∈ (entries N).filter (fun p => 0 < side x y z p), p.1.choose p.2 ≠
        ∑ p ∈ (entries N).filter (fun p => side x y z p < 0), p.1.choose p.2 := by
    rcases le_or_gt (((N : ℝ) - 5) * y) (2 * x) with h | h
    · exact steep N hN x y z hx hy h hne
    · exact shallow N hN x y z hx hy h hne
  rcases mul_pos_iff.mp hab with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · exact positive a b c ha hb avoid
  · have reverse (p : ℕ × ℕ) : side (-a) (-b) (-c) p = -side a b c p := by
      simp only [side]
      ring
    have h := positive (-a) (-b) (-c) (neg_pos.mpr ha) (neg_pos.mpr hb) (by
      intro p hp
      rw [reverse]
      exact neg_ne_zero.mpr (avoid p hp))
    simp only [reverse, neg_pos, neg_lt_zero] at h
    exact h.symm

end OMA.R_mse_4815847_R2_H1_R1
