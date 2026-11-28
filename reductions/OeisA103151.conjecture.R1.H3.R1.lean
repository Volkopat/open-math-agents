import OMAReductions.R_OeisA103151_conjecture_R1
import Mathlib.Tactic

/-!
# Reduction of the `n ≡ 0 (mod 3)` case of A103151

In this residue class the decomposition `2n + 1 = 2·3 + (2n - 5)` is available.
Whenever `2n - 5` is prime, it immediately contributes the admissible prime `p = 3`;
that positive case is proved here.  The remaining composite case is split by the
parity of `n`, equivalently by the two residue classes of `n` modulo `6`.
-/

namespace OMA.R_OeisA103151_conjecture_R1_H3_R1

open OeisA103151

/-- The composite exceptional case with `n` even. -/
def H1 : Prop :=
  ∀ n : ℕ, 4 ≤ n → n % 3 = 0 → ¬ (2 * n - 5).Prime → n % 2 = 0 → a n ≥ 1

/-- The composite exceptional case with `n` odd. -/
def H2 : Prop :=
  ∀ n : ℕ, 4 ≤ n → n % 3 = 0 → ¬ (2 * n - 5).Prime → n % 2 = 1 → a n ≥ 1

/-- If `2n - 5` is prime, then `p = 3` is already counted by `a n`. -/
theorem prime_tail_witness (n : ℕ) (hn : 4 ≤ n) (hp : (2 * n - 5).Prime) :
    a n ≥ 1 := by
  have hq : 2 * n + 1 - 2 * 3 = 2 * n - 5 := by omega
  have hmem : 3 ∈ Finset.filter (fun p : ℕ =>
      p.Prime ∧ p ≠ 2 ∧ 2 * p < 2 * n + 1 ∧ Nat.Prime (2 * n + 1 - 2 * p))
      (Finset.range (n + 1)) := by
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, by decide, by decide, by omega, ?_⟩
    rw [hq]
    exact hp
  have hpos : 0 < a n := by
    unfold a
    exact Finset.card_pos.mpr ⟨3, hmem⟩
  omega

theorem main : H1 → H2 → OMA.R_OeisA103151_conjecture_R1.H3 := by
  intro h1 h2 n hn hnmod
  by_cases hp : (2 * n - 5).Prime
  · exact prime_tail_witness n hn hp
  · have hpar : n % 2 = 0 ∨ n % 2 = 1 := by omega
    rcases hpar with hpar | hpar
    · exact h1 n hn hnmod hp hpar
    · exact h2 n hn hnmod hp hpar

end OMA.R_OeisA103151_conjecture_R1_H3_R1
