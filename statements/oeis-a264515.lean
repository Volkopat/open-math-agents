import Mathlib.Algebra.Group.End
import Mathlib.SetTheory.Cardinal.Finite

/-!
# A square identity for restricted permutations (OEIS A264515)

R. H. Hardin defines A264515 and A264507 by directed moves on rectangular
boards. Each original position is sent to its new position by a permutation.
Bruce Nye conjectured that the first count is the square of the second
(February 11, 2026). Both sequences start at index 1.

Sources: https://oeis.org/A264515 and https://oeis.org/A264507.
-/

namespace OMA.S_oeis_a264515

abbrev Wide (n : ℕ) := Fin (n + 1) × Fin 4
abbrev Narrow (n : ℕ) := Fin 2 × Fin (n + 1)

/-- The directed displacements are (-1,0), (0,2), (-1,-2), and (1,0). -/
def wideMove {n : ℕ} (u v : Wide n) : Prop :=
  (u.1.val = v.1.val + 1 ∧ v.2.val = u.2.val) ∨
  (v.1.val = u.1.val ∧ v.2.val = u.2.val + 2) ∨
  (u.1.val = v.1.val + 1 ∧ u.2.val = v.2.val + 2) ∨
  (v.1.val = u.1.val + 1 ∧ v.2.val = u.2.val)

/-- The directed displacements are (-1,1), (0,-1), (0,1), and (1,0). -/
def narrowMove {n : ℕ} (u v : Narrow n) : Prop :=
  (u.1.val = v.1.val + 1 ∧ v.2.val = u.2.val + 1) ∨
  (v.1.val = u.1.val ∧ u.2.val = v.2.val + 1) ∨
  (v.1.val = u.1.val ∧ v.2.val = u.2.val + 1) ∨
  (v.1.val = u.1.val + 1 ∧ v.2.val = u.2.val)

noncomputable def a515 (n : ℕ) : ℕ :=
  Nat.card {σ : Equiv.Perm (Wide n) // ∀ u, wideMove u (σ u)}

noncomputable def a507 (n : ℕ) : ℕ :=
  Nat.card {σ : Equiv.Perm (Narrow n) // ∀ u, narrowMove u (σ u)}

theorem main : ∀ n : ℕ, 1 ≤ n → a515 n = a507 n ^ 2 := by
  sorry

end OMA.S_oeis_a264515
