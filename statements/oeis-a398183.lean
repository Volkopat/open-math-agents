import Mathlib

/-!
# Second Goldbach partitions in OEIS A398183

Source: https://oeis.org/A398183 (OEIS Foundation, CC BY-SA 4.0).
Formalization: @sturdy4days.

Each unordered partition of 2n is represented by its smaller prime.
The OEIS sequence starts at n = 3.
-/

namespace OMA.S_oeis_a398183

def hasGoldbachPartner (n p : ℕ) : Prop :=
  p ≤ n ∧ p.Prime ∧ (2 * n - p).Prime

theorem main : ∀ n : ℕ, 3 ≤ n →
    ((¬ ∃ p q : ℕ, p < q ∧ hasGoldbachPartner n p ∧ hasGoldbachPartner n q) ↔
      n = 3 ∨ n = 4 ∨ n = 6) := by
  sorry

end OMA.S_oeis_a398183
