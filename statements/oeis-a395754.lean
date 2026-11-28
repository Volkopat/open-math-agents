import Mathlib.Data.Nat.Nth
import Mathlib.RingTheory.Radical.NatInt

/-!
The conjecture in OEIS A395754 (Michael De Vlieger, May 2026).
Sources: https://oeis.org/A395754 and https://oeis.org/A005117.
The sequence of squarefree numbers begins with 1 at index 1.
The candidates are strictly positive, as in the defining algorithm.
-/

namespace OMA.S_oeis_a395754

open UniqueFactorizationMonoid

noncomputable def squarefreeTerm (n : ℕ) : ℕ := Nat.nth Squarefree (n - 1)

noncomputable def candidates (m : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (m ^ 2)).filter
    (fun k => 0 < k ∧ radical k ∣ m ∧ radical (k + 1) ∣ m)

noncomputable def a (n : ℕ) : ℕ := (candidates (squarefreeTerm n)).card

theorem main : ∀ n : ℕ, 1 ≤ n → Odd (squarefreeTerm n) → a n = 0 := by
  sorry

end OMA.S_oeis_a395754
