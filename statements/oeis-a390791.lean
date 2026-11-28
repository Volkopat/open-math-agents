import Mathlib.Data.Set.Card

/-!
# Hamiltonian paths on a four-cycle times a path

Source: https://oeis.org/A390791
Credit: @luciusacarr

The generating-function conjecture is stated coefficientwise. Multiplying
by the denominator gives the first four counts and the recurrence.
-/

namespace OMA.S_oeis_a390791

abbrev Vertex (n : ℕ) := Fin 4 × Fin (2 * n + 2)

def adjacent {n : ℕ} (u v : Vertex n) : Prop :=
  (u.2 = v.2 ∧ ((u.1.val + 1) % 4 = v.1.val ∨ (v.1.val + 1) % 4 = u.1.val)) ∨
  (u.1 = v.1 ∧ (u.2.val + 1 = v.2.val ∨ v.2.val + 1 = u.2.val))

/-- Lists visit every vertex once and use zero-based coordinates for the
specified first and last vertices. -/
noncomputable def a (n : ℕ) : ℕ :=
  ({p : List (Vertex n) | p.Nodup ∧
    (∀ v : Vertex n, v ∈ p) ∧ p.IsChain adjacent ∧
    p.head? = some (0, 0) ∧ p.getLast? = some (2, Fin.last (2 * n + 1))}).ncard

theorem main :
    a 0 = 6 ∧ a 1 = 100 ∧ a 2 = 1940 ∧ a 3 = 38404 ∧
    ∀ n : ℕ, (a (n + 4) : ℤ) =
      21 * (a (n + 3) : ℤ) - 26 * (a (n + 2) : ℤ) +
        44 * (a (n + 1) : ℤ) - 8 * (a n : ℤ) := by
  sorry

end OMA.S_oeis_a390791
