import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Finset.Sort

/-!
# Palindromic residues of proper divisors

Source: https://oeis.org/A393833
Credit: @jatin6

Michel Lagneau's conjecture asks whether the set defining the least value is
nonempty for every positive modulus. The proper divisors are sorted before
taking residues, as in the defining sequence.
-/

namespace OMA.S_oeis_a393833

def residues (n k : ℕ) : List ℕ :=
  (k.properDivisors.sort).map (fun d => d % n)

theorem main : ∀ n : ℕ, 1 ≤ n → ∃ k : ℕ, 0 < k ∧ k.divisors.card = 2 * n + 2 ∧
    residues n k = (residues n k).reverse := by
  sorry

end OMA.S_oeis_a393833
