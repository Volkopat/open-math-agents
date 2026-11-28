import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Logic.Function.Iterate

/-!
# A269304: Coalescence under iteration using the greatest prime factor

Cody M. Haderlie conjectures that the sequences from any two positive starting
values share an infinite tail under the iteration described in the entry.

Source: https://oeis.org/A269304
Credit: @MMexicann
-/

namespace OMA.S_oeis_a269304

/-- One step of Haderlie's iteration. The greatest prime factor is taken to be
one at the input one. -/
def step (n : ℕ) : ℕ :=
  n + n / max 1 (n.primeFactors.sup id) + 1

theorem main : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
    ∃ i j : ℕ, ∀ k : ℕ, (step^[i + k]) a = (step^[j + k]) b := by
  sorry

end OMA.S_oeis_a269304
