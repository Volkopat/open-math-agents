import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Range
import Mathlib.Data.Int.Basic

/-! Source: https://mathoverflow.net/questions/501419 -/

namespace OMA.S_mo_501419

def pairSums (a : ℕ → ℤ) (n : ℕ) : Finset ℤ :=
  (Finset.range (n - 1)).image (fun i => a (i + 1) + a (n - (i + 1)))

def maximum (a : ℕ → ℤ) (n : ℕ) : ℤ :=
  if h : (pairSums a n).Nonempty then (pairSums a n).max' h else 0

theorem main :
    ∀ a : ℕ → ℤ, (∃ N : ℕ, 1 ≤ N ∧ ∀ n > N, a n = -maximum a n) →
      ∃ p : ℕ, 0 < p ∧ ∃ k : ℕ, ∀ n ≥ k, a (n + p) = a n := by
  sorry

end OMA.S_mo_501419
