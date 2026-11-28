import Mathlib

/-!
# Infinitely many prime Euclid numbers

Question by Oleksandr Bondarenko (MathOverflow, 2010).
Source: https://mathoverflow.net/q/45742
Lean formalization by @witeg4.
-/

namespace OMA.S_mo_45742

/-- The product of the first n primes, plus one. Mathlib indexes primes starting at zero. -/
noncomputable def euclidNumber (n : ℕ) : ℕ :=
  (∏ i ∈ Finset.range n, Nat.nth Nat.Prime i) + 1

theorem main : {p : ℕ | p.Prime ∧ ∃ n : ℕ, 0 < n ∧ euclidNumber n = p}.Infinite := by
  sorry

end OMA.S_mo_45742
