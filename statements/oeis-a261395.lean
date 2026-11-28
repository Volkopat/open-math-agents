import Mathlib

/-!
# Geometric progressions of shifted prime-indexed primes

In OEIS A261395, Zhi-Wei Sun conjectures infinitude for every nonzero
integer shift. The sequence itself records the middle prime indices when
the shift is minus one. Prime indices in the source start at one.

Source: https://oeis.org/A261395
Credit: @jacklarmer
-/

namespace OMA.S_oeis_a261395

/-- Shift the prime at the one-based index `i` by the integer `d`. -/
noncomputable def shiftedPrime (d : ℤ) (i : ℕ) : ℤ :=
  (Nat.nth Nat.Prime (i - 1) : ℤ) + d

def isSolution (d : ℤ) (triple : ℕ × ℕ × ℕ) : Prop :=
  let (p, q, r) := triple
  p.Prime ∧ q.Prime ∧ r.Prime ∧ p ≠ q ∧ p ≠ r ∧ q ≠ r ∧
    shiftedPrime d p ^ 2 = shiftedPrime d q * shiftedPrime d r

theorem main : ∀ d : ℤ, d ≠ 0 → {triple | isSolution d triple}.Infinite := by
  sorry

end OMA.S_oeis_a261395
