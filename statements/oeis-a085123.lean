import Mathlib

/-!
# A085123: Smallest 7-smooth number whose base-10 digital product is the n-th 7-smooth number

Source: https://oeis.org/A085123

Conjecture (OEIS A085123):
No entry of A085123 is zero; equivalently, for every 7-smooth number `m` (A002473),
there exists a 7-smooth number `k` whose base-10 digital product equals `m`.

Conventions:
- Offset: `1`; first terms of A002473: `1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 18, 20, ...`.
- First terms of A085123: `1, 2, 3, 4, 5, 6, 7, 8, 9, 25, 126, 27, 35, 28, 36, 45, ...`.
  For instance, `a(16) = 45` because `A002473(16) = 20 = 4 * 5` and `45` is 7-smooth.
-/

namespace OMA.S_oeis_a085123

/-- Predicate stating that `m ≥ 1` is 7-smooth (OEIS A002473). -/
def IsSevenSmooth (m : ℕ) : Prop :=
  1 ≤ m ∧ ∀ p : ℕ, Nat.Prime p → p ∣ m → p ≤ 7

/-- Product of the base-10 digits of `n : ℕ`. -/
def digitProd (n : ℕ) : ℕ :=
  (Nat.digits 10 n).prod

/-- Conjecture: every 7-smooth number is the base-10 digital product of some 7-smooth number. -/
theorem main :
    ∀ m : ℕ, IsSevenSmooth m → ∃ k : ℕ, IsSevenSmooth k ∧ digitProd k = m := by
  sorry

end OMA.S_oeis_a085123
