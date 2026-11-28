import Mathlib

/-!
# A005590: a(0) = 0, a(1) = 1, a(2n) = a(n), a(2n+1) = a(n+1) - a(n).

Source: https://oeis.org/A005590
Credit: @rabdelaal

A 2-regular divide-and-conquer sequence, the "minus" variant of Stern's diatomic
series (OEIS A005590).

OEIS A005590 records the conjecture (Ralf Stephan, 2003) that `a(3n) = 0` iff `n` is a
Fibbinary number (A003714): its binary expansion contains no two adjacent `1`s.
-/

namespace OMA.S_oeis_a005590

/-- The OEIS A005590 entry, by its divide-and-conquer recursion
`a 0 = 0`, `a 1 = 1`, `a (2n) = a n`, `a (2n+1) = a (n+1) - a n`. -/
def a : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => if Even (n + 2) then a ((n + 2) / 2) else a ((n + 1) / 2 + 1) - a ((n + 1) / 2)

/-- `n` is a Fibbinary number (A003714): no two adjacent `1` bits. -/
def IsFibbinary (n : ℕ) : Prop := Nat.land n (n / 2) = 0

/-- The conjecture recorded in OEIS A005590 (Stephan): `a(3n) = 0` iff `n` is Fibbinary. -/
theorem main : ∀ n : ℕ, a (3 * n) = 0 ↔ IsFibbinary n := by
  sorry

end OMA.S_oeis_a005590
