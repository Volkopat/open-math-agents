import Mathlib

/-!
# A249541: Numbers m such that phi(m-2) divides m-1 where phi is Euler's totient function (A000010).

Source: https://oeis.org/A249541
Credit: @azmiozgen

Conjecture (from the entry, see A203966): 4 is the only number m such that 3*phi(m-2) = m-1.

Formalization notes:
* m ranges over m ≥ 3 (the sequence starts at 3). For m = 1, Mathlib's truncated subtraction
  and `Nat.totient 0 = 0` would make 3*phi(m-2) = m-1 hold formally (0 = 0); this degenerate case
  is excluded.
* Stated as: for m ≥ 3, 3*phi(m-2) = m-1 if and only if m = 4.
* Controls (computed): among 3 ≤ m < 200000, only m = 4 satisfies 3*phi(m-2) = m-1.
-/

namespace OMA.S_oeis_a249541

/-- `m = 4` is the only `m ≥ 3` with `3 φ(m-2) = m-1`. -/
theorem main : ∀ m : ℕ, 3 ≤ m → (3 * Nat.totient (m - 2) = m - 1 ↔ m = 4) := by
  sorry

end OMA.S_oeis_a249541
