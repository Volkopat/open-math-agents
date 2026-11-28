import Mathlib

/-!
# A224709: The number of unordered partitions {a,b} of the even numbers 2n such that a and b are composite.

Source: https://oeis.org/A224709
Credit: @avivorly

A224709 (offset 1): the number of unordered pairs `{a, b}` with `a + b = 2n` and `a`, `b` both composite:
0, 0, 0, 1, 1, 2, 2, 3, 4, 4, 4, 6, 5, 6, 8, ... (e.g. `a(6) = 2`: `12 = 4 + 8 = 6 + 6`).

Conjecture (Anthony Browne, Jun 26 2016, in the entry): `a(3n+9) > a(3n+8)` and `a(3n+10) < a(3n+9)` for `n >= 1`.

Conventions:
- A composite number is a natural number `> 1` that is not prime (so `0` and `1` are not composite).
- An unordered pair `{a, b}` with `a + b = 2n` is counted once, by its smaller element `a ≤ n` (so `b = 2n - a ≥ n`);
  `a = b = n` is allowed (as in the entry's example `(6,6)`).
- Both inequalities are asserted for every `n ≥ 1`, as one conjunction.
-/

namespace OMA.S_oeis_a224709

/-- A natural number is composite when it is `> 1` and not prime. -/
def IsComposite (m : ℕ) : Prop := 1 < m ∧ ¬ m.Prime

instance : DecidablePred IsComposite := fun m => inferInstanceAs (Decidable (1 < m ∧ ¬ m.Prime))

/-- A224709: the number of unordered pairs `{a, 2n - a}` (`1 ≤ a ≤ n`) with both parts composite. -/
def a (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).filter (fun x => IsComposite x ∧ IsComposite (2 * n - x))).card

theorem main : ∀ n : ℕ, 1 ≤ n → a (3 * n + 9) > a (3 * n + 8) ∧ a (3 * n + 10) < a (3 * n + 9) := by
  sorry

end OMA.S_oeis_a224709
