import Mathlib

/-!
# A306289: The smallest prime factor of numbers greater than 1 and coprime to 6.

Source: https://oeis.org/A306289

Comment in the entry (Davis Smith, Feb 03 2019), after listing the cases 5, 7, 11, 13, 17, 19:

  Conjecture: This pattern continues indefinitely. a(n) = A007310(m + 1) when n is congruent to
  {m, A306277(m + 1)} (mod A091999(m + 1)) but not congruent to {k, A306277(k + 1)}
  (mod A091999(k + 1)), m > k >= 1.

Translation notes (please check):
* Offset of A306289 is 1, and the entry gives a(n) = A020639(A007310(n + 1)), where A020639 is the
  least prime factor (with value 1 at 1). `Nat.minFac` is exactly A020639.
* A007310 (offset 1) = numbers congruent to 1 or 5 mod 6: 1, 5, 7, 11, 13, ... Encoded by the
  closed form 3 i - 1 (i even), 3 i - 2 (i odd). The natural-number subtraction is harmless for
  i >= 1, and only indices >= 2 are used.
* A306277 (offset 1) = numbers congruent to 1 or 8 mod 10: 1, 8, 11, 18, 21, ... Encoded by the
  closed form 5 i - 2 (i even), 5 i - 4 (i odd); again harmless for i >= 1.
* A091999 (offset 1) = numbers congruent to 2 or 10 mod 12; the entry gives a(n) = 2 * A007310(n),
  which is used as the definition.
* The phrase: n is congruent to {x, y} (mod M) is read as: n = x (mod M) or n = y (mod M), as in
  the worked cases of the entry (a(n) = 5 when n is congruent to {1, 8} (mod 10), a(n) = 7 when n
  is congruent to {2, 11} (mod 14) but not {1, 8} (mod 10), ...).
* The clause: but not congruent to ... m > k >= 1, is read as: for every k with 1 <= k < m,
  n is in neither of the two residue classes attached to k.
* n >= 1 and m >= 1 as in the source.
-/

namespace OMA.S_oeis_a306289

/-- A007310 (offset 1): numbers congruent to 1 or 5 mod 6. -/
def A007310 (i : ℕ) : ℕ := 3 * i - (if i % 2 = 0 then 1 else 2)

/-- A306277 (offset 1): numbers congruent to 1 or 8 mod 10. -/
def A306277 (i : ℕ) : ℕ := 5 * i - (if i % 2 = 0 then 2 else 4)

/-- A091999 (offset 1): numbers congruent to 2 or 10 mod 12, a(n) = 2 * A007310(n). -/
def A091999 (i : ℕ) : ℕ := 2 * A007310 i

/-- A306289 (offset 1): a(n) = A020639(A007310(n + 1)). -/
def A306289 (n : ℕ) : ℕ := Nat.minFac (A007310 (n + 1))

theorem main : ∀ n m : ℕ, 1 ≤ n → 1 ≤ m →
    (n ≡ m [MOD A091999 (m + 1)] ∨ n ≡ A306277 (m + 1) [MOD A091999 (m + 1)]) →
    (∀ k : ℕ, 1 ≤ k → k < m →
      ¬ (n ≡ k [MOD A091999 (k + 1)] ∨ n ≡ A306277 (k + 1) [MOD A091999 (k + 1)])) →
    A306289 n = A007310 (m + 1) := by
  sorry

end OMA.S_oeis_a306289
