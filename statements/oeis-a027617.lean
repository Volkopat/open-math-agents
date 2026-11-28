import Mathlib

/-!
# A027617: two conjectured recurrences

Source: https://oeis.org/A027617
Credit: @ivillar

Status: recorded in the entry as conjectures; no proof or verification is noted there. Both statements
follow from the closed form of the entry, which is used as the definition here.

A027617 (offset 0): number of permutations of n elements containing a 3-cycle;
data 0, 0, 0, 2, 8, 40, 200, 1400, 11200, 103040, 1030400, 11334400, 135766400, ...

Conjectures from Stéphane Rézel, Dec 11 2019:
(1) a(n) = n*a(n-1), for n > 3 and n !== 0 (mod 3);
(2) for k > 1, a(3*k) = a(3*k-1)*S(k)/S(k-1) where S(k) = 3*k*S(k-1) - (-1)^k with S(1) = 1.

Formalization: the entry records the closed form a(n) = n! * (1 - Sum_{k=0..floor(n/3)} (-1)^k/(3^k * k!)),
and this formula (with values in ℚ) is the definition of a(n) used here. S is defined by the stated
recurrence; S(0) = 0 is the value for which the recurrence at k = 1 gives S(1) = 1, and only S(k) with
k ≥ 1 occurs in `main`. `main` is the conjunction of (1) and (2). Checked on the data, for example
a(4) = 8 = 4 * 2, and a(6) = 200 = a(5)*S(2)/S(1) = 40 * 5 / 1.
-/

namespace OMA.S_oeis_a027617

/-- a(n) = n! * (1 - Sum_{k=0..floor(n/3)} (-1)^k / (3^k * k!)), the closed form recorded in the entry. -/
def a (n : ℕ) : ℚ :=
  (n.factorial : ℚ) *
    (1 - ∑ k ∈ Finset.range (n / 3 + 1), (-1 : ℚ) ^ k / (3 ^ k * (k.factorial : ℚ)))

/-- S(k) = 3*k*S(k-1) - (-1)^k with S(1) = 1 (and S(0) = 0). -/
def S : ℕ → ℚ
  | 0 => 0
  | (k + 1) => 3 * ((k : ℚ) + 1) * S k - (-1) ^ (k + 1)

/-- The two conjectured recurrences of A027617. -/
theorem main : (∀ n : ℕ, 3 < n → n % 3 ≠ 0 → a n = (n : ℚ) * a (n - 1)) ∧
    (∀ k : ℕ, 1 < k → a (3 * k) = a (3 * k - 1) * S k / S (k - 1)) := by
  sorry

end OMA.S_oeis_a027617
