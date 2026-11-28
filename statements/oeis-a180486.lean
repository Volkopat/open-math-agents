import Mathlib

/-!
# A180486: Numbers of the form ceiling(A179896(j)/A018252(j)) where A179896(j) mod A018252(j) <> 0.

Source: https://oeis.org/A180486
Credit: @Salofe

The conjectures, quoted from the FORMULA section of the entry:

  Conjectures from Colin Barker, Nov 25 2019: (Start)
  G.f.: x*(5 - 2*x) / (1 - x)^2.
  a(n) = 2*a(n-1) - a(n-2) for n>2.
  a(n) = 2 + 3*n.
  (End)

Formalization notes:
* Offset 1 for A180486, A179896 and A018252, as in the three OEIS entries.
* A018252 is "The nonprime numbers: 1 together with the composite numbers": 1, 4, 6, 8, 9, ...
  `A018252 j` (j ≥ 1) is the j-th natural number k ≥ 1 that is not prime, i.e.
  `Nat.nth (fun k => 1 ≤ k ∧ ¬ k.Prime) (j - 1)` (`Nat.nth` counts from 0).
* A179896 is "Sum of the numbers between k := n-th nonprime and 2k": the integers strictly
  between k and 2k, i.e. the sum over `Finset.Ioo k (2 * k)`. This matches its data:
  A179896(1) = 0 (k = 1), A179896(2) = 5 + 6 + 7 = 18 (k = 4), A179896(3) = 7 + ... + 11 = 45 (k = 6).
* The ceiling is that of the exact rational quotient A179896(j)/A018252(j) (`Nat.ceil` in ℚ;
  the quotient is nonnegative), and the condition is `A179896 j % A018252 j ≠ 0`.
* "Numbers of the form ..." is the set `S` of these values over all j ≥ 1, and A180486 lists
  `S` in increasing order: `a n = Nat.nth (· ∈ S) (n - 1)` for n ≥ 1. (These values increase
  with j, so listing them by j instead, as in the entry's previous name, gives the same terms.)
* `series` is the generating function sum_{n ≥ 1} a(n) x^n over ℚ (coefficient 0 at x^0, as the
  offset is 1). The g.f. claim is stated multiplied by its denominator: (1 - x)^2 is a unit of
  ℚ[[x]], so `(1 - X) ^ 2 * series = X * (5 - 2 * X)` says exactly that
  `series = x*(5 - 2*x) / (1 - x)^2`.
* The recurrence is stated in ℤ, for every n > 2 as in the entry; the closed form is stated
  for every n ≥ 1.
-/

namespace OMA.S_oeis_a180486

/-- A018252 (offset 1): the nonprime numbers 1, 4, 6, 8, 9, ... -/
noncomputable def A018252 (j : ℕ) : ℕ := Nat.nth (fun k => 1 ≤ k ∧ ¬ k.Prime) (j - 1)

/-- A179896 (offset 1): the sum of the numbers strictly between k = A018252(j) and 2k. -/
noncomputable def A179896 (j : ℕ) : ℕ := ∑ i ∈ Finset.Ioo (A018252 j) (2 * A018252 j), i

/-- The numbers of the form ceiling(A179896(j)/A018252(j)) with A179896(j) mod A018252(j) ≠ 0,
for j ≥ 1. -/
def S : Set ℕ :=
  {v | ∃ j : ℕ, 1 ≤ j ∧ A179896 j % A018252 j ≠ 0 ∧
    v = ⌈(A179896 j : ℚ) / (A018252 j : ℚ)⌉₊}

/-- A180486 (offset 1): the elements of `S` in increasing order. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth (· ∈ S) (n - 1)

/-- The ordinary generating function sum_{n ≥ 1} a(n) x^n. -/
noncomputable def series : PowerSeries ℚ :=
  PowerSeries.mk (fun n => if n = 0 then 0 else (a n : ℚ))

open PowerSeries in
theorem main :
    (1 - X) ^ 2 * series = X * (5 - 2 * X) ∧
    (∀ n : ℕ, 2 < n → (a n : ℤ) = 2 * a (n - 1) - a (n - 2)) ∧
    (∀ n : ℕ, 1 ≤ n → a n = 2 + 3 * n) := by
  sorry

end OMA.S_oeis_a180486
