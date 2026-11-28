import Mathlib

/-!
# A203533: a(n) = A203530(n)/A000178(n-1); A000178 = (superfactorials).

Source: https://oeis.org/A203533
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A203533 (Clark Kimberling, Jan 03 2012): every term is
an integer.

Conventions:
* The sequence has offset 1 (data 1, 10, 840, 464100, 1481407200, 32851686067200,
  5186361382800998400, 4436556151786001058816000, 19667253420867342693731328000000,
  605862171333980479840975997239296000000, 132207384898194165523202154782408753283072000000, ...).
* c(i) is the i-th term of the composite numbers (A002808: 4, 6, 8, 9, 10, ...), i.e. the integers
  m > 1 that are not prime; with the 0-indexed `Nat.nth`, c(i) is `Nat.nth` of the predicate at i
  - 1.
* A203530(n) = Product_{1 <= i < j <= n} (c(i) + c(j)) is the helper `v n`; A000178(m) =
  Product_{k=0..m} k! is the superfactorial, the helper `sf m`.
* a(n) = A203530(n)/A000178(n-1), so `every term is an integer` is the divisibility of v(n) by
  sf(n-1), for every n >= 1 (the offset); n - 1 is then an exact subtraction.
-/

namespace OMA.S_oeis_a203533

/-- c(i), the i-th term (i >= 1) of the sequence of numbers m with 1 < m and not m prime. -/
noncomputable def c (i : ℕ) : ℕ := Nat.nth (fun m : ℕ => 1 < m ∧ ¬m.Prime) (i - 1)

/-- A203530(n) = Product_{1 <= i < j <= n} (c(i) + c(j)). -/
noncomputable def v (n : ℕ) : ℕ := ∏ j ∈ Finset.Icc 1 n, ∏ i ∈ Finset.Ico 1 j, (c i + c j)

/-- The superfactorial A000178(m) = Product_{k=0..m} k!. -/
def sf (m : ℕ) : ℕ := ∏ k ∈ Finset.range (m + 1), Nat.factorial k

/-- The conjecture recorded in A203533: A203530(n)/A000178(n-1) is an integer for every n >= 1. -/
theorem main : ∀ n : ℕ, 1 ≤ n → sf (n - 1) ∣ v n := by
  sorry

end OMA.S_oeis_a203533
