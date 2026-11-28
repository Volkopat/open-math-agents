import Mathlib

/-!
# A203529: a(n) = A203527(n)/A000178(n-1); A000178 = (superfactorials).

Source: https://oeis.org/A203529
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A203529 (Clark Kimberling, Jan 03 2012): every term is
an integer.

Conventions:
* The sequence has offset 1 (data 1, 5, 175, 44100, 60913125, 427756329000, 20552836095792000,
  6952965728817588480000, 11895516181976215338950400000, 99606443887767729350960121600000000,
  5830034964946921746536425070101217280000000, ...).
* c(i) is the i-th term of the nonprime numbers (A018252: 1, 4, 6, 8, 9, ...), i.e. the positive
  integers that are not prime; with the 0-indexed `Nat.nth`, c(i) is `Nat.nth` of the predicate at
  i - 1.
* A203527(n) = Product_{1 <= i < j <= n} (c(i) + c(j)) is the helper `v n`; A000178(m) =
  Product_{k=0..m} k! is the superfactorial, the helper `sf m`.
* a(n) = A203527(n)/A000178(n-1), so `every term is an integer` is the divisibility of v(n) by
  sf(n-1), for every n >= 1 (the offset); n - 1 is then an exact subtraction.
-/

namespace OMA.S_oeis_a203529

/-- c(i), the i-th term (i >= 1) of the sequence of numbers m with 0 < m and not m prime. -/
noncomputable def c (i : ℕ) : ℕ := Nat.nth (fun m : ℕ => 0 < m ∧ ¬m.Prime) (i - 1)

/-- A203527(n) = Product_{1 <= i < j <= n} (c(i) + c(j)). -/
noncomputable def v (n : ℕ) : ℕ := ∏ j ∈ Finset.Icc 1 n, ∏ i ∈ Finset.Ico 1 j, (c i + c j)

/-- The superfactorial A000178(m) = Product_{k=0..m} k!. -/
def sf (m : ℕ) : ℕ := ∏ k ∈ Finset.range (m + 1), Nat.factorial k

/-- The conjecture recorded in A203529: A203527(n)/A000178(n-1) is an integer for every n >= 1. -/
theorem main : ∀ n : ℕ, 1 ≤ n → sf (n - 1) ∣ v n := by
  sorry

end OMA.S_oeis_a203529
