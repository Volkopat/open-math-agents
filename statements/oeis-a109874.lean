import Mathlib

/-!
# A109874: Largest exponent e such that n^e that divides A001142(n).

Source: https://oeis.org/A109874
Credit: @agchua

Comment of A109874 (the entry is by Amarnath Murthy, Jul 10 2005):
  Conjectures: (1) If n is even and n = 2^r*m, m odd and >1, then a(n)= n-r-1. (2) If n = 2^r
  then a(n) = n-3. (3) If n is odd and composite then a(n) = n-2.
A001142(n) = Product_{k=0..n} binomial(n, k), as in the comment of Joerg Arndt (Jun 04 2022) and
the entry's Mathematica and PARI programs. The sequence has offset 2, so the three claims are
stated together for n >= 2; composite means not prime (and n >= 2). For n >= 2 every e with n^e
dividing the positive number A001142(n) has e < n^e <= A001142(n), so the largest such e is
Nat.findGreatest with the bound A001142(n). The differences n-r-1, n-3, n-2 are taken in the
integers.
-/

namespace OMA.S_oeis_a109874

/-- A001142(n) = Product_{k=0..n} binomial(n, k). -/
def P (n : ℕ) : ℕ := ∏ k ∈ Finset.range (n + 1), n.choose k

/-- A109874(n): the largest exponent e such that n^e divides A001142(n). -/
def a (n : ℕ) : ℕ := Nat.findGreatest (fun e => n ^ e ∣ P n) (P n)

/-- The three conjectures of the comment, for n >= 2. -/
theorem main :
    (∀ n r m : ℕ, 2 ≤ n → Even n → n = 2 ^ r * m → Odd m → 1 < m → (a n : ℤ) = n - r - 1) ∧
    (∀ n r : ℕ, 2 ≤ n → n = 2 ^ r → (a n : ℤ) = n - 3) ∧
    (∀ n : ℕ, 2 ≤ n → Odd n → ¬ n.Prime → (a n : ℤ) = n - 2) := by
  sorry

end OMA.S_oeis_a109874