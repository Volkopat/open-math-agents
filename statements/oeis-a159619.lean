import Mathlib

/-!
# A159619: Slowest increasing sequence beginning with 4 such that n and a(n) are either both evil or both odious.

Source: https://oeis.org/A159619
Credit: @agchua

Comment of A159619 (the entry is by Vladimir Shevelev, 2009):
  There is a conjecture arising in Sequence Machine that a(n) = A026491(2+n)-1. This appears to
  be true: ... - R. J. Mathar, Jun 24 2021
This file states the conjecture as printed, with the entries' offsets: A159619 has offset 1 and
A026491 has offset 0, so it is stated for every n ≥ 1. As printed it fails at n = 1: a(1) = 4,
while A026491(3) - 1 = 8 - 1 = 7. The shifted form a(n) = A026491(n+1) - 1 fits all listed terms
of both entries (and was checked for n ≤ 5000).

A159619: a number is evil if its binary expansion has an even number of 1's and odious
otherwise; `ones m` is the number of 1's among the binary digits of m. The slowest increasing
sequence beginning with 4 has a(1) = 4 and, for n ≥ 1, a(n+1) = the least m > a(n) such that m
and n+1 are both evil or both odious. (The value a(0) is outside the offset and set to 0.)

The referenced sequences, by their own entries' definitions:
* A026491 (offset 0): a(0) = 1 (the first listed term) and a(n) = least k > a(n-1) such that
  A001285(k-1) = A001285(n-1), for n ≥ 1.
* A001285 (offset 0), the Thue-Morse sequence: let A_k denote the first 2^k terms; then A_0 = 1
  and A_{k+1} = A_k B_k, where B_k is obtained from A_k by interchanging 1's and 2's (x -> 3 - x).
  Term n is term n of A_n, which has 2^n > n terms.
-/

namespace OMA.S_oeis_a159619

/-- The number of 1's in the binary expansion of m. -/
def ones (m : ℕ) : ℕ := (Nat.digits 2 m).count 1

/-- A159619(n), n ≥ 1. -/
noncomputable def a : ℕ → ℕ
  | 0 => 0
  | 1 => 4
  | n + 2 => sInf {m : ℕ | a (n + 1) < m ∧ ones m % 2 = ones (n + 2) % 2}

/-- A_k: the first 2^k terms of the Thue-Morse sequence A001285. -/
def thueBlock : ℕ → List ℕ
  | 0 => [1]
  | k + 1 => thueBlock k ++ (thueBlock k).map (fun x => 3 - x)

/-- A001285(n), n ≥ 0. -/
def a001285 (n : ℕ) : ℕ := (thueBlock n).getD n 0

/-- A026491(n), n ≥ 0. -/
noncomputable def a026491 : ℕ → ℕ
  | 0 => 1
  | n + 1 => sInf {k : ℕ | a026491 n < k ∧ a001285 (k - 1) = a001285 n}

/-- The conjecture as printed: a(n) = A026491(2+n) - 1 for n ≥ 1. -/
theorem main : ∀ n : ℕ, 1 ≤ n → (a n : ℤ) = (a026491 (2 + n) : ℤ) - 1 := by
  sorry

end OMA.S_oeis_a159619
