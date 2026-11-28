import Mathlib

/-!
# A165968: Mathar's recurrence

Source: https://oeis.org/A165968
Credit: @ivillar

Status: false as stated at n = 3 with the present offset 1: a(3) + 2*(-3+1)*a(2) + 2*(-3+2)*a(1) =
2 - 4 - 0 = -2. The entry notes (Sergey Kirgizov, Jun 03 2022) that Mathar's recurrence is the
recurrence of Gary Detlefs, a(n) = (2*n-4)*a(n-1) + (2*n-6)*a(n-2) for n > 2, with the index shifted
by one, and that the latter is correct because a(n)*(2n-2) satisfies the recurrence of A053871.
With the data the shift is b(n) = a(n+1): Mathar's recurrence holds for the sequence read with
offset 0. `main` is the corrected recurrence (Mathar's recurrence for b(n) = a(n+1), n ≥ 2), so it
is a known result.

A165968 (offset 1): number of pairings disjoint to a given pairing, and containing a given pair not
in the given pairing; data 0, 1, 2, 10, 68, 604, 6584, 85048, 1269680, 21505552, 407414816, ...

Conjecture (R. J. Mathar, Nov 15 2012): a(n) +2*(-n+1)*a(n-1) +2*(-n+2)*a(n-2)=0.

Formalization: the entry gives the inclusion-exclusion formula
a(n) = (2n-3)!! - C(n-2,1) * (2n-5)!! + ... with alternating signs down to the last term 1, that is
(as in the Mathematica program of the entry) a(n) = Sum_{k=0..n-2} (-1)^(n-k-2) * C(n-2,k) * (2k+1)!!, with a(1) = 0 (empty sum). This is
the definition of a(n) used here; the sign is written (-1)^(n+k), which equals (-1)^(n-k-2).
-/

namespace OMA.S_oeis_a165968

/-- a(n) = Sum_{k=0..n-2} (-1)^(n-k-2) C(n-2,k) (2k+1)!!, with a(n) = 0 for n < 2. -/
def a (n : ℕ) : ℤ :=
  if n < 2 then 0
  else ∑ k ∈ Finset.range (n - 1),
    (-1 : ℤ) ^ (n + k) * ((n - 2).choose k : ℤ) * (Nat.doubleFactorial (2 * k + 1) : ℤ)

/-- Mathar's recurrence for b(n) = a(n+1), n ≥ 2. -/
theorem main : ∀ n : ℕ, 2 ≤ n →
    a (n + 1) + 2 * (-(n : ℤ) + 1) * a n + 2 * (-(n : ℤ) + 2) * a (n - 1) = 0 := by
  sorry

end OMA.S_oeis_a165968
