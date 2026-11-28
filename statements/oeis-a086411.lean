import Mathlib

/-!
# A086411: Greatest prime factor of 3-smooth numbers.

Source: https://oeis.org/A086411
Credit: @bnb9001

a(n) = A006530(A003586(n)) (offset 1: 1, 2, 3, 2, 3, 2, 3, 3, ...), where A003586 lists the
3-smooth numbers 2^i * 3^j in increasing order and A006530 is the greatest prime factor, with
A006530(1) = 1.

Conjecture (R. J. Mathar, 2024): a(n) = A049237(n+1) for n > 1, where A049237 is the quotient
k/phi(k) for k in A007694, the numbers k such that phi(k) divides k (1, 2, 4, 6, 8, 12, ...).
Chai Wah Wu notes that the conjecture is true.
-/

namespace OMA.S_oeis_a086411

/-- Membership in A003586: `m = 2^i * 3^j` for some `i, j >= 0`. -/
def Is3Smooth (m : ℕ) : Prop := ∃ i j : ℕ, m = 2 ^ i * 3 ^ j

/-- A003586 (offset 1): the `n`-th 3-smooth number. -/
noncomputable def smooth3 (n : ℕ) : ℕ := Nat.nth Is3Smooth (n - 1)

/-- A006530: the greatest prime factor of `m`, with value 1 at `m = 1`. -/
def gpf (m : ℕ) : ℕ := max 1 (m.primeFactors.sup id)

/-- A086411: the greatest prime factor of the `n`-th 3-smooth number. -/
noncomputable def a (n : ℕ) : ℕ := gpf (smooth3 n)

/-- Membership in A007694: `k` is positive and `phi k` divides `k`. -/
def PhiDvd (k : ℕ) : Prop := 0 < k ∧ Nat.totient k ∣ k

/-- A007694 (offset 1). -/
noncomputable def phiDvdSeq (n : ℕ) : ℕ := Nat.nth PhiDvd (n - 1)

/-- A049237: `k / phi k` for the `n`-th term `k` of A007694. -/
noncomputable def b (n : ℕ) : ℕ := phiDvdSeq n / Nat.totient (phiDvdSeq n)

/-- Mathar's conjecture, proved: `a(n) = A049237(n+1)` for `n > 1`. -/
theorem main : ∀ n : ℕ, 1 < n → a n = b (n + 1) := by
  sorry

end OMA.S_oeis_a086411
