import Mathlib

/-!
# A178808: a(n) = (1/n^2) * Sum_{k = 0..n-1} (2*k+1)*(D_k)^2, where D_0, D_1, ... are central Delannoy numbers given by A001850.

Source: https://oeis.org/A178808
Credit: @azmiozgen

Conjectures (Zhi-Wei Sun, Jun 14 2010, from the entry): a(n) is always an integer, and
p^2*a(p) = p^2 - 4*p^3*q_p(2) - 2*p^4*q_p(2)^2 (mod p^5) for any prime p > 3, where q_p(2) is the
Fermat quotient (2^(p-1) - 1)/p. (A further conjecture of the entry, about the alternating sum,
is not stated here.)

Formalization notes:
* D_k = Sum_{j=0..k} binomial(k,j) * binomial(k+j,j) (central Delannoy numbers, A001850).
* With S(n) = Sum_{k=0..n-1} (2k+1) D_k^2 we have n^2 a(n) = S(n), so the first conjecture is
  n^2 | S(n) for n ≥ 1 and the second is S(p) == p^2 - 4p^3 q - 2p^4 q^2 (mod p^5), in ℤ.
* Controls (computed): a(1..7) = 1, 7, 97, 1791, 38241, 892039, 22092673, as in the entry; the
  first conjecture holds for n < 60, the second for primes 5 ≤ p < 60.
-/

namespace OMA.S_oeis_a178808

/-- The central Delannoy numbers A001850. -/
def delannoy (k : ℕ) : ℕ := ∑ j ∈ Finset.range (k + 1), k.choose j * (k + j).choose j

/-- `S(n) = ∑_{k<n} (2k+1) D_k^2`, so that `a(n) = S(n) / n^2`. -/
def S (n : ℕ) : ℕ := ∑ k ∈ Finset.range n, (2 * k + 1) * delannoy k ^ 2

/-- Sun's two conjectures. -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → n ^ 2 ∣ S n) ∧
      ∀ p : ℕ, p.Prime → 3 < p →
        let q : ℤ := ((2 ^ (p - 1) - 1) / p : ℕ)
        (p : ℤ) ^ 5 ∣ (S p : ℤ) - (p ^ 2 - 4 * p ^ 3 * q - 2 * p ^ 4 * q ^ 2) := by
  sorry

end OMA.S_oeis_a178808
