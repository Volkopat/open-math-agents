import Mathlib

/-!
# A178790: The arithmetic mean of (2*k+1)*A_k (k=0,...,n-1), where A_0,A_1,... are Apery numbers given by A005259.

Source: https://oeis.org/A178790
Credit: @azmiozgen

Conjectures (Zhi-Wei Sun, from the entry):
1. a(n) = n^(-1)*Sum_{k=0..n-1}(2*k+1)*A_k is always an integer.
2. If p = 5,7 (mod 8) is a prime then Sum_{k=0}^{p-1} A_k == 0 (mod p^2); if p = 1,3 (mod 8) is a
   prime greater than 3 and p = x^2 + 2y^2 with x, y integers then
   Sum_{k=0}^{p-1} A_k == 4x^2 - 2p (mod p^2).

Formalization notes:
* A_k = Sum_{j=0..k} binomial(k,j)^2 * binomial(k+j,j)^2 (A005259).
* Conjecture 1 is stated as: n divides Sum_{k=0..n-1} (2k+1) A_k, for every n ≥ 1.
* Conjecture 2 is stated in ℤ for every prime p as in the entry; in the second case it is
  stated for every representation p = x^2 + 2y^2.
* Controls (computed): a(1..7) = 1, 8, 127, 2624, 61501, 1552760, 41186755, as in the entry;
  conjecture 1 holds for n < 60 and conjecture 2 for primes 5 ≤ p < 80.
-/

namespace OMA.S_oeis_a178790

/-- The Apéry numbers A005259. -/
def apery (k : ℕ) : ℕ := ∑ j ∈ Finset.range (k + 1), (k.choose j) ^ 2 * ((k + j).choose j) ^ 2

/-- Both conjectures of the entry. -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → n ∣ ∑ k ∈ Finset.range n, (2 * k + 1) * apery k) ∧
      ∀ p : ℕ, p.Prime →
        ((p % 8 = 5 ∨ p % 8 = 7) → p ^ 2 ∣ ∑ k ∈ Finset.range p, apery k) ∧
        ((p % 8 = 1 ∨ p % 8 = 3) → 3 < p → ∀ x y : ℤ, (p : ℤ) = x ^ 2 + 2 * y ^ 2 →
          (p : ℤ) ^ 2 ∣ (∑ k ∈ Finset.range p, (apery k : ℤ)) - (4 * x ^ 2 - 2 * p)) := by
  sorry

end OMA.S_oeis_a178790
