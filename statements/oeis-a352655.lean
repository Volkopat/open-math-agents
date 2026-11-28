import Mathlib

/-!
# A352655: a(n) = (1/2)*(A005258(n) + A005258(n-1)).

Source: https://oeis.org/A352655
Credit: @azmiozgen

Conjectures (Peter Bala, from the entry): a(p) == 2 (mod p^5) for primes p >= 5; and for r >= 2
and all primes p >= 5, a(p^r) == a(p^(r-1)) (mod p^(3*r+3)).

Formalization notes:
* A005258(n) = Sum_{k=0..n} binomial(n,k)^2 * binomial(n+k,k) (Apéry numbers); a(n), offset 1,
  is defined in ℚ; its values are integers.
* "x == y (mod p^m)" for these values is stated as: x - y = p^m * z for an integer z.
* Controls (computed): a(1..6) = 2, 11, 83, 699, 6252, 58106, as in the entry; a(p) ≡ 2 (mod p^5)
  for p = 5, 7, 11, and a(25) ≡ a(5) (mod 5^9).
-/

namespace OMA.S_oeis_a352655

/-- The Apéry numbers A005258(n) = ∑_{k=0}^{n} C(n,k)^2 C(n+k,k). -/
def apery (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), (n.choose k) ^ 2 * (n + k).choose k

/-- A352655(n) = (A005258(n) + A005258(n-1)) / 2. -/
noncomputable def a (n : ℕ) : ℚ := ((apery n : ℚ) + apery (n - 1)) / 2

/-- Both conjectures of the entry. -/
theorem main :
    (∀ p : ℕ, p.Prime → 5 ≤ p → ∃ z : ℤ, a p - 2 = (p : ℚ) ^ 5 * z) ∧
      ∀ p r : ℕ, p.Prime → 5 ≤ p → 2 ≤ r →
        ∃ z : ℤ, a (p ^ r) - a (p ^ (r - 1)) = (p : ℚ) ^ (3 * r + 3) * z := by
  sorry

end OMA.S_oeis_a352655
