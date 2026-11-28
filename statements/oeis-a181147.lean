import Mathlib

/-!
# A181147: a(n) = Sum_{k=0..n-1} (105k+44)*C(2k,k)^2*T(k)*(-1)^(n-1-k)/(2n*C(2n,n)), where T(k) (k=0,1,2,...) are central trinomial coefficients given by A002426.

Source: https://oeis.org/A181147
Credit: @azmiozgen

Conjectures (Zhi-Wei Sun, Jan 22 2011, from the entry): a(n) is a positive integer for every
n = 1, 2, 3, ...; and for any prime p > 3, a(p) == 5 + 6*(p/3)*(2-3^(p-1)) (mod p^2). (A further
conjecture of the entry, on Sum_{k<p} (-1)^k C(2k,k)^2 T(k) mod p^2, is not stated here.)

Formalization notes:
* T(k) = Sum_{j} C(k,2j) C(2j,j) is the central trinomial coefficient (A002426).
* a(n), offset 1, is defined in ℚ by the formula in the name. (p/3) is the Legendre symbol,
  `jacobiSym p 3`.
* Controls (computed): a(1..5) = 11, 23, 224, 1747, 16754, as in the entry; a(n) is a positive integer
  for n < 80.
-/

namespace OMA.S_oeis_a181147

/-- The central trinomial coefficient `T(k)` (A002426): the coefficient of `x^k` in `(x^2 + x + 1)^k`. -/
def T (k : ℕ) : ℕ := ∑ j ∈ Finset.range (k / 2 + 1), k.choose (2 * j) * (2 * j).choose j

/-- A181147(n), in `ℚ`. -/
noncomputable def a (n : ℕ) : ℚ :=
  (∑ k ∈ Finset.range n, ((105 * k + 44) * ((2 * k).choose k) ^ 2 * T k : ℕ) * (-1 : ℚ) ^ (n - 1 - k)) /
    (2 * n * ((2 * n).choose n : ℚ))

/-- The conjecture of the entry (the parts listed above). -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → ∃ m : ℕ, 0 < m ∧ a n = m) ∧
      ∀ p : ℕ, p.Prime → 3 < p → ∃ z : ℤ, a p = z ∧
        ((p : ℤ) ^ 2 ∣ z - (5 + 6 * jacobiSym p 3 * (2 - 3 ^ (p - 1)))) := by
  sorry

end OMA.S_oeis_a181147
