import Mathlib

/-!
# A357559: a(n) = Sum_{k = 0..n} (-1)^(n+k)*k^3*binomial(n,k)*binomial(n+k,k)^2.

Source: https://oeis.org/A357559
Credit: @azmiozgen

Conjecture (formula section): 3*a(2*n) == 0 ( mod n^2*(2*n + 1)^3 ).

Formalization notes:
* a(n) is the sum in the name (offset 0), computed in ℤ.
* The congruence is stated for every n ≥ 1 as divisibility of 3*a(2n) by n^2 (2n+1)^3.
* Controls (computed): a(0..4) = 0, 4, 270, 8448, 192000, as in the entry; the divisibility
  holds for n = 1..11.
-/

namespace OMA.S_oeis_a357559

/-- A357559(n) = ∑_{k=0}^{n} (-1)^(n+k) k^3 C(n,k) C(n+k,k)^2. -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n + k) * (k ^ 3 * n.choose k * ((n + k).choose k) ^ 2 : ℕ)

/-- `n^2 (2n+1)^3` divides `3 a(2n)` for every `n ≥ 1`. -/
theorem main :
    ∀ n : ℕ, 1 ≤ n → ((n : ℤ) ^ 2 * (2 * n + 1) ^ 3 ∣ 3 * a (2 * n)) := by
  sorry

end OMA.S_oeis_a357559
