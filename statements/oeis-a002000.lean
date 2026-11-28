import Mathlib

/-!
# A002000: a(n+1) = a(n)*(a(n)^2 - 3) with a(0) = 7

Source: https://oeis.org/A002000
Credit: @jagong-cmu

Formalizes Peter Bala's OEIS A002000 conjecture (Nov 15 2022), offset 0:
`Conjecture: a(n+1) == a(n) (mod 3^(n+r+2)) for n >= r.`

Conventions:
* The sequence follows the OEIS definition `a(0) = 7`, `a(n+1) = a(n)*(a(n)^2 - 3)`.
  It takes values in `ℤ`, so the subtraction `a(n)^2 - 3` is the usual one (all terms are positive).
* `r` ranges over the natural numbers (`r >= 0`), and the claim is stated for every pair `n >= r`.
* The congruence is written with `Int.ModEq`.
-/

namespace OMA.S_oeis_a002000

/-- `a(0) = 7`, `a(n+1) = a(n)*(a(n)^2 - 3)`. -/
def a : ℕ → ℤ
  | 0 => 7
  | n + 1 => a n * (a n ^ 2 - 3)

/-- For all `n >= r >= 0`: `a(n+1) ≡ a(n) (mod 3^(n+r+2))`. -/
theorem main : ∀ n r : ℕ, r ≤ n → a (n + 1) ≡ a n [ZMOD 3 ^ (n + r + 2)] := by
  sorry

end OMA.S_oeis_a002000
