import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Fintype.Prod

/-!
# A087412: number of solutions to x^3 + y^3 ≡ 1 (mod 3^e)

Source: https://oeis.org/A087412

`a(n)` is the number of pairs `(x, y) ∈ {0, …, n - 1}²` satisfying `x^3 + y^3 ≡ 1 (mod n)`.
Andrew Howroyd (Jul 17 2018) conjectured in OEIS A087412 that
`a(3^e) = 2 * 3^e` for all `e > 1`.
-/

namespace OMA.S_oeis_a087412

/-- `a n` is the number of solutions `(x, y)` modulo `n` to `x^3 + y^3 ≡ 1 (mod n)`. -/
def a (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin n × Fin n)).filter
    fun p => (p.1.val ^ 3 + p.2.val ^ 3) ≡ 1 [MOD n]).card

/-- Howroyd's conjecture for OEIS A087412: `a(3^e) = 2 * 3^e` for all `e > 1`. -/
theorem main : ∀ e : ℕ, 1 < e → a (3 ^ e) = 2 * 3 ^ e := by
  sorry

end OMA.S_oeis_a087412
