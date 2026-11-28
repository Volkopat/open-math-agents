import Mathlib

/-!
# Generalized binomial coefficients for gcd products

Source: https://oeis.org/A129453
Credit: @Iraeeee
-/

namespace OMA.S_oeis_a129453

/-- Each coordinate encodes one of the integers 1,...,n. -/
def tupleGCD {r n : ℕ} (v : Fin r → Fin n) : ℕ :=
  Finset.univ.gcd (fun i => (v i).val+1)

def table (r n : ℕ) : ℕ := ∏ v : Fin r → Fin n, tupleGCD v

/- Clearing the positive denominators expresses integrality and the perfect-power refinement together. -/
theorem main : ∀ n k : ℕ, k ≤ n → ∃ z : ℕ,
    table 2 n = (table 2 (n-k)*table 2 k*n.choose k)*z^2 := by
  sorry

end OMA.S_oeis_a129453
