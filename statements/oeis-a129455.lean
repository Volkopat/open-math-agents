import Mathlib

/-!
# Generalized binomial coefficients for gcd products

Source: https://oeis.org/A129455
Credit: @Iraeeee
-/

namespace OMA.S_oeis_a129455

/-- Each coordinate encodes one of the integers 1,...,n. -/
def tupleGCD {r n : ℕ} (v : Fin r → Fin n) : ℕ :=
  Finset.univ.gcd (fun i => (v i).val+1)

def table (r n : ℕ) : ℕ := ∏ v : Fin r → Fin n, tupleGCD v

/- Clearing the positive denominators expresses integrality and the perfect-power refinement together. -/
theorem main : ∀ n k : ℕ, k ≤ n → ∃ z : ℕ,
    table 3 n = (table 3 (n-k)*table 3 k*n.choose k)*z^6 := by
  sorry

end OMA.S_oeis_a129455
