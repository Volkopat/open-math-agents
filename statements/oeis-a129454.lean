import Mathlib

/-!
# Valuations of the triple gcd product A129454

Source: https://oeis.org/A129454
Credit: @Iraeeee
-/

namespace OMA.S_oeis_a129454

/-- Each coordinate encodes one of the integers 1,...,n. -/
def tupleGCD {r n : ℕ} (v : Fin r → Fin n) : ℕ :=
  Finset.univ.gcd (fun i => (v i).val+1)

def table (r n : ℕ) : ℕ := ∏ v : Fin r → Fin n, tupleGCD v

/- A129454 at index n is the three-dimensional table on the integers 1,...,n−1.
The proposed formula uses n in its numerator. Terms with i>n vanish, so the displayed finite sum equals the source series. -/
theorem main : ∀ n p : ℕ, p.Prime →
    (table 3 (n-1)).factorization p = ∑ i ∈ Finset.Ico 1 (n+1), (n/p^i)^3 := by
  sorry

end OMA.S_oeis_a129454
