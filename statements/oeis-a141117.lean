import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Substitution

namespace OMA.S_oeis_a141117

open PowerSeries

/-- OEIS A141117 Conjecture: let `G(x), A(x) ∈ ℤ[[x]]` be formal power series with zero constant
term satisfying `G(x) = x + x * G(G(G(x)))` (g.f. of A091713) and `A(x) = G(G(x))`.
Then `[x^1] A(x) = 1`, and for all `n > 1`, `4 ∣ [x^n] A(x)` if and only if `3 ∣ n`, and
otherwise `[x^n] A(x) ≡ 2 (mod 4)`. -/
theorem main :
    ∀ G A : PowerSeries ℤ,
      G.constantCoeff = 0 →
      G = PowerSeries.X + PowerSeries.X * G.subst (G.subst G) →
      A = G.subst G →
      PowerSeries.coeff 1 A = 1 ∧
      ∀ n : ℕ, 1 < n →
        (3 ∣ n → PowerSeries.coeff n A % 4 = 0) ∧
        (¬ (3 ∣ n) → PowerSeries.coeff n A % 4 = 2) := by
  sorry

end OMA.S_oeis_a141117
