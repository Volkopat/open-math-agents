import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Int.ModEq

namespace OMA.S_oeis_a247031

/-- Conjecture on OEIS A247031 (and A245658):
for any formal power series `A, B ∈ ℤ[[x]]` such that `A = B^3` (i.e. `A` is the self-convolution
cube of `B`), `a(3*n) ≡ 2 (mod 3)` if and only if `b(n) ≡ 2 (mod 3)` for every `n ≥ 0`. -/
theorem main :
    ∀ A B : PowerSeries ℤ, A = B ^ 3 →
      ∀ n : ℕ, PowerSeries.coeff (3 * n) A ≡ 2 [ZMOD 3] ↔ PowerSeries.coeff n B ≡ 2 [ZMOD 3] := by
  sorry

end OMA.S_oeis_a247031
