import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.PowerSeries.Basic

namespace OMA.S_oeis_a202943

/-- OEIS A000695 (Moser–de Bruijn numbers): nonnegative integers whose binary expansion
has no `1` bits in odd positions (equivalently, sums of distinct powers of `4`). -/
def IsMoserDeBruijn (m : ℕ) : Prop :=
  ∀ k : ℕ, (m / 2 ^ (2 * k + 1)) % 2 = 0

/-- The base power series `F(x) = ∑_{n ≥ 0} ((n+1)(n+2)/2) * 2^(n*(n-1)) * x^n` over `ℤ`. -/
noncomputable def F202943 : PowerSeries ℤ :=
  PowerSeries.mk fun n => (((n + 1) * (n + 2) / 2 : ℕ) : ℤ) * (2 : ℤ) ^ (n * (n - 1))

open Classical in
/-- Conjecture (Paul D. Hanna; OEIS A202943): For the integer power series `A(x) ∈ ℤ⟦x⟧`
with `A(0) = 1` and `A(x)^3 = ∑_{n ≥ 0} ((n+1)(n+2)/2) * 2^(n*(n-1)) * x^n`, the
characteristic series of `A(x) mod 2` equals
`(1 + x) * (1 + x^2) * (1 + x^8) * ∑_{m ∈ A000695} x^(32*m)` in `(ZMod 2)⟦x⟧`. -/
theorem main :
    ∀ A : PowerSeries ℤ,
      PowerSeries.constantCoeff A = 1 →
      A ^ 3 = F202943 →
      PowerSeries.map (Int.castRingHom (ZMod 2)) A =
        (1 + PowerSeries.X) * (1 + PowerSeries.X ^ 2) * (1 + PowerSeries.X ^ 8) *
          PowerSeries.mk (fun n =>
            if ∃ m : ℕ, IsMoserDeBruijn m ∧ n = 32 * m then (1 : ZMod 2) else 0) := by
  sorry

end OMA.S_oeis_a202943
