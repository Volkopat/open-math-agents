import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Int.ModEq

namespace OMA.S_oeis_a374570

/-- Formal power series composition `(F ∘ G)(x) = ∑_{k≥0} [x^k] F * G(x)^k`
(exact whenever `[x^0] G = 0`). -/
noncomputable def psComp (F G : PowerSeries ℤ) : PowerSeries ℤ :=
  PowerSeries.mk fun n =>
    ∑ k ∈ Finset.range (n + 1), PowerSeries.coeff k F * PowerSeries.coeff n (G ^ k)

/-- `IsCatalanX C` asserts that `C(x) = ∑_{n≥1} C_{n-1} x^n` is the shifted Catalan g.f.
satisfying `[x^0] C = 0` and `C(x) = x + C(x)^2`. -/
def IsCatalanX (C : PowerSeries ℤ) : Prop :=
  PowerSeries.coeff 0 C = 0 ∧ C = PowerSeries.X + C ^ 2

/-- `IsA374570 A` asserts that `A(x) = ∑_{n≥1} a(n) x^n` is the g.f. of OEIS A374570,
satisfying `[x^0] A = 0`, `[x^1] A = 1`, and `A(x)^2 = A(A(x) * C(x))`. -/
def IsA374570 (A : PowerSeries ℤ) : Prop :=
  PowerSeries.coeff 0 A = 0 ∧
  PowerSeries.coeff 1 A = 1 ∧
  ∃ C : PowerSeries ℤ, IsCatalanX C ∧ A ^ 2 = psComp A (A * C)

/-- Conjecture on OEIS A374570:
for all `n > 1`, `a(n)` is odd iff `n = 2^k + 1` for some `k : ℕ`. -/
theorem main :
    ∀ A : PowerSeries ℤ, IsA374570 A →
      ∀ n : ℕ, 1 < n →
        (PowerSeries.coeff n A % 2 = 1 ↔ ∃ k : ℕ, n = 2 ^ k + 1) := by
  sorry

end OMA.S_oeis_a374570
