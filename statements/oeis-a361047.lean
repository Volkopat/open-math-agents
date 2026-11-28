import Mathlib

/-!
# OEIS A361047: Expansion of `A(x) = Series_Reversion(x - x^3 * A'(x)^2)`

Source: https://oeis.org/A361047 (OEIS Foundation, CC BY-SA 4.0).
Here `A(x) = ∑_{n ≥ 0} a(n) * x^(2*n + 1)` is the odd formal power series satisfying
`A(x - x^3 * A'(x)^2) = x` (with `A(0) = 0`, `A'(0) = 1`), where `A'(x)` is the formal derivative
of `A(x)`.

Conjecture (Paul D. Hanna, OEIS A361047):
For every `n ≥ 0`:
- `a(n) ≡ 1 (mod 3)` if `n = (3^k - 1) / 2` for some `k ≥ 0`,
- `a(n) ≡ 0 (mod 3)` otherwise.
Equivalently, writing `a(n) = [x^(2*n + 1)] A(x)`, `a(n) % 3 = if ∃ k : ℕ, 2 * n + 1 = 3 ^ k then 1 else 0`.
-/

namespace OMA.S_oeis_a361047

/-- Formal derivative of a power series `A(x) = ∑ c_m x^m`: `(derivPS A).coeff m = (m + 1) * A.coeff (m + 1)`. -/
noncomputable def derivPS (A : PowerSeries ℤ) : PowerSeries ℤ :=
  PowerSeries.mk fun m => ((m + 1 : ℕ) : ℤ) * A.coeff (m + 1)

/-- Formal substitution `F(G(x))` for `G` with `G.coeff 0 = 0`, defined coefficientwise by
`[x^n] F(G(x)) = ∑_{m=0}^n F.coeff m * (G ^ m).coeff n`. -/
noncomputable def compPS (F G : PowerSeries ℤ) : PowerSeries ℤ :=
  PowerSeries.mk fun n => ∑ m ∈ Finset.range (n + 1), F.coeff m * (G ^ m).coeff n

/-- Functional equation for OEIS A361047:
`A(0) = 0`, `A'(0) = 1`, and `A(x - x^3 * A'(x)^2) = x`. -/
def SatisfiesA361047 (A : PowerSeries ℤ) : Prop :=
  A.coeff 0 = 0 ∧
  A.coeff 1 = 1 ∧
  compPS A (PowerSeries.X - PowerSeries.X ^ 3 * (derivPS A) ^ 2) = PowerSeries.X

/-- Conjecture (OEIS A361047):
There exists a formal power series `A` satisfying `SatisfiesA361047 A`, and for every such `A`,
setting `a(n) = A.coeff (2 * n + 1)`:
- for every `n : ℕ`, `a(n) % 3 = 1 ↔ ∃ k : ℕ, n = (3 ^ k - 1) / 2`, and
- for every `n : ℕ`, `(¬ ∃ k : ℕ, n = (3 ^ k - 1) / 2) → a(n) % 3 = 0`. -/
theorem main :
    (∃ A : PowerSeries ℤ, SatisfiesA361047 A) ∧
    (∀ A : PowerSeries ℤ, SatisfiesA361047 A →
      ∀ n : ℕ,
        (A.coeff (2 * n + 1) % 3 = 1 ↔ ∃ k : ℕ, n = (3 ^ k - 1) / 2) ∧
        ((¬ ∃ k : ℕ, n = (3 ^ k - 1) / 2) → A.coeff (2 * n + 1) % 3 = 0)) := by
  sorry

end OMA.S_oeis_a361047
