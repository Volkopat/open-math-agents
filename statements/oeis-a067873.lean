import Mathlib

/-!
# OEIS A067873: Even Solutions to Multiple Pell Equations x^2 - D y^2 = 1

Source: https://oeis.org/A067873
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Consider positive integers $x \ge 2$ satisfying $x^2 - D y^2 = 1$ (with $D, y \ge 1$)
for more than one value of $D$ distinct from $x^2 - 1$.

Conjecture: Every even term $e$ of this sequence satisfies
$$\Omega(e^2 - 1) - \omega(e^2 - 1) > 2,$$
where $\Omega(E)$ is the number of prime factors of $E$ counted with multiplicity
and $\omega(E)$ is the number of distinct prime factors of $E$.
-/

namespace OMA.S_oeis_a067873

/-- `InA067873 x` holds when `x ≥ 2` satisfies `x^2 - D * y^2 = 1` for at least two
distinct positive integers `D₁ ≠ D₂`, both distinct from `x^2 - 1`. -/
def InA067873 (x : ℕ) : Prop :=
  2 ≤ x ∧
    ∃ D₁ D₂ y₁ y₂ : ℕ,
      1 ≤ D₁ ∧ 1 ≤ D₂ ∧ 1 ≤ y₁ ∧ 1 ≤ y₂ ∧
      D₁ ≠ D₂ ∧ D₁ ≠ x ^ 2 - 1 ∧ D₂ ≠ x ^ 2 - 1 ∧
      x ^ 2 = D₁ * y₁ ^ 2 + 1 ∧ x ^ 2 = D₂ * y₂ ^ 2 + 1

/-- Number of prime factors counted with multiplicity (`Ω`). -/
def bigOmega (n : ℕ) : ℕ :=
  n.primeFactorsList.length

/-- Number of distinct prime factors (`ω`). -/
def littleOmega (n : ℕ) : ℕ :=
  n.primeFactors.card

theorem main :
    ∀ e : ℕ, InA067873 e → Even e →
      2 < bigOmega (e ^ 2 - 1) - littleOmega (e ^ 2 - 1) := by
  sorry

end OMA.S_oeis_a067873
