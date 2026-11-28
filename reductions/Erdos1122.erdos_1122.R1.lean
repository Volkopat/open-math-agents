import FormalConjectures.ErdosProblems.«1122»
/-! Erdős 1122 split into Erdős's 1946 theorem and a monotonicity statement.

Erdős (1946) proved that a nondecreasing additive function is a multiple of the logarithm (H1).
So the problem is equivalent to showing that an additive function whose set of descents
`{n | f (n + 1) < f n}` has density zero has no descents at all (H2). H2 is necessary: if
`f = c * log` with density-zero descents then `c ≥ 0`, and then `f` is nondecreasing.
This is a classical case, not progress on the conjecture. -/
namespace OMA.R_Erdos1122_erdos_1122_R1
open Filter

/-- Erdős (1946): a nondecreasing additive function is `c * log n`. -/
def H1 : Prop := ∀ f : ℕ → ℝ,
    (∀ᵉ (a > 0) (b > 0), a.Coprime b → f (a * b) = f a + f b) →
    (∀ n ≥ 1, f n ≤ f (n + 1)) →
    ∃ c : ℝ, ∀ n > 0, f n = c * Real.log n

/-- The open core: density-zero descents force no descents. -/
def H2 : Prop := ∀ f : ℕ → ℝ,
    (∀ᵉ (a > 0) (b > 0), a.Coprime b → f (a * b) = f a + f b) →
    {n | 1 ≤ n ∧ f (n + 1) < f n}.HasDensity 0 →
    ∀ n ≥ 1, f n ≤ f (n + 1)

theorem main : H1 → H2 → type_of% @Erdos1122.erdos_1122 := by
  intro h₁ h₂ f hf hd
  exact h₁ f hf (h₂ f hf hd)

end OMA.R_Erdos1122_erdos_1122_R1
