import OMAReductions.R_Arxiv_2607_27197_maxwell_conjecture_variants_three_equal_magnitudes_R1

namespace OMA.R_Arxiv_2607_27197_maxwell_conjecture_variants_three_equal_magnitudes_R1_H1_R1

/-- Hypothesis H1: Every equilibrium point of three equal-sign charges lies strictly in the
interior of the triangle spanned by `(0, 0)`, `(1, 0)`, and `(u, w)`. -/
def H1 : Prop :=
  ∀ (q : Fin 3 → ℝ) (u w : ℝ), w ≠ 0 → (∀ j, q j ≠ 0) → (∀ i j, q i = q j) →
    ∀ p : ℝ × ℝ,
      ((∀ j, (p.1 - ![0, 1, u] j)^2 + (p.2 - ![0, 0, w] j)^2 ≠ 0) ∧
        ∑ j, q j * (p.1 - ![0, 1, u] j) / Real.sqrt ((p.1 - ![0, 1, u] j)^2 + (p.2 - ![0, 0, w] j)^2)^3 = 0 ∧
        ∑ j, q j * (p.2 - ![0, 0, w] j) / Real.sqrt ((p.1 - ![0, 1, u] j)^2 + (p.2 - ![0, 0, w] j)^2)^3 = 0) →
      ∃ l0 l1 l2 : ℝ, 0 < l0 ∧ 0 < l1 ∧ 0 < l2 ∧ l0 + l1 + l2 = 1 ∧
        p.1 = l1 + l2 * u ∧ p.2 = l2 * w

/-- Hypothesis H2: Given that every equilibrium point lies strictly inside the open triangle
and all equilibria are non-degenerate, there are at most 4 equilibrium points. -/
def H2 : Prop :=
  ∀ (q : Fin 3 → ℝ) (u w : ℝ), w ≠ 0 → (∀ j, q j ≠ 0) → (∀ i j, q i = q j) →
    (∀ p : ℝ × ℝ, (∀ j, (p.1 - ![0, 1, u] j)^2 + (p.2 - ![0, 0, w] j)^2 ≠ 0) →
      ∑ j, q j * (p.1 - ![0, 1, u] j) / Real.sqrt ((p.1 - ![0, 1, u] j)^2 + (p.2 - ![0, 0, w] j)^2)^3 = 0 →
      ∑ j, q j * (p.2 - ![0, 0, w] j) / Real.sqrt ((p.1 - ![0, 1, u] j)^2 + (p.2 - ![0, 0, w] j)^2)^3 = 0 →
      (∑ j, q j * (2 * (p.1 - ![0, 1, u] j)^2 - (p.2 - ![0, 0, w] j)^2) / Real.sqrt ((p.1 - ![0, 1, u] j)^2 + (p.2 - ![0, 0, w] j)^2)^5) *
        (∑ j, q j * (2 * (p.2 - ![0, 0, w] j)^2 - (p.1 - ![0, 1, u] j)^2) / Real.sqrt ((p.1 - ![0, 1, u] j)^2 + (p.2 - ![0, 0, w] j)^2)^5) -
        (∑ j, q j * (3 * (p.1 - ![0, 1, u] j) * (p.2 - ![0, 0, w] j)) / Real.sqrt ((p.1 - ![0, 1, u] j)^2 + (p.2 - ![0, 0, w] j)^2)^5)^2 ≠ 0) →
    (∀ p : ℝ × ℝ,
      ((∀ j, (p.1 - ![0, 1, u] j)^2 + (p.2 - ![0, 0, w] j)^2 ≠ 0) ∧
        ∑ j, q j * (p.1 - ![0, 1, u] j) / Real.sqrt ((p.1 - ![0, 1, u] j)^2 + (p.2 - ![0, 0, w] j)^2)^3 = 0 ∧
        ∑ j, q j * (p.2 - ![0, 0, w] j) / Real.sqrt ((p.1 - ![0, 1, u] j)^2 + (p.2 - ![0, 0, w] j)^2)^3 = 0) →
      ∃ l0 l1 l2 : ℝ, 0 < l0 ∧ 0 < l1 ∧ 0 < l2 ∧ l0 + l1 + l2 = 1 ∧
        p.1 = l1 + l2 * u ∧ p.2 = l2 * w) →
    {p : ℝ × ℝ | (∀ j, (p.1 - ![0, 1, u] j)^2 + (p.2 - ![0, 0, w] j)^2 ≠ 0) ∧
      ∑ j, q j * (p.1 - ![0, 1, u] j) / Real.sqrt ((p.1 - ![0, 1, u] j)^2 + (p.2 - ![0, 0, w] j)^2)^3 = 0 ∧
      ∑ j, q j * (p.2 - ![0, 0, w] j) / Real.sqrt ((p.1 - ![0, 1, u] j)^2 + (p.2 - ![0, 0, w] j)^2)^3 = 0}.encard ≤ 4

theorem main : H1 → H2 → OMA.R_Arxiv_2607_27197_maxwell_conjecture_variants_three_equal_magnitudes_R1.H1 := by
  intro h1 h2 q u w hw hq heq hnd
  exact h2 q u w hw hq heq hnd (h1 q u w hw hq heq)

end OMA.R_Arxiv_2607_27197_maxwell_conjecture_variants_three_equal_magnitudes_R1_H1_R1
