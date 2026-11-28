import Mathlib

/-!
# The two affine branches of a dyadic coupling

The source draws a uniform Y on [0,1]. On the layer (r,2r] with r=2⁻⁽ⁿ⁺¹⁾
its two branches start at zero, take midpoint values 1/2−r and 1/2+r, and
finish at one. The conditional distribution gives each branch weight 1/2.

Parameterize each half-layer by t in [0,1], starting at its outside endpoint.
On the lower half the unordered pair of outcomes is (low n*t, high n*t).
On the upper half the pair is their reflection about 1/2. Each half-layer has
uniform mass r/2. Countably many shared endpoints have zero source mass.
Thus `certain A` is the probability that both outcomes are in A and
`marginal A` is the probability that the outcome selected by the coin is in A.

For the stated zero-indexed dyadic layers the largest layer has a flat branch
on each half. This gives an atom at each endpoint. The positive-Lebesgue
criterion below also explains what happens on all sufficiently fine layers.

Source: thibault_student, https://mathoverflow.net/questions/487278
(CC BY-SA 4.0). Credit: @connoranderson (agent: Codex).
-/

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace OMA.S_mo_487278

abbrev I := Icc (0 : ℝ) 1

noncomputable def gap (n : ℕ) : ℝ := (1 / 2 : ℝ)^(n+1)
noncomputable def low (n : ℕ) : ℝ := 1/2 - gap n
noncomputable def high (n : ℕ) : ℝ := 1/2 + gap n
noncomputable def weight (n : ℕ) : ℝ≥0∞ := ENNReal.ofReal (gap n / 2)
def reflect (A : Set ℝ) : Set ℝ := (fun x => 1-x) ⁻¹' A

noncomputable def oneBranch (A : Set ℝ) (c : ℝ) : ℝ≥0∞ :=
  volume {t | t ∈ I ∧ c*t ∈ A}
noncomputable def bothBranch (A : Set ℝ) (n : ℕ) : ℝ≥0∞ :=
  volume {t | t ∈ I ∧ low n*t ∈ A ∧ high n*t ∈ A}

noncomputable def certain (A : Set ℝ) : ℝ≥0∞ :=
  ∑' n, weight n * (bothBranch A n + bothBranch (reflect A) n)

noncomputable def marginal (A : Set ℝ) : ℝ≥0∞ :=
  ∑' n, (weight n / 2) *
    (oneBranch A (low n) + oneBranch A (high n) +
      oneBranch (reflect A) (low n) + oneBranch (reflect A) (high n))

theorem main :
    (certain univ = 1 ∧ marginal univ = 1) ∧
    (marginal {0} = 1/8 ∧ marginal {1} = 1/8 ∧ certain {0} = 0 ∧ certain {1} = 0) ∧
    ∀ A : Set ℝ, MeasurableSet A →
      (0 < certain A ↔ 0 < volume (A ∩ I)) ∧
      (0 < marginal A ↔ 0 < volume (A ∩ I) ∨ 0 ∈ A ∨ 1 ∈ A) ∧
      (0 < volume (A ∩ I) ↔ ∀ᶠ n in atTop, 0 < bothBranch A n + bothBranch (reflect A) n) := by
  sorry
end OMA.S_mo_487278
