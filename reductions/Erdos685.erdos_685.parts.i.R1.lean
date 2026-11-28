import FormalConjectures.ErdosProblems.«685»

/-! Reduction of part (i) into a two-sided estimate:
    H1 is the upper bound and H2 is the lower bound, both uniform in k.
    The absolute-value bound in the target is exactly the conjunction of
    these two one-sided bounds after subtracting the common main term. -/

open Filter
open scoped ArithmeticFunction.omega
open Erdos685

namespace OMA.R_Erdos685_erdos_685_parts_i_R1

def H1 : Prop :=
  ∀ ε > (0 : ℝ), ∀ δ > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ k : ℕ,
    (n : ℝ) ^ ε < (k : ℝ) → (k : ℝ) ≤ (n : ℝ) ^ (1 - ε) →
      (ω (n.choose k) : ℝ) ≤ (1 + δ) * ((k : ℝ) * primeRecipSum k n)

def H2 : Prop :=
  ∀ ε > (0 : ℝ), ∀ δ > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ k : ℕ,
    (n : ℝ) ^ ε < (k : ℝ) → (k : ℝ) ≤ (n : ℝ) ^ (1 - ε) →
      (1 - δ) * ((k : ℝ) * primeRecipSum k n) ≤ (ω (n.choose k) : ℝ)

theorem main : H1 → H2 → type_of% @Erdos685.erdos_685.parts.i := by
  intro h1 h2 ε hε δ hδ
  filter_upwards [h1 ε hε δ hδ, h2 ε hε δ hδ] with n hu hl
  intro k hk hk2
  rw [abs_le]
  constructor
  · have hl' := hl k hk hk2
    linarith
  · have hu' := hu k hk hk2
    linarith

end OMA.R_Erdos685_erdos_685_parts_i_R1
