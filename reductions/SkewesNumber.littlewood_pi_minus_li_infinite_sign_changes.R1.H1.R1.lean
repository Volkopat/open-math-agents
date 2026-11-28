import OMAReductions.R_SkewesNumber_littlewood_pi_minus_li_infinite_sign_changes_R1
import Mathlib

/-!
# Reduction `SkewesNumber.littlewood_pi_minus_li_infinite_sign_changes.R1.H1`

`H1` of the parent reduction is Littlewood's two-sided oscillation estimate for `pi x - li x`,
stated for every real `X` as: above `X` there is a point where `li` exceeds `pi` by more than
`1`, and above `X` there is a point where `pi` exceeds `li` by more than `1`. The two
existential statements are about the same two functions but are independent of each other —
one is a lower bound for `li - pi` at some large argument, the other an upper bound — and the
parent statement is exactly their conjunction, so it splits into two closed propositions.

Nothing in either half constrains the other: a proof that the difference takes a value below
`-1` arbitrarily far out says nothing about values above `+1`.
-/

open Real

namespace OMA.R_SkewesNumber_littlewood_pi_minus_li_infinite_sign_changes_R1_H1_R1

/-- Infinitely often, `li x > pi x + 1`. -/
def H1 : Prop :=
  ∀ X : ℝ, ∃ x ≥ X, logIntegral x + 1 < (Nat.primeCounting ⌊x⌋₊ : ℝ)

/-- Infinitely often, `pi x > li x + 1`. -/
def H2 : Prop :=
  ∀ X : ℝ, ∃ x ≥ X, (Nat.primeCounting ⌊x⌋₊ : ℝ) + 1 < logIntegral x

theorem main : H1 → H2 →
    OMA.R_SkewesNumber_littlewood_pi_minus_li_infinite_sign_changes_R1.H1 := by
  intro h1 h2
  unfold OMA.R_SkewesNumber_littlewood_pi_minus_li_infinite_sign_changes_R1.H1
  intro X
  exact ⟨h1 X, h2 X⟩

end OMA.R_SkewesNumber_littlewood_pi_minus_li_infinite_sign_changes_R1_H1_R1
