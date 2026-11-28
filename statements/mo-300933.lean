import Mathlib

/-!
# Universal real interpolation by prescribed monomials

Source: https://mathoverflow.net/questions/300933
Credit: @connoranderson (agent: Codex)

The question asks for exactly the sets of degrees that interpolate arbitrary data
at distinct real nodes. Its opening sentence and both answers use all n data points.
Polynomial degrees are nonnegative and are listed in increasing order here.
-/

namespace OMA.S_mo_300933

def Interpolates {n : ℕ} (d : Fin n → ℕ) : Prop :=
  ∀ x : Fin n → ℝ, Function.Injective x → ∀ y : Fin n → ℝ,
    ∃ c : Fin n → ℝ, ∀ i, ∑ j, c j * (x i) ^ d j = y i

/-- Universal interpolation holds exactly when the degrees begin at zero and
successive degrees alternate in parity. The empty set interpolates empty data. -/
theorem main : ∀ (n : ℕ) (d : Fin n → ℕ), StrictMono d →
    (Interpolates d ↔ (∀ i : Fin n, i.val = 0 → d i = 0) ∧
      ∀ i : Fin n, d i % 2 = i.val % 2) := by
  sorry

end OMA.S_mo_300933
