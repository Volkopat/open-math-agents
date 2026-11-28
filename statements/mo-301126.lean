import Mathlib

/-!
# An exact finite test for three bounded moments

Source: Sihuang Hu, https://mathoverflow.net/questions/301126 (CC BY-SA 4.0).
Credit: @connoranderson.

For a fixed sample size the maximum third moment occurs at a vector consisting
of upper endpoints, a repeated lower value, and one exceptional value. The
first two moments determine both values for each candidate multiplicity.
-/

namespace OMA.S_mo_301126

def candidate (m r : ℕ) (a₁ a₂ a₃ : ℝ) : Prop :=
  let u : ℝ := 1/4
  let z : ℝ := (m-1-r : ℕ)
  let s := a₁-z*u
  let q := a₂-z*u^2
  let d := Real.sqrt (((r+1 : ℝ)*q-s^2)/r)
  let l := (s-d)/(r+1)
  let v := (s+r*d)/(r+1)
  0 ≤ l ∧ l ≤ v ∧ v ≤ u ∧
    r*l+v+z*u = a₁ ∧ r*l^2+v^2+z*u^2 = a₂ ∧ a₃ ≤ r*l^3+v^3+z*u^3

theorem main : ∀ (m : ℕ) (_ : 0 < m) (a₁ a₂ a₃ : ℝ),
    0 < a₁ → 0 < a₂ → 0 < a₃ →
    ((∃ x : Fin m → ℝ, (∀ i, x i ∈ Set.Icc 0 (1/4 : ℝ)) ∧
      (∑ i, x i) = a₁ ∧ (∑ i, (x i)^2) = a₂ ∧ a₃ ≤ ∑ i, (x i)^3) ↔
      ∃ r : Fin m, candidate m r.val a₁ a₂ a₃) := by
  sorry

end OMA.S_mo_301126
