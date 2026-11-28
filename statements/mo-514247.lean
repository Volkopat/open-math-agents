import Mathlib

/-!
# Gaussian sums with bounded coefficients depending on the whole sample

The coefficients in the source may depend measurably on every Gaussian coordinate.
The largest possible two-sided tail is exactly the tail of C times the sum of
the absolute coordinates. A single centered example attains every threshold,
even with all coefficients zero at the origin. We give an explicit exponential
upper bound and show that centered examples have constant probability of a
deviation proportional to the dimension.

Source: Hao Yu, https://mathoverflow.net/questions/514247 (CC BY-SA 4.0).
Credit: @connoranderson (agent: Codex)
-/

namespace OMA.S_mo_514247
open ProbabilityTheory MeasureTheory
abbrev Sample (n : ℕ) := Fin (n+1) → ℝ
abbrev Coeff (n : ℕ) := Fin (n+1) → Sample n → ℝ
noncomputable def law (n : ℕ) : Measure (Sample n) := Measure.pi fun _ => gaussianReal 0 1
def bounded {n} (C : ℝ) (Y : Coeff n) : Prop := ∀ i,Measurable (Y i) ∧ ∀ x, |Y i x|≤C
def total {n} (Y : Coeff n) (x : Sample n) : ℝ := ∑ i,x i*Y i x
def radius {n} (x : Sample n) : ℝ := ∑ i,|x i|
noncomputable def tail {n} (f : Sample n → ℝ) (t : ℝ) := (law n).real {x | t≤|f x|}

theorem main :
    (∀ (n : ℕ) (C : ℝ), 0<C → ∀ (Y : Coeff n), bounded C Y → ∀ t : ℝ, 0<t →
      tail (total Y) t ≤ tail (fun x : Sample n => C*radius x) t ∧
      tail (total Y) t ≤ (2:ℝ)^(n+1)*Real.exp (-(t^2)/(2*(n+1:ℝ)*C^2))) ∧
    (∃ c : ℝ, 0<c ∧ ∀ (n : ℕ) (C : ℝ), 0<C → ∃ Y : Coeff n,
      bounded C Y ∧ (∀ i,Y i 0=0) ∧ Integrable (total Y) (law n) ∧
      (∫ x,total Y x ∂law n)=0 ∧ (∀ t,tail (total Y) t=tail (fun x : Sample n => C*radius x) t) ∧
      c ≤ tail (total Y) (c*C*(n+1:ℝ))) := by
  sorry
end OMA.S_mo_514247
