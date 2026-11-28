import Mathlib

/-!
# The second-order oscillation of a nonlinear recurrence

Source: https://mathoverflow.net/questions/429627. For an arbitrary positive
initial value, compare the observed correction with a nonconstant sinusoid of
the logarithm of the index.
-/
namespace OMA.S_mo_429627
open Filter Topology

/-- Index zero stores the source's first term and its first partial sum. -/
noncomputable def state (a : ℝ) : ℕ → ℝ × ℝ
  | 0 => (a, a)
  | k+1 =>
    let v := state a k
    let next := v.1 + ((k:ℝ)+1)/v.2
    (next, v.2 + next)

noncomputable def correction (a : ℝ) (k : ℕ) : ℝ :=
  ((k:ℝ)+1)*Real.sqrt 3 - (state a k).1*Real.sqrt ((k:ℝ)+1)

noncomputable def phase (k : ℕ) : ℂ :=
  Complex.exp (Complex.I * ((Real.log ((k:ℝ)+1) / Real.sqrt 2 : ℝ) : ℂ))

noncomputable def idx (k : ℕ) : ℝ := (k:ℝ)+1
noncomputable def D (a : ℝ) (k : ℕ) : ℝ := (state a k).1^2 - 3*idx k + 3/2
noncomputable def Y (a : ℝ) (k : ℕ) : ℝ :=
  (state a k).1*(state a k).2/idx k - 2*idx k + 1/2
noncomputable def u (a : ℝ) (k : ℕ) := D a k - Y a k
noncomputable def z (a : ℝ) (k : ℕ) : ℂ := ⟨u a k, Y a k / Real.sqrt 2⟩
def bounded (a : ℝ) := ∃ R : ℝ, ∀ᶠ k in atTop, ‖z a k‖ ≤ R

theorem main : ∀ a : ℝ, 0 < a → ∃ w : ℂ, w ≠ 0 ∧
    Tendsto (fun k => correction a k - (Real.sqrt 3 / 4 + (w * phase k).re))
      atTop (𝓝 0) := by
  sorry

end OMA.S_mo_429627
