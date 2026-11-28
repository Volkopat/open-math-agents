import Mathlib

/-!
# A constructive inverse for conditional expectation in a uniform-interval coupling

Write a source point as y = n + t with n a natural number and 0 ≤ t ≤ 1.
Integer endpoints are null. The function ρ n t is the density of the arbitrary
source law equivalent to Lebesgue measure on the positive half-line.
Conditional on y, X is uniform on the unit interval intersected with the closed
ball about t of radius 2⁻ⁿ. The function `marginal` is its marginal density.
Thus an integrable target f is represented by the integrable density F = f m.

At each stage, `firstScale` takes the least unused dyadic scale above all
earlier scales on which averaging reduces the L¹ error by the specified
factor q. The lifting formula corrects the residual on that layer by the
interval length and the source density. Its input norm is at most
‖f‖₁/(1−q), while every preimage has norm at least ‖f‖₁.

Source: thibault_student, https://mathoverflow.net/questions/503875
(CC BY-SA 4.0). The author gives a nonconstructive surjectivity proof and asks
for a construction. The first-scale iteration supplies that construction.
Credit: @connoranderson (agent: Codex).
-/


open MeasureTheory Set Filter
open scoped Topology BigOperators
namespace OMA.S_mo_503875

noncomputable def unitVol : Measure ℝ := volume.restrict (Icc 0 1)

noncomputable def width (n : ℕ) : ℝ := (1 / 2 : ℝ)^n

noncomputable def lengthAt (n : ℕ) (t : ℝ) : ℝ :=
  unitVol.real (Metric.closedBall t (width n))

noncomputable def box (n : ℕ) (h : ℝ → ℝ) (x : ℝ) : ℝ :=
  (2 * width n)⁻¹ * ∫ t in Metric.closedBall x (width n), h t ∂unitVol

noncomputable def cost (h : ℝ → ℝ) : ℝ := ∫ t, |h t| ∂unitVol

/-- The first fresh scale achieving the requested reduction in the residual. -/
noncomputable def firstScale (q : ℝ) (lo : ℕ) (h : ℝ → ℝ) : ℕ :=
  sInf {n : ℕ | lo ≤ n ∧ cost (fun x => h x - box n h x) ≤ q * cost h}

/-- The pair stores the next available scale and the current residual density. -/
noncomputable def iteration (q : ℝ) (F : ℝ → ℝ) : ℕ → ℕ × (ℝ → ℝ)
  | 0 => (0, F)
  | j + 1 =>
    let p := iteration q F j
    let n := firstScale q p.1 p.2
    (n + 1, fun x => p.2 x - box n p.2 x)

noncomputable def scale (q : ℝ) (F : ℝ → ℝ) (j : ℕ) : ℕ :=
  firstScale q (iteration q F j).1 (iteration q F j).2

noncomputable def residual (q : ℝ) (F : ℝ → ℝ) (j : ℕ) : ℝ → ℝ :=
  (iteration q F j).2

/-- The contribution to the output density from one source layer. -/
noncomputable def spread (n : ℕ) (h : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ t in Metric.closedBall x (width n), h t / lengthAt n t ∂unitVol

/-- Density of the first marginal when the source density at n+t is ρ n t. -/
noncomputable def marginal (ρ : ℕ → ℝ → ℝ) (x : ℝ) : ℝ := ∑' n, spread n (ρ n) x

/-- The lifting formula on the selected scales, extended by zero on every skipped layer. -/
noncomputable def lift (q : ℝ) (F : ℝ → ℝ) (ρ : ℕ → ℝ → ℝ) : ℕ → ℝ → ℝ :=
  Function.extend (scale q F) (fun j t =>
    residual q F j t * lengthAt (scale q F j) t / (2 * width (scale q F j) * ρ (scale q F j) t))
    (fun _ _ => 0)

def SourceLaw (ρ : ℕ → ℝ → ℝ) : Prop :=
  (∀ n, Integrable (ρ n) unitVol) ∧ (∀ n, ∀ᵐ t ∂unitVol, 0 < ρ n t) ∧
  HasSum (fun n => ∫ t, ρ n t ∂unitVol) 1

/-- Integrability on the source and the density form of the conditional expectation identity. -/
def Preimage (ρ g : ℕ → ℝ → ℝ) (f : ℝ → ℝ) : Prop :=
  (∀ n, Integrable (fun t => g n t * ρ n t) unitVol) ∧
  Summable (fun n => cost (fun t => g n t * ρ n t)) ∧
  ∀ᵐ x ∂unitVol, HasSum (fun n => spread n (fun t => g n t * ρ n t) x)
    (f x * marginal ρ x)

noncomputable def inputNorm (ρ g : ℕ → ℝ → ℝ) : ℝ :=
  ∑' n, cost (fun t => g n t * ρ n t)

theorem main : ∀ (ρ : ℕ → ℝ → ℝ) (hρ : SourceLaw ρ) (f : ℝ → ℝ)
    (hf : Integrable (fun x => f x * marginal ρ x) unitVol) (q : ℝ) (hq : 0 < q) (hq1 : q < 1),
    let F := fun x => f x * marginal ρ x
    let g := lift q F ρ
    (Integrable (marginal ρ) unitVol ∧ (∫ x, marginal ρ x ∂unitVol) = 1 ∧
      ∀ᵐ x ∂unitVol, 0 < marginal ρ x) ∧
    StrictMono (scale q F) ∧ (∀ j, cost (residual q F j) ≤ q^j * cost F) ∧
    Preimage ρ g f ∧ inputNorm ρ g ≤ cost F / (1-q) ∧
    (∀ᵐ x ∂unitVol, (∑' n, spread n (fun t => g n t * ρ n t) x) / marginal ρ x = f x) ∧
    ∀ other, Preimage ρ other f → cost F ≤ inputNorm ρ other := by
  sorry
end OMA.S_mo_503875
