import Mathlib

namespace OMA.S_arxiv_2609_13765

/-- A real-valued function `f` on a real inner product space `E` is convex and `1`-smooth
with gradient `g` (`f ∈ F_{0,1}`). -/
def IsSmoothConvex {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (g : E → E) : Prop :=
  ConvexOn ℝ Set.univ f ∧
  (∀ x : E, HasFDerivAt f (innerSL ℝ (g x)) x) ∧
  LipschitzWith 1 g

/-- Gradient descent trajectory `x_{k+1} = x_k - h_k g(x_k)` along a schedule `h`. -/
def IsGDTrajectory {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : E → E) (h : List ℝ) (x : ℕ → E) : Prop :=
  ∀ (k : ℕ) (hk : k < h.length), x (k + 1) = x k - h[k] • g (x k)

/-- A positive stepsize schedule `h` is `s`-composable with rate `η`
(Definition 1 of arXiv:2609.13765 / Definition 3 of Grimmer–Shu–Wang 2025). -/
def IsSComposable (h : List ℝ) (eta : ℝ) : Prop :=
  (∀ s ∈ h, 0 < s) ∧
  eta = (1 + h.sum)⁻¹ ∧
  eta = (h.map (fun s => s - 1)).prod ∧
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (g : E → E) (x_star : E) (x : ℕ → E),
    IsSmoothConvex f g →
    (∀ y : E, f x_star ≤ f y) →
    IsGDTrajectory g h x →
    ((1 - eta) / 2) * ‖g (x h.length)‖ ^ 2 +
      (eta ^ 2 / 2) * ‖x h.length - x_star‖ ^ 2 +
      eta * (1 - eta) * (f (x h.length) - f x_star) ≤
      (eta ^ 2 / 2) * ‖x 0 - x_star‖ ^ 2

/-- Proximal point relation `z ∈ prox_{λ F}(x)`. -/
def IsProx {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (F : E → ℝ) (lam : ℝ) (x z : E) : Prop :=
  ∀ y : E, F z + (1 / (2 * lam)) * ‖z - x‖ ^ 2 ≤ F y + (1 / (2 * lam)) * ‖y - x‖ ^ 2

/-- Relaxed proximal point trajectory `z_k = prox_{λ F}(x_k)`,
`x_{k+1} = x_k + h_k (z_k - x_k)` along a schedule `h`. -/
def IsProxTrajectory {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (F : E → ℝ) (lam : ℝ) (h : List ℝ) (x z : ℕ → E) : Prop :=
  (∀ k : ℕ, k ≤ h.length → IsProx F lam (x k) (z k)) ∧
  (∀ (k : ℕ) (hk : k < h.length), x (k + 1) = x k + h[k] • (z k - x k))

/-- Silver ratio `ρ = 1 + √2`. -/
noncomputable def silverRatio : ℝ := 1 + Real.sqrt 2

/-- Original silver stepsize schedule of length `2^m - 1` (Altschuler–Parrilo 2025). -/
noncomputable def silverSchedule : ℕ → List ℝ
  | 0 => []
  | m + 1 => silverSchedule m ++ [1 + silverRatio ^ m * (Real.sqrt 2 - 1)] ++ silverSchedule m

/-- Exact last-iterate proximal objective-gap constant for every positive `s`-composable
schedule and for the original silver schedule (Theorems 1 and 4 of arXiv:2609.13765):
1. For any positive `s`-composable schedule `h` with rate `η` and any `λ > 0`,
   the sharp worst-case terminal proximal objective gap is `η ‖x_0 - x_*‖^2 / (4 λ)`,
   attained by a one-dimensional convex function.
2. For every `m ≥ 1`, the original silver schedule `silverSchedule m` of length `2^m - 1`
   is `s`-composable with rate `ρ^{-m}` (`ρ = 1 + √2`), and its exact worst-case terminal
   proximal objective gap is `‖x_0 - x_*‖^2 / (4 λ ρ^m)`, attained in one dimension. -/
theorem main :
    (∀ (h : List ℝ) (eta lam : ℝ),
      IsSComposable h eta → 0 < lam →
      (∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        (F : E → ℝ) (x_star : E) (x z : ℕ → E),
        ConvexOn ℝ Set.univ F →
        (∀ y : E, F x_star ≤ F y) →
        IsProxTrajectory F lam h x z →
        F (z h.length) - F x_star ≤ eta * ‖x 0 - x_star‖ ^ 2 / (4 * lam)) ∧
      (∀ R : ℝ, 0 < R →
        ∃ (F : ℝ → ℝ) (x_star : ℝ) (x z : ℕ → ℝ),
          ConvexOn ℝ Set.univ F ∧
          (∀ y : ℝ, F x_star ≤ F y) ∧
          IsProxTrajectory F lam h x z ∧
          ‖x 0 - x_star‖ = R ∧
          F (z h.length) - F x_star = eta * R ^ 2 / (4 * lam))) ∧
    (∀ (m : ℕ) (lam : ℝ),
      1 ≤ m → 0 < lam →
      (silverSchedule m).length = 2 ^ m - 1 ∧
      IsSComposable (silverSchedule m) (silverRatio ^ m)⁻¹ ∧
      (∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        (F : E → ℝ) (x_star : E) (x z : ℕ → E),
        ConvexOn ℝ Set.univ F →
        (∀ y : E, F x_star ≤ F y) →
        IsProxTrajectory F lam (silverSchedule m) x z →
        F (z (silverSchedule m).length) - F x_star ≤
          ‖x 0 - x_star‖ ^ 2 / (4 * lam * silverRatio ^ m)) ∧
      (∀ R : ℝ, 0 < R →
        ∃ (F : ℝ → ℝ) (x_star : ℝ) (x z : ℕ → ℝ),
          ConvexOn ℝ Set.univ F ∧
          (∀ y : ℝ, F x_star ≤ F y) ∧
          IsProxTrajectory F lam (silverSchedule m) x z ∧
          ‖x 0 - x_star‖ = R ∧
          F (z (silverSchedule m).length) - F x_star =
            R ^ 2 / (4 * lam * silverRatio ^ m))) := by sorry

end OMA.S_arxiv_2609_13765
