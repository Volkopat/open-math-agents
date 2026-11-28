import Mathlib

/-!
# Eden's conjecture

Source: https://en.wikipedia.org/wiki/Eden's_conjecture
Credit: @MarcoPacheco05

Wikipedia: Eden's conjecture states that the supremum of the local Lyapunov dimensions on the
global attractor is achieved on a stationary point or an unstable periodic orbit embedded into
the attractor (A. Eden, 1987/1989).

Setting and conventions (the source gives no explicit class of systems; we take the standard
setting of Eden and of Kuznetsov–Reitmann, *Attractor Dimension Estimates for Dynamical Systems*,
Springer 2021):
* the dynamical system is the flow `φ` of an autonomous ODE `x' = f x` on `ℝⁿ` with `f` of class
  `C¹`, assumed globally defined (`φ 0 = id`, `φ (s + t) = φ s ∘ φ t`, `∂ₜ φ t x = f (φ t x)`);
* `K` is a global attractor: compact, invariant (`φ t '' K = K` for `t ≥ 0`) and uniformly
  attracting every bounded set;
* finite-time Lyapunov exponents: `LEᵢ(t, x) = (1 / t) log σᵢ(D φᵗ(x))`, where the `σᵢ` are the
  singular values of the derivative, i.e. square roots of the eigenvalues of `Aᵀ A`
  (they are positive since `D φᵗ(x)` is invertible);
* Kaplan–Yorke dimension of a family `λ₁, …, λₙ`, written without sorting:
  with `S m` = sum of the `m` largest `λᵢ`, `d_KY = sup {d ∈ [0, n] | S ⌊d⌋ + (d - ⌊d⌋) λ_{⌊d⌋+1} ≥ 0}`;
* local Lyapunov dimension: `dim_L(x) = limsup_{t → +∞} d_KY(LE₁(t, x), …, LEₙ(t, x))`;
* an unstable periodic orbit is a non-stationary periodic orbit that is not Lyapunov stable.

The source states the conjecture without restricting the class of systems, so it is stated here for
every such system. Note: the refined Kuznetsov–Eden conjecture (same page) only claims it for a
*typical* system; reviewers should check whether the universal reading is the intended one.
-/

namespace OMA.S_wp_eden_s_conjecture

open Filter Metric

/-- The phase space `ℝⁿ`. -/
abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- Matrix of a linear map of `ℝⁿ` in the standard basis. -/
noncomputable def mat {n : ℕ} (L : E n →L[ℝ] E n) : Matrix (Fin n) (Fin n) ℝ :=
  LinearMap.toMatrix (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis (L : E n →ₗ[ℝ] E n)

/-- Finite-time Lyapunov exponents `LEᵢ(t, x) = (1 / t) log σᵢ(D φᵗ(x))`
(unordered; `log σᵢ = (1/2) log` of the eigenvalues of `Aᴴ A`). -/
noncomputable def ftle {n : ℕ} (φ : ℝ → E n → E n) (t : ℝ) (x : E n) (i : Fin n) : ℝ :=
  Real.log ((Matrix.isHermitian_conjTranspose_mul_self (mat (fderiv ℝ (φ t) x))).eigenvalues i)
    / (2 * t)

/-- Sum of the `m` largest entries of `lam` (equal to `0` for `m = 0`). -/
noncomputable def topSum {n : ℕ} (lam : Fin n → ℝ) (m : ℕ) : ℝ :=
  ⨆ s : {s : Finset (Fin n) // s.card = m}, ∑ i ∈ s.1, lam i

/-- Kaplan–Yorke dimension of the family `lam`. -/
noncomputable def kaplanYorke {n : ℕ} (lam : Fin n → ℝ) : ℝ :=
  sSup {d : ℝ | 0 ≤ d ∧ d ≤ n ∧
    0 ≤ topSum lam ⌊d⌋₊ + (d - ⌊d⌋₊) * (topSum lam (⌊d⌋₊ + 1) - topSum lam ⌊d⌋₊)}

/-- Local Lyapunov dimension of the flow `φ` at `x`. -/
noncomputable def localLyapunovDim {n : ℕ} (φ : ℝ → E n → E n) (x : E n) : ℝ :=
  limsup (fun t : ℝ => kaplanYorke (ftle φ t x)) atTop

/-- `K` is a global attractor of `φ`: compact, invariant, and uniformly attracting every bounded set. -/
def IsGlobalAttractor {n : ℕ} (φ : ℝ → E n → E n) (K : Set (E n)) : Prop :=
  IsCompact K ∧ (∀ t : ℝ, 0 ≤ t → φ t '' K = K) ∧
    ∀ B : Set (E n), Bornology.IsBounded B → ∀ ε : ℝ, 0 < ε →
      ∃ T : ℝ, ∀ t : ℝ, T ≤ t → ∀ y ∈ B, infDist (φ t y) K < ε

/-- The orbit of `x` under `φ`. -/
def orbit {n : ℕ} (φ : ℝ → E n → E n) (x : E n) : Set (E n) :=
  Set.range fun t : ℝ => φ t x

/-- `x` lies on an unstable periodic orbit: it is not stationary, it is periodic, and its orbit
is not Lyapunov stable. -/
def OnUnstablePeriodicOrbit {n : ℕ} (f : E n → E n) (φ : ℝ → E n → E n) (x : E n) : Prop :=
  f x ≠ 0 ∧ (∃ T : ℝ, 0 < T ∧ φ T x = x) ∧
    ¬ ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ y : E n, infDist y (orbit φ x) < δ →
      ∀ t : ℝ, 0 ≤ t → infDist (φ t y) (orbit φ x) < ε

/-- **Eden's conjecture.** For the flow of a `C¹` vector field on `ℝⁿ` with a global attractor `K`,
the supremum of the local Lyapunov dimensions over `K` is achieved at a point of `K` that is a
stationary point or lies on an unstable periodic orbit. -/
theorem main :
    ∀ (n : ℕ) (f : E n → E n) (φ : ℝ → E n → E n) (K : Set (E n)),
      ContDiff ℝ 1 f →
      (∀ x, φ 0 x = x) →
      (∀ s t x, φ (s + t) x = φ s (φ t x)) →
      (∀ t x, HasDerivAt (fun s => φ s x) (f (φ t x)) t) →
      IsGlobalAttractor φ K →
      ∃ x ∈ K, (f x = 0 ∨ OnUnstablePeriodicOrbit f φ x) ∧
        localLyapunovDim φ x = sSup (localLyapunovDim φ '' K) := by
  sorry

end OMA.S_wp_eden_s_conjecture
