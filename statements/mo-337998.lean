import Mathlib

/-!
# Is the set of square roots of an exponential family convex in `L²`?

Source: https://mathoverflow.net/questions/337998
Credit: @koolkao

Question (AB_IM, MathOverflow 337998, 2019; CC BY-SA 4.0). It is known that (given a σ-finite
Borel reference measure `ν`) the parameter space of an exponential family is convex in
Euclidean space. However, my question is, is the associated exponential manifold `√EM(c)` a
convex subset of `L²_ν`? Where
`EM(c) = {p(·, θ) : θ ∈ Θ, p(x, θ) = exp(θᵀ c(x) - ψ(θ))}`, for some fixed continuously
differentiable scalar functions `c = {c_1, …, c_n}` on `ℝ^d`. We assume that `EM(c) ⊆ L²_ν`.

`main` states that `√EM(c) = {√p : p ∈ EM(c)}` is always convex: for all parameters `θ₁, θ₂`
and `a ∈ [0, 1]`, the function `a √p(·, θ₁) + (1 - a) √p(·, θ₂)` agrees `ν`-almost everywhere
with `√p(·, θ)` for some parameter `θ`. A disproof is one exponential family for which some such
combination is not the square root of a member of the family.

Translation choices:
* the sample space is `ℝ^d = Fin d → ℝ` (the source takes `ν` on `ℝ` and `c` on `ℝ^d`; we
  put `ν` on the space where `c` lives) with a σ-finite (Borel) measure `ν`;
* `c : (Fin d → ℝ) → (Fin n → ℝ)` is `C¹` (`ContDiff ℝ 1 c`) and `θᵀ c(x) = ∑ i, θ i * c x i`;
* `Θ` is the natural parameter space `{θ | x ↦ exp(θᵀ c(x)) is ν-integrable}` and
  `ψ(θ) = log ∫ exp(θᵀ c) dν` (`dens ν c θ` is `p(·, θ)`);
* the assumption `EM(c) ⊆ L²_ν` is `MemLp (dens ν c θ) 2 ν` for all `θ ∈ Θ`;
* elements of `L²_ν` are functions up to `ν`-a.e. equality, so convexity of `√EM(c)` is stated
  with `=ᵐ[ν]`.
-/

namespace OMA.S_mo_337998

open MeasureTheory

/-- The natural parameter space of the exponential family with statistic `c`. -/
def Θ {d n : ℕ} (ν : Measure (Fin d → ℝ)) (c : (Fin d → ℝ) → (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  {θ | Integrable (fun x => Real.exp (∑ i, θ i * c x i)) ν}

/-- The density `p(x, θ) = exp(θᵀ c(x) - ψ(θ))` with `ψ(θ) = log ∫ exp(θᵀ c) dν`. -/
noncomputable def dens {d n : ℕ} (ν : Measure (Fin d → ℝ)) (c : (Fin d → ℝ) → (Fin n → ℝ))
    (θ : Fin n → ℝ) (x : Fin d → ℝ) : ℝ :=
  Real.exp (∑ i, θ i * c x i - Real.log (∫ y, Real.exp (∑ i, θ i * c y i) ∂ν))

/-- The square roots of the members of an exponential family form a convex subset of `L²_ν`. -/
theorem main :
    ∀ (d n : ℕ) (ν : Measure (Fin d → ℝ)), SigmaFinite ν →
      ∀ c : (Fin d → ℝ) → (Fin n → ℝ), ContDiff ℝ 1 c →
      (∀ θ ∈ Θ ν c, MemLp (dens ν c θ) 2 ν) →
      ∀ θ₁ ∈ Θ ν c, ∀ θ₂ ∈ Θ ν c, ∀ a : ℝ, 0 ≤ a → a ≤ 1 →
        ∃ θ ∈ Θ ν c, (fun x => a * √(dens ν c θ₁ x) + (1 - a) * √(dens ν c θ₂ x))
          =ᵐ[ν] fun x => √(dens ν c θ x) := by
  sorry

end OMA.S_mo_337998
