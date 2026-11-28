import Mathlib

/-!
# Broadcasting on the two-dimensional regular grid is impossible

Source: https://arxiv.org/abs/2010.01390
Credit: @tox5tox5

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.

A. Makur, E. Mossel and Y. Polyanskiy, "Broadcasting on Two-Dimensional Regular Grids"
(arXiv:2010.01390). Model: a root bit `X_{0,0} ∼ Bernoulli(1/2)`; level `k` has vertices
`X_{k,j}`, `j = 0, …, k`, with edges `(X_{k,j}, X_{k+1,j})` and `(X_{k,j}, X_{k+1,j+1})`; every edge
is an independent binary symmetric channel with crossover probability `δ ∈ (0, 1/2)` (independent
`Bernoulli(δ)` noise bits `Z`). Interior vertices compute
`X_{k,j} = f₂(X_{k-1,j-1} ⊕ Z_{k,j,1}, X_{k-1,j} ⊕ Z_{k,j,2})` with the same Boolean `f₂` everywhere,
and the boundary vertices compute `X_{k,0} = f₁(X_{k-1,0} ⊕ Z)`, `X_{k,k} = f₁(X_{k-1,k-1} ⊕ Z)`.
With `P^±_{X_k}` the law of level `k` given `X_{0,0} = 1` / `0`, broadcasting is impossible iff
`‖P^+_{X_k} - P^-_{X_k}‖_TV → 0`. The abstract conjectures "that it is impossible to propagate
information in a 2D regular grid regardless of the noise level `δ` and the choice of common Boolean
processing function"; the paper proves it for `f₂ = AND` and `f₂ = XOR`, and the `NAND` case is open
(its Conjecture 1). This file states the conjecture.

Modelling choices:
* A level-`k` configuration is `Fin (k + 1) → Bool`. Given level `k`, the vertices of level `k + 1`
  are conditionally independent (each uses its own edges' noise), so the law of level `k + 1` is
  obtained from that of level `k` by the explicit transition kernel `trans`.
* The conjecture ranges over the common two-input interior function `f₂` (one of the 16 gates,
  the same at every interior vertex). The one-input boundary rule is the identity, as fixed in the
  paper's analysis ("all Boolean processing functions … with one input are the identity rule"); the
  definitions keep `f₁` as a parameter and `main` instantiates it with `id`.
* The total variation distance is `½ ∑_x |P^+(x) - P^-(x)|`.
-/

namespace OMA.S_arxiv_2010_01390

open Filter Topology

/-- Probability that a bit sent through a BSC(`δ`) has noise `z`. -/
noncomputable def w (δ : ℝ) (z : Bool) : ℝ := if z then δ else 1 - δ

/-- `P(f₁(a ⊕ Z) = y)`. -/
noncomputable def p1 (δ : ℝ) (f₁ : Bool → Bool) (a y : Bool) : ℝ :=
  ∑ z : Bool, w δ z * (if f₁ (a ^^ z) = y then 1 else 0)

/-- `P(f₂(a ⊕ Z₁, c ⊕ Z₂) = y)`. -/
noncomputable def p2 (δ : ℝ) (f₂ : Bool → Bool → Bool) (a c y : Bool) : ℝ :=
  ∑ z₁ : Bool, ∑ z₂ : Bool, w δ z₁ * w δ z₂ * (if f₂ (a ^^ z₁) (c ^^ z₂) = y then 1 else 0)

/-- The transition probability from level `k` (configuration `x`) to level `k + 1`
(configuration `y`). -/
noncomputable def trans (δ : ℝ) (f₁ : Bool → Bool) (f₂ : Bool → Bool → Bool) (k : ℕ)
    (x : Fin (k + 1) → Bool) (y : Fin (k + 2) → Bool) : ℝ :=
  ∏ j : Fin (k + 2),
    if h0 : (j : ℕ) = 0 then p1 δ f₁ (x 0) (y j)
    else if hk : (j : ℕ) = k + 1 then p1 δ f₁ (x (Fin.last k)) (y j)
    else p2 δ f₂ (x ⟨(j : ℕ) - 1, by omega⟩) (x ⟨(j : ℕ), by omega⟩) (y j)

/-- The law of level `k` given the root bit `b`. -/
noncomputable def law (δ : ℝ) (f₁ : Bool → Bool) (f₂ : Bool → Bool → Bool) :
    (k : ℕ) → Bool → (Fin (k + 1) → Bool) → ℝ
  | 0, b, x => if x 0 = b then 1 else 0
  | k + 1, b, y => ∑ x : Fin (k + 1) → Bool, law δ f₁ f₂ k b x * trans δ f₁ f₂ k x y

/-- `‖P^+_{X_k} - P^-_{X_k}‖_TV`. -/
noncomputable def tv (δ : ℝ) (f₁ : Bool → Bool) (f₂ : Bool → Bool → Bool) (k : ℕ) : ℝ :=
  (1 / 2) * ∑ x : Fin (k + 1) → Bool, |law δ f₁ f₂ k true x - law δ f₁ f₂ k false x|

/-- **Makur–Mossel–Polyanskiy conjecture: broadcasting on the 2D regular grid is impossible.** -/
theorem main :
    ∀ (δ : ℝ), 0 < δ → δ < 1 / 2 → ∀ f₂ : Bool → Bool → Bool,
      Tendsto (tv δ id f₂) atTop (𝓝 0) := by
  sorry

end OMA.S_arxiv_2010_01390
