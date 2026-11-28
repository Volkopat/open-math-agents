import Mathlib

/-!
# Dictators maximize the symmetric and asymmetric `1/2`-stability among balanced Boolean functions

Source: https://arxiv.org/abs/2410.10147
Credit: @tox5tox5

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.

L. Yu, "Local Optimality of Dictator Functions with Applications to Courtade–Kumar and Li–Médard
Conjectures" (arXiv:2410.10147). Setting: `X` is uniform on `{±1}ⁿ`, `Y` flips each coordinate of
`X` independently with probability `(1-ρ)/2`, `T_ρ` is the Bonami–Beckner (noise) operator, and for
a Boolean function `f : {±1}ⁿ → {0,1}` and convex `Φ`, `Stab_Φ[f] = E[Φ(T_ρ f(X))]`. With
`ln_q(t) = (t^{q-1} - 1)/(q - 1)`, `Φ_q(t) = t ln_q(t)` gives the asymmetric `q`-stability and
`Φ_q^sym(t) = Φ_q(t) + Φ_q(1-t)` the symmetric one; dictators are `f_d = 1{x_k = 1}` or
`1{x_k = -1}`. The abstract states: "we conjecture that dictator functions maximize both the
symmetric and asymmetric `1/2`-stability over all balanced Boolean functions" (Conjectures 5.15 and
5.16, which state no range for `ρ`; the paper observes that dictators "seem to have the largest
`q`-stability for all `0 < ρ < 1`" when `1/2 ≤ q < 1`). This file states that conjecture for every
`ρ ∈ [0, 1]`: at `ρ = 0` (`T₀ f ≡ 1/2` for balanced `f`) and `ρ = 1` (`T₁ f = f ∈ {0, 1}`) both sides
coincide, so the endpoints add nothing.

Modelling choices:
* `{±1}ⁿ` is `Fin n → Bool` with `true` for `+1`; `f` takes values in `Bool` read as `{0, 1}`.
* `T_ρ f(x) = ∑_y f(y) ∏ᵢ ((1 + ρ)/2 if yᵢ = xᵢ else (1 - ρ)/2)`, and the expectation over
  uniform `X` is `2⁻ⁿ ∑_x`.
* For `q = 1/2`, `Φ_{1/2}(t) = t (t^{-1/2} - 1)/(-1/2) = 2t - 2√t` (with `0 · ln_q 0 = 0`).
* "Balanced" means `E[f] = 1/2`, i.e. `f` takes the value `1` on exactly half of the cube.
  Dictators are balanced (for `n ≥ 1`) and all give the same value, so the claim is stated against
  every dictator `x ↦ x k` and `x ↦ ¬ x k`.
-/

namespace OMA.S_arxiv_2410_10147

/-- The Boolean cube `{±1}ⁿ` (`true` = `+1`). -/
abbrev Cube (n : ℕ) := Fin n → Bool

/-- The noise operator: `T_ρ f(x) = E[f(Y) | X = x]`. -/
noncomputable def noise {n : ℕ} (ρ : ℝ) (f : Cube n → Bool) (x : Cube n) : ℝ :=
  ∑ y : Cube n, (if f y then 1 else 0) * ∏ i, if y i = x i then (1 + ρ) / 2 else (1 - ρ) / 2

/-- `Φ_{1/2}(t) = t ln_{1/2}(t) = 2t - 2√t`. -/
noncomputable def Φ (t : ℝ) : ℝ := 2 * t - 2 * Real.sqrt t

/-- Asymmetric `1/2`-stability `E[Φ_{1/2}(T_ρ f(X))]`. -/
noncomputable def stab {n : ℕ} (ρ : ℝ) (f : Cube n → Bool) : ℝ :=
  (2 : ℝ) ^ (-(n : ℤ)) * ∑ x : Cube n, Φ (noise ρ f x)

/-- Symmetric `1/2`-stability `E[Φ_{1/2}(T_ρ f(X)) + Φ_{1/2}(1 - T_ρ f(X))]`. -/
noncomputable def stabSym {n : ℕ} (ρ : ℝ) (f : Cube n → Bool) : ℝ :=
  (2 : ℝ) ^ (-(n : ℤ)) * ∑ x : Cube n, (Φ (noise ρ f x) + Φ (1 - noise ρ f x))

/-- `f` is balanced: it equals `1` on exactly half of the cube. -/
def Balanced {n : ℕ} (f : Cube n → Bool) : Prop :=
  2 * (Finset.univ.filter fun x => f x = true).card = 2 ^ n

/-- **Yu's `1/2`-stability conjecture.** -/
theorem main :
    ∀ (n : ℕ) (ρ : ℝ), 1 ≤ n → 0 ≤ ρ → ρ ≤ 1 →
      ∀ f : Cube n → Bool, Balanced f →
        ∀ (k : Fin n) (s : Bool),
          stab ρ f ≤ stab ρ (fun x => x k == s) ∧
            stabSym ρ f ≤ stabSym ρ (fun x => x k == s) := by
  sorry

end OMA.S_arxiv_2410_10147
