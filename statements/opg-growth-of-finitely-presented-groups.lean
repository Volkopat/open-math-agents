import Mathlib

/-!
# Growth of finitely presented groups

Source: https://www.openproblemgarden.org/op/growth_of_finitely_presented_groups (posed by S. I. Adyan)
Credit: @k-okubo (agent: Claude Code, model claude-opus-5-5)

**Problem.** Does there exist a finitely presented group of intermediate growth?

The source defines: a finitely generated group has *intermediate growth* if its growth rate (for every
finite generating set) is subexponential but superpolynomial. Grigorchuk's groups of intermediate
growth (answering Milnor's question) are finitely generated but not finitely presented.

## Encoding

* *Finitely presented* is Mathlib's `Group.IsFinitelyPresented`.
* For a finite set `S` generating `G`, the ball `ball S n` is the set of elements that are products of
  at most `n` letters from `S ∪ S⁻¹`, and the growth function is `γ_S(n) = |ball S n|`
  (the standard growth function; it is finite because `S` is finite).
* *Subexponential*: for every `c > 1`, eventually `γ_S(n) ≤ cⁿ` (equivalently `γ_S(n)^(1/n) → 1`).
* *Superpolynomial*: `γ_S` is not bounded by a polynomial: there are no `C, d` with
  `γ_S(n) ≤ C · (n + 1)^d` for all `n`.
* Following the source, intermediate growth is required for *every* finite generating set (these
  growth types do not depend on the generating set, so this is the usual notion).
* The source asks a yes/no question; `main` states the answer yes, and a disproof would answer no
  (the source reports that expert opinion expects no).
-/

namespace OMA.S_opg_growth_of_finitely_presented_groups

/-- The ball of radius `n` for the generating set `S`: products of at most `n` letters, each in `S`
or the inverse of an element of `S`. -/
def ball {G : Type*} [Group G] (S : Set G) (n : ℕ) : Set G :=
  {g | ∃ l : List G, l.length ≤ n ∧ (∀ x ∈ l, x ∈ S ∨ x⁻¹ ∈ S) ∧ l.prod = g}

/-- The growth function `n ↦ |ball S n|`. -/
noncomputable def growth {G : Type*} [Group G] (S : Set G) (n : ℕ) : ℕ :=
  (ball S n).ncard

/-- Subexponential growth: for every `c > 1`, eventually `γ(n) ≤ cⁿ`. -/
def IsSubexponential (γ : ℕ → ℕ) : Prop :=
  ∀ c : ℝ, 1 < c → ∀ᶠ n in Filter.atTop, (γ n : ℝ) ≤ c ^ n

/-- Polynomial growth: `γ(n) ≤ C · (n + 1)^d` for all `n`, for some constants `C, d`. -/
def IsPolynomiallyBounded (γ : ℕ → ℕ) : Prop :=
  ∃ C d : ℕ, ∀ n : ℕ, γ n ≤ C * (n + 1) ^ d

/-- `G` has intermediate growth: for every finite generating set `S`, the growth function of `S` is
subexponential but superpolynomial. -/
def HasIntermediateGrowth (G : Type*) [Group G] : Prop :=
  ∀ S : Set G, S.Finite → Subgroup.closure S = ⊤ →
    IsSubexponential (growth S) ∧ ¬ IsPolynomiallyBounded (growth S)

/-- **Adyan's question**, answered yes: there exists a finitely presented group of intermediate
growth. -/
theorem main :
    ∃ (G : Type) (_ : Group G), Group.IsFinitelyPresented G ∧ HasIntermediateGrowth G := by
  sorry

end OMA.S_opg_growth_of_finitely_presented_groups
