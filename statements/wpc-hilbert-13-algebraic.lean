import Mathlib

/-!
# Hilbert's thirteenth problem (algebraic version)

Source: https://en.wikipedia.org/wiki/Hilbert%27s_thirteenth_problem
Credit: @biondadave

Can a root of the general seventh-degree equation `x⁷ + a x³ + b x² + c x + 1 = 0`, as an
algebraic function of the three coefficients `(a, b, c)`, be written as a finite composition of
algebraic functions of two variables? (For continuous functions the answer is yes, by
Kolmogorov–Arnold; the algebraic version is open.)

Formalization notes:
* The coefficients `a, b, c` are independent indeterminates over `ℂ`: we work in
  `L`, an algebraic closure of `K = ℂ(a, b, c)` (the fraction field of `ℂ[X₀, X₁, X₂]`). Every
  composition of algebraic functions of `a, b, c` is an element of `L`.
* A finite composition of algebraic functions of two variables is encoded, as usual (Arnold,
  Brauer's resolvent degree as in Farb–Wolfson), by a finite tower of fields
  `ℂ(a, b, c) = F₀ ⊆ F₁ ⊆ ⋯ ⊆ Fₙ ⊆ L` in which each step adjoins one new function `α` that is an
  algebraic function of two functions `β, γ` already built, i.e. `Fᵢ₊₁ = Fᵢ(α)` with `β, γ ∈ Fᵢ`
  and `α` algebraic over `ℂ(β, γ)`. The field operations of `Fᵢ` give the rational operations
  (and functions of fewer variables) for free.
* The question asks whether some root of the septic lies in such an `Fₙ`. Hilbert conjectured
  that the answer is no; `main` states that conjectured answer. A proof of the negation of
  `main` would answer the question with yes.
-/

namespace OMA.S_wpc_hilbert_13_algebraic

/-- The field `ℂ(a, b, c)` of rational functions in three independent variables. -/
abbrev K := FractionRing (MvPolynomial (Fin 3) ℂ)

/-- An algebraic closure of `ℂ(a, b, c)`: it contains every algebraic function of `a, b, c`. -/
abbrev L := AlgebraicClosure K

/-- The `i`-th coefficient variable (`a`, `b`, `c` for `i = 0, 1, 2`), as an element of `L`. -/
noncomputable def var (i : Fin 3) : L :=
  algebraMap K L (algebraMap (MvPolynomial (Fin 3) ℂ) K (MvPolynomial.X i))

/-- One step of a composition: `F'` is obtained from `F` by adjoining a single `α` that is an
algebraic function of two elements `β, γ` of `F`, i.e. `α` is algebraic over `ℂ(β, γ)`. -/
def TwoVariableStep (F F' : IntermediateField ℂ L) : Prop :=
  ∃ β ∈ F, ∃ γ ∈ F, ∃ α : L,
    IsAlgebraic (IntermediateField.adjoin ℂ ({β, γ} : Set L)) α ∧
    F' = F ⊔ IntermediateField.adjoin ℂ ({α} : Set L)

/-- `x` is a finite composition of algebraic functions of two variables, applied to `a, b, c`:
it lies at the top of a finite tower of `TwoVariableStep`s starting at `ℂ(a, b, c)`. -/
def IsTwoVariableComposition (x : L) : Prop :=
  ∃ (n : ℕ) (F : Fin (n + 1) → IntermediateField ℂ L),
    F 0 = IntermediateField.adjoin ℂ (Set.range var) ∧
    (∀ i : Fin n, TwoVariableStep (F i.castSucc) (F i.succ)) ∧
    x ∈ F (Fin.last n)

/-- Hilbert's thirteenth problem, algebraic version, with Hilbert's conjectured answer: no root
of `x⁷ + a x³ + b x² + c x + 1` is a finite composition of algebraic functions of two
variables. -/
theorem main :
    ∀ x : L, x ^ 7 + var 0 * x ^ 3 + var 1 * x ^ 2 + var 2 * x + 1 = 0 →
      ¬ IsTwoVariableComposition x := by
  sorry

end OMA.S_wpc_hilbert_13_algebraic
