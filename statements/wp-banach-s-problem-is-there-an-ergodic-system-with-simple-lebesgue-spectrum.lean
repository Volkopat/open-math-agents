import Mathlib

/-!
# Banach's problem – is there an ergodic system with simple Lebesgue spectrum?

Source: https://en.wikipedia.org/wiki/Stefan_Banach
(listed in https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics, citing
S. M. Ulam, *Problems in Modern Mathematics*, Wiley, 1964, p. 76).
Credit: @biondadave

Does there exist an ergodic measure-preserving system whose Koopman operator has simple
Lebesgue spectrum?

Formalization notes:
* A system is an invertible measure-preserving transformation `T` of a standard Borel
  probability space `(Ω, μ)`. Its Koopman operator `U f = f ∘ T` is unitary on `L²(μ)` (complex
  coefficients) and fixes the constants, so it acts on `L²₀(μ)`, the orthogonal complement of
  the constant functions. The spectrum of the system is, as usual, the spectrum of `U` on
  `L²₀(μ)`.
* "Simple Lebesgue spectrum" means: `U` restricted to `L²₀(μ)` is unitarily equivalent to
  multiplication by `z` on `L²(S¹, Lebesgue)`, i.e. (via Fourier series) to the bilateral shift
  on `ℓ²(ℤ)`. A unitary operator is unitarily equivalent to the bilateral shift iff some vector
  `f` has orbit `(Uⁿ f)_{n ∈ ℤ}` forming an orthonormal basis (a Hilbert basis) of the space.
  This is the form stated below: `orbit T hT f n = Uⁿ f`, and the orbit is orthonormal with
  dense span in `L²₀(μ)`.
* Ergodicity is required as in the source. (It is in fact implied by the spectral condition,
  since a Lebesgue spectrum has no eigenvalue `1` on `L²₀`.)
* A standard probability space with an atom carrying an ergodic `T` is a finite cycle, whose
  `L²₀` is finite dimensional, so such spaces never qualify; the statement is thus equivalent
  to the classical one on the unit interval with Lebesgue measure.
* `main` states the "yes" answer; a disproof is its negation.
-/

namespace OMA.S_wp_banach_s_problem_is_there_an_ergodic_system_with_simple_lebesgue_spectrum

open MeasureTheory

variable {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The Koopman operator `f ↦ f ∘ T` on `L²(μ)`. -/
noncomputable def koopman (T : Ω ≃ᵐ Ω) (hT : MeasurePreserving T μ μ) :
    Lp ℂ 2 μ → Lp ℂ 2 μ :=
  Lp.compMeasurePreserving T hT

/-- The orbit `n ↦ Uⁿ f` (`n ∈ ℤ`) of `f` under the Koopman operator `U` of `T`: forward
iterates of `U` for `n ≥ 0`, iterates of `U⁻¹ = (f ↦ f ∘ T⁻¹)` for `n < 0`. -/
noncomputable def orbit (T : Ω ≃ᵐ Ω) (hT : MeasurePreserving T μ μ) (f : Lp ℂ 2 μ) :
    ℤ → Lp ℂ 2 μ
  | Int.ofNat k => (koopman T hT)^[k] f
  | Int.negSucc k => (koopman T.symm (hT.symm T))^[k + 1] f

/-- `L²₀(μ)`: the orthogonal complement of the constant functions in `L²(μ)`. -/
noncomputable def L2zero (μ : Measure Ω) [IsFiniteMeasure μ] : Submodule ℂ (Lp ℂ 2 μ) :=
  (Submodule.span ℂ {(memLp_const (1 : ℂ) : MemLp (fun _ : Ω => (1 : ℂ)) 2 μ).toLp _})ᗮ

/-- Banach's problem: there is an ergodic invertible measure-preserving transformation of a
standard Borel probability space whose Koopman operator has simple Lebesgue spectrum on
`L²₀`, i.e. some `f` has orbit `(Uⁿ f)_{n ∈ ℤ}` forming a Hilbert basis of `L²₀(μ)`. -/
theorem main :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (_ : StandardBorelSpace Ω) (μ : Measure Ω)
      (_ : IsProbabilityMeasure μ) (T : Ω ≃ᵐ Ω) (hT : MeasurePreserving T μ μ),
      Ergodic T μ ∧
      ∃ f : Lp ℂ 2 μ, Orthonormal ℂ (orbit T hT f) ∧
        (Submodule.span ℂ (Set.range (orbit T hT f))).topologicalClosure = L2zero μ := by
  sorry

end OMA.S_wp_banach_s_problem_is_there_an_ergodic_system_with_simple_lebesgue_spectrum
