import Mathlib

/-!
# Artin conjecture (L-functions)

Source: https://en.wikipedia.org/wiki/Artin_conjecture_(L-functions)
Credit: @biondadave

Let `L / K` be a finite Galois extension of number fields with group `G`, and `ρ` a complex
finite-dimensional representation of `G`. The Artin conjecture: if `ρ` is irreducible and
nontrivial, the Artin L-function `L(s, ρ)` extends to an entire function of `s`.

Formalization notes:
* `L(s, ρ)` is the Euler product over the nonzero primes `𝔭` of `𝓞 K`, absolutely convergent for
  `Re s > 1`, of the local factors `det(1 - N𝔭^{-s} ρ(Frob_𝔓) | V^{I_𝔓})⁻¹`, where `𝔓` is a prime
  of `𝓞 L` above `𝔭`, `I_𝔓` its inertia group and `Frob_𝔓` any Frobenius element at `𝔓`
  (`σ x ≡ x ^ N𝔭 mod 𝔓` for all integers `x`). The factor is independent of these choices.
  "Extends to an entire function" is stated as: some entire `F : ℂ → ℂ` agrees with the Euler
  product on `Re s > 1` (the product is `tprod`, convergent there).
* The determinant on the inertia invariants `V^{I_𝔓}` is computed on all of `V` as
  `det(1 - t ρ(σ) e)` with `e = |I|⁻¹ ∑_{τ ∈ I} ρ(τ)`, the `G`-equivariant projection of `V` onto
  `V^{I}` along the sum of the nontrivial `I`-isotypic parts. Since `σ` normalizes `I`, `ρ(σ)`
  preserves both summands, and `ρ(σ) e` is `ρ(σ)` on `V^{I}` and `0` on the other summand; so
  this is exactly `det(1 - t ρ(σ) | V^{I})`.
* To avoid fixing a choice of `𝔓` and `Frob_𝔓` for every `𝔭`, the statement quantifies over any
  family of local factors `f 𝔭 s` that agrees with the formula above for every choice. Such a
  family exists (the factor does not depend on the choice), so this is not vacuous.
* Irreducible: `V ≠ 0` and the only `G`-stable subspaces are `⊥` and `⊤`. Nontrivial: some
  `ρ g ≠ 1` (for an irreducible representation, equivalently `ρ` is not the trivial
  one-dimensional representation, whose L-function is the Dedekind zeta function of `K`, which
  has a pole at `s = 1`).
-/

namespace OMA.S_wp_artin_conjecture_l_functions

open NumberField IsDedekindDomain

variable {K L : Type} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]

/-- `σ` is a Frobenius element at the prime `𝔓` of `𝓞 L` lying over `𝔭` (of norm `q`):
`σ x - x ^ q ∈ 𝔓` for every integer `x` of `L`. -/
def IsFrobeniusAt (σ : L ≃ₐ[K] L) (𝔓 : Ideal (𝓞 L)) (q : ℕ) : Prop :=
  ∀ x : 𝓞 L, ∃ y ∈ 𝔓, (y : L) = σ (x : L) - (x : L) ^ q

/-- `τ` is in the inertia group of `𝔓`: `τ x - x ∈ 𝔓` for every integer `x` of `L`. -/
def IsInInertia (τ : L ≃ₐ[K] L) (𝔓 : Ideal (𝓞 L)) : Prop :=
  ∀ x : 𝓞 L, ∃ y ∈ 𝔓, (y : L) = τ (x : L) - (x : L)

variable {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- The projection `e = |I|⁻¹ ∑_{τ ∈ I} ρ(τ)` of `V` onto the invariants of the inertia group
`I` of `𝔓`. -/
noncomputable def inertiaProjection [FiniteDimensional K L]
    (ρ : Representation ℂ (L ≃ₐ[K] L) V) (𝔓 : Ideal (𝓞 L)) : V →ₗ[ℂ] V := by
  classical
  exact ((Finset.univ.filter fun τ : L ≃ₐ[K] L => IsInInertia τ 𝔓).card : ℂ)⁻¹ •
    ∑ τ ∈ Finset.univ.filter (fun τ : L ≃ₐ[K] L => IsInInertia τ 𝔓), ρ τ

/-- The Euler factor `det(1 - N𝔭^{-s} ρ(σ) | V^{I_𝔓})⁻¹`, for a prime `𝔓` above `𝔭` and a
Frobenius element `σ` at `𝔓`. -/
noncomputable def localFactor [FiniteDimensional K L]
    (ρ : Representation ℂ (L ≃ₐ[K] L) V) (𝔭 : HeightOneSpectrum (𝓞 K))
    (𝔓 : Ideal (𝓞 L)) (σ : L ≃ₐ[K] L) (s : ℂ) : ℂ :=
  (LinearMap.det (1 - ((Ideal.absNorm 𝔭.asIdeal : ℂ) ^ (-s)) •
    (ρ σ ∘ₗ inertiaProjection ρ 𝔓)))⁻¹

/-- `ρ` is irreducible: `V ≠ 0` and the only `G`-stable subspaces are `⊥` and `⊤`. -/
def IsIrreducibleRep [FiniteDimensional K L] (ρ : Representation ℂ (L ≃ₐ[K] L) V) : Prop :=
  Nontrivial V ∧
    ∀ W : Submodule ℂ V, (∀ g, ∀ v ∈ W, ρ g v ∈ W) → W = ⊥ ∨ W = ⊤

/-- The Artin conjecture: for a nontrivial irreducible representation `ρ` of `Gal(L/K)`, the
Artin L-function `L(s, ρ)` (the Euler product of the local factors, for `Re s > 1`) extends to
an entire function. -/
theorem main :
    ∀ (K L : Type) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
      [FiniteDimensional K L] [IsGalois K L]
      (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
      (ρ : Representation ℂ (L ≃ₐ[K] L) V),
      IsIrreducibleRep ρ → (∃ g, ρ g ≠ 1) →
      ∀ f : HeightOneSpectrum (𝓞 K) → ℂ → ℂ,
        (∀ (𝔭 : HeightOneSpectrum (𝓞 K)) (𝔓 : Ideal (𝓞 L)) (σ : L ≃ₐ[K] L),
          𝔓.IsPrime → 𝔓.comap (algebraMap (𝓞 K) (𝓞 L)) = 𝔭.asIdeal →
          IsFrobeniusAt σ 𝔓 (Ideal.absNorm 𝔭.asIdeal) →
          ∀ s, f 𝔭 s = localFactor ρ 𝔭 𝔓 σ s) →
        ∃ F : ℂ → ℂ, Differentiable ℂ F ∧ ∀ s : ℂ, 1 < s.re → F s = ∏' 𝔭, f 𝔭 s := by
  sorry

end OMA.S_wp_artin_conjecture_l_functions
