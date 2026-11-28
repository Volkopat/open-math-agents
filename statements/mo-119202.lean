import Mathlib.NumberTheory.NumberField.CMField
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.NumberTheory.Padics.Complex
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! # David Loeffler's variant of Leopoldt's conjecture, MathOverflow 119202 (2013)

The logarithm is needed only on images of algebraic units. Raising such a unit to
a positive even power gives a principal unit since its residue lies in a finite
field. On the principal-unit disk the usual p-adic logarithm is given by its
power series. Dividing by that even exponent recovers its value on the unit.
-/

open NumberField Module

namespace OMA.S_mo_119202

/-- The p-adic logarithm of an algebraic p-adic unit. The exponent is positive
even on all inputs. For inputs used in the statement the defining set is nonempty. -/
noncomputable def logUnit (p : ℕ) [Fact p.Prime] (x : ℂ_[p]) : ℂ_[p] :=
  let y := x ^ 2
  let m := sInf {n : ℕ | ‖y ^ (n + 1) - 1‖ < 1} + 1
  let z := y ^ m - 1
  (∑' n : ℕ, (-1 : ℂ_[p]) ^ n * z ^ (n + 1) / (n + 1 : ℕ)) / (2 * m : ℕ)

/-- The columns represent a basis of the global unit group modulo torsion. -/
def IsFundamental (K : Type) [Field K] [NumberField K]
    (u : Fin (Units.rank K) → (𝓞 K)ˣ) : Prop :=
  ∃ b : type_of% (Units.basisModTorsion K),
    ∀ i, Additive.ofMul (QuotientGroup.mk (u i) : (𝓞 K)ˣ ⧸ Units.torsion K) = b i

/-- An injection selecting k of the embeddings describes one maximal minor.
Its nonvanishing is independent of the order in which the rows are selected. -/
theorem main :
    ∀ (K : Type) [Field K] [NumberField K],
      (∀ E : IntermediateField ℚ K, ¬ IsCMField E) →
      ∀ (p : ℕ) [Fact p.Prime],
      ∀ u : Fin (Units.rank K) → (𝓞 K)ˣ, IsFundamental K u →
      ∀ σ : Fin (Units.rank K) ↪ (K →+* ℂ_[p]),
        Matrix.det (fun i j => logUnit p (σ i (((u j : (𝓞 K)ˣ) : 𝓞 K) : K))) ≠ 0 := by
  sorry

end OMA.S_mo_119202
