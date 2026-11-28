import OMAReductions.R_SymbolLengthMilnorKTheory_symbol_length_problem_variants_degree_two_isLeast_R1_H1_R1
import Mathlib.Algebra.BrauerGroup.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Modulo-three symbol length over the complex rational function field

We derive the bound from the norm-residue comparison, period–index equality,
and cyclicity in degree three. The Brauer-group statements use Mathlib's
quotient of finite-dimensional central simple algebras.
-/

-- Credit: @Alewawa

namespace OMA.R_SymbolLengthMilnorKTheory_symbol_length_problem_variants_degree_two_isLeast_R1_H1_R1_H2_R1

open scoped TensorProduct

/-- Merkurjev–Suslin over `ℂ(x,y)` at 3, including the formula on symbols.
A split tensor cube expresses 3-torsion using the Brauer quotient. -/
def H1 : Prop :=
  let F := MvRatFunc (Fin 2) ℂ
  ∃ ζ : F, IsPrimitiveRoot ζ 3 ∧
    ∃ f : MilnorK.grade F 3 2 → BrauerGroup.{0, 0} F,
      Function.Injective f ∧
      (∀ z, ∃ A : CSA.{0, 0} F, f z = Quotient.mk (Brauer.CSA_Setoid F) A ∧
        ∃ d : ℕ, 0 < d ∧
          Nonempty (((A ⊗[F] A) ⊗[F] A) ≃ₐ[F] Matrix (Fin d) (Fin d) F)) ∧
      ∀ (a b : Fˣ) (A : CSA.{0, 0} F) (u v : A),
        Module.finrank F A = 9 →
        u ^ 3 = algebraMap F A (a : F) →
        v ^ 3 = algebraMap F A (b : F) →
        v * u = algebraMap F A ζ * (u * v) →
        Submodule.span F (Set.range (fun ij : Fin 3 × Fin 3 =>
          u ^ (ij.1 : ℕ) * v ^ (ij.2 : ℕ))) = ⊤ →
        f ⟨MilnorK.symbol 3 ![a, b], MilnorK.symbol_mem_grade F 3 ![a, b]⟩ =
          Quotient.mk (Brauer.CSA_Setoid F) A

/-- The period–index theorem over `ℂ(x,y)` for classes of period dividing 3.
A class of index 1 is represented in degree 3 by the split matrix algebra. -/
def H2 : Prop :=
  let F := MvRatFunc (Fin 2) ℂ
  ∀ A : CSA.{0, 0} F,
    (∃ d : ℕ, 0 < d ∧
      Nonempty (((A ⊗[F] A) ⊗[F] A) ≃ₐ[F] Matrix (Fin d) (Fin d) F)) →
    ∃ B : CSA.{0, 0} F, Module.finrank F B = 9 ∧ IsBrauerEquivalent A B

/-- The degree-three cyclicity theorem in its Kummer presentation.
For a split matrix algebra the presentation uses a diagonal matrix and a cyclic shift. -/
def H3 : Prop :=
  let F := MvRatFunc (Fin 2) ℂ
  ∀ (ζ : F), IsPrimitiveRoot ζ 3 →
    ∀ B : CSA.{0, 0} F, Module.finrank F B = 9 →
      ∃ (a b : Fˣ) (u v : B),
        u ^ 3 = algebraMap F B (a : F) ∧
        v ^ 3 = algebraMap F B (b : F) ∧
        v * u = algebraMap F B ζ * (u * v) ∧
        Submodule.span F (Set.range (fun ij : Fin 3 × Fin 3 =>
          u ^ (ij.1 : ℕ) * v ^ (ij.2 : ℕ))) = ⊤

theorem main : H1 → H2 → H3 →
    OMA.R_SymbolLengthMilnorKTheory_symbol_length_problem_variants_degree_two_isLeast_R1_H1_R1.H2 := by
  intro hComparison hDegree hCyclic z hz
  obtain ⟨ζ, hζ, f, hf, hTorsion, hSymbol⟩ := hComparison
  obtain ⟨A, hA, hSplit⟩ := hTorsion ⟨z, hz⟩
  obtain ⟨B, hDim, hEquivalent⟩ := hDegree A hSplit
  obtain ⟨a, b, u, v, hu, hv, hComm, hSpan⟩ := hCyclic ζ hζ B hDim
  have hB : f ⟨z, hz⟩ = Quotient.mk (Brauer.CSA_Setoid _) B :=
    hA.trans (Quotient.sound (s := Brauer.CSA_Setoid _) hEquivalent)
  have hEq : z = MilnorK.symbol 3 ![a, b] :=
    congrArg Subtype.val (hf (hB.trans (hSymbol a b B u v hDim hu hv hComm hSpan).symm))
  exact ⟨1, le_rfl, fun _ => ![a, b], by simpa using hEq⟩

end OMA.R_SymbolLengthMilnorKTheory_symbol_length_problem_variants_degree_two_isLeast_R1_H1_R1_H2_R1
