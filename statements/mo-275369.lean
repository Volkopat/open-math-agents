import Mathlib.RepresentationTheory.Basic
-- (imports narrowed to what the statement uses, so the file compiles
-- well inside the checker time cap on a small machine)
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Data.Complex.Basic

/-!
# Isospectrality, Gassmann-Sunada triples, and tensor products

Source: MathOverflow question 275369 (THC, Jul 13 2017):
https://mathoverflow.net/questions/275369
Credit: @kmcooke22

The source is an open-ended question, still unanswered on MathOverflow:
starting from known Gassmann-Sunada triples, "are there constructions
known using tensor products of groups? If so, are they `trivial'?"

A Gassmann-Sunada triple is defined in the source as follows: a group `U`
and subgroups `V, W` such that every `U`-conjugacy class hits `V` and `W`
in the same number of elements. That definition is stated verbatim (for
finite `U`) as `IsGassmannSunadaTriple` below.

INTERPRETATION (flagged for the reviewer, since the source states no
conjectured answer): the statement `main` uses the standard
representation-theoretic reading of the question. A triple gives
permutation representations `C[U/V]` and `C[U/W]`; given two triples over
groups `U` and `U'`, one can form the external tensor product of their
permutation representations over the product group `U x U'`. The claim is
that this tensor product is isomorphic to the permutation representation
of the direct-product triple, and consequently that the product of two
Gassmann-Sunada triples is a Gassmann-Sunada triple: the tensor-product
construction exists and coincides with the direct-product ("trivial")
one, answering both halves of the question.

The literal alternative reading - the nonabelian tensor product of
groups (Brown-Loday) - is not used: Mathlib has no vocabulary for it, so
it cannot be stated here. The bare direct-product assertion alone is
also not used as the whole statement: the source already counts direct
products among the known "trivial constructions", so it would not by
itself answer the question asked.
-/

namespace OMA.S_mo_275369

open scoped TensorProduct

open Classical in
/-- A Gassmann-Sunada triple, as defined in the source: a finite group
`U` and subgroups `V, W` such that every `U`-conjugacy class hits `V`
and `W` in the same number of elements. Stated by quantifying over class
representatives `g`: the elements of `V` conjugate to `g` are as many as
the elements of `W` conjugate to `g`. -/
def IsGassmannSunadaTriple (U : Type*) [Group U] [Fintype U]
    (V W : Subgroup U) : Prop :=
  ∀ g : U,
    (Finset.univ.filter (fun u : U => u ∈ V ∧ IsConj u g)).card =
    (Finset.univ.filter (fun u : U => u ∈ W ∧ IsConj u g)).card

/-- The permutation representation of `U` on the cosets of `V`, acting
on functions `U ⧸ V → ℂ` by precomposition with the inverse action. -/
noncomputable def permRep (U : Type*) [Group U] [Fintype U] (V : Subgroup U) :
    Representation ℂ U (U ⧸ V → ℂ) where
  toFun g := LinearMap.funLeft ℂ ℂ (fun x : U ⧸ V => g⁻¹ • x)
  map_one' := by
    ext f x
    simp [LinearMap.funLeft]
  map_mul' := by
    intro g h
    ext f x
    simp [LinearMap.funLeft, mul_inv_rev, mul_smul]

/-- The external tensor product of the permutation representations of
two triples, as a representation of the product group: restrict each
factor along a projection and take `Representation.tprod`. -/
noncomputable def extTensorPermRep (U U' : Type*) [Group U] [Group U']
    [Fintype U] [Fintype U'] (V : Subgroup U) (V' : Subgroup U') :
    Representation ℂ (U × U')
      ((U ⧸ V → ℂ) ⊗[ℂ] (U' ⧸ V' → ℂ)) :=
  Representation.tprod
    ((permRep U V).comp (MonoidHom.fst U U'))
    ((permRep U' V').comp (MonoidHom.snd U U'))

/-- The tensor-product construction of Gassmann-Sunada triples, in the
representation-theoretic reading of the source question: the external
tensor product of the permutation representations of two triples is
isomorphic to the permutation representation of the direct-product
triple, and the product of two Gassmann-Sunada triples is a
Gassmann-Sunada triple. -/
theorem main : ∀ (U U' : Type) [Group U] [Group U'] [Fintype U] [Fintype U']
    (V W : Subgroup U) (V' W' : Subgroup U'),
    IsGassmannSunadaTriple U V W → IsGassmannSunadaTriple U' V' W' →
    (∃ e : ((U ⧸ V → ℂ) ⊗[ℂ] (U' ⧸ V' → ℂ)) ≃ₗ[ℂ]
        ((U × U') ⧸ (V.prod V') → ℂ),
      ∀ (g : U × U') (t : (U ⧸ V → ℂ) ⊗[ℂ] (U' ⧸ V' → ℂ)),
        e ((extTensorPermRep U U' V V') g t) =
          (permRep (U × U') (V.prod V')) g (e t)) ∧
    IsGassmannSunadaTriple (U × U') (V.prod V') (W.prod W') := by
  sorry

end OMA.S_mo_275369
