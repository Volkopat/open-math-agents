import OMAReductions.R_HyperbolicGroupsResiduallyFinite_hyperbolic_exists_finiteIndex_ne_top_R3
import Mathlib.GroupTheory.CoprodI
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.ResiduallyFinite
import Mathlib.Tactic

/-!
This implements the free-product strategy in MacChan1203’s parent reduction.
The base group in H1 is the construction of OpenAI (math release 075).
The Lean proof adapted in PR #3425 retains its torsion-freeness.
H2 is the hyperbolicity combination theorem in the case of a free product
with two identical factors. H3 is the torsion theorem for the same free product.
The argument below uses Mathlib’s reduced words and ping-pong lemma to embed
a rank-two free group whose generators vanish in every finite image.
-/

namespace OMA.R_HyperbolicGroupsResiduallyFinite_hyperbolic_exists_finiteIndex_ne_top_R3_H1_R1

open Monoid Monoid.CoprodI
open scoped Pointwise

/-- Torsion-free hyperbolic groups need not be residually finite. -/
def H1 : Prop :=
  ∃ (A : Type) (_ : Group A) (_ : Group.IsHyperbolic A),
    (∀ (a : A) (n : ℕ), 0 < n → a ^ n = 1 → a = 1) ∧ ¬ Group.ResiduallyFinite A

/-- A free product of two copies of a hyperbolic group is hyperbolic. -/
def H2 : Prop :=
  ∀ (A : Type) [Group A] [Group.IsHyperbolic A],
    Group.IsHyperbolic (Monoid.CoprodI (fun _ : Fin 2 => A))

/-- A free product of two copies of a torsion-free group is torsion-free. -/
def H3 : Prop :=
  ∀ (A : Type) [Group A], (∀ (a : A) (n : ℕ), 0 < n → a ^ n = 1 → a = 1) →
    ∀ (g : Monoid.CoprodI (fun _ : Fin 2 => A)) (n : ℕ), 0 < n → g ^ n = 1 → g = 1

/-- The two copies of an infinite-order, finite-quotient-invisible element
of G freely generate an invisible free group in G * G. -/
theorem free_invisible_in_double {G : Type} [Group G] (g : G)
    (hinf : ¬ IsOfFinOrder g)
    (hk : ∀ (F : Type) [Group F] [Finite F] (u : G →* F), u g = 1) :
    ∃ i : FreeGroup (Fin 2) →* CoprodI (fun _ : Fin 2 => G),
      Function.Injective i ∧ ∀ (F : Type) [Group F] [Finite F]
        (u : CoprodI (fun _ : Fin 2 => G) →* F) (j : Fin 2), u (i (FreeGroup.of j)) = 1 := by
  classical
  let A := fun _ : Fin 2 => G
  let inc (j : Fin 2) := @CoprodI.of (Fin 2) A _ j
  let t : Fin 2 → CoprodI A := fun j => inc j g
  let f (j : Fin 2) : FreeGroup Unit →* CoprodI A := FreeGroup.lift (fun _ => t j)
  let X (j : Fin 2) : Set (CoprodI.Word A) := {w | w.fstIdx = some j}
  have hgne : g ≠ 1 := by
    rintro rfl
    exact hinf (isOfFinOrder_iff_pow_eq_one.mpr ⟨1, one_pos, one_pow _⟩)
  have hnon (j : Fin 2) : (X j).Nonempty := by
    have hn : (Word.empty : Word A).fstIdx ≠ some j := by simp [Word.fstIdx, Word.empty]
    exact ⟨Word.cons (i := j) g .empty hn hgne, Word.fstIdx_cons ..⟩
  have hdis : Pairwise (fun i j => Disjoint (X i) (X j)) := by
    intro i j h
    apply Set.disjoint_left.mpr
    intro w wi wj
    exact h (Option.some.inj (wi.symm.trans wj))
  have hping : Pairwise fun i j => ∀ h : FreeGroup Unit, h ≠ 1 → f i h • X j ⊆ X i := by
    intro i j hij
    refine FreeGroup.freeGroupUnitEquivInt.forall_congr_left.mpr ?_
    intro n hne
    change FreeGroup.lift (fun _ : Unit => t i) (FreeGroup.of () ^ n) • X j ⊆ X i
    simp only [map_zpow, FreeGroup.lift_apply_of]
    have hn : n ≠ 0 := by
      rintro rfl
      apply hne
      simp [FreeGroup.freeGroupUnitEquivInt]
    have hpow : g ^ n ≠ 1 := by
      intro he
      apply hn
      apply (injective_zpow_iff_not_isOfFinOrder.mpr hinf)
      simpa using he
    rintro _ ⟨w, hw, rfl⟩
    have hidx : w.fstIdx ≠ some i := fun e => hij (Option.some.inj (e.symm.trans hw))
    change ((inc i g) ^ n • w).fstIdx = some i
    rw [← map_zpow]
    change ((CoprodI.of (M := A) (i := i) (g ^ n)) • w).fstIdx = some i
    rw [← Word.cons_eq_smul (h1 := hidx) (h2 := hpow)]
    exact Word.fstIdx_cons ..
  have card : 3 ≤ Cardinal.mk (Fin 2) ∨ ∃ _i : Fin 2, 3 ≤ Cardinal.mk (FreeGroup Unit) := by
    right
    refine ⟨0, ?_⟩
    rw [FreeGroup.freeGroupUnitEquivInt.cardinal_eq, Cardinal.mk_denumerable]
    exact Cardinal.natCast_le_aleph0
  have hi := CoprodI.lift_injective_of_ping_pong f card X hnon hdis hping
  refine ⟨FreeGroup.lift t, ?_, ?_⟩
  · have eq : FreeGroup.lift t = (CoprodI.lift f).comp freeGroupEquivCoprodI.toMonoidHom := by
      ext j
      simp [f]
    rw [eq]
    exact hi.comp freeGroupEquivCoprodI.injective
  · intro F _ _ u j
    simpa [t] using hk F (u.comp (inc j))


theorem main : H1 → H2 → H3 → OMA.R_HyperbolicGroupsResiduallyFinite_hyperbolic_exists_finiteIndex_ne_top_R3.H1 := by
  classical
  intro seed hyperbolic_double torsion_free_double
  obtain ⟨A, _, _, ht, hnr⟩ := seed
  have bad : ∃ g : A, g ≠ 1 ∧
      ∀ (F : Type) [Group F] [Finite F] (u : A →* F), u g = 1 := by
    by_contra! hn
    apply hnr
    apply Group.residuallyFinite_of_forall_exists_finite_monoidHom
    intro a ha
    obtain ⟨F, groupF, finiteF, u, hu⟩ := hn a ha
    exact ⟨F, groupF, finiteF, u, hu⟩
  obtain ⟨g, hgne, hk⟩ := bad
  have hi : ¬ IsOfFinOrder g := by
    rintro h
    obtain ⟨n,hn,hpow⟩ := h.exists_pow_eq_one
    exact hgne (ht g n hn hpow)
  have hyp := hyperbolic_double A
  have tor := torsion_free_double A ht
  exact ⟨Monoid.CoprodI (fun _ : Fin 2 => A), inferInstance, hyp, tor, free_invisible_in_double g hi hk⟩

end OMA.R_HyperbolicGroupsResiduallyFinite_hyperbolic_exists_finiteIndex_ne_top_R3_H1_R1
