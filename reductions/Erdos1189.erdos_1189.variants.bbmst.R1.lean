import FormalConjectures.ErdosProblems.«1189»
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Set.Card
import Mathlib.Data.Finset.Image
import Mathlib.Tactic.Push
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.InfiniteSum.Real

namespace OMA.R_Erdos1189_erdos_1189_variants_bbmst_R1
open Finset Set Filter Erdos1189

/-- The upper bound of the BBMST enumeration theorem, counting all normalized minimal families. -/
def H1 : Prop :=
  let families := fun k : ℕ => {A : Finset (ℕ × ℤ) | ((∀ p ∈ A, 1 < p.1 ∧ 0 ≤ p.2 ∧ p.2 < (p.1:ℤ)) ∧
  (∀ z : ℤ, ∃ p ∈ A, z ≡ p.2 [ZMOD p.1]) ∧
  ∀ p ∈ A, ∃ z : ℤ, z ≡ p.2 [ZMOD p.1] ∧
    ∀ q ∈ A, q ≠ p → ¬ z ≡ q.2 [ZMOD q.1]) ∧ A.card=k}
  ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop, ((families k).ncard : ℝ) ≤ Real.exp ((4 * Real.sqrt bbmstTau / 3 + ε) * ((k : ℝ) ^ (3 / 2 : ℝ) / Real.sqrt (Real.log k)))

/-- There are only finitely many normalized minimal families with a fixed number of classes. -/
def H2 : Prop :=
  ∀ k : ℕ, ({A : Finset (ℕ × ℤ) | ((∀ p ∈ A, 1 < p.1 ∧ 0 ≤ p.2 ∧ p.2 < (p.1:ℤ)) ∧
  (∀ z : ℤ, ∃ p ∈ A, z ≡ p.2 [ZMOD p.1]) ∧
  ∀ p ∈ A, ∃ z : ℤ, z ≡ p.2 [ZMOD p.1] ∧
    ∀ q ∈ A, q ≠ p → ¬ z ≡ q.2 [ZMOD q.1]) ∧ A.card=k}).Finite

theorem normalized_family {M : Finset ℕ} (irr : IsIrreducibleCoveringSet M) :
    ∃ A : Finset (ℕ × ℤ), ((∀ p ∈ A, 1 < p.1 ∧ 0 ≤ p.2 ∧ p.2 < (p.1:ℤ)) ∧
  (∀ z : ℤ, ∃ p ∈ A, z ≡ p.2 [ZMOD p.1]) ∧
  ∀ p ∈ A, ∃ z : ℤ, z ≡ p.2 [ZMOD p.1] ∧
    ∀ q ∈ A, q ≠ p → ¬ z ≡ q.2 [ZMOD q.1]) ∧ A.card = M.card ∧ A.image Prod.fst = M := by
  obtain ⟨⟨mods,a,cover⟩,minimal⟩ := irr
  let f (m : ℕ) : ℕ × ℤ := (m, a m % (m:ℤ))
  have fi : Function.Injective f := fun _ _ h => congrArg Prod.fst h
  refine ⟨M.image f,⟨?_,?_,?_⟩,card_image_of_injective _ fi,?_⟩
  · intro p hp
    obtain ⟨m,hm,rfl⟩ := mem_image.mp hp
    have pos : 0 < (m:ℤ) := by exact_mod_cast (Nat.zero_lt_of_lt (mods m hm))
    exact ⟨mods m hm,Int.emod_nonneg _ pos.ne',Int.emod_lt_of_pos _ pos⟩
  · intro z
    obtain ⟨m,hm,cong⟩ := cover z
    exact ⟨f m,mem_image_of_mem _ hm,cong.trans (Int.mod_modEq _ _).symm⟩
  · intro p hp
    obtain ⟨m,hm,rfl⟩ := mem_image.mp hp
    have missing : ¬ ∀ z : ℤ, ∃ j ∈ M.erase m, z ≡ a j [ZMOD j] := by
      intro h
      exact minimal _ (erase_ssubset hm) ⟨fun j hj => mods j (mem_of_mem_erase hj),a,h⟩
    obtain ⟨z,hz⟩ := Classical.not_forall.mp missing
    obtain ⟨j,hj,cong⟩ := cover z
    have jm : j=m := by
      by_contra ne
      exact hz ⟨j,mem_erase.mpr ⟨ne,hj⟩,cong⟩
    subst j
    refine ⟨z,cong.trans (Int.mod_modEq _ _).symm,?_⟩
    intro q hq nq matchq
    obtain ⟨j,hj,rfl⟩ := mem_image.mp hq
    exact hz ⟨j,mem_erase.mpr ⟨fun h => nq (congrArg f h),hj⟩,matchq.trans (Int.mod_modEq _ _)⟩
  · ext m
    simp [Finset.image_image,f,Function.comp_def]

theorem count_transfer (k : ℕ) (fin : {A : Finset (ℕ × ℤ) | ((∀ p ∈ A, 1 < p.1 ∧ 0 ≤ p.2 ∧ p.2 < (p.1:ℤ)) ∧
  (∀ z : ℤ, ∃ p ∈ A, z ≡ p.2 [ZMOD p.1]) ∧
  ∀ p ∈ A, ∃ z : ℤ, z ≡ p.2 [ZMOD p.1] ∧
    ∀ q ∈ A, q ≠ p → ¬ z ≡ q.2 [ZMOD q.1]) ∧ A.card=k}.Finite) :
    {M : Finset ℕ | IsIrreducibleCoveringSet M ∧ M.card=k}.ncard ≤
      {A : Finset (ℕ × ℤ) | ((∀ p ∈ A, 1 < p.1 ∧ 0 ≤ p.2 ∧ p.2 < (p.1:ℤ)) ∧
  (∀ z : ℤ, ∃ p ∈ A, z ≡ p.2 [ZMOD p.1]) ∧
  ∀ p ∈ A, ∃ z : ℤ, z ≡ p.2 [ZMOD p.1] ∧
    ∀ q ∈ A, q ≠ p → ¬ z ≡ q.2 [ZMOD q.1]) ∧ A.card=k}.ncard := by
  let proj := fun A : Finset (ℕ × ℤ) => A.image Prod.fst
  apply le_trans _ (Set.ncard_image_le (f := proj) (s := _) fin)
  apply Set.ncard_le_ncard _ (fin.image proj)
  rintro M ⟨irr,sz⟩
  obtain ⟨A,h,card,eqn⟩ := normalized_family irr
  exact ⟨A,⟨h,card.trans sz⟩,eqn⟩
theorem main : H1 → H2 → type_of% @Erdos1189.erdos_1189.variants.bbmst := by
  intro bound finiteFamilies ε hε
  filter_upwards [bound ε hε] with k boundK
  apply le_trans _ boundK
  exact_mod_cast count_transfer k (finiteFamilies k)

end OMA.R_Erdos1189_erdos_1189_variants_bbmst_R1
