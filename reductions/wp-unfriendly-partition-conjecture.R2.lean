import OMAStatements.S_wp_unfriendly_partition_conjecture
import Mathlib

/-!
# Unfriendly partitions of locally finite graphs

Every graph in which every vertex has finite degree has an unfriendly
2-partition, with no countability assumption. On a finite set S that
contains F and all neighbours of F, a colouring minimising the number of
monochromatic adjacent pairs in S is unfriendly at every vertex of F,
since recolouring a bad vertex would lower that count. The unfriendly
condition at a vertex depends on finitely many coordinates, so it is a
closed condition in the compact space of all colourings, and compactness
gives a colouring that is unfriendly everywhere. This is the folklore
case extended by Aharoni, Milner and Prikry (JCTB 50, 1990).

The cases with some vertex of infinite degree are split as H1 (finitely
many such vertices, proved by Aharoni, Milner and Prikry but not
formalized) and H2 (infinitely many such vertices, open).
-/

namespace OMA.R_wp_unfriendly_partition_conjecture_R2

open SimpleGraph

-- Countable graphs with finitely many, but at least one, vertices of infinite degree
-- have unfriendly 2-partitions (Aharoni, Milner and Prikry, JCTB 50, 1990).
def H1 : Prop :=
  ∀ (V : Type) [Countable V] (G : SimpleGraph V),
    {v | (G.neighborSet v).Infinite}.Nonempty → {v | (G.neighborSet v).Infinite}.Finite →
    ∃ f : V → Bool, ∀ v : V,
      Cardinal.mk {w // G.Adj v w ∧ f w = f v} ≤ Cardinal.mk {w // G.Adj v w ∧ f w ≠ f v}

-- Countable graphs with infinitely many vertices of infinite degree have unfriendly
-- 2-partitions (open).
def H2 : Prop :=
  ∀ (V : Type) [Countable V] (G : SimpleGraph V), {v | (G.neighborSet v).Infinite}.Infinite →
    ∃ f : V → Bool, ∀ v : V,
      Cardinal.mk {w // G.Adj v w ∧ f w = f v} ≤ Cardinal.mk {w // G.Adj v w ∧ f w ≠ f v}

lemma mk_adj_eq {V : Type*} (G : SimpleGraph V) (hlf : ∀ v, (G.neighborSet v).Finite)
    (v : V) (P : V → Prop) [DecidablePred P] :
    Cardinal.mk {w // G.Adj v w ∧ P w} = (((hlf v).toFinset.filter P).card : Cardinal) := by
  rw [← Cardinal.mk_coe_finset]
  exact Cardinal.mk_congr (Equiv.subtypeEquivRight (fun w => by simp))

lemma good_iff {V : Type*} (G : SimpleGraph V) (hlf : ∀ v, (G.neighborSet v).Finite)
    (f : V → Bool) (v : V) :
    Cardinal.mk {w // G.Adj v w ∧ f w = f v} ≤ Cardinal.mk {w // G.Adj v w ∧ f w ≠ f v} ↔
      ((hlf v).toFinset.filter fun w => f w = f v).card ≤
        ((hlf v).toFinset.filter fun w => f w ≠ f v).card := by
  rw [mk_adj_eq G hlf v, mk_adj_eq G hlf v]
  exact Nat.cast_le

lemma isClosed_good {V : Type*} (G : SimpleGraph V) (hlf : ∀ v, (G.neighborSet v).Finite)
    (v : V) :
    IsClosed {f : V → Bool | ((hlf v).toFinset.filter fun w => f w = f v).card ≤
        ((hlf v).toFinset.filter fun w => f w ≠ f v).card} := by
  classical
  let T : Finset V := insert v (hlf v).toFinset
  let r : (V → Bool) → (T → Bool) := fun f i => f i
  have hr : Continuous r := continuous_pi fun i => continuous_apply _
  have heq : {f : V → Bool | ((hlf v).toFinset.filter fun w => f w = f v).card ≤
        ((hlf v).toFinset.filter fun w => f w ≠ f v).card} =
      r ⁻¹' (r '' {f : V → Bool | ((hlf v).toFinset.filter fun w => f w = f v).card ≤
        ((hlf v).toFinset.filter fun w => f w ≠ f v).card}) := by
    ext g
    constructor
    · intro hg
      exact ⟨g, hg, rfl⟩
    · rintro ⟨f, hf, hfg⟩
      have hag : ∀ w ∈ T, f w = g w := fun w hw => congrFun hfg ⟨w, hw⟩
      have hv : f v = g v := hag v (Finset.mem_insert_self _ _)
      have e1 : ((hlf v).toFinset.filter fun w => g w = g v) =
          (hlf v).toFinset.filter fun w => f w = f v :=
        Finset.filter_congr (fun w hw => by rw [hag w (Finset.mem_insert_of_mem hw), hv])
      have e2 : ((hlf v).toFinset.filter fun w => g w ≠ g v) =
          (hlf v).toFinset.filter fun w => f w ≠ f v :=
        Finset.filter_congr (fun w hw => by rw [hag w (Finset.mem_insert_of_mem hw), hv])
      show ((hlf v).toFinset.filter fun w => g w = g v).card ≤
        ((hlf v).toFinset.filter fun w => g w ≠ g v).card
      rw [e1, e2]
      exact hf
  rw [heq]
  exact (isClosed_discrete _).preimage hr

lemma split_sum {V : Type*} [DecidableEq V] (S : Finset V) (a : V → V → ℕ) (v : V)
    (hv : v ∈ S) (hsym : ∀ x y, a x y = a y x) (hvv : a v v = 0) :
    ∑ x ∈ S, ∑ y ∈ S, a x y =
      2 * ∑ y ∈ S, a v y + ∑ x ∈ S.erase v, ∑ y ∈ S.erase v, a x y := by
  have h1 : ∑ x ∈ S, ∑ y ∈ S, a x y =
      ∑ y ∈ S, a v y + ∑ x ∈ S.erase v, ∑ y ∈ S, a x y :=
    (Finset.add_sum_erase S (fun x => ∑ y ∈ S, a x y) hv).symm
  have h2 : ∀ x, ∑ y ∈ S, a x y = a x v + ∑ y ∈ S.erase v, a x y :=
    fun x => (Finset.add_sum_erase S (fun y => a x y) hv).symm
  have h3 : ∑ x ∈ S.erase v, a x v = ∑ y ∈ S, a v y := by
    rw [← Finset.add_sum_erase S (fun y => a v y) hv, hvv, zero_add]
    exact Finset.sum_congr rfl (fun x _ => hsym x v)
  calc ∑ x ∈ S, ∑ y ∈ S, a x y
      = ∑ y ∈ S, a v y + ∑ x ∈ S.erase v, (a x v + ∑ y ∈ S.erase v, a x y) := by
        rw [h1]
        congr 1
        exact Finset.sum_congr rfl (fun x _ => h2 x)
    _ = ∑ y ∈ S, a v y + (∑ x ∈ S.erase v, a x v +
          ∑ x ∈ S.erase v, ∑ y ∈ S.erase v, a x y) := by
        rw [Finset.sum_add_distrib]
    _ = 2 * ∑ y ∈ S, a v y + ∑ x ∈ S.erase v, ∑ y ∈ S.erase v, a x y := by
        rw [h3]
        ring

lemma finite_good {V : Type*} (G : SimpleGraph V) (hlf : ∀ v, (G.neighborSet v).Finite)
    (u : Finset V) : ∃ f : V → Bool, ∀ v ∈ u,
      ((hlf v).toFinset.filter fun w => f w = f v).card ≤
        ((hlf v).toFinset.filter fun w => f w ≠ f v).card := by
  classical
  let S : Finset V := u ∪ u.biUnion (fun v => (hlf v).toFinset)
  let Φ : (V → Bool) → ℕ := fun f =>
    ∑ x ∈ S, ∑ y ∈ S, if G.Adj x y ∧ f x = f y then 1 else 0
  obtain ⟨f, hf⟩ : ∃ f, ∀ g, Φ f ≤ Φ g := by
    obtain ⟨f, hf⟩ := Nat.sInf_mem (s := Set.range Φ) ⟨_, ⟨fun _ => true, rfl⟩⟩
    exact ⟨f, fun g => hf ▸ Nat.sInf_le ⟨g, rfl⟩⟩
  refine ⟨f, fun v hvu => ?_⟩
  have hvS : v ∈ S := Finset.mem_union_left _ hvu
  have hNS : (hlf v).toFinset ⊆ S := fun w hw =>
    Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨v, hvu, hw⟩)
  obtain ⟨g, hg⟩ : ∃ g : V → Bool, g = Function.update f v (!f v) := ⟨_, rfl⟩
  have hgv : g v = !f v := by rw [hg, Function.update_self]
  have hgo : ∀ x, x ≠ v → g x = f x := fun x hx => by rw [hg, Function.update_of_ne hx]
  have key : ∀ h : V → Bool, Φ h =
      2 * (∑ y ∈ S, if G.Adj v y ∧ h v = h y then 1 else 0) +
        ∑ x ∈ S.erase v, ∑ y ∈ S.erase v, if G.Adj x y ∧ h x = h y then 1 else 0 :=
    fun h => split_sum S (fun x y => if G.Adj x y ∧ h x = h y then 1 else 0) v hvS
      (fun x y => by simp only [G.adj_comm x y, @eq_comm _ (h x) (h y)]) (by simp)
  have hR : (∑ x ∈ S.erase v, ∑ y ∈ S.erase v, if G.Adj x y ∧ g x = g y then 1 else 0) =
      ∑ x ∈ S.erase v, ∑ y ∈ S.erase v, if G.Adj x y ∧ f x = f y then 1 else 0 := by
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro y hy
    rw [hgo x (Finset.ne_of_mem_erase hx), hgo y (Finset.ne_of_mem_erase hy)]
  have hA : ∀ h : V → Bool, (∑ y ∈ S, if G.Adj v y ∧ h v = h y then 1 else 0) =
      ((hlf v).toFinset.filter fun w => h w = h v).card := by
    intro h
    rw [← Finset.card_filter]
    congr 1
    ext y
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset, mem_neighborSet]
    constructor
    · rintro ⟨_, ha, he⟩
      exact ⟨ha, he.symm⟩
    · rintro ⟨ha, he⟩
      exact ⟨hNS (by simpa using ha), ha, he.symm⟩
  have hB : ((hlf v).toFinset.filter fun w => g w = g v) =
      (hlf v).toFinset.filter fun w => f w ≠ f v := by
    apply Finset.filter_congr
    intro w hw
    have hwv : w ≠ v := (G.ne_of_adj (by simpa using hw)).symm
    rw [hgo w hwv, hgv]
    cases f w <;> cases f v <;> simp
  have hmin := hf g
  rw [key f, key g, hR, hA f, hA g, hB] at hmin
  omega

theorem locallyFinite_unfriendly {V : Type*} (G : SimpleGraph V)
    (hlf : ∀ v, (G.neighborSet v).Finite) :
    ∃ f : V → Bool, ∀ v : V,
      Cardinal.mk {w // G.Adj v w ∧ f w = f v} ≤ Cardinal.mk {w // G.Adj v w ∧ f w ≠ f v} := by
  obtain ⟨f, -, hf⟩ := (isCompact_univ (X := V → Bool)).inter_iInter_nonempty
    (fun v => {f : V → Bool | ((hlf v).toFinset.filter fun w => f w = f v).card ≤
        ((hlf v).toFinset.filter fun w => f w ≠ f v).card})
    (fun v => isClosed_good G hlf v)
    (fun u => by
      obtain ⟨f, hf⟩ := finite_good G hlf u
      exact ⟨f, Set.mem_univ _, Set.mem_iInter₂.mpr hf⟩)
  exact ⟨f, fun v => (good_iff G hlf f v).mpr (Set.mem_iInter.mp hf v)⟩

theorem main : H1 → H2 → type_of% @OMA.S_wp_unfriendly_partition_conjecture.main := by
  intro h1 h2 V _ G
  by_cases hD : {v | (G.neighborSet v).Infinite}.Infinite
  · exact h2 V G hD
  · rcases Set.eq_empty_or_nonempty {v | (G.neighborSet v).Infinite} with he | hne
    · have hlf : ∀ v, (G.neighborSet v).Finite := fun v =>
        Set.not_infinite.mp (fun h => (Set.eq_empty_iff_forall_notMem.mp he) v h)
      obtain ⟨f, hf⟩ := locallyFinite_unfriendly G hlf
      exact ⟨f, hf⟩
    · exact h1 V G hne (Set.not_infinite.mp hD)

end OMA.R_wp_unfriendly_partition_conjecture_R2
