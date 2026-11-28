import OMAStatements.S_mo_18548
import Mathlib

/-
MathOverflow 18548: a simplicial complex on three vertices whose face poset is not a lattice
and whose face poset with a top element added is not distributive.

Take the three isolated vertices: F is the family of subsets of Fin 3 with at most one element.
- Not a lattice: an upper bound of the faces {0} and {1} would contain two elements.
- With a top added: the only upper bound of {1} and {2} is the top, and the only lower bound
  of {0} and {1} (or of {0} and {2}) is the empty face. In a distributive lattice
  a inf (b sup c) = (a inf b) sup (a inf c), which here would give {0} = the empty face.
-/

namespace OMA.PMO18548

open OMA.S_mo_18548

lemma no_sup {α : Type} [Lattice α] (a b : α) (h : ∀ z, a ≤ z → b ≤ z → False) : False :=
  h (a ⊔ b) le_sup_left le_sup_right

lemma no_M3 {α : Type} [DistribLattice α] (a b c e t : α) (hbc : ∀ z, b ≤ z → c ≤ z → z = t)
    (hat : a ≤ t) (hab : ∀ w, w ≤ a → w ≤ b → w = e) (hac : ∀ w, w ≤ a → w ≤ c → w = e) :
    a = e := by
  have h := inf_sup_left a b c
  rw [hbc (b ⊔ c) le_sup_left le_sup_right, inf_eq_left.2 hat,
    hab (a ⊓ b) inf_le_left inf_le_right, hac (a ⊓ c) inf_le_left inf_le_right, sup_idem] at h
  exact h

lemma two {s : Finset (Fin 3)} (hs : s.card ≤ 1) {i j : Fin 3} (hij : i ≠ j) (hi : i ∈ s)
    (hj : j ∈ s) : False := by
  have := Finset.one_lt_card.2 ⟨i, hi, j, hj, hij⟩
  omega

lemma meet {i j : Fin 3} (hij : i ≠ j) {s : Finset (Fin 3)} (hi : s ⊆ {i}) (hj : s ⊆ {j}) :
    s = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun x hx => hij ?_
  rw [← Finset.mem_singleton.1 (hi hx), ← Finset.mem_singleton.1 (hj hx)]

lemma main' : ∃ F : Set (Finset (Fin 3)), IsSimplicialFaceFamily F ∧
    (∀ i : Fin 3, {i} ∈ F) ∧ ¬ FaceOrderLattice F ∧ ¬ AugmentedFaceDistributive F := by
  refine ⟨{s | s.card ≤ 1}, ⟨by simp, fun s t ht hst => le_trans (Finset.card_le_card hst) ht⟩,
    fun i => by simp, ?_, ?_⟩
  · rintro ⟨L, hL⟩
    refine @no_sup _ L ⟨{0}, by simp⟩ ⟨{1}, by simp⟩ fun z h0 h1 => ?_
    have h0' : ({0} : Finset (Fin 3)) ⊆ z.val := (hL _ _).1 h0
    have h1' : ({1} : Finset (Fin 3)) ⊆ z.val := (hL _ _).1 h1
    exact two z.2 (by decide : (0 : Fin 3) ≠ 1) (h0' (Finset.mem_singleton_self _))
      (h1' (Finset.mem_singleton_self _))
  · rintro ⟨L, hL⟩
    have key : (some ⟨{0}, by simp⟩ : Option ↥{s : Finset (Fin 3) | s.card ≤ 1}) =
        some ⟨∅, by simp⟩ := by
      refine @no_M3 _ L _ (some ⟨{1}, by simp⟩) (some ⟨{2}, by simp⟩) _ none ?_ ?_ ?_ ?_
      · intro z hb hc
        rcases z with _ | t
        · rfl
        · exfalso
          have hb' : ({1} : Finset (Fin 3)) ⊆ t.val := (hL _ _).1 hb
          have hc' : ({2} : Finset (Fin 3)) ⊆ t.val := (hL _ _).1 hc
          exact two t.2 (by decide : (1 : Fin 3) ≠ 2) (hb' (Finset.mem_singleton_self _))
            (hc' (Finset.mem_singleton_self _))
      · exact (hL _ _).2 trivial
      · intro w ha hb
        rcases w with _ | s
        · exact False.elim ((hL _ _).1 ha)
        · have ha' : s.val ⊆ ({0} : Finset (Fin 3)) := (hL _ _).1 ha
          have hb' : s.val ⊆ ({1} : Finset (Fin 3)) := (hL _ _).1 hb
          exact congrArg some (Subtype.ext (meet (by decide) ha' hb'))
      · intro w ha hc
        rcases w with _ | s
        · exact False.elim ((hL _ _).1 ha)
        · have ha' : s.val ⊆ ({0} : Finset (Fin 3)) := (hL _ _).1 ha
          have hc' : s.val ⊆ ({2} : Finset (Fin 3)) := (hL _ _).1 hc
          exact congrArg some (Subtype.ext (meet (by decide) ha' hc'))
    exact Finset.singleton_ne_empty (0 : Fin 3) (congrArg Subtype.val (Option.some.inj key))

end OMA.PMO18548

theorem OMA.solution : type_of% @OMA.S_mo_18548.main := OMA.PMO18548.main'
