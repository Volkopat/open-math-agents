import FormalConjectures.Wikipedia.TuzaConjecture
import Mathlib
-- Problem: Tuza conjecture, Haxell variant
-- Upstream: formal-conjectures FormalConjectures/Wikipedia/TuzaConjecture.lean (declaration TuzaConjecture.tuza_conjecture.variants.haxell)
-- Source of the proof of 165/59 (which is below 66/23): Lean 4 development sichen-wang/tuza-lean,
-- commit 5cae999212a06418941fa9c909529a4ff38e1e5e, MIT License, Copyright (c) 2026 Sichen Wang.
-- Its files are concatenated below with imports removed, one small tactic fix for Lean 4.33.1, and a bridge
-- from its tau and nu to the formal-conjectures definitions (TuzaBridge section at the end).

-- ==== Tuza.Basic.Geometry

/-! Triangle edges and the geometry of two and three pages. -/

namespace Tuza

variable {V : Type*} [DecidableEq V]

/-- The three unoriented edges on the listed vertices. -/
def triangleEdges (u v w : V) : Finset (Sym2 V) :=
  {s(u, v), s(u, w), s(v, w)}

@[simp]
theorem mem_triangleEdges {e : Sym2 V} {u v w : V} :
    e ∈ triangleEdges u v w ↔ e = s(u, v) ∨ e = s(u, w) ∨ e = s(v, w) := by
  simp [triangleEdges]

/-- A triangle is an edge set on three distinct vertices. -/
def IsTriangle (T : Finset (Sym2 V)) : Prop :=
  ∃ u v w, u ≠ v ∧ u ≠ w ∧ v ≠ w ∧ T = triangleEdges u v w

theorem isTriangle_triangleEdges {u v w : V}
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) :
    IsTriangle (triangleEdges u v w) :=
  ⟨u, v, w, huv, huw, hvw, rfl⟩

theorem triangleEdges_card {u v w : V}
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) :
    (triangleEdges u v w).card = 3 := by
  have h₁ : s(u, v) ≠ s(u, w) := by
    intro h
    exact hvw (Sym2.congr_right.mp h)
  have h₂ : s(u, v) ≠ s(v, w) := by
    intro h
    rcases Sym2.eq_iff.mp h with h | h
    · exact huv h.1
    · exact huw h.1
  have h₃ : s(u, w) ≠ s(v, w) := by
    intro h
    exact huv (Sym2.congr_left.mp h)
  simp [triangleEdges, h₁, h₂, h₃]

theorem IsTriangle.card_eq_three {T : Finset (Sym2 V)} (hT : IsTriangle T) :
    T.card = 3 := by
  rcases hT with ⟨u, v, w, huv, huw, hvw, rfl⟩
  exact triangleEdges_card huv huw hvw

theorem IsTriangle.not_mem_diag {T : Finset (Sym2 V)}
    (hT : IsTriangle T) (z : V) : s(z, z) ∉ T := by
  rcases hT with ⟨u, v, w, huv, huw, hvw, rfl⟩
  simp only [mem_triangleEdges, Sym2.eq_iff]
  aesop

theorem IsTriangle.ne_of_mem {T : Finset (Sym2 V)} (hT : IsTriangle T)
    {u v : V} (h : s(u, v) ∈ T) : u ≠ v := by
  rintro rfl
  exact hT.not_mem_diag u h

/-- Any two edges of a triangle have a common endpoint. -/
theorem IsTriangle.edges_incident {T : Finset (Sym2 V)} (hT : IsTriangle T)
    {e f : Sym2 V} (he : e ∈ T) (hf : f ∈ T) :
    ∃ z : V, z ∈ e ∧ z ∈ f := by
  rcases hT with ⟨u, v, w, huv, huw, hvw, rfl⟩
  rcases mem_triangleEdges.mp he with rfl | rfl | rfl <;>
    rcases mem_triangleEdges.mp hf with rfl | rfl | rfl
  · exact ⟨u, by simp, by simp⟩
  · exact ⟨u, by simp, by simp⟩
  · exact ⟨v, by simp, by simp⟩
  · exact ⟨u, by simp, by simp⟩
  · exact ⟨u, by simp, by simp⟩
  · exact ⟨w, by simp, by simp⟩
  · exact ⟨v, by simp, by simp⟩
  · exact ⟨w, by simp, by simp⟩
  · exact ⟨v, by simp, by simp⟩

/-- Two distinct edges incident at a vertex determine the triangle. -/
theorem IsTriangle.eq_of_spokes {T : Finset (Sym2 V)} (hT : IsTriangle T)
    {u v w : V} (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (he : s(u, v) ∈ T) (hf : s(u, w) ∈ T) :
    T = triangleEdges u v w := by
  rcases hT with ⟨a, b, c, hab, hac, hbc, rfl⟩
  simp only [mem_triangleEdges, Sym2.eq_iff] at he hf
  rcases he with h | h | h <;>
    rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;>
    rcases hf with h | h | h <;>
    rcases h with ⟨hc, hd⟩ | ⟨hc, hd⟩ <;>
    subst_vars <;>
    simp_all [triangleEdges, Sym2.eq_swap, Finset.insert_comm]
  all_goals
    ext e
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto

theorem IsTriangle.exists_third_of_mem {T : Finset (Sym2 V)}
    (hT : IsTriangle T) {u v : V} (he : s(u, v) ∈ T) :
    ∃ w, u ≠ w ∧ v ≠ w ∧ T = triangleEdges u v w := by
  rcases hT with ⟨a, b, c, hab, hac, hbc, rfl⟩
  simp only [mem_triangleEdges, Sym2.eq_iff] at he
  rcases he with h | h | h
  · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨c, hac, hbc, rfl⟩
    · refine ⟨c, hbc, hac, ?_⟩
      ext e
      simp [triangleEdges, Sym2.eq_swap, or_comm]
  · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · refine ⟨b, hab, hbc.symm, ?_⟩
      ext e
      simp [triangleEdges, Sym2.eq_swap, or_left_comm]
    · refine ⟨b, hbc.symm, hab, ?_⟩
      ext e
      simp [triangleEdges, Sym2.eq_swap, or_comm, or_assoc]
  · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · refine ⟨a, hab.symm, hac.symm, ?_⟩
      ext e
      simp [triangleEdges, Sym2.eq_swap, or_comm, or_left_comm]
    · refine ⟨a, hac.symm, hab.symm, ?_⟩
      ext e
      simp [triangleEdges, Sym2.eq_swap, or_comm, or_assoc]

/-- Triangles whose listed vertices have only the first vertex in common share no edge. -/
theorem triangleEdges_disjoint_of_five_distinct {u v w x y : V}
    (hvertices : [u, v, w, x, y].Nodup) :
    Disjoint (triangleEdges u v w) (triangleEdges u x y) := by
  apply Finset.disjoint_left.mpr
  intro e he hf
  rcases mem_triangleEdges.mp he with rfl | rfl | rfl <;>
    simp_all [mem_triangleEdges, List.nodup_cons]

/-- A triangle meeting both pages and missing their spine uses the opposite edge. -/
theorem two_page_triangle {T : Finset (Sym2 V)} (hT : IsTriangle T)
    {u v x y : V} (hvertices : [u, v, x, y].Nodup)
    (hspine : s(u, v) ∉ T)
    (hx : (T ∩ triangleEdges u v x).Nonempty)
    (hy : (T ∩ triangleEdges u v y).Nonempty) :
    T = triangleEdges u x y ∨ T = triangleEdges v x y := by
  have hdistinct : u ≠ v ∧ u ≠ x ∧ u ≠ y ∧ v ≠ x ∧ v ≠ y ∧ x ≠ y := by
    simpa [List.nodup_cons, and_assoc] using hvertices
  rcases hdistinct with ⟨huv, hux, huy, hvx, hvy, hxy⟩
  obtain ⟨e, he⟩ := hx
  obtain ⟨heT, heX⟩ := Finset.mem_inter.mp he
  obtain ⟨f, hf⟩ := hy
  obtain ⟨hfT, hfY⟩ := Finset.mem_inter.mp hf
  rcases mem_triangleEdges.mp heX with rfl | rfl | rfl <;>
    rcases mem_triangleEdges.mp hfY with rfl | rfl | rfl
  all_goals try exact (hspine heT).elim
  all_goals try exact (hspine hfT).elim
  · exact Or.inl (hT.eq_of_spokes hux huy hxy heT hfT)
  · obtain ⟨z, hz, hz'⟩ := hT.edges_incident heT hfT
    simp only [Sym2.mem_iff] at hz hz'
    rcases hz with rfl | rfl <;> rcases hz' with h | h <;> simp_all
  · obtain ⟨z, hz, hz'⟩ := hT.edges_incident heT hfT
    simp only [Sym2.mem_iff] at hz hz'
    rcases hz with rfl | rfl <;> rcases hz' with h | h <;> simp_all
  · exact Or.inr (hT.eq_of_spokes hvx hvy hxy heT hfT)

theorem two_page_opposite_mem {T : Finset (Sym2 V)} (hT : IsTriangle T)
    {u v x y : V} (hvertices : [u, v, x, y].Nodup)
    (hspine : s(u, v) ∉ T)
    (hx : (T ∩ triangleEdges u v x).Nonempty)
    (hy : (T ∩ triangleEdges u v y).Nonempty) : s(x, y) ∈ T := by
  rcases two_page_triangle hT hvertices hspine hx hy with rfl | rfl <;> simp

/-- A triangle meeting three distinct pages must contain their common spine. -/
theorem three_page_spine {T : Finset (Sym2 V)} (hT : IsTriangle T)
    {u v x y z : V} (hvertices : [u, v, x, y, z].Nodup)
    (hx : (T ∩ triangleEdges u v x).Nonempty)
    (hy : (T ∩ triangleEdges u v y).Nonempty)
    (hz : (T ∩ triangleEdges u v z).Nonempty) : s(u, v) ∈ T := by
  by_contra hspine
  have hfour : [u, v, x, y].Nodup := by
    simp_all [List.nodup_cons]
  obtain ⟨e, he⟩ := hz
  obtain ⟨heT, heZ⟩ := Finset.mem_inter.mp he
  rcases two_page_triangle hT hfour hspine hx hy with h | h <;>
    rw [h] at heT <;>
    rcases mem_triangleEdges.mp heT with rfl | rfl | rfl <;>
    simp_all [mem_triangleEdges, List.nodup_cons] <;> aesop

end Tuza

-- ==== Tuza.Basic.Packing

/-!
Finite families of edge sets. These definitions are independent of graph geometry.
Graph triangles are connected to them in the graph module.
-/

namespace Tuza

open Finset

variable {E : Type*} [DecidableEq E]

/-- The union of the edges used by a family. -/
def support (P : Finset (Finset E)) : Finset E := P.biUnion id

@[simp] theorem mem_support {e : E} {P : Finset (Finset E)} :
    e ∈ support P ↔ ∃ T ∈ P, e ∈ T := by
  simp [support]

@[simp] theorem support_insert (T : Finset E) (P : Finset (Finset E)) :
    support (insert T P) = T ∪ support P := by
  simp [support]

theorem support_mono {P Q : Finset (Finset E)} (h : P ⊆ Q) :
    support P ⊆ support Q := by
  intro e he
  obtain ⟨T, hT, heT⟩ := mem_support.mp he
  exact mem_support.mpr ⟨T, h hT, heT⟩

/-- A packing consists of members of the family that are pairwise edge-disjoint. -/
def IsPacking (F P : Finset (Finset E)) : Prop :=
  P ⊆ F ∧ (P : Set (Finset E)).Pairwise Disjoint

/-- Maximum is with respect to the number of triangles. -/
def IsMaximumPacking (F P : Finset (Finset E)) : Prop :=
  IsPacking F P ∧ ∀ Q, IsPacking F Q → Q.card ≤ P.card

/-- A transversal meets every member in an edge. -/
def IsCover (F : Finset (Finset E)) (C : Finset E) : Prop :=
  ∀ T ∈ F, (T ∩ C).Nonempty

/-- Deleting selected edges removes every member that meets one of them. -/
def residual (F : Finset (Finset E)) (C : Finset E) : Finset (Finset E) :=
  F.filter (fun T => Disjoint T C)

@[simp] theorem mem_residual {F : Finset (Finset E)} {C T : Finset E} :
    T ∈ residual F C ↔ T ∈ F ∧ Disjoint T C := by
  simp [residual]

omit [DecidableEq E] in
theorem packing_empty (F : Finset (Finset E)) : IsPacking F ∅ := by
  simp [IsPacking, Set.Pairwise]

omit [DecidableEq E] in
theorem IsPacking.subfamily {F P Q : Finset (Finset E)}
    (hP : IsPacking F P) (hQ : Q ⊆ P) : IsPacking F Q := by
  exact ⟨hQ.trans hP.1, fun T hT U hU hne => hP.2 (hQ hT) (hQ hU) hne⟩

omit [DecidableEq E] in
theorem IsPacking.mono_family {F F' P : Finset (Finset E)}
    (hP : IsPacking F P) (hF : F ⊆ F') : IsPacking F' P :=
  ⟨hP.1.trans hF, hP.2⟩

theorem IsPacking.union {F P Q : Finset (Finset E)}
    (hP : IsPacking F P) (hQ : IsPacking F Q)
    (hd : Disjoint (support P) (support Q)) : IsPacking F (P ∪ Q) := by
  refine ⟨union_subset hP.1 hQ.1, ?_⟩
  have hcross : ∀ T ∈ P, ∀ U ∈ Q, Disjoint T U := by
    intro T hT U hU
    exact hd.mono (fun e he => mem_support.mpr ⟨T, hT, he⟩)
      (fun e he => mem_support.mpr ⟨U, hU, he⟩)
  intro T hT U hU hne
  rcases mem_union.mp hT with hT | hT <;> rcases mem_union.mp hU with hU | hU
  · exact hP.2 hT hU hne
  · exact hcross T hT U hU
  · exact (hcross U hU T hT).symm
  · exact hQ.2 hT hU hne

theorem disjoint_of_support_disjoint {P Q : Finset (Finset E)}
    (hne : ∀ T ∈ P, T.Nonempty) (hd : Disjoint (support P) (support Q)) :
    Disjoint P Q := by
  apply disjoint_left.mpr
  intro T hT hU
  obtain ⟨e, he⟩ := hne T hT
  exact disjoint_left.mp hd (mem_support.mpr ⟨T, hT, he⟩)
    (mem_support.mpr ⟨T, hU, he⟩)

omit [DecidableEq E] in
theorem exists_maximumPacking (F : Finset (Finset E)) :
    ∃ P, IsMaximumPacking F P := by
  classical
  let candidates := F.powerset.filter (IsPacking F)
  have hc : (∅ : Finset (Finset E)) ∈ candidates := by
    simp [candidates, packing_empty]
  obtain ⟨P, hP, hmax⟩ := candidates.exists_max_image Finset.card ⟨∅, hc⟩
  refine ⟨P, (mem_filter.mp hP).2, ?_⟩
  intro Q hQ
  exact hmax Q (mem_filter.mpr ⟨mem_powerset.mpr hQ.1, hQ⟩)

/-- One maximum packing, chosen from the finite collection of all packings. -/
noncomputable def maximumPacking (F : Finset (Finset E)) : Finset (Finset E) :=
  Classical.choose (exists_maximumPacking F)

omit [DecidableEq E] in
theorem maximumPacking_spec (F : Finset (Finset E)) :
    IsMaximumPacking F (maximumPacking F) :=
  Classical.choose_spec (exists_maximumPacking F)

/-- The maximum packing size. -/
noncomputable def packingNumber (F : Finset (Finset E)) : ℕ :=
  (maximumPacking F).card

omit [DecidableEq E] in
theorem IsPacking.card_le {F P : Finset (Finset E)} (hP : IsPacking F P) :
    P.card ≤ packingNumber F :=
  (maximumPacking_spec F).2 P hP

omit [DecidableEq E] in
theorem IsMaximumPacking.card_eq {F P : Finset (Finset E)}
    (hP : IsMaximumPacking F P) : P.card = packingNumber F := by
  apply Nat.le_antisymm hP.1.card_le
  exact hP.2 _ (maximumPacking_spec F).1

theorem packing_insert {F P : Finset (Finset E)} {T : Finset E}
    (hP : IsPacking F P) (hT : T ∈ F) (hd : Disjoint T (support P)) :
    IsPacking F (insert T P) := by
  refine ⟨insert_subset hT hP.1, ?_⟩
  intro U hU V hV hne
  have hdis : ∀ U ∈ P, Disjoint T U := by
    intro U hU
    exact hd.mono_right (fun e he => mem_support.mpr ⟨U, hU, he⟩)
  simp only [mem_coe, mem_insert] at hU hV
  rcases hU with rfl | hU
  · rcases hV with rfl | hV
    · exact False.elim (hne rfl)
    · exact hdis V hV
  · rcases hV with rfl | hV
    · exact (hdis U hU).symm
    · exact hP.2 hU hV hne

theorem IsMaximumPacking.meets_support {F P : Finset (Finset E)}
    (hP : IsMaximumPacking F P) {T : Finset E} (hT : T ∈ F)
    (hne : T.Nonempty) : (T ∩ support P).Nonempty := by
  by_contra hn
  have hd : Disjoint T (support P) := disjoint_iff_inter_eq_empty.mpr
    (not_nonempty_iff_eq_empty.mp hn)
  have hnot : T ∉ P := by
    intro hmem
    obtain ⟨e, he⟩ := hne
    exact disjoint_left.mp hd he (mem_support.mpr ⟨T, hmem, he⟩)
  have hlt := hP.2 (insert T P) (packing_insert hP.1 hT hd)
  simp [hnot] at hlt

theorem IsMaximumPacking.support_covers {F P : Finset (Finset E)}
    (hP : IsMaximumPacking F P) (hF : ∀ T ∈ F, T.Nonempty) :
    IsCover F (support P) :=
  fun T hT => hP.meets_support hT (hF T hT)

theorem IsPacking.disjoint_support_erase {F P : Finset (Finset E)}
    (hP : IsPacking F P) {S T : Finset E} (hS : S ∈ P)
    (hT : ∀ e ∈ T, e ∈ support P → e ∈ S) :
    Disjoint T (support (P.erase S)) := by
  apply disjoint_left.mpr
  intro e heT heP
  obtain ⟨U, hU, heU⟩ := mem_support.mp heP
  obtain ⟨hUS, hUP⟩ := mem_erase.mp hU
  have heS := hT e heT (mem_support.mpr ⟨U, hUP, heU⟩)
  exact disjoint_left.mp (hP.2 hUP hS hUS) heU heS

/-- Replacing one member of a maximum packing by two disjoint members is impossible. -/
theorem IsMaximumPacking.no_two_for_one {F P : Finset (Finset E)}
    (hP : IsMaximumPacking F P) {S T U : Finset E}
    (hS : S ∈ P) (hT : T ∈ F) (hU : U ∈ F)
    (hneT : T.Nonempty) (hneU : U.Nonempty) (hdTU : Disjoint T U)
    (hdT : Disjoint T (support (P.erase S)))
    (hdU : Disjoint U (support (P.erase S))) : False := by
  have hbase := hP.1.subfamily (erase_subset S P)
  have hfirst := packing_insert hbase hT hdT
  have hsecond : IsPacking F (insert U (insert T (P.erase S))) := by
    apply packing_insert hfirst hU
    rw [support_insert]
    exact disjoint_union_right.mpr ⟨hdTU.symm, hdU⟩
  have ht : T ∉ P.erase S := by
    intro hmem
    obtain ⟨e, he⟩ := hneT
    exact disjoint_left.mp hdT he (mem_support.mpr ⟨T, hmem, he⟩)
  have hu : U ∉ P.erase S := by
    intro hmem
    obtain ⟨e, he⟩ := hneU
    exact disjoint_left.mp hdU he (mem_support.mpr ⟨U, hmem, he⟩)
  have hUT : U ≠ T := by
    rintro rfl
    obtain ⟨e, he⟩ := hneU
    exact disjoint_left.mp hdTU he he
  have hbound := hP.2 _ hsecond
  have hsize := card_erase_add_one hS
  simp only [card_insert_of_notMem ht,
    card_insert_of_notMem (by simp [hu, hUT] : U ∉ insert T (P.erase S))] at hbound
  omega

theorem support_covers (F : Finset (Finset E))
    (hF : ∀ T ∈ F, T.Nonempty) : IsCover F (support F) := by
  intro T hT
  obtain ⟨e, he⟩ := hF T hT
  exact ⟨e, mem_inter.mpr ⟨he, mem_support.mpr ⟨T, hT, he⟩⟩⟩

/-- Minimum transversal size; the theorems below ensure attainment for
families of nonempty edge sets, in particular for triangle families. -/
noncomputable def transversalNumber (F : Finset (Finset E)) : ℕ :=
  sInf {n : ℕ | ∃ C : Finset E, IsCover F C ∧ C.card = n}

theorem IsCover.number_le {F : Finset (Finset E)} {C : Finset E}
    (hC : IsCover F C) : transversalNumber F ≤ C.card := by
  exact csInf_le (OrderBot.bddBelow _) ⟨C, hC, rfl⟩

theorem exists_minimumCover (F : Finset (Finset E))
    (hF : ∀ T ∈ F, T.Nonempty) :
    ∃ C, IsCover F C ∧ C.card = transversalNumber F := by
  have hex : {n : ℕ | ∃ C : Finset E, IsCover F C ∧ C.card = n}.Nonempty :=
    ⟨(support F).card, support F, support_covers F hF, rfl⟩
  exact csInf_mem hex

theorem IsCover.mono {F : Finset (Finset E)} {C D : Finset E}
    (hC : IsCover F C) (hCD : C ⊆ D) : IsCover F D := by
  intro T hT
  obtain ⟨e, he⟩ := hC T hT
  exact ⟨e, mem_inter.mpr ⟨(mem_inter.mp he).1, hCD (mem_inter.mp he).2⟩⟩

theorem IsCover.mono_family {F F' : Finset (Finset E)} {C : Finset E}
    (hC : IsCover F C) (hF : F' ⊆ F) : IsCover F' C :=
  fun T hT => hC T (hF hT)

/-- Extraneous edges never help a transversal: every cover can be restricted
to the edges that actually occur in the family. -/
theorem IsCover.inter_support {F : Finset (Finset E)} {C : Finset E}
    (hC : IsCover F C) : IsCover F (C ∩ support F) := by
  intro T hT
  obtain ⟨e, he⟩ := hC T hT
  obtain ⟨heT, heC⟩ := mem_inter.mp he
  exact ⟨e, mem_inter.mpr ⟨heT,
    mem_inter.mpr ⟨heC, mem_support.mpr ⟨T, hT, heT⟩⟩⟩⟩

theorem exists_minimumCover_subset_support (F : Finset (Finset E))
    (hF : ∀ T ∈ F, T.Nonempty) :
    ∃ C, C ⊆ support F ∧ IsCover F C ∧ C.card = transversalNumber F := by
  obtain ⟨C, hC, hc⟩ := exists_minimumCover F hF
  refine ⟨C ∩ support F, inter_subset_right, hC.inter_support, ?_⟩
  exact Nat.le_antisymm ((card_le_card inter_subset_left).trans_eq hc)
    hC.inter_support.number_le

theorem cover_union_residual {F : Finset (Finset E)} {C D : Finset E}
    (hD : IsCover (residual F C) D) : IsCover F (C ∪ D) := by
  intro T hT
  by_cases hd : Disjoint T C
  · obtain ⟨e, he⟩ := hD T (mem_residual.mpr ⟨hT, hd⟩)
    exact ⟨e, mem_inter.mpr ⟨(mem_inter.mp he).1,
      mem_union_right _ (mem_inter.mp he).2⟩⟩
  · obtain ⟨e, heT, heC⟩ := not_disjoint_iff.mp hd
    exact ⟨e, mem_inter.mpr ⟨heT, mem_union_left _ heC⟩⟩

theorem transversalNumber_le_add_residual (F : Finset (Finset E)) (C : Finset E)
    (hF : ∀ T ∈ F, T.Nonempty) :
    transversalNumber F ≤ C.card + transversalNumber (residual F C) := by
  obtain ⟨D, hD, hcard⟩ := exists_minimumCover (residual F C)
    (fun T hT => hF T (mem_residual.mp hT).1)
  calc
    transversalNumber F ≤ (C ∪ D).card := (cover_union_residual hD).number_le
    _ ≤ C.card + D.card := card_union_le C D
    _ = _ := by rw [hcard]

theorem IsPacking.card_support {F P : Finset (Finset E)} (hP : IsPacking F P) :
    (support P).card = ∑ T ∈ P, T.card := by
  exact card_biUnion hP.2

theorem IsPacking.card_support_uniform {F P : Finset (Finset E)}
    (hP : IsPacking F P) {k : ℕ} (hcard : ∀ T ∈ P, T.card = k) :
    (support P).card = k * P.card := by
  rw [hP.card_support]
  calc
    ∑ T ∈ P, T.card = ∑ _T ∈ P, k := sum_congr rfl hcard
    _ = k * P.card := by simp [Nat.mul_comm]

/-- First maximize the number of members in S, then the total packing size. -/
def IsLexMaximumPacking (F S P : Finset (Finset E)) : Prop :=
  IsPacking F P ∧ ∀ Q, IsPacking F Q →
    (Q ∩ S).card ≤ (P ∩ S).card ∧
    ((Q ∩ S).card = (P ∩ S).card → Q.card ≤ P.card)

theorem exists_lexMaximumPacking (F S : Finset (Finset E)) :
    ∃ P, IsLexMaximumPacking F S P := by
  classical
  let candidates := F.powerset.filter (IsPacking F)
  have hc : (∅ : Finset (Finset E)) ∈ candidates := by
    simp [candidates, packing_empty]
  obtain ⟨P₀, hP₀, hmax₀⟩ := candidates.exists_max_image
    (fun P => (P ∩ S).card) ⟨∅, hc⟩
  let tied := candidates.filter (fun P => (P ∩ S).card = (P₀ ∩ S).card)
  have htied : P₀ ∈ tied := by simp [tied, hP₀]
  obtain ⟨P, hP, hmax⟩ := tied.exists_max_image Finset.card ⟨P₀, htied⟩
  obtain ⟨hPc, hPeq⟩ := mem_filter.mp hP
  refine ⟨P, (mem_filter.mp hPc).2, ?_⟩
  intro Q hQ
  have hQc : Q ∈ candidates := mem_filter.mpr ⟨mem_powerset.mpr hQ.1, hQ⟩
  refine ⟨?_, ?_⟩
  · rw [hPeq]
    exact hmax₀ Q hQc
  · intro hQeq
    exact hmax Q (mem_filter.mpr ⟨hQc, hQeq.trans hPeq⟩)

theorem IsLexMaximumPacking.typePart_maximum {F S P : Finset (Finset E)}
    (hP : IsLexMaximumPacking F S P) (hSF : S ⊆ F) :
    IsMaximumPacking S (P ∩ S) := by
  have hp : IsPacking S (P ∩ S) :=
    ⟨inter_subset_right, fun T hT U hU hne =>
      hP.1.2 (mem_inter.mp hT).1 (mem_inter.mp hU).1 hne⟩
  refine ⟨hp, fun Q hQ => ?_⟩
  have hbound := (hP.2 Q (hQ.mono_family hSF)).1
  simpa [inter_eq_left.mpr hQ.1] using hbound

theorem IsLexMaximumPacking.meets_support {F S P : Finset (Finset E)}
    (hP : IsLexMaximumPacking F S P) {T : Finset E}
    (hT : T ∈ F) (hne : T.Nonempty) : (T ∩ support P).Nonempty := by
  by_contra hn
  have hd : Disjoint T (support P) := disjoint_iff_inter_eq_empty.mpr
    (not_nonempty_iff_eq_empty.mp hn)
  have hnot : T ∉ P := by
    intro hmem
    obtain ⟨e, he⟩ := hne
    exact disjoint_left.mp hd he (mem_support.mpr ⟨T, hmem, he⟩)
  have hins := packing_insert hP.1 hT hd
  have hlex := hP.2 (insert T P) hins
  have hmono : (P ∩ S).card ≤ (insert T P ∩ S).card :=
    card_le_card (inter_subset_inter (subset_insert T P) Subset.rfl)
  have heq := Nat.le_antisymm hlex.1 hmono
  have hcard := hlex.2 heq
  simp [hnot] at hcard

theorem IsLexMaximumPacking.support_covers {F S P : Finset (Finset E)}
    (hP : IsLexMaximumPacking F S P) (hF : ∀ T ∈ F, T.Nonempty) :
    IsCover F (support P) :=
  fun T hT => hP.meets_support hT (hF T hT)

/-- Any packing with the same two optimal counts retains the same maximality. -/
theorem IsLexMaximumPacking.of_same_counts {F S P Q : Finset (Finset E)}
    (hP : IsLexMaximumPacking F S P) (hQ : IsPacking F Q)
    (hfirst : (Q ∩ S).card = (P ∩ S).card) (hsecond : Q.card = P.card) :
    IsLexMaximumPacking F S Q := by
  refine ⟨hQ, fun U hU => ?_⟩
  obtain ⟨hu₁, hu₂⟩ := hP.2 U hU
  rw [hfirst, hsecond]
  exact ⟨hu₁, hu₂⟩

end Tuza

-- ==== Tuza.Basic.Graph

/-! The connection between finite edge families and ordinary finite simple graphs. -/

namespace Tuza

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- All actual triangles whose edges belong to the given edge set. -/
noncomputable def trianglesOn (A : Finset (Sym2 V)) : Finset (Finset (Sym2 V)) := by
  classical
  exact univ.filter (fun T => IsTriangle T ∧ T ⊆ A)

@[simp] theorem mem_trianglesOn {A T : Finset (Sym2 V)} :
    T ∈ trianglesOn A ↔ IsTriangle T ∧ T ⊆ A := by
  classical
  simp [trianglesOn]

theorem trianglesOn_card {A T : Finset (Sym2 V)} (hT : T ∈ trianglesOn A) :
    T.card = 3 := (mem_trianglesOn.mp hT).1.card_eq_three

theorem trianglesOn_nonempty {A T : Finset (Sym2 V)} (hT : T ∈ trianglesOn A) :
    T.Nonempty := card_pos.mp (by rw [trianglesOn_card hT]; decide)

theorem trianglesOn_mono {A B : Finset (Sym2 V)} (h : A ⊆ B) :
    trianglesOn A ⊆ trianglesOn B := by
  intro T hT
  obtain ⟨ht, hta⟩ := mem_trianglesOn.mp hT
  exact mem_trianglesOn.mpr ⟨ht, hta.trans h⟩

/-- Edge deletion removes precisely the triangles meeting a deleted edge. -/
theorem trianglesOn_sdiff (A C : Finset (Sym2 V)) :
    trianglesOn (A \ C) = residual (trianglesOn A) C := by
  ext T
  simp only [mem_trianglesOn, mem_residual]
  constructor
  · rintro ⟨hT, hsub⟩
    refine ⟨⟨hT, fun e he => (mem_sdiff.mp (hsub he)).1⟩, disjoint_left.mpr ?_⟩
    intro e heT heC
    exact (mem_sdiff.mp (hsub heT)).2 heC
  · rintro ⟨⟨hT, hsub⟩, hd⟩
    refine ⟨hT, fun e he => mem_sdiff.mpr ⟨hsub he, ?_⟩⟩
    exact fun heC => disjoint_left.mp hd he heC

/-- The edge set of a finite simple graph. -/
noncomputable def graphEdges (G : SimpleGraph V) : Finset (Sym2 V) := by
  classical
  exact G.edgeSet.toFinset

omit [DecidableEq V] in
@[simp] theorem mem_graphEdges {G : SimpleGraph V} {e : Sym2 V} :
    e ∈ graphEdges G ↔ e ∈ G.edgeSet := by
  classical
  simp [graphEdges]

omit [DecidableEq V] in
@[simp] theorem pair_mem_graphEdges {G : SimpleGraph V} {u v : V} :
    s(u, v) ∈ graphEdges G ↔ G.Adj u v := by
  simp

/-- The family used to define the graph's packing and transversal numbers. -/
noncomputable def graphTriangles (G : SimpleGraph V) : Finset (Finset (Sym2 V)) :=
  trianglesOn (graphEdges G)

/-- Membership means exactly three pairwise adjacent vertices and their three edges. -/
theorem mem_graphTriangles_iff {G : SimpleGraph V} {T : Finset (Sym2 V)} :
    T ∈ graphTriangles G ↔
      ∃ u v w, G.Adj u v ∧ G.Adj u w ∧ G.Adj v w ∧ T = triangleEdges u v w := by
  constructor
  · intro hT
    obtain ⟨⟨u, v, w, huv, huw, hvw, rfl⟩, hsub⟩ := mem_trianglesOn.mp hT
    refine ⟨u, v, w, ?_, ?_, ?_, rfl⟩
    all_goals apply pair_mem_graphEdges.mp; apply hsub; simp
  · rintro ⟨u, v, w, huv, huw, hvw, rfl⟩
    apply mem_trianglesOn.mpr
    refine ⟨isTriangle_triangleEdges huv.ne huw.ne hvw.ne, ?_⟩
    intro e he
    rcases mem_triangleEdges.mp he with rfl | rfl | rfl
    · exact pair_mem_graphEdges.mpr huv
    · exact pair_mem_graphEdges.mpr huw
    · exact pair_mem_graphEdges.mpr hvw

/-- The paper's ν(G). -/
noncomputable def nu (G : SimpleGraph V) : ℕ := packingNumber (graphTriangles G)

/-- The paper's τ(G). -/
noncomputable def tau (G : SimpleGraph V) : ℕ := transversalNumber (graphTriangles G)

/-- The finite-family cover condition is exactly the usual requirement on
every triple of pairwise adjacent vertices. -/
theorem graph_cover_iff_adj (G : SimpleGraph V) (C : Finset (Sym2 V)) :
    IsCover (graphTriangles G) C ↔
      ∀ u v w, G.Adj u v → G.Adj u w → G.Adj v w →
        s(u, v) ∈ C ∨ s(u, w) ∈ C ∨ s(v, w) ∈ C := by
  constructor
  · intro hC u v w huv huw hvw
    obtain ⟨e, he⟩ := hC (triangleEdges u v w)
      (mem_graphTriangles_iff.mpr ⟨u, v, w, huv, huw, hvw, rfl⟩)
    obtain ⟨heT, heC⟩ := mem_inter.mp he
    rcases mem_triangleEdges.mp heT with rfl | rfl | rfl
    · exact Or.inl heC
    · exact Or.inr (Or.inl heC)
    · exact Or.inr (Or.inr heC)
  · intro hC T hT
    obtain ⟨u, v, w, huv, huw, hvw, rfl⟩ := mem_graphTriangles_iff.mp hT
    rcases hC u v w huv huw hvw with he | he | he
    · exact ⟨s(u, v), mem_inter.mpr ⟨by simp, he⟩⟩
    · exact ⟨s(u, w), mem_inter.mpr ⟨by simp, he⟩⟩
    · exact ⟨s(v, w), mem_inter.mpr ⟨by simp, he⟩⟩

theorem graphTriangles_support_subset (G : SimpleGraph V) :
    support (graphTriangles G) ⊆ graphEdges G := by
  intro e he
  obtain ⟨T, hT, heT⟩ := mem_support.mp he
  exact (mem_trianglesOn.mp hT).2 heT

/-- A minimum cover can be chosen from the graph's edges. -/
theorem exists_graph_minimumCover (G : SimpleGraph V) :
    ∃ C, C ⊆ graphEdges G ∧ IsCover (graphTriangles G) C ∧ C.card = tau G := by
  obtain ⟨C, hsub, hC, hc⟩ := exists_minimumCover_subset_support (graphTriangles G)
    (fun _ hT => trianglesOn_nonempty hT)
  exact ⟨C, hsub.trans (graphTriangles_support_subset G), hC, hc⟩

end Tuza

-- ==== Tuza.Books.Families

/-! Finite page choices in books. -/

namespace Tuza

namespace Books

open Finset

variable {E I : Type*} [DecidableEq E] [Fintype I]

/-- One page is selected for each index. -/
def ChoosesPages (pages : I → Finset (Finset E)) (f : I → Finset E) : Prop :=
  ∀ i, f i ∈ pages i

/-- The family obtained by choosing one page from each book. -/
def choice (f : I → Finset E) : Finset (Finset E) :=
  Finset.univ.image f

@[simp] theorem mem_choice {f : I → Finset E} {T : Finset E} :
    T ∈ choice f ↔ ∃ i, f i = T := by
  simp [choice]

/-- Distinct books may share original vertices, but not edges. -/
def DisjointSupports (pages : I → Finset (Finset E)) : Prop :=
  Pairwise (fun i j => Disjoint (support (pages i)) (support (pages j)))

omit [Fintype I] in
theorem page_subset_support {pages : I → Finset (Finset E)} {i : I}
    {T : Finset E} (hT : T ∈ pages i) : T ⊆ support (pages i) := by
  intro e he
  exact mem_support.mpr ⟨T, hT, he⟩

omit [Fintype I] in
theorem choices_pairwise_disjoint {pages : I → Finset (Finset E)}
    (hd : DisjointSupports pages) {f : I → Finset E}
    (hf : ChoosesPages pages f) : Pairwise (fun i j => Disjoint (f i) (f j)) := by
  intro i j hij
  exact (hd hij).mono (page_subset_support (hf i)) (page_subset_support (hf j))

omit [Fintype I] in
/-- Nonempty pages in different books cannot become the same chosen page. -/
theorem choice_injective {pages : I → Finset (Finset E)}
    (hd : DisjointSupports pages)
    (hne : ∀ i T, T ∈ pages i → T.Nonempty) {f : I → Finset E}
    (hf : ChoosesPages pages f) : Function.Injective f := by
  intro i j hij
  by_contra hneij
  have hdis := choices_pairwise_disjoint hd hf hneij
  obtain ⟨e, he⟩ := hne i (f i) (hf i)
  exact Finset.disjoint_left.mp hdis he (hij ▸ he)

theorem card_choice {pages : I → Finset (Finset E)}
    (hd : DisjointSupports pages)
    (hne : ∀ i T, T ∈ pages i → T.Nonempty) {f : I → Finset E}
    (hf : ChoosesPages pages f) : (choice f).card = Fintype.card I := by
  rw [choice, Finset.card_image_of_injective _ (choice_injective hd hne hf)]
  exact Finset.card_univ

/-- Every page choice is a packing when all pages belong to the family and
the supports of distinct books are disjoint. -/
theorem choice_isPacking {F : Finset (Finset E)}
    {pages : I → Finset (Finset E)}
    (hF : ∀ i, pages i ⊆ F) (hd : DisjointSupports pages)
    {f : I → Finset E} (hf : ChoosesPages pages f) :
    IsPacking F (choice f) := by
  refine ⟨?_, ?_⟩
  · intro T hT
    obtain ⟨i, rfl⟩ := mem_choice.mp hT
    exact hF i (hf i)
  · intro T hT U hU hTU
    obtain ⟨i, rfl⟩ := mem_choice.mp hT
    obtain ⟨j, rfl⟩ := mem_choice.mp hU
    apply choices_pairwise_disjoint hd hf
    intro hij
    exact hTU (congrArg f hij)

/-- A known upper bound on every packing makes all full page choices maximum. -/
theorem choice_isMaximumPacking {F : Finset (Finset E)}
    {pages : I → Finset (Finset E)}
    (hF : ∀ i, pages i ⊆ F) (hd : DisjointSupports pages)
    (hne : ∀ i T, T ∈ pages i → T.Nonempty)
    (hbound : ∀ P, IsPacking F P → P.card ≤ Fintype.card I)
    {f : I → Finset E} (hf : ChoosesPages pages f) :
    IsMaximumPacking F (choice f) := by
  refine ⟨choice_isPacking hF hd hf, ?_⟩
  intro P hP
  rw [card_choice hd hne hf]
  exact hbound P hP

/-- Every page choice meets each member of the family. -/
def EveryChoiceMeets (F : Finset (Finset E))
    (pages : I → Finset (Finset E)) : Prop :=
  ∀ f, ChoosesPages pages f → ∀ T ∈ F, ∃ i, ¬ Disjoint T (f i)

/-- Maximum page choices give the required maximality when family members
are nonempty. -/
theorem everyChoiceMeets_of_maximum {F : Finset (Finset E)}
    {pages : I → Finset (Finset E)}
    (hne : ∀ T ∈ F, T.Nonempty)
    (hmax : ∀ f, ChoosesPages pages f → IsMaximumPacking F (choice f)) :
    EveryChoiceMeets F pages := by
  intro f hf T hT
  obtain ⟨e, he⟩ := (hmax f hf).meets_support hT (hne T hT)
  obtain ⟨U, hU, heU⟩ := mem_support.mp (Finset.mem_inter.mp he).2
  obtain ⟨i, rfl⟩ := mem_choice.mp hU
  refine ⟨i, ?_⟩
  intro hdis
  exact Finset.disjoint_left.mp hdis (Finset.mem_inter.mp he).1 heU

/-- If every full page choice meets a family member, one book has all its
pages meeting that member. -/
theorem exists_book_all_pages_meet {F : Finset (Finset E)}
    {pages : I → Finset (Finset E)} (hchoice : EveryChoiceMeets F pages)
    {T : Finset E} (hT : T ∈ F) :
    ∃ i, ∀ U ∈ pages i, ¬ Disjoint T U := by
  classical
  by_contra hnone
  push Not at hnone
  choose f hf hdis using hnone
  obtain ⟨i, hi⟩ := hchoice f hf T hT
  exact hi (hdis i)

theorem exists_book_all_pages_meet_of_maximum {F : Finset (Finset E)}
    {pages : I → Finset (Finset E)}
    (hne : ∀ T ∈ F, T.Nonempty)
    (hmax : ∀ f, ChoosesPages pages f → IsMaximumPacking F (choice f))
    {T : Finset E} (hT : T ∈ F) :
    ∃ i, ∀ U ∈ pages i, ¬ Disjoint T U :=
  exists_book_all_pages_meet (everyChoiceMeets_of_maximum hne hmax) hT

end Books

end Tuza

-- ==== Tuza.Books.Cover

/-!
Books with one to three pages and their covers: Lemma 2.2.

A two-page cover includes the opposite vertex pair. Restricting the cover to the
graph's edges preserves coverage and can only reduce its size.
-/

namespace Tuza

open Finset
open scoped BigOperators

variable {V : Type*}

/-- Books with one, two, or three distinct pages and their actual vertices. -/
inductive Book (V : Type*) where
  | single (u v x : V) (vertices : [u, v, x].Nodup)
  | double (u v x y : V) (vertices : [u, v, x, y].Nodup)
  | triple (u v x y z : V) (vertices : [u, v, x, y, z].Nodup)

namespace Book

def spine : Book V → Sym2 V
  | .single u v _ _ => s(u, v)
  | .double u v _ _ _ => s(u, v)
  | .triple u v _ _ _ _ => s(u, v)

/-- Only a two-page book has an opposite edge relevant to its cover. -/
def opposite : Book V → Option (Sym2 V)
  | .single .. => none
  | .double _ _ x y _ => some s(x, y)
  | .triple .. => none

def pageCount : Book V → ℕ
  | .single .. => 1
  | .double .. => 2
  | .triple .. => 3

variable [DecidableEq V]

def pages : Book V → Finset (Finset (Sym2 V))
  | .single u v x _ => {triangleEdges u v x}
  | .double u v x y _ => {triangleEdges u v x, triangleEdges u v y}
  | .triple u v x y z _ =>
      {triangleEdges u v x, triangleEdges u v y, triangleEdges u v z}

def cover : Book V → Finset (Sym2 V)
  | .single u v x _ => triangleEdges u v x
  | .double u v x y _ => {s(u, v), s(x, y)}
  | .triple u v _ _ _ _ => {s(u, v)}

omit [DecidableEq V] in
@[simp] theorem opposite_double (u v x y : V) (h : [u, v, x, y].Nodup) :
    (Book.double u v x y h).opposite = some s(x, y) := rfl

@[simp] theorem cover_double (u v x y : V) (h : [u, v, x, y].Nodup) :
    (Book.double u v x y h).cover = {s(u, v), s(x, y)} := rfl

private theorem pages_ne {u v x y : V} (h : [u, v, x, y].Nodup) :
    triangleEdges u v x ≠ triangleEdges u v y := by
  have hd : u ≠ v ∧ u ≠ x ∧ u ≠ y ∧ v ≠ x ∧ v ≠ y ∧ x ≠ y := by
    simpa [List.nodup_cons, and_assoc] using h
  intro heq
  have hx : s(u, x) ∈ triangleEdges u v y := heq ▸ (by simp)
  simp only [mem_triangleEdges, Sym2.eq_iff] at hx
  aesop

theorem pages_nonempty (b : Book V) : b.pages.Nonempty := by
  cases b <;> simp [pages]

theorem pages_card (b : Book V) : b.pages.card = b.pageCount := by
  cases b with
  | single u v x h => simp [pages, pageCount]
  | double u v x y h => simp [pages, pageCount, pages_ne h]
  | triple u v x y z h =>
    have hxy : [u, v, x, y].Nodup := by simp_all [List.nodup_cons]
    have hxz : [u, v, x, z].Nodup := by simp_all [List.nodup_cons]
    have hyz : [u, v, y, z].Nodup := by simp_all [List.nodup_cons]
    simp [pages, pageCount, pages_ne hxy, pages_ne hxz, pages_ne hyz]

theorem pages_card_le_three (b : Book V) : b.pages.card ≤ 3 := by
  rw [pages_card]
  cases b <;> simp [pageCount]

theorem cover_card_add_pages_card_le_four (b : Book V) :
    b.cover.card + b.pages.card ≤ 4 := by
  rw [pages_card]
  cases b with
  | single u v x h =>
    have huv : u ≠ v := by simp_all [List.nodup_cons]
    have hux : u ≠ x := by simp_all [List.nodup_cons]
    have hvx : v ≠ x := by simp_all [List.nodup_cons]
    simp [cover, pageCount, triangleEdges_card huv hux hvx]
  | double u v x y h =>
    have hc : ({s(u, v), s(x, y)} : Finset (Sym2 V)).card ≤ 2 := card_le_two
    simp only [cover, pageCount]
    omega
  | triple u v x y z h => simp [cover, pageCount]

/-- Meeting every page of an actual book forces a triangle to meet its cover. -/
theorem meets_cover (b : Book V) {T : Finset (Sym2 V)} (hT : IsTriangle T)
    (hmeet : ∀ U ∈ b.pages, (T ∩ U).Nonempty) : (T ∩ b.cover).Nonempty := by
  cases b with
  | single u v x h => exact hmeet (triangleEdges u v x) (by simp [pages])
  | double u v x y h =>
    by_cases he : s(u, v) ∈ T
    · exact ⟨s(u, v), mem_inter.mpr ⟨he, by simp [cover]⟩⟩
    · have hop := two_page_opposite_mem hT h he
        (hmeet (triangleEdges u v x) (by simp [pages]))
        (hmeet (triangleEdges u v y) (by simp [pages]))
      exact ⟨s(x, y), mem_inter.mpr ⟨hop, by simp [cover]⟩⟩
  | triple u v x y z h =>
    have he := three_page_spine hT h
      (hmeet (triangleEdges u v x) (by simp [pages]))
      (hmeet (triangleEdges u v y) (by simp [pages]))
      (hmeet (triangleEdges u v z) (by simp [pages]))
    exact ⟨s(u, v), mem_inter.mpr ⟨he, by simp [cover]⟩⟩

theorem meets_cover_of_not_disjoint (b : Book V) {T : Finset (Sym2 V)}
    (hT : IsTriangle T) (hmeet : ∀ U ∈ b.pages, ¬ Disjoint T U) :
    (T ∩ b.cover).Nonempty := by
  apply b.meets_cover hT
  intro U hU
  obtain ⟨e, heT, heU⟩ := not_disjoint_iff.mp (hmeet U hU)
  exact ⟨e, mem_inter.mpr ⟨heT, heU⟩⟩

/-- Every nonempty family of at most three actual triangles with a common edge
has one of the three book representations above, with that precise spine. -/
theorem exists_representation (S : Finset (Finset (Sym2 V))) (e : Sym2 V)
    (hne : S.Nonempty) (hcard : S.card ≤ 3)
    (htri : ∀ T ∈ S, IsTriangle T) (hspine : ∀ T ∈ S, e ∈ T) :
    ∃ b : Book V, b.pages = S ∧ b.spine = e := by
  obtain ⟨u, v, rfl⟩ : ∃ u v, e = s(u, v) :=
    Sym2.inductionOn e (fun u v => ⟨u, v, rfl⟩)
  have huv : u ≠ v := by
    obtain ⟨T, hT⟩ := hne
    exact (htri T hT).ne_of_mem (hspine T hT)
  have hr (T : Finset (Sym2 V)) (hT : T ∈ S) :
      ∃ x, u ≠ x ∧ v ≠ x ∧ T = triangleEdges u v x :=
    (htri T hT).exists_third_of_mem (hspine T hT)
  have hcpos : 0 < S.card := card_pos.mpr hne
  have hc : S.card = 1 ∨ S.card = 2 ∨ S.card = 3 := by omega
  rcases hc with hc | hc | hc
  · obtain ⟨T, rfl⟩ := card_eq_one.mp hc
    obtain ⟨x, hux, hvx, rfl⟩ := hr T (by simp)
    have hv : [u, v, x].Nodup := by simp [List.nodup_cons, huv, hux, hvx]
    exact ⟨.single u v x hv, rfl, rfl⟩
  · obtain ⟨T, U, hTU, rfl⟩ := card_eq_two.mp hc
    obtain ⟨x, hux, hvx, rfl⟩ := hr T (by simp)
    obtain ⟨y, huy, hvy, rfl⟩ := hr U (by simp)
    have hxy : x ≠ y := by rintro rfl; exact hTU rfl
    have hv : [u, v, x, y].Nodup := by
      simp [List.nodup_cons, huv, hux, huy, hvx, hvy, hxy]
    exact ⟨.double u v x y hv, rfl, rfl⟩
  · obtain ⟨T, U, W, hTU, hTW, hUW, rfl⟩ := card_eq_three.mp hc
    obtain ⟨x, hux, hvx, rfl⟩ := hr T (by simp)
    obtain ⟨y, huy, hvy, rfl⟩ := hr U (by simp)
    obtain ⟨z, huz, hvz, rfl⟩ := hr W (by simp)
    have hxy : x ≠ y := by rintro rfl; exact hTU rfl
    have hxz : x ≠ z := by rintro rfl; exact hTW rfl
    have hyz : y ≠ z := by rintro rfl; exact hUW rfl
    have hv : [u, v, x, y, z].Nodup := by
      simp [List.nodup_cons, huv, hux, huy, huz, hvx, hvy, hvz, hxy, hxz, hyz]
    exact ⟨.triple u v x y z hv, rfl, rfl⟩

theorem pages_card_of_opposite {b : Book V} {e : Sym2 V}
    (hop : b.opposite = some e) : b.pages.card = 2 := by
  rw [b.pages_card]
  cases b <;> simp_all [Book.opposite, Book.pageCount]

end Book

variable [DecidableEq V] {I : Type*} [Fintype I]

/-- The union of the actual per-book covers, counting repeated edges only once. -/
def bookFamilyCover (books : I → Book V) : Finset (Sym2 V) :=
  univ.biUnion (fun i => (books i).cover)

theorem bookFamilyCover_covers (books : I → Book V)
    (F : Finset (Finset (Sym2 V))) (htri : ∀ T ∈ F, IsTriangle T)
    (hmeet : ∀ T ∈ F, ∃ i, ∀ U ∈ (books i).pages, ¬ Disjoint T U) :
    IsCover F (bookFamilyCover books) := by
  intro T hT
  obtain ⟨i, hi⟩ := hmeet T hT
  obtain ⟨e, he⟩ := (books i).meets_cover_of_not_disjoint (htri T hT) hi
  exact ⟨e, mem_inter.mpr ⟨(mem_inter.mp he).1,
    mem_biUnion.mpr ⟨i, mem_univ _, (mem_inter.mp he).2⟩⟩⟩

theorem bookFamilyCover_card (books : I → Book V) :
    (bookFamilyCover books).card + (∑ i, (books i).pages.card) ≤
      4 * Fintype.card I := by
  have hu : (bookFamilyCover books).card ≤ ∑ i, (books i).cover.card :=
    card_biUnion_le
  have hs : (∑ i, (books i).cover.card) + (∑ i, (books i).pages.card) ≤
      4 * Fintype.card I := by
    rw [← sum_add_distrib]
    calc
      (∑ i, ((books i).cover.card + (books i).pages.card)) ≤ ∑ _i : I, 4 :=
        sum_le_sum (fun i _ => (books i).cover_card_add_pages_card_le_four)
      _ = 4 * Fintype.card I := by simp [Nat.mul_comm]
  omega

/-- Represent each page family as a book and combine the book covers. -/
theorem exists_cover_of_small_common_spine_books
    (F : Finset (Finset (Sym2 V))) (pages : I → Finset (Finset (Sym2 V)))
    (hne : ∀ i, (pages i).Nonempty) (hcard : ∀ i, (pages i).card ≤ 3)
    (hpages : ∀ i T, T ∈ pages i → IsTriangle T)
    (hspine : ∀ i, ∃ e, ∀ T ∈ pages i, e ∈ T)
    (htri : ∀ T ∈ F, IsTriangle T) (hchoice : Books.EveryChoiceMeets F pages) :
    ∃ C : Finset (Sym2 V), IsCover F C ∧
      C.card + (∑ i, (pages i).card) ≤ 4 * Fintype.card I := by
  classical
  choose spine hs using hspine
  have hb (i : I) : ∃ b : Book V, b.pages = pages i ∧ b.spine = spine i :=
    Book.exists_representation (pages i) (spine i) (hne i) (hcard i) (hpages i) (hs i)
  choose books hbpages hbspine using hb
  refine ⟨bookFamilyCover books, ?_, ?_⟩
  · apply bookFamilyCover_covers books F htri
    intro T hT
    obtain ⟨i, hi⟩ := Books.exists_book_all_pages_meet hchoice hT
    exact ⟨i, by simpa only [hbpages i] using hi⟩
  · simpa only [hbpages] using bookFamilyCover_card books

end Tuza

-- ==== Tuza.Basic.Coloring

/-! Red and blue edges in finite families of three-edge sets. -/

namespace Tuza

open Finset

variable {E : Type*} [DecidableEq E]

/-- The red edges used by a family. -/
def redEdges (R : Finset E) (P : Finset (Finset E)) : Finset E :=
  support P ∩ R

/-- Every edge outside the specified red set is blue. -/
def blueEdges (R : Finset E) (P : Finset (Finset E)) : Finset E :=
  support P \ R

/-- Each member has exactly three edges, exactly one of which is red. -/
def ColoredFamily (F : Finset (Finset E)) (R : Finset E) : Prop :=
  ∀ T ∈ F, T.card = 3 ∧ (T ∩ R).card = 1

@[simp] theorem mem_redEdges {R : Finset E} {P : Finset (Finset E)} {e : E} :
    e ∈ redEdges R P ↔ e ∈ support P ∧ e ∈ R := by
  simp [redEdges]

@[simp] theorem mem_blueEdges {R : Finset E} {P : Finset (Finset E)} {e : E} :
    e ∈ blueEdges R P ↔ e ∈ support P ∧ e ∉ R := by
  simp [blueEdges]

theorem redEdges_subset_support (R : Finset E) (P : Finset (Finset E)) :
    redEdges R P ⊆ support P := inter_subset_left

theorem blueEdges_subset_support (R : Finset E) (P : Finset (Finset E)) :
    blueEdges R P ⊆ support P := sdiff_subset

@[simp] theorem redEdges_union_blueEdges (R : Finset E) (P : Finset (Finset E)) :
    redEdges R P ∪ blueEdges R P = support P := by
  ext e
  by_cases he : e ∈ R <;> simp [redEdges, blueEdges, he]

theorem card_blueEdges_add_card_redEdges (R : Finset E) (P : Finset (Finset E)) :
    (blueEdges R P).card + (redEdges R P).card = (support P).card := by
  exact card_sdiff_add_card_inter (support P) R

theorem redEdges_eq_biUnion (R : Finset E) (P : Finset (Finset E)) :
    redEdges R P = P.biUnion (fun T => T ∩ R) := by
  ext e
  constructor
  · intro he
    obtain ⟨heP, heR⟩ := mem_redEdges.mp he
    obtain ⟨T, hT, heT⟩ := mem_support.mp heP
    exact mem_biUnion.mpr ⟨T, hT, mem_inter.mpr ⟨heT, heR⟩⟩
  · intro he
    obtain ⟨T, hT, heTR⟩ := mem_biUnion.mp he
    obtain ⟨heT, heR⟩ := mem_inter.mp heTR
    exact mem_redEdges.mpr ⟨mem_support.mpr ⟨T, hT, heT⟩, heR⟩

theorem ColoredFamily.subfamily {F F' : Finset (Finset E)} {R : Finset E}
    (hF : ColoredFamily F R) (hsub : F' ⊆ F) : ColoredFamily F' R :=
  fun T hT => hF T (hsub hT)

theorem ColoredFamily.residual {F : Finset (Finset E)} {R C : Finset E}
    (hF : ColoredFamily F R) : ColoredFamily (residual F C) R :=
  hF.subfamily (filter_subset _ _)

theorem ColoredFamily.member_nonempty {F : Finset (Finset E)} {R T : Finset E}
    (hF : ColoredFamily F R) (hT : T ∈ F) : T.Nonempty := by
  apply card_pos.mp
  rw [(hF T hT).1]
  decide

theorem ColoredFamily.member_blue_card {F : Finset (Finset E)} {R T : Finset E}
    (hF : ColoredFamily F R) (hT : T ∈ F) : (T \ R).card = 2 := by
  have hsum := card_sdiff_add_card_inter T R
  obtain ⟨hthree, hone⟩ := hF T hT
  omega

theorem ColoredFamily.red_eq_singleton {F : Finset (Finset E)} {R T : Finset E}
    {e : E} (hF : ColoredFamily F R) (hT : T ∈ F) (heT : e ∈ T) (heR : e ∈ R) :
    T ∩ R = {e} := by
  obtain ⟨r, hr⟩ := card_eq_one.mp (hF T hT).2
  have he : e ∈ ({r} : Finset E) := hr ▸ mem_inter.mpr ⟨heT, heR⟩
  have her : e = r := mem_singleton.mp he
  subst e
  exact hr

/-- Different members of a packing have different singleton red intersections. -/
theorem IsPacking.red_inter_injective {F P : Finset (Finset E)} {R : Finset E}
    (hP : IsPacking F P) (hF : ColoredFamily F R) {T U : Finset E}
    (hT : T ∈ P) (hU : U ∈ P) (heq : T ∩ R = U ∩ R) : T = U := by
  by_contra hne
  have hn : (T ∩ R).Nonempty := card_pos.mp (by rw [(hF T (hP.1 hT)).2]; decide)
  obtain ⟨e, he⟩ := hn
  have heU : e ∈ U ∩ R := heq ▸ he
  exact disjoint_left.mp (hP.2 hT hU hne) (mem_inter.mp he).1 (mem_inter.mp heU).1

theorem IsPacking.card_redEdges {F P : Finset (Finset E)} {R : Finset E}
    (hP : IsPacking F P) (hF : ColoredFamily F R) :
    (redEdges R P).card = P.card := by
  rw [redEdges_eq_biUnion]
  have hd : (P : Set (Finset E)).Pairwise
      (fun T U => Disjoint (T ∩ R) (U ∩ R)) := by
    intro T hT U hU hne
    exact (hP.2 hT hU hne).mono inter_subset_left inter_subset_left
  rw [card_biUnion hd]
  calc
    ∑ T ∈ P, (T ∩ R).card = ∑ _T ∈ P, 1 := by
      apply sum_congr rfl
      intro T hT
      exact (hF T (hP.1 hT)).2
    _ = P.card := by simp

theorem IsPacking.card_blueEdges {F P : Finset (Finset E)} {R : Finset E}
    (hP : IsPacking F P) (hF : ColoredFamily F R) :
    (blueEdges R P).card = 2 * P.card := by
  have hsum := card_blueEdges_add_card_redEdges R P
  have hred := hP.card_redEdges hF
  have hsupport := hP.card_support_uniform (fun T hT => (hF T (hP.1 hT)).1)
  omega

/-- A residual member meets the parent support precisely in its unique red
edge. Maximality supplies a nonempty intersection; the color count identifies it. -/
theorem residual_inter_support_eq_inter_red {F P : Finset (Finset E)}
    {R T : Finset E} (hF : ColoredFamily F R) (hP : IsMaximumPacking F P)
    (hT : T ∈ residual F (blueEdges R P)) : T ∩ support P = T ∩ R := by
  obtain ⟨hTF, hdis⟩ := mem_residual.mp hT
  have hsub : T ∩ support P ⊆ T ∩ R := by
    intro e he
    obtain ⟨heT, heP⟩ := mem_inter.mp he
    refine mem_inter.mpr ⟨heT, ?_⟩
    by_contra heR
    exact disjoint_left.mp hdis heT (mem_blueEdges.mpr ⟨heP, heR⟩)
  apply Subset.antisymm hsub
  intro e he
  obtain ⟨f, hf⟩ := hP.meets_support hTF (hF.member_nonempty hTF)
  have hsmall : (T ∩ R).card ≤ 1 := by rw [(hF T hTF).2]
  have hef : e = f := card_le_one.mp hsmall e he f (hsub hf)
  subst e
  exact hf

theorem residual_red_subset_parent_red {F P : Finset (Finset E)} {R T : Finset E}
    (hF : ColoredFamily F R) (hP : IsMaximumPacking F P)
    (hT : T ∈ residual F (blueEdges R P)) : T ∩ R ⊆ redEdges R P := by
  intro e he
  have heP : e ∈ T ∩ support P :=
    (residual_inter_support_eq_inter_red hF hP hT).symm ▸ he
  exact mem_redEdges.mpr ⟨(mem_inter.mp heP).2, (mem_inter.mp he).2⟩

/-- Blue residual edges avoid the parent support. -/
theorem IsPacking.blueEdges_disjoint_parent_support {F P Q : Finset (Finset E)}
    {R : Finset E} (hQ : IsPacking (residual F (blueEdges R P)) Q) :
    Disjoint (blueEdges R Q) (support P) := by
  apply disjoint_left.mpr
  intro e heQ heP
  obtain ⟨heQ, heR⟩ := mem_blueEdges.mp heQ
  obtain ⟨T, hT, heT⟩ := mem_support.mp heQ
  have hdis := (mem_residual.mp (hQ.1 hT)).2
  exact disjoint_left.mp hdis heT (mem_blueEdges.mpr ⟨heP, heR⟩)

/-- Packing members whose red edge occurs in no other member of the family. -/
noncomputable def privateRedPages (F : Finset (Finset E)) (R : Finset E)
    (P : Finset (Finset E)) : Finset (Finset E) := by
  classical
  exact P.filter (fun T => ∀ U ∈ F, U ∩ R = T ∩ R → U = T)

@[simp] theorem mem_privateRedPages {F P : Finset (Finset E)} {R T : Finset E} :
    T ∈ privateRedPages F R P ↔ T ∈ P ∧ ∀ U ∈ F, U ∩ R = T ∩ R → U = T := by
  classical
  simp [privateRedPages]

theorem privateRedPages_subset (F : Finset (Finset E)) (R : Finset E)
    (P : Finset (Finset E)) : privateRedPages F R P ⊆ P := by
  intro T hT
  exact (mem_privateRedPages.mp hT).1

/-- A cover may omit these private red edges if it contains the corresponding
blue edges. Only their own triangles could lose a selected red edge. -/
theorem IsCover.sdiff_privateRed {F P U : Finset (Finset E)} {R C : Finset E}
    (hC : IsCover F C) (hF : ColoredFamily F R) (hP : IsPacking F P)
    (hU : U ⊆ privateRedPages F R P) (hblue : blueEdges R U ⊆ C) :
    IsCover F (C \ redEdges R U) := by
  intro T hT
  obtain ⟨e, he⟩ := hC T hT
  obtain ⟨heT, heC⟩ := mem_inter.mp he
  by_cases heU : e ∈ redEdges R U
  · obtain ⟨heSupport, heR⟩ := mem_redEdges.mp heU
    obtain ⟨S, hS, heS⟩ := mem_support.mp heSupport
    obtain ⟨hSP, hprivate⟩ := mem_privateRedPages.mp (hU hS)
    have hTS : T = S := hprivate T hT
      ((hF.red_eq_singleton hT heT heR).trans
        (hF.red_eq_singleton (hP.1 hSP) heS heR).symm)
    subst T
    have hblueCard := hF.member_blue_card (hP.1 hSP)
    obtain ⟨f, hf⟩ := card_pos.mp (show 0 < (S \ R).card by omega)
    obtain ⟨hfS, hfR⟩ := mem_sdiff.mp hf
    have hfC := hblue (mem_blueEdges.mpr ⟨mem_support.mpr ⟨S, hS, hfS⟩, hfR⟩)
    exact ⟨f, mem_inter.mpr ⟨hfS, mem_sdiff.mpr ⟨hfC,
      fun hfRed => hfR (mem_redEdges.mp hfRed).2⟩⟩⟩
  · exact ⟨e, mem_inter.mpr ⟨heT, mem_sdiff.mpr ⟨heC, heU⟩⟩⟩

theorem card_sdiff_privateRed {F P U : Finset (Finset E)} {R C : Finset E}
    (hF : ColoredFamily F R) (hP : IsPacking F P)
    (hU : U ⊆ privateRedPages F R P) (hred : redEdges R U ⊆ C) :
    (C \ redEdges R U).card + U.card = C.card := by
  have hpack := hP.subfamily (hU.trans (privateRedPages_subset F R P))
  have hcard := card_sdiff_add_card_inter C (redEdges R U)
  rw [inter_eq_right.mpr hred, hpack.card_redEdges hF] at hcard
  exact hcard

/-- The second colored cover is the parent blue edges and a residual maximum
packing, with every residual-private red edge deleted. -/
theorem second_colored_cover {F P Q : Finset (Finset E)} {R : Finset E}
    (hF : ColoredFamily F R) (hP : IsPacking F P)
    (hQ : IsMaximumPacking (residual F (blueEdges R P)) Q) :
    transversalNumber F + (privateRedPages (residual F (blueEdges R P)) R Q).card
      ≤ 2 * P.card + 3 * Q.card := by
  let S := residual F (blueEdges R P)
  let U := privateRedPages S R Q
  have hS : ColoredFamily S R := hF.residual
  have hU : U ⊆ privateRedPages S R Q := Subset.refl _
  have hUP : U ⊆ Q := privateRedPages_subset S R Q
  have hcover : IsCover S (support Q) :=
    hQ.support_covers (fun _ hT => hS.member_nonempty hT)
  have hblue : blueEdges R U ⊆ support Q :=
    (blueEdges_subset_support _ _).trans (support_mono hUP)
  have hred : redEdges R U ⊆ support Q :=
    (redEdges_subset_support _ _).trans (support_mono hUP)
  have hremoved := hcover.sdiff_privateRed hS hQ.1 hU hblue
  have hsize := card_sdiff_privateRed hS hQ.1 hU hred
  have hQsize := hQ.1.card_support_uniform (fun T hT => (hS T (hQ.1.1 hT)).1)
  have hPblue := hP.card_blueEdges hF
  have hbound := (cover_union_residual hremoved).number_le
  have hunion := card_union_le (blueEdges R P) (support Q \ redEdges R U)
  change transversalNumber F + U.card ≤ _
  omega

end Tuza

-- ==== Tuza.Books.Layered

/-!
Two-layer books obtained by pairing a maximum packing with a residual packing.
-/

namespace Tuza
namespace Layered

open Finset

variable {E : Type*} [DecidableEq E]

noncomputable def pairedParents (R : Finset E) (P Q : Finset (Finset E)) :
    Finset (Finset E) := by
  classical
  exact P.filter (fun p => ∃ q ∈ Q, p ∩ R = q ∩ R)

def children (R : Finset E) (Q : Finset (Finset E)) (p : Finset E) :
    Finset (Finset E) := Q.filter (fun q => q ∩ R = p ∩ R)

def twoLayerPages (R : Finset E) (P Q : Finset (Finset E))
    (p : {T // T ∈ P}) : Finset (Finset E) := insert p.val (children R Q p.val)

@[simp] theorem mem_pairedParents {R : Finset E} {P Q : Finset (Finset E)}
    {p : Finset E} :
    p ∈ pairedParents R P Q ↔ p ∈ P ∧ ∃ q ∈ Q, p ∩ R = q ∩ R := by
  classical
  simp [pairedParents]

@[simp] theorem mem_children {R : Finset E} {Q : Finset (Finset E)}
    {p q : Finset E} : q ∈ children R Q p ↔ q ∈ Q ∧ q ∩ R = p ∩ R := by
  simp [children]

@[simp] theorem mem_twoLayerPages {R : Finset E} {P Q : Finset (Finset E)}
    {p : {T // T ∈ P}} {T : Finset E} :
    T ∈ twoLayerPages R P Q p ↔ T = p.val ∨ (T ∈ Q ∧ T ∩ R = p.val ∩ R) := by
  simp [twoLayerPages]

theorem pairedParents_subset (R : Finset E) (P Q : Finset (Finset E)) :
    pairedParents R P Q ⊆ P := by
  intro p hp
  exact (mem_pairedParents.mp hp).1

variable {F P Q : Finset (Finset E)} {R : Finset E}

theorem exists_parent (hF : ColoredFamily F R) (hP : IsMaximumPacking F P)
    (hQ : IsPacking (residual F (blueEdges R P)) Q) (q : {T // T ∈ Q}) :
    ∃ p : {T // T ∈ P}, p.val ∩ R = q.val ∩ R := by
  have hq := hQ.1 q.property
  have hqF := (mem_residual.mp hq).1
  have hn : (q.val ∩ R).Nonempty := card_pos.mp (by rw [(hF q.val hqF).2]; decide)
  obtain ⟨e, he⟩ := hn
  have heP := residual_red_subset_parent_red hF hP hq he
  obtain ⟨p, hp, hep⟩ := mem_support.mp (mem_redEdges.mp heP).1
  refine ⟨⟨p, hp⟩, ?_⟩
  have hpone := hF.red_eq_singleton (hP.1.1 hp) hep (mem_inter.mp he).2
  have hqone := hF.red_eq_singleton hqF (mem_inter.mp he).1 (mem_inter.mp he).2
  exact hpone.trans hqone.symm

noncomputable def parent (hF : ColoredFamily F R) (hP : IsMaximumPacking F P)
    (hQ : IsPacking (residual F (blueEdges R P)) Q) (q : {T // T ∈ Q}) :
    {T // T ∈ P} := Classical.choose (exists_parent hF hP hQ q)

theorem parent_spec (hF : ColoredFamily F R) (hP : IsMaximumPacking F P)
    (hQ : IsPacking (residual F (blueEdges R P)) Q) (q : {T // T ∈ Q}) :
    (parent hF hP hQ q).val ∩ R = q.val ∩ R :=
  Classical.choose_spec (exists_parent hF hP hQ q)

theorem parent_unique (hF : ColoredFamily F R) (hP : IsMaximumPacking F P)
    (hQ : IsPacking (residual F (blueEdges R P)) Q) (q : {T // T ∈ Q})
    (p : {T // T ∈ P}) (heq : p.val ∩ R = q.val ∩ R) :
    p = parent hF hP hQ q := by
  apply Subtype.ext
  exact hP.1.red_inter_injective hF p.property (parent hF hP hQ q).property
    (heq.trans (parent_spec hF hP hQ q).symm)

theorem parent_injective (hF : ColoredFamily F R) (hP : IsMaximumPacking F P)
    (hQ : IsPacking (residual F (blueEdges R P)) Q) :
    Function.Injective (parent hF hP hQ) := by
  intro q₁ q₂ heq
  apply Subtype.ext
  apply hQ.red_inter_injective hF.residual q₁.property q₂.property
  calc
    q₁.val ∩ R = (parent hF hP hQ q₁).val ∩ R := (parent_spec hF hP hQ q₁).symm
    _ = (parent hF hP hQ q₂).val ∩ R := by rw [heq]
    _ = q₂.val ∩ R := parent_spec hF hP hQ q₂

theorem pairedParents_eq_image (hF : ColoredFamily F R) (hP : IsMaximumPacking F P)
    (hQ : IsPacking (residual F (blueEdges R P)) Q) :
    pairedParents R P Q = Q.attach.image (fun q => (parent hF hP hQ q).val) := by
  classical
  ext p
  constructor
  · intro hp
    obtain ⟨hpP, q, hq, heq⟩ := mem_pairedParents.mp hp
    have hpq := parent_unique hF hP hQ ⟨q, hq⟩ ⟨p, hpP⟩ heq
    exact mem_image.mpr ⟨⟨q, hq⟩, mem_attach _ _, (congrArg Subtype.val hpq).symm⟩
  · intro hp
    obtain ⟨q, _, rfl⟩ := mem_image.mp hp
    exact mem_pairedParents.mpr ⟨(parent hF hP hQ q).property,
      q.val, q.property, parent_spec hF hP hQ q⟩

theorem pairedParents_card (hF : ColoredFamily F R) (hP : IsMaximumPacking F P)
    (hQ : IsPacking (residual F (blueEdges R P)) Q) :
    (pairedParents R P Q).card = Q.card := by
  classical
  rw [pairedParents_eq_image hF hP hQ]
  have hinj : Function.Injective (fun q => (parent hF hP hQ q).val) := by
    intro q₁ q₂ heq
    exact parent_injective hF hP hQ (Subtype.ext heq)
  rw [card_image_of_injective _ hinj, card_attach]

/-- A residual page cannot be an original parent page: its two blue edges
avoid the parent support. -/
theorem residual_member_not_parent (hF : ColoredFamily F R)
    (hQ : IsPacking (residual F (blueEdges R P)) Q) {q : Finset E} (hq : q ∈ Q) :
    q ∉ P := by
  intro hqP
  have hqF := (mem_residual.mp (hQ.1 hq)).1
  have hn : (q \ R).Nonempty := card_pos.mp (by rw [hF.member_blue_card hqF]; decide)
  obtain ⟨e, he⟩ := hn
  obtain ⟨heq, heR⟩ := mem_sdiff.mp he
  exact disjoint_left.mp hQ.blueEdges_disjoint_parent_support
    (mem_blueEdges.mpr ⟨mem_support.mpr ⟨q, hq, heq⟩, heR⟩)
    (mem_support.mpr ⟨q, hqP, heq⟩)

theorem pages_nonempty (R : Finset E) (P Q : Finset (Finset E))
    (p : {T // T ∈ P}) : (twoLayerPages R P Q p).Nonempty := by
  exact ⟨p.val, mem_insert_self _ _⟩

theorem pages_subset_family (hP : IsMaximumPacking F P)
    (hQ : IsPacking (residual F (blueEdges R P)) Q) (p : {T // T ∈ P}) :
    twoLayerPages R P Q p ⊆ F := by
  intro T hT
  rcases mem_twoLayerPages.mp hT with rfl | ⟨hTQ, _⟩
  · exact hP.1.1 p.property
  · exact (mem_residual.mp (hQ.1 hTQ)).1

theorem pages_members_nonempty (hF : ColoredFamily F R) (hP : IsMaximumPacking F P)
    (hQ : IsPacking (residual F (blueEdges R P)) Q) (p : {T // T ∈ P})
    (T : Finset E) (hT : T ∈ twoLayerPages R P Q p) : T.Nonempty :=
  hF.member_nonempty (pages_subset_family hP hQ p hT)

/-- All parent-support edges of a book belong to that book's parent. -/
theorem book_inter_parent_subset (hF : ColoredFamily F R) (hP : IsMaximumPacking F P)
    (hQ : IsPacking (residual F (blueEdges R P)) Q) (p : {T // T ∈ P}) :
    support (twoLayerPages R P Q p) ∩ support P ⊆ p.val := by
  intro e he
  obtain ⟨hebook, heP⟩ := mem_inter.mp he
  obtain ⟨T, hT, heT⟩ := mem_support.mp hebook
  rcases mem_twoLayerPages.mp hT with rfl | ⟨hTQ, hred⟩
  · exact heT
  · have heTR : e ∈ T ∩ R :=
      residual_inter_support_eq_inter_red hF hP (hQ.1 hTQ) ▸
        mem_inter.mpr ⟨heT, heP⟩
    exact (mem_inter.mp (hred ▸ heTR)).1

theorem supports_disjoint (hF : ColoredFamily F R) (hP : IsMaximumPacking F P)
    (hQ : IsPacking (residual F (blueEdges R P)) Q) :
    Books.DisjointSupports (twoLayerPages R P Q) := by
  intro p p' hne
  have hval : p.val ≠ p'.val := fun h => hne (Subtype.ext h)
  have hdparents := hP.1.2 p.property p'.property hval
  apply disjoint_left.mpr
  intro e he he'
  obtain ⟨T, hT, heT⟩ := mem_support.mp he
  obtain ⟨U, hU, heU⟩ := mem_support.mp he'
  rcases mem_twoLayerPages.mp hT with rfl | ⟨hTQ, hTR⟩
  · have hep' := book_inter_parent_subset hF hP hQ p'
      (mem_inter.mpr ⟨he', mem_support.mpr ⟨p.val, p.property, heT⟩⟩)
    exact disjoint_left.mp hdparents heT hep'
  · rcases mem_twoLayerPages.mp hU with rfl | ⟨hUQ, hUR⟩
    · have hep := book_inter_parent_subset hF hP hQ p
        (mem_inter.mpr ⟨he, mem_support.mpr ⟨p'.val, p'.property, heU⟩⟩)
      exact disjoint_left.mp hdparents hep heU
    · have hTU : T ≠ U := by
        intro heq
        apply hval
        apply hP.1.red_inter_injective hF p.property p'.property
        calc
          p.val ∩ R = T ∩ R := hTR.symm
          _ = U ∩ R := by rw [heq]
          _ = p'.val ∩ R := hUR
      exact disjoint_left.mp (hQ.2 hTQ hUQ hTU) heT heU

theorem choices_maximum (hF : ColoredFamily F R) (hP : IsMaximumPacking F P)
    (hQ : IsPacking (residual F (blueEdges R P)) Q)
    {f : {T // T ∈ P} → Finset E}
    (hf : Books.ChoosesPages (twoLayerPages R P Q) f) :
    IsMaximumPacking F (Books.choice f) := by
  apply Books.choice_isMaximumPacking (pages_subset_family hP hQ)
    (supports_disjoint hF hP hQ) (pages_members_nonempty hF hP hQ) ?_ hf
  intro K hK
  simpa using hP.2 K hK

theorem children_card_le_one (hF : ColoredFamily F R)
    (hQ : IsPacking (residual F (blueEdges R P)) Q) (p : Finset E) :
    (children R Q p).card ≤ 1 := by
  apply card_le_one.mpr
  intro T hT U hU
  obtain ⟨hTQ, hTR⟩ := mem_children.mp hT
  obtain ⟨hUQ, hUR⟩ := mem_children.mp hU
  exact hQ.red_inter_injective hF.residual hTQ hUQ (hTR.trans hUR.symm)

theorem children_nonempty_iff_paired (p : {T // T ∈ P}) :
    (children R Q p.val).Nonempty ↔ p.val ∈ pairedParents R P Q := by
  constructor
  · rintro ⟨q, hq⟩
    obtain ⟨hqQ, heq⟩ := mem_children.mp hq
    exact mem_pairedParents.mpr ⟨p.property, q, hqQ, heq.symm⟩
  · intro hp
    obtain ⟨_, q, hqQ, heq⟩ := mem_pairedParents.mp hp
    exact ⟨q, mem_children.mpr ⟨hqQ, heq.symm⟩⟩

theorem parent_not_child (hF : ColoredFamily F R)
    (hQ : IsPacking (residual F (blueEdges R P)) Q) (p : {T // T ∈ P}) :
    p.val ∉ children R Q p.val := by
  intro hp
  exact residual_member_not_parent hF hQ (mem_children.mp hp).1 p.property

theorem pages_card_paired (hF : ColoredFamily F R)
    (hQ : IsPacking (residual F (blueEdges R P)) Q) (p : {T // T ∈ P})
    (hp : p.val ∈ pairedParents R P Q) : (twoLayerPages R P Q p).card = 2 := by
  have hpos := card_pos.mpr ((children_nonempty_iff_paired p).mpr hp)
  have hle := children_card_le_one hF hQ p.val
  rw [twoLayerPages, card_insert_of_notMem (parent_not_child hF hQ p)]
  omega

theorem pages_eq_singleton_unpaired (p : {T // T ∈ P})
    (hp : p.val ∉ pairedParents R P Q) : twoLayerPages R P Q p = {p.val} := by
  have hempty : children R Q p.val = ∅ := by
    apply not_nonempty_iff_eq_empty.mp
    intro hn
    exact hp ((children_nonempty_iff_paired p).mp hn)
  simp [twoLayerPages, hempty]

theorem pages_card_unpaired (p : {T // T ∈ P})
    (hp : p.val ∉ pairedParents R P Q) : (twoLayerPages R P Q p).card = 1 := by
  rw [pages_eq_singleton_unpaired p hp, card_singleton]

end Layered
end Tuza

-- ==== Tuza.Colored.Family

/-! The complete family of triangles with one red edge. -/

namespace Tuza

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The complete family of triangles with exactly one red edge.
The ambient graph has edge set A; membership in R means red. -/
noncomputable def oneRedTriangles (A R : Finset (Sym2 V)) :
    Finset (Finset (Sym2 V)) := by
  classical
  exact (trianglesOn A).filter (fun T => (T ∩ R).card = 1)

@[simp] theorem mem_oneRedTriangles {A R T : Finset (Sym2 V)} :
    T ∈ oneRedTriangles A R ↔ IsTriangle T ∧ T ⊆ A ∧ (T ∩ R).card = 1 := by
  classical
  simp [oneRedTriangles, and_assoc]

theorem oneRedTriangles_colored (A R : Finset (Sym2 V)) :
    ColoredFamily (oneRedTriangles A R) R := by
  intro T hT
  obtain ⟨ht, _, hr⟩ := mem_oneRedTriangles.mp hT
  exact ⟨ht.card_eq_three, hr⟩

/-- Deleting any edge set preserves completeness of the colored family. -/
theorem oneRedTriangles_sdiff (A R C : Finset (Sym2 V)) :
    oneRedTriangles (A \ C) R = residual (oneRedTriangles A R) C := by
  classical
  ext T
  simp only [oneRedTriangles, mem_filter, trianglesOn_sdiff, mem_residual]
  tauto

end Tuza

-- ==== Tuza.Construction.Types

/-! Triangle types relative to the edges of a maximum packing. -/

namespace Tuza

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Type j means exactly j edges in the fixed old edge set O. -/
noncomputable def typeFamily (A O : Finset (Sym2 V)) (j : ℕ) :
    Finset (Finset (Sym2 V)) := by
  classical
  exact (trianglesOn A).filter (fun T => (T ∩ O).card = j)

@[simp] theorem mem_typeFamily {A O T : Finset (Sym2 V)} {j : ℕ} :
    T ∈ typeFamily A O j ↔ T ∈ trianglesOn A ∧ (T ∩ O).card = j := by
  classical
  simp [typeFamily]

theorem typeFamily_subset (A O : Finset (Sym2 V)) (j : ℕ) :
    typeFamily A O j ⊆ trianglesOn A := by
  classical
  exact filter_subset _ _

theorem typeOne_colored (A O : Finset (Sym2 V)) :
    ColoredFamily (typeFamily A O 1) O := by
  intro T hT
  obtain ⟨ht, hc⟩ := mem_typeFamily.mp hT
  exact ⟨trianglesOn_card ht, hc⟩

/-- In a triangle, two old edges are equivalent to one new edge. -/
theorem typeTwo_eq_oneRed (A O : Finset (Sym2 V)) :
    typeFamily A O 2 = oneRedTriangles A (A \ O) := by
  ext T
  simp only [mem_typeFamily, mem_oneRedTriangles, mem_trianglesOn]
  constructor
  · rintro ⟨⟨hT, hsub⟩, hold⟩
    refine ⟨hT, hsub, ?_⟩
    have heq : T ∩ (A \ O) = T \ O := by
      ext e
      simp only [mem_inter, mem_sdiff]
      constructor
      · tauto
      · exact fun ⟨he, hno⟩ => ⟨he, hsub he, hno⟩
    rw [heq]
    have hpartition := card_sdiff_add_card_inter T O
    have hcard := hT.card_eq_three
    omega
  · rintro ⟨hT, hsub, hnew⟩
    refine ⟨⟨hT, hsub⟩, ?_⟩
    have heq : T ∩ (A \ O) = T \ O := by
      ext e
      simp only [mem_inter, mem_sdiff]
      constructor
      · tauto
      · exact fun ⟨he, hno⟩ => ⟨he, hsub he, hno⟩
    rw [heq] at hnew
    have hpartition := card_sdiff_add_card_inter T O
    have hcard := hT.card_eq_three
    omega

theorem typeTwo_colored (A O : Finset (Sym2 V)) :
    ColoredFamily (typeFamily A O 2) (A \ O) := by
  rw [typeTwo_eq_oneRed]
  exact oneRedTriangles_colored _ _

theorem new_edge_forces_typeTwo {A O T : Finset (Sym2 V)}
    (hT : T ∈ trianglesOn A) (hold : 2 ≤ (T ∩ O).card)
    {e : Sym2 V} (he : e ∈ T \ O) : T ∈ typeFamily A O 2 := by
  refine mem_typeFamily.mpr ⟨hT, ?_⟩
  have hnew : 0 < (T \ O).card := card_pos.mpr ⟨e, he⟩
  have hpartition := card_sdiff_add_card_inter T O
  have hcard := trianglesOn_card hT
  omega

theorem maximumPacking_old_nonempty {A : Finset (Sym2 V)}
    {P : Finset (Finset (Sym2 V))} (hP : IsMaximumPacking (trianglesOn A) P)
    {T : Finset (Sym2 V)} (hT : T ∈ trianglesOn A) :
    1 ≤ (T ∩ support P).card := by
  exact card_pos.mpr (hP.meets_support hT (trianglesOn_nonempty hT))

/-- After deleting a maximum packing of type-1 triangles, every remaining
triangle has at least two old edges. -/
theorem old_card_ge_two_after_typeOne {A : Finset (Sym2 V)}
    {P Q : Finset (Finset (Sym2 V))}
    (hP : IsMaximumPacking (trianglesOn A) P)
    (hQ : IsMaximumPacking (typeFamily A (support P) 1) Q)
    {T : Finset (Sym2 V)} (hT : T ∈ trianglesOn (A \ support Q)) :
    2 ≤ (T ∩ support P).card := by
  rw [trianglesOn_sdiff] at hT
  obtain ⟨ht, hd⟩ := mem_residual.mp hT
  have hpos := maximumPacking_old_nonempty hP ht
  by_contra hn
  have hone : (T ∩ support P).card = 1 := by omega
  have htype : T ∈ typeFamily A (support P) 1 := mem_typeFamily.mpr ⟨ht, hone⟩
  obtain ⟨e, he⟩ := hQ.meets_support htype (trianglesOn_nonempty ht)
  exact disjoint_left.mp hd (mem_inter.mp he).1 (mem_inter.mp he).2

/-- The old edges left after deleting the type-1 packing are counted exactly. -/
theorem remaining_old_card {A : Finset (Sym2 V)}
    {P Q : Finset (Finset (Sym2 V))}
    (hP : IsPacking (trianglesOn A) P)
    (hQ : IsPacking (typeFamily A (support P) 1) Q) :
    (support P \ support Q).card + Q.card = 3 * P.card := by
  have hred := hQ.card_redEdges (typeOne_colored A (support P))
  have hpartition := card_sdiff_add_card_inter (support P) (support Q)
  have hp := hP.card_support_uniform (fun T hT => trianglesOn_card (hP.1 hT))
  change (support Q ∩ support P).card = Q.card at hred
  rw [inter_comm] at hred
  omega

/-- A packing in the remaining graph can be combined with the deleted packing. -/
theorem deleted_packing_card_add_le {A : Finset (Sym2 V)}
    {P Q : Finset (Finset (Sym2 V))}
    (hP : IsPacking (trianglesOn A) P)
    (hQ : IsPacking (trianglesOn (A \ support P)) Q) :
    P.card + Q.card ≤ packingNumber (trianglesOn A) := by
  have hQ' : IsPacking (trianglesOn A) Q :=
    hQ.mono_family (trianglesOn_mono sdiff_subset)
  have hd : Disjoint (support P) (support Q) := by
    apply disjoint_left.mpr
    intro e heP heQ
    obtain ⟨T, hT, heT⟩ := mem_support.mp heQ
    exact (mem_sdiff.mp ((mem_trianglesOn.mp (hQ.1 hT)).2 heT)).2 heP
  have hPQ := hP.union hQ' hd
  have hdis := disjoint_of_support_disjoint
    (fun T hT => trianglesOn_nonempty (hP.1 hT)) hd
  simpa [card_union_of_disjoint hdis] using hPQ.card_le

end Tuza

-- ==== Tuza.Construction.Setup

/-! Haxell's packing construction and the complete residual colored family. -/

namespace Tuza

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The three packing choices made before constructing the residual family.
`initial`, `first`, and `rest` are the paper's P, A, and P', respectively. -/
structure Construction (edges : Finset (Sym2 V)) where
  initial : Finset (Finset (Sym2 V))
  initial_maximum : IsMaximumPacking (trianglesOn edges) initial
  first : Finset (Finset (Sym2 V))
  first_maximum : IsMaximumPacking (typeFamily edges (support initial) 1) first
  rest : Finset (Finset (Sym2 V))
  rest_lexMaximum : IsLexMaximumPacking (trianglesOn (edges \ support first))
    (typeFamily (edges \ support first) (support initial) 2) rest

theorem exists_construction (edges : Finset (Sym2 V)) : Nonempty (Construction edges) := by
  obtain ⟨P, hP⟩ := exists_maximumPacking (trianglesOn edges)
  obtain ⟨A, hA⟩ := exists_maximumPacking (typeFamily edges (support P) 1)
  obtain ⟨P', hP'⟩ := exists_lexMaximumPacking (trianglesOn (edges \ support A))
    (typeFamily (edges \ support A) (support P) 2)
  exact ⟨⟨P, hP, A, hA, P', hP'⟩⟩

namespace Construction

variable {edges : Finset (Sym2 V)} (c : Construction edges)

def old : Finset (Sym2 V) := support c.initial
def remainingEdges : Finset (Sym2 V) := edges \ support c.first
def oldRemaining : Finset (Sym2 V) := c.old \ support c.first
noncomputable def typeTwo : Finset (Finset (Sym2 V)) :=
  c.rest ∩ typeFamily c.remainingEdges c.old 2
def newEdges : Finset (Sym2 V) := support c.rest \ c.old

theorem first_packing : IsPacking (trianglesOn edges) c.first :=
  c.first_maximum.1.mono_family (typeFamily_subset _ _ _)

theorem rest_packing : IsPacking (trianglesOn c.remainingEdges) c.rest :=
  c.rest_lexMaximum.1

theorem old_subset_edges : c.old ⊆ edges := by
  intro e he
  obtain ⟨T, hT, heT⟩ := mem_support.mp he
  exact (mem_trianglesOn.mp (c.initial_maximum.1.1 hT)).2 heT

theorem rest_support_subset : support c.rest ⊆ c.remainingEdges := by
  intro e he
  obtain ⟨T, hT, heT⟩ := mem_support.mp he
  exact (mem_trianglesOn.mp (c.rest_packing.1 hT)).2 heT

theorem oldRemaining_subset_remaining : c.oldRemaining ⊆ c.remainingEdges := by
  intro e he
  exact mem_sdiff.mpr ⟨c.old_subset_edges (mem_sdiff.mp he).1, (mem_sdiff.mp he).2⟩

theorem remaining_old_ge_two {T : Finset (Sym2 V)} (hT : T ∈ trianglesOn c.remainingEdges) :
    2 ≤ (T ∩ c.old).card :=
  old_card_ge_two_after_typeOne c.initial_maximum c.first_maximum hT

theorem remaining_new_le_one {T : Finset (Sym2 V)} (hT : T ∈ trianglesOn c.remainingEdges) :
    (T \ c.old).card ≤ 1 := by
  have hold := c.remaining_old_ge_two hT
  have hcard := trianglesOn_card hT
  have hp := card_sdiff_add_card_inter T c.old
  omega

theorem typeTwo_maximum :
    IsMaximumPacking (typeFamily c.remainingEdges c.old 2) c.typeTwo :=
  c.rest_lexMaximum.typePart_maximum (typeFamily_subset _ _ _)

theorem typeTwo_subset_rest : c.typeTwo ⊆ c.rest := inter_subset_left

theorem newEdges_subset_remaining : c.newEdges ⊆ c.remainingEdges :=
  sdiff_subset.trans c.rest_support_subset

theorem newEdges_disjoint_old : Disjoint c.newEdges c.old := sdiff_disjoint

theorem newEdges_eq_red_typeTwo :
    c.newEdges = redEdges (c.remainingEdges \ c.old) c.typeTwo := by
  ext e
  constructor
  · intro he
    obtain ⟨heP, heO⟩ := mem_sdiff.mp he
    obtain ⟨T, hT, heT⟩ := mem_support.mp heP
    have hactual := c.rest_packing.1 hT
    have htype := new_edge_forces_typeTwo hactual (c.remaining_old_ge_two hactual)
      (mem_sdiff.mpr ⟨heT, heO⟩)
    exact mem_redEdges.mpr ⟨mem_support.mpr ⟨T, mem_inter.mpr ⟨hT, htype⟩, heT⟩,
      mem_sdiff.mpr ⟨c.newEdges_subset_remaining he, heO⟩⟩
  · intro he
    obtain ⟨heB, heR⟩ := mem_redEdges.mp he
    exact mem_sdiff.mpr ⟨support_mono c.typeTwo_subset_rest heB, (mem_sdiff.mp heR).2⟩

theorem card_newEdges : c.newEdges.card = c.typeTwo.card := by
  rw [c.newEdges_eq_red_typeTwo]
  exact c.typeTwo_maximum.1.card_redEdges (typeTwo_colored _ _)

theorem first_rest_card_le : c.first.card + c.rest.card ≤ c.initial.card := by
  have h := deleted_packing_card_add_le c.first_packing c.rest_packing
  rwa [← c.initial_maximum.card_eq] at h

theorem oldRemaining_card : c.oldRemaining.card + c.first.card = 3 * c.initial.card :=
  remaining_old_card c.initial_maximum.1 c.first_maximum.1

theorem rest_covers : IsCover (trianglesOn c.remainingEdges) (support c.rest) :=
  c.rest_lexMaximum.support_covers (fun _ hT => trianglesOn_nonempty hT)

/-- The paper's complete residual family S. -/
noncomputable def specialFamily : Finset (Finset (Sym2 V)) :=
  oneRedTriangles (c.newEdges ∪ (c.oldRemaining \ support c.rest)) c.newEdges

theorem specialFamily_colored : ColoredFamily c.specialFamily c.newEdges :=
  oneRedTriangles_colored _ _

theorem special_edges_subset :
    c.newEdges ∪ (c.oldRemaining \ support c.rest) ⊆ c.remainingEdges :=
  union_subset c.newEdges_subset_remaining
    (sdiff_subset.trans c.oldRemaining_subset_remaining)

theorem specialFamily_subset_triangles : c.specialFamily ⊆ trianglesOn c.remainingEdges := by
  intro T hT
  obtain ⟨ht, hsub, _⟩ := mem_oneRedTriangles.mp hT
  exact mem_trianglesOn.mpr ⟨ht, hsub.trans c.special_edges_subset⟩

/-- Selecting the old edges of P' leaves precisely S. -/
theorem specialFamily_eq_residual :
    c.specialFamily = residual (trianglesOn c.remainingEdges) (support c.rest ∩ c.old) := by
  ext T
  constructor
  · intro hT
    refine mem_residual.mpr ⟨c.specialFamily_subset_triangles hT, disjoint_left.mpr ?_⟩
    intro e heT heSelected
    obtain ⟨heRest, heOld⟩ := mem_inter.mp heSelected
    have he := (mem_oneRedTriangles.mp hT).2.1 heT
    rcases mem_union.mp he with heNew | heBlue
    · exact (mem_sdiff.mp heNew).2 heOld
    · exact (mem_sdiff.mp heBlue).2 heRest
  · intro hT
    obtain ⟨hactual, hd⟩ := mem_residual.mp hT
    obtain ⟨e, he⟩ := c.rest_covers T hactual
    obtain ⟨heT, heRest⟩ := mem_inter.mp he
    have heNotOld : e ∉ c.old := by
      intro heOld
      exact disjoint_left.mp hd heT (mem_inter.mpr ⟨heRest, heOld⟩)
    have heNew : e ∈ c.newEdges := mem_sdiff.mpr ⟨heRest, heNotOld⟩
    have hunique := card_le_one.mp (c.remaining_new_le_one hactual)
    apply mem_oneRedTriangles.mpr
    refine ⟨(mem_trianglesOn.mp hactual).1, ?_, ?_⟩
    · intro f hf
      by_cases hfOld : f ∈ c.old
      · have hfRemain := (mem_trianglesOn.mp hactual).2 hf
        have hfRest : f ∉ support c.rest := by
          intro hfr
          exact disjoint_left.mp hd hf (mem_inter.mpr ⟨hfr, hfOld⟩)
        exact mem_union_right _ (mem_sdiff.mpr
          ⟨mem_sdiff.mpr ⟨hfOld, (mem_sdiff.mp hfRemain).2⟩, hfRest⟩)
      · have hfe := hunique f (mem_sdiff.mpr ⟨hf, hfOld⟩)
          e (mem_sdiff.mpr ⟨heT, heNotOld⟩)
        exact mem_union_left _ (hfe.symm ▸ heNew)
    · apply card_eq_one.mpr
      refine ⟨e, ?_⟩
      ext f
      constructor
      · intro hf
        obtain ⟨hfT, hfNew⟩ := mem_inter.mp hf
        exact mem_singleton.mpr (hunique f
          (mem_sdiff.mpr ⟨hfT, (mem_sdiff.mp hfNew).2⟩)
          e (mem_sdiff.mpr ⟨heT, heNotOld⟩))
      · intro hf
        rw [mem_singleton.mp hf]
        exact mem_inter.mpr ⟨heT, heNew⟩

theorem specialFamily_subset_typeTwo :
    c.specialFamily ⊆ typeFamily c.remainingEdges c.old 2 := by
  intro T hT
  have hactual := c.specialFamily_subset_triangles hT
  have hred := (mem_oneRedTriangles.mp hT).2.2
  obtain ⟨e, he⟩ := card_pos.mp (show 0 < (T ∩ c.newEdges).card by omega)
  obtain ⟨heT, heNew⟩ := mem_inter.mp he
  exact new_edge_forces_typeTwo hactual (c.remaining_old_ge_two hactual)
    (mem_sdiff.mpr ⟨heT, (mem_sdiff.mp heNew).2⟩)

/-- The embedding used to apply the unique-red exchange in the larger graph. -/
theorem specialFamily_subset_typeTwo_residual :
    c.specialFamily ⊆ residual (typeFamily c.remainingEdges c.old 2)
      (blueEdges (c.remainingEdges \ c.old) c.typeTwo) := by
  intro T hT
  refine mem_residual.mpr ⟨c.specialFamily_subset_typeTwo hT, ?_⟩
  have hd := (mem_residual.mp (c.specialFamily_eq_residual ▸ hT)).2
  apply hd.mono_right
  intro e he
  obtain ⟨heB, heNotRed⟩ := mem_blueEdges.mp he
  have heRest := support_mono c.typeTwo_subset_rest heB
  refine mem_inter.mpr ⟨heRest, ?_⟩
  by_contra heNotOld
  exact heNotRed (mem_sdiff.mpr ⟨c.rest_support_subset heRest, heNotOld⟩)

theorem inter_oldRemaining {T : Finset (Sym2 V)} (hT : T ⊆ c.remainingEdges) :
    T ∩ c.oldRemaining = T ∩ c.old := by
  ext e
  constructor
  · intro he
    exact mem_inter.mpr ⟨(mem_inter.mp he).1, (mem_sdiff.mp (mem_inter.mp he).2).1⟩
  · intro he
    obtain ⟨heT, heOld⟩ := mem_inter.mp he
    exact mem_inter.mpr ⟨heT, mem_sdiff.mpr ⟨heOld, (mem_sdiff.mp (hT heT)).2⟩⟩

theorem typeFamily_oldRemaining (j : ℕ) :
    typeFamily c.remainingEdges c.oldRemaining j = typeFamily c.remainingEdges c.old j := by
  ext T
  simp only [mem_typeFamily]
  constructor <;> rintro ⟨hT, hc⟩
  · exact ⟨hT, (c.inter_oldRemaining (mem_trianglesOn.mp hT).2) ▸ hc⟩
  · exact ⟨hT, (c.inter_oldRemaining (mem_trianglesOn.mp hT).2).symm ▸ hc⟩

theorem remaining_sdiff_oldRemaining :
    c.remainingEdges \ c.oldRemaining = c.remainingEdges \ c.old := by
  ext e
  simp only [remainingEdges, oldRemaining, mem_sdiff]
  tauto

theorem remaining_oldRemaining_ge_two {T : Finset (Sym2 V)}
    (hT : T ∈ trianglesOn c.remainingEdges) : 2 ≤ (T ∩ c.oldRemaining).card := by
  rw [c.inter_oldRemaining (mem_trianglesOn.mp hT).2]
  exact c.remaining_old_ge_two hT

theorem old_not_diag {e : Sym2 V} (he : e ∈ c.old) : ¬ e.IsDiag := by
  obtain ⟨T, hT, heT⟩ := mem_support.mp he
  intro hd
  have hloop : s(e.diagElem hd, e.diagElem hd) ∈ T :=
    (congrArg (fun f : Sym2 V => f ∈ T) (Sym2.diag_diagElem hd)).mpr heT
  exact (mem_trianglesOn.mp (c.initial_maximum.1.1 hT)).1.not_mem_diag _ hloop

theorem newEdges_not_diag {e : Sym2 V} (he : e ∈ c.newEdges) : ¬ e.IsDiag := by
  obtain ⟨T, hT, heT⟩ := mem_support.mp (mem_sdiff.mp he).1
  intro hd
  have hloop : s(e.diagElem hd, e.diagElem hd) ∈ T :=
    (congrArg (fun f : Sym2 V => f ∈ T) (Sym2.diag_diagElem hd)).mpr heT
  exact (mem_trianglesOn.mp (c.rest_packing.1 hT)).1.not_mem_diag _ hloop

variable {c}

theorem rest_red_eq_sdiff (p : {T // T ∈ c.rest}) :
    p.val ∩ c.newEdges = p.val \ c.old := by
  ext e
  constructor
  · intro he
    exact mem_sdiff.mpr ⟨(mem_inter.mp he).1, (mem_sdiff.mp (mem_inter.mp he).2).2⟩
  · intro he
    obtain ⟨hep, heO⟩ := mem_sdiff.mp he
    exact mem_inter.mpr ⟨hep, mem_sdiff.mpr ⟨mem_support.mpr ⟨p.val, p.property, hep⟩, heO⟩⟩

theorem typeTwo_red_card (p : {T // T ∈ c.typeTwo}) :
    (p.val ∩ c.newEdges).card = 1 := by
  rw [rest_red_eq_sdiff (c := c) ⟨p.val, c.typeTwo_subset_rest p.property⟩]
  change (p.val \ c.old).card = 1
  have ho := (mem_typeFamily.mp (mem_inter.mp p.property).2).2
  have ht := trianglesOn_card (c.rest_packing.1 (c.typeTwo_subset_rest p.property))
  have hs := card_sdiff_add_card_inter p.val c.old
  omega

theorem typeTwo_red_nonempty (p : {T // T ∈ c.typeTwo}) :
    (p.val ∩ c.newEdges).Nonempty := card_pos.mp (by rw [typeTwo_red_card p]; decide)

noncomputable def typeTwoSpine (p : {T // T ∈ c.typeTwo}) : Sym2 V :=
  Classical.choose (typeTwo_red_nonempty p)

theorem typeTwoSpine_mem (p : {T // T ∈ c.typeTwo}) :
    typeTwoSpine p ∈ p.val ∩ c.newEdges :=
  Classical.choose_spec (typeTwo_red_nonempty p)

end Construction

end Tuza

-- ==== Tuza.Construction.BookCover

/-! The three-page book cover: equation (5). -/

namespace Tuza

open Finset
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {edges : Finset (Sym2 V)}

/-- The maximum residual packing Q and its maximum blue-edge residual packing Q1. -/
structure RefinedConstruction (c : Construction edges) where
  second : Finset (Finset (Sym2 V))
  second_maximum : IsMaximumPacking c.specialFamily second
  third : Finset (Finset (Sym2 V))
  third_maximum : IsMaximumPacking
    (residual c.specialFamily (blueEdges c.newEdges second)) third

theorem exists_refinedConstruction (c : Construction edges) :
    Nonempty (RefinedConstruction c) := by
  obtain ⟨Q, hQ⟩ := exists_maximumPacking c.specialFamily
  obtain ⟨Q1, hQ1⟩ := exists_maximumPacking
    (residual c.specialFamily (blueEdges c.newEdges Q))
  exact ⟨⟨Q, hQ, Q1, hQ1⟩⟩

namespace ThreeLayer

variable {c : Construction edges} (r : RefinedConstruction c)

theorem second_packing : IsPacking c.specialFamily r.second := r.second_maximum.1

theorem third_packing : IsPacking c.specialFamily r.third :=
  r.third_maximum.1.mono_family (filter_subset _ _)

def pages (p : {T // T ∈ c.rest}) : Finset (Finset (Sym2 V)) :=
  Layered.twoLayerPages c.newEdges c.rest (r.second ∪ r.third) p

@[simp] theorem mem_pages {p : {T // T ∈ c.rest}} {T : Finset (Sym2 V)} :
    T ∈ pages r p ↔ T = p.val ∨
      (T ∈ r.second ∪ r.third ∧ T ∩ c.newEdges = p.val ∩ c.newEdges) :=
  Layered.mem_twoLayerPages

theorem parent_mem_pages (p : {T // T ∈ c.rest}) : p.val ∈ pages r p :=
  (mem_pages r).mpr (Or.inl rfl)

theorem child_actual {T : Finset (Sym2 V)} (hT : T ∈ r.second ∪ r.third) :
    T ∈ c.specialFamily := by
  rcases mem_union.mp hT with hT | hT
  · exact r.second_maximum.1.1 hT
  · exact (third_packing r).1 hT

theorem rest_red_card_le_one (p : {T // T ∈ c.rest}) :
    (p.val ∩ c.newEdges).card ≤ 1 := by
  apply le_trans (card_le_card ?_) (c.remaining_new_le_one (c.rest_packing.1 p.property))
  intro e he
  exact mem_sdiff.mpr ⟨(mem_inter.mp he).1, (mem_sdiff.mp (mem_inter.mp he).2).2⟩

theorem rest_red_eq_singleton (p : {T // T ∈ c.rest}) {e : Sym2 V}
    (hep : e ∈ p.val) (heN : e ∈ c.newEdges) : p.val ∩ c.newEdges = {e} := by
  ext f
  constructor
  · intro hf
    exact mem_singleton.mpr
      (card_le_one.mp (rest_red_card_le_one (c := c) p) f hf e (mem_inter.mpr ⟨hep, heN⟩))
  · intro hf
    rw [mem_singleton.mp hf]
    exact mem_inter.mpr ⟨hep, heN⟩

theorem owner_unique {T : Finset (Sym2 V)} (hT : T ∈ c.specialFamily)
    (p p' : {T // T ∈ c.rest})
    (hp : T ∩ c.newEdges = p.val ∩ c.newEdges)
    (hp' : T ∩ c.newEdges = p'.val ∩ c.newEdges) : p = p' := by
  by_contra hne
  have hval : p.val ≠ p'.val := fun h => hne (Subtype.ext h)
  have hn : (T ∩ c.newEdges).Nonempty :=
    card_pos.mp (by rw [(c.specialFamily_colored T hT).2]; decide)
  obtain ⟨e, he⟩ := hn
  exact disjoint_left.mp (c.rest_packing.2 p.property p'.property hval)
    (mem_inter.mp (hp ▸ he)).1 (mem_inter.mp (hp' ▸ he)).1

theorem exists_parent {T : Finset (Sym2 V)} (hT : T ∈ c.specialFamily) :
    ∃ p : {T // T ∈ c.rest}, T ∩ c.newEdges = p.val ∩ c.newEdges := by
  have hn : (T ∩ c.newEdges).Nonempty :=
    card_pos.mp (by rw [(c.specialFamily_colored T hT).2]; decide)
  obtain ⟨e, heT, heN⟩ := show ∃ e, e ∈ T ∧ e ∈ c.newEdges from by
    obtain ⟨e, he⟩ := hn
    exact ⟨e, (mem_inter.mp he).1, (mem_inter.mp he).2⟩
  obtain ⟨p, hp, hep⟩ := mem_support.mp (mem_sdiff.mp heN).1
  refine ⟨⟨p, hp⟩, ?_⟩
  exact (c.specialFamily_colored.red_eq_singleton hT heT heN).trans
    (rest_red_eq_singleton (c := c) ⟨p, hp⟩ hep heN).symm

theorem special_inter_rest {T : Finset (Sym2 V)} (hT : T ∈ c.specialFamily) :
    T ∩ support c.rest = T ∩ c.newEdges := by
  have hd := (mem_residual.mp (c.specialFamily_eq_residual ▸ hT)).2
  ext e
  constructor
  · intro he
    obtain ⟨heT, heP⟩ := mem_inter.mp he
    refine mem_inter.mpr ⟨heT, mem_sdiff.mpr ⟨heP, ?_⟩⟩
    intro heO
    exact disjoint_left.mp hd heT (mem_inter.mpr ⟨heP, heO⟩)
  · intro he
    exact mem_inter.mpr ⟨(mem_inter.mp he).1, (mem_sdiff.mp (mem_inter.mp he).2).1⟩

theorem special_not_rest {T : Finset (Sym2 V)} (hT : T ∈ c.specialFamily) :
    T ∉ c.rest := by
  intro hp
  have heq : T ∩ support c.rest = T := inter_eq_left.mpr
    (fun _ he => mem_support.mpr ⟨T, hp, he⟩)
  have hc := congrArg Finset.card (special_inter_rest (c := c) hT)
  rw [heq, (c.specialFamily_colored T hT).1, (c.specialFamily_colored T hT).2] at hc
  omega

theorem children_card_le_one {K : Finset (Finset (Sym2 V))}
    (hK : IsPacking c.specialFamily K) (p : Finset (Sym2 V)) :
    (Layered.children c.newEdges K p).card ≤ 1 := by
  apply card_le_one.mpr
  intro T hT U hU
  obtain ⟨hTK, hTp⟩ := Layered.mem_children.mp hT
  obtain ⟨hUK, hUp⟩ := Layered.mem_children.mp hU
  exact hK.red_inter_injective c.specialFamily_colored hTK hUK (hTp.trans hUp.symm)

theorem second_third_disjoint : Disjoint r.second r.third := by
  apply disjoint_left.mpr
  intro T hTQ hTQ1
  exact Layered.residual_member_not_parent c.specialFamily_colored
    r.third_maximum.1 hTQ1 hTQ

theorem children_union (p : Finset (Sym2 V)) :
    Layered.children c.newEdges (r.second ∪ r.third) p =
      Layered.children c.newEdges r.second p ∪ Layered.children c.newEdges r.third p := by
  simp [Layered.children, filter_union]

theorem parent_not_child (p : {T // T ∈ c.rest}) :
    p.val ∉ Layered.children c.newEdges (r.second ∪ r.third) p.val := by
  intro hp
  exact special_not_rest (child_actual r (Layered.mem_children.mp hp).1) p.property

theorem pages_nonempty (p : {T // T ∈ c.rest}) : (pages r p).Nonempty :=
  ⟨p.val, parent_mem_pages r p⟩

theorem pages_card_le_three (p : {T // T ∈ c.rest}) : (pages r p).card ≤ 3 := by
  have hq := children_card_le_one (second_packing r) p.val
  have hq1 := children_card_le_one (third_packing r) p.val
  have hu := card_union_le (Layered.children c.newEdges r.second p.val)
    (Layered.children c.newEdges r.third p.val)
  change (insert p.val (Layered.children c.newEdges (r.second ∪ r.third) p.val)).card ≤ 3
  rw [card_insert_of_notMem (parent_not_child r p), children_union]
  omega

theorem pages_subset_family (p : {T // T ∈ c.rest}) :
    pages r p ⊆ trianglesOn c.remainingEdges := by
  intro T hT
  rcases (mem_pages r).mp hT with rfl | ⟨hTc, _⟩
  · exact c.rest_packing.1 p.property
  · exact c.specialFamily_subset_triangles (child_actual r hTc)

theorem second_third_overlap_red {T U : Finset (Sym2 V)}
    (hT : T ∈ r.second) (hU : U ∈ r.third) {e : Sym2 V}
    (heT : e ∈ T) (heU : e ∈ U) : e ∈ c.newEdges := by
  by_contra heN
  have hd := (mem_residual.mp (r.third_maximum.1.1 hU)).2
  exact disjoint_left.mp hd heU
    (mem_blueEdges.mpr ⟨mem_support.mpr ⟨T, hT, heT⟩, heN⟩)

theorem overlapping_children_red_eq {T U : Finset (Sym2 V)}
    (hT : T ∈ r.second ∪ r.third) (hU : U ∈ r.second ∪ r.third)
    {e : Sym2 V} (heT : e ∈ T) (heU : e ∈ U) :
    T ∩ c.newEdges = U ∩ c.newEdges := by
  have hTc := child_actual r hT
  have hUc := child_actual r hU
  rcases mem_union.mp hT with hT | hT <;> rcases mem_union.mp hU with hU | hU
  · by_cases h : T = U
    · rw [h]
    · exact (disjoint_left.mp (r.second_maximum.1.2 hT hU h) heT heU).elim
  · have heN := second_third_overlap_red r hT hU heT heU
    exact (c.specialFamily_colored.red_eq_singleton hTc heT heN).trans
      (c.specialFamily_colored.red_eq_singleton hUc heU heN).symm
  · have heN := second_third_overlap_red r hU hT heU heT
    exact (c.specialFamily_colored.red_eq_singleton hTc heT heN).trans
      (c.specialFamily_colored.red_eq_singleton hUc heU heN).symm
  · by_cases h : T = U
    · rw [h]
    · exact (disjoint_left.mp (r.third_maximum.1.2 hT hU h) heT heU).elim

theorem book_inter_rest_subset (p : {T // T ∈ c.rest}) :
    support (pages r p) ∩ support c.rest ⊆ p.val := by
  intro e he
  obtain ⟨heb, heP⟩ := mem_inter.mp he
  obtain ⟨T, hT, heT⟩ := mem_support.mp heb
  rcases (mem_pages r).mp hT with rfl | ⟨hTc, hTR⟩
  · exact heT
  · have heR : e ∈ T ∩ c.newEdges :=
      special_inter_rest (child_actual r hTc) ▸ mem_inter.mpr ⟨heT, heP⟩
    exact (mem_inter.mp (hTR ▸ heR)).1

theorem supports_disjoint : Books.DisjointSupports (pages r) := by
  intro p p' hne
  have hval : p.val ≠ p'.val := fun h => hne (Subtype.ext h)
  have hd := c.rest_packing.2 p.property p'.property hval
  apply disjoint_left.mpr
  intro e he he'
  obtain ⟨T, hT, heT⟩ := mem_support.mp he
  obtain ⟨U, hU, heU⟩ := mem_support.mp he'
  rcases (mem_pages r).mp hT with rfl | ⟨hTc, hTR⟩
  · have hep' := book_inter_rest_subset r p'
      (mem_inter.mpr ⟨he', mem_support.mpr ⟨p.val, p.property, heT⟩⟩)
    exact disjoint_left.mp hd heT hep'
  · rcases (mem_pages r).mp hU with rfl | ⟨hUc, hUR⟩
    · have hep := book_inter_rest_subset r p
        (mem_inter.mpr ⟨he, mem_support.mpr ⟨p'.val, p'.property, heU⟩⟩)
      exact disjoint_left.mp hd hep heU
    · exact hne (owner_unique (child_actual r hTc) p p' hTR
        ((overlapping_children_red_eq r hTc hUc heT heU).trans hUR))

theorem children_pairwise_disjoint {K : Finset (Finset (Sym2 V))}
    (hK : K ⊆ c.specialFamily) :
    Pairwise (fun p p' : {T // T ∈ c.rest} =>
      Disjoint (Layered.children c.newEdges K p.val) (Layered.children c.newEdges K p'.val)) := by
  intro p p' hne
  apply disjoint_left.mpr
  intro T hT hT'
  obtain ⟨hTK, hTp⟩ := Layered.mem_children.mp hT
  exact hne (owner_unique (hK hTK) p p' hTp (Layered.mem_children.mp hT').2)

theorem children_biUnion {K : Finset (Finset (Sym2 V))} (hK : K ⊆ c.specialFamily) :
    univ.biUnion (fun p : {T // T ∈ c.rest} => Layered.children c.newEdges K p.val) = K := by
  ext T
  constructor
  · intro hT
    obtain ⟨p, _, hp⟩ := mem_biUnion.mp hT
    exact (Layered.mem_children.mp hp).1
  · intro hT
    obtain ⟨p, hp⟩ := exists_parent (hK hT)
    exact mem_biUnion.mpr ⟨p, mem_univ _, Layered.mem_children.mpr ⟨hT, hp⟩⟩

theorem sum_children_card {K : Finset (Finset (Sym2 V))} (hK : K ⊆ c.specialFamily) :
    (∑ p : {T // T ∈ c.rest}, (Layered.children c.newEdges K p.val).card) = K.card := by
  conv_rhs => rw [← children_biUnion hK]
  symm
  apply card_biUnion
  intro p _ p' _ hne
  exact children_pairwise_disjoint hK hne

theorem sum_pages_card : (∑ p : {T // T ∈ c.rest}, (pages r p).card) =
    c.rest.card + r.second.card + r.third.card := by
  have hc (p : {T // T ∈ c.rest}) : (pages r p).card =
      (Layered.children c.newEdges (r.second ∪ r.third) p.val).card + 1 :=
    card_insert_of_notMem (parent_not_child r p)
  have hsub : r.second ∪ r.third ⊆ c.specialFamily := fun _ hT => child_actual r hT
  calc
    (∑ p : {T // T ∈ c.rest}, (pages r p).card) =
        ∑ p : {T // T ∈ c.rest},
          ((Layered.children c.newEdges (r.second ∪ r.third) p.val).card + 1) :=
      sum_congr rfl (fun p _ => hc p)
    _ = c.rest.card + r.second.card + r.third.card := by
      rw [sum_add_distrib, sum_children_card hsub, card_union_of_disjoint (second_third_disjoint r)]
      simp [Nat.add_comm, Nat.add_left_comm]

theorem parent_typeTwo_iff_red_nonempty (p : {T // T ∈ c.rest}) :
    p.val ∈ c.typeTwo ↔ (p.val ∩ c.newEdges).Nonempty := by
  constructor
  · intro hp
    exact Construction.typeTwo_red_nonempty (c := c) ⟨p.val, hp⟩
  · rintro ⟨e, he⟩
    have hactual := c.rest_packing.1 p.property
    refine mem_inter.mpr ⟨p.property, ?_⟩
    exact new_edge_forces_typeTwo hactual (c.remaining_old_ge_two hactual)
      (mem_sdiff.mpr ⟨(mem_inter.mp he).1, (mem_sdiff.mp (mem_inter.mp he).2).2⟩)

theorem page_typeTwo_iff_parent (p : {T // T ∈ c.rest}) {T : Finset (Sym2 V)}
    (hT : T ∈ pages r p) :
    T ∈ typeFamily c.remainingEdges c.old 2 ↔ p.val ∈ c.typeTwo := by
  rcases (mem_pages r).mp hT with rfl | ⟨hTc, hTR⟩
  · exact ⟨fun h => mem_inter.mpr ⟨p.property, h⟩, fun h => (mem_inter.mp h).2⟩
  · have hc := child_actual r hTc
    have hp : p.val ∈ c.typeTwo := by
      apply (parent_typeTwo_iff_red_nonempty p).mpr
      rw [← hTR]
      exact card_pos.mp (by rw [(c.specialFamily_colored T hc).2]; decide)
    exact ⟨fun _ => hp, fun _ => c.specialFamily_subset_typeTwo hc⟩

theorem pages_common_edge (p : {T // T ∈ c.rest}) :
    ∃ e, ∀ T ∈ pages r p, e ∈ T := by
  by_cases hn : (p.val ∩ c.newEdges).Nonempty
  · obtain ⟨e, he⟩ := hn
    refine ⟨e, ?_⟩
    intro T hT
    rcases (mem_pages r).mp hT with rfl | ⟨_, hTR⟩
    · exact (mem_inter.mp he).1
    · exact (mem_inter.mp (hTR.symm ▸ he)).1
  · obtain ⟨e, he⟩ := trianglesOn_nonempty (c.rest_packing.1 p.property)
    refine ⟨e, ?_⟩
    intro T hT
    rcases (mem_pages r).mp hT with rfl | ⟨hTc, hTR⟩
    · exact he
    · have hred : (T ∩ c.newEdges).Nonempty :=
        card_pos.mp (by rw [(c.specialFamily_colored T (child_actual r hTc)).2]; decide)
      exact (hn (hTR ▸ hred)).elim

theorem choices_packing {f : {T // T ∈ c.rest} → Finset (Sym2 V)}
    (hf : Books.ChoosesPages (pages r) f) :
    IsPacking (trianglesOn c.remainingEdges) (Books.choice f) :=
  Books.choice_isPacking (pages_subset_family r) (supports_disjoint r) hf

theorem choices_card {f : {T // T ∈ c.rest} → Finset (Sym2 V)}
    (hf : Books.ChoosesPages (pages r) f) : (Books.choice f).card = c.rest.card := by
  simpa using Books.card_choice (supports_disjoint r)
    (fun p T hT => trianglesOn_nonempty (pages_subset_family r p hT)) hf

/-- A full choice preserves exactly the original set of type-two parent slots. -/
theorem choices_typeTwo_card {f : {T // T ∈ c.rest} → Finset (Sym2 V)}
    (hf : Books.ChoosesPages (pages r) f) :
    (Books.choice f ∩ typeFamily c.remainingEdges c.old 2).card = c.typeTwo.card := by
  classical
  have heq : Books.choice f ∩ typeFamily c.remainingEdges c.old 2 =
      univ.image (fun p : {T // T ∈ c.typeTwo} =>
        f ⟨p.val, c.typeTwo_subset_rest p.property⟩) := by
    ext T
    constructor
    · intro hT
      obtain ⟨hTf, hTtype⟩ := mem_inter.mp hT
      obtain ⟨p, rfl⟩ := Books.mem_choice.mp hTf
      have hp := (page_typeTwo_iff_parent r p (hf p)).mp hTtype
      exact mem_image.mpr ⟨⟨p.val, hp⟩, mem_univ _, rfl⟩
    · intro hT
      obtain ⟨p, _, rfl⟩ := mem_image.mp hT
      exact mem_inter.mpr
        ⟨Books.mem_choice.mpr ⟨⟨p.val, c.typeTwo_subset_rest p.property⟩, rfl⟩,
          (page_typeTwo_iff_parent r ⟨p.val, c.typeTwo_subset_rest p.property⟩
            (hf ⟨p.val, c.typeTwo_subset_rest p.property⟩)).mpr p.property⟩
  have hfInj := Books.choice_injective (supports_disjoint r)
    (fun p T hT => trianglesOn_nonempty (pages_subset_family r p hT)) hf
  have hgInj : Function.Injective (fun p : {T // T ∈ c.typeTwo} =>
      f ⟨p.val, c.typeTwo_subset_rest p.property⟩) := by
    intro p p' h
    exact Subtype.ext (congrArg (fun q : {T // T ∈ c.rest} => q.val) (hfInj h))
  rw [heq, card_image_of_injective _ hgInj]
  simp

/-- Full choices preserve both counts in the lexicographic maximum. -/
theorem choices_lexMaximum {f : {T // T ∈ c.rest} → Finset (Sym2 V)}
    (hf : Books.ChoosesPages (pages r) f) :
    IsLexMaximumPacking (trianglesOn c.remainingEdges)
      (typeFamily c.remainingEdges c.old 2) (Books.choice f) := by
  apply c.rest_lexMaximum.of_same_counts (choices_packing r hf)
  · exact choices_typeTwo_card r hf
  · exact choices_card r hf

theorem everyChoiceMeets :
    Books.EveryChoiceMeets (trianglesOn c.remainingEdges) (pages r) := by
  intro f hf T hT
  obtain ⟨e, he⟩ := (choices_lexMaximum r hf).meets_support hT (trianglesOn_nonempty hT)
  obtain ⟨U, hU, heU⟩ := mem_support.mp (mem_inter.mp he).2
  obtain ⟨p, rfl⟩ := Books.mem_choice.mp hU
  refine ⟨p, ?_⟩
  intro hd
  exact disjoint_left.mp hd (mem_inter.mp he).1 heU

/-- The actual third cover of the remaining graph, with all three layers paid. -/
theorem exists_third_cover :
    ∃ C : Finset (Sym2 V), IsCover (trianglesOn c.remainingEdges) C ∧
      C.card + r.second.card + r.third.card ≤ 3 * c.rest.card := by
  obtain ⟨C, hC, hcard⟩ := exists_cover_of_small_common_spine_books
    (trianglesOn c.remainingEdges) (pages r) (pages_nonempty r) (pages_card_le_three r)
    (fun p T hT => (mem_trianglesOn.mp (pages_subset_family r p hT)).1)
    (pages_common_edge r) (fun _ hT => (mem_trianglesOn.mp hT).1) (everyChoiceMeets r)
  rw [sum_pages_card r] at hcard
  simp only [Fintype.card_coe] at hcard
  exact ⟨C, hC, by omega⟩

end ThreeLayer
end Tuza

namespace Tuza
namespace Construction

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {edges : Finset (Sym2 V)} (c : Construction edges)

/-- The book cover of G' together with the deleted first packing covers G. -/
theorem exists_full_book_cover (r : RefinedConstruction c) :
    ∃ C, IsCover (trianglesOn edges) C ∧
      C.card + r.second.card + r.third.card ≤ 3 * c.initial.card := by
  obtain ⟨D, hD, hc⟩ := ThreeLayer.exists_third_cover r
  have hres : IsCover (residual (trianglesOn edges) (support c.first)) D := by
    rw [← trianglesOn_sdiff]
    exact hD
  refine ⟨support c.first ∪ D, cover_union_residual hres, ?_⟩
  have hsize := c.first_packing.card_support_uniform
    (fun _ hT => trianglesOn_card (c.first_packing.1 hT))
  have hu := card_union_le (support c.first) D
  have hp := c.first_rest_card_le
  omega

theorem full_book_cover (r : RefinedConstruction c) :
    transversalNumber (trianglesOn edges) + r.second.card + r.third.card ≤
      3 * c.initial.card := by
  obtain ⟨C, hC, hc⟩ := c.exists_full_book_cover r
  have ht := hC.number_le
  omega

end Construction
end Tuza

-- ==== Tuza.Basic.Arithmetic

/-! The arithmetic combining the colored and full-graph covers. -/

namespace Tuza

/-- Arithmetic in the first colored-cover comparison, with denominators cleared. -/
theorem colored_bound_arithmetic {t p a r u : ℕ}
    (hfirst : t + 2 * a + u ≤ 3 * p + r)
    (hsecond : t + r ≤ 2 * p + 3 * a) (hra : r ≤ a) :
    3 * t + 2 * u ≤ 8 * p := by
  omega

/-- Arithmetic after applying the first colored estimate to the residual family. -/
theorem colored_refined_arithmetic {t p a r u : ℕ}
    (hfirst : t + 2 * a + u ≤ 3 * p + r)
    (hresidual : 3 * t + 2 * r ≤ 6 * p + 8 * a) :
    4 * t + u ≤ 9 * p + 6 * a := by
  omega

/-- Equations (3)--(6), combined with weights 20, 8, 19, and 12. -/
theorem four_bounds_arithmetic {t n a b c d h : ℕ}
    (hfirst : t + a ≤ 3 * n)
    (hcut : 8 * t + 8 * c ≤ 12 * n + 20 * a + 12 * b + 3 * h)
    (hbooks : t + c + d ≤ 3 * n)
    (hcolored : 4 * t + 4 * b + h ≤ 12 * n + 9 * c + 6 * d) :
    59 * t + d ≤ 165 * n := by
  omega

end Tuza

-- ==== Tuza.Colored.Exchange

/-! The two-for-one exchange: Lemma 2.1. -/

namespace Tuza

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
private theorem red_edges_eq {T R : Finset (Sym2 V)}
    (hcard : (T ∩ R).card = 1) {e f : Sym2 V}
    (he : e ∈ T) (heR : e ∈ R) (hf : f ∈ T) (hfR : f ∈ R) : e = f := by
  exact Finset.card_le_one.mp (Nat.le_of_eq hcard)
    e (mem_inter.mpr ⟨he, heR⟩) f (mem_inter.mpr ⟨hf, hfR⟩)

/-- The two-for-one exchange in Lemma 2.1 of the manuscript. -/
theorem unique_residual_triangle {A R : Finset (Sym2 V)}
    {P : Finset (Finset (Sym2 V))} {u v x y : V}
    (hP : IsMaximumPacking (oneRedTriangles A R) P)
    (hparent : triangleEdges u v x ∈ P)
    (hpage : triangleEdges u v y ∈
      residual (oneRedTriangles A R) (blueEdges R P))
    (hspine : s(u, v) ∈ R)
    (hoppA : s(x, y) ∈ A) (hoppR : s(x, y) ∈ R)
    (hoppNew : s(x, y) ∉ redEdges R P) :
    ∀ T ∈ residual (oneRedTriangles A R) (blueEdges R P),
      s(u, v) ∈ T → T = triangleEdges u v y := by
  classical
  obtain ⟨hX, hXA, hXR⟩ := mem_oneRedTriangles.mp (hP.1.1 hparent)
  obtain ⟨hpageF, hpageDisj⟩ := mem_residual.mp hpage
  obtain ⟨hY, hYA, hYR⟩ := mem_oneRedTriangles.mp hpageF
  have huv : u ≠ v := hX.ne_of_mem (by simp)
  have hux : u ≠ x := hX.ne_of_mem (by simp)
  have hvx : v ≠ x := hX.ne_of_mem (by simp)
  have huy : u ≠ y := hY.ne_of_mem (by simp)
  have hvy : v ≠ y := hY.ne_of_mem (by simp)

  have huxNotRed : s(u, x) ∉ R := by
    intro hred
    have heq := red_edges_eq hXR (by simp) hred (by simp) hspine
    exact hvx (Sym2.congr_right.mp heq).symm
  have huyNotRed : s(u, y) ∉ R := by
    intro hred
    have heq := red_edges_eq hYR (by simp) hred (by simp) hspine
    exact hvy (Sym2.congr_right.mp heq).symm
  have huxBlue : s(u, x) ∈ blueEdges R P := by
    exact mem_sdiff.mpr ⟨mem_support.mpr ⟨triangleEdges u v x, hparent, by simp⟩,
      huxNotRed⟩
  have hxy : x ≠ y := by
    intro h
    exact disjoint_left.mp hpageDisj (by simp [h]) huxBlue
  have huyOutside : s(u, y) ∉ support P := by
    intro hs
    exact disjoint_left.mp hpageDisj (by simp)
      (mem_sdiff.mpr ⟨hs, huyNotRed⟩)
  have hxyOutside : s(x, y) ∉ support P := by
    intro hs
    exact hoppNew (mem_inter.mpr ⟨hs, hoppR⟩)

  intro T hT huvT
  have hTreal := (mem_oneRedTriangles.mp (mem_residual.mp hT).1).1
  obtain ⟨z, huz, hvz, rfl⟩ := hTreal.exists_third_of_mem huvT
  by_contra hne
  obtain ⟨hTF, hTDisj⟩ := mem_residual.mp hT
  obtain ⟨hZ, hZA, hZR⟩ := mem_oneRedTriangles.mp hTF
  have hxz : x ≠ z := by
    intro h
    exact disjoint_left.mp hTDisj (by simp [h]) huxBlue
  have hyz : y ≠ z := by
    intro h
    apply hne
    subst z
    rfl

  have hnew : triangleEdges u x y ∈ oneRedTriangles A R := by
    apply mem_oneRedTriangles.mpr
    refine ⟨isTriangle_triangleEdges hux huy hxy, ?_, ?_⟩
    · intro e he
      rcases mem_triangleEdges.mp he with rfl | rfl | rfl
      · exact hXA (by simp)
      · exact hYA (by simp)
      · exact hoppA
    · have hinter : triangleEdges u x y ∩ R = {s(x, y)} := by
        ext e
        simp only [mem_inter, mem_triangleEdges, mem_singleton]
        constructor
        · rintro ⟨he, hr⟩
          rcases he with rfl | rfl | rfl
          · exact (huxNotRed hr).elim
          · exact (huyNotRed hr).elim
          · rfl
        · rintro rfl
          exact ⟨Or.inr (Or.inr rfl), hoppR⟩
      simp [hinter]

  have hvertices : [u, x, y, v, z].Nodup := by
    simp [List.nodup_cons, hux, huy, huv, huz, hxy, hvx.symm, hxz,
      hvy.symm, hyz, hvz]
  have hnewDisj : Disjoint (triangleEdges u x y) (triangleEdges u v z) :=
    triangleEdges_disjoint_of_five_distinct hvertices
  have hnewRest : Disjoint (triangleEdges u x y)
      (support (P.erase (triangleEdges u v x))) := by
    apply hP.1.disjoint_support_erase hparent
    intro e he hs
    rcases mem_triangleEdges.mp he with rfl | rfl | rfl
    · simp
    · exact (huyOutside hs).elim
    · exact (hxyOutside hs).elim
  have hotherRest : Disjoint (triangleEdges u v z)
      (support (P.erase (triangleEdges u v x))) := by
    apply hP.1.disjoint_support_erase hparent
    intro e he hs
    have hr : e ∈ R := by
      by_contra hr
      exact disjoint_left.mp hTDisj he (mem_sdiff.mpr ⟨hs, hr⟩)
    have heq := red_edges_eq hZR he hr (by simp) hspine
    rw [heq]
    simp
  exact hP.no_two_for_one hparent hnew hTF
    ⟨s(u, x), by simp⟩ ⟨s(u, v), by simp⟩ hnewDisj hnewRest hotherRest

end Tuza

-- ==== Tuza.Colored.Covers

/-! The two colored covering bounds: Lemma 2.3. -/

namespace Tuza

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem paired_geometry {A R : Finset (Sym2 V)}
    {P Q : Finset (Finset (Sym2 V))}
    (hP : IsMaximumPacking (oneRedTriangles A R) P)
    (hQ : IsPacking (residual (oneRedTriangles A R) (blueEdges R P)) Q)
    (q : {T // T ∈ Q}) :
    ∃ u v x y,
      (Layered.parent (oneRedTriangles_colored A R) hP hQ q).val = triangleEdges u v x ∧
      q.val = triangleEdges u v y ∧ s(u, v) ∈ R ∧ [u, v, x, y].Nodup := by
  classical
  let hF := oneRedTriangles_colored A R
  let p := Layered.parent hF hP hQ q
  have hpF := hP.1.1 p.property
  have hqF := (mem_residual.mp (hQ.1 q.property)).1
  have hn : (p.val ∩ R).Nonempty := card_pos.mp (by rw [(hF p.val hpF).2]; decide)
  obtain ⟨e, he⟩ := hn
  obtain ⟨⟨u, v⟩, rfl⟩ := Sym2.mk_surjective e
  have heq : s(u, v) ∈ q.val ∩ R := Layered.parent_spec hF hP hQ q ▸ he
  have hpReal := (mem_oneRedTriangles.mp hpF).1
  have hqReal := (mem_oneRedTriangles.mp hqF).1
  have huv := hpReal.ne_of_mem (mem_inter.mp he).1
  obtain ⟨x, hux, hvx, hpx⟩ := hpReal.exists_third_of_mem (mem_inter.mp he).1
  obtain ⟨y, huy, hvy, hqy⟩ := hqReal.exists_third_of_mem (mem_inter.mp heq).1
  have hxy : x ≠ y := by
    intro h
    have hpq : p.val = q.val := by rw [hpx, hqy, h]
    exact Layered.residual_member_not_parent hF hQ q.property (hpq ▸ p.property)
  refine ⟨u, v, x, y, hpx, hqy, (mem_inter.mp he).2, ?_⟩
  simp [List.nodup_cons, huv, hux, huy, hvx, hvy, hxy]

/-- A fixed opposite edge handles every triangle that misses the chosen red spines.
If it is needed, the associated residual page has a private red edge. -/
private theorem paired_extra {A R : Finset (Sym2 V)}
    {P Q : Finset (Finset (Sym2 V))}
    (hP : IsMaximumPacking (oneRedTriangles A R) P)
    (hQ : IsPacking (residual (oneRedTriangles A R) (blueEdges R P)) Q)
    (q : {T // T ∈ Q}) :
    ∃ e : Sym2 V, ∀ T ∈ oneRedTriangles A R,
      ¬ Disjoint T (Layered.parent (oneRedTriangles_colored A R) hP hQ q).val →
      ¬ Disjoint T q.val → Disjoint T (redEdges R P) →
      e ∈ T ∧ ∀ W ∈ residual (oneRedTriangles A R) (blueEdges R P),
        W ∩ R = q.val ∩ R → W = q.val := by
  classical
  let hF := oneRedTriangles_colored A R
  let p := Layered.parent hF hP hQ q
  obtain ⟨u, v, x, y, hp, hq, hred, hvertices⟩ := paired_geometry hP hQ q
  refine ⟨s(x, y), ?_⟩
  intro T hT hTp hTq hdR
  have hparent : triangleEdges u v x ∈ P := hp ▸ p.property
  have hpage : triangleEdges u v y ∈
      residual (oneRedTriangles A R) (blueEdges R P) := hq ▸ hQ.1 q.property
  have hspineP : s(u, v) ∈ redEdges R P :=
    mem_redEdges.mpr ⟨mem_support.mpr ⟨triangleEdges u v x, hparent, by simp⟩, hred⟩
  have havoid : s(u, v) ∉ T := fun h => disjoint_left.mp hdR h hspineP
  obtain ⟨ep, hep, hepp⟩ := not_disjoint_iff.mp hTp
  obtain ⟨eq, heq, heqq⟩ := not_disjoint_iff.mp hTq
  have hx : (T ∩ triangleEdges u v x).Nonempty :=
    ⟨ep, mem_inter.mpr ⟨hep, hp ▸ hepp⟩⟩
  have hy : (T ∩ triangleEdges u v y).Nonempty :=
    ⟨eq, mem_inter.mpr ⟨heq, hq ▸ heqq⟩⟩
  have hreal := (mem_oneRedTriangles.mp hT).1
  have hopp := two_page_opposite_mem hreal hvertices havoid hx hy
  have hoppA := (mem_oneRedTriangles.mp hT).2.1 hopp
  have hoppNew : s(x, y) ∉ redEdges R P := fun h => disjoint_left.mp hdR hopp h
  have hoppR : s(x, y) ∈ R := by
    obtain ⟨f, hf⟩ := card_pos.mp (by rw [(hF T hT).2]; decide)
    obtain ⟨hfT, hfR⟩ := mem_inter.mp hf
    have hparentRed : ∀ e ∈ triangleEdges u v x, e ∈ R → e ∈ redEdges R P := by
      intro e he heR
      exact mem_redEdges.mpr ⟨mem_support.mpr ⟨_, hparent, he⟩, heR⟩
    have hchildRed : ∀ e ∈ triangleEdges u v y, e ∈ R → e ∈ redEdges R P := by
      intro e he heR
      exact residual_red_subset_parent_red hF hP hpage (mem_inter.mpr ⟨he, heR⟩)
    rcases two_page_triangle hreal hvertices havoid hx hy with h | h <;>
      rw [h] at hfT <;> rcases mem_triangleEdges.mp hfT with rfl | rfl | rfl
    · exact (disjoint_left.mp hdR (by simp [h])
        (hparentRed _ (by simp) hfR)).elim
    · exact (disjoint_left.mp hdR (by simp [h])
        (hchildRed _ (by simp) hfR)).elim
    · exact hfR
    · exact (disjoint_left.mp hdR (by simp [h])
        (hparentRed _ (by simp) hfR)).elim
    · exact (disjoint_left.mp hdR (by simp [h])
        (hchildRed _ (by simp) hfR)).elim
    · exact hfR
  refine ⟨hopp, ?_⟩
  intro W hW hWR
  have huvQ : s(u, v) ∈ q.val ∩ R := mem_inter.mpr ⟨by simp [hq], hred⟩
  have huvW : s(u, v) ∈ W := (mem_inter.mp (hWR.symm ▸ huvQ)).1
  exact (unique_residual_triangle hP hparent hpage hred hoppA hoppR hoppNew W hW huvW).trans hq.symm

private theorem exists_first_cover_base {A R : Finset (Sym2 V)}
    {P Q J : Finset (Finset (Sym2 V))}
    (hP : IsMaximumPacking (oneRedTriangles A R) P)
    (hQ : IsPacking (residual (oneRedTriangles A R) (blueEdges R P)) Q)
    (hJQ : J ⊆ Q)
    (hJ : ∀ q ∈ Q,
      (∀ W ∈ residual (oneRedTriangles A R) (blueEdges R P),
        W ∩ R = q ∩ R → W = q) → q ∈ J) :
    ∃ C, IsCover (oneRedTriangles A R) C ∧
      support (P \ Layered.pairedParents R P Q) ⊆ C ∧ redEdges R P ⊆ C ∧
      C.card + 2 * Q.card ≤ 3 * P.card + J.card := by
  classical
  let hF := oneRedTriangles_colored A R
  choose opposite hopposite using
    (fun q : {T // T ∈ Q} => paired_extra hP hQ q)
  let W := P \ Layered.pairedParents R P Q
  let extras := J.attach.image (fun q => opposite ⟨q.val, hJQ q.property⟩)
  let base := blueEdges R W ∪ redEdges R P
  let C := base ∪ extras
  have hredC : redEdges R P ⊆ C := by
    intro e he
    exact mem_union_left _ (mem_union_right _ he)
  have hsingleC : support W ⊆ C := by
    intro e he
    apply mem_union_left
    by_cases hr : e ∈ R
    · exact mem_union_right _ (mem_redEdges.mpr
        ⟨support_mono sdiff_subset he, hr⟩)
    · exact mem_union_left _ (mem_blueEdges.mpr ⟨he, hr⟩)
  have hcover : IsCover (oneRedTriangles A R) C := by
    intro T hT
    by_contra hn
    have hd : Disjoint T C := disjoint_left.mpr (fun e heT heC =>
      hn ⟨e, mem_inter.mpr ⟨heT, heC⟩⟩)
    obtain ⟨p, hp⟩ := Books.exists_book_all_pages_meet_of_maximum
      (pages := Layered.twoLayerPages R P Q)
      (fun _ hS => hF.member_nonempty hS)
      (fun _ hf => Layered.choices_maximum hF hP hQ hf) hT
    have hTp := hp p.val (Layered.mem_twoLayerPages.mpr (Or.inl rfl))
    by_cases hpaired : p.val ∈ Layered.pairedParents R P Q
    · obtain ⟨_, q, hqQ, hpq⟩ := Layered.mem_pairedParents.mp hpaired
      have hchosen := Layered.parent_unique hF hP hQ ⟨q, hqQ⟩ p hpq
      have hTq := hp q (Layered.mem_twoLayerPages.mpr (Or.inr ⟨hqQ, hpq.symm⟩))
      have hTp' : ¬ Disjoint T (Layered.parent hF hP hQ ⟨q, hqQ⟩).val := by
        rw [← hchosen]
        exact hTp
      obtain ⟨heT, hprivate⟩ := hopposite ⟨q, hqQ⟩ T hT hTp' hTq (hd.mono_right hredC)
      have hqJ := hJ q hqQ hprivate
      have heExtra : opposite ⟨q, hqQ⟩ ∈ extras :=
        mem_image.mpr ⟨⟨q, hqJ⟩, mem_attach _ _, rfl⟩
      exact disjoint_left.mp hd heT (mem_union_right _ heExtra)
    · obtain ⟨e, heT, hep⟩ := not_disjoint_iff.mp hTp
      have heW : e ∈ support W :=
        mem_support.mpr ⟨p.val, mem_sdiff.mpr ⟨p.property, hpaired⟩, hep⟩
      exact disjoint_left.mp hd heT (hsingleC heW)
  have hWpacking := hP.1.subfamily (sdiff_subset : W ⊆ P)
  have hblue : (blueEdges R W).card = 2 * W.card := hWpacking.card_blueEdges hF
  have hred : (redEdges R P).card = P.card := hP.1.card_redEdges hF
  have hWcard : W.card + Q.card = P.card := by
    have h := card_sdiff_add_card_eq_card (Layered.pairedParents_subset R P Q)
    rw [Layered.pairedParents_card hF hP hQ] at h
    exact h
  have hextras : extras.card ≤ J.card := by
    calc
      extras.card ≤ J.attach.card := card_image_le
      _ = J.card := card_attach
  have hcard : C.card ≤ (blueEdges R W).card + (redEdges R P).card + J.card := by
    calc
      C.card ≤ base.card + extras.card := card_union_le _ _
      _ ≤ (blueEdges R W).card + (redEdges R P).card + J.card :=
        Nat.add_le_add (card_union_le _ _) hextras
  refine ⟨C, hcover, hsingleC, hredC, ?_⟩
  omega

/-- The first cover includes one opposite edge for each private residual page.
Every opposite edge that is actually needed is assigned to such a page by
`paired_extra`; counting additional private pages only enlarges the bound. -/
theorem exists_first_colored_cover {A R : Finset (Sym2 V)}
    {P Q U : Finset (Finset (Sym2 V))}
    (hP : IsMaximumPacking (oneRedTriangles A R) P)
    (hQ : IsPacking (residual (oneRedTriangles A R) (blueEdges R P)) Q)
    (hU : U ⊆ privateRedPages (oneRedTriangles A R) R P) :
    ∃ C, IsCover (oneRedTriangles A R) C ∧
      C.card + 2 * Q.card + U.card ≤ 3 * P.card +
        (privateRedPages (residual (oneRedTriangles A R) (blueEdges R P)) R Q).card := by
  classical
  let hF := oneRedTriangles_colored A R
  let J := privateRedPages (residual (oneRedTriangles A R) (blueEdges R P)) R Q
  have hJQ : J ⊆ Q := privateRedPages_subset _ _ _
  have hJ : ∀ q ∈ Q,
      (∀ W ∈ residual (oneRedTriangles A R) (blueEdges R P),
        W ∩ R = q ∩ R → W = q) → q ∈ J := by
    intro q hq hp
    exact mem_privateRedPages.mpr ⟨hq, hp⟩
  obtain ⟨C, hC, hsingle, hred, hcard⟩ := exists_first_cover_base hP hQ hJQ hJ
  have hUP : U ⊆ P := hU.trans (privateRedPages_subset _ _ _)
  have hUunpaired : U ⊆ P \ Layered.pairedParents R P Q := by
    intro p hp
    obtain ⟨hpP, hprivate⟩ := mem_privateRedPages.mp (hU hp)
    refine mem_sdiff.mpr ⟨hpP, ?_⟩
    intro hpaired
    obtain ⟨_, q, hq, hpq⟩ := Layered.mem_pairedParents.mp hpaired
    have hqp := hprivate q (mem_residual.mp (hQ.1 hq)).1 hpq.symm
    exact Layered.residual_member_not_parent hF hQ hq (hqp.symm ▸ hpP)
  have hblueU : blueEdges R U ⊆ C :=
    (blueEdges_subset_support _ _).trans ((support_mono hUunpaired).trans hsingle)
  have hredU : redEdges R U ⊆ C := by
    intro e he
    obtain ⟨heU, heR⟩ := mem_redEdges.mp he
    exact hred (mem_redEdges.mpr ⟨support_mono hUP heU, heR⟩)
  have hremoved := hC.sdiff_privateRed hF hP.1 hU hblueU
  have hsize := card_sdiff_privateRed hF hP.1 hU hredU
  refine ⟨C \ redEdges R U, hremoved, ?_⟩
  change (C \ redEdges R U).card + 2 * Q.card + U.card ≤ 3 * P.card + J.card
  omega

theorem first_colored_cover {A R : Finset (Sym2 V)}
    {P Q U : Finset (Finset (Sym2 V))}
    (hP : IsMaximumPacking (oneRedTriangles A R) P)
    (hQ : IsPacking (residual (oneRedTriangles A R) (blueEdges R P)) Q)
    (hU : U ⊆ privateRedPages (oneRedTriangles A R) R P) :
    transversalNumber (oneRedTriangles A R) + 2 * Q.card + U.card ≤ 3 * P.card +
      (privateRedPages (residual (oneRedTriangles A R) (blueEdges R P)) R Q).card := by
  obtain ⟨C, hC, hc⟩ := exists_first_colored_cover hP hQ hU
  exact (Nat.add_le_add_right (Nat.add_le_add_right hC.number_le _) _).trans hc

/-- The first colored bound: equation (1). -/
theorem colored_bound {A R : Finset (Sym2 V)}
    {P Q U : Finset (Finset (Sym2 V))}
    (hP : IsMaximumPacking (oneRedTriangles A R) P)
    (hQ : IsMaximumPacking (residual (oneRedTriangles A R) (blueEdges R P)) Q)
    (hU : U ⊆ privateRedPages (oneRedTriangles A R) R P) :
    3 * transversalNumber (oneRedTriangles A R) + 2 * U.card ≤ 8 * P.card := by
  have hfirst := first_colored_cover hP hQ.1 hU
  have hsecond := second_colored_cover (oneRedTriangles_colored A R) hP.1 hQ
  have hr := card_le_card
    (privateRedPages_subset (residual (oneRedTriangles A R) (blueEdges R P)) R Q)
  exact colored_bound_arithmetic hfirst hsecond hr

/-- Apply the first bound to the family left after deleting the parent blue edges. -/
theorem colored_refined {A R : Finset (Sym2 V)}
    {P Q U : Finset (Finset (Sym2 V))}
    (hP : IsMaximumPacking (oneRedTriangles A R) P)
    (hQ : IsMaximumPacking (residual (oneRedTriangles A R) (blueEdges R P)) Q)
    (hU : U ⊆ privateRedPages (oneRedTriangles A R) R P) :
    4 * transversalNumber (oneRedTriangles A R) + U.card ≤
      9 * P.card + 6 * Q.card := by
  have hfirst := first_colored_cover hP hQ.1 hU
  have hQ' : IsMaximumPacking (oneRedTriangles (A \ blueEdges R P) R) Q := by
    rw [oneRedTriangles_sdiff]
    exact hQ
  have hlocal :
      3 * transversalNumber (residual (oneRedTriangles A R) (blueEdges R P)) +
        2 * (privateRedPages (residual (oneRedTriangles A R) (blueEdges R P)) R Q).card
      ≤ 8 * Q.card := by
    rw [← oneRedTriangles_sdiff A R (blueEdges R P)]
    exact colored_bound hQ' (maximumPacking_spec _) (Subset.refl _)
  have hdelete := transversalNumber_le_add_residual (oneRedTriangles A R) (blueEdges R P)
    (fun _ hT => (oneRedTriangles_colored A R).member_nonempty hT)
  have hblue : (blueEdges R P).card = 2 * P.card :=
    hP.1.card_blueEdges (oneRedTriangles_colored A R)
  have hresidual : 3 * transversalNumber (oneRedTriangles A R) +
      2 * (privateRedPages (residual (oneRedTriangles A R) (blueEdges R P)) R Q).card
      ≤ 6 * P.card + 8 * Q.card := by omega
  exact colored_refined_arithmetic hfirst hresidual

end Tuza

-- ==== Tuza.Construction.ColoredCover

/-! The refined colored cover of the full graph: equation (6). -/

namespace Tuza
namespace Construction

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {edges : Finset (Sym2 V)}

/-- The fourth cover consists of the first packing, the old edges of the
remaining packing, and a minimum cover of the complete special family. -/
theorem exists_fourth_cover (c : Construction edges)
    {Q Q1 : Finset (Finset (Sym2 V))}
    (hQ : IsMaximumPacking c.specialFamily Q)
    (hQ1 : IsMaximumPacking (residual c.specialFamily (blueEdges c.newEdges Q)) Q1) :
    ∃ C, IsCover (trianglesOn edges) C ∧
      4 * C.card + 4 * c.typeTwo.card + (privateRedPages c.specialFamily c.newEdges Q).card
      ≤ 12 * c.initial.card + 9 * Q.card + 6 * Q1.card := by
  classical
  have hcolored :
      4 * transversalNumber c.specialFamily + (privateRedPages c.specialFamily c.newEdges Q).card
      ≤ 9 * Q.card + 6 * Q1.card :=
    colored_refined hQ hQ1 (Subset.refl _)
  obtain ⟨D, hD, hDcard⟩ := exists_minimumCover c.specialFamily
    (fun _ hT => c.specialFamily_colored.member_nonempty hT)
  have hDres :
      IsCover (residual (trianglesOn c.remainingEdges) (support c.rest ∩ c.old)) D := by
    rw [← c.specialFamily_eq_residual]
    exact hD
  have hremaining := cover_union_residual hDres
  have hremainingRes : IsCover (residual (trianglesOn edges) (support c.first))
      ((support c.rest ∩ c.old) ∪ D) := by
    rw [← trianglesOn_sdiff edges (support c.first)]
    exact hremaining
  let C := support c.first ∪ ((support c.rest ∩ c.old) ∪ D)
  have hC : IsCover (trianglesOn edges) C := cover_union_residual hremainingRes
  have hCcard : C.card ≤ (support c.first).card + (support c.rest ∩ c.old).card + D.card := by
    calc
      C.card ≤ (support c.first).card + ((support c.rest ∩ c.old) ∪ D).card :=
        card_union_le _ _
      _ ≤ (support c.first).card + ((support c.rest ∩ c.old).card + D.card) :=
        Nat.add_le_add_left (card_union_le _ _) _
      _ = (support c.first).card + (support c.rest ∩ c.old).card + D.card := by omega
  have hfirst : (support c.first).card = 3 * c.first.card :=
    c.first_packing.card_support_uniform (fun _ hT => trianglesOn_card (c.first_packing.1 hT))
  have hrest : (support c.rest).card = 3 * c.rest.card :=
    c.rest_packing.card_support_uniform (fun _ hT => trianglesOn_card (c.rest_packing.1 hT))
  have hnew : (support c.rest \ c.old).card = c.typeTwo.card := c.card_newEdges
  have hsplit := card_sdiff_add_card_inter (support c.rest) c.old
  have hpack := c.first_rest_card_le
  refine ⟨C, hC, ?_⟩
  omega

theorem fourth_cover (c : Construction edges)
    {Q Q1 : Finset (Finset (Sym2 V))}
    (hQ : IsMaximumPacking c.specialFamily Q)
    (hQ1 : IsMaximumPacking (residual c.specialFamily (blueEdges c.newEdges Q)) Q1) :
    4 * transversalNumber (trianglesOn edges) + 4 * c.typeTwo.card +
      (privateRedPages c.specialFamily c.newEdges Q).card
      ≤ 12 * c.initial.card + 9 * Q.card + 6 * Q1.card := by
  obtain ⟨C, hC, hcard⟩ := c.exists_fourth_cover hQ hQ1
  have hbound := hC.number_le
  omega

end Construction
end Tuza

-- ==== Tuza.Construction.FirstCover

/-!
The first book cover uses a maximum packing and a packing of type-1 triangles.
A two-for-one exchange shows that distinct type-1 pages have distinct parents.
-/

namespace Tuza
namespace FirstCover

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {A : Finset (Sym2 V)} {P Q : Finset (Finset (Sym2 V))}

def children (P Q : Finset (Finset (Sym2 V))) (p : Finset (Sym2 V)) :
    Finset (Finset (Sym2 V)) := Q.filter (fun q => q ∩ support P ⊆ p)

def pages (P Q : Finset (Finset (Sym2 V))) (p : {T // T ∈ P}) :
    Finset (Finset (Sym2 V)) := insert p.val (children P Q p.val)

omit [Fintype V] in
@[simp] theorem mem_children {p q : Finset (Sym2 V)} :
    q ∈ children P Q p ↔ q ∈ Q ∧ q ∩ support P ⊆ p := by
  simp [children]

omit [Fintype V] in
@[simp] theorem mem_pages {p : {T // T ∈ P}} {T : Finset (Sym2 V)} :
    T ∈ pages P Q p ↔ T = p.val ∨ (T ∈ Q ∧ T ∩ support P ⊆ p.val) := by
  simp [pages]

theorem old_inter_nonempty (hQ : IsPacking (typeFamily A (support P) 1) Q)
    {q : Finset (Sym2 V)} (hq : q ∈ Q) : (q ∩ support P).Nonempty := by
  apply card_pos.mp
  rw [(mem_typeFamily.mp (hQ.1 hq)).2]
  decide

theorem exists_parent (hQ : IsPacking (typeFamily A (support P) 1) Q)
    (q : {T // T ∈ Q}) : ∃ p : {T // T ∈ P}, q.val ∩ support P ⊆ p.val := by
  obtain ⟨e, heq⟩ := card_eq_one.mp (mem_typeFamily.mp (hQ.1 q.property)).2
  have he : e ∈ q.val ∩ support P := by rw [heq]; simp
  obtain ⟨p, hp, hep⟩ := mem_support.mp (mem_inter.mp he).2
  refine ⟨⟨p, hp⟩, ?_⟩
  rw [heq]
  exact singleton_subset_iff.mpr hep

noncomputable def parent (hQ : IsPacking (typeFamily A (support P) 1) Q)
    (q : {T // T ∈ Q}) : {T // T ∈ P} := Classical.choose (exists_parent hQ q)

theorem parent_spec (hQ : IsPacking (typeFamily A (support P) 1) Q)
    (q : {T // T ∈ Q}) : q.val ∩ support P ⊆ (parent hQ q).val :=
  Classical.choose_spec (exists_parent hQ q)

theorem owner_unique (hP : IsPacking (trianglesOn A) P)
    (hQ : IsPacking (typeFamily A (support P) 1) Q) {q : Finset (Sym2 V)}
    (hq : q ∈ Q) (p p' : {T // T ∈ P})
    (hp : q ∩ support P ⊆ p.val) (hp' : q ∩ support P ⊆ p'.val) : p = p' := by
  by_contra hne
  have hval : p.val ≠ p'.val := fun h => hne (Subtype.ext h)
  obtain ⟨e, he⟩ := old_inter_nonempty hQ hq
  exact disjoint_left.mp (hP.2 p.property p'.property hval) (hp he) (hp' he)

theorem parent_unique (hP : IsPacking (trianglesOn A) P)
    (hQ : IsPacking (typeFamily A (support P) 1) Q) (q : {T // T ∈ Q})
    (p : {T // T ∈ P}) (hp : q.val ∩ support P ⊆ p.val) : p = parent hQ q :=
  owner_unique hP hQ q.property p (parent hQ q) hp (parent_spec hQ q)

theorem parent_injective (hP : IsMaximumPacking (trianglesOn A) P)
    (hQ : IsPacking (typeFamily A (support P) 1) Q) :
    Function.Injective (parent hQ) := by
  intro q q' heq
  by_contra hne
  have hval : q.val ≠ q'.val := fun h => hne (Subtype.ext h)
  have hqt := (mem_typeFamily.mp (hQ.1 q.property)).1
  have hq't := (mem_typeFamily.mp (hQ.1 q'.property)).1
  have havoid : Disjoint q.val (support (P.erase (parent hQ q).val)) := by
    apply hP.1.disjoint_support_erase (parent hQ q).property
    intro e heq heP
    exact parent_spec hQ q (mem_inter.mpr ⟨heq, heP⟩)
  have havoid' : Disjoint q'.val (support (P.erase (parent hQ q).val)) := by
    apply hP.1.disjoint_support_erase (parent hQ q).property
    intro e heq' heP
    have h := parent_spec hQ q' (mem_inter.mpr ⟨heq', heP⟩)
    simpa only [← heq] using h
  exact hP.no_two_for_one (parent hQ q).property hqt hq't
    (trianglesOn_nonempty hqt) (trianglesOn_nonempty hq't)
    (hQ.2 q.property q'.property hval) havoid havoid'

theorem child_not_parent (hQ : IsPacking (typeFamily A (support P) 1) Q)
    {q : Finset (Sym2 V)} (hq : q ∈ Q) : q ∉ P := by
  intro hp
  have heq : q ∩ support P = q := by
    apply inter_eq_left.mpr
    intro e he
    exact mem_support.mpr ⟨q, hp, he⟩
  have hc := (mem_typeFamily.mp (hQ.1 hq)).2
  have ht := trianglesOn_card (mem_typeFamily.mp (hQ.1 hq)).1
  rw [heq] at hc
  omega

theorem children_card_le_one (hP : IsMaximumPacking (trianglesOn A) P)
    (hQ : IsPacking (typeFamily A (support P) 1) Q) (p : {T // T ∈ P}) :
    (children P Q p.val).card ≤ 1 := by
  apply card_le_one.mpr
  intro q hq q' hq'
  obtain ⟨hqQ, hqp⟩ := mem_children.mp hq
  obtain ⟨hq'Q, hq'p⟩ := mem_children.mp hq'
  have h₁ := parent_unique hP.1 hQ ⟨q, hqQ⟩ p hqp
  have h₂ := parent_unique hP.1 hQ ⟨q', hq'Q⟩ p hq'p
  exact congrArg Subtype.val (parent_injective hP hQ (h₁.symm.trans h₂))

theorem parent_not_child (hQ : IsPacking (typeFamily A (support P) 1) Q)
    (p : {T // T ∈ P}) : p.val ∉ children P Q p.val := by
  intro hp
  exact child_not_parent hQ (mem_children.mp hp).1 p.property

omit [Fintype V] in
theorem pages_nonempty (P Q : Finset (Finset (Sym2 V))) (p : {T // T ∈ P}) :
    (pages P Q p).Nonempty := ⟨p.val, mem_insert_self _ _⟩

theorem pages_subset_family (hP : IsPacking (trianglesOn A) P)
    (hQ : IsPacking (typeFamily A (support P) 1) Q) (p : {T // T ∈ P}) :
    pages P Q p ⊆ trianglesOn A := by
  intro T hT
  rcases mem_pages.mp hT with rfl | ⟨hTQ, _⟩
  · exact hP.1 p.property
  · exact (mem_typeFamily.mp (hQ.1 hTQ)).1

theorem pages_card_le_two (hP : IsMaximumPacking (trianglesOn A) P)
    (hQ : IsPacking (typeFamily A (support P) 1) Q) (p : {T // T ∈ P}) :
    (pages P Q p).card ≤ 2 := by
  have hle := children_card_le_one hP hQ p
  rw [pages, card_insert_of_notMem (parent_not_child hQ p)]
  omega

theorem book_inter_parent_subset (_hQ : IsPacking (typeFamily A (support P) 1) Q)
    (p : {T // T ∈ P}) : support (pages P Q p) ∩ support P ⊆ p.val := by
  intro e he
  obtain ⟨heb, heP⟩ := mem_inter.mp he
  obtain ⟨T, hT, heT⟩ := mem_support.mp heb
  rcases mem_pages.mp hT with rfl | ⟨_, hsub⟩
  · exact heT
  · exact hsub (mem_inter.mpr ⟨heT, heP⟩)

theorem supports_disjoint (hP : IsMaximumPacking (trianglesOn A) P)
    (hQ : IsPacking (typeFamily A (support P) 1) Q) :
    Books.DisjointSupports (pages P Q) := by
  intro p p' hne
  have hval : p.val ≠ p'.val := fun h => hne (Subtype.ext h)
  have hd := hP.1.2 p.property p'.property hval
  apply disjoint_left.mpr
  intro e he he'
  obtain ⟨T, hT, heT⟩ := mem_support.mp he
  obtain ⟨U, hU, heU⟩ := mem_support.mp he'
  rcases mem_pages.mp hT with rfl | ⟨hTQ, hsubT⟩
  · have hep' := book_inter_parent_subset hQ p'
      (mem_inter.mpr ⟨he', mem_support.mpr ⟨p.val, p.property, heT⟩⟩)
    exact disjoint_left.mp hd heT hep'
  · rcases mem_pages.mp hU with rfl | ⟨hUQ, hsubU⟩
    · have hep := book_inter_parent_subset hQ p
        (mem_inter.mpr ⟨he, mem_support.mpr ⟨p'.val, p'.property, heU⟩⟩)
      exact disjoint_left.mp hd hep heU
    · have hTU : T ≠ U := by
        intro hEq
        subst U
        exact hne (owner_unique hP.1 hQ hTQ p p' hsubT hsubU)
      exact disjoint_left.mp (hQ.2 hTQ hUQ hTU) heT heU

theorem choices_maximum (hP : IsMaximumPacking (trianglesOn A) P)
    (hQ : IsPacking (typeFamily A (support P) 1) Q)
    {f : {T // T ∈ P} → Finset (Sym2 V)} (hf : Books.ChoosesPages (pages P Q) f) :
    IsMaximumPacking (trianglesOn A) (Books.choice f) := by
  apply Books.choice_isMaximumPacking (pages_subset_family hP.1 hQ)
    (supports_disjoint hP hQ)
    (fun p T hT => trianglesOn_nonempty (pages_subset_family hP.1 hQ p hT)) ?_ hf
  intro K hK
  simpa using hP.2 K hK

theorem everyChoiceMeets (hP : IsMaximumPacking (trianglesOn A) P)
    (hQ : IsPacking (typeFamily A (support P) 1) Q) :
    Books.EveryChoiceMeets (trianglesOn A) (pages P Q) :=
  Books.everyChoiceMeets_of_maximum (fun _ hT => trianglesOn_nonempty hT)
    (fun _ hf => choices_maximum hP hQ hf)

theorem children_pairwise_disjoint (hP : IsPacking (trianglesOn A) P)
    (hQ : IsPacking (typeFamily A (support P) 1) Q) :
    Pairwise (fun p p' : {T // T ∈ P} =>
      Disjoint (children P Q p.val) (children P Q p'.val)) := by
  intro p p' hne
  apply disjoint_left.mpr
  intro q hq hq'
  obtain ⟨hqQ, hsub⟩ := mem_children.mp hq
  obtain ⟨_, hsub'⟩ := mem_children.mp hq'
  exact hne (owner_unique hP hQ hqQ p p' hsub hsub')

theorem children_biUnion (hQ : IsPacking (typeFamily A (support P) 1) Q) :
    univ.biUnion (fun p : {T // T ∈ P} => children P Q p.val) = Q := by
  ext q
  constructor
  · intro hq
    obtain ⟨p, _, hp⟩ := mem_biUnion.mp hq
    exact (mem_children.mp hp).1
  · intro hq
    exact mem_biUnion.mpr ⟨parent hQ ⟨q, hq⟩, mem_univ _,
      mem_children.mpr ⟨hq, parent_spec hQ ⟨q, hq⟩⟩⟩

theorem sum_children_card (hP : IsPacking (trianglesOn A) P)
    (hQ : IsPacking (typeFamily A (support P) 1) Q) :
    (∑ p : {T // T ∈ P}, (children P Q p.val).card) = Q.card := by
  conv_rhs => rw [← children_biUnion hQ]
  symm
  apply card_biUnion
  intro p _ p' _ hne
  exact children_pairwise_disjoint hP hQ hne

theorem sum_pages_card (hP : IsPacking (trianglesOn A) P)
    (hQ : IsPacking (typeFamily A (support P) 1) Q) :
    (∑ p : {T // T ∈ P}, (pages P Q p).card) = P.card + Q.card := by
  have hc : ∀ p : {T // T ∈ P}, (pages P Q p).card = (children P Q p.val).card + 1 := by
    intro p
    exact card_insert_of_notMem (parent_not_child hQ p)
  calc
    (∑ p : {T // T ∈ P}, (pages P Q p).card) =
        ∑ p : {T // T ∈ P}, ((children P Q p.val).card + 1) := sum_congr rfl (fun p _ => hc p)
    _ = P.card + Q.card := by rw [sum_add_distrib, sum_children_card hP hQ]; simp [Nat.add_comm]

theorem pages_common_edge (hP : IsMaximumPacking (trianglesOn A) P)
    (hQ : IsPacking (typeFamily A (support P) 1) Q) (p : {T // T ∈ P}) :
    ∃ e, ∀ T ∈ pages P Q p, e ∈ T := by
  by_cases hn : (children P Q p.val).Nonempty
  · obtain ⟨q, hq⟩ := hn
    obtain ⟨hqQ, hsubq⟩ := mem_children.mp hq
    obtain ⟨e, he⟩ := old_inter_nonempty hQ hqQ
    refine ⟨e, ?_⟩
    intro T hT
    rcases mem_pages.mp hT with rfl | ⟨hTQ, hsubT⟩
    · exact hsubq he
    · have hTchild := mem_children.mpr ⟨hTQ, hsubT⟩
      have hTq : T = q := card_le_one.mp (children_card_le_one hP hQ p) T hTchild q hq
      subst T
      exact (mem_inter.mp he).1
  · have hempty := not_nonempty_iff_eq_empty.mp hn
    obtain ⟨e, he⟩ := trianglesOn_nonempty (hP.1.1 p.property)
    refine ⟨e, ?_⟩
    intro T hT
    have ht : T = p.val := by simpa [pages, hempty] using hT
    subst T
    exact he

/-- The first cover saves one edge for every packed type-1 triangle. -/
theorem exists_first_cover (hP : IsMaximumPacking (trianglesOn A) P)
    (hQ : IsPacking (typeFamily A (support P) 1) Q) :
    ∃ C : Finset (Sym2 V), IsCover (trianglesOn A) C ∧ C.card + Q.card ≤ 3 * P.card := by
  obtain ⟨C, hC, hbound⟩ := exists_cover_of_small_common_spine_books
    (trianglesOn A) (pages P Q) (pages_nonempty P Q)
    (fun p => (pages_card_le_two hP hQ p).trans (by decide))
    (fun p T hT => (mem_trianglesOn.mp (pages_subset_family hP.1 hQ p hT)).1)
    (pages_common_edge hP hQ) (fun T hT => (mem_trianglesOn.mp hT).1)
    (everyChoiceMeets hP hQ)
  rw [sum_pages_card hP.1 hQ] at hbound
  simp only [Fintype.card_coe] at hbound
  exact ⟨C, hC, by omega⟩

theorem transversalNumber_add_typeOne_packing_le (hP : IsMaximumPacking (trianglesOn A) P)
    (hQ : IsPacking (typeFamily A (support P) 1) Q) :
    transversalNumber (trianglesOn A) + Q.card ≤ 3 * P.card := by
  obtain ⟨C, hC, hbound⟩ := exists_first_cover hP hQ
  have ht := hC.number_le
  omega

end FirstCover
end Tuza

-- ==== Tuza.Probability.Average

/-! Finite rational averages and uniformly chosen Boolean vertex colorings. -/

namespace Tuza

open scoped BigOperators

variable {Ω : Type*} {Ω' : Type*} {I : Type*} {V : Type*}

/-- The uniform average on a finite type, with values in the rationals. -/
def finiteAverage [Fintype Ω] (f : Ω → ℚ) : ℚ :=
  (∑ ω, f ω) / Fintype.card Ω

/-- The uniform average over all Boolean vertex colorings. -/
def bitAverage [Fintype V] [DecidableEq V] (f : (V → Bool) → ℚ) : ℚ :=
  finiteAverage f

theorem finiteAverage_equiv [Fintype Ω] [Fintype Ω']
    (e : Ω ≃ Ω') (f : Ω' → ℚ) :
    finiteAverage (fun ω => f (e ω)) = finiteAverage f := by
  unfold finiteAverage
  rw [e.sum_comp, Fintype.card_congr e]

theorem finiteAverage_const [Fintype Ω] [Nonempty Ω] (c : ℚ) :
    finiteAverage (fun _ : Ω => c) = c := by
  have hn : (Fintype.card Ω : ℚ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp [finiteAverage, hn]

theorem finiteAverage_add [Fintype Ω] (f g : Ω → ℚ) :
    finiteAverage (fun ω => f ω + g ω) = finiteAverage f + finiteAverage g := by
  simp only [finiteAverage, Finset.sum_add_distrib, add_div]

theorem finiteAverage_finset_sum [Fintype Ω] (s : Finset I) (f : I → Ω → ℚ) :
    finiteAverage (fun ω => ∑ i ∈ s, f i ω) =
      ∑ i ∈ s, finiteAverage (f i) := by
  unfold finiteAverage
  rw [Finset.sum_comm, Finset.sum_div]

theorem finiteAverage_mono [Fintype Ω] (f g : Ω → ℚ)
    (h : ∀ ω, f ω ≤ g ω) : finiteAverage f ≤ finiteAverage g := by
  unfold finiteAverage
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun ω _ => h ω)
    (by positivity)

/-- Some outcome costs no more than its uniform finite average. -/
theorem exists_le_finiteAverage [Fintype Ω] [Nonempty Ω] (f : Ω → ℚ) :
    ∃ ω, f ω ≤ finiteAverage f := by
  classical
  obtain ⟨ω, _, hω⟩ :=
    Finset.exists_min_image (Finset.univ : Finset Ω) f Finset.univ_nonempty
  refine ⟨ω, ?_⟩
  have hn : (0 : ℚ) < Fintype.card Ω := by
    exact_mod_cast Fintype.card_pos
  apply (le_div_iff₀ hn).2
  calc
    f ω * (Fintype.card Ω : ℚ) = ∑ _ : Ω, f ω := by simp [mul_comm]
    _ ≤ ∑ a : Ω, f a := Finset.sum_le_sum fun a ha => hω a ha

private theorem finiteAverage_prod_fst [Fintype Ω] [Fintype Ω']
    [Nonempty Ω] [Nonempty Ω'] (f : Ω → ℚ) :
    finiteAverage (fun p : Ω × Ω' => f p.1) = finiteAverage f := by
  have ha : (Fintype.card Ω : ℚ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hb : (Fintype.card Ω' : ℚ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  unfold finiteAverage
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Fintype.card_prod, Nat.cast_mul]
  rw [← Finset.mul_sum]
  field_simp

/-- Uniform Boolean colorings restrict uniformly to any list of distinct
vertices.  This is the finite independence statement used below. -/
theorem bitAverage_restrict [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
    (v : I → V) (hv : Function.Injective v) (f : (I → Bool) → ℚ) :
    bitAverage (fun χ : V → Bool => f (χ ∘ v)) = bitAverage f := by
  letI : DecidablePred (fun a : V => a ∈ Set.range v) :=
    fun _ => Classical.propDecidable _
  let e : (V → Bool) ≃
      (I → Bool) × ({a : V // a ∉ Set.range v} → Bool) :=
    (Equiv.piEquivPiSubtypeProd (fun a => a ∈ Set.range v) (fun _ => Bool)).trans
      (Equiv.prodCongr
        (Equiv.arrowCongr (Equiv.ofInjective v hv).symm (Equiv.refl Bool))
        (Equiv.refl _))
  have he (χ : V → Bool) : (e χ).1 = χ ∘ v := by
    rfl
  change finiteAverage (fun χ : V → Bool => f (χ ∘ v)) = finiteAverage f
  calc
    finiteAverage (fun χ : V → Bool => f (χ ∘ v)) =
        finiteAverage (fun χ : V → Bool => f (e χ).1) := by
      simp only [he]
    _ = finiteAverage (fun p :
        (I → Bool) × ({a : V // a ∉ Set.range v} → Bool) => f p.1) :=
      finiteAverage_equiv e (fun p => f p.1)
    _ = finiteAverage f := finiteAverage_prod_fst f

/-- An edge is noncrossing when its endpoints have the same Boolean color. -/
def sameColor (u v : V) (χ : V → Bool) : Prop := χ u = χ v

/-- The event allowing an opposite edge of a two-page book to be added. -/
def bookEvent (u v x y : V) (χ : V → Bool) : Prop :=
  χ x = χ y ∧ (χ u ≠ χ x ∨ χ v ≠ χ x)

instance (u v : V) : DecidablePred (sameColor u v) :=
  fun _ => inferInstanceAs (Decidable (_ = _))

instance (u v x y : V) : DecidablePred (bookEvent u v x y) :=
  fun _ => inferInstanceAs (Decidable (_ ∧ (_ ∨ _)))

/-- Two distinct vertices agree in exactly half of all Boolean colorings. -/
theorem sameColor_average [Fintype V] [DecidableEq V] (u v : V) (huv : u ≠ v) :
    bitAverage (fun χ => if sameColor u v χ then (1 : ℚ) else 0) = 1 / 2 := by
  have hi : Function.Injective (![u, v] : Fin 2 → V) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  have h := bitAverage_restrict (![u, v] : Fin 2 → V) hi
    (fun χ => if χ 0 = χ 1 then (1 : ℚ) else 0)
  have hsmall : bitAverage
      (fun χ : Fin 2 → Bool => if χ 0 = χ 1 then (1 : ℚ) else 0) = 1 / 2 := by
    decide +kernel
  calc
    bitAverage (fun χ => if sameColor u v χ then (1 : ℚ) else 0) =
        bitAverage (fun χ : V → Bool =>
          if (χ ∘ (![u, v] : Fin 2 → V)) 0 =
              (χ ∘ (![u, v] : Fin 2 → V)) 1 then (1 : ℚ) else 0) := by
      congr 1
    _ = 1 / 2 := h.trans hsmall

/-- The book event occurs in six of the sixteen local Boolean colorings. -/
theorem bookEvent_average_of_injective [Fintype V] [DecidableEq V] (u v x y : V)
    (h : Function.Injective (![u, v, x, y] : Fin 4 → V)) :
    bitAverage (fun χ => if bookEvent u v x y χ then (1 : ℚ) else 0) = 3 / 8 := by
  have hr := bitAverage_restrict (![u, v, x, y] : Fin 4 → V) h
    (fun χ => if χ 2 = χ 3 ∧ (χ 0 ≠ χ 2 ∨ χ 1 ≠ χ 2) then (1 : ℚ) else 0)
  have hsmall : bitAverage (fun χ : Fin 4 → Bool =>
      if χ 2 = χ 3 ∧ (χ 0 ≠ χ 2 ∨ χ 1 ≠ χ 2) then (1 : ℚ) else 0) = 3 / 8 := by
    decide +kernel
  calc
    bitAverage (fun χ => if bookEvent u v x y χ then (1 : ℚ) else 0) =
        bitAverage (fun χ : V → Bool =>
          if (χ ∘ (![u, v, x, y] : Fin 4 → V)) 2 =
              (χ ∘ (![u, v, x, y] : Fin 4 → V)) 3 ∧
            ((χ ∘ (![u, v, x, y] : Fin 4 → V)) 0 ≠
              (χ ∘ (![u, v, x, y] : Fin 4 → V)) 2 ∨
             (χ ∘ (![u, v, x, y] : Fin 4 → V)) 1 ≠
              (χ ∘ (![u, v, x, y] : Fin 4 → V)) 2) then (1 : ℚ) else 0) := by
      congr 1
    _ = 3 / 8 := hr.trans hsmall

theorem bookEvent_average [Fintype V] [DecidableEq V] (u v x y : V)
    (huv : u ≠ v) (hux : u ≠ x) (huy : u ≠ y)
    (hvx : v ≠ x) (hvy : v ≠ y) (hxy : x ≠ y) :
    bitAverage (fun χ => if bookEvent u v x y χ then (1 : ℚ) else 0) = 3 / 8 := by
  apply bookEvent_average_of_injective
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

end Tuza

-- ==== Tuza.Probability.Cut

/-!
The random-cut cover selects W, noncrossing old edges, and each uncovered
triangle's new edges. When each triangle has at least two old edges, every
added edge is noncrossing.
-/

namespace Tuza

open Finset
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- An unoriented edge is noncrossing when its two colors agree. -/
def noncrossingEdge (χ : V → Bool) (e : Sym2 V) : Prop :=
  (Sym2.map χ e).IsDiag

instance (χ : V → Bool) : DecidablePred (noncrossingEdge χ) :=
  fun e => inferInstanceAs (Decidable (Sym2.map χ e).IsDiag)

omit [Fintype V] [DecidableEq V] in
@[simp] theorem noncrossingEdge_pair (χ : V → Bool) (u v : V) :
    noncrossingEdge χ s(u, v) ↔ χ u = χ v := by
  simp [noncrossingEdge]

/-- The old edges selected before any uncovered triangles are considered. -/
def selectedOld (W O : Finset (Sym2 V)) (χ : V → Bool) : Finset (Sym2 V) :=
  W ∪ O.filter (noncrossingEdge χ)

/-- Add every non-old edge of every triangle that the selected old edges miss.
Using a union counts a repeated edge only once. -/
noncomputable def cutAddedEdges (A W O : Finset (Sym2 V)) (χ : V → Bool) :
    Finset (Sym2 V) :=
  (residual (trianglesOn A) (selectedOld W O χ)).biUnion (fun T => T \ O)

noncomputable def cutCover (A W O : Finset (Sym2 V)) (χ : V → Bool) :
    Finset (Sym2 V) := selectedOld W O χ ∪ cutAddedEdges A W O χ

@[simp] theorem mem_cutAddedEdges {A W O : Finset (Sym2 V)} {χ : V → Bool}
    {e : Sym2 V} :
    e ∈ cutAddedEdges A W O χ ↔
      ∃ T ∈ residual (trianglesOn A) (selectedOld W O χ), e ∈ T \ O := by
  classical
  simp [cutAddedEdges]

omit [Fintype V] in
/-- Every triangle has a noncrossing edge under a Boolean vertex coloring. -/
theorem IsTriangle.exists_noncrossing {T : Finset (Sym2 V)} (hT : IsTriangle T)
    (χ : V → Bool) : ∃ e ∈ T, noncrossingEdge χ e := by
  obtain ⟨u, v, w, huv, huw, hvw, rfl⟩ := hT
  have h : χ u = χ v ∨ χ u = χ w ∨ χ v = χ w := by
    cases χ u <;> cases χ v <;> cases χ w <;> decide
  rcases h with h | h | h
  · exact ⟨s(u, v), by simp, (noncrossingEdge_pair χ u v).mpr h⟩
  · exact ⟨s(u, w), by simp, (noncrossingEdge_pair χ u w).mpr h⟩
  · exact ⟨s(v, w), by simp, (noncrossingEdge_pair χ v w).mpr h⟩

/-- A noncrossing edge of an uncovered triangle cannot be old. -/
theorem residual_noncrossing_not_old {A W O T : Finset (Sym2 V)} {χ : V → Bool}
    (hT : T ∈ residual (trianglesOn A) (selectedOld W O χ))
    {e : Sym2 V} (he : e ∈ T) (hNC : noncrossingEdge χ e) : e ∉ O := by
  intro heO
  exact disjoint_left.mp (mem_residual.mp hT).2 he
    (mem_union_right _ (mem_filter.mpr ⟨heO, hNC⟩))

theorem residual_new_edges_nonempty {A W O T : Finset (Sym2 V)} {χ : V → Bool}
    (hT : T ∈ residual (trianglesOn A) (selectedOld W O χ)) :
    (T \ O).Nonempty := by
  have htri := (mem_trianglesOn.mp (mem_residual.mp hT).1).1
  obtain ⟨e, he, hNC⟩ := htri.exists_noncrossing χ
  exact ⟨e, mem_sdiff.mpr ⟨he, residual_noncrossing_not_old hT he hNC⟩⟩

/-- The selected old edges and the uncovered triangles' new edges cover every triangle. -/
theorem cutCover_covers (A W O : Finset (Sym2 V)) (χ : V → Bool) :
    IsCover (trianglesOn A) (cutCover A W O χ) := by
  apply cover_union_residual
  intro T hT
  obtain ⟨e, he⟩ := residual_new_edges_nonempty hT
  exact ⟨e, mem_inter.mpr ⟨(mem_sdiff.mp he).1,
    mem_cutAddedEdges.mpr ⟨T, hT, he⟩⟩⟩

theorem cutAddedEdges_subset {A W O : Finset (Sym2 V)} (χ : V → Bool) :
    cutAddedEdges A W O χ ⊆ A \ O := by
  intro e he
  obtain ⟨T, hT, heT⟩ := mem_cutAddedEdges.mp he
  obtain ⟨heT, heO⟩ := mem_sdiff.mp heT
  exact mem_sdiff.mpr
    ⟨(mem_trianglesOn.mp (mem_residual.mp hT).1).2 heT, heO⟩

/-- There is only one possible new edge in a triangle with at least two old
edges, so every added edge equals its noncrossing edge. -/
theorem cutAddedEdges_noncrossing {A W O : Finset (Sym2 V)}
    (hOld : ∀ T ∈ trianglesOn A, 2 ≤ (T ∩ O).card) (χ : V → Bool)
    {e : Sym2 V} (he : e ∈ cutAddedEdges A W O χ) : noncrossingEdge χ e := by
  obtain ⟨T, hT, heT⟩ := mem_cutAddedEdges.mp he
  have ht := (mem_residual.mp hT).1
  have htri := (mem_trianglesOn.mp ht).1
  obtain ⟨f, hf, hNC⟩ := htri.exists_noncrossing χ
  have hfnew : f ∈ T \ O :=
    mem_sdiff.mpr ⟨hf, residual_noncrossing_not_old hT hf hNC⟩
  have hcard : (T \ O).card ≤ 1 := by
    have hs := card_sdiff_add_card_inter T O
    have htcard := trianglesOn_card ht
    have ho := hOld T ht
    omega
  have hef : e = f := (card_le_one.mp hcard) e heT f hfnew
  exact hef ▸ hNC

theorem cutAddedEdges_inter_subset_noncrossing {A W O : Finset (Sym2 V)}
    (hOld : ∀ T ∈ trianglesOn A, 2 ≤ (T ∩ O).card)
    (N : Finset (Sym2 V)) (χ : V → Bool) :
    cutAddedEdges A W O χ ∩ N ⊆ N.filter (noncrossingEdge χ) := by
  intro e he
  obtain ⟨heAdd, heN⟩ := mem_inter.mp he
  exact mem_filter.mpr ⟨heN, cutAddedEdges_noncrossing hOld χ heAdd⟩

/-- Every actual nonloop edge is noncrossing in exactly half of all cuts. -/
theorem noncrossingEdge_average (e : Sym2 V) (he : ¬ e.IsDiag) :
    bitAverage (fun χ => if noncrossingEdge χ e then (1 : ℚ) else 0) = 1 / 2 := by
  revert he
  refine Sym2.inductionOn e ?_
  intro u v he
  have huv : u ≠ v := fun h => he (Sym2.mk_isDiag_iff.mpr h)
  calc
    bitAverage (fun χ => if noncrossingEdge χ s(u, v) then (1 : ℚ) else 0) =
        bitAverage (fun χ => if sameColor u v χ then (1 : ℚ) else 0) := by
      congr 1
      funext χ
      simp only [sameColor]
      congr 1
    _ = 1 / 2 := sameColor_average u v huv

/-- The expected number of noncrossing edges is half the number of edges. -/
theorem noncrossingEdges_average (E : Finset (Sym2 V))
    (hE : ∀ e ∈ E, ¬ e.IsDiag) :
    bitAverage (fun χ => ((E.filter (noncrossingEdge χ)).card : ℚ)) =
      (E.card : ℚ) / 2 := by
  calc
    bitAverage (fun χ => ((E.filter (noncrossingEdge χ)).card : ℚ)) =
        ∑ e ∈ E, bitAverage (fun χ => if noncrossingEdge χ e then (1 : ℚ) else 0) := by
      unfold bitAverage
      simp_rw [natCast_card_filter]
      exact finiteAverage_finset_sum E _
    _ = ∑ _e ∈ E, (1 / 2 : ℚ) := by
      apply sum_congr rfl
      intro e he
      exact noncrossingEdge_average e (hE e he)
    _ = (E.card : ℚ) / 2 := by simp [div_eq_mul_inv]

omit [Fintype V] in
theorem selectedOld_eq_union_sdiff (W O : Finset (Sym2 V)) (χ : V → Bool) :
    selectedOld W O χ = W ∪ (O \ W).filter (noncrossingEdge χ) := by
  ext e
  simp only [selectedOld, mem_union, mem_filter, mem_sdiff]
  tauto

omit [Fintype V] in
theorem selectedOld_card (W O : Finset (Sym2 V)) (χ : V → Bool) :
    (selectedOld W O χ).card = W.card + ((O \ W).filter (noncrossingEdge χ)).card := by
  rw [selectedOld_eq_union_sdiff, card_union_of_disjoint]
  apply disjoint_left.mpr
  intro e heW heF
  exact (mem_sdiff.mp (mem_filter.mp heF).1).2 heW

/-- The expected cost of the selected old edges. -/
theorem selectedOld_average {W O : Finset (Sym2 V)} (hW : W ⊆ O)
    (hO : ∀ e ∈ O, ¬ e.IsDiag) :
    bitAverage (fun χ => ((selectedOld W O χ).card : ℚ)) =
      (W.card : ℚ) + ((O.card : ℚ) - W.card) / 2 := by
  calc
    bitAverage (fun χ => ((selectedOld W O χ).card : ℚ)) =
        (W.card : ℚ) + bitAverage
          (fun χ => (((O \ W).filter (noncrossingEdge χ)).card : ℚ)) := by
      simp_rw [selectedOld_card, Nat.cast_add]
      exact (finiteAverage_add _ _).trans
        (by rw [finiteAverage_const]; rfl)
    _ = (W.card : ℚ) + ((O \ W).card : ℚ) / 2 := by
      rw [noncrossingEdges_average (O \ W)
        (fun e he => hO e (mem_sdiff.mp he).1)]
    _ = (W.card : ℚ) + ((O.card : ℚ) - W.card) / 2 := by
      rw [card_sdiff_of_subset hW, Nat.cast_sub (card_le_card hW)]

/-- The pointwise cover cost, separating added edges inside and outside `N`. -/
theorem cutCover_card_le {A W O : Finset (Sym2 V)}
    (hOld : ∀ T ∈ trianglesOn A, 2 ≤ (T ∩ O).card)
    (N : Finset (Sym2 V)) (χ : V → Bool) :
    (cutCover A W O χ).card ≤ W.card +
      ((O \ W).filter (noncrossingEdge χ)).card +
      (N.filter (noncrossingEdge χ)).card + (cutAddedEdges A W O χ \ N).card := by
  have hi := card_le_card (cutAddedEdges_inter_subset_noncrossing (W := W) hOld N χ)
  have hs := card_inter_add_card_sdiff (cutAddedEdges A W O χ) N
  have hu := card_union_le (selectedOld W O χ) (cutAddedEdges A W O χ)
  rw [selectedOld_card] at hu
  change (selectedOld W O χ ∪ cutAddedEdges A W O χ).card ≤ _
  omega

end Tuza

-- ==== Tuza.Probability.Books

/-! The expected cost of adding opposite edges to a random-cut cover. -/

namespace Tuza

open Finset
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {I : Type*} [Fintype I]

namespace Book

/-- Only a two-page book can contribute an opposite edge to a cut cover. -/
def cutEvent (b : Book V) (χ : V → Bool) : Prop :=
  match b with
  | .double u v x y _ => bookEvent u v x y χ
  | _ => False

instance (b : Book V) : DecidablePred b.cutEvent := by
  intro χ
  cases b <;> unfold cutEvent <;> infer_instance

theorem cutEvent_average (b : Book V) :
    bitAverage (fun χ => if b.cutEvent χ then (1 : ℚ) else 0) ≤ 3 / 8 := by
  cases b with
  | single u v x h => norm_num [cutEvent, bitAverage, finiteAverage_const]
  | double u v x y h =>
    apply le_of_eq
    apply bookEvent_average <;> simp_all [List.nodup_cons]
  | triple u v x y z h => norm_num [cutEvent, bitAverage, finiteAverage_const]

end Book

/-- Books whose opposite edge is an actual new edge outside the packing. -/
noncomputable def oppositeBooks (A O N : Finset (Sym2 V)) (books : I → Book V) : Finset I := by
  classical
  exact univ.filter (fun i => ∃ e, (books i).opposite = some e ∧ e ∈ A \ O ∧ e ∉ N)

omit [Fintype V] in
@[simp] theorem mem_oppositeBooks {A O N : Finset (Sym2 V)} {books : I → Book V} {i : I} :
    i ∈ oppositeBooks A O N books ↔
      ∃ e, (books i).opposite = some e ∧ e ∈ A \ O ∧ e ∉ N := by
  classical
  simp [oppositeBooks]

/-- Every added edge outside N comes from a two-page book whose local
cut event occurs. The witness is derived from the actual uncovered triangle. -/
theorem cutAddedEdges_book_witness {A W O N : Finset (Sym2 V)} (books : I → Book V)
    (hOld : ∀ T ∈ trianglesOn A, 2 ≤ (T ∩ O).card)
    (hNO : Disjoint N O)
    (hspine : ∀ i, (books i).spine ∈ N)
    (hblue : ∀ i U, U ∈ (books i).pages → U \ {(books i).spine} ⊆ O)
    (hsingle : ∀ i, (books i).pages.card = 1 →
      ∀ U ∈ (books i).pages, U ∩ O ⊆ W)
    (hchoice : Books.EveryChoiceMeets (typeFamily A O 2) (fun i => (books i).pages))
    (χ : V → Bool) {e : Sym2 V} (he : e ∈ cutAddedEdges A W O χ \ N) :
    ∃ i ∈ oppositeBooks A O N books, (books i).opposite = some e ∧ (books i).cutEvent χ := by
  obtain ⟨heAdd, heN⟩ := mem_sdiff.mp he
  obtain ⟨T, hT, heNew⟩ := mem_cutAddedEdges.mp heAdd
  have hactual := (mem_residual.mp hT).1
  have htri := (mem_trianglesOn.mp hactual).1
  have htype := new_edge_forces_typeTwo hactual (hOld T hactual) heNew
  have hnewCard : (T \ O).card ≤ 1 := by
    have hc := trianglesOn_card hactual
    have ho := hOld T hactual
    have hp := card_sdiff_add_card_inter T O
    omega
  have hdisN : Disjoint T N := by
    apply disjoint_left.mpr
    intro f hfT hfN
    have hfO : f ∉ O := fun hf => disjoint_left.mp hNO hfN hf
    have hfe := card_le_one.mp hnewCard f (mem_sdiff.mpr ⟨hfT, hfO⟩) e heNew
    exact heN (hfe ▸ hfN)
  obtain ⟨i, hi⟩ := Books.exists_book_all_pages_meet hchoice htype
  have hnotspine : (books i).spine ∉ T :=
    fun hm => disjoint_left.mp hdisN hm (hspine i)
  have hmeet : ∀ U ∈ (books i).pages, (T ∩ U).Nonempty := by
    intro U hU
    obtain ⟨f, hfT, hfU⟩ := not_disjoint_iff.mp (hi U hU)
    exact ⟨f, mem_inter.mpr ⟨hfT, hfU⟩⟩
  have hmemberOld : ∀ f ∈ T, ∀ U ∈ (books i).pages, f ∈ U → f ∈ O := by
    intro f hfT U hU hfU
    apply hblue i U hU
    exact mem_sdiff.mpr ⟨hfU, fun hf => hnotspine (mem_singleton.mp hf ▸ hfT)⟩
  have heNC := cutAddedEdges_noncrossing hOld χ heAdd
  have heA : e ∈ A \ O := cutAddedEdges_subset χ heAdd
  generalize hb : books i = b at hnotspine hmeet hmemberOld
  cases b with
  | single u v x hv =>
    obtain ⟨f, hf⟩ := hmeet (triangleEdges u v x) (by simp [Book.pages])
    obtain ⟨hfT, hfU⟩ := mem_inter.mp hf
    have hfOld := hmemberOld f hfT (triangleEdges u v x) (by simp [Book.pages]) hfU
    have hfW := hsingle i (by simp [hb, Book.pages]) (triangleEdges u v x)
      (by simp [hb, Book.pages]) (mem_inter.mpr ⟨hfU, hfOld⟩)
    exact False.elim (disjoint_left.mp (mem_residual.mp hT).2 hfT (mem_union_left _ hfW))
  | triple u v x y z hv =>
    have hs := three_page_spine htri hv
      (hmeet (triangleEdges u v x) (by simp [Book.pages]))
      (hmeet (triangleEdges u v y) (by simp [Book.pages]))
      (hmeet (triangleEdges u v z) (by simp [Book.pages]))
    exact False.elim (hnotspine hs)
  | double u v x y hv =>
    have hn : u ≠ v ∧ u ≠ x ∧ u ≠ y ∧ v ≠ x ∧ v ≠ y ∧ x ≠ y := by
      simpa [List.nodup_cons, and_assoc] using hv
    obtain ⟨huv, hux, huy, hvx, hvy, hxy⟩ := hn
    have hshape := two_page_triangle htri hv hnotspine
      (hmeet (triangleEdges u v x) (by simp [Book.pages]))
      (hmeet (triangleEdges u v y) (by simp [Book.pages]))
    have huxOld : s(u, x) ∈ O := hblue i (triangleEdges u v x)
      (by simp [hb, Book.pages]) (by simp [hb, Book.spine, hvx.symm, huv])
    have hvxOld : s(v, x) ∈ O := hblue i (triangleEdges u v x)
      (by simp [hb, Book.pages]) (by simp [hb, Book.spine, hux.symm, huv.symm])
    have huyOld : s(u, y) ∈ O := hblue i (triangleEdges u v y)
      (by simp [hb, Book.pages]) (by simp [hb, Book.spine, hvy.symm, huv])
    have hvyOld : s(v, y) ∈ O := hblue i (triangleEdges u v y)
      (by simp [hb, Book.pages]) (by simp [hb, Book.spine, huy.symm, huv.symm])
    have hexy : e = s(x, y) := by
      obtain ⟨heT, heO⟩ := mem_sdiff.mp heNew
      rcases hshape with hshape | hshape <;> rw [hshape] at heT <;>
        simp only [mem_triangleEdges] at heT
      · rcases heT with rfl | rfl | heT
        · exact False.elim (heO huxOld)
        · exact False.elim (heO huyOld)
        · exact heT
      · rcases heT with rfl | rfl | heT
        · exact False.elim (heO hvxOld)
        · exact False.elim (heO hvyOld)
        · exact heT
    have hop : (books i).opposite = some e := by simp [hb, hexy]
    refine ⟨i, mem_oppositeBooks.mpr ⟨e, hop, heA, heN⟩, hop, ?_⟩
    rw [hb]
    change χ x = χ y ∧ (χ u ≠ χ x ∨ χ v ≠ χ x)
    refine ⟨(noncrossingEdge_pair χ x y).mp (hexy ▸ heNC), ?_⟩
    rcases hshape with hshape | hshape
    · left
      intro hh
      exact residual_noncrossing_not_old hT
        (by simp [hshape] : s(u, x) ∈ T)
        ((noncrossingEdge_pair χ u x).mpr hh) huxOld
    · right
      intro hh
      exact residual_noncrossing_not_old hT
        (by simp [hshape] : s(v, x) ∈ T)
        ((noncrossingEdge_pair χ v x).mpr hh) hvxOld

omit [Fintype V] [Fintype I] in
/-- Each book contributes at most one opposite edge, so the union has at most
as many edges as there are books whose cut events occur. -/
theorem card_le_book_events (books : I → Book V) (J : Finset I)
    (D : Finset (Sym2 V)) (χ : V → Bool)
    (hw : ∀ e ∈ D, ∃ i ∈ J, (books i).opposite = some e ∧ (books i).cutEvent χ) :
    D.card ≤ (J.filter (fun i => (books i).cutEvent χ)).card := by
  classical
  let K := J.filter (fun i => (books i).cutEvent χ)
  have hsub : D ⊆ K.biUnion (fun i => (books i).opposite.toFinset) := by
    intro e he
    obtain ⟨i, hi, hop, hev⟩ := hw e he
    apply mem_biUnion.mpr
    exact ⟨i, mem_filter.mpr ⟨hi, hev⟩, by simp [hop]⟩
  calc
    D.card ≤ (K.biUnion (fun i => (books i).opposite.toFinset)).card := card_le_card hsub
    _ ≤ ∑ i ∈ K, (books i).opposite.toFinset.card := card_biUnion_le
    _ ≤ ∑ _i ∈ K, 1 := by
      apply sum_le_sum
      intro i _
      cases (books i).opposite <;> simp
    _ = K.card := by simp

omit [Fintype I] in
theorem book_events_average_le (books : I → Book V) (J : Finset I) :
    bitAverage (fun χ => ((J.filter (fun i => (books i).cutEvent χ)).card : ℚ))
      ≤ 3 * (J.card : ℚ) / 8 := by
  classical
  calc
    bitAverage (fun χ => ((J.filter (fun i => (books i).cutEvent χ)).card : ℚ)) =
        ∑ i ∈ J, bitAverage (fun χ => if (books i).cutEvent χ then (1 : ℚ) else 0) := by
      unfold bitAverage
      simp_rw [natCast_card_filter]
      exact finiteAverage_finset_sum J _
    _ ≤ ∑ _i ∈ J, (3 / 8 : ℚ) :=
      sum_le_sum (fun i _ => (books i).cutEvent_average)
    _ = 3 * (J.card : ℚ) / 8 := by simp; ring

/-- The random-cover bound obtained by averaging, with denominators cleared. -/
theorem random_book_cover {A W O N : Finset (Sym2 V)} (books : I → Book V)
    (hOld : ∀ T ∈ trianglesOn A, 2 ≤ (T ∩ O).card)
    (hNO : Disjoint N O) (hW : W ⊆ O)
    (hOdiag : ∀ e ∈ O, ¬ e.IsDiag) (hNdiag : ∀ e ∈ N, ¬ e.IsDiag)
    (hspine : ∀ i, (books i).spine ∈ N)
    (hblue : ∀ i U, U ∈ (books i).pages → U \ {(books i).spine} ⊆ O)
    (hsingle : ∀ i, (books i).pages.card = 1 →
      ∀ U ∈ (books i).pages, U ∩ O ⊆ W)
    (hchoice : Books.EveryChoiceMeets (typeFamily A O 2) (fun i => (books i).pages)) :
    8 * transversalNumber (trianglesOn A) ≤
      4 * O.card + 4 * W.card + 4 * N.card + 3 * (oppositeBooks A O N books).card := by
  classical
  let J := oppositeBooks A O N books
  have hout (χ : V → Bool) : (cutAddedEdges A W O χ \ N).card ≤
      (J.filter (fun i => (books i).cutEvent χ)).card :=
    card_le_book_events books J _ χ (fun _ he =>
      cutAddedEdges_book_witness books hOld hNO hspine hblue hsingle hchoice χ he)
  have hpoint (χ : V → Bool) : ((cutCover A W O χ).card : ℚ) ≤
      ((selectedOld W O χ).card : ℚ) + ((N.filter (noncrossingEdge χ)).card : ℚ) +
        ((J.filter (fun i => (books i).cutEvent χ)).card : ℚ) := by
    have hc := cutCover_card_le (W := W) hOld N χ
    rw [← selectedOld_card] at hc
    exact_mod_cast hc.trans (Nat.add_le_add_left (hout χ) _)
  have havg := finiteAverage_mono _ _ hpoint
  rw [finiteAverage_add, finiteAverage_add] at havg
  change bitAverage _ ≤ bitAverage _ + bitAverage _ + bitAverage _ at havg
  rw [selectedOld_average hW hOdiag, noncrossingEdges_average N hNdiag] at havg
  have hevent := book_events_average_le books J
  obtain ⟨χ, hχ⟩ := exists_le_finiteAverage
    (fun χ : V → Bool => ((cutCover A W O χ).card : ℚ))
  have hcover : (transversalNumber (trianglesOn A) : ℚ) ≤ (cutCover A W O χ).card := by
    exact_mod_cast (cutCover_covers A W O χ).number_le
  have hfinal : (8 : ℚ) * transversalNumber (trianglesOn A) ≤
      4 * O.card + 4 * W.card + 4 * N.card + 3 * J.card := by
    change _ ≤ bitAverage _ at hχ
    linarith
  exact_mod_cast hfinal

end Tuza

-- ==== Tuza.Construction.OppositeEdges

/-! Opposite edges outside the packing's new edges give private red pages. -/

namespace Tuza
namespace OppositeEdges

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {edges : Finset (Sym2 V)} (c : Construction edges)

/-- The full type-2 family supplies the ambient graph needed for the exchange. -/
theorem pair_unique_in_special {u v x y : V}
    (hparent : triangleEdges u v x ∈ c.typeTwo)
    (hpage : triangleEdges u v y ∈ c.specialFamily)
    (hspine : s(u, v) ∈ c.newEdges)
    (hopposite : s(x, y) ∈ c.remainingEdges \ c.old)
    (houtside : s(x, y) ∉ c.newEdges) :
    ∀ T ∈ c.specialFamily, s(u, v) ∈ T → T = triangleEdges u v y := by
  have hmax : IsMaximumPacking
      (oneRedTriangles c.remainingEdges (c.remainingEdges \ c.old)) c.typeTwo := by
    rw [← typeTwo_eq_oneRed]
    exact c.typeTwo_maximum
  have hres : triangleEdges u v y ∈
      residual (oneRedTriangles c.remainingEdges (c.remainingEdges \ c.old))
        (blueEdges (c.remainingEdges \ c.old) c.typeTwo) := by
    rw [← typeTwo_eq_oneRed]
    exact c.specialFamily_subset_typeTwo_residual hpage
  have hred : s(u, v) ∈ c.remainingEdges \ c.old :=
    mem_sdiff.mpr ⟨c.newEdges_subset_remaining hspine, (mem_sdiff.mp hspine).2⟩
  have hnot : s(x, y) ∉ redEdges (c.remainingEdges \ c.old) c.typeTwo := by
    rwa [← c.newEdges_eq_red_typeTwo]
  have hu := unique_residual_triangle hmax hparent hres hred
    (mem_sdiff.mp hopposite).1 hopposite hnot
  intro T hT he
  apply hu T ?_ he
  rw [← typeTwo_eq_oneRed]
  exact c.specialFamily_subset_typeTwo_residual hT

theorem pair_mem_privateRed {Q : Finset (Finset (Sym2 V))}
    (hQ : IsPacking c.specialFamily Q) {u v x y : V}
    (hparent : triangleEdges u v x ∈ c.typeTwo)
    (hpage : triangleEdges u v y ∈ Q)
    (hspine : s(u, v) ∈ c.newEdges)
    (hopposite : s(x, y) ∈ c.remainingEdges \ c.old)
    (houtside : s(x, y) ∉ c.newEdges) :
    triangleEdges u v y ∈ privateRedPages c.specialFamily c.newEdges Q := by
  refine mem_privateRedPages.mpr ⟨hpage, ?_⟩
  intro T hT heq
  apply pair_unique_in_special c hparent (hQ.1 hpage) hspine hopposite houtside T hT
  have he : s(u, v) ∈ triangleEdges u v y ∩ c.newEdges :=
    mem_inter.mpr ⟨by simp, hspine⟩
  exact (mem_inter.mp (heq.symm ▸ he)).1

theorem special_member_not_typeTwo {Q : Finset (Finset (Sym2 V))}
    (hQ : IsPacking c.specialFamily Q) {q : Finset (Sym2 V)} (hq : q ∈ Q) :
    q ∉ c.typeTwo := by
  exact Layered.residual_member_not_parent (typeTwo_colored c.remainingEdges c.old)
    (hQ.mono_family c.specialFamily_subset_typeTwo_residual) hq

theorem book_child_private {Q : Finset (Finset (Sym2 V))}
    (hQ : IsPacking c.specialFamily Q) (b : Book V) {p q : Finset (Sym2 V)}
    (hp : p ∈ c.typeTwo) (hpb : p ∈ b.pages) (hq : q ∈ Q) (hqb : q ∈ b.pages)
    (hspine : b.spine ∈ c.newEdges) {e : Sym2 V} (hop : b.opposite = some e)
    (he : e ∈ c.remainingEdges \ c.old) (heout : e ∉ c.newEdges) :
    q ∈ privateRedPages c.specialFamily c.newEdges Q := by
  have hne : q ≠ p := by
    intro heq
    exact special_member_not_typeTwo c hQ hq (heq ▸ hp)
  cases b with
  | single u v x hv => simp [Book.opposite] at hop
  | triple u v x y z hv => simp [Book.opposite] at hop
  | double u v x y hv =>
    have heq : s(x, y) = e := Option.some.inj hop
    subst e
    change s(u, v) ∈ c.newEdges at hspine
    simp only [Book.pages, mem_insert, mem_singleton] at hpb hqb
    rcases hpb with rfl | rfl
    · rcases hqb with hsame | rfl
      · exact (hne hsame).elim
      · exact pair_mem_privateRed c hQ hp hq hspine he heout
    · rcases hqb with rfl | hsame
      · exact pair_mem_privateRed c hQ hp hq hspine
          (Sym2.eq_swap ▸ he) (Sym2.eq_swap ▸ heout)
      · exact (hne hsame).elim

/-- Disjoint book supports give distinct private pages. -/
theorem count_books_le_privateRed {I : Type*} [Fintype I] [DecidableEq I]
    {Q : Finset (Finset (Sym2 V))} (hQ : IsPacking c.specialFamily Q)
    (books : I → Book V) (B : Finset I)
    (hparent : ∀ i, ∃ p ∈ c.typeTwo, p ∈ (books i).pages)
    (hspine : ∀ i, (books i).spine ∈ c.newEdges)
    (hbad : ∀ i ∈ B, ∃ e, (books i).opposite = some e ∧
      e ∈ c.remainingEdges \ c.old ∧ e ∉ c.newEdges)
    (hchild : ∀ i ∈ B, ∃ q ∈ Q, q ∈ (books i).pages)
    (hdis : Books.DisjointSupports (fun i => (books i).pages)) :
    B.card ≤ (privateRedPages c.specialFamily c.newEdges Q).card := by
  classical
  have hs : ∀ i : {j // j ∈ B}, ∃ q,
      q ∈ privateRedPages c.specialFamily c.newEdges Q ∧ q ∈ (books i.val).pages := by
    intro i
    obtain ⟨p, hp, hpb⟩ := hparent i.val
    obtain ⟨q, hq, hqb⟩ := hchild i.val i.property
    obtain ⟨e, hop, he, heout⟩ := hbad i.val i.property
    exact ⟨q, book_child_private c hQ (books i.val) hp hpb hq hqb
      (hspine i.val) hop he heout, hqb⟩
  choose f hfprivate hfpage using hs
  have hinj : Function.Injective f := by
    intro i j heq
    by_contra hne
    have hij : i.val ≠ j.val := fun h => hne (Subtype.ext h)
    have hfiQ := (mem_privateRedPages.mp (hfprivate i)).1
    obtain ⟨e, he⟩ := c.specialFamily_colored.member_nonempty (hQ.1 hfiQ)
    exact disjoint_left.mp (hdis hij)
      (mem_support.mpr ⟨f i, hfpage i, he⟩)
      (mem_support.mpr ⟨f j, hfpage j, heq ▸ he⟩)
  have hsub : univ.image f ⊆ privateRedPages c.specialFamily c.newEdges Q := by
    intro q hq
    obtain ⟨i, _, rfl⟩ := mem_image.mp hq
    exact hfprivate i
  have hcard := card_le_card hsub
  rw [card_image_of_injective _ hinj] at hcard
  simpa using hcard

theorem random_books_card_le_privateRed {I : Type*} [Fintype I] [DecidableEq I]
    {Q : Finset (Finset (Sym2 V))} (hQ : IsPacking c.specialFamily Q)
    (books : I → Book V)
    (hparent : ∀ i, ∃ p ∈ c.typeTwo, p ∈ (books i).pages)
    (hspine : ∀ i, (books i).spine ∈ c.newEdges)
    (hchild : ∀ i ∈ oppositeBooks c.remainingEdges c.oldRemaining c.newEdges books,
      ∃ q ∈ Q, q ∈ (books i).pages)
    (hdis : Books.DisjointSupports (fun i => (books i).pages)) :
    (oppositeBooks c.remainingEdges c.oldRemaining c.newEdges books).card ≤
      (privateRedPages c.specialFamily c.newEdges Q).card := by
  apply count_books_le_privateRed c hQ books
    (oppositeBooks c.remainingEdges c.oldRemaining c.newEdges books) hparent hspine ?_ hchild hdis
  intro i hi
  obtain ⟨e, hop, he, heout⟩ := mem_oppositeBooks.mp hi
  exact ⟨e, hop, c.remaining_sdiff_oldRemaining ▸ he, heout⟩

end OppositeEdges
end Tuza

-- ==== Tuza.Construction.RandomCover

/-! The two-layer random cover: equation (4). -/

namespace Tuza
namespace TwoLayer

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {edges : Finset (Sym2 V)} (c : Construction edges)
variable {Q : Finset (Finset (Sym2 V))} (hQ : IsPacking c.specialFamily Q)

include hQ in
private theorem residual_packing :
    IsPacking (residual (typeFamily c.remainingEdges c.old 2)
      (blueEdges (c.remainingEdges \ c.old) c.typeTwo)) Q :=
  hQ.mono_family c.specialFamily_subset_typeTwo_residual

/-- The cut uses only the type-two packing and its second pages. -/
noncomputable def pages (Q : Finset (Finset (Sym2 V))) (p : {T // T ∈ c.typeTwo}) :=
  Layered.twoLayerPages (c.remainingEdges \ c.old) c.typeTwo Q p

include hQ in
theorem pages_subset (p : {T // T ∈ c.typeTwo}) :
    pages c Q p ⊆ typeFamily c.remainingEdges c.old 2 :=
  Layered.pages_subset_family c.typeTwo_maximum (residual_packing c hQ) p

include hQ in
theorem pages_card_le_two (p : {T // T ∈ c.typeTwo}) :
    (pages c Q p).card ≤ 2 := by
  have hc := Layered.children_card_le_one (typeTwo_colored c.remainingEdges c.old)
    (residual_packing c hQ) p.val
  have hi := card_insert_le p.val (Layered.children (c.remainingEdges \ c.old) Q p.val)
  change (insert p.val (Layered.children (c.remainingEdges \ c.old) Q p.val)).card ≤ 2
  omega

theorem pages_common_spine (p : {T // T ∈ c.typeTwo}) :
    ∀ T ∈ pages c Q p, Construction.typeTwoSpine p ∈ T := by
  intro T hT
  have hs := Construction.typeTwoSpine_mem p
  rcases Layered.mem_twoLayerPages.mp hT with rfl | ⟨_, hred⟩
  · exact (mem_inter.mp hs).1
  · have hsR : Construction.typeTwoSpine p ∈ p.val ∩ (c.remainingEdges \ c.old) :=
      mem_inter.mpr ⟨(mem_inter.mp hs).1,
        mem_sdiff.mpr ⟨c.newEdges_subset_remaining (mem_inter.mp hs).2,
          (mem_sdiff.mp (mem_inter.mp hs).2).2⟩⟩
    exact (mem_inter.mp (hred.symm ▸ hsR)).1

include hQ in
private theorem exists_book (p : {T // T ∈ c.typeTwo}) :
    ∃ b : Book V, b.pages = pages c Q p ∧ b.spine = Construction.typeTwoSpine p :=
  Book.exists_representation (pages c Q p) (Construction.typeTwoSpine p)
    (Layered.pages_nonempty _ _ _ p) ((pages_card_le_two c hQ p).trans (by decide))
    (fun _ hT => (mem_trianglesOn.mp
      (typeFamily_subset _ _ _ (pages_subset c hQ p hT))).1)
    (pages_common_spine c p)

noncomputable def book (p : {T // T ∈ c.typeTwo}) : Book V :=
  Classical.choose (exists_book c hQ p)

theorem book_pages (p : {T // T ∈ c.typeTwo}) :
    (book c hQ p).pages = pages c Q p :=
  (Classical.choose_spec (exists_book c hQ p)).1

theorem book_spine (p : {T // T ∈ c.typeTwo}) :
    (book c hQ p).spine = Construction.typeTwoSpine p :=
  (Classical.choose_spec (exists_book c hQ p)).2

theorem book_spine_mem (p : {T // T ∈ c.typeTwo}) :
    (book c hQ p).spine ∈ c.newEdges := by
  rw [book_spine]
  exact (mem_inter.mp (Construction.typeTwoSpine_mem p)).2

theorem book_parent_mem (p : {T // T ∈ c.typeTwo}) : p.val ∈ (book c hQ p).pages := by
  rw [book_pages]
  exact Layered.mem_twoLayerPages.mpr (Or.inl rfl)

theorem books_disjoint : Books.DisjointSupports (fun p => (book c hQ p).pages) := by
  simpa only [book_pages, pages] using
    Layered.supports_disjoint (typeTwo_colored c.remainingEdges c.old)
      c.typeTwo_maximum (residual_packing c hQ)

theorem books_everyChoiceMeets :
    Books.EveryChoiceMeets (typeFamily c.remainingEdges c.old 2)
      (fun p => (book c hQ p).pages) := by
  simp only [book_pages, pages]
  exact Books.everyChoiceMeets_of_maximum
    (fun _ hT => trianglesOn_nonempty (typeFamily_subset _ _ _ hT))
    (fun _ hf => Layered.choices_maximum (typeTwo_colored c.remainingEdges c.old)
      c.typeTwo_maximum (residual_packing c hQ) hf)

theorem book_blue_old (p : {T // T ∈ c.typeTwo})
    {U : Finset (Sym2 V)} (hU : U ∈ (book c hQ p).pages) :
    U \ {(book c hQ p).spine} ⊆ c.oldRemaining := by
  rw [book_pages] at hU
  have hactual := typeFamily_subset _ _ _ (pages_subset c hQ p hU)
  have hs := pages_common_spine c p U hU
  have hsN := (mem_inter.mp (Construction.typeTwoSpine_mem p)).2
  intro e he
  obtain ⟨heU, heSpine⟩ := mem_sdiff.mp he
  have heRemain := (mem_trianglesOn.mp hactual).2 heU
  have heOld : e ∈ c.old := by
    by_contra hn
    have heq := card_le_one.mp (c.remaining_new_le_one hactual)
      e (mem_sdiff.mpr ⟨heU, hn⟩) (Construction.typeTwoSpine p)
      (mem_sdiff.mpr ⟨hs, (mem_sdiff.mp hsN).2⟩)
    exact heSpine (mem_singleton.mpr (heq.trans (book_spine c hQ p).symm))
  exact mem_sdiff.mpr ⟨heOld, (mem_sdiff.mp heRemain).2⟩

/-- The old edges in the one-page books form the fixed part of the cover. -/
noncomputable def fixedOld (Q : Finset (Finset (Sym2 V))) : Finset (Sym2 V) :=
  blueEdges (c.remainingEdges \ c.old)
    (c.typeTwo \ Layered.pairedParents (c.remainingEdges \ c.old) c.typeTwo Q)

include hQ in
theorem fixedOld_card : (fixedOld c Q).card + 2 * Q.card = 2 * c.typeTwo.card := by
  classical
  let R := c.remainingEdges \ c.old
  let P := Layered.pairedParents R c.typeTwo Q
  have hpaired : P.card = Q.card :=
    Layered.pairedParents_card (typeTwo_colored c.remainingEdges c.old)
      c.typeTwo_maximum (residual_packing c hQ)
  have hsub : P ⊆ c.typeTwo := Layered.pairedParents_subset R c.typeTwo Q
  have hblue : (fixedOld c Q).card = 2 * (c.typeTwo \ P).card :=
    (c.typeTwo_maximum.1.subfamily sdiff_subset).card_blueEdges
      (typeTwo_colored c.remainingEdges c.old)
  have hsplit := card_sdiff_add_card_eq_card hsub
  omega

theorem fixedOld_subset : fixedOld c Q ⊆ c.oldRemaining := by
  intro e he
  obtain ⟨heP, heR⟩ := mem_blueEdges.mp he
  obtain ⟨p, hp, hep⟩ := mem_support.mp heP
  have hpB := (mem_sdiff.mp hp).1
  have heRemain := c.rest_support_subset
    (mem_support.mpr ⟨p, c.typeTwo_subset_rest hpB, hep⟩)
  have heOld : e ∈ c.old := by
    by_contra hn
    exact heR (mem_sdiff.mpr ⟨heRemain, hn⟩)
  exact mem_sdiff.mpr ⟨heOld, (mem_sdiff.mp heRemain).2⟩

theorem book_single_fixedOld (p : {T // T ∈ c.typeTwo})
    (hc : (book c hQ p).pages.card = 1) :
    ∀ U ∈ (book c hQ p).pages, U ∩ c.oldRemaining ⊆ fixedOld c Q := by
  have hnot : p.val ∉ Layered.pairedParents
      (c.remainingEdges \ c.old) c.typeTwo Q := by
    intro hp
    have htwo := Layered.pages_card_paired (typeTwo_colored c.remainingEdges c.old)
      (residual_packing c hQ) p hp
    rw [book_pages] at hc
    change (pages c Q p).card = 2 at htwo
    omega
  intro U hU e he
  have hUp := card_le_one.mp (show (book c hQ p).pages.card ≤ 1 by omega)
    U hU p.val (book_parent_mem c hQ p)
  obtain ⟨heU, heOld⟩ := mem_inter.mp he
  apply mem_blueEdges.mpr
  refine ⟨mem_support.mpr ⟨p.val, mem_sdiff.mpr ⟨p.property, hnot⟩, hUp ▸ heU⟩, ?_⟩
  intro heR
  exact (mem_sdiff.mp heR).2 (mem_sdiff.mp heOld).1

theorem book_child_of_opposite (p : {T // T ∈ c.typeTwo}) {e : Sym2 V}
    (hop : (book c hQ p).opposite = some e) :
    ∃ q ∈ Q, q ∈ (book c hQ p).pages := by
  have hpaired : p.val ∈ Layered.pairedParents
      (c.remainingEdges \ c.old) c.typeTwo Q := by
    by_contra hn
    have hone := Layered.pages_card_unpaired p hn
    have htwo := Book.pages_card_of_opposite hop
    rw [book_pages] at htwo
    change (pages c Q p).card = 1 at hone
    omega
  obtain ⟨_, q, hq, hred⟩ := Layered.mem_pairedParents.mp hpaired
  refine ⟨q, hq, ?_⟩
  rw [book_pages]
  exact Layered.mem_twoLayerPages.mpr (Or.inr ⟨hq, hred.symm⟩)

theorem oppositeBooks_card_le_privateRed :
    (oppositeBooks c.remainingEdges c.oldRemaining c.newEdges (book c hQ)).card ≤
      (privateRedPages c.specialFamily c.newEdges Q).card := by
  apply OppositeEdges.random_books_card_le_privateRed c hQ (book c hQ)
    (fun p => ⟨p.val, p.property, book_parent_mem c hQ p⟩)
    (book_spine_mem c hQ) ?_ (books_disjoint c hQ)
  intro p hp
  obtain ⟨e, hop, _, _⟩ := mem_oppositeBooks.mp hp
  exact book_child_of_opposite c hQ p hop

include hQ in
/-- The random-cover estimate for G' using the second-page packing Q. -/
theorem remaining_random_cover :
    8 * transversalNumber (trianglesOn c.remainingEdges) + 8 * Q.card
      ≤ 4 * c.oldRemaining.card + 12 * c.typeTwo.card
        + 3 * (privateRedPages c.specialFamily c.newEdges Q).card := by
  have hNO : Disjoint c.newEdges c.oldRemaining :=
    c.newEdges_disjoint_old.mono_right sdiff_subset
  have hchoice : Books.EveryChoiceMeets
      (typeFamily c.remainingEdges c.oldRemaining 2) (fun p => (book c hQ p).pages) := by
    rw [c.typeFamily_oldRemaining]
    exact books_everyChoiceMeets c hQ
  have hcut := random_book_cover (book c hQ)
    (fun _ hT => c.remaining_oldRemaining_ge_two hT) hNO (fixedOld_subset c)
    (fun _ he => c.old_not_diag (mem_sdiff.mp he).1)
    (fun _ he => c.newEdges_not_diag he) (book_spine_mem c hQ)
    (fun p _ hU => book_blue_old c hQ p hU) (book_single_fixedOld c hQ) hchoice
  have hW := fixedOld_card c hQ
  have hN := c.card_newEdges
  have hprivate := oppositeBooks_card_le_privateRed c hQ
  omega

include hQ in
/-- Restoring the first packing gives the random-cover inequality in G. -/
theorem random_cover :
    8 * transversalNumber (trianglesOn edges) + 8 * Q.card
      ≤ 12 * c.initial.card + 20 * c.first.card + 12 * c.typeTwo.card
        + 3 * (privateRedPages c.specialFamily c.newEdges Q).card := by
  have hdelete := transversalNumber_le_add_residual
    (trianglesOn edges) (support c.first) (fun _ hT => trianglesOn_nonempty hT)
  rw [← trianglesOn_sdiff] at hdelete
  have hfirst : (support c.first).card = 3 * c.first.card :=
    c.first_packing.card_support_uniform (fun _ hT => trianglesOn_card (c.first_packing.1 hT))
  have hremaining := remaining_random_cover c hQ
  have hOld := c.oldRemaining_card
  change transversalNumber (trianglesOn edges) ≤
    (support c.first).card + transversalNumber (trianglesOn c.remainingEdges) at hdelete
  omega

end TwoLayer
end Tuza

-- ==== Tuza.Main

/-! Four covers of the same graph give the bound 165/59. -/

namespace Tuza

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace Construction

variable {edges : Finset (Sym2 V)} (c : Construction edges)

theorem first_cover :
    transversalNumber (trianglesOn edges) + c.first.card ≤ 3 * c.initial.card :=
  FirstCover.transversalNumber_add_typeOne_packing_le c.initial_maximum c.first_maximum.1

/-- The four estimates for the same choices of P, A, P', Q and Q1, using
the paper's count h of private red pages. -/
theorem four_covers (r : RefinedConstruction c) :
    (transversalNumber (trianglesOn edges) + c.first.card ≤ 3 * c.initial.card) ∧
    (8 * transversalNumber (trianglesOn edges) + 8 * r.second.card ≤
      12 * c.initial.card + 20 * c.first.card + 12 * c.typeTwo.card +
        3 * (privateRedPages c.specialFamily c.newEdges r.second).card) ∧
    (transversalNumber (trianglesOn edges) + r.second.card + r.third.card ≤
      3 * c.initial.card) ∧
    (4 * transversalNumber (trianglesOn edges) + 4 * c.typeTwo.card +
      (privateRedPages c.specialFamily c.newEdges r.second).card ≤
      12 * c.initial.card + 9 * r.second.card + 6 * r.third.card) :=
  ⟨c.first_cover, TwoLayer.random_cover c r.second_maximum.1, c.full_book_cover r,
    c.fourth_cover r.second_maximum r.third_maximum⟩

theorem bound_with_residual (r : RefinedConstruction c) :
    59 * transversalNumber (trianglesOn edges) + r.third.card ≤ 165 * c.initial.card := by
  obtain ⟨hfirst, hcut, hbooks, hcolored⟩ := c.four_covers r
  exact four_bounds_arithmetic hfirst hcut hbooks hcolored

end Construction

/-- The 165/59 bound for the triangle family of any finite edge set. -/
theorem triangles_bound (edges : Finset (Sym2 V)) :
    59 * transversalNumber (trianglesOn edges) ≤ 165 * packingNumber (trianglesOn edges) := by
  obtain ⟨c⟩ := exists_construction edges
  obtain ⟨r⟩ := exists_refinedConstruction c
  have h := c.bound_with_residual r
  rw [c.initial_maximum.card_eq] at h
  omega

/-- The main theorem for a finite simple graph, with denominators cleared. -/
theorem tuza_bound_nat (G : SimpleGraph V) : 59 * tau G ≤ 165 * nu G :=
  triangles_bound (graphEdges G)

end Tuza

namespace TuzaBridge
open Tuza Finset TuzaConjecture
open scoped Classical

variable {V : Type} [Fintype V]

noncomputable def verts (T : Finset (Sym2 V)) : Finset V :=
  Finset.univ.filter (fun x => ∃ e ∈ T, x ∈ e)

theorem mem_verts_tri {u v w x : V} :
    x ∈ verts (triangleEdges u v w) ↔ x = u ∨ x = v ∨ x = w := by
  simp only [verts, Finset.mem_filter, Finset.mem_univ, true_and, mem_triangleEdges]
  constructor
  · rintro ⟨e, he | he | he, hx⟩ <;> subst he <;> simp [Sym2.mem_iff] at hx <;> tauto
  · rintro (h | h | h)
    · exact ⟨s(u, v), Or.inl rfl, by simp [h]⟩
    · exact ⟨s(u, v), Or.inl rfl, by simp [h]⟩
    · exact ⟨s(u, w), Or.inr (Or.inl rfl), by simp [h]⟩

theorem pair_mem_tri {u v w x y : V} (hxy : x ≠ y)
    (hx : x ∈ verts (triangleEdges u v w)) (hy : y ∈ verts (triangleEdges u v w)) :
    s(x, y) ∈ triangleEdges u v w := by
  rw [mem_verts_tri] at hx hy
  simp only [mem_triangleEdges, Sym2.eq_iff]
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;> simp_all

theorem edges_eq_of_verts_eq {u v w u' v' w' : V}
    (h1 : u ≠ v) (h2 : u ≠ w) (h3 : v ≠ w) (h1' : u' ≠ v') (h2' : u' ≠ w') (h3' : v' ≠ w')
    (h : verts (triangleEdges u v w) = verts (triangleEdges u' v' w')) :
    triangleEdges u v w = triangleEdges u' v' w' := by
  have key : ∀ {a b c a' b' c' : V}, a ≠ b → a ≠ c → b ≠ c →
      verts (triangleEdges a b c) = verts (triangleEdges a' b' c') →
      triangleEdges a b c ⊆ triangleEdges a' b' c' := by
    intro a b c a' b' c' hab hac hbc h e he
    simp only [mem_triangleEdges] at he
    have ha : a ∈ verts (triangleEdges a' b' c') := by rw [← h]; simp [mem_verts_tri]
    have hb : b ∈ verts (triangleEdges a' b' c') := by rw [← h]; simp [mem_verts_tri]
    have hc : c ∈ verts (triangleEdges a' b' c') := by rw [← h]; simp [mem_verts_tri]
    rcases he with rfl | rfl | rfl
    · exact pair_mem_tri hab ha hb
    · exact pair_mem_tri hac ha hc
    · exact pair_mem_tri hbc hb hc
  exact Finset.Subset.antisymm (key h1 h2 h3 h) (key h1' h2' h3' h.symm)

theorem tauFC_le_tau (G : SimpleGraph V) :
    triangleCoverNumber G ≤ tau G := by
  obtain ⟨C, hsub, hC, hcard⟩ := exists_graph_minimumCover G
  have hcov : IsTriangleCover G (C : Set (Sym2 V)) := by
    refine ⟨fun e he => ?_, fun t ht => ?_⟩
    · exact mem_graphEdges.mp (hsub (by simpa using he))
    · obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := SimpleGraph.is3Clique_iff.mp ht
      have := (graph_cover_iff_adj G C).mp hC a b c hab hac hbc
      rcases this with h | h | h
      · exact ⟨s(a, b), by simpa using h, by simp⟩
      · exact ⟨s(a, c), by simpa using h, by simp⟩
      · exact ⟨s(b, c), by simpa using h, by simp⟩
  unfold triangleCoverNumber
  rw [← hcard]
  exact Nat.sInf_le ⟨(C : Set (Sym2 V)), hcov, Set.ncard_coe_finset C⟩

theorem nu_le_nuFC (G : SimpleGraph V) :
    nu G ≤ trianglePackingNumber G := by
  obtain ⟨hP, -⟩ := maximumPacking_spec (graphTriangles G)
  set P := maximumPacking (graphTriangles G) with hPdef
  have hvt : ∀ T ∈ P, ∃ u v w, G.Adj u v ∧ G.Adj u w ∧ G.Adj v w ∧ T = triangleEdges u v w :=
    fun T hT => mem_graphTriangles_iff.mp (hP.1 hT)
  have hinj : Set.InjOn verts (P : Set (Finset (Sym2 V))) := by
    intro T hT T' hT' h
    obtain ⟨u, v, w, a1, a2, a3, rfl⟩ := hvt T hT
    obtain ⟨u', v', w', b1, b2, b3, rfl⟩ := hvt T' hT'
    exact edges_eq_of_verts_eq a1.ne a2.ne a3.ne b1.ne b2.ne b3.ne h
  have hpack : IsTrianglePacking G ((P.image verts : Finset (Finset V)) : Set (Finset V)) := by
    constructor
    · intro t ht
      obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp (by simpa using ht)
      obtain ⟨u, v, w, huv, huw, hvw, rfl⟩ := hvt T hT
      have : verts (triangleEdges u v w) = {u, v, w} := by
        ext x; simp [mem_verts_tri]
      rw [this, SimpleGraph.is3Clique_triple_iff]
      exact ⟨huv, huw, hvw⟩
    · intro t1 ht1 t2 ht2 hne
      obtain ⟨T1, hT1, rfl⟩ := Finset.mem_image.mp (by simpa using ht1)
      obtain ⟨T2, hT2, rfl⟩ := Finset.mem_image.mp (by simpa using ht2)
      have hTne : T1 ≠ T2 := fun h => hne (by rw [h])
      have hd : Disjoint T1 T2 := hP.2 hT1 hT2 hTne
      obtain ⟨u, v, w, -, -, -, rfl⟩ := hvt T1 hT1
      obtain ⟨u', v', w', -, -, -, rfl⟩ := hvt T2 hT2
      rw [Set.ncard_le_one_iff]
      intro x y hx hy
      by_contra hxy
      simp only [Set.mem_inter_iff, Finset.mem_coe] at hx hy
      exact Finset.disjoint_left.mp hd (pair_mem_tri hxy hx.1 hy.1) (pair_mem_tri hxy hx.2 hy.2)
  have hcard : ((P.image verts : Finset (Finset V)) : Set (Finset V)).ncard = P.card := by
    rw [Set.ncard_coe_finset]
    exact Finset.card_image_of_injOn hinj
  have hnu : nu G = P.card := rfl
  rw [hnu, ← hcard]
  unfold trianglePackingNumber
  apply le_csSup
  · refine ⟨Nat.card (Finset V), ?_⟩
    rintro n ⟨T, -, rfl⟩
    calc T.ncard ≤ (Set.univ : Set (Finset V)).ncard :=
          Set.ncard_le_ncard (Set.subset_univ T) Set.finite_univ
      _ = Nat.card (Finset V) := Set.ncard_univ _
  · exact ⟨_, hpack, rfl⟩

end TuzaBridge

open scoped Classical in
theorem tuza_haxell_final {V : Type} [Fintype V] (G : SimpleGraph V) :
    (TuzaConjecture.triangleCoverNumber G : ℝ) ≤ 66 / 23 * TuzaConjecture.trianglePackingNumber G := by
  have h1 := TuzaBridge.tauFC_le_tau G
  have h2 := TuzaBridge.nu_le_nuFC G
  have h3 := Tuza.tuza_bound_nat G
  have : 23 * TuzaConjecture.triangleCoverNumber G ≤ 66 * TuzaConjecture.trianglePackingNumber G := by omega
  have : (23:ℝ) * TuzaConjecture.triangleCoverNumber G ≤ 66 * TuzaConjecture.trianglePackingNumber G := by exact_mod_cast this
  linarith

theorem OMA.solution : type_of% @TuzaConjecture.tuza_conjecture.variants.haxell := tuza_haxell_final
