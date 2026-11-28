import OMAReductions.R_TotalColoringConjecture_total_coloring_conjecture_variants_molloy_reed_R1

-- Step TotalColoringConjecture.total_coloring_conjecture.variants.molloy_reed.R1.H2: hypothesis H2
-- of reduction TotalColoringConjecture.total_coloring_conjecture.variants.molloy_reed.R1.
-- Written with Claude Code (AI-assisted).
-- Greedy colouring of the conflict graph on vertices ⊕ edges: a vertex conflicts with at most
-- Δ neighbours and Δ incident edges, an edge with its 2 ends and at most 2(Δ - 1) edges meeting
-- it, so 2Δ + 1 colours suffice.

namespace OMA.TotalH2

open SimpleGraph Finset

/-- Greedy colouring: a graph on a finite type with all degrees ≤ k is (k+1)-colourable. -/
theorem greedy {X : Type} [Fintype X] [DecidableEq X] (H : SimpleGraph X) [DecidableRel H.Adj]
    (k : ℕ) (hk : ∀ x, H.degree x ≤ k) :
    ∀ s : Finset X, ∃ f : X → Fin (k + 1), ∀ u ∈ s, ∀ v ∈ s, H.Adj u v → f u ≠ f v := by
  intro s
  induction s using Finset.induction_on with
  | empty => exact ⟨fun _ => 0, by simp⟩
  | @insert a s ha ih =>
    obtain ⟨f, hf⟩ := ih
    set used : Finset (Fin (k + 1)) := ((H.neighborFinset a).filter (· ∈ s)).image f
    have hused : used.card < k + 1 := by
      calc used.card ≤ ((H.neighborFinset a).filter (· ∈ s)).card := card_image_le
        _ ≤ (H.neighborFinset a).card := card_filter_le _ _
        _ = H.degree a := H.card_neighborFinset_eq_degree a
        _ ≤ k := hk a
        _ < k + 1 := Nat.lt_succ_self _
    have hex : ∃ c, c ∉ used := by
      by_contra hall
      push Not at hall
      have : (univ : Finset (Fin (k + 1))) ⊆ used := fun c _ => hall c
      have := card_le_card this
      simp at this
      omega
    obtain ⟨c, hc⟩ := hex
    refine ⟨Function.update f a c, ?_⟩
    have key : ∀ v ∈ s, H.Adj a v → c ≠ f v := by
      intro v hv hav heq
      exact hc (mem_image.mpr ⟨v, mem_filter.mpr ⟨(H.mem_neighborFinset a v).mpr hav, hv⟩,
        heq.symm⟩)
    have hne : ∀ v ∈ s, v ≠ a := fun v hv h => ha (h ▸ hv)
    intro u hu v hv huv
    rw [mem_insert] at hu hv
    rcases hu with rfl | hu <;> rcases hv with rfl | hv
    · exact absurd huv H.irrefl
    · rw [Function.update_self, Function.update_of_ne (hne v hv)]
      exact key v hv huv
    · rw [Function.update_self, Function.update_of_ne (hne u hu)]
      exact fun h => key u hu huv.symm h.symm
    · rw [Function.update_of_ne (hne u hu), Function.update_of_ne (hne v hv)]
      exact hf u hu v hv huv

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The conflict relation of total colourings. -/
def conflict : V ⊕ G.edgeSet → V ⊕ G.edgeSet → Prop
  | Sum.inl u, Sum.inl v => G.Adj u v
  | Sum.inr e, Sum.inr f => e ≠ f ∧ ∃ v, v ∈ (e : Sym2 V) ∧ v ∈ (f : Sym2 V)
  | Sum.inl v, Sum.inr e => v ∈ (e : Sym2 V)
  | Sum.inr e, Sum.inl v => v ∈ (e : Sym2 V)

theorem incident_card (v : V) :
    (univ.filter (fun e : G.edgeSet => v ∈ (e : Sym2 V))).card ≤ G.degree v := by
  rw [← G.card_incidenceFinset_eq_degree v]
  apply card_le_card_of_injOn Subtype.val
  · intro e he
    simp only [coe_filter, mem_univ, true_and] at he
    rw [Finset.mem_coe, SimpleGraph.mem_incidenceFinset]
    exact ⟨e.2, he⟩
  · intro a _ b _ h
    exact Subtype.ext h

theorem incident_card_erase (v : V) (e : G.edgeSet) (hv : v ∈ (e : Sym2 V)) :
    (univ.filter (fun f : G.edgeSet => f ≠ e ∧ v ∈ (f : Sym2 V))).card + 1 ≤ G.degree v := by
  have hsub : insert e (univ.filter (fun f : G.edgeSet => f ≠ e ∧ v ∈ (f : Sym2 V))) ⊆
      univ.filter (fun f : G.edgeSet => v ∈ (f : Sym2 V)) := by
    intro f hf
    rw [mem_insert] at hf
    rcases hf with rfl | hf
    · simpa using hv
    · simp only [mem_filter, mem_univ, true_and] at hf ⊢
      exact hf.2
  have := card_le_card hsub
  rw [card_insert_of_notMem (by simp)] at this
  exact this.trans (incident_card G v)

theorem total_le : G.totalChromaticNumber ≤ 2 * G.maxDegree + 1 := by
  classical
  let H : SimpleGraph (V ⊕ G.edgeSet) := SimpleGraph.fromRel (conflict G)
  have hadj : ∀ x y, H.Adj x y → conflict G x y := by
    intro x y h
    rw [SimpleGraph.fromRel_adj] at h
    rcases h.2 with h | h
    · exact h
    · rcases x with u | e <;> rcases y with v | f
      · exact h.symm
      · exact h
      · exact h
      · exact ⟨h.1.symm, by obtain ⟨w, h1, h2⟩ := h.2; exact ⟨w, h2, h1⟩⟩
  have hdeg : ∀ x, H.degree x ≤ 2 * G.maxDegree := by
    intro x
    rw [← H.card_neighborFinset_eq_degree]
    rcases x with v | e
    · have hsub : H.neighborFinset (Sum.inl v) ⊆
          (G.neighborFinset v).image Sum.inl ∪
            (univ.filter (fun e : G.edgeSet => v ∈ (e : Sym2 V))).image Sum.inr := by
        intro y hy
        rw [mem_neighborFinset] at hy
        have := hadj _ _ hy
        rcases y with w | f
        · exact mem_union_left _ (mem_image.mpr ⟨w, (G.mem_neighborFinset v w).mpr this, rfl⟩)
        · exact mem_union_right _ (mem_image.mpr ⟨f, by
            simp only [mem_filter, mem_univ, true_and]; exact this, rfl⟩)
      calc (H.neighborFinset (Sum.inl v)).card
          ≤ ((G.neighborFinset v).image Sum.inl ∪
            (univ.filter (fun e : G.edgeSet => v ∈ (e : Sym2 V))).image Sum.inr).card :=
            card_le_card hsub
        _ ≤ (G.neighborFinset v).card +
            (univ.filter (fun e : G.edgeSet => v ∈ (e : Sym2 V))).card :=
            (card_union_le _ _).trans (add_le_add card_image_le card_image_le)
        _ ≤ G.degree v + G.degree v :=
            add_le_add (G.card_neighborFinset_eq_degree v).le (incident_card G v)
        _ ≤ 2 * G.maxDegree := by
            have := G.degree_le_maxDegree v; omega
    · obtain ⟨⟨a, b⟩, hab⟩ := Quot.exists_rep (e : Sym2 V)
      have he : (e : Sym2 V) = s(a, b) := hab.symm
      have ha : a ∈ (e : Sym2 V) := by rw [he]; exact Sym2.mem_mk_left a b
      have hb : b ∈ (e : Sym2 V) := by rw [he]; exact Sym2.mem_mk_right a b
      have hsub : H.neighborFinset (Sum.inr e) ⊆
          ({Sum.inl a, Sum.inl b} : Finset (V ⊕ G.edgeSet)) ∪
            ((univ.filter (fun f : G.edgeSet => f ≠ e ∧ a ∈ (f : Sym2 V))).image Sum.inr ∪
             (univ.filter (fun f : G.edgeSet => f ≠ e ∧ b ∈ (f : Sym2 V))).image Sum.inr) := by
        intro y hy
        rw [mem_neighborFinset] at hy
        have := hadj _ _ hy
        rcases y with w | f
        · apply mem_union_left
          have hw : w ∈ (e : Sym2 V) := this
          rw [he, Sym2.mem_iff] at hw
          rcases hw with rfl | rfl <;> simp
        · apply mem_union_right
          obtain ⟨hne, w, hwe, hwf⟩ := this
          rw [he, Sym2.mem_iff] at hwe
          rcases hwe with rfl | rfl
          · exact mem_union_left _ (mem_image.mpr ⟨f, by simp [hne.symm, hwf], rfl⟩)
          · exact mem_union_right _ (mem_image.mpr ⟨f, by simp [hne.symm, hwf], rfl⟩)
      have h1 := incident_card_erase G a e ha
      have h2 := incident_card_erase G b e hb
      have hda := G.degree_le_maxDegree a
      have hdb := G.degree_le_maxDegree b
      calc (H.neighborFinset (Sum.inr e)).card
          ≤ _ := card_le_card hsub
        _ ≤ ({Sum.inl a, Sum.inl b} : Finset (V ⊕ G.edgeSet)).card +
            ((univ.filter (fun f : G.edgeSet => f ≠ e ∧ a ∈ (f : Sym2 V))).card +
             (univ.filter (fun f : G.edgeSet => f ≠ e ∧ b ∈ (f : Sym2 V))).card) :=
            (card_union_le _ _).trans (Nat.add_le_add_left
              ((card_union_le _ _).trans (add_le_add card_image_le card_image_le)) _)
        _ ≤ 2 + ((G.degree a - 1) + (G.degree b - 1)) := by
            have : ({Sum.inl a, Sum.inl b} : Finset (V ⊕ G.edgeSet)).card ≤ 2 := card_le_two
            omega
        _ ≤ 2 * G.maxDegree := by omega
  obtain ⟨f, hf⟩ := greedy H (2 * G.maxDegree) hdeg univ
  have hcol : G.TotalColorable (2 * G.maxDegree + 1) := by
    refine ⟨f, ?_, ?_, ?_⟩
    · intro u v huv
      exact hf _ (mem_univ _) _ (mem_univ _) (by
        rw [SimpleGraph.fromRel_adj]
        exact ⟨fun h => G.ne_of_adj huv (Sum.inl_injective h), Or.inl huv⟩)
    · intro e e' hne hv
      exact hf _ (mem_univ _) _ (mem_univ _) (by
        rw [SimpleGraph.fromRel_adj]
        exact ⟨fun h => hne (Sum.inr_injective h), Or.inl ⟨hne, hv⟩⟩)
    · intro v e hv
      exact hf _ (mem_univ _) _ (mem_univ _) (by
        rw [SimpleGraph.fromRel_adj]
        exact ⟨Sum.inl_ne_inr, Or.inl hv⟩)
  exact Nat.sInf_le hcol

end OMA.TotalH2

theorem OMA.solution :
    OMA.R_TotalColoringConjecture_total_coloring_conjecture_variants_molloy_reed_R1.H2 := by
  intro V _ _ G _
  exact OMA.TotalH2.total_le G
