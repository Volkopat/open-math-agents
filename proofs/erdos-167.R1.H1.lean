import OMAReductions.R_erdos_167_R1

/-!
The packing-number-at-most-one case of Tuza's conjecture (Tuza, 1981).
Source: https://www.erdosproblems.com/167
Credit: @grp06. The problem's formal statement is credited to @Ciphore.
-/

open OMA.S_erdos_167 (IsEdgeDisjointTrianglePacking)

namespace OMA

private theorem thirdVertex {V : Type} [DecidableEq V] {A : Finset V} {a b : V}
    (hA : A.card = 3) (ha : a ∈ A) (hb : b ∈ A) (hab : a ≠ b) :
    ∃ c, c ∈ A ∧ A = {a, b, c} := by
  have hpair : ({a, b} : Finset V).card ≤ 2 := Finset.card_le_two
  have hlt : ({a, b} : Finset V).card < A.card := by omega
  obtain ⟨c, hc, hcnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have hac : a ≠ c := by
    intro h
    exact hcnot (Finset.mem_insert.mpr (Or.inl h.symm))
  have hbc : b ≠ c := by
    intro h
    exact hcnot (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr h.symm)))
  have hcard : ({a, b, c} : Finset V).card = 3 :=
    Finset.card_eq_three.mpr ⟨a, b, c, hab, hac, hbc, rfl⟩
  refine ⟨c, hc, (Finset.eq_of_subset_of_card_le (s := ({a, b, c} : Finset V))
    (t := A) ?_ (hA.trans hcard.symm).le).symm⟩
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hc

private theorem containsThird {V : Type} [DecidableEq V] {A : Finset V} {a b c : V}
    (hmiss : ¬ (a ∈ A ∧ b ∈ A))
    (hlarge : 2 ≤ (A ∩ {a, b, c}).card) : c ∈ A := by
  by_contra hc
  have hsmall : ∀ x ∈ A ∩ {a, b, c}, x = a ∨ x = b := by
    intro x hx
    obtain ⟨hxA, hxabc⟩ := Finset.mem_inter.mp hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxabc
    rcases hxabc with hxa | hxb | hxc
    · exact Or.inl hxa
    · exact Or.inr hxb
    · exact False.elim (hc (hxc ▸ hxA))
  by_cases ha : a ∈ A
  · have hb : b ∉ A := fun h => hmiss ⟨ha, h⟩
    have hsub : A ∩ {a, b, c} ⊆ ({a} : Finset V) := by
      intro x hx
      rcases hsmall x hx with hxa | rfl
      · exact Finset.mem_singleton.mpr hxa
      · exact False.elim (hb (Finset.mem_inter.mp hx).1)
    have h := Finset.card_le_card hsub
    rw [Finset.card_singleton] at h
    omega
  · have hsub : A ∩ {a, b, c} ⊆ ({b} : Finset V) := by
      intro x hx
      rcases hsmall x hx with rfl | hxb
      · exact False.elim (ha (Finset.mem_inter.mp hx).1)
      · exact Finset.mem_singleton.mpr hxb
    have h := Finset.card_le_card hsub
    rw [Finset.card_singleton] at h
    omega

end OMA

theorem OMA.solution : OMA.R_erdos_167_R1.H1 := by
  intro V _ _ G k hk hpacking
  classical
  have remove_hits (F : Finset (Sym2 V))
      (hF : ∀ A, G.IsNClique 3 A →
        ∃ a ∈ A, ∃ b ∈ A, a ≠ b ∧ s(a, b) ∈ F) :
      (G.deleteEdges (F : Set (Sym2 V))).CliqueFree 3 := by
    intro A hA
    have hAG : G.IsNClique 3 A :=
      ⟨hA.isClique.mono (SimpleGraph.deleteEdges_le (G := G) (F : Set (Sym2 V))),
        hA.card_eq⟩
    obtain ⟨a, ha, b, hb, hab, he⟩ := hF A hAG
    have hadj := hA.isClique (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb) hab
    exact (SimpleGraph.deleteEdges_adj.mp hadj).2 (Finset.mem_coe.mpr he)
  have empty_cover (hnone : ¬ ∃ A, G.IsNClique 3 A) :
      ∃ F : Finset (Sym2 V), F.card ≤ 2 * k ∧
        (∀ e ∈ F, e ∈ G.edgeSet) ∧ (G.deleteEdges (F : Set (Sym2 V))).CliqueFree 3 := by
    refine ⟨∅, by simp, by simp, remove_hits ∅ ?_⟩
    intro A hA
    exact (hnone ⟨A, hA⟩).elim
  by_cases hk0 : k = 0
  · apply empty_cover
    rintro ⟨A, hA⟩
    have hp : IsEdgeDisjointTrianglePacking G {A} := by
      constructor
      · intro t ht
        rcases Finset.mem_singleton.mp ht with rfl
        exact hA
      · intro t ht u hu htu
        exact (htu ((Finset.mem_singleton.mp ht).trans
          (Finset.mem_singleton.mp hu).symm)).elim
    have h := hpacking {A} hp
    simp [hk0] at h
  have hk1 : k = 1 := by omega
  have intersect_two {A B : Finset V} (hA : G.IsNClique 3 A) (hB : G.IsNClique 3 B)
      (hAB : A ≠ B) : 2 ≤ (A ∩ B).card := by
    by_contra h
    have hle : (A ∩ B).card ≤ 1 := by omega
    have hp : IsEdgeDisjointTrianglePacking G {A, B} := by
      have split_mem : ∀ t ∈ ({A, B} : Finset (Finset V)), t = A ∨ t = B := by
        intro t ht
        simpa only [Finset.mem_insert, Finset.mem_singleton] using ht
      constructor
      · intro t ht
        rcases split_mem t ht with rfl | rfl
        · exact hA
        · exact hB
      · intro t ht u hu htu
        rcases split_mem t ht with rfl | rfl <;> rcases split_mem u hu with rfl | rfl
        · exact (htu rfl).elim
        · exact hle
        · rw [Finset.inter_comm]
          exact hle
        · exact (htu rfl).elim
    have hbound := hpacking {A, B} hp
    rw [Finset.card_pair_eq_two_iff.mpr hAB, hk1] at hbound
    omega
  by_cases hex : ∃ A, G.IsNClique 3 A
  · obtain ⟨A, hA⟩ := hex
    have one_edge (a b : V) (hab : a ≠ b) (haA : a ∈ A) (hbA : b ∈ A)
        (hall : ∀ T, G.IsNClique 3 T → a ∈ T ∧ b ∈ T) :
        ∃ F : Finset (Sym2 V), F.card ≤ 2 * k ∧
          (∀ e ∈ F, e ∈ G.edgeSet) ∧ (G.deleteEdges (F : Set (Sym2 V))).CliqueFree 3 := by
      refine ⟨{s(a, b)}, by simp [hk1], ?_, remove_hits {s(a, b)} ?_⟩
      · intro e he
        rcases Finset.mem_singleton.mp he with rfl
        change G.Adj a b
        exact hA.isClique (Finset.mem_coe.mpr haA) (Finset.mem_coe.mpr hbA) hab
      · intro T hT
        exact ⟨a, (hall T hT).1, b, (hall T hT).2, hab, by simp⟩
    by_cases hother : ∃ B, G.IsNClique 3 B ∧ A ≠ B
    · obtain ⟨B, hB, hAB⟩ := hother
      obtain ⟨P, hP, hPcard⟩ :=
        Finset.le_card_iff_exists_subset_card.mp (intersect_two hA hB hAB)
      obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hPcard
      have ha := Finset.mem_inter.mp (hP (show a ∈ ({a, b} : Finset V) by simp))
      have hb := Finset.mem_inter.mp (hP (show b ∈ ({a, b} : Finset V) by simp))
      obtain ⟨c, hcA, hAform⟩ := OMA.thirdVertex hA.card_eq ha.1 hb.1 hab
      obtain ⟨d, hdB, hBform⟩ := OMA.thirdVertex hB.card_eq ha.2 hb.2 hab
      have hcd : c ≠ d := by
        intro h
        subst d
        exact hAB (hAform.trans hBform.symm)
      have opposite {T : Finset V} (hT : G.IsNClique 3 T)
          (hmiss : ¬ (a ∈ T ∧ b ∈ T)) : c ∈ T ∧ d ∈ T := by
        have hTA : T ≠ A := by
          rintro rfl
          exact hmiss ⟨ha.1, hb.1⟩
        have hTB : T ≠ B := by
          rintro rfl
          exact hmiss ⟨ha.2, hb.2⟩
        have hTac := intersect_two hT hA hTA
        have hTbd := intersect_two hT hB hTB
        rw [hAform] at hTac
        rw [hBform] at hTbd
        exact ⟨OMA.containsThird hmiss hTac, OMA.containsThird hmiss hTbd⟩
      by_cases hthird : ∃ C, G.IsNClique 3 C ∧ ¬ (a ∈ C ∧ b ∈ C)
      · obtain ⟨C, hC, hmiss⟩ := hthird
        obtain ⟨hcC, hdC⟩ := opposite hC hmiss
        refine ⟨{s(a, b), s(c, d)}, by rw [hk1]; exact Finset.card_le_two, ?_,
          remove_hits {s(a, b), s(c, d)} ?_⟩
        · intro e he
          simp only [Finset.mem_insert, Finset.mem_singleton] at he
          rcases he with rfl | rfl
          · change G.Adj a b
            exact hA.isClique (Finset.mem_coe.mpr ha.1) (Finset.mem_coe.mpr hb.1) hab
          · change G.Adj c d
            exact hC.isClique (Finset.mem_coe.mpr hcC) (Finset.mem_coe.mpr hdC) hcd
        · intro T hT
          by_cases hboth : a ∈ T ∧ b ∈ T
          · exact ⟨a, hboth.1, b, hboth.2, hab, by simp⟩
          · obtain ⟨hc, hd⟩ := opposite hT hboth
            exact ⟨c, hc, d, hd, hcd, by simp⟩
      · apply one_edge a b hab ha.1 hb.1
        intro T hT
        by_contra hmiss
        exact hthird ⟨T, hT, hmiss⟩
    · obtain ⟨a, b, c, hab, _, _, hform⟩ := Finset.card_eq_three.mp hA.card_eq
      have haA : a ∈ A := by simp [hform]
      have hbA : b ∈ A := by simp [hform]
      apply one_edge a b hab haA hbA
      intro T hT
      have hAT : A = T := by
        by_contra h
        exact hother ⟨T, hT, h⟩
      rw [← hAT]
      exact ⟨haA, hbA⟩
  · exact empty_cover hex
