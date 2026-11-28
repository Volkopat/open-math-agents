import OMAReductions.R_opg_triangle_packing_vs_triangle_edge_transversal_R1
import Mathlib

open Finset SimpleGraph

theorem OMA.solution : OMA.R_opg_triangle_packing_vs_triangle_edge_transversal_R1.H1 := by
  intro V _ _ G k hk hpack
  classical
  have kill (S : Finset (Sym2 V))
      (hit : ∀ t : Finset V, G.IsNClique 3 t →
        ∃ a ∈ t, ∃ b ∈ t, a ≠ b ∧ s(a, b) ∈ S) :
      (G.deleteEdges (S : Set (Sym2 V))).CliqueFree 3 := by
    intro t ht
    obtain ⟨a, ha, b, hb, hab, he⟩ := hit t (ht.mono (fun _ _ hadj => (deleteEdges_adj.mp hadj).1))
    exact (deleteEdges_adj.mp (ht.isClique ha hb hab)).2 he
  by_cases hnone : ∃ t, G.IsNClique 3 t
  · obtain ⟨t, ht⟩ := hnone
    have hkpos : 1 ≤ k := by
      simpa using hpack {t} (by simpa) (by simp)
    have coverTwo (u v : Finset V) (hu : G.IsNClique 3 u) (hv : G.IsNClique 3 v) :
        2 ≤ (u ∩ v).card := by
      by_cases huv : u = v
      · subst v
        simp [hu.card_eq]
      by_contra! hlt
      have hle : ({u, v} : Finset (Finset V)).card ≤ k := hpack {u, v}
        (by intro q hq; simp at hq; rcases hq with rfl | rfl <;> assumption)
        (by
          intro a ha b hb hab
          simp at ha hb
          rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
          · contradiction
          · omega
          · rw [inter_comm]; omega
          · contradiction)
      rw [card_pair huv] at hle
      omega
    by_cases hone : ∃ u, G.IsNClique 3 u ∧ u ≠ t
    · obtain ⟨u, hu, hut⟩ := hone
      let I := t ∩ u
      have hi : I.card = 2 := by
        have h₂ : 2 ≤ I.card := coverTwo t u ht hu
        by_contra! hne
        have h₃ : 3 ≤ I.card := by omega
        have ht' : I = t := eq_of_subset_of_card_le inter_subset_left (ht.card_eq ▸ h₃)
        have hu' : I = u := eq_of_subset_of_card_le inter_subset_right (hu.card_eq ▸ h₃)
        exact hut (hu'.symm.trans ht')
      obtain ⟨a, b, hab, hI⟩ := card_eq_two.mp hi
      have houter (q : Finset V) (hq : q.card = 3) (hs : I ⊆ q) :
          ∃ c ∈ q, c ∉ I ∧ q = insert c I := by
        obtain ⟨c, hc, hcI⟩ := exists_mem_notMem_of_card_lt_card (show I.card < q.card by omega)
        refine ⟨c, hc, hcI, (eq_of_subset_of_card_le (insert_subset hc hs) ?_).symm⟩
        rw [card_insert_of_notMem hcI, hi, hq]
      obtain ⟨c, hct, hcI, htI⟩ := houter t ht.card_eq inter_subset_left
      obtain ⟨d, hdu, _, huI⟩ := houter u hu.card_eq inter_subset_right
      have hcd : c ≠ d := by
        intro h
        exact hcI (mem_inter.mpr ⟨hct, h ▸ hdu⟩)
      refine ⟨{s(a, b), s(c, d)}, ?_, kill _ ?_⟩
      · have hh : ({s(a, b), s(c, d)} : Finset (Sym2 V)).card ≤ 2 := card_insert_le _ _
        omega
      intro v hv
      by_cases hiv : I ⊆ v
      · exact ⟨a, hiv (by simp [hI]), b, hiv (by simp [hI]), hab, by simp⟩
      have hz : ∃ z ∈ I, z ∉ v := by
        by_contra! hh
        exact hiv hh
      obtain ⟨z, hzI, hzv⟩ := hz
      have forced (q : Finset V) (hq : G.IsNClique 3 q) (x : V)
          (heq : q = insert x I) : x ∈ v := by
        by_contra hx
        have hsub : v ∩ q ⊆ I.erase z := by
          intro y hy
          obtain ⟨hyv, hyq⟩ := mem_inter.mp hy
          have hne : y ≠ z := fun h => hzv (h ▸ hyv)
          have hyi : y ∈ I := by
            rw [heq, mem_insert] at hyq
            exact hyq.resolve_left (fun h => hx (h ▸ hyv))
          exact mem_erase.mpr ⟨hne, hyi⟩
        have hle := card_le_card hsub
        rw [card_erase_of_mem hzI, hi] at hle
        have hbig := coverTwo v q hv hq
        omega
      exact ⟨c, forced t ht c htI, d, forced u hu d huI, hcd, by simp⟩
    · obtain ⟨a, b, c, hab, _, _, htab⟩ := card_eq_three.mp ht.card_eq
      refine ⟨{s(a, b)}, by simpa using (show 1 ≤ 2 * k by omega), kill _ ?_⟩
      intro u hu
      have h : u = t := by
        by_contra hne
        exact hone ⟨u, hu, hne⟩
      subst u
      exact ⟨a, by simp [htab], b, by simp [htab], hab, by simp⟩
  · exact ⟨∅, by simp, kill _ fun t ht => False.elim (hnone ⟨t, ht⟩)⟩