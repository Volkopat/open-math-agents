import OMAReductions.R_TuzaConjecture_tuza_conjecture_R1
import Mathlib

/-! Tuza's bound when `ν(G) ≤ 1`. Without triangles `τ = 0`. Otherwise `ν = 1`, so any two
triangles share at least two vertices. Fix a triangle `{a, b, c}`. If every triangle contains
`{a, b}` or `{a, c}` (resp. `{a, b}` or `{b, c}`) these two edges cover. Otherwise there are
triangles `{b, c, x}` and `{a, c, x}` (the same `x`), and `{a, b}`, `{c, x}` cover. -/

open TuzaConjecture

namespace TuzaH1

variable {V : Type} [DecidableEq V]

lemma two_of {t : Finset V} {p q r : V} (h : 2 ≤ (t ∩ {p, q, r}).card) :
    (p ∈ t ∧ q ∈ t) ∨ (p ∈ t ∧ r ∈ t) ∨ (q ∈ t ∧ r ∈ t) := by
  by_contra hc
  push_neg at hc
  have : (t ∩ {p, q, r}).card ≤ 1 := by
    refine Finset.card_le_one.mpr fun u hu v hv => ?_
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hu hv
    rcases hu with ⟨hut, rfl | rfl | rfl⟩ <;> rcases hv with ⟨hvt, rfl | rfl | rfl⟩ <;> simp_all
  omega

end TuzaH1

open TuzaH1 in
theorem OMA.solution : OMA.R_TuzaConjecture_tuza_conjecture_R1.H1 := by
  intro V _ G hν
  classical
  by_cases hfree : G.CliqueFree 3
  · rw [triangleCoverNumber_eq_zero G hfree]; omega
  simp only [SimpleGraph.CliqueFree, not_forall, not_not] at hfree
  obtain ⟨T0, hT0⟩ := hfree
  have bdd : BddAbove {n | ∃ T : Set (Finset V), IsTrianglePacking G T ∧ T.ncard = n} :=
    ⟨Nat.card (Finset V), fun n ⟨T, _, hT⟩ => hT ▸ Set.ncard_le_card T⟩
  have hν1 : 1 ≤ trianglePackingNumber G :=
    le_csSup bdd ⟨{T0}, ⟨by simp [hT0], by simp⟩, Set.ncard_singleton _⟩
  -- any two triangles share at least two vertices
  have pair : ∀ t t' : Finset V, G.IsNClique 3 t → G.IsNClique 3 t' → 2 ≤ (t ∩ t').card := by
    intro t t' ht ht'
    by_cases heq : t = t'
    · subst heq; simp [ht.card_eq]
    by_contra hlt
    push_neg at hlt
    have hP : IsTrianglePacking G {t, t'} := by
      refine ⟨by simp [ht, ht'], fun u1 hu1 u2 hu2 hne => ?_⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu1 hu2
      rw [← Finset.coe_inter, Set.ncard_coe_finset]
      rcases hu1 with rfl | rfl <;> rcases hu2 with rfl | rfl
      · exact absurd rfl hne
      · omega
      · rw [Finset.inter_comm]; omega
      · exact absurd rfl hne
    have := le_csSup bdd ⟨{t, t'}, hP, Set.ncard_pair heq⟩
    unfold trianglePackingNumber at hν
    omega
  -- a cover with at most two edges suffices
  suffices h2 : ∃ C : Set (Sym2 V), IsTriangleCover G C ∧ C.ncard ≤ 2 by
    obtain ⟨C, hC, hc⟩ := h2
    have := Nat.sInf_le (s := {n | ∃ C : Set (Sym2 V), IsTriangleCover G C ∧ C.ncard = n}) ⟨C, hC, rfl⟩
    unfold triangleCoverNumber
    omega
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := SimpleGraph.is3Clique_iff.mp hT0
  have adj_of : ∀ t : Finset V, G.IsNClique 3 t → ∀ u ∈ t, ∀ v ∈ t, u ≠ v → G.Adj u v :=
    fun t ht u hu v hv hne => ht.1 (Finset.mem_coe.2 hu) (Finset.mem_coe.2 hv) hne
  have pair_cover : ∀ e f : Sym2 V, e ∈ G.edgeSet → f ∈ G.edgeSet →
      (∀ t : Finset V, G.IsNClique 3 t → (∀ x ∈ e, x ∈ t) ∨ (∀ x ∈ f, x ∈ t)) →
      ∃ C : Set (Sym2 V), IsTriangleCover G C ∧ C.ncard ≤ 2 := by
    intro e f he hf hcov
    refine ⟨{e, f}, ⟨by simp [Set.insert_subset_iff, he, hf], fun t ht => ?_⟩, ?_⟩
    · rcases hcov t ht with h | h
      · exact ⟨e, by simp, h⟩
      · exact ⟨f, by simp, h⟩
    · calc ({e, f} : Set (Sym2 V)).ncard ≤ ({f} : Set (Sym2 V)).ncard + 1 := Set.ncard_insert_le _ _
        _ = 2 := by simp
  have mem2 : ∀ u v : V, ∀ t : Finset V, (∀ x ∈ s(u, v), x ∈ t) ↔ u ∈ t ∧ v ∈ t := by
    intro u v t; simp [Sym2.mem_iff]
  by_cases P : ∀ t : Finset V, G.IsNClique 3 t → (a ∈ t ∧ b ∈ t) ∨ (a ∈ t ∧ c ∈ t)
  · exact pair_cover s(a, b) s(a, c) hab hac fun t ht => by simpa [mem2] using P t ht
  by_cases Q : ∀ t : Finset V, G.IsNClique 3 t → (a ∈ t ∧ b ∈ t) ∨ (b ∈ t ∧ c ∈ t)
  · exact pair_cover s(a, b) s(b, c) hab hbc fun t ht => by simpa [mem2] using Q t ht
  push_neg at P Q
  obtain ⟨t1, ht1, hn1, hn1'⟩ := P
  obtain ⟨t2, ht2, hn2, hn2'⟩ := Q
  -- `t1 ⊇ {b, c}`, `a ∉ t1`; `t2 ⊇ {a, c}`, `b ∉ t2`
  have h1 := two_of (pair t1 _ ht1 hT0)
  have h2 := two_of (pair t2 _ ht2 hT0)
  have hb1 : b ∈ t1 ∧ c ∈ t1 := by
    rcases h1 with h | h | h
    · exact absurd h.2 (hn1 h.1)
    · exact absurd h.2 (hn1' h.1)
    · exact h
  have ha1 : a ∉ t1 := fun h => hn1 h hb1.1
  have ha2 : a ∈ t2 ∧ c ∈ t2 := by
    rcases h2 with h | h | h
    · exact absurd h.2 (hn2 h.1)
    · exact h
    · exact absurd h.2 (hn2' h.1)
  have hb2 : b ∉ t2 := fun h => hn2 ha2.1 h
  -- the third vertex `x` of `t1`
  obtain ⟨x, hx1, hxb, hxc⟩ : ∃ x ∈ t1, x ≠ b ∧ x ≠ c := by
    by_contra hno
    push_neg at hno
    have : t1 ⊆ {b, c} := fun y hy => by
      by_cases hyb : y = b
      · simp [hyb]
      · simp [hno y hy hyb]
    have := Finset.card_le_card this
    rw [ht1.card_eq] at this
    have := Finset.card_insert_le b ({c} : Finset V)
    simp at this
    omega
  have hxa : x ≠ a := fun h => ha1 (h ▸ hx1)
  have ht1eq : t1 = {b, c, x} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl | rfl
      · exact hb1.1
      · exact hb1.2
      · exact hx1
    · rw [ht1.card_eq, Finset.card_eq_three.mpr ⟨b, c, x, hbc.ne, hxb.symm, hxc.symm, rfl⟩]
  have hx2 : x ∈ t2 := by
    have hp := pair t2 t1 ht2 ht1
    rw [ht1eq] at hp
    rcases two_of hp with h | h | h
    · exact absurd h.1 hb2
    · exact absurd h.1 hb2
    · exact h.2
  have ht2eq : t2 = {a, c, x} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl | rfl
      · exact ha2.1
      · exact ha2.2
      · exact hx2
    · rw [ht2.card_eq, Finset.card_eq_three.mpr ⟨a, c, x, hac.ne, hxa.symm, hxc.symm, rfl⟩]
  have hcx : G.Adj c x := adj_of t1 ht1 c hb1.2 x hx1 hxc.symm
  refine pair_cover s(a, b) s(c, x) hab hcx fun t ht => ?_
  have k1 := two_of (pair t _ ht hT0)
  have p2 := pair t t1 ht ht1
  rw [ht1eq] at p2
  have k2 := two_of p2
  have p3 := pair t t2 ht ht2
  rw [ht2eq] at p3
  have k3 := two_of p3
  simp only [mem2]
  by_cases hA : a ∈ t ∧ b ∈ t
  · exact Or.inl hA
  right
  rcases k1 with h | h | h
  · exact absurd h hA
  · have hb : b ∉ t := fun hb => hA ⟨h.1, hb⟩
    rcases k2 with h' | h' | h'
    · exact absurd h'.1 hb
    · exact absurd h'.1 hb
    · exact h'
  · have ha : a ∉ t := fun ha => hA ⟨ha, h.1⟩
    rcases k3 with h' | h' | h'
    · exact absurd h'.1 ha
    · exact absurd h'.1 ha
    · exact h'
