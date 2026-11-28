import OMAReductions.R_ReconstructionConjecture_reconstruction_conjecture_R1

-- Reduction ReconstructionConjecture.reconstruction_conjecture.R1.H2.R1 of step ReconstructionConjecture.reconstruction_conjecture.R1.H2
-- Credit: @AlfredMelson

namespace OMA.R_ReconstructionConjecture_reconstruction_conjecture_R1_H2_R1

open SimpleGraph ReconstructionConjecture Finset Classical

-- Degree and card identities, and extension of a card bijection, adapted from the
-- project's ReconstructionConjecture.reconstruction_conjecture.R2 proof.
/-- Isomorphisms preserve degrees. -/
theorem iso_degree {X Y : Type} [Fintype X] [Fintype Y] {K : SimpleGraph X}
    {L : SimpleGraph Y} (f : K ≃g L) (x : X) : L.degree (f x) = K.degree x := by
  rw [← card_neighborSet_eq_degree, ← card_neighborSet_eq_degree]
  symm
  refine Fintype.card_congr (Equiv.subtypeEquiv f.toEquiv (fun a => ?_))
  show K.Adj x a ↔ L.Adj (f x) (f a)
  exact f.map_rel_iff.symm

/-- Isomorphisms preserve the degree sum. -/
theorem iso_sum {X Y : Type} [Fintype X] [Fintype Y] {K : SimpleGraph X}
    {L : SimpleGraph Y} (f : K ≃g L) : ∑ y, L.degree y = ∑ x, K.degree x := by
  rw [← Equiv.sum_comp f.toEquiv]
  exact sum_congr rfl (fun x _ => iso_degree f x)

/-- Degree in a vertex-deleted subgraph. -/
theorem induce_degree {X : Type} [Fintype X] (K : SimpleGraph X) (v : X)
    (u : ({v}ᶜ : Set X)) :
    (K.induce {v}ᶜ).degree u + (if K.Adj u v then 1 else 0) = K.degree u := by
  rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree]
  have h1 : #((K.induce {v}ᶜ).neighborFinset u) = #((K.neighborFinset u).filter (· ≠ v)) := by
    refine card_bij (fun a _ => a.val) ?_ ?_ ?_
    · intro a ha
      have h2 := a.2
      simp only [mem_neighborFinset, comap_adj, Function.Embedding.coe_subtype] at ha
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at h2
      simp only [mem_filter, mem_neighborFinset]
      exact ⟨ha, h2⟩
    · intro a _ b _ h
      exact Subtype.ext h
    · intro b hb
      simp only [mem_filter, mem_neighborFinset] at hb
      refine ⟨⟨b, hb.2⟩, ?_, rfl⟩
      simp only [mem_neighborFinset, comap_adj, Function.Embedding.coe_subtype]
      exact hb.1
  have h2 : #((K.neighborFinset u).filter (fun w => ¬ (w ≠ v))) =
      if K.Adj u v then 1 else 0 := by
    split_ifs with h
    · rw [card_eq_one]
      refine ⟨v, ?_⟩
      ext w
      simp only [mem_filter, mem_neighborFinset, ne_eq, not_not, mem_singleton]
      constructor
      · exact fun h' => h'.2
      · rintro rfl
        exact ⟨h, rfl⟩
    · rw [card_eq_zero, filter_eq_empty_iff]
      intro w hw hne
      apply hne
      rintro rfl
      exact h ((mem_neighborFinset _ _ _).mp hw)
  rw [h1, ← h2, card_filter_add_card_filter_not]

/-- Kelly's identity: the degree sum of a card plus twice the deleted degree. -/
theorem card_deck_sum {X : Type} [Fintype X] (K : SimpleGraph X) (v : X) :
    (∑ u, (K.induce {v}ᶜ).degree u) + 2 * K.degree v = ∑ x, K.degree x := by
  have e1 : (∑ u : ({v}ᶜ : Set X), (K.induce {v}ᶜ).degree u) +
      (∑ u : ({v}ᶜ : Set X), (if K.Adj u v then 1 else 0)) =
      ∑ u : ({v}ᶜ : Set X), K.degree u := by
    rw [← sum_add_distrib]
    exact sum_congr rfl (fun u _ => induce_degree K v u)
  have hs : ∀ g : X → ℕ, ∑ u ∈ univ.erase v, g u = ∑ u : ({v}ᶜ : Set X), g u := fun g =>
    sum_subtype (univ.erase v) (fun x => by simp) g
  have e2 := hs (fun u => K.degree u)
  have e3 := hs (fun u => if K.Adj u v then 1 else 0)
  have e4 := sum_erase_add univ (fun u => K.degree u) (mem_univ v)
  have e5 := sum_erase_add univ (fun u => if K.Adj u v then 1 else 0) (mem_univ v)
  have hb : ∑ x, (if K.Adj x v then 1 else 0) = K.degree v := by
    rw [sum_boole, ← card_neighborFinset_eq_degree, neighborFinset_eq_filter]
    simp [adj_comm]
  simp only [SimpleGraph.irrefl, if_false, add_zero] at e5
  omega

/-- Kelly's lemma: hypomorphisms preserve degrees. -/
theorem deg_hyp {V W : Type} [Fintype V] [Fintype W] (hV : 3 ≤ Fintype.card V)
    (G : SimpleGraph V) (H : SimpleGraph W) (σ : V ≃ W)
    (hc : ∀ v, Nonempty (G.induce {v}ᶜ ≃g H.induce {σ v}ᶜ)) (v : V) :
    H.degree (σ v) = G.degree v := by
  have hS : ∀ v, (∑ u, (G.induce {v}ᶜ).degree u) = ∑ u, (H.induce {σ v}ᶜ).degree u :=
    fun v => by
      obtain ⟨f⟩ := hc v
      exact (iso_sum f).symm
  have tG : ∑ v, ((∑ u, (G.induce {v}ᶜ).degree u) + 2 * G.degree v) =
      Fintype.card V * ∑ x, G.degree x := by
    rw [sum_congr rfl (fun v _ => card_deck_sum G v)]
    simp
  have tH : ∑ v, ((∑ u, (H.induce {σ v}ᶜ).degree u) + 2 * H.degree (σ v)) =
      Fintype.card V * ∑ x, H.degree x := by
    rw [sum_congr rfl (fun v _ => card_deck_sum H (σ v))]
    simp
  rw [sum_add_distrib, ← mul_sum] at tG tH
  have hσ : ∑ v, H.degree (σ v) = ∑ x, H.degree x := Equiv.sum_comp σ (fun x => H.degree x)
  rw [hσ, sum_congr rfl (fun v _ => (hS v).symm)] at tH
  obtain ⟨m, hm⟩ : ∃ m, Fintype.card V = m + 3 := ⟨_, (Nat.sub_add_cancel hV).symm⟩
  rw [hm] at tG tH
  have heq : ∑ x, G.degree x = ∑ x, H.degree x := by
    have e : (m + 1) * ∑ x, G.degree x = (m + 1) * ∑ x, H.degree x := by nlinarith
    exact Nat.eq_of_mul_eq_mul_left (Nat.succ_pos m) e
  have a1 := card_deck_sum G v
  have a2 := card_deck_sum H (σ v)
  have a3 := hS v
  omega

private theorem gap_case {V W : Type} [Fintype V] [Fintype W] (hV : 3 ≤ Fintype.card V)
    (G : SimpleGraph V) (H : SimpleGraph W) (v : V)
    (gap : ∀ a b : V, a ≠ v → b ≠ v → G.degree a + 1 ≠ G.degree b)
    (h : Hypomorphic G H) : Nonempty (G ≃g H) := by
  obtain ⟨σ, hc⟩ := h
  obtain ⟨φ⟩ := hc v
  have key : ∀ u : ({v}ᶜ : Set V), (H.Adj (φ u) (σ v) ↔ G.Adj u v) := by
    intro u
    have a1 := induce_degree G v u
    have a2 := induce_degree H (σ v) (φ u)
    have a3 := iso_degree φ u
    let b := σ.symm (φ u : W)
    have hb : b ≠ v := by
      intro he
      exact (φ u).2 (show (φ u : W) = σ v from
        (σ.apply_symm_apply _).symm.trans (congrArg σ he))
    have db := deg_hyp hV G H σ hc b
    change H.degree (σ (σ.symm _)) = G.degree b at db
    rw [σ.apply_symm_apply] at db
    have g1 := gap u b u.2 hb
    have g2 := gap b u hb u.2
    by_cases p : G.Adj u v <;> by_cases q : H.Adj (φ u) (σ v) <;>
      simp [p, q] at a1 a2 ⊢ <;> omega
  let f : V → W := fun u => if hu : u = v then σ v else (φ ⟨u, hu⟩ : W)
  have fv : f v = σ v := by simp [f]
  have fu : ∀ u (hu : u ≠ v), f u = φ ⟨u, hu⟩ := fun u hu => by simp [f, hu]
  have fne : ∀ u (hu : u ≠ v), f u ≠ σ v := fun u hu => by
    rw [fu u hu]
    exact (φ ⟨u, hu⟩).2
  have finj : Function.Injective f := by
    intro a b hab
    by_cases ha : a = v <;> by_cases hb : b = v
    · rw [ha, hb]
    · rw [ha] at hab
      exact absurd (hab.symm.trans fv) (fne b hb)
    · rw [hb] at hab
      exact absurd (hab.trans fv) (fne a ha)
    · rw [fu a ha, fu b hb] at hab
      have := φ.injective (Subtype.ext hab)
      exact congrArg Subtype.val this
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr ⟨finj, Fintype.card_congr σ⟩
  refine ⟨⟨Equiv.ofBijective f hbij, ?_⟩⟩
  intro a b
  simp only [Equiv.ofBijective_apply]
  by_cases ha : a = v <;> by_cases hb : b = v
  · rw [ha, hb]
    exact iff_of_false (H.irrefl) (G.irrefl)
  · rw [ha, fv, fu b hb, H.adj_comm, G.adj_comm]
    exact key ⟨b, hb⟩
  · rw [hb, fv, fu a ha]
    exact key ⟨a, ha⟩
  · rw [fu a ha, fu b hb]
    exact φ.map_rel_iff

private def IntervalModel {X : Type} (K : SimpleGraph X) : Prop :=
  ∃ l r : X → ℝ, (∀ v, l v ≤ r v) ∧
    ∀ x y, K.Adj x y ↔ x ≠ y ∧ l x ≤ r y ∧ l y ≤ r x

def H1 : Prop := ∀ {V W : Type} [Fintype V] [Fintype W],
  3 ≤ Fintype.card V → ∀ (G : SimpleGraph V) (H : SimpleGraph W),
  ¬ IntervalModel G → ¬ IntervalModel Gᶜ → ¬ IntervalModel H → ¬ IntervalModel Hᶜ →
  (∀ v, ∃ a b : V, a ≠ v ∧ b ≠ v ∧ G.degree a + 1 = G.degree b) →
  (¬ G.Connected ∨ ¬ Gᶜ.Connected) → Hypomorphic G H → Nonempty (G ≃g H)

def H2 : Prop := ∀ {V W : Type} [Fintype V] [Fintype W],
  3 ≤ Fintype.card V → ∀ (G : SimpleGraph V) (H : SimpleGraph W),
  ¬ IntervalModel G → ¬ IntervalModel Gᶜ → ¬ IntervalModel H → ¬ IntervalModel Hᶜ →
  (∀ v, ∃ a b : V, a ≠ v ∧ b ≠ v ∧ G.degree a + 1 = G.degree b) →
  G.Connected → Gᶜ.Connected → Hypomorphic G H → Nonempty (G ≃g H)

theorem main : H1 → H2 → OMA.R_ReconstructionConjecture_reconstruction_conjecture_R1.H2 := by
  classical
  intro h1 h2 V W _ _ hn G H iG icG iH icH deck
  by_cases bad : ∀ v, ∃ a b : V, a ≠ v ∧ b ≠ v ∧ G.degree a + 1 = G.degree b
  · by_cases hc : G.Connected
    · by_cases hcc : Gᶜ.Connected
      · exact h2 hn G H iG icG iH icH bad hc hcc deck
      · exact h1 hn G H iG icG iH icH bad (Or.inr hcc) deck
    · exact h1 hn G H iG icG iH icH bad (Or.inl hc) deck
  · push_neg at bad
    obtain ⟨v,hv⟩ := bad
    exact gap_case hn G H v hv deck

end OMA.R_ReconstructionConjecture_reconstruction_conjecture_R1_H2_R1
