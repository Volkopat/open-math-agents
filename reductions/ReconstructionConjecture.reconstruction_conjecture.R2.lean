import FormalConjectures.Wikipedia.ReconstructionConjecture

-- Reduction ReconstructionConjecture.reconstruction_conjecture.R2
-- of the graph reconstruction conjecture.

/-!
Proved here (Kelly 1957, see Bondy 1991): the degree of every vertex is
determined by the deck, and regular graphs are reconstructible.

H1 is the classical theorem that disconnected graphs are reconstructible
(Kelly 1957; Bondy 1991). It is applied to the graph and to its complement.
H2 is the remaining case: graphs that are not regular, connected, and
whose complement is connected.
-/

namespace OMA.R_ReconstructionConjecture_reconstruction_conjecture_R2

open SimpleGraph ReconstructionConjecture Finset

open Classical

private theorem complement_iso {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G ≃g H) : Nonempty (Gᶜ ≃g Hᶜ) := by
  refine ⟨⟨f.toEquiv, ?_⟩⟩
  intro a b
  change (f a ≠ f b ∧ ¬ H.Adj (f a) (f b)) ↔ (a ≠ b ∧ ¬ G.Adj a b)
  exact and_congr (not_congr f.injective.eq_iff) (not_congr f.map_rel_iff)

private theorem induce_complement {V : Type*} (G : SimpleGraph V) (S : Set V) :
    (Gᶜ).induce S = (G.induce S)ᶜ := by
  ext a b
  change ((a : V) ≠ (b : V) ∧ ¬ G.Adj a b) ↔ (a ≠ b ∧ ¬ G.Adj a b)
  exact and_congr (not_congr Subtype.val_injective.eq_iff) Iff.rfl

private theorem complement_hypomorphic {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (h : Hypomorphic G H) : Hypomorphic Gᶜ Hᶜ := by
  obtain ⟨σ, cards⟩ := h
  refine ⟨σ, fun v => ?_⟩
  obtain ⟨f⟩ := cards v
  rw [induce_complement, induce_complement]
  exact complement_iso f

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

/-- Regular graphs are reconstructible (Kelly 1957). -/
theorem regular_case {V W : Type} [Fintype V] [Fintype W] (hV : 3 ≤ Fintype.card V)
    (G : SimpleGraph V) (H : SimpleGraph W) {d : ℕ} (hG : G.IsRegularOfDegree d)
    (h : Hypomorphic G H) : Nonempty (G ≃g H) := by
  obtain ⟨σ, hc⟩ := h
  have hH : ∀ w, H.degree w = d := fun w => by
    have := deg_hyp hV G H σ hc (σ.symm w)
    rw [σ.apply_symm_apply] at this
    rw [this]
    exact hG _
  have hne : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨v⟩ := hne
  obtain ⟨φ⟩ := hc v
  have key : ∀ u : ({v}ᶜ : Set V), (H.Adj (φ u) (σ v) ↔ G.Adj u v) := by
    intro u
    have a1 := induce_degree G v u
    have a2 := induce_degree H (σ v) (φ u)
    have a3 := iso_degree φ u
    rw [hG u] at a1
    rw [hH] at a2
    by_cases p : G.Adj u v <;> by_cases q : H.Adj (φ u) (σ v) <;> simp [p, q] at a1 a2 ⊢ <;>
      omega
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

/-- Disconnected graphs are reconstructible (Kelly 1957; Bondy 1991). -/
def H1 : Prop :=
  ∀ {V W : Type} [Fintype V] [Fintype W], 3 ≤ Fintype.card V →
    ∀ (G : SimpleGraph V) (H : SimpleGraph W), ¬ G.Connected →
      Hypomorphic G H → Nonempty (G ≃g H)

/-- The remaining case: non-regular graphs that are connected with connected complement. -/
def H2 : Prop :=
  ∀ {V W : Type} [Fintype V] [Fintype W], 3 ≤ Fintype.card V →
    ∀ (G : SimpleGraph V) (H : SimpleGraph W), (¬ ∃ d, G.IsRegularOfDegree d) →
      G.Connected → Gᶜ.Connected → Hypomorphic G H → Nonempty (G ≃g H)

theorem main : H1 → H2 → type_of% @ReconstructionConjecture.reconstruction_conjecture := by
  intro h1 h2 V W _ _ hV G H h
  by_cases hr : ∃ d, G.IsRegularOfDegree d
  · obtain ⟨d, hd⟩ := hr
    exact regular_case hV G H hd h
  by_cases hc : G.Connected
  · by_cases hcc : Gᶜ.Connected
    · exact h2 hV G H hr hc hcc h
    · obtain ⟨f⟩ := h1 hV Gᶜ Hᶜ hcc (complement_hypomorphic h)
      simpa only [compl_compl] using complement_iso f
  · exact h1 hV G H hc h

end OMA.R_ReconstructionConjecture_reconstruction_conjecture_R2
