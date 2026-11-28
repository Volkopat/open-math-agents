import OMAReductions.R_erdos_738_R1
import Mathlib

/-!
Stars in triangle-free graphs of infinite chromatic number.
* Greedy colouring: if every vertex has its neighbours inside a finite set of fewer than `s`
  vertices, every finite vertex set can be properly coloured with `s` colours (insert one vertex
  at a time; its neighbours use fewer than `s` colours).
* Compactness: the proper-colouring conditions are closed in the compact space `V → Fin s`, so
  the whole graph is `s`-colourable.
* Hence a graph of infinite chromatic number has a vertex `v` with `s` neighbours; in a
  triangle-free graph they are pairwise non-adjacent, and `v` with them spans an induced star.
-/

namespace OMA.E738Star

lemma finite_coloring {V : Type} [DecidableEq V] (G : SimpleGraph V) (s : ℕ)
    (hdeg : ∀ v, ∃ N : Finset V, N.card < s ∧ ∀ w, G.Adj v w → w ∈ N) (S : Finset V) :
    ∃ c : V → Fin s, ∀ u ∈ S, ∀ v ∈ S, G.Adj u v → c u ≠ c v := by
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨fun v => ⟨0, ?_⟩, by simp⟩
    obtain ⟨N, hN, -⟩ := hdeg v
    omega
  | insert a S ha ih =>
    obtain ⟨c, hc⟩ := ih
    obtain ⟨N, hN, hNa⟩ := hdeg a
    have hex : ∃ col : Fin s, col ∉ N.image c := by
      by_contra h
      push_neg at h
      have h1 : (Finset.univ : Finset (Fin s)) ⊆ N.image c := fun x _ => h x
      have h2 := Finset.card_le_card h1
      have h3 := Finset.card_image_le (s := N) (f := c)
      rw [Finset.card_univ, Fintype.card_fin] at h2
      omega
    obtain ⟨col, hcol⟩ := hex
    refine ⟨Function.update c a col, ?_⟩
    intro u hu v hv huv
    by_cases hua : u = a
    · subst hua
      have hvS : v ∈ S := by
        rcases Finset.mem_insert.1 hv with h | h
        · exact absurd (h ▸ huv) G.irrefl
        · exact h
      have hvu : v ≠ u := fun h => ha (h ▸ hvS)
      rw [Function.update_self, Function.update_of_ne hvu]
      intro h
      exact hcol (h ▸ Finset.mem_image_of_mem c (hNa v huv))
    · have huS : u ∈ S := (Finset.mem_insert.1 hu).resolve_left hua
      by_cases hva : v = a
      · subst hva
        rw [Function.update_of_ne hua, Function.update_self]
        intro h
        exact hcol (h ▸ Finset.mem_image_of_mem c (hNa u huv.symm))
      · have hvS : v ∈ S := (Finset.mem_insert.1 hv).resolve_left hva
        rw [Function.update_of_ne hua, Function.update_of_ne hva]
        exact hc u huS v hvS huv

lemma colorable_of_deg {V : Type} (G : SimpleGraph V) (s : ℕ)
    (hdeg : ∀ v, ∃ N : Finset V, N.card < s ∧ ∀ w, G.Adj v w → w ∈ N) : G.Colorable s := by
  classical
  let C : {p : V × V // G.Adj p.1 p.2} → Set (V → Fin s) := fun e => {c | c e.1.1 ≠ c e.1.2}
  have hclosed : ∀ e, IsClosed (C e) := by
    intro e
    have hcont : Continuous fun c : V → Fin s => (c e.1.1, c e.1.2) :=
      (continuous_apply _).prodMk (continuous_apply _)
    exact (isClosed_discrete {p : Fin s × Fin s | p.1 ≠ p.2}).preimage hcont
  have hfip : ∀ u : Finset {p : V × V // G.Adj p.1 p.2}, (Set.univ ∩ ⋂ e ∈ u, C e).Nonempty := by
    intro u
    obtain ⟨c, hc⟩ := finite_coloring G s hdeg (u.image (fun e => e.1.1) ∪ u.image (fun e => e.1.2))
    refine ⟨c, Set.mem_univ _, ?_⟩
    simp only [Set.mem_iInter]
    intro e he
    exact hc _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ he)) _
      (Finset.mem_union_right _ (Finset.mem_image_of_mem _ he)) e.2
  obtain ⟨c, -, hc⟩ := isCompact_univ.inter_iInter_nonempty C hclosed hfip
  exact ⟨SimpleGraph.Coloring.mk c (fun {u v} h => Set.mem_iInter.1 hc ⟨(u, v), h⟩)⟩

end OMA.E738Star

theorem OMA.solution : OMA.R_erdos_738_R1.H1 := by
  intro V G hchi htri W _ T hT hstar
  classical
  obtain ⟨c0, hc0⟩ := hstar
  set s := Fintype.card W - 1 with hs
  have hbig : ∃ v : V, ∃ N : Finset V, N.card = s ∧ ∀ w ∈ N, G.Adj v w := by
    by_contra hno
    push_neg at hno
    have hdeg : ∀ v, ∃ N : Finset V, N.card < s ∧ ∀ w, G.Adj v w → w ∈ N := by
      intro v
      by_cases hfin : (G.neighborSet v).Finite
      · refine ⟨hfin.toFinset, ?_, fun w hw => by simpa using hw⟩
        by_contra hge
        push_neg at hge
        obtain ⟨N, hNsub, hNcard⟩ := Finset.exists_subset_card_eq hge
        obtain ⟨w, hw, hnw⟩ := hno v N hNcard
        exact hnw (by simpa using hNsub hw)
      · obtain ⟨N, hNsub, hNcard⟩ := Set.Infinite.exists_subset_card_eq hfin s
        obtain ⟨w, hw, hnw⟩ := hno v N hNcard
        exact (hnw (hNsub hw)).elim
    have hle := (OMA.E738Star.colorable_of_deg G s hdeg).chromaticNumber_le
    rw [hchi] at hle
    exact absurd hle (by simp)
  obtain ⟨v, N, hNcard, hNadj⟩ := hbig
  let L : Finset W := Finset.univ.erase c0
  have hL : L.card = N.card := by
    rw [hNcard, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
  let e : {x // x ∈ L} ≃ {x // x ∈ N} := Fintype.equivOfCardEq (by simpa using hL)
  let φ : W → V := fun x => if h : x = c0 then v else (e ⟨x, by simp [L, h]⟩).1
  have hφc : φ c0 = v := by simp [φ]
  have hφN : ∀ x, x ≠ c0 → φ x ∈ N := by
    intro x hx
    simp only [φ, dif_neg hx]
    exact (e _).2
  have hφne : ∀ x, x ≠ c0 → φ x ≠ v := by
    intro x hx h
    have := hNadj _ (hφN x hx)
    rw [h] at this
    exact G.irrefl this
  have htree3 : T.CliqueFree 3 := hT.isAcyclic.cliqueFree le_rfl
  have hinj : Function.Injective φ := by
    intro a b hab
    by_cases ha : a = c0 <;> by_cases hb : b = c0
    · rw [ha, hb]
    · rw [ha, hφc] at hab
      exact absurd hab.symm (hφne b hb)
    · rw [hb, hφc] at hab
      exact absurd hab (hφne a ha)
    · simp only [φ, dif_neg ha, dif_neg hb] at hab
      have := e.injective (Subtype.ext hab)
      simpa using this
  refine ⟨⟨⟨φ, hinj⟩, ?_⟩⟩
  intro a b
  show G.Adj (φ a) (φ b) ↔ T.Adj a b
  by_cases ha : a = c0 <;> by_cases hb : b = c0
  · subst ha
    subst hb
    simp
  · subst ha
    rw [hφc]
    exact ⟨fun _ => hc0 b hb, fun _ => hNadj _ (hφN b hb)⟩
  · subst hb
    rw [hφc]
    exact ⟨fun _ => (hc0 a ha).symm, fun _ => (hNadj _ (hφN a ha)).symm⟩
  · constructor
    · intro h
      exfalso
      exact htri {v, φ a, φ b} (SimpleGraph.is3Clique_triple_iff.2
        ⟨hNadj _ (hφN a ha), hNadj _ (hφN b hb), h⟩)
    · intro h
      exfalso
      exact htree3 {c0, a, b} (SimpleGraph.is3Clique_triple_iff.2 ⟨hc0 a ha, hc0 b hb, h⟩)
