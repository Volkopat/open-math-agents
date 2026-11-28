import FormalConjectures.ErdosProblems.«1182»

/-! Chvátal: R(K₃, T) = 2n - 1 for every tree T on n vertices.

Upper bound: let C be triangle-free on 2n - 1 vertices. If some vertex has C-degree at least n,
its C-neighbourhood is a clique of size n in Cᶜ, which contains T. Otherwise every vertex has
a Cᶜ-neighbour outside any set of at most n - 1 vertices, and T embeds greedily leaf by leaf
(`OMA.emb`).

Lower bound: on N < 2n - 1 vertices, split the vertices into two blocks of size at most n - 1
(via `Fin N ↪ Fin 2 × Fin (n - 1)`) and let C be the complete bipartite graph between them.
C has no triangle, and a connected copy of T in Cᶜ would sit inside one block. -/

open SimpleGraph

/-- Greedy tree embedding: if every vertex of `H` has a neighbour outside every set of at most
`k` vertices containing it, then every tree on `k + 1` vertices is contained in `H`. -/
lemma OMA.emb {V : Type} (H : SimpleGraph V) (x : V) (k : ℕ)
    (hd : ∀ s : Finset V, s.card ≤ k → ∀ v ∈ s, ∃ w ∉ s, H.Adj v w) :
    ∀ (A : Type) [Fintype A] (G : SimpleGraph A), Fintype.card A = k + 1 → G.IsTree → G ⊑ H := by
  classical
  induction k with
  | zero =>
    intro A _ G hA _
    obtain ⟨y, hy⟩ := Fintype.card_eq_one_iff.mp hA
    exact ⟨⟨⟨fun _ => x, fun h => (h.ne ((hy _).trans (hy _).symm)).elim⟩,
      fun a b _ => (hy a).trans (hy b).symm⟩⟩
  | succ k ih =>
    intro A _ G hA hG
    have := Fintype.one_lt_card_iff_nontrivial.mp (by omega : 1 < Fintype.card A)
    -- remove a leaf `v` with unique neighbour `u`, embed the rest, then place `v` at a fresh
    -- neighbour `w` of the image of `u`
    obtain ⟨v, hv⟩ := hG.exists_vert_degree_one_of_nontrivial
    obtain ⟨u, hu, hU⟩ := degree_eq_one_iff_existsUnique_adj.mp hv
    have hS : Fintype.card ({v}ᶜ : Set A) = k + 1 := by rw [Fintype.card_compl_set]; simp [hA]
    obtain ⟨f⟩ := ih (fun s hs => hd s (by omega)) _ _ hS
      ⟨hG.1.induce_compl_singleton_of_degree_eq_one hv, hG.2.induce _⟩
    obtain ⟨w, hn, hw⟩ := hd (Finset.univ.map f.toEmbedding) (by simp [hS]) (f ⟨u, hu.ne'⟩)
      (Finset.mem_map_of_mem _ (Finset.mem_univ _))
    refine ⟨⟨⟨fun a => if h : a = v then w else f ⟨a, h⟩, fun {a b} hab => ?_⟩, fun a b hab => ?_⟩⟩
    · split_ifs with ha hb hb
      · exact absurd (ha.trans hb.symm) hab.ne
      · subst ha
        obtain rfl := hU b hab
        exact hw.symm
      · subst hb
        obtain rfl := hU a hab.symm
        exact hw
      · exact f.toHom.map_adj hab
    · dsimp at hab
      split_ifs at hab with ha hb hb
      · exact ha.trans hb.symm
      · exact (hn (hab ▸ Finset.mem_map_of_mem _ (Finset.mem_univ _))).elim
      · exact (hn (hab ▸ Finset.mem_map_of_mem _ (Finset.mem_univ _))).elim
      · exact congrArg Subtype.val (f.injective hab)

theorem OMA.solution : type_of% @Erdos1182.erdos_1182.variants.chvatal := by
  classical
  intro n T hT
  obtain ⟨x⟩ := hT.1.2
  have := x.2
  refine IsLeast.csInf_eq ⟨fun C => ?_, fun N hN => ?_⟩
  · by_cases h3 : C.CliqueFree 3
    · right
      by_cases hd : ∀ v, C.degree v < n
      · refine OMA.emb _ ⟨0, by omega⟩ (n - 1) (fun s hs v hv => ?_) _ T (by simp; omega) hT
        obtain ⟨w, h1, h2⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := C.neighborFinset v)
          (t := sᶜ) (by rw [Finset.card_compl, card_neighborFinset_eq_degree]; simp; have := hd v; omega)
        exact ⟨w, by simpa using h1, by simp at h1 h2; exact ⟨fun h => h1 (h ▸ hv), h2⟩⟩
      · push Not at hd
        obtain ⟨v, hv⟩ := hd
        obtain ⟨t, ht, hc⟩ :=
          Finset.exists_subset_card_eq (hv.trans_eq (card_neighborFinset_eq_degree C v).symm)
        exact (IsContained.of_le le_top).trans ((not_cliqueFree_iff_top_isContained n).mp fun h =>
          h t ⟨((isClique_compl C).2 (isIndepSet_neighborSet_of_triangleFree C h3 v)).subset
            (Set.subset_toFinset.1 ht), hc⟩)
    · exact .inl ((not_cliqueFree_iff_top_isContained 3).mp h3)
  · by_contra! h
    have e := (Fin.castLEEmb (by omega : N ≤ 2 * (n - 1))).trans finProdFinEquiv.symm.toEmbedding
    rcases hN ((⊤ : SimpleGraph (Fin 2)).comap fun v => (e v).1) with ⟨⟨f⟩⟩ | ⟨⟨f⟩⟩
    · exact absurd (Fin.le_of_injective (fun i => (e (f i)).1)
        fun i j h => by_contra fun hij => f.toHom.map_adj hij h) (by omega)
    · have k (i j) : (e (f i)).1 = (e (f j)).1 := by
        obtain ⟨w⟩ := hT.1.1 i j
        induction w with
        | nil => rfl
        | cons h _ ih => exact (not_ne_iff.mp (f.toHom.map_adj h).2).trans ih
      have := Fin.le_of_injective (fun i => (e (f i)).2)
        fun i j h => f.injective (e.injective (Prod.ext (k i j) h))
      omega
