import FormalConjectures.WrittenOnTheWallII.GraphConjecture17

/-! On a diameter path, each pair at 3i and 3i+1 has a vertex outside a max independent set. -/

open SimpleGraph

theorem OMA.solution : type_of% @WrittenOnTheWallII.GraphConjecture17.conjecture17 := by
  intro V _ _ _ G hc
  classical
  obtain ⟨a, b, hab⟩ := G.exists_dist_eq_diam
  obtain ⟨p, hp⟩ := hc.exists_walk_length_eq_dist a b
  obtain ⟨s, hs⟩ := G.exists_isNIndepSet_indepNum
  let k := (p.length + 2) / 3
  have place (n : ℕ) (hn : n ≤ p.length) : G.dist a (p.getVert n) = n := by
    simpa [Walk.take_length, Nat.min_eq_left hn] using
      (length_eq_dist_of_subwalk hp (p.isSubwalk_take n)).symm
  have pair (i : Fin k) : ∃ v ∉ s, 3 * i.1 ≤ G.dist a v ∧ G.dist a v ≤ 3 * i.1 + 1 := by
    have hn : 3 * i.1 + 1 ≤ p.length := by have := i.2; omega
    have he := p.adj_getVert_succ (by omega : 3 * i.1 < p.length)
    by_cases h0 : p.getVert (3 * i.1) ∈ s
    · refine ⟨p.getVert (3 * i.1 + 1), fun h1 => hs.isIndepSet h0 h1 he.ne he, ?_⟩
      rw [place _ hn]; omega
    · refine ⟨p.getVert (3 * i.1), h0, ?_⟩
      rw [place _ (by omega)]; omega
  choose f fout flo fhi using pair
  have inj : Function.Injective f := fun i j hij => Fin.ext (by
    have := congrArg (G.dist a) hij; have := flo i; have := fhi i; have := flo j; have := fhi j; omega)
  let t : Finset V := Finset.univ.map ⟨f, inj⟩
  have hd : Disjoint s t := Finset.disjoint_left.2 fun v hv ht => by
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp ht; exact fout i hv
  have ht : G.IsIndepSet t := fun u hu v hv huv h => by
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hu
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hv
    have hne : i.1 ≠ j.1 := fun h => huv (congrArg f (Fin.ext h))
    have gap := h.symm.diff_dist_adj (u := a); dsimp at gap
    have := flo i; have := fhi i; have := flo j; have := fhi j; omega
  have hb : (G.induce (↑(s ∪ t) : Set V)).IsBipartite :=
    (induce_isBipartite_iff_exists_coloring G _).2 ⟨fun v => if v ∈ s then 0 else 1, fun v hv w hw h => by
      by_cases hvs : v ∈ s <;> by_cases hws : w ∈ s
      · exact False.elim (hs.isIndepSet hvs hws h.ne h)
      · simp [hvs, hws]
      · simp [hvs, hws]
      · exact False.elim (ht ((Finset.mem_union.mp hv).resolve_left hvs)
          ((Finset.mem_union.mp hw).resolve_left hws) h.ne h)⟩
  have hle : s.card + t.card ≤ G.largestInducedBipartiteSubgraphSize :=
    le_csSup ⟨Fintype.card V, fun _ ⟨z, _, hz⟩ => hz ▸ z.card_le_univ⟩
      ⟨s ∪ t, hb, Finset.card_union_of_disjoint hd⟩
  simp [t, hs.card_eq] at hle
  have hceil : ⌈(G.diam : ℝ) / 3⌉ ≤ (k : ℤ) := by
    apply Int.ceil_le.2
    rw [div_le_iff₀ (by norm_num)]
    norm_cast
    omega
  unfold SimpleGraph.b
  norm_cast
  omega
