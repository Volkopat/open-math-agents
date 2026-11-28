import FormalConjectures.ErdosProblems.«716»

/-!
# Erdős Problem 716 (Ruzsa–Szemerédi (6,3) theorem)

Every pair of vertices lies in at most two edges of a `(6,3)`-free `3`-uniform hypergraph `H`,
and every triangle of its shadow graph `G` belongs to `H`. Thus deleting edges to destroy all
triangles in `G` removes at least `#H / 2` edges, giving both `#H ≤ n ^ 2` (using `G' = ⊥`) and
`#H ≤ c * n ^ 2` for large `n` via `SimpleGraph.triangle_removal`.
-/

open Filter Asymptotics Finset SimpleGraph

theorem OMA.solution : type_of% @Erdos716.erdos_716 := by
  classical
  rw [isLittleO_iff]
  intro c hc
  set δ := triangleRemovalBound (c / 2)
  have hδ : 0 < δ := triangleRemovalBound_pos (by positivity)
  filter_upwards [eventually_ge_atTop (⌊1 / δ⌋₊ + 7)] with n hn
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity),
    Hypergraph.configurationExtremalNumber, Hypergraph.extremalNumber]
  refine (Nat.cast_le.2 (Finset.sup_le fun H hH ↦ Nat.le_floor ?_)).trans (Nat.floor_le (by positivity))
  simp only [mem_filter, mem_powerset, ContainsSubgraph, not_exists, not_and, not_le] at hH
  have hU : ∀ e ∈ H, #e = 3 := fun e he ↦ (mem_powersetCard.1 (hH.1 he)).2
  have h3 : ∀ a ∈ H, ∀ b ∈ H, ∀ d ∈ H, ∀ u v w,
      u ∈ a → u ∈ b → v ∈ a ∪ b → v ∈ d → w ∈ a ∪ b → w ∈ d → v ≠ w →
      a = b ∨ a = d ∨ b = d := by
    intro a ha b hb d hd u v w hua hub hva hvd hwa hwd hvw
    have := card_union_add_card_inter a b
    have := card_union_add_card_inter (a ∪ b) d
    have : 1 ≤ #(a ∩ b) := card_pos.2 ⟨u, mem_inter.2 ⟨hua, hub⟩⟩
    have : 2 ≤ #((a ∪ b) ∩ d) := card_pair hvw ▸
      card_le_card (by simp [insert_subset_iff, hva, hvd, hwa, hwd])
    have := hU a ha; have := hU b hb; have := hU d hd
    have h6 : #(a ∪ b ∪ d) ≤ 6 := by omega
    by_contra! h
    obtain ⟨S, hTS, hS⟩ := exists_superset_card_eq h6 (by simp; omega)
    have : #({a, b, d} : Finset _) ≤ #{e ∈ H | e ⊆ S} := card_le_card fun e he ↦ by
      simp only [mem_insert, mem_singleton] at he
      rcases he with rfl | rfl | rfl <;> exact mem_filter.2 ⟨‹_›, fun x hx ↦ hTS (by simp [hx])⟩
    have := card_eq_three.2 ⟨a, b, d, h.1, h.2.1, h.2.2, rfl⟩
    have := hH.2 S hS; omega
  let G : SimpleGraph (Fin n) :=
    { Adj x y := x ≠ y ∧ ∃ e ∈ H, x ∈ e ∧ y ∈ e
      symm := ⟨fun _ _ ⟨h, e, he, hx, hy⟩ ↦ ⟨h.symm, e, he, hy, hx⟩⟩
      loopless := ⟨fun _ h ↦ h.1 rfl⟩ }
  have hcl : G.cliqueFinset 3 ⊆ H := by
    intro t ht
    obtain ⟨x, y, z, ⟨hxy, a, ha, hxa, hya⟩, ⟨hxz, b, hb, hxb, hzb⟩, ⟨hyz, d, hd, hyd, hzd⟩, rfl⟩ :=
      is3Clique_iff.1 (mem_cliqueFinset_iff.1 ht)
    have tri : ∀ e ∈ H, x ∈ e → y ∈ e → z ∈ e → ({x, y, z} : Finset (Fin n)) ∈ H := fun e he hx hy hz ↦ by
      have heq : ({x, y, z} : Finset (Fin n)) = e := eq_of_subset_of_card_le
        (by simp [insert_subset_iff, hx, hy, hz])
        (by rw [hU e he, card_eq_three.2 ⟨x, y, z, hxy, hxz, hyz, rfl⟩])
      simpa only [heq] using he
    rcases h3 a ha b hb d hd x y z hxa hxb (mem_union_left _ hya) hyd (mem_union_right _ hzb) hzd hyz
      with rfl | rfl | rfl
    · exact tri a ha hxa hya hzb
    · exact tri a ha hxa hya hzd
    · exact tri b hb hxb hyd hzb
  have hdel : ∀ G' ≤ G, ∀ [DecidableRel G'.Adj], G'.CliqueFree 3 →
      #H ≤ (#G.edgeFinset - #G'.edgeFinset) * 2 := by
    intro G' hle _ hcf
    rw [← card_sdiff_of_subset (edgeFinset_mono hle)]
    simpa using card_mul_le_card_mul (s := H) (t := G.edgeFinset \ G'.edgeFinset)
      (fun e p ↦ p ∈ e.sym2) (m := 1) (n := 2)
      (fun e he ↦ card_pos.2 <| by
        have : ¬ (e : Set (Fin n)).Pairwise G'.Adj := fun hp ↦ hcf e ⟨hp, hU e he⟩
        simp only [Set.Pairwise, mem_coe, not_forall] at this
        obtain ⟨x, hx, y, hy, hxy, hna⟩ := this
        exact ⟨s(x, y), (mem_bipartiteAbove _).2 ⟨mem_sdiff.2
          ⟨mem_edgeFinset.2 ⟨hxy, e, he, hx, hy⟩, by simpa using hna⟩,
          by simp [hx, hy]⟩⟩)
      (fun p hp ↦ by
        induction p using Sym2.ind with | _ x y =>
        have hadj : G.Adj x y := mem_edgeFinset.1 (mem_sdiff.1 hp).1
        have hxy : x ≠ y := hadj.1
        by_contra! hlt
        obtain ⟨a, ha, b, hb, d, hd, hab, had, hbd⟩ := two_lt_card.1 hlt
        simp only [mem_bipartiteBelow, mem_sym2_iff, Sym2.mem_iff, forall_eq_or_imp, forall_eq] at ha hb hd
        rcases h3 a ha.1 b hb.1 d hd.1 x x y ha.2.1 hb.2.1
          (mem_union_left _ ha.2.1) hd.2.1 (mem_union_left _ ha.2.2) hd.2.2 hxy
          with h | h | h <;> contradiction)
  have hHle : #H ≤ n ^ 2 := by
    have h1 : #H ≤ #G.edgeFinset * 2 :=
      (hdel ⊥ bot_le (cliqueFree_bot (by decide))).trans
        (Nat.mul_le_mul_right 2 (Nat.sub_le _ _))
    have h2 : #G.edgeFinset ≤ n.choose 2 := by simpa using G.card_edgeFinset_le_card_choose_two
    have h3 : n.choose 2 * 2 ≤ n ^ 2 := by
      rw [Nat.choose_two_right, sq]
      exact (Nat.div_mul_le_self _ _).trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
    exact h1.trans ((Nat.mul_le_mul_right 2 h2).trans h3)
  obtain ⟨G', hle, _, hlt, hcf⟩ := G.triangle_removal (ε := c / 2) <| by
    rw [Fintype.card_fin]
    have h1 : 1 / δ < (n : ℝ) :=
      (Nat.lt_floor_add_one _).trans_le (by exact_mod_cast (show ⌊1 / δ⌋₊ + 1 ≤ n by omega))
    have h2 : (1 : ℝ) < δ * n := by rwa [div_lt_iff₀ hδ, mul_comm] at h1
    have h3 : (#(G.cliqueFinset 3) : ℝ) ≤ (n : ℝ) ^ 2 := by
      exact_mod_cast (card_le_card hcl).trans hHle
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    change (#(G.cliqueFinset 3) : ℝ) < δ * (n : ℝ) ^ 3
    calc
      _ ≤ (n : ℝ) ^ 2 := h3
      _ = 1 * (n : ℝ) ^ 2 := (one_mul _).symm
      _ < (δ * n) * (n : ℝ) ^ 2 := mul_lt_mul_of_pos_right h2 (pow_pos hnpos 2)
      _ = _ := by ring
  have hbd : (#H : ℝ) ≤ ((#G.edgeFinset : ℝ) - #G'.edgeFinset) * 2 := by
    rw [← Nat.cast_sub (card_le_card (edgeFinset_mono hle))]
    exact_mod_cast hdel G' hle hcf
  simp only [Fintype.card_fin, Nat.cast_pow] at hlt
  linarith
