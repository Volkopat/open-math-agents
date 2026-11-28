import FormalConjectures.WrittenOnTheWallII.GraphConjecture13

/-! Shorter proof of `WrittenOnTheWallII.GraphConjecture13.conjecture13`. -/

open SimpleGraph Finset

theorem OMA.solution : type_of% @WrittenOnTheWallII.GraphConjecture13.conjecture13 := by
  intro V _ _ _ G hc
  classical
  let vals := univ.image fun v => indepNeighborsCard G v
  have hn : vals.Nonempty := by simp [vals]
  obtain ⟨x, -, hx⟩ := mem_image.mp (vals.max'_mem hn)
  obtain ⟨a, b, hab⟩ := G.exists_dist_eq_diam
  obtain ⟨p, hp⟩ := hc.exists_walk_length_eq_dist a b
  let r := G.dist a x
  let I := (range (p.length + 1)).filter fun i => i + 1 < r ∨ r + 1 < i
  let T := I.image p.getVert
  have pos (i) (hi : i ∈ I) : G.dist a (p.getVert i) = i := by
    have hle : i ≤ p.length := by have := mem_range.mp (mem_filter.mp hi).1; omega
    simpa [Walk.take_length, Nat.min_eq_left hle] using
      (length_eq_dist_of_subwalk hp (p.isSubwalk_take i)).symm
  have gap (y) (hy : y ∈ T) : G.dist a y + 1 < r ∨ r + 1 < G.dist a y := by
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hy; rw [pos _ hi]; exact (mem_filter.mp hi).2
  have hxT : x ∉ T := fun h => by have := gap x h; omega
  have hTcard : T.card = I.card := card_image_of_injOn fun i hi j hj he => by
    simpa only [pos i hi, pos j hj] using congrArg (G.dist a) he
  let bad := (range (p.length + 1)).filter fun i => ¬(i + 1 < r ∨ r + 1 < i)
  have hbad : bad.card ≤ 3 := by
    have h := card_le_card (show bad ⊆ Icc (r - 1) (r + 1) from fun i hi => by
      have := (mem_filter.mp hi).2; exact mem_Icc.mpr (by omega))
    rw [Nat.card_Icc] at h; omega
  have hpart : I.card + bad.card = p.length + 1 := by
    simpa [I, bad] using (range (p.length + 1)).card_filter_add_card_filter_not
      fun i => i + 1 < r ∨ r + 1 < i
  let C := insert x T
  have cgap (v) (hv : v ∈ C) : v = x ∨ G.dist a v + 1 < r ∨ r + 1 < G.dist a v :=
    (mem_insert.mp hv).imp_right (gap v)
  have uniq {v w} (hv : v ∈ C) (hw : w ∈ C) (he : G.dist a v = G.dist a w) : v = w := by
    rcases mem_insert.mp hv with rfl | hv <;> rcases mem_insert.mp hw with rfl | hw
    · rfl
    · have := gap w hw; omega
    · have := gap v hv; omega
    · obtain ⟨i, hi, rfl⟩ := mem_image.mp hv; obtain ⟨j, hj, rfl⟩ := mem_image.mp hw
      rw [pos _ hi, pos _ hj] at he; rw [he]
  obtain ⟨N, hN⟩ := (G.induce (G.neighborSet x)).exists_isNIndepSet_indepNum
  let M : Finset V := N.map (Function.Embedding.subtype _)
  have hM : M.card = G.indepNeighborsCard x := by simpa [M, indepNeighborsCard] using hN.card_eq
  have hadj {v} (hv : v ∈ M) : G.Adj x v := by obtain ⟨y, -, rfl⟩ := mem_map.mp hv; exact y.prop
  have hind : G.IsIndepSet M := fun v hv w hw hne he => by
    obtain ⟨u, hu, rfl⟩ := mem_map.mp hv; obtain ⟨z, hz, rfl⟩ := mem_map.mp hw
    exact hN.isIndepSet hu hz (fun h => hne (congrArg Subtype.val h)) he
  have hdisj : Disjoint C M := disjoint_left.mpr fun v hv hm => by
    have he := hadj hm; have := he.diff_dist_adj (u := a)
    rcases cgap v hv with rfl | h | h
    · exact he.ne rfl
    all_goals omega
  have bnd {v w} (hv : v ∈ M) (hw : w ∈ C) (he : G.Adj v w) : G.dist a w % 2 = r % 2 := by
    have := (hadj hv).diff_dist_adj (u := a); have := he.diff_dist_adj (u := a)
    rcases cgap w hw with rfl | h | h <;> omega
  let col (v : V) : Fin 2 := if v ∈ M then 1 else if G.dist a v % 2 = r % 2 then 0 else 1
  have bip : (G.induce (↑(C ∪ M) : Set V)).IsBipartite :=
    (induce_isBipartite_iff_exists_coloring _ _).mpr ⟨col, fun v hv w hw he => by
      by_cases vm : v ∈ M <;> by_cases wm : w ∈ M
      · exact False.elim (hind vm wm he.ne he)
      · simp [col, vm, wm, bnd vm ((mem_union.mp hw).resolve_right wm) he]
      · simp [col, vm, wm, bnd wm ((mem_union.mp hv).resolve_right vm) he.symm]
      · have neq : G.dist a v ≠ G.dist a w := fun h => he.ne
          (uniq ((mem_union.mp hv).resolve_right vm) ((mem_union.mp hw).resolve_right wm) h)
        have := he.diff_dist_adj (u := a); simp only [col, vm, wm, if_false]; split_ifs <;> omega⟩
  have sz : (C ∪ M).card ≤ G.largestInducedBipartiteSubgraphSize :=
    le_csSup ⟨Fintype.card V, fun _ ⟨s, _, hs⟩ => hs ▸ s.card_le_univ⟩ ⟨_, bip, rfl⟩
  rw [card_union_of_disjoint hdisj, card_insert_of_notMem hxT, hTcard, hM, hx] at sz
  unfold SimpleGraph.b
  rw [sub_le_iff_le_add]
  norm_cast
  change G.diam + vals.max' hn ≤ _
  rw [← hx, ← hM]
  omega
