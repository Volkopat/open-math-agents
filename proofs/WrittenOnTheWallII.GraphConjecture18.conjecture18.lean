import FormalConjectures.WrittenOnTheWallII.GraphConjecture18

/-! Formalization of Benny John’s bound. Short geodesics use two nonadjacent
neighbors of a maximum-degree endpoint. Longer geodesics use disjoint pairs
of consecutive positions spaced three layers apart. Credit: @Deldor14. -/

open SimpleGraph

namespace OMA.MaxDistance

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

lemma two_sets {s t : Finset V} (hs : G.IsIndepSet s) (ht : G.IsIndepSet t)
    (hd : Disjoint s t) : s.card + t.card ≤ G.largestInducedBipartiteSubgraphSize := by
  classical
  have hb : (G.induce (↑(s ∪ t) : Set V)).IsBipartite := by
    apply (induce_isBipartite_iff_exists_coloring G _).mpr
    refine ⟨fun v => if v ∈ s then 0 else 1, ?_⟩
    intro v hv w hw h
    by_cases hvs : v ∈ s <;> by_cases hws : w ∈ s
    · exact False.elim (hs hvs hws h.ne h)
    · simp [hvs,hws]
    · simp [hvs,hws]
    · exact False.elim (ht ((Finset.mem_union.mp hv).resolve_left hvs)
        ((Finset.mem_union.mp hw).resolve_left hws) h.ne h)
  unfold largestInducedBipartiteSubgraphSize
  apply le_csSup
  · exact ⟨Fintype.card V, fun _ ⟨z, _, hz⟩ => hz ▸ z.card_le_univ⟩
  · exact ⟨s ∪ t, hb, Finset.card_union_of_disjoint hd⟩

private lemma place {a b : V} (p : G.Walk a b) (hp : p.length = G.dist a b)
    (i : ℕ) (hi : i ≤ p.length) : G.dist a (p.getVert i) = i := by
  have h := length_eq_dist_of_subwalk hp (p.isSubwalk_take i)
  simpa [Walk.take_length, Nat.min_eq_left hi] using h.symm

lemma extra_vertices (s : Finset V) (hs : G.IsIndepSet s) {a b : V}
    (p : G.Walk a b) (hp : p.length = G.dist a b) :
    ∃ t : Finset V, Disjoint s t ∧ G.IsIndepSet t ∧ t.card = (p.length + 2) / 3 := by
  let k := (p.length + 2) / 3
  have pair (i : Fin k) : ∃ v ∉ s, 3*i.val ≤ G.dist a v ∧ G.dist a v ≤ 3*i.val+1 := by
    have hi := i.isLt
    have hn : 3*i.val+1 ≤ p.length := by dsimp [k] at hi; omega
    have he := p.adj_getVert_succ (show 3*i.val < p.length by omega)
    by_cases h : p.getVert (3*i.val) ∈ s
    · exact ⟨_, fun hv => hs h hv he.ne he, by rw [place p hp _ hn]; omega⟩
    · exact ⟨_, h, by rw [place p hp _ (by omega)]; omega⟩
  choose f outside lower upper using pair
  have hinj : Function.Injective f := by
    intro i j h
    have := congrArg (G.dist a) h
    have := lower i
    have := upper i
    have := lower j
    have := upper j
    exact Fin.ext (by omega)
  let e : Fin k ↪ V := ⟨f,hinj⟩
  refine ⟨Finset.univ.map e, Finset.disjoint_left.mpr ?_, ?_, by simp [k]⟩
  · intro v hv ht
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp ht
    exact outside i hv
  · intro u hu v hv huv h
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hu
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hv
    have hne : i.val ≠ j.val := fun hij => huv (congrArg e (Fin.ext hij))
    have gap := h.symm.diff_dist_adj (u := a)
    dsimp [e] at gap
    have := lower i
    have := upper i
    have := lower j
    have := upper j
    omega

variable [DecidableRel G.Adj]

-- A maximum-degree vertex whose component extends beyond its closed neighborhood
-- has two nonadjacent neighbors: otherwise its first neighbor on a geodesic
-- would have strictly larger degree.
private lemma two_neighbors {a b : V} (hc : G.Connected) (ha : G.degree a = G.maxDegree)
    (hab : 2 ≤ G.dist a b) :
    ∃ x y, G.Adj a x ∧ G.Adj a y ∧ x ≠ y ∧ ¬ G.Adj x y := by
  obtain ⟨p, hp⟩ := hc.exists_walk_length_eq_dist a b
  let x := p.getVert 1
  let z := p.getVert 2
  have hx : G.Adj a x := by simpa [x] using p.adj_getVert_succ (show 0 < p.length by omega)
  have hz : G.Adj x z := p.adj_getVert_succ (show 1 < p.length by omega)
  have hd : G.dist a z = 2 := place p hp 2 (by omega)
  by_contra! h
  let C (v : V) := insert v (G.neighborFinset v)
  have sub : C a ⊆ C x := by
    intro w hw
    simp only [C, Finset.mem_insert, mem_neighborFinset] at hw ⊢
    grind [adj_comm]
  have hz' : z ∉ C a := by
    simp only [C, Finset.mem_insert, mem_neighborFinset]
    rintro (he | h')
    · simp [he] at hd
    · rw [dist_eq_one_iff_adj.mpr h'] at hd; omega
  have hlt := Finset.card_lt_card ((Finset.ssubset_iff_of_subset sub).2
    ⟨z, by simp [C,hz], hz'⟩)
  simp [C, ha] at hlt
  exact (Nat.not_lt_of_ge (G.degree_le_maxDegree x)) hlt

private lemma outside_near (s : Finset V) (hs : G.IsIndepSet s) {a b : V}
    (hc : G.Connected) (hd : 0 < G.dist a b) : ∃ w ∉ s, G.dist a w ≤ 1 := by
  by_cases ha : a ∈ s
  · obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist a b
    have h : G.Adj a (p.getVert 1) := by simpa using p.adj_getVert_succ (show 0 < p.length by omega)
    exact ⟨_, fun hw => hs ha hw h.ne h, (dist_eq_one_iff_adj.mpr h).le⟩
  · exact ⟨a, ha, by simp⟩

private lemma two_out (s : Finset V) (hs : G.IsIndepSet s) {x y : V}
    (hx : x ∉ s) (hy : y ∉ s) (hne : x ≠ y) (hxy : ¬ G.Adj x y) :
    s.card + 2 ≤ G.largestInducedBipartiteSubgraphSize := by
  classical
  have ht : G.IsIndepSet ({x,y} : Finset V) := by
    intro a ha b hb hab had
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at ha hb
    grind [adj_comm]
  have hdis : Disjoint s ({x,y} : Finset V) := by simp [Finset.disjoint_left]; grind
  simpa [hne] using two_sets hs ht hdis

private lemma three_out (s : Finset V) (hs : G.IsIndepSet s) {x y z : V}
    (hx : x ∉ s) (hy : y ∉ s) (hz : z ∉ s) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (h₁ : ¬ G.Adj x y) (h₂ : ¬ G.Adj x z) (h₃ : ¬ G.Adj y z) :
    s.card + 3 ≤ G.largestInducedBipartiteSubgraphSize := by
  classical
  have ht : G.IsIndepSet ({x,y,z} : Finset V) := by
    intro a ha b hb hab had
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at ha hb
    grind [adj_comm]
  have hdis : Disjoint s ({x,y,z} : Finset V) := by
    simp [Finset.disjoint_left]; grind
  simpa [hxy,hxz,hyz] using two_sets hs ht hdis

private lemma far {v w : V} (hd : 2 ≤ G.dist v w) : v ≠ w ∧ ¬ G.Adj v w := by
  constructor
  · rintro rfl; simp at hd
  · intro h; rw [dist_eq_one_iff_adj.mpr h] at hd; omega

private lemma endpoint_in (s : Finset V) (hs : G.IsIndepSet s) {a b : V}
    (hc : G.Connected) (ha : G.degree a = G.maxDegree) (has : a ∈ s)
    (hd : 2 ≤ G.dist a b) : s.card + 2 ≤ G.largestInducedBipartiteSubgraphSize ∧
      (5 ≤ G.dist a b → s.card + 3 ≤ G.largestInducedBipartiteSubgraphSize) := by
  obtain ⟨x,y,hx,hy,hne,hnadj⟩ := two_neighbors hc ha hd
  have hxs := fun h => hs has h hx.ne hx
  have hys := fun h => hs has h hy.ne hy
  refine ⟨two_out s hs hxs hys hne hnadj, ?_⟩
  intro hd5
  obtain ⟨z,hzs,hbz⟩ := outside_near s hs (a := b) (b := a) hc (by rw [SimpleGraph.dist_comm]; omega)
  have far' (v : V) (hv : G.Adj a v) : 2 ≤ G.dist v z := by
    have h₁ := hc.dist_triangle (u := a) (v := v) (w := z)
    have h₂ := hc.dist_triangle (u := a) (v := z) (w := b)
    rw [dist_eq_one_iff_adj.mpr hv] at h₁
    rw [SimpleGraph.dist_comm (G := G) (u := b) (v := z)] at hbz
    omega
  exact three_out s hs hxs hys hzs hne (far (far' x hx)).1 (far (far' y hy)).1
    hnadj (far (far' x hx)).2 (far (far' y hy)).2

private lemma small_distance (s : Finset V) (hs : G.IsIndepSet s) {a b : V}
    (hc : G.Connected) (ha : G.degree a = G.maxDegree) (hb : G.degree b = G.maxDegree)
    (hd : 2 ≤ G.dist a b) : s.card + 2 ≤ G.largestInducedBipartiteSubgraphSize ∧
      (5 ≤ G.dist a b → s.card + 3 ≤ G.largestInducedBipartiteSubgraphSize) := by
  by_cases has : a ∈ s
  · exact endpoint_in s hs hc ha has hd
  by_cases hbs : b ∈ s
  · rw [SimpleGraph.dist_comm (G := G) (u := a) (v := b)] at hd ⊢
    exact endpoint_in s hs hc hb hbs hd
  obtain ⟨hab,hnadj⟩ := far hd
  refine ⟨two_out s hs has hbs hab hnadj, ?_⟩
  intro hd5
  obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist a b
  have e := p.adj_getVert_succ (show 2 < p.length by omega)
  have ex : ∃ i, 2 ≤ i ∧ i ≤ 3 ∧ p.getVert i ∉ s := by
    by_cases h : p.getVert 2 ∈ s
    · exact ⟨3, by decide, le_rfl, fun h' => hs h h' e.ne e⟩
    · exact ⟨2, le_rfl, by decide, h⟩
  obtain ⟨i,hi,hi',houts⟩ := ex
  have hf := place p hp i (by omega)
  have htr := hc.dist_triangle (u := a) (v := p.getVert i) (w := b)
  have hf' : 2 ≤ G.dist b (p.getVert i) := by rw [SimpleGraph.dist_comm]; omega
  have hleft : 2 ≤ G.dist a (p.getVert i) := hf.symm ▸ hi
  exact three_out s hs has hbs houts hab (far hleft).1 (far hf').1
    hnadj (far hleft).2 (far hf').2

end OMA.MaxDistance

open OMA.MaxDistance in
theorem OMA.solution : type_of% @WrittenOnTheWallII.GraphConjecture18.conjecture18 := by
  intro V _ _ _ G _ hc
  classical
  let M := Finset.univ.filter fun v : V => G.degree v = G.maxDegree
  obtain ⟨u,hu⟩ := G.exists_maximal_degree_vertex
  have hm : M.Nonempty := ⟨u, by simpa [M] using hu.symm⟩
  obtain ⟨⟨a,b⟩,hab,hmax⟩ := Finset.exists_mem_eq_sup (M ×ˢ M) (hm.product hm)
    (fun p : V × V => G.dist p.1 p.2)
  have ha : G.degree a = G.maxDegree := by simpa [M] using (Finset.mem_product.mp hab).1
  have hb : G.degree b = G.maxDegree := by simpa [M] using (Finset.mem_product.mp hab).2
  have heq : G.distMaxSet {v | G.degree v = G.maxDegree} = G.dist a b := by
    rw [← hmax]
    unfold distMaxSet
    apply congrArg (fun t : Finset (V × V) => t.sup (fun p => G.dist p.1 p.2))
    ext z
    simp [M]
  dsimp only
  rw [heq]
  obtain ⟨s,hs⟩ := G.exists_isNIndepSet_indepNum
  obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist a b
  obtain ⟨t,hd,ht,hcard⟩ := extra_vertices s hs.isIndepSet p hp
  have basic := two_sets hs.isIndepSet ht hd
  rw [hcard,hp] at basic
  suffices h : ∃ k : ℕ, s.card + k ≤ G.largestInducedBipartiteSubgraphSize ∧
      G.dist a b ≤ k*k by
    obtain ⟨k,hk,hk'⟩ := h
    have hceil : ⌈Real.sqrt (G.dist a b : ℝ)⌉ ≤ (k : ℤ) := Int.ceil_le.2 <| by
      apply Real.sqrt_le_iff.mpr
      exact ⟨by positivity, by exact_mod_cast (show G.dist a b ≤ k^2 by simpa [pow_two] using hk')⟩
    rw [hs.card_eq] at hk
    unfold SimpleGraph.b
    norm_cast
    omega
  by_cases h2 : 2 ≤ G.dist a b
  · obtain ⟨two,three⟩ := small_distance s hs.isIndepSet hc ha hb h2
    by_cases h4 : G.dist a b ≤ 4
    · exact ⟨2,two,h4⟩
    by_cases h9 : G.dist a b ≤ 9
    · exact ⟨3,three (by omega),h9⟩
    let k := (G.dist a b + 2)/3
    have hk : 3 ≤ k := by dsimp [k]; omega
    have hk' : G.dist a b ≤ 3*k := by dsimp [k]; omega
    exact ⟨k,basic,hk'.trans (Nat.mul_le_mul_right k hk)⟩
  · exact ⟨_,basic,by rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (show G.dist a b ≤ 1 by omega) with h|h <;> simp [h]⟩
