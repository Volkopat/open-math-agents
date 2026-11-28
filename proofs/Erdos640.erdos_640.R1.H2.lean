import OMAReductions.R_Erdos640_erdos_640_R1

/-!
# Closing a chromatically rich path in a breadth-first level

This formalizes the local closing step in Raphael Steiner's observation
on Erdős Problem 640 (10 August 2025).
https://www.erdosproblems.com/forum/thread/640

The even return path is built inductively by choosing predecessors on
shortest paths to the root. Both high endpoints lie outside the lower
return path, so the extension preserves simplicity.
-/

open SimpleGraph

namespace OMA.Erdos640BFS

private theorem predecessor {V : Type*} (G : SimpleGraph V) (r u : V) (d : ℕ)
    (hr : G.Reachable r u) (hd : G.dist r u = d + 1) :
    ∃ a, G.Adj u a ∧ G.Reachable r a ∧ G.dist r a = d := by
  obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_dist
  let q := p.reverse
  have hq : q.length = d + 1 := by simpa [q, hp] using hd
  have hnon : ¬q.Nil := by
    intro h
    have hz := h.length_eq_zero
    omega
  have hadj := q.adj_snd hnon
  have hre : G.Reachable r q.snd := q.tail.reachable.symm
  refine ⟨q.snd, hadj, hre, ?_⟩
  have hlo := hadj.symm.reachable.dist_triangle_right r
  rw [SimpleGraph.dist_eq_one_iff_adj.mpr hadj.symm, hd] at hlo
  have hhi := G.dist_le q.tail.reverse
  rw [Walk.length_reverse, Walk.length_tail, hq] at hhi
  omega

/-- Equal-distance endpoints have a simple even return through strictly lower levels.
The nil path handles coincident endpoints when their predecessors coincide. -/
theorem even_return {V : Type*} (G : SimpleGraph V) (r : V) (d : ℕ) {u v : V}
    (hu : G.Reachable r u) (hv : G.Reachable r v)
    (hdu : G.dist r u = d) (hdv : G.dist r v = d) :
    ∃ p : G.Walk u v, p.IsPath ∧ Even p.length ∧
      ∀ x ∈ p.support, x = u ∨ x = v ∨ G.dist r x < d := by
  classical
  induction d generalizing u v with
  | zero =>
    have e := (hu.dist_eq_zero_iff.mp hdu).symm.trans (hv.dist_eq_zero_iff.mp hdv)
    subst v
    exact ⟨.nil, Walk.IsPath.nil, by simp, by simp⟩
  | succ d ih =>
    by_cases huv : u = v
    · subst v
      exact ⟨.nil, Walk.IsPath.nil, by simp, by simp⟩
    obtain ⟨a, hua, hra, hda⟩ := predecessor G r u d hu hdu
    obtain ⟨b, hvb, hrb, hdb⟩ := predecessor G r v d hv hdv
    obtain ⟨p, hp, heven, hlow⟩ := ih hra hrb hda hdb
    have hl (x) (hx : x ∈ p.support) : G.dist r x < d + 1 := by
      rcases hlow x hx with rfl | rfl | hx
      · omega
      · omega
      · omega
    have hnu : u ∉ p.support := fun h => by have := hl u h; omega
    have hnv : v ∉ p.support := fun h => by have := hl v h; omega
    refine ⟨(p.concat hvb.symm).cons hua, ?_, ?_, ?_⟩
    · rw [Walk.isPath_def, Walk.support_cons, Walk.support_concat, List.nodup_cons,
        List.nodup_append']
      refine ⟨by simp [hnu, huv], hp.support_nodup, by simp, ?_⟩
      exact fun x hx hy => hnv ((List.mem_singleton.mp hy) ▸ hx)
    · rcases heven with ⟨k, hk⟩
      refine ⟨k + 1, ?_⟩
      rw [Walk.length_cons, Walk.length_concat]
      omega
    · intro x hx
      simp only [Walk.support_cons, Walk.support_concat, List.mem_cons, List.mem_append,
        List.not_mem_nil, or_false] at hx
      rcases hx with rfl | hx | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inr (hl x hx))
      · exact Or.inr (Or.inl rfl)

private theorem start_not_mem_tail_support {V : Type*} {G : SimpleGraph V} {u v : V}
    {p : G.Walk u v} (hp : p.IsPath) : u ∉ p.support.tail := by
  have hn := hp.support_nodup
  rw [← p.cons_tail_support, List.nodup_cons] at hn
  exact hn.1

/-- Closing an odd path in one level preserves all its vertices. -/
theorem close_layer_path {V : Type*} (G : SimpleGraph V) (r : V) (d : ℕ)
    {u v : {x : V // G.Reachable r x ∧ G.dist r x = d}}
    (p : (G.induce {x | G.Reachable r x ∧ G.dist r x = d}).Walk u v)
    (hp : p.IsPath) (hodd : Odd p.length) :
    ∃ c : G.Walk u.val u.val, c.IsCycle ∧ Odd c.length ∧
      ∀ x ∈ p.support, x.val ∈ c.support := by
  let i : (G.induce {x | G.Reachable r x ∧ G.dist r x = d}) →g G :=
    ⟨Subtype.val, fun hadj => hadj⟩
  let p' := p.map i
  have hp' : p'.IsPath := hp.map (f := i) Subtype.val_injective
  have hodd' : Odd p'.length := by simpa [p'] using hodd
  have huv : u.val ≠ v.val := by
    intro h
    have hn := hp'.nil_iff_eq.mpr h
    simp [hn.length_eq_zero] at hodd'
  obtain ⟨q, hq, hqeven, hqlow⟩ :=
    even_return G r d v.property.1 u.property.1 v.property.2 u.property.2
  refine ⟨p'.append q, ?_, ?_, ?_⟩
  · apply hp'.isCycle_append hq
    · intro x hx hy
      have hxd : G.dist r x = d := by
        have hxp : x ∈ p'.support := List.mem_of_mem_tail hx
        simp only [p', Walk.support_map, List.mem_map] at hxp
        obtain ⟨y, _, hyx⟩ := hxp
        exact hyx ▸ y.property.2
      rcases hqlow x (List.mem_of_mem_tail hy) with h | h | h
      · subst x
        exact start_not_mem_tail_support hq hy
      · subst x
        exact start_not_mem_tail_support hp' hx
      · omega
    · right
      have hpos := Walk.not_nil_iff_lt_length.mp (Walk.not_nil_of_ne (p := q) huv.symm)
      rcases hqeven with ⟨k, hk⟩
      omega
  · rw [Walk.length_append]
    exact hodd'.add_even hqeven
  · intro x hx
    rw [Walk.support_append]
    apply List.mem_append_left
    rw [Walk.support_map]
    exact List.mem_map.mpr ⟨x, hx, rfl⟩

end OMA.Erdos640BFS

namespace OMA.Erdos640OddPath

open SimpleGraph

private theorem colorable_add_vertex {V : Type*} (G : SimpleGraph V) (s : Set V)
    (v : V) {k : ℕ} (h : (G.induce (s \ {v})).Colorable k) :
    (G.induce s).Colorable (k + 1) := by
  classical
  obtain ⟨c⟩ := h
  let color (x : s) : Fin (k + 1) :=
    if hx : x.val = v then Fin.last k
    else (c ⟨x.val, x.property, hx⟩).castSucc
  refine ⟨Coloring.mk color ?_⟩
  intro x y hxy heq
  by_cases hx : x.val = v
  · by_cases hy : y.val = v
    · exact (G.induce s).ne_of_adj hxy (Subtype.ext (hx.trans hy.symm))
    · have hlast : Fin.last k = (c ⟨y.val, y.property, hy⟩).castSucc := by
        simpa [color, hx, hy] using heq
      exact Fin.castSucc_ne_last _ hlast.symm
  · by_cases hy : y.val = v
    · simp [color, hx, hy] at heq
    · have hsame : c ⟨x.val, x.property, hx⟩ = c ⟨y.val, y.property, hy⟩ := by
        simpa [color, hx, hy] using heq
      exact c.valid (v := ⟨x.val, x.property, hx⟩) (w := ⟨y.val, y.property, hy⟩) hxy hsame

private theorem lose_one_color {V : Type*} (G : SimpleGraph V) (s : Set V) (v : V)
    (m : ℕ) (h : ((m + 2 : ℕ) : ℕ∞) ≤ (G.induce s).chromaticNumber) :
    ((m + 1 : ℕ) : ℕ∞) ≤ (G.induce (s \ {v})).chromaticNumber := by
  refine le_chromaticNumber_iff_colorable.mpr ?_
  intro k hk
  have hbound := le_chromaticNumber_iff_colorable.mp h (k + 1)
    (colorable_add_vertex G s v hk)
  omega

theorem odd_path_of_high_chromatic {V : Type*} (G : SimpleGraph V) (m : ℕ)
    {u v : V} (p : G.Walk u v) (hp : p.IsPath)
    (hc : ((m + 2 : ℕ) : ℕ∞) ≤ (G.induce {x | x ∈ p.support}).chromaticNumber) :
    ∃ a b, ∃ q : G.Walk a b, q.IsPath ∧ Odd q.length ∧
      ((m + 1 : ℕ) : ℕ∞) ≤ (G.induce {x | x ∈ q.support}).chromaticNumber := by
  by_cases ho : Odd p.length
  · have hm : ((m + 1 : ℕ) : ℕ∞) ≤ ((m + 2 : ℕ) : ℕ∞) := by exact_mod_cast Nat.le_succ (m + 1)
    exact ⟨u, v, p, hp, ho, hm.trans hc⟩
  · cases p with
    | nil =>
        let s : Set V := {x | x ∈ (SimpleGraph.Walk.nil : G.Walk u u).support}
        have hs : Subsingleton s := ⟨fun x y => Subtype.ext (by
          have hx : x.val = u := by simpa [s] using x.property
          have hy : y.val = u := by simpa [s] using y.property
          exact hx.trans hy.symm)⟩
        have hsmall : (G.induce s).Colorable 1 :=
          chromaticNumber_le_iff_colorable.mp (@chromaticNumber_le_one_of_subsingleton _ (G.induce s) hs)
        have hbound := le_chromaticNumber_iff_colorable.mp hc 1 hsmall
        omega
    | cons hxy q =>
        have hnot : u ∉ q.support := ((Walk.cons_isPath_iff hxy q).mp hp).2
        have hs : ({w | w ∈ (Walk.cons hxy q).support} : Set V) \ {u} =
            {w | w ∈ q.support} := by
          ext w
          change (w ∈ (Walk.cons hxy q).support ∧ w ≠ u) ↔ w ∈ q.support
          simp only [Walk.support_cons, List.mem_cons]
          constructor
          · rintro ⟨heq | hq, hn⟩
            · exact (hn heq).elim
            · exact hq
          · exact fun hq => ⟨Or.inr hq, fun heq => hnot (heq ▸ hq)⟩
        have hchrom := lose_one_color G {w | w ∈ (Walk.cons hxy q).support} u m hc
        rw [hs] at hchrom
        have hodd : Odd q.length := by
          rw [Walk.length_cons, Nat.odd_iff] at ho
          rw [Nat.odd_iff]
          omega
        exact ⟨_, _, q, hp.of_cons, hodd, hchrom⟩

end OMA.Erdos640OddPath

theorem OMA.solution : OMA.R_Erdos640_erdos_640_R1.H2 := by
  intro V G r d m
  dsimp only
  rintro ⟨u, v, p, hp, hchrom⟩
  let S := G.induce {x | G.Reachable r x ∧ G.dist r x = d}
  obtain ⟨a, b, q, hq, hodd, hspan⟩ :=
    OMA.Erdos640OddPath.odd_path_of_high_chromatic S m p hp hchrom
  obtain ⟨c, hcycle, hoddCycle, hsupport⟩ :=
    OMA.Erdos640BFS.close_layer_path G r d q hq hodd
  refine ⟨a.val, c, hcycle, hoddCycle, ?_⟩
  let f : (S.induce {x | x ∈ q.support}) →g (G.induce {x | x ∈ c.support}) :=
    ⟨fun x => ⟨x.val.val, hsupport x.val x.property⟩, fun h => h⟩
  exact hspan.trans (SimpleGraph.chromaticNumber_mono_of_hom f)
