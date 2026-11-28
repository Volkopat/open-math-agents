import OMAReductions.R_Erdos628_erdos_628_R1

-- Reduction Erdos628.erdos_628.R1.H1.R1 of step Erdos628.erdos_628.R1.H1
-- Credit: @rickmanelius

/-!
# Erdős 628, step H1 (the case `a = 2`): `k = 3` outright, then `k = 4`, `k = 5` and `k ≥ 6`

The step asks: every vertex-critical `K_k`-free graph `G` on `Fin n` with chromatic number
`k ≥ 3` has a vertex set `s` such that `G[s]` needs at least `2` colours and `G[sᶜ]` needs at
least `k - 1` colours. This is the `(2, k - 1)` case of the Erdős–Lovász Tihany conjecture.

Proved below, with no hypothesis (`case_three`): the case `k = 3`. A triangle-free graph that is
not `2`-colourable has two vertex-disjoint edges (`two_disjoint_edges`): given an edge `uv`, the
colourings that separate `u` (respectively `v`) from all other vertices are not proper, so some edge
avoids `u` and some edge avoids `v`; if neither of them avoids both, they are `vw` and `ux`, and
`w = x` would give a triangle. Taking `s` to be the two ends of one edge, both `G[s]` and `G[sᶜ]`
contain an edge, so each needs at least `2` colours. Vertex-criticality is not needed here.

The remaining cases are left as hypotheses, each the step restricted to one range of `k`:
* `H1`: `k = 4` (the `(2, 3)` case of the Erdős–Lovász Tihany conjecture, reported as settled in
  the literature, without the vertex-critical assumption);
* `H2`: `k = 5` (the `(2, 4)` case, also reported as settled);
* `H3`: `k ≥ 6` (open in general; it is closely related to the double-critical graph conjecture).
-/

namespace OMA.R_Erdos628_erdos_628_R1_H1_R1

open SimpleGraph

/-- The step for `k = 4`. -/
def H1 : Prop :=
  ∀ (n k : ℕ) (G : SimpleGraph (Fin n)),
    G.chromaticNumber = (k : ℕ∞) → G.CliqueFree k →
    (∀ v : Fin n, (G.induce ({v}ᶜ : Set (Fin n))).chromaticNumber < (k : ℕ∞)) →
    k = 4 →
    ∃ s : Set (Fin n), (G.induce s).chromaticNumber ≥ (2 : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ ((k - 1 : ℕ) : ℕ∞)

/-- The step for `k = 5`. -/
def H2 : Prop :=
  ∀ (n k : ℕ) (G : SimpleGraph (Fin n)),
    G.chromaticNumber = (k : ℕ∞) → G.CliqueFree k →
    (∀ v : Fin n, (G.induce ({v}ᶜ : Set (Fin n))).chromaticNumber < (k : ℕ∞)) →
    k = 5 →
    ∃ s : Set (Fin n), (G.induce s).chromaticNumber ≥ (2 : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ ((k - 1 : ℕ) : ℕ∞)

/-- The step for `k ≥ 6`. -/
def H3 : Prop :=
  ∀ (n k : ℕ) (G : SimpleGraph (Fin n)),
    G.chromaticNumber = (k : ℕ∞) → G.CliqueFree k →
    (∀ v : Fin n, (G.induce ({v}ᶜ : Set (Fin n))).chromaticNumber < (k : ℕ∞)) →
    6 ≤ k →
    ∃ s : Set (Fin n), (G.induce s).chromaticNumber ≥ (2 : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ ((k - 1 : ℕ) : ℕ∞)

/-- A triangle-free graph with chromatic number `3` has two vertex-disjoint edges `uv` and `xy`. -/
lemma two_disjoint_edges {n : ℕ} (G : SimpleGraph (Fin n)) (hχ : G.chromaticNumber = 3)
    (hfree : G.CliqueFree 3) :
    ∃ u v x y : Fin n, G.Adj u v ∧ G.Adj x y ∧ x ≠ u ∧ x ≠ v ∧ y ≠ u ∧ y ≠ v := by
  classical
  have hnot2 : ¬ G.Colorable 2 := by
    intro h
    have := h.chromaticNumber_le
    rw [hχ] at this
    norm_num at this
  have hedge : ∃ u v, G.Adj u v := by
    by_contra hno
    push Not at hno
    exact hnot2 ⟨Coloring.mk (fun _ => (0 : Fin 2)) (fun {v w} h => absurd h (hno v w))⟩
  obtain ⟨u, v, huv⟩ := hedge
  -- some edge avoids any given vertex, else separating that vertex would colour `G` with two colours
  have avoid : ∀ w : Fin n, ∃ a b, G.Adj a b ∧ a ≠ w ∧ b ≠ w := by
    intro w
    by_contra hno
    push Not at hno
    apply hnot2
    refine ⟨Coloring.mk (fun z => if z = w then (0 : Fin 2) else 1) ?_⟩
    intro a b hab
    by_cases ha : a = w
    · have hb : b ≠ w := fun hb => hab.ne (ha.trans hb.symm)
      simp [ha, hb]
    · have hb : b = w := hno a b hab ha
      simp [hb, ha]
  obtain ⟨a, b, hab, hau, hbu⟩ := avoid u
  obtain ⟨a', b', hab', hav', hbv'⟩ := avoid v
  by_cases h1 : a ≠ v ∧ b ≠ v
  · exact ⟨u, v, a, b, huv, hab, hau, h1.1, hbu, h1.2⟩
  by_cases h2 : a' ≠ u ∧ b' ≠ u
  · exact ⟨u, v, a', b', huv, hab', h2.1, hav', h2.2, hbv'⟩
  -- the edge avoiding `u` is `vw`, the edge avoiding `v` is `ux`
  obtain ⟨w, hvw, hwu⟩ : ∃ w, G.Adj v w ∧ w ≠ u := by
    rcases not_and_or.mp h1 with h | h
    · push Not at h
      subst h
      exact ⟨b, hab, hbu⟩
    · push Not at h
      subst h
      exact ⟨a, hab.symm, hau⟩
  obtain ⟨x, hux, hxv⟩ : ∃ x, G.Adj u x ∧ x ≠ v := by
    rcases not_and_or.mp h2 with h | h
    · push Not at h
      subst h
      exact ⟨b', hab', hbv'⟩
    · push Not at h
      subst h
      exact ⟨a', hab'.symm, hav'⟩
  by_cases hwx : w = x
  · subst hwx
    exact absurd (is3Clique_triple_iff.mpr ⟨huv, hux, hvw⟩) (hfree {u, v, w})
  · exact ⟨v, w, u, x, hvw, hux, huv.ne, hwu.symm, hxv, fun h => hwx h.symm⟩

/-- The case `k = 3` of the step: split off the two ends of one edge. -/
lemma case_three {n : ℕ} (G : SimpleGraph (Fin n)) (hχ : G.chromaticNumber = 3)
    (hfree : G.CliqueFree 3) :
    ∃ s : Set (Fin n), (G.induce s).chromaticNumber ≥ (2 : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (2 : ℕ∞) := by
  obtain ⟨u, v, x, y, huv, hxy, hxu, hxv, hyu, hyv⟩ := two_disjoint_edges G hχ hfree
  refine ⟨{u, v}, ?_, ?_⟩
  · have hu : u ∈ ({u, v} : Set (Fin n)) := by simp
    have hv : v ∈ ({u, v} : Set (Fin n)) := by simp
    exact two_le_chromaticNumber_of_adj (G := G.induce ({u, v} : Set (Fin n)))
      (u := ⟨u, hu⟩) (v := ⟨v, hv⟩) (by simpa using huv)
  · have hx : x ∈ ({u, v} : Set (Fin n))ᶜ := by simp [hxu, hxv]
    have hy : y ∈ ({u, v} : Set (Fin n))ᶜ := by simp [hyu, hyv]
    exact two_le_chromaticNumber_of_adj (G := G.induce ({u, v} : Set (Fin n))ᶜ)
      (u := ⟨x, hx⟩) (v := ⟨y, hy⟩) (by simpa using hxy)

theorem main : H1 → H2 → H3 → OMA.R_Erdos628_erdos_628_R1.H1 := by
  intro h1 h2 h3
  unfold OMA.R_Erdos628_erdos_628_R1.H1
  intro n k G hχ hfree hcrit hk
  rcases (show k = 3 ∨ k = 4 ∨ k = 5 ∨ 6 ≤ k by omega) with rfl | rfl | rfl | h6
  · obtain ⟨s, hs1, hs2⟩ := case_three G (by simpa using hχ) hfree
    exact ⟨s, hs1, by simpa using hs2⟩
  · exact h1 n 4 G hχ hfree hcrit rfl
  · exact h2 n 5 G hχ hfree hcrit rfl
  · exact h3 n k G hχ hfree hcrit h6

end OMA.R_Erdos628_erdos_628_R1_H1_R1
