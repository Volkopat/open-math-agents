import OMAReductions.R_Erdos628_erdos_628_R1_H1_R1
import Mathlib

-- Reduction Erdos628.erdos_628.R1.H1.R1.H3.R1 of step Erdos628.erdos_628.R1.H1.R1.H3
-- Credit: @rickmanelius

/-!
# Erdős 628, the `(2, k - 1)` case for `k ≥ 6`, split by the clique number

The step: a vertex-critical `K_k`-free graph `G` with `χ(G) = k ≥ 6` has a vertex set `s` such
that `G[s]` contains an edge and `G[sᶜ]` needs at least `k - 1` colours. Its clique number
`ω(G)` is at most `k - 1`.

Proved below, with no hypothesis (`clique_case`): the case `ω(G) = k - 1`. Let `t` be a clique on
`k - 1` vertices. If the vertices off `t` span an edge, take `s` to be the complement of `t`:
`G[sᶜ] = G[t]` is complete on `k - 1` vertices. Otherwise the vertices off `t` are independent.
No vertex `w` off `t` is adjacent to all of `t`, since `t` and `w` would form a `K_k`, so `w` has
a non-neighbour `u` in `t`. Colour `t` with `k - 1` distinct colours and give `w` the colour of
`u`. This is a proper `(k - 1)`-colouring of `G`, which is impossible. Vertex-criticality is not
used here.

What is left, by the clique number:
* `H1`: `ω(G) = k - 2` (`G` contains a `K_(k - 2)` but no `K_(k - 1)`);
* `H2`: `ω(G) ≤ k - 3` (`G` contains no `K_(k - 2)`).
-/

namespace OMA.R_Erdos628_erdos_628_R1_H1_R1_H3_R1

open SimpleGraph

/-- The step when the clique number is `k - 2`. -/
def H1 : Prop :=
  ∀ (n k : ℕ) (G : SimpleGraph (Fin n)),
    G.chromaticNumber = (k : ℕ∞) → G.CliqueFree (k - 1) → ¬ G.CliqueFree (k - 2) →
    (∀ v : Fin n, (G.induce ({v}ᶜ : Set (Fin n))).chromaticNumber < (k : ℕ∞)) →
    6 ≤ k →
    ∃ s : Set (Fin n), (G.induce s).chromaticNumber ≥ (2 : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ ((k - 1 : ℕ) : ℕ∞)

/-- The step when the clique number is at most `k - 3`. -/
def H2 : Prop :=
  ∀ (n k : ℕ) (G : SimpleGraph (Fin n)),
    G.chromaticNumber = (k : ℕ∞) → G.CliqueFree (k - 2) →
    (∀ v : Fin n, (G.induce ({v}ᶜ : Set (Fin n))).chromaticNumber < (k : ℕ∞)) →
    6 ≤ k →
    ∃ s : Set (Fin n), (G.induce s).chromaticNumber ≥ (2 : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ ((k - 1 : ℕ) : ℕ∞)

/-- The case `ω(G) = k - 1`: the complement of a `K_(k - 1)` works. -/
theorem clique_case {V : Type*} (G : SimpleGraph V) {k : ℕ}
    (hχ : G.chromaticNumber = (k : ℕ∞)) (hK : G.CliqueFree k) (hQ : ¬ G.CliqueFree (k - 1))
    (hk : 2 ≤ k) :
    ∃ s : Set V, (G.induce s).chromaticNumber ≥ (2 : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ ((k - 1 : ℕ) : ℕ∞) := by
  classical
  unfold CliqueFree at hQ
  push Not at hQ
  obtain ⟨t, ht⟩ := hQ
  rw [isNClique_iff] at ht
  obtain ⟨htc, htcard⟩ := ht
  by_cases hcase : ∃ x y, x ∉ t ∧ y ∉ t ∧ G.Adj x y
  · obtain ⟨x, y, hx, hy, hxy⟩ := hcase
    refine ⟨(↑t : Set V)ᶜ, ?_, ?_⟩
    · exact two_le_chromaticNumber_of_adj (G := G.induce (↑t : Set V)ᶜ)
        (u := ⟨x, by simpa using hx⟩) (v := ⟨y, by simpa using hy⟩) hxy
    · have hmem : ∀ v ∈ t, v ∈ (↑t : Set V)ᶜᶜ := fun v hv => by simpa using hv
      have hnc : ¬ (G.induce (↑t : Set V)ᶜᶜ).Colorable (k - 2) := by
        rintro ⟨c⟩
        let f : t → Fin (k - 2) := fun v => c ⟨v.1, hmem v.1 v.2⟩
        have hf : Function.Injective f := by
          intro a b hab
          by_contra hne
          have hne' : a.1 ≠ b.1 := fun h => hne (Subtype.ext h)
          have hadj : G.Adj a.1 b.1 := htc a.2 b.2 hne'
          exact (c.valid (v := ⟨a.1, hmem a.1 a.2⟩) (w := ⟨b.1, hmem b.1 b.2⟩) hadj) hab
        have hcard := Fintype.card_le_of_injective f hf
        rw [Fintype.card_coe, htcard, Fintype.card_fin] at hcard
        omega
      have hlt : ((k - 2 : ℕ) : ℕ∞) < (G.induce (↑t : Set V)ᶜᶜ).chromaticNumber := by
        rw [← not_le]
        intro h
        exact hnc (chromaticNumber_le_iff_colorable.mp h)
      have h1 := Order.add_one_le_of_lt hlt
      have e : ((k - 2 : ℕ) : ℕ∞) + 1 = ((k - 1 : ℕ) : ℕ∞) := by
        rw [← Nat.cast_succ]
        congr 1
        omega
      rw [ge_iff_le, ← e]
      exact h1
  · exfalso
    have hout : ∀ x y, x ∉ t → y ∉ t → ¬ G.Adj x y :=
      fun x y hx hy hxy => hcase ⟨x, y, hx, hy, hxy⟩
    have hnon : ∀ w, w ∉ t → ∃ u ∈ t, ¬ G.Adj w u := by
      intro w hw
      by_contra hall
      push Not at hall
      apply hK (insert w t)
      rw [isNClique_iff]
      refine ⟨?_, ?_⟩
      · rw [Finset.coe_insert, isClique_insert]
        exact ⟨htc, fun b hb _ => hall b hb⟩
      · rw [Finset.card_insert_of_notMem hw, htcard]
        omega
    choose! u hut hun using hnon
    let e := Finset.equivFinOfCardEq htcard
    have hcol : G.Colorable (k - 1) := by
      refine ⟨Coloring.mk (fun v => if h : v ∈ t then e ⟨v, h⟩ else e ⟨u v, hut v h⟩) ?_⟩
      intro a b hab
      by_cases ha : a ∈ t
      · by_cases hb : b ∈ t
        · rw [dif_pos ha, dif_pos hb]
          intro heq
          have := congrArg Subtype.val (e.injective heq)
          exact G.ne_of_adj hab this
        · rw [dif_pos ha, dif_neg hb]
          intro heq
          have h1 : a = u b := congrArg Subtype.val (e.injective heq)
          exact hun b hb (h1 ▸ hab.symm)
      · by_cases hb : b ∈ t
        · rw [dif_neg ha, dif_pos hb]
          intro heq
          have h1 : u a = b := congrArg Subtype.val (e.injective heq)
          exact hun a ha (h1 ▸ hab)
        · exact absurd hab (hout a b ha hb)
    have h := chromaticNumber_le_iff_colorable.mpr hcol
    rw [hχ] at h
    have := ENat.natCast_le_natCast.mp h
    omega

theorem main : H1 → H2 → OMA.R_Erdos628_erdos_628_R1_H1_R1.H3 := by
  intro h1 h2
  unfold OMA.R_Erdos628_erdos_628_R1_H1_R1.H3
  intro n k G hχ hK hcrit hk
  by_cases hk1 : G.CliqueFree (k - 1)
  · by_cases hk2 : G.CliqueFree (k - 2)
    · exact h2 n k G hχ hk2 hcrit hk
    · exact h1 n k G hχ hk1 hk2 hcrit hk
  · exact clique_case G hχ hK hk1 (by omega)

end OMA.R_Erdos628_erdos_628_R1_H1_R1_H3_R1
