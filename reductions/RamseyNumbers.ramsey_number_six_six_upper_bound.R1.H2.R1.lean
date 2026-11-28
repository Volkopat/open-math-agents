import OMAReductions.R_RamseyNumbers_ramsey_number_six_six_upper_bound_R1
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic

/-!
# Reduction of `RamseyNumbers.ramsey_number_six_six_upper_bound.R1.H2` ($R(4, 6) \le 41$)

Following G. Kéry (1964), B. D. McKay & S. P. Radziszowski (*$R(4, 5) = 25$*, J. Graph Theory
19 (1995), 309–322; and *Subgraph counting identities and Ramsey numbers*, J. Combin. Theory Ser. B
69 (1997), 193–209), we reduce the upper bound $R(4, 6) \le 41$ (`IsGraphRamsey 41 4 6`) to three
canonical, independent pillars:

1. `H1`: **Off-diagonal Ramsey bound $R(3, 6) \le 18$** (`IsGraphRamsey 18 3 6`, Kéry 1964).
2. `H2`: **Off-diagonal Ramsey bound $R(4, 5) \le 25$** (`IsGraphRamsey 25 4 5`,
   McKay–Radziszowski 1995).
3. `H3`: **Extremal 41-vertex exclusion**: no `(4, 6)`-free simple graph on `41` vertices has all
   degrees in `{16, 17}`, at least one vertex of degree `16`, and every edge having at most `5`
   common neighbors.

Inside `main`, we prove completely from scratch:
- **Neighborhood extraction**: `H1` bounds every `G.degree v ≤ 17` and `H2` bounds every
  `Gᶜ.degree v ≤ 24`; via `G.degree v + Gᶜ.degree v = 40`, every vertex satisfies
  `16 ≤ G.degree v ≤ 17`.
- **Parity / Handshaking deduction**: since `∑ v : Fin 41, G.degree v = 2 * |E(G)|` is even while
  `41 * 17 = 697` is odd, at least one vertex has `G.degree v = 16`.
- **Triangle-free common-neighborhood bound (zero extra hypotheses)**: for any edge `G.Adj u v`,
  the common neighborhood `G.neighborFinset u ∩ G.neighborFinset v` is independent in `G` (any
  internal edge would complete a `K_4` with `u` and `v`), hence forms a clique in `Gᶜ`, so
  `Gᶜ.CliqueFree 6` forces `(G.neighborFinset u ∩ G.neighborFinset v).card ≤ 5`.

Credit: @tkaiman
-/

namespace OMA.R_RamseyNumbers_ramsey_number_six_six_upper_bound_R1_H2_R1

open SimpleGraph RamseyNumbers

private lemma neighbor_card_lt_of_ramsey {n m k l : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj]
    (hG : G.CliqueFree (k + 1)) (hGc : Gᶜ.CliqueFree l)
    (hR : IsGraphRamsey m k l) (v : Fin n) :
    (G.neighborFinset v).card < m := by
  by_contra hge
  push Not at hge
  let S := G.neighborFinset v
  let eFin : Fin S.card ≃ S := S.equivFin.symm
  let f : Fin m ↪ Fin n :=
    (Fin.castLEEmb hge).trans (eFin.toEmbedding.trans (Function.Embedding.subtype _))
  let H : SimpleGraph (Fin m) := G.comap f
  have hH_cf : H.CliqueFree k := by
    intro t ht
    have hnotv : v ∉ t.image f := by
      intro hv
      obtain ⟨x, _, hfx⟩ := Finset.mem_image.mp hv
      have hmem : f x ∈ S := (eFin (Fin.castLE hge x)).2
      rw [hfx, mem_neighborFinset] at hmem
      exact G.ne_of_adj hmem rfl
    have hcard : (insert v (t.image f)).card = k + 1 := by
      rw [Finset.card_insert_of_notMem hnotv, Finset.card_image_of_injective _ f.injective, ht.2]
    have hclq : G.IsClique (↑(insert v (t.image f)) : Set (Fin n)) := by
      rw [Finset.coe_insert, isClique_insert]
      refine ⟨?_, ?_⟩
      · intro a ha b hb hab
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hb
        exact ht.1 hx hy (fun h => hab (congrArg f h))
      · intro a ha _
        obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp ha
        exact (mem_neighborFinset G v (f x)).mp (eFin (Fin.castLE hge x)).2
    exact hG (insert v (t.image f)) ⟨hclq, hcard⟩
  have hHc_cf : Hᶜ.CliqueFree l := by
    have emb : H ↪g G := SimpleGraph.Embedding.comap f G
    have embc : Hᶜ ↪g Gᶜ := (SimpleGraph.Embedding.complEquiv (G := H) (H := G)).toFun emb
    exact SimpleGraph.CliqueFree.comap embc.isContained hGc
  exact hR H ⟨hH_cf, hHc_cf⟩

private lemma degree_add_compl_degree {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] [DecidableRel Gᶜ.Adj] (v : Fin n) :
    G.degree v + Gᶜ.degree v = n - 1 := by
  rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree]
  have hdisj : Disjoint (G.neighborFinset v) (Gᶜ.neighborFinset v) := by
    rw [Finset.disjoint_left]
    intro w h1 h2
    rw [mem_neighborFinset] at h1 h2
    exact h2.2 h1
  have hunion : G.neighborFinset v ∪ Gᶜ.neighborFinset v = Finset.univ.erase v := by
    ext w
    simp only [Finset.mem_union, mem_neighborFinset, Finset.mem_erase, Finset.mem_univ, and_true,
      compl_adj]
    constructor
    · rintro (h | ⟨hne, _⟩)
      · exact (G.ne_of_adj h).symm
      · exact hne.symm
    · intro hne
      by_cases hadj : G.Adj v w
      · exact Or.inl hadj
      · exact Or.inr ⟨hne.symm, hadj⟩
  rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_erase_of_mem (Finset.mem_univ v),
    Finset.card_univ, Fintype.card_fin]

private lemma common_neighbor_card_le_five {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : G.CliqueFree 4) (hGc : Gᶜ.CliqueFree 6) {u v : Fin n} (huv : G.Adj u v) :
    (G.neighborFinset u ∩ G.neighborFinset v).card ≤ 5 := by
  by_contra hgt
  push Not at hgt
  let S := G.neighborFinset u ∩ G.neighborFinset v
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq (show 6 ≤ S.card by dsimp [S]; omega)
  have hTclq : Gᶜ.IsClique (T : Set (Fin n)) := by
    intro a ha b hb hab
    have haS := Finset.mem_inter.mp (hTsub ha)
    have hbS := Finset.mem_inter.mp (hTsub hb)
    have hua : G.Adj u a := (mem_neighborFinset G u a).mp haS.1
    have hva : G.Adj v a := (mem_neighborFinset G v a).mp haS.2
    have hub : G.Adj u b := (mem_neighborFinset G u b).mp hbS.1
    have hvb : G.Adj v b := (mem_neighborFinset G v b).mp hbS.2
    refine ⟨hab, fun hab_adj => ?_⟩
    have h4 : G.IsNClique 4 {u, v, a, b} := by
      refine ⟨?_, ?_⟩
      · intro x hx y hy hxy
        simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
          Set.mem_singleton_iff] at hx hy
        rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl
        · exact (hxy rfl).elim
        · exact huv
        · exact hua
        · exact hub
        · exact huv.symm
        · exact (hxy rfl).elim
        · exact hva
        · exact hvb
        · exact hua.symm
        · exact hva.symm
        · exact (hxy rfl).elim
        · exact hab_adj
        · exact hub.symm
        · exact hvb.symm
        · exact hab_adj.symm
        · exact (hxy rfl).elim
      · have hne_uv : u ≠ v := G.ne_of_adj huv
        have hne_ua : u ≠ a := G.ne_of_adj hua
        have hne_ub : u ≠ b := G.ne_of_adj hub
        have hne_va : v ≠ a := G.ne_of_adj hva
        have hne_vb : v ≠ b := G.ne_of_adj hvb
        rw [Finset.card_insert_of_notMem (by simp [hne_uv, hne_ua, hne_ub]),
          Finset.card_insert_of_notMem (by simp [hne_va, hne_vb]),
          Finset.card_insert_of_notMem (by simp [hab]),
          Finset.card_singleton]
    exact hG {u, v, a, b} h4
  exact hGc T ⟨hTclq, hTcard⟩

/- ### Hypotheses -/

/-- **Off-diagonal Ramsey bound $R(3, 6) \le 18$** (Kéry 1964). -/
def H1 : Prop :=
  IsGraphRamsey 18 3 6

/-- **Off-diagonal Ramsey bound $R(4, 5) \le 25$** (McKay–Radziszowski 1995). -/
def H2 : Prop :=
  IsGraphRamsey 25 4 5

/-- **Extremal 41-vertex exclusion** (McKay–Radziszowski 1997): no `(4, 6)`-free simple graph on
`41` vertices has all degrees in `{16, 17}`, at least one vertex of degree `16`, and every edge
having at most `5` common neighbors. -/
def H3 : Prop :=
  ∀ (G : SimpleGraph (Fin 41)) [DecidableRel G.Adj],
    (∀ v, 16 ≤ G.degree v ∧ G.degree v ≤ 17) →
    (∃ v, G.degree v = 16) →
    (∀ u v, G.Adj u v → (G.neighborFinset u ∩ G.neighborFinset v).card ≤ 5) →
    G.CliqueFree 4 → Gᶜ.CliqueFree 6 → False

/- ### Main Reduction Theorem -/

theorem main : H1 → H2 → H3 → OMA.R_RamseyNumbers_ramsey_number_six_six_upper_bound_R1.H2 := by
  classical
  intro h1 h2 h3
  dsimp only [OMA.R_RamseyNumbers_ramsey_number_six_six_upper_bound_R1.H2]
  intro G ⟨hG, hGc⟩
  have hGcc : (Gᶜ)ᶜ.CliqueFree 4 := by simpa only [compl_compl] using hG
  have hR54 : IsGraphRamsey 25 5 4 := by
    intro H ⟨hH5, hHc4⟩
    exact h2 Hᶜ ⟨hHc4, by simpa only [compl_compl] using hH5⟩
  have hdeg : ∀ v : Fin 41, 16 ≤ G.degree v ∧ G.degree v ≤ 17 := by
    intro v
    have hhi : G.degree v ≤ 17 := by
      rw [← card_neighborFinset_eq_degree]
      have hlt := neighbor_card_lt_of_ramsey G hG hGc h1 v
      omega
    have hhic : Gᶜ.degree v ≤ 24 := by
      rw [← card_neighborFinset_eq_degree]
      have hlt := neighbor_card_lt_of_ramsey Gᶜ hGc hGcc hR54 v
      omega
    have hsum := degree_add_compl_degree G v
    omega
  have hex16 : ∃ v : Fin 41, G.degree v = 16 := by
    by_contra hall
    push Not at hall
    have hall17 : ∀ v : Fin 41, G.degree v = 17 := by
      intro v
      have := hdeg v
      have := hall v
      omega
    have hhand := G.sum_degrees_eq_twice_card_edges
    have hsum17 : ∑ v : Fin 41, G.degree v = 41 * 17 := by
      simp [hall17]
    rw [hsum17] at hhand
    omega
  have hcn : ∀ u v : Fin 41, G.Adj u v → (G.neighborFinset u ∩ G.neighborFinset v).card ≤ 5 :=
    fun u v huv => common_neighbor_card_le_five G hG hGc huv
  exact h3 G hdeg hex16 hcn hG hGc

end OMA.R_RamseyNumbers_ramsey_number_six_six_upper_bound_R1_H2_R1
