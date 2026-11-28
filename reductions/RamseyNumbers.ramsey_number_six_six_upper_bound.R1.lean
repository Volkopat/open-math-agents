import FormalConjectures.Wikipedia.RamseyNumbers
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic

/-!
# Reduction of `RamseyNumbers.ramsey_number_six_six_upper_bound`

Following J. Mackey (*Combinatorial Remedies*, Ph.D. thesis, University of Hawaii, 1994) and
S. P. Radziszowski (*Small Ramsey Numbers*, Electron. J. Combin., Dynamic Survey DS1), we reduce
the upper bound $R(6, 6) \le 165$ (`IsGraphRamsey 165 6 6`) to three independent pillars:
1. `H1`: **Off-diagonal Ramsey bound $R(5, 6) \le 85$** (`IsGraphRamsey 85 5 6`).
2. `H2`: **Off-diagonal Ramsey bound $R(4, 6) \le 41$** (`IsGraphRamsey 41 4 6`).
3. `H3`: **Extremal 165-vertex exclusion**: no `(6, 6)`-Ramsey graph on `165` vertices has all
   degrees in `[80, 84]` and every monochromatic edge having at most `40` common monochromatic
   neighbors.

Inside `main`, we prove from scratch:
- **One-vertex neighborhood extraction**: if `G` is `CliqueFree 6` and `Gᶜ` is `CliqueFree 6`,
  then for every vertex `v`, the induced subgraph on `G.neighborFinset v` is `(5, 6)`-free, so
  `H1` forces `G.degree v ≤ 84`; applying the same lemma to `Gᶜ` yields `Gᶜ.degree v ≤ 84`, and
  the partition identity `G.degree v + Gᶜ.degree v = 164` forces `80 ≤ G.degree v`.
- **Two-anchor common-neighborhood extraction**: for every adjacent pair `G.Adj u v`, the induced
  subgraph on `G.neighborFinset u ∩ G.neighborFinset v` is `(4, 6)`-free (adding `u` and `v` lifts
  any `4`-clique to a `6`-clique in `G`), so `H2` forces
  `(G.neighborFinset u ∩ G.neighborFinset v).card ≤ 40`; symmetrically for `Gᶜ`.
- Assembly with `H3` closing `IsGraphRamsey 165 6 6`.

Thanks to @MechaNuggan and @AaronRai123 for the two-anchor common-neighborhood restriction and
degree-range analysis.
Credit: @tkaiman
-/

namespace OMA.R_RamseyNumbers_ramsey_number_six_six_upper_bound_R1

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
        have hxy : x ≠ y := fun h => hab (congrArg f h)
        exact ht.1 hx hy hxy
      · intro a ha _
        obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp ha
        exact (mem_neighborFinset G v (f x)).mp (eFin (Fin.castLE hge x)).2
    exact hG (insert v (t.image f)) ⟨hclq, hcard⟩
  have hHc_cf : Hᶜ.CliqueFree l := by
    have emb : H ↪g G := SimpleGraph.Embedding.comap f G
    have embc : Hᶜ ↪g Gᶜ := (SimpleGraph.Embedding.complEquiv (G := H) (H := G)).toFun emb
    exact SimpleGraph.CliqueFree.comap embc.isContained hGc
  exact hR H ⟨hH_cf, hHc_cf⟩

private lemma common_neighbor_card_lt_of_ramsey {n m k l : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj]
    (hG : G.CliqueFree (k + 2)) (hGc : Gᶜ.CliqueFree l)
    (hR : IsGraphRamsey m k l) {u v : Fin n} (huv : G.Adj u v) :
    (G.neighborFinset u ∩ G.neighborFinset v).card < m := by
  by_contra hge
  push Not at hge
  let S := G.neighborFinset u ∩ G.neighborFinset v
  let eFin : Fin S.card ≃ S := S.equivFin.symm
  let f : Fin m ↪ Fin n :=
    (Fin.castLEEmb hge).trans (eFin.toEmbedding.trans (Function.Embedding.subtype _))
  let H : SimpleGraph (Fin m) := G.comap f
  have hH_cf : H.CliqueFree k := by
    intro t ht
    have hmem_u : ∀ x : Fin m, G.Adj u (f x) := fun x =>
      (mem_neighborFinset G u (f x)).mp (Finset.mem_inter.mp (eFin (Fin.castLE hge x)).2).1
    have hmem_v : ∀ x : Fin m, G.Adj v (f x) := fun x =>
      (mem_neighborFinset G v (f x)).mp (Finset.mem_inter.mp (eFin (Fin.castLE hge x)).2).2
    have hnotv : v ∉ t.image f := by
      intro hv
      obtain ⟨x, _, hfx⟩ := Finset.mem_image.mp hv
      exact G.ne_of_adj (hfx ▸ hmem_v x) rfl
    have hnotu : u ∉ insert v (t.image f) := by
      rw [Finset.mem_insert, not_or]
      refine ⟨G.ne_of_adj huv, fun hu => ?_⟩
      obtain ⟨x, _, hfx⟩ := Finset.mem_image.mp hu
      exact G.ne_of_adj (hfx ▸ hmem_u x) rfl
    have hcard : (insert u (insert v (t.image f))).card = k + 2 := by
      rw [Finset.card_insert_of_notMem hnotu, Finset.card_insert_of_notMem hnotv,
        Finset.card_image_of_injective _ f.injective, ht.2]
    have hclq_v : G.IsClique (↑(insert v (t.image f)) : Set (Fin n)) := by
      rw [Finset.coe_insert, isClique_insert]
      refine ⟨?_, ?_⟩
      · intro a ha b hb hab
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hb
        exact ht.1 hx hy (fun h => hab (congrArg f h))
      · intro a ha _
        obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp ha
        exact hmem_v x
    have hclq_uv : G.IsClique (↑(insert u (insert v (t.image f))) : Set (Fin n)) := by
      rw [Finset.coe_insert, isClique_insert]
      refine ⟨hclq_v, ?_⟩
      intro a ha _
      rcases Finset.mem_insert.mp ha with rfl | ha'
      · exact huv
      · obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp ha'
        exact hmem_u x
    exact hG (insert u (insert v (t.image f))) ⟨hclq_uv, hcard⟩
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

/-- **Off-diagonal Ramsey upper bound $R(5, 6) \le 85$** (Angeltveit–McKay / Radziszowski DS1). -/
def H1 : Prop :=
  IsGraphRamsey 85 5 6

/-- **Off-diagonal Ramsey upper bound $R(4, 6) \le 41$** (McKay–Radziszowski). -/
def H2 : Prop :=
  IsGraphRamsey 41 4 6

/-- **Extremal 165-vertex exclusion** (Mackey 1994 / Angeltveit–McKay): no `(6, 6)`-free simple
graph on `165` vertices has all degrees in `[80, 84]` and every edge in `G` and `Gᶜ` having at
most `40` common neighbors in the same color. -/
def H3 : Prop :=
  ∀ (G : SimpleGraph (Fin 165)) [DecidableRel G.Adj],
    (∀ v, 80 ≤ G.degree v ∧ G.degree v ≤ 84) →
    (∀ u v, G.Adj u v → (G.neighborFinset u ∩ G.neighborFinset v).card ≤ 40) →
    (∀ u v, Gᶜ.Adj u v → (Gᶜ.neighborFinset u ∩ Gᶜ.neighborFinset v).card ≤ 40) →
    G.CliqueFree 6 → Gᶜ.CliqueFree 6 → False

theorem main : H1 → H2 → H3 → type_of% @RamseyNumbers.ramsey_number_six_six_upper_bound := by
  classical
  intro h1 h2 h3 G ⟨hG, hGc⟩
  have hGcc : (Gᶜ)ᶜ.CliqueFree 6 := by simpa only [compl_compl] using hG
  have hdeg : ∀ v : Fin 165, 80 ≤ G.degree v ∧ G.degree v ≤ 84 := by
    intro v
    have hhi : G.degree v ≤ 84 := by
      rw [← card_neighborFinset_eq_degree]
      have hlt := neighbor_card_lt_of_ramsey G hG hGc h1 v
      omega
    have hhic : Gᶜ.degree v ≤ 84 := by
      rw [← card_neighborFinset_eq_degree]
      have hlt := neighbor_card_lt_of_ramsey Gᶜ hGc hGcc h1 v
      omega
    have hsum := degree_add_compl_degree G v
    omega
  have hcnG : ∀ u v : Fin 165, G.Adj u v →
      (G.neighborFinset u ∩ G.neighborFinset v).card ≤ 40 := by
    intro u v huv
    have hlt := common_neighbor_card_lt_of_ramsey G hG hGc h2 huv
    omega
  have hcnGc : ∀ u v : Fin 165, Gᶜ.Adj u v →
      (Gᶜ.neighborFinset u ∩ Gᶜ.neighborFinset v).card ≤ 40 := by
    intro u v huv
    have hlt := common_neighbor_card_lt_of_ramsey Gᶜ hGc hGcc h2 huv
    omega
  exact h3 G hdeg hcnG hcnGc hG hGc

end OMA.R_RamseyNumbers_ramsey_number_six_six_upper_bound_R1
