import FormalConjectures.ErdosProblems.«151»
import Mathlib

-- Reduction Erdos151.erdos_151.R2 of Erdős Problem 151
-- Credit: @sun-jiao
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Structural Reduction of Erdős Problem 151 (Max-Degree 3, Guarded Blocks, and Clique Expansion)

We strengthen `R1` substantially for **general** graphs `G` on `n` vertices (without assuming
`K₄`-freeness):

1. **Neighborhood bound (`neighborhood_bound`):** For every vertex `v`, the complement `(N_G(v))ᶜ`
   is a clique transversal, immediately resolving all graphs with maximum degree `≥ H n`.
2. **Maximum-degree `≤ 3` theorem (`max_deg_three_bound`):** Every graph `G` with maximum degree
   at most `3` satisfies `cliqueTransversalNumber G ≤ n - H n` unconditionally, even when `G`
   contains `K₄` components. Together with `neighborhood_bound`, this **unconditionally proves
   Erdős Problem 151 for all `n` with `H n ≤ 4` (every `n ≤ 13`, since `R(3, 5) = 14`)**.
3. **Guarded-block strong induction (`delete_block`) and clique-subset expansion
   (`clique_subset_guarded`):** Whenever `A ⊆ B` has `B` nonempty and every big maximal clique
   meeting `A` also meets `B \ A`, deleting `B` gives `τ(G) ≤ τ(G - B) + |B \ A|`. In particular:
   - Taking `A = ∅, B = {v}` eliminates non-jump values where `H (n + 1) ≤ H n`.
   - Taking any clique `K` and proper subset `A ⊂ K` with `B = K ∪ ⋃_{x ∈ A} N_G(x)` guards `A`,
     forcing strong external neighborhood expansion on every clique in any minimal counterexample.

Only graphs at Ramsey jump points with `H (n + 1) ≥ 5`, maximum degree `< H (n + 1)`, no
triangle-free big-clique-hitting subgraph, and resisting guarded-block / clique-expansion
deletions remain, split into `H1` (`H = 5`, i.e. `n + 1 = 14`, `Δ ≤ 4`), `H2` (`K₄`-free for
`H ≥ 6`), and `H3` (`K₄`-containing for `H ≥ 6`).
-/

namespace OMA.R_Erdos151_erdos_151_R2

open Finset SimpleGraph
open scoped Classical

/-- Step 1: The `H = 5` Ramsey jump (`n + 1 = 14`, maximum degree at most `4`). -/
def H1 : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin (n + 1))),
    Erdos151.H (n + 1) = 5 → Erdos151.H n < Erdos151.H (n + 1) →
    (∀ v, (Finset.univ.filter (G.Adj v)).card ≤ 4) →
    (¬ ∃ F : SimpleGraph (Fin (n + 1)), F.CliqueFree 3 ∧
      ∀ s, G.IsBigMaximalClique s → ∃ u ∈ s, ∃ v ∈ s, F.Adj u v) →
    (∀ A B : Finset (Fin (n + 1)), B.Nonempty → A ⊆ B →
      (∀ t, G.IsBigMaximalClique t → (∃ x ∈ t, x ∈ A) → ∃ y ∈ t, y ∈ B \ A) →
      A.card + Erdos151.H (n + 1 - B.card) < 5) →
    cliqueTransversalNumber G ≤ (n + 1) - Erdos151.H (n + 1)

/-- Step 2: The `K₄`-free residual core at Ramsey jump points with `H ≥ 6`. -/
def H2 : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin (n + 1))),
    6 ≤ Erdos151.H (n + 1) → Erdos151.H n < Erdos151.H (n + 1) →
    G.CliqueFree 4 →
    (∀ v, (Finset.univ.filter (G.Adj v)).card < Erdos151.H (n + 1)) →
    (¬ ∃ F : SimpleGraph (Fin (n + 1)), F.CliqueFree 3 ∧
      ∀ s, G.IsBigMaximalClique s → ∃ u ∈ s, ∃ v ∈ s, F.Adj u v) →
    (∀ A B : Finset (Fin (n + 1)), B.Nonempty → A ⊆ B →
      (∀ t, G.IsBigMaximalClique t → (∃ x ∈ t, x ∈ A) → ∃ y ∈ t, y ∈ B \ A) →
      A.card + Erdos151.H (n + 1 - B.card) < Erdos151.H (n + 1)) →
    cliqueTransversalNumber G ≤ (n + 1) - Erdos151.H (n + 1)

/-- Step 3: The `K₄`-containing residual core with forced clique expansion for `H ≥ 6`. -/
def H3 : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin (n + 1))),
    6 ≤ Erdos151.H (n + 1) → Erdos151.H n < Erdos151.H (n + 1) →
    ¬ G.CliqueFree 4 →
    (∀ v, (Finset.univ.filter (G.Adj v)).card < Erdos151.H (n + 1)) →
    (¬ ∃ F : SimpleGraph (Fin (n + 1)), F.CliqueFree 3 ∧
      ∀ s, G.IsBigMaximalClique s → ∃ u ∈ s, ∃ v ∈ s, F.Adj u v) →
    (∀ K A : Finset (Fin (n + 1)), G.IsClique (K : Set (Fin (n + 1))) → A ⊂ K →
      A.card + Erdos151.H (n + 1 -
        (K ∪ A.biUnion (fun x => Finset.univ.filter (G.Adj x))).card) <
        Erdos151.H (n + 1)) →
    cliqueTransversalNumber G ≤ (n + 1) - Erdos151.H (n + 1)

section Proof

lemma H_attained {n : ℕ} (F : SimpleGraph (Fin n)) (hF : F.CliqueFree 3) :
    ∃ s, F.IsNIndepSet (Erdos151.H n) s := by
  let sizes : Set ℕ :=
    {k | ∀ G : SimpleGraph (Fin n), G.CliqueFree 3 → ∃ s, G.IsNIndepSet k s}
  have hnonempty : sizes.Nonempty :=
    ⟨0, fun _ _ => ⟨∅, by simp [SimpleGraph.isNIndepSet_iff]⟩⟩
  have hfinite : sizes.Finite := by
    refine (Set.finite_Iic n).subset ?_
    intro k hk
    obtain ⟨s, hs⟩ := hk F hF
    simpa [hs.card_eq] using Finset.card_le_univ s
  exact (hnonempty.csSup_mem hfinite) F hF

lemma H_le (n : ℕ) : Erdos151.H n ≤ n := by
  obtain ⟨s, hs⟩ := H_attained (⊥ : SimpleGraph (Fin n)) (cliqueFree_bot (by norm_num))
  simpa [hs.card_eq] using Finset.card_le_univ s

/-- Any vertex neighborhood misses every maximal clique, bounding `τ(G)` by `n - deg(v)`. -/
lemma neighborhood_bound {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n)
    (hv : Erdos151.H n ≤ (univ.filter (G.Adj v)).card) :
    cliqueTransversalNumber G ≤ n - Erdos151.H n := by
  let N := univ.filter (G.Adj v)
  have hhit : G.IsCliqueTransversal Nᶜ := by
    intro t ht
    by_contra! h
    have hAdj (w : Fin n) (hw : w ∈ t) : G.Adj v w :=
      (mem_filter.mp (not_not.mp (by simpa only [mem_compl] using h w hw))).2
    have hc : G.IsClique (↑(insert v t) : Set (Fin n)) := by
      rw [coe_insert]
      exact ht.1.1.insert (fun w hw _ => hAdj w hw)
    have hv' : v ∈ t := ht.1.2 hc (subset_insert _ _) (mem_insert_self _ _)
    exact G.irrefl (hAdj v hv')
  refine (csInf_le' (show Nᶜ.card ∈ {k | ∃ T, G.IsCliqueTransversal T ∧ T.card = k}
    from ⟨Nᶜ, hhit, rfl⟩)).trans ?_
  rw [card_compl, Fintype.card_fin]
  exact Nat.sub_le_sub_left hv n

/-- Any triangle-free graph `F` with an edge inside every big maximal clique of `G` yields the bound. -/
lemma bound_of_hitting {n : ℕ} (G F : SimpleGraph (Fin n)) (hF : F.CliqueFree 3)
    (hit : ∀ s, G.IsBigMaximalClique s → ∃ u ∈ s, ∃ v ∈ s, F.Adj u v) :
    cliqueTransversalNumber G ≤ n - Erdos151.H n := by
  obtain ⟨s, hs⟩ := H_attained F hF
  have htransversal : G.IsCliqueTransversal sᶜ := by
    intro t ht
    obtain ⟨u, hu, v, hv, huv⟩ := hit t ht
    by_cases hsu : u ∈ s
    · by_cases hsv : v ∈ s
      · exact (hs.isIndepSet hsu hsv huv.ne huv).elim
      · exact ⟨v, hv, mem_compl.mpr hsv⟩
    · exact ⟨u, hu, mem_compl.mpr hsu⟩
  apply csInf_le'
  exact ⟨sᶜ, htransversal, by rw [card_compl, Fintype.card_fin, hs.card_eq]⟩

lemma pullback_big_clique {m n : ℕ} (G : SimpleGraph (Fin n)) (e : Fin m ↪ Fin n)
    (t : Finset (Fin n)) (ht : G.IsBigMaximalClique t)
    (hr : ∀ x ∈ t, ∃ i, e i = x) :
    (G.comap e).IsBigMaximalClique (t.preimage e e.injective.injOn) := by
  let u := t.preimage e e.injective.injOn
  have heq : u.map e = t := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi, rfl⟩ := mem_map.mp hx
      exact mem_preimage.mp hi
    · intro hx
      obtain ⟨i, rfl⟩ := hr x hx
      exact mem_map.mpr ⟨i, mem_preimage.mpr hx, rfl⟩
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro i hi j hj hij
    exact ht.1.1 (mem_preimage.mp hi) (mem_preimage.mp hj) (e.injective.ne hij)
  · intro w hw huw j hj
    have hc : G.IsClique (↑(w.map e) : Set (Fin n)) := by
      intro x hx y hy hxy
      obtain ⟨i, hi, rfl⟩ := mem_map.mp hx
      obtain ⟨k, hk, rfl⟩ := mem_map.mp hy
      exact hw hi hk (fun h => hxy (congrArg e h))
    have hsub : t ⊆ w.map e := by
      rw [← heq]
      exact map_subset_map.mpr huw
    exact mem_preimage.mpr (ht.1.2 hc hsub (mem_map.mpr ⟨j, hj, rfl⟩))
  · have h := ht.2
    rwa [← heq, card_map] at h

/-- Guarded-block deletion inequality for arbitrary graphs. -/
lemma delete_block {n : ℕ} (G : SimpleGraph (Fin n))
    (A B : Finset (Fin n)) (hAB : A ⊆ B)
    (guarded : ∀ t, G.IsBigMaximalClique t → (∃ x ∈ t, x ∈ A) → ∃ y ∈ t, y ∈ B \ A)
    (e : Fin (n - B.card) ↪ Fin n)
    (cover : ∀ x, x ∉ B → ∃ i, e i = x) :
    G.cliqueTransversalNumber ≤ (G.comap e).cliqueTransversalNumber + (B.card - A.card) := by
  let F := G.comap e
  have hn : {k | ∃ T : Finset (Fin (n - B.card)), F.IsCliqueTransversal T ∧ T.card = k}.Nonempty := by
    refine ⟨univ.card, univ, ?_, rfl⟩
    intro t ht
    obtain ⟨x, _, hx, _, _⟩ := one_lt_card_iff.mp ht.2
    exact ⟨x, hx, mem_univ _⟩
  obtain ⟨T, hT, hsize⟩ := Nat.sInf_mem hn
  change T.card = F.cliqueTransversalNumber at hsize
  let U := T.map e ∪ (B \ A)
  have hU : G.IsCliqueTransversal U := by
    intro t ht
    by_cases hhit : ∃ y ∈ t, y ∈ B \ A
    · obtain ⟨y, hy, hmem⟩ := hhit
      exact ⟨y, hy, mem_union_right _ hmem⟩
    have hout (x) (hx : x ∈ t) : x ∉ B := by
      intro hb
      by_cases ha : x ∈ A
      · exact hhit (guarded t ht ⟨x, hx, ha⟩)
      · exact hhit ⟨x, hx, mem_sdiff.mpr ⟨hb, ha⟩⟩
    have hbig := pullback_big_clique G e t ht (fun x hx => cover x (hout x hx))
    obtain ⟨i, hi, hiT⟩ := hT _ hbig
    exact ⟨e i, mem_preimage.mp hi, mem_union_left _ (mem_map.mpr ⟨i, hiT, rfl⟩)⟩
  calc
    G.cliqueTransversalNumber ≤ U.card := csInf_le' ⟨U, hU, rfl⟩
    _ ≤ (T.map e).card + (B \ A).card := card_union_le _ _
    _ = _ := by rw [card_map, card_sdiff_of_subset hAB, hsize]

/-- Every proper subset `A ⊂ K` of a clique `K` is guarded inside `K ∪ ⋃_{x ∈ A} N_G(x)`. -/
lemma clique_subset_guarded {n : ℕ} (G : SimpleGraph (Fin n))
    (K A : Finset (Fin n)) (hK : G.IsClique (K : Set (Fin n))) (hAK : A ⊂ K) :
    let B := K ∪ A.biUnion (fun x => univ.filter (G.Adj x))
    B.Nonempty ∧ A ⊆ B ∧
      ∀ t, G.IsBigMaximalClique t → (∃ x ∈ t, x ∈ A) → ∃ y ∈ t, y ∈ B \ A := by
  intro B
  obtain ⟨w, hwK, hwA⟩ := exists_of_ssubset hAK
  refine ⟨⟨w, mem_union_left _ hwK⟩, hAK.subset.trans subset_union_left, ?_⟩
  intro t ht ⟨x, hxt, hxA⟩
  have hnotSub : ¬ t ⊆ A := by
    intro htA
    have hw_in_t : w ∈ t := ht.1.2 hK (htA.trans hAK.subset) hwK
    exact hwA (htA hw_in_t)
  obtain ⟨y, hyt, hyA⟩ := not_subset.mp hnotSub
  have hxy : x ≠ y := fun h => hyA (h ▸ hxA)
  have hadj : G.Adj x y := ht.1.1 hxt hyt hxy
  have hyB : y ∈ B :=
    mem_union_right _ (mem_biUnion.mpr ⟨x, hxA, mem_filter.mpr ⟨mem_univ y, hadj⟩⟩)
  exact ⟨y, hyt, mem_sdiff.mpr ⟨hyB, hyA⟩⟩

private lemma no_third {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (T : Finset ι) (E : ι → Finset α)
    (hDegree : ∀ x, (T.filter (fun t => x ∈ E t)).card ≤ 2)
    {t u v : ι} (ht : t ∈ T) (hu : u ∈ T) (hv : v ∈ T)
    (htu : t ≠ u) (htv : t ≠ v) (huv : u ≠ v)
    {x : α} (hxt : x ∈ E t) (hxu : x ∈ E u) (hxv : x ∈ E v) : False := by
  have hSub : ({t, u, v} : Finset ι) ⊆ T.filter (fun t => x ∈ E t) := by
    intro y hy
    simp only [mem_insert, mem_singleton] at hy
    rcases hy with rfl | rfl | rfl
    · exact mem_filter.mpr ⟨ht, hxt⟩
    · exact mem_filter.mpr ⟨hu, hxu⟩
    · exact mem_filter.mpr ⟨hv, hxv⟩
  have hh := (card_le_card hSub).trans (hDegree x)
  simp [htu, htv, huv] at hh

/-- Every 3-uniform hypergraph of maximum vertex degree at most `2` is 2-colorable. -/
private lemma red_blue_hypergraph {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (T : Finset ι) (E : ι → Finset α)
    (hSize : ∀ t ∈ T, (E t).card = 3)
    (hDegree : ∀ x, (T.filter (fun t => x ∈ E t)).card ≤ 2) :
    ∃ R : Finset α, ∀ t ∈ T, (∃ x ∈ E t, x ∈ R) ∧ (∃ y ∈ E t, y ∉ R) := by
  by_cases hT : T.Nonempty
  · obtain ⟨t0, ht0⟩ := hT
    let V := T.biUnion E
    let Good := V.powerset.filter (fun R => ∀ t ∈ T, (E t ∩ R).card ≤ 1)
    have hEmpty : ∅ ∈ Good := by simp [Good]
    obtain ⟨R, hR, hMax⟩ := exists_max_image Good card ⟨∅, hEmpty⟩
    have hRSub : R ⊆ V := mem_powerset.mp (mem_filter.mp hR).1
    have hRGood : ∀ t ∈ T, (E t ∩ R).card ≤ 1 := (mem_filter.mp hR).2
    let U := T.filter (fun t => E t ∩ R = ∅)
    have hUT : U ⊆ T := filter_subset _ _
    have hU0 (t : ι) (ht : t ∈ U) : E t ∩ R = ∅ := (mem_filter.mp ht).2
    have hVx {x : α} {t : ι} (ht : t ∈ T) (hx : x ∈ E t) : x ∈ V :=
      mem_biUnion.mpr ⟨t, ht, hx⟩
    have hNonRed {x : α} {t : ι} (ht : t ∈ U) (hx : x ∈ E t) : x ∉ R := by
      intro hr
      have hmem := mem_inter.mpr ⟨hx, hr⟩
      rw [hU0 t ht] at hmem
      exact notMem_empty _ hmem
    have hNeedsRed {x : α} (hx : x ∈ V) (hxR : x ∉ R) :
        ∃ t ∈ T, t ∉ U ∧ x ∈ E t := by
      by_contra! hf
      have hNew : insert x R ∈ Good := by
        refine mem_filter.mpr ⟨mem_powerset.mpr (insert_subset hx hRSub), ?_⟩
        intro t ht
        by_cases he : x ∈ E t
        · have heq : E t ∩ insert x R = {x} := by
            ext y
            simp only [mem_inter, mem_insert, mem_singleton]
            constructor
            · rintro ⟨hy, rfl | hyR⟩
              · rfl
              · have hh : y ∈ E t ∩ R := mem_inter.mpr ⟨hy, hyR⟩
                rw [hU0 t (by by_contra hn; exact hf t ht hn he)] at hh
                exact (notMem_empty _ hh).elim
            · rintro rfl
              exact ⟨he, Or.inl rfl⟩
          rw [heq, card_singleton]
        · have heq : E t ∩ insert x R = E t ∩ R := by
            ext y
            simp only [mem_inter, mem_insert]
            constructor
            · rintro ⟨hy, rfl | hyR⟩
              · exact (he hy).elim
              · exact ⟨hy, hyR⟩
            · rintro ⟨hy, hyR⟩
              exact ⟨hy, Or.inr hyR⟩
          rw [heq]
          exact hRGood t ht
      have hh := hMax _ hNew
      rw [card_insert_of_notMem hxR] at hh
      omega
    have hUDisjoint : (U : Set ι).PairwiseDisjoint E := by
      intro t ht u hu htu
      apply Finset.disjoint_left.mpr
      intro x hxt hxu
      obtain ⟨v, hv, hvU, hxv⟩ := hNeedsRed (hVx (hUT ht) hxt) (hNonRed ht hxt)
      exact no_third T E hDegree (hUT ht) (hUT hu) hv htu
        (fun he => hvU (he ▸ ht)) (fun he => hvU (he ▸ hu)) hxt hxu hxv
    let key (x : α) : ι :=
      if h : ∃ t ∈ T, t ∉ U ∧ x ∈ E t then h.choose else t0
    have hKey {t : ι} (ht : t ∈ U) {x : α} (hx : x ∈ E t) :
        key x ∈ T ∧ key x ∉ U ∧ x ∈ E (key x) := by
      have h := hNeedsRed (hVx (hUT ht) hx) (hNonRed ht hx)
      simpa only [key, dif_pos h] using h.choose_spec
    have hKeyEq {t u : ι} (ht : t ∈ U) (hu : u ∈ T) (huU : u ∉ U)
        {x : α} (hx : x ∈ E t) (hxu : x ∈ E u) : key x = u := by
      obtain ⟨hk, hkU, hxk⟩ := hKey ht hx
      by_contra hne
      exact no_third T E hDegree (hUT ht) hk hu (fun he => hkU (he ▸ ht))
        (fun he => huU (he ▸ ht)) hne hx hxk hxu
    have hOtherCard {u : ι} (hu : u ∈ T) (huU : u ∉ U) : (E u \ R).card = 2 := by
      have hh := card_sdiff_add_card_inter (E u) R
      have hp : 0 < (E u ∩ R).card := card_pos.mpr
        (nonempty_iff_ne_empty.mpr (fun h => huU (mem_filter.mpr ⟨hu, h⟩)))
      have hh' := hRGood u hu
      rw [hSize u hu] at hh
      omega
    let options (t : U) : Finset ι := (E t.val).image key
    have hHall : ∀ S : Finset U, S.card ≤ (S.biUnion options).card := by
      intro S
      let W := S.biUnion (fun t => E t.val)
      have hWsize : W.card = 3 * S.card := by
        rw [card_biUnion (show (S : Set U).PairwiseDisjoint (fun t => E t.val) from by
          intro t ht u hu hn
          exact hUDisjoint t.property u.property (fun he => hn (Subtype.ext he)))]
        simp [fun t : U => hSize t.val (hUT t.property), mul_comm]
      have hOpts : S.biUnion options = W.image key := by
        ext u
        constructor
        · intro hu
          obtain ⟨t, ht, htu⟩ := mem_biUnion.mp hu
          obtain ⟨x, hx, rfl⟩ := mem_image.mp htu
          exact mem_image.mpr ⟨x, mem_biUnion.mpr ⟨t, ht, hx⟩, rfl⟩
        · intro hu
          obtain ⟨x, hx, rfl⟩ := mem_image.mp hu
          obtain ⟨t, ht, hxt⟩ := mem_biUnion.mp hx
          exact mem_biUnion.mpr ⟨t, ht, mem_image_of_mem key hxt⟩
      have hFiber (u : ι) (hu : u ∈ W.image key) :
          (W.filter (fun x => key x = u)).card ≤ 2 := by
        obtain ⟨x, hx, rfl⟩ := mem_image.mp hu
        obtain ⟨t, _, hxt⟩ := mem_biUnion.mp hx
        have hk := hKey t.property hxt
        rw [← hOtherCard hk.1 hk.2.1]
        apply card_le_card
        intro y hy
        obtain ⟨hy, hey⟩ := mem_filter.mp hy
        obtain ⟨u', _, hyu⟩ := mem_biUnion.mp hy
        exact mem_sdiff.mpr ⟨hey ▸ (hKey u'.property hyu).2.2, hNonRed u'.property hyu⟩
      have hcount : W.card ≤ 2 * (W.image key).card := by
        rw [card_eq_sum_card_fiberwise (fun x hx => mem_image_of_mem key hx)]
        calc
          _ ≤ ∑ _u ∈ W.image key, 2 := sum_le_sum hFiber
          _ = _ := by simp [mul_comm]
      rw [hOpts]
      omega
    obtain ⟨f, hInj, hf⟩ := (all_card_le_biUnion_card_iff_exists_injective options).mp hHall
    let chosen (t : U) := (mem_image.mp (hf t)).choose
    have hChosen (t : U) : chosen t ∈ E t.val ∧ key (chosen t) = f t :=
      (mem_image.mp (hf t)).choose_spec
    let Add := univ.image chosen
    refine ⟨R ∪ Add, ?_⟩
    intro t ht
    have hAtMost : (E t ∩ Add).card ≤ 1 := by
      apply card_le_one.mpr
      intro x hx y hy
      obtain ⟨hxT, hxA⟩ := mem_inter.mp hx
      obtain ⟨hyT, hyA⟩ := mem_inter.mp hy
      obtain ⟨u, _, rfl⟩ := mem_image.mp hxA
      obtain ⟨v, _, rfl⟩ := mem_image.mp hyA
      congr 1
      by_cases htU : t ∈ U
      · have hu : u = ⟨t, htU⟩ := by
          by_contra hn
          exact (Finset.disjoint_left.mp (hUDisjoint u.property htU
            (fun he => hn (Subtype.ext he)))) (hChosen u).1 hxT
        have hv : v = ⟨t, htU⟩ := by
          by_contra hn
          exact (Finset.disjoint_left.mp (hUDisjoint v.property htU
            (fun he => hn (Subtype.ext he)))) (hChosen v).1 hyT
        exact hu.trans hv.symm
      · apply hInj
        exact (hChosen u).2.symm.trans ((hKeyEq u.property ht htU (hChosen u).1 hxT).trans
          ((hKeyEq v.property ht htU (hChosen v).1 hyT).symm.trans (hChosen v).2))
    have hRed : (E t ∩ (R ∪ Add)).card ≤ 2 := by
      rw [inter_union_distrib_left]
      exact (card_union_le _ _).trans (by have := hRGood t ht; omega)
    constructor
    · by_cases htU : t ∈ U
      · let u : U := ⟨t, htU⟩
        exact ⟨chosen u, (hChosen u).1, mem_union_right _ (mem_image_of_mem _ (mem_univ u))⟩
      · obtain ⟨x, hx⟩ := nonempty_iff_ne_empty.mpr (fun h => htU (mem_filter.mpr ⟨ht, h⟩))
        exact ⟨x, (mem_inter.mp hx).1, mem_union_left _ (mem_inter.mp hx).2⟩
    · by_contra! hn
      have he : E t ∩ (R ∪ Add) = E t := inter_eq_left.mpr hn
      rw [he, hSize t ht] at hRed
      omega
  · exact ⟨∅, by simp [not_nonempty_iff_eq_empty.mp hT]⟩

/-- Every graph of maximum degree at most `3` satisfies `τ(G) ≤ n - H n` unconditionally
(including graphs containing `K₄` components). -/
lemma max_deg_three_bound {n : ℕ} (G : SimpleGraph (Fin n))
    (hdeg : ∀ v, (univ.filter (G.Adj v)).card ≤ 3) :
    cliqueTransversalNumber G ≤ n - Erdos151.H n := by
  by_cases hn0 : n = 0
  · subst hn0
    have h0 : cliqueTransversalNumber G ≤ 0 := by
      apply csInf_le'
      refine ⟨∅, ?_, rfl⟩
      intro s hs
      obtain ⟨a, -, -, -⟩ := one_lt_card_iff.mp hs.2
      exact a.elim0
    omega
  have : NeZero n := ⟨hn0⟩
  let Q4 : Finset (Finset (Fin n)) := univ.powerset.filter (fun q => G.IsNClique 4 q)
  let U : Finset (Fin n) := Q4.biUnion id
  have hQ4_eq {q : Finset (Fin n)} (hq : q ∈ Q4) {x : Fin n} (hx : x ∈ q) :
      q.erase x = univ.filter (G.Adj x) ∧ q = insert x (univ.filter (G.Adj x)) := by
    have hqc : G.IsNClique 4 q := (mem_filter.mp hq).2
    have hsub : q.erase x ⊆ univ.filter (G.Adj x) := by
      intro y hy
      obtain ⟨hyx, hyq⟩ := mem_erase.mp hy
      exact mem_filter.mpr ⟨mem_univ y, hqc.1 hx hyq hyx.symm⟩
    have hcard : (q.erase x).card = 3 := by
      rw [card_erase_of_mem hx, hqc.2]
    have heq : q.erase x = univ.filter (G.Adj x) :=
      eq_of_subset_of_card_le hsub (by rw [hcard]; exact hdeg x)
    exact ⟨heq, by rw [← heq, insert_erase hx]⟩
  have hQ4_unique {q₁ q₂ : Finset (Fin n)} (hq₁ : q₁ ∈ Q4) (hq₂ : q₂ ∈ Q4)
      {x : Fin n} (hx₁ : x ∈ q₁) (hx₂ : x ∈ q₂) : q₁ = q₂ :=
    (hQ4_eq hq₁ hx₁).2.trans (hQ4_eq hq₂ hx₂).2.symm
  let T3 : Finset (Finset (Fin n)) :=
    univ.powerset.filter (fun t => G.IsNClique 3 t ∧ Disjoint t U)
  have hT3_deg (x : Fin n) : (T3.filter (fun t => x ∈ t)).card ≤ 2 := by
    by_cases hxU : x ∈ U
    · have hemp : T3.filter (fun t => x ∈ t) = ∅ := by
        ext t
        simp only [mem_filter, notMem_empty, iff_false, not_and]
        intro ht hxt
        exact Finset.disjoint_left.mp (mem_filter.mp ht).2.2 hxt hxU
      simp [hemp]
    · let N := univ.filter (G.Adj x)
      let S := T3.filter (fun t => x ∈ t)
      change S.card ≤ 2
      have hinj : Set.InjOn (fun t : Finset (Fin n) => t.erase x) (S : Set (Finset (Fin n))) := by
        intro t₁ ht₁ t₂ ht₂ heq
        dsimp only at heq
        have hx₁ : x ∈ t₁ := (mem_filter.mp ht₁).2
        have hx₂ : x ∈ t₂ := (mem_filter.mp ht₂).2
        rw [← insert_erase hx₁, ← insert_erase hx₂, heq]
      have himg : S.image (fun t => t.erase x) ⊆ N.powersetCard 2 := by
        intro p hp
        obtain ⟨t, htS, rfl⟩ := mem_image.mp hp
        obtain ⟨htT, hxt⟩ := mem_filter.mp htS
        have htc : G.IsNClique 3 t := (mem_filter.mp htT).2.1
        refine mem_powersetCard.mpr ⟨?_, ?_⟩
        · intro y hy
          obtain ⟨hyx, hyt⟩ := mem_erase.mp hy
          exact mem_filter.mpr ⟨mem_univ y, htc.1 hxt hyt hyx.symm⟩
        · rw [card_erase_of_mem hxt, htc.2]
      have hN3 : N.card ≤ 3 := hdeg x
      by_cases hNle2 : N.card ≤ 2
      · have hpc : (N.powersetCard 2).card ≤ 1 := by
          rw [card_powersetCard]
          interval_cases N.card <;> decide
        exact (card_image_of_injOn hinj).symm ▸ (card_le_card himg).trans hpc |>.trans (by omega)
      · have hNeq3 : N.card = 3 := by omega
        have hpc : (N.powersetCard 2).card = 3 := by
          rw [card_powersetCard, hNeq3]
          decide
        by_contra! hgt
        have hScard_ge : 3 ≤ (S.image (fun t => t.erase x)).card := by
          rw [card_image_of_injOn hinj]
          omega
        have hall : S.image (fun t => t.erase x) = N.powersetCard 2 :=
          eq_of_subset_of_card_le himg (by omega)
        have hNclique : G.IsClique (N : Set (Fin n)) := by
          intro y hy z hz hyz
          have hmem : ({y, z} : Finset (Fin n)) ∈ N.powersetCard 2 := by
            refine mem_powersetCard.mpr ⟨?_, card_pair hyz⟩
            intro w hw
            simp only [mem_insert, mem_singleton] at hw
            rcases hw with rfl | rfl <;> assumption
          rw [← hall] at hmem
          obtain ⟨t, htS, hteq⟩ := mem_image.mp hmem
          have htc : G.IsNClique 3 t := (mem_filter.mp (mem_filter.mp htS).1).2.1
          have hyt : y ∈ t := erase_subset x t (hteq ▸ mem_insert_self y {z})
          have hzt : z ∈ t := erase_subset x t (hteq ▸ mem_insert_of_mem (mem_singleton_self z))
          exact htc.1 hyt hzt hyz
        have hxnotN : x ∉ N := fun hxN => G.irrefl (mem_filter.mp hxN).2
        have hq4 : G.IsNClique 4 (insert x N) := by
          refine ⟨?_, by rw [card_insert_of_notMem hxnotN, hNeq3]⟩
          rw [coe_insert]
          exact hNclique.insert (fun y hy _ => (mem_filter.mp hy).2)
        have hq4_mem : insert x N ∈ Q4 :=
          mem_filter.mpr ⟨mem_powerset.mpr (subset_univ _), hq4⟩
        exact hxU (mem_biUnion.mpr ⟨insert x N, hq4_mem, mem_insert_self x N⟩)
  obtain ⟨RW, hRW⟩ := red_blue_hypergraph T3 id
    (fun t ht => (mem_filter.mp ht).2.1.2) hT3_deg
  let RU : Finset (Fin n) := Q4.image (fun q => if h : q.Nonempty then q.min' h else 0)
  let R : Finset (Fin n) := (RW \ U) ∪ RU
  have hRU_sub : RU ⊆ U := by
    intro x hx
    obtain ⟨q, hq, rfl⟩ := mem_image.mp hx
    have hqc : G.IsNClique 4 q := (mem_filter.mp hq).2
    have hne : q.Nonempty := card_pos.mp (by rw [hqc.2]; omega)
    rw [dif_pos hne]
    exact mem_biUnion.mpr ⟨q, hq, min'_mem q hne⟩
  have hT3_bichrom {t : Finset (Fin n)} (ht : t ∈ T3) :
      (∃ u ∈ t, u ∈ R) ∧ (∃ v ∈ t, v ∉ R) := by
    have hdisj : Disjoint t U := (mem_filter.mp ht).2.2
    obtain ⟨⟨u, hut, huRW⟩, ⟨v, hvt, hvRW⟩⟩ := hRW t ht
    refine ⟨⟨u, hut, mem_union_left _ (mem_sdiff.mpr ⟨huRW, Finset.disjoint_left.mp hdisj hut⟩)⟩,
      ⟨v, hvt, ?_⟩⟩
    intro hvR
    rcases mem_union.mp hvR with hv1 | hv2
    · exact hvRW (mem_sdiff.mp hv1).1
    · exact Finset.disjoint_left.mp hdisj hvt (hRU_sub hv2)
  have hQ4_bichrom {q : Finset (Fin n)} (hq : q ∈ Q4) :
      (∃ u ∈ q, u ∈ R) ∧ (∃ v ∈ q, v ∉ R) := by
    have hqc : G.IsNClique 4 q := (mem_filter.mp hq).2
    have hne : q.Nonempty := card_pos.mp (by rw [hqc.2]; omega)
    let m := q.min' hne
    have hm_q : m ∈ q := min'_mem q hne
    have hm_R : m ∈ R := by
      refine mem_union_right _ (mem_image.mpr ⟨q, hq, ?_⟩)
      simp [m, dif_pos hne]
    have herase_ne : (q.erase m).Nonempty := by
      apply card_pos.mp
      rw [card_erase_of_mem hm_q, hqc.2]
      omega
    obtain ⟨v, hv_er⟩ := herase_ne
    obtain ⟨hvm, hvq⟩ := mem_erase.mp hv_er
    refine ⟨⟨m, hm_q, hm_R⟩, ⟨v, hvq, ?_⟩⟩
    intro hvR
    have hvU : v ∈ U := mem_biUnion.mpr ⟨q, hq, hvq⟩
    rcases mem_union.mp hvR with hv1 | hv2
    · exact (mem_sdiff.mp hv1).2 hvU
    · obtain ⟨q', hq', hv_eq⟩ := mem_image.mp hv2
      have hq'c : G.IsNClique 4 q' := (mem_filter.mp hq').2
      have hne' : q'.Nonempty := card_pos.mp (by rw [hq'c.2]; omega)
      rw [dif_pos hne'] at hv_eq
      have hvq' : v ∈ q' := hv_eq ▸ min'_mem q' hne'
      have hqq' : q' = q := hQ4_unique hq' hq hvq' hvq
      subst hqq'
      exact hvm hv_eq.symm
  let F : SimpleGraph (Fin n) := {
    Adj := fun x y => G.Adj x y ∧ ((x ∈ R ↔ y ∉ R) ∨ ¬ ∃ w, G.Adj x w ∧ G.Adj y w)
    symm := ⟨fun x y h => ⟨h.1.symm, h.2.elim
      (fun hbip => Or.inl ⟨fun hy hx => hbip.mp hx hy, fun hnx => by_contra fun hny => hnx (hbip.mpr hny)⟩)
      (fun hno => Or.inr (fun ⟨w, hwy, hwx⟩ => hno ⟨w, hwx, hwy⟩))⟩⟩
    loopless := ⟨fun x h => G.irrefl h.1⟩
  }
  have hF_free : F.CliqueFree 3 := by
    intro t ht
    obtain ⟨x, y, z, hxy, hxz, hyz, -⟩ := is3Clique_iff.mp ht
    have bxy : x ∈ R ↔ y ∉ R := hxy.2.resolve_right (fun h => h ⟨z, hxz.1, hyz.1⟩)
    have bxz : x ∈ R ↔ z ∉ R := hxz.2.resolve_right (fun h => h ⟨y, hxy.1, hyz.1.symm⟩)
    have byz : y ∈ R ↔ z ∉ R := hyz.2.resolve_right (fun h => h ⟨x, hxy.1.symm, hxz.1.symm⟩)
    by_cases hx : x ∈ R
    · have hy : y ∉ R := bxy.mp hx
      have hz : z ∉ R := bxz.mp hx
      exact hz (by_contra fun hz' => hy (byz.mpr hz'))
    · have hy : y ∈ R := by_contra fun hy' => hx (bxy.mpr hy')
      have hz : z ∈ R := by_contra fun hz' => hx (bxz.mpr hz')
      exact (byz.mp hy) hz
  refine bound_of_hitting G F hF_free ?_
  intro K hK
  obtain ⟨x0, hx0⟩ := card_pos.mp (lt_of_lt_of_le (by decide : 0 < 2) hK.2)
  have hK_le4 : K.card ≤ 4 := by
    have hsub : K.erase x0 ⊆ univ.filter (G.Adj x0) := by
      intro y hy
      obtain ⟨hyx, hyK⟩ := mem_erase.mp hy
      exact mem_filter.mpr ⟨mem_univ y, hK.1.1 hx0 hyK hyx.symm⟩
    have hc := (card_le_card hsub).trans (hdeg x0)
    rw [card_erase_of_mem hx0] at hc
    omega
  have hK_cases : K.card = 2 ∨ K.card = 3 ∨ K.card = 4 := by
    have := hK.2
    omega
  rcases hK_cases with hc2 | hc3 | hc4
  · obtain ⟨u, v, huv, hKeq⟩ := card_eq_two.mp hc2
    have hu : u ∈ K := by simp [hKeq]
    have hv : v ∈ K := by simp [hKeq]
    have hadj : G.Adj u v := hK.1.1 hu hv huv
    have hno : ¬ ∃ w, G.Adj u w ∧ G.Adj v w := by
      rintro ⟨w, hwu, hwv⟩
      have hcl : G.IsClique (↑(insert w K) : Set (Fin n)) := by
        rw [coe_insert]
        apply hK.1.1.insert
        intro z hz _
        have : z = u ∨ z = v := by simpa [hKeq] using hz
        rcases this with rfl | rfl
        · exact hwu.symm
        · exact hwv.symm
      have hwK : w ∈ K := hK.1.2 hcl (subset_insert _ _) (mem_insert_self _ _)
      have : w = u ∨ w = v := by simpa [hKeq] using hwK
      rcases this with rfl | rfl
      · exact G.irrefl hwu
      · exact G.irrefl hwv
    exact ⟨u, hu, v, hv, hadj, Or.inr hno⟩
  · have hdisj : Disjoint K U := by
      rw [Finset.disjoint_left]
      intro x hxK hxU
      obtain ⟨q, hq, hxq⟩ := mem_biUnion.mp hxU
      have hK_sub_q : K ⊆ q := by
        intro y hyK
        by_cases hyx : y = x
        · exact hyx ▸ hxq
        · have hyN : y ∈ univ.filter (G.Adj x) :=
            mem_filter.mpr ⟨mem_univ y, hK.1.1 hxK hyK (fun h => hyx h.symm)⟩
          rw [(hQ4_eq hq hxq).2]
          exact mem_insert_of_mem hyN
      have hqc : G.IsNClique 4 q := (mem_filter.mp hq).2
      have hq_sub_K : q ⊆ K := hK.1.2 hqc.1 hK_sub_q
      have := card_le_card hq_sub_K
      rw [hqc.2, hc3] at this
      omega
    have hKT3 : K ∈ T3 :=
      mem_filter.mpr ⟨mem_powerset.mpr (subset_univ _), ⟨hK.1.1, hc3⟩, hdisj⟩
    obtain ⟨⟨u, huK, huR⟩, ⟨v, hvK, hvR⟩⟩ := hT3_bichrom hKT3
    have huv : u ≠ v := fun h => hvR (h ▸ huR)
    exact ⟨u, huK, v, hvK, hK.1.1 huK hvK huv, Or.inl ⟨fun _ => hvR, fun _ => huR⟩⟩
  · have hKQ4 : K ∈ Q4 :=
      mem_filter.mpr ⟨mem_powerset.mpr (subset_univ _), ⟨hK.1.1, hc4⟩⟩
    obtain ⟨⟨u, huK, huR⟩, ⟨v, hvK, hvR⟩⟩ := hQ4_bichrom hKQ4
    have huv : u ≠ v := fun h => hvR (h ▸ huR)
    exact ⟨u, huK, v, hvK, hK.1.1 huK hvK huv, Or.inl ⟨fun _ => hvR, fun _ => huR⟩⟩

theorem main : H1 → H2 → H3 → type_of% @Erdos151.erdos_151 := by
  intro h1 h2 h3 m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro G
    rcases m with _ | n
    · have : cliqueTransversalNumber G ≤ 0 := by
        apply csInf_le'
        refine ⟨∅, ?_, rfl⟩
        intro s hs
        obtain ⟨a, -, -, -⟩ := one_lt_card_iff.mp hs.2
        exact a.elim0
      omega
    · by_cases hblock : ∃ A B : Finset (Fin (n + 1)), B.Nonempty ∧ A ⊆ B ∧
          (∀ t, G.IsBigMaximalClique t → (∃ x ∈ t, x ∈ A) → ∃ y ∈ t, y ∈ B \ A) ∧
          Erdos151.H (n + 1) ≤ A.card + Erdos151.H (n + 1 - B.card)
      · obtain ⟨A, B, hB, hAB, hg, hgain⟩ := hblock
        have hb : B.card ≤ n + 1 := by simpa using card_le_univ B
        have ha := card_le_card hAB
        have hbpos := card_pos.mpr hB
        let W := Bᶜ
        have hW : Fintype.card (↥W) = n + 1 - B.card := by simp [W]
        let f := Fintype.equivFinOfCardEq hW
        let e := f.symm.toEmbedding.trans (Function.Embedding.subtype (· ∈ W))
        have hcover (x : Fin (n + 1)) (hx : x ∉ B) : ∃ i, e i = x := by
          let z : ↥W := ⟨x, mem_compl.mpr hx⟩
          exact ⟨f z, by simp [e, z]⟩
        have hsmall := ih (n + 1 - B.card) (by omega) (G.comap e)
        have hdelete := delete_block G A B hAB hg e hcover
        have hH := H_le (n + 1 - B.card)
        omega
      have hstrict : ∀ A B : Finset (Fin (n + 1)), B.Nonempty → A ⊆ B →
          (∀ t, G.IsBigMaximalClique t → (∃ x ∈ t, x ∈ A) → ∃ y ∈ t, y ∈ B \ A) →
          A.card + Erdos151.H (n + 1 - B.card) < Erdos151.H (n + 1) := by
        intro A B hb hab hg
        exact lt_of_not_ge (fun h => hblock ⟨A, B, hb, hab, hg, h⟩)
      have hjump : Erdos151.H n < Erdos151.H (n + 1) := by
        have h0 := hstrict ∅ {0} (singleton_nonempty 0) (empty_subset _)
          (fun _ _ ⟨_, _, hx⟩ => (notMem_empty _ hx).elim)
        simpa using h0
      by_cases hlarge : ∃ v, Erdos151.H (n + 1) ≤ (univ.filter (G.Adj v)).card
      · obtain ⟨v, hv⟩ := hlarge
        exact neighborhood_bound G v hv
      have hdeg (v : Fin (n + 1)) : (univ.filter (G.Adj v)).card < Erdos151.H (n + 1) :=
        lt_of_not_ge (fun h => hlarge ⟨v, h⟩)
      by_cases hH4 : Erdos151.H (n + 1) ≤ 4
      · exact max_deg_three_bound G (fun v => by have := hdeg v; omega)
      by_cases hgood : ∃ F : SimpleGraph (Fin (n + 1)), F.CliqueFree 3 ∧
          ∀ s, G.IsBigMaximalClique s → ∃ u ∈ s, ∃ v ∈ s, F.Adj u v
      · obtain ⟨F, hF, hit⟩ := hgood
        exact bound_of_hitting G F hF hit
      by_cases hH5 : Erdos151.H (n + 1) = 5
      · refine h1 n G hH5 hjump (fun v => by have := hdeg v; omega) hgood ?_
        intro A B hb hab hg
        rw [← hH5]
        exact hstrict A B hb hab hg
      have hH6 : 6 ≤ Erdos151.H (n + 1) := by omega
      by_cases hK4 : G.CliqueFree 4
      · exact h2 n G hH6 hjump hK4 hdeg hgood hstrict
      · refine h3 n G hH6 hjump hK4 hdeg hgood ?_
        intro K A hK hAK
        obtain ⟨hBne, hAB, hguard⟩ := clique_subset_guarded G K A hK hAK
        exact hstrict A (K ∪ A.biUnion (fun x => univ.filter (G.Adj x))) hBne hAB hguard

end Proof

end OMA.R_Erdos151_erdos_151_R2
