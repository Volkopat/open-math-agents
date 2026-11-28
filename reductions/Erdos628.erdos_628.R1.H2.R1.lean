import OMAReductions.R_Erdos628_erdos_628_R1
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Sum

/-!
In a coloring of the complement of a clique, a color class with no common
neighbor of the clique can be moved into the clique's palette. A minimum
intersection between b-cliques then gives the large-clique case by exchange.
The recoloring and clique exchange follow the ideas in Longbrake and Tariq,
Lemmas 2.2 and 2.3, https://arxiv.org/html/2406.15164v2.
-/

namespace OMA.Erdos628Recolor

open Finset SimpleGraph
open scoped Classical

private theorem colorable_of_missed_class {V : Type*} (G : SimpleGraph V)
    (s : Finset V) {m : ℕ} (C : (G.induce (s : Set V)ᶜ).Coloring (Fin m)) (j : Fin m)
    (misses : ∀ (v : {x : V // x ∉ s}), C v = j → ∃ u : s, ¬ G.Adj v.val u.val) :
    G.Colorable (s.card + (m - 1)) := by
  classical
  let D := {i : Fin m // i ≠ j}
  let choice (v : {x : V // x ∉ s}) (hv : C v = j) : s := (misses v hv).choose
  have hChoice (v : {x : V // x ∉ s}) (hv : C v = j) : ¬ G.Adj v.val (choice v hv).val :=
    (misses v hv).choose_spec
  let paint (x : V) : s ⊕ D :=
    if hx : x ∈ s then Sum.inl ⟨x, hx⟩ else
      let v : {v : V // v ∉ s} := ⟨x, hx⟩
      if hv : C v = j then Sum.inl (choice v hv) else Sum.inr ⟨C v, hv⟩
  have cross (u v : V) (hu : u ∈ s) (hv : v ∉ s) (hadj : G.Adj u v)
      (heq : paint u = paint v) : False := by
    let z : {z : V // z ∉ s} := ⟨v, hv⟩
    by_cases hz : C z = j
    · have equ : (⟨u, hu⟩ : s) = choice z hz := by simpa [paint, hu, hv, z, hz] using heq
      have hvu : u = (choice z hz).val := congrArg Subtype.val equ
      exact hChoice z hz (hvu ▸ hadj.symm)
    · simp [paint, hu, hv, z, hz] at heq
  let coloring : G.Coloring (s ⊕ D) := Coloring.mk paint (by
    intro u v hadj heq
    by_cases hu : u ∈ s <;> by_cases hv : v ∈ s
    · have equ : (⟨u, hu⟩ : s) = ⟨v, hv⟩ := by simpa [paint, hu, hv] using heq
      exact hadj.ne (congrArg Subtype.val equ)
    · exact cross u v hu hv hadj heq
    · exact cross v u hv hu hadj.symm heq.symm
    · let x : {x : V // x ∉ s} := ⟨u, hu⟩
      let y : {y : V // y ∉ s} := ⟨v, hv⟩
      have hne := C.valid (v := x) (w := y) hadj
      by_cases hx : C x = j <;> by_cases hy : C y = j
      · exact hne (hx.trans hy.symm)
      · simp [paint, hu, hv, x, y, hx, hy] at heq
      · simp [paint, hu, hv, x, y, hx, hy] at heq
      · have pu : paint u = Sum.inr (⟨C x, hx⟩ : D) := by simp [paint, hu, x, hx]
        have pv : paint v = Sum.inr (⟨C y, hy⟩ : D) := by simp [paint, hv, y, hy]
        rw [pu, pv] at heq
        exact hne (congrArg Subtype.val (Sum.inr.inj heq)))
  simpa [D] using coloring.colorable

theorem common_card_ge_of_colorable_compl {V : Type*} [Fintype V] (G : SimpleGraph V)
    (s : Finset V) (m : ℕ)
    (large : ((s.card + (m - 1) : ℕ) : ℕ∞) < G.chromaticNumber)
    (colorable : (G.induce (s : Set V)ᶜ).Colorable m) :
    m ≤ (univ.filter (fun v => ∀ u ∈ s, G.Adj v u)).card := by
  classical
  let common := univ.filter (fun v => ∀ u ∈ s, G.Adj v u)
  let C := colorable.some
  let outside (v : common) : {x : V // x ∉ s} := ⟨v.val, fun hv =>
    G.irrefl ((mem_filter.mp v.property).2 _ hv)⟩
  let color (v : common) : Fin m := C (outside v)
  have hSurj : Function.Surjective color := by
    intro j
    by_contra noCommon
    have misses (v : {x : V // x ∉ s}) (hv : C v = j) : ∃ u : s, ¬ G.Adj v.val u.val := by
      by_contra h
      have adj (u : V) (hu : u ∈ s) : G.Adj v.val u := by
        by_contra hnot
        exact h ⟨⟨u, hu⟩, hnot⟩
      let z : common := ⟨v.val, mem_filter.mpr ⟨mem_univ _, adj⟩⟩
      exact noCommon ⟨z, hv⟩
    exact large.not_ge (colorable_of_missed_class G s C j misses).chromaticNumber_le
  simpa only [Fintype.card_fin, Fintype.card_coe] using Fintype.card_le_of_surjective color hSurj

theorem split_of_small_common {V : Type*} [Fintype V] (G : SimpleGraph V)
    (k a b : ℕ) (chrom : G.chromaticNumber = (k : ℕ∞)) (hb : 2 ≤ b) (hab : a + b = k + 1)
    (s : Finset V) (clique : G.IsNClique a s)
    (few : (univ.filter (fun v => ∀ u ∈ s, G.Adj v u)).card < b - 1) :
    ∃ t : Set V, (a : ℕ∞) ≤ (G.induce t).chromaticNumber ∧
      (b : ℕ∞) ≤ (G.induce tᶜ).chromaticNumber := by
  refine ⟨(s : Set V), ?_, ?_⟩
  · rw [induce_eq_top.mpr clique.isClique, chromaticNumber_top]
    change (a : ℕ∞) ≤ (Fintype.card s : ℕ)
    simp only [Fintype.card_coe, clique.card_eq, le_refl]
  · by_contra! inadequate
    let m := b - 1
    have hb' : b = m + 1 := by dsimp [m]; omega
    have C : (G.induce (s : Set V)ᶜ).Colorable m := by
      apply chromaticNumber_le_iff_colorable.mp
      apply ENat.lt_natCast_add_one_iff.mp
      rw [← Nat.cast_one, ← Nat.cast_add, ← hb']
      exact inadequate
    have hl : ((s.card + ((b - 1) - 1) : ℕ) : ℕ∞) < G.chromaticNumber := by
      rw [chrom, ENat.natCast_lt_natCast, clique.card_eq]
      omega
    exact few.not_ge (common_card_ge_of_colorable_compl G s (b - 1) hl C)

end OMA.Erdos628Recolor

namespace OMA.Erdos628CliqueExchange

open Finset SimpleGraph
open scoped Classical

private theorem induce_clique_chromatic {V : Type*} [Fintype V]
    (G : SimpleGraph V) (L : Finset V) (hL : G.IsClique L) :
    (L.card : ℕ∞) ≤ (G.induce (L : Set V)).chromaticNumber := by
  apply SimpleGraph.le_chromaticNumber_of_pairwise_adj
    (ι := (L : Set V)) (by simp [Nat.card_eq_fintype_card]) id
  intro u v huv
  exact hL u.property v.property (fun he => huv (Subtype.ext he))

private theorem clique_sdiff_card_le_of_colorable {V : Type*} [Fintype V]
    (G : SimpleGraph V) (X L : Finset V) {m : ℕ} (hX : G.IsClique X)
    (hcolor : (G.induce ((L : Set V)ᶜ)).Colorable m) :
    (X \ L).card ≤ m := by
  let f : (X \ L : Finset V) → ((L : Set V)ᶜ : Set V) :=
    fun u => ⟨u.val, (mem_sdiff.mp u.property).2⟩
  have hadj : Pairwise fun u v => (G.induce ((L : Set V)ᶜ)).Adj (f u) (f v) := by
    intro u v huv
    exact hX (mem_sdiff.mp u.property).1 (mem_sdiff.mp v.property).1
      (fun he => huv (Subtype.ext he))
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using
    hcolor.card_le_of_pairwise_adj f hadj

/-- If the larger requested part fits in a clique, there is a Tihany partition.
The only input beyond the chromatic and clique conditions is the bound from
recoloring one color class into the vertices of a removed finite set. -/
theorem split_of_large_clique {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hcommon : ∀ (s : Finset V) (m : ℕ),
      ((s.card + (m - 1) : ℕ) : ℕ∞) < G.chromaticNumber →
      (G.induce ((s : Set V)ᶜ)).Colorable m →
      m ≤ ((Finset.univ : Finset V).filter (fun v => ∀ u ∈ s, G.Adj v u)).card)
    {a b k : ℕ} (ha : 3 ≤ a) (hab : a ≤ b) (hk : a + b = k + 1)
    (hχ : G.chromaticNumber = (k : ℕ∞)) (hfree : G.CliqueFree k)
    {X : Finset V} (hX : G.IsNClique b X) :
    ∃ s : Set V, (a : ℕ∞) ≤ (G.induce s).chromaticNumber ∧
      (b : ℕ∞) ≤ (G.induce sᶜ).chromaticNumber := by
  classical
  by_contra hsplit
  obtain ⟨L, hL', hmin⟩ := (G.cliqueFinset b).exists_min_image
    (fun T => (T ∩ X).card) ⟨X, mem_cliqueFinset_iff.mpr hX⟩
  have hL : G.IsNClique b L := mem_cliqueFinset_iff.mp hL'
  have hLχ : (b : ℕ∞) ≤ (G.induce (L : Set V)).chromaticNumber := by
    simpa only [hL.card_eq] using induce_clique_chromatic G L hL.isClique
  have hcomp : (G.induce ((L : Set V)ᶜ)).chromaticNumber < (a : ℕ∞) := by
    apply lt_of_not_ge
    intro h
    refine hsplit ⟨(L : Set V)ᶜ, h, ?_⟩
    rw [show ((L : Set V)ᶜ)ᶜ = (L : Set V) from compl_compl _]
    exact hLχ
  let m := a - 1
  have ha' : a = m + 1 := by dsimp [m]; omega
  have hcolor : (G.induce ((L : Set V)ᶜ)).Colorable m := by
    apply chromaticNumber_le_iff_colorable.mp
    apply ENat.lt_natCast_add_one_iff.mp
    rw [← Nat.cast_one, ← Nat.cast_add, ← ha']
    exact hcomp
  have hdiff : (X \ L).card ≤ m := clique_sdiff_card_le_of_colorable G X L hX.isClique hcolor
  let N := (Finset.univ : Finset V).filter (fun v => ∀ u ∈ L, G.Adj v u)
  have hcardN : m ≤ N.card := by
    refine hcommon L m ?_ hcolor
    rw [hχ, ENat.natCast_lt_natCast, hL.card_eq]
    dsimp [m]
    omega
  have hlinks (v : V) (hv : v ∈ N) (u : V) (hu : u ∈ L) : G.Adj v u :=
    (mem_filter.mp hv).2 u hu
  have hout (v : V) (hv : v ∈ N) : v ∉ L := fun h => G.irrefl (hlinks v hv v h)
  have hNX : ¬ N ⊆ X := by
    intro hNX
    have hNcl : G.IsClique N := hX.isClique.subset (Finset.coe_subset.mpr hNX)
    have hunion : G.IsClique (L ∪ N : Finset V) := by
      intro u hu v hv huv
      obtain hu | hu := mem_union.mp (mem_coe.mp hu)
      · obtain hv | hv := mem_union.mp (mem_coe.mp hv)
        · exact hL.isClique hu hv huv
        · exact (hlinks v hv u hu).symm
      · obtain hv | hv := mem_union.mp (mem_coe.mp hv)
        · exact hlinks u hu v hv
        · exact hNcl hu hv huv
    have hdisj : Disjoint L N := disjoint_left.mpr fun v hv hv' => hout v hv' hv
    have hk' : k ≤ (L ∪ N).card := by
      rw [card_union_of_disjoint hdisj, hL.card_eq]
      dsimp [m] at hcardN
      omega
    obtain ⟨T, hT, hsize⟩ := exists_subset_card_eq hk'
    exact hfree T ⟨hunion.subset (Finset.coe_subset.mpr hT), hsize⟩
  obtain ⟨w, hwN, hwX⟩ := Finset.not_subset.mp hNX
  have hinter : (L ∩ X).Nonempty := by
    have hsum := card_sdiff_add_card_inter X L
    rw [hX.card_eq] at hsum
    apply card_pos.mp
    rw [inter_comm]
    dsimp [m] at hdiff
    omega
  obtain ⟨v, hv⟩ := hinter
  have hvL := (mem_inter.mp hv).1
  let L' := insert w (L.erase v)
  have hL'clique : G.IsClique L' := by
    have hsub : G.IsClique (L.erase v : Finset V) :=
      hL.isClique.subset (Finset.coe_subset.mpr (erase_subset v L))
    change G.IsClique ((insert w (L.erase v) : Finset V) : Set V)
    rw [Finset.coe_insert]
    exact hsub.insert (fun u hu _ => hlinks w hwN u (mem_of_mem_erase hu))
  have hL'card : L'.card = b := by
    have hn : w ∉ L.erase v := fun hw => hout w hwN (mem_of_mem_erase hw)
    change (insert w (L.erase v)).card = b
    rw [card_insert_of_notMem hn, card_erase_of_mem hvL, hL.card_eq]
    omega
  have hL'valid : L' ∈ G.cliqueFinset b := mem_cliqueFinset_iff.mpr ⟨hL'clique, hL'card⟩
  have hnewInter : L' ∩ X = (L ∩ X).erase v := by
    change insert w (L.erase v) ∩ X = (L ∩ X).erase v
    rw [insert_inter_of_notMem hwX]
    ext u
    simp only [mem_inter, mem_erase]
    tauto
  have hlt : (L' ∩ X).card < (L ∩ X).card := by
    rw [hnewInter, card_erase_of_mem hv]
    have hp : 0 < (L ∩ X).card := card_pos.mpr ⟨v, hv⟩
    omega
  exact (not_lt_of_ge (hmin L' hL'valid)) hlt

end OMA.Erdos628CliqueExchange

namespace OMA.R_Erdos628_erdos_628_R1_H2_R1

open SimpleGraph Finset
open scoped Classical

/-- The remaining case with an a-clique and many common neighbors. -/
def H1 : Prop := ∀ (n k : ℕ) (G : SimpleGraph (Fin n)),
    G.chromaticNumber = (k : ℕ∞) → G.CliqueFree k →
    (∀ v : Fin n, (G.induce ({v}ᶜ : Set (Fin n))).chromaticNumber < (k : ℕ∞)) →
    ∀ a b : ℕ, 3 ≤ a → a ≤ b → a + b = k + 1 →
    G.CliqueFree b → (¬ G.CliqueFree a) →
    (∀ s : Finset (Fin n), G.IsNClique a s →
      b - 1 ≤ (univ.filter (fun v => ∀ u ∈ s, G.Adj v u)).card) →
    ∃ s : Set (Fin n), (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)

/-- The remaining case with no a-clique. -/
def H2 : Prop := ∀ (n k : ℕ) (G : SimpleGraph (Fin n)),
    G.chromaticNumber = (k : ℕ∞) → G.CliqueFree k →
    (∀ v : Fin n, (G.induce ({v}ᶜ : Set (Fin n))).chromaticNumber < (k : ℕ∞)) →
    ∀ a b : ℕ, 3 ≤ a → a ≤ b → a + b = k + 1 → G.CliqueFree a →
    ∃ s : Set (Fin n), (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)

theorem main : H1 → H2 → OMA.R_Erdos628_erdos_628_R1.H2 := by
  intro withClique withoutClique n k G chrom hk critical a b ha hab sumAB
  by_cases freeA : G.CliqueFree a
  · exact withoutClique n k G chrom hk critical a b ha hab sumAB freeA
  by_cases freeB : G.CliqueFree b
  · by_cases common : ∀ s : Finset (Fin n), G.IsNClique a s →
        b - 1 ≤ (univ.filter (fun v => ∀ u ∈ s, G.Adj v u)).card
    · exact withClique n k G chrom hk critical a b ha hab sumAB freeB freeA common
    · push Not at common
      obtain ⟨s, hs, hfew⟩ := common
      apply OMA.Erdos628Recolor.split_of_small_common G k a b chrom (by omega) sumAB s hs
      convert hfew using 1
      · rfl
      · exact congrArg Finset.card (Finset.filter_congr_decidable _ _ _)
  · unfold CliqueFree at freeB
    push Not at freeB
    obtain ⟨s, hs⟩ := freeB
    exact OMA.Erdos628CliqueExchange.split_of_large_clique G
      (OMA.Erdos628Recolor.common_card_ge_of_colorable_compl G) ha hab sumAB chrom hk hs

end OMA.R_Erdos628_erdos_628_R1_H2_R1
