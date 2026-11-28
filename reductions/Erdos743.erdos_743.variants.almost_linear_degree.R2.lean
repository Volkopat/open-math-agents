import FormalConjectures.ErdosProblems.«743»

/-!
The two perfect-packing inputs here correspond to the leaf case in Theorem 5 and
the bare-path case in Theorem 10 of Allen, Böttcher, Clemens, Hladký, Piguet and
Taraz, arXiv:2106.11720v3, specialized to the complete host and the prescribed
tree orders. In the second case the proof supplies a disjoint family of trees
carrying independent vertices of odd degree, as required by Definition 9.

The degree accounting and the twelve-vertex path extraction below are the
existing proofs from this project's bounded-degree reduction R2, whose source
blob is fec1a8dcc60f53909934949d3ad1f8de7dd19c15. Both work for arbitrary trees.
-/

namespace OMA.R_Erdos743_erdos_743_variants_almost_linear_degree_R2

open Filter Finset SimpleGraph Erdos743
open scoped Classical

/-- Perfect packing when many nonspanning trees each have many leaves. -/
def H1 : Prop :=
  ∃ c : ℝ, 0<c ∧ ∀ᶠ n : ℕ in atTop, ∀ (T : (k : ℕ) → SimpleGraph (Fin k))
    (J : Finset ℕ), (∀ k ∈ Set.Icc 2 n, (T k).IsTree ∧
      ((T k).maxDegree:ℝ) ≤ c*n/Real.log n) →
    J ⊆ Icc ((n+3)/4) (n/2) →
    n^2 ≤ 4000000 * (∑ k ∈ J, (univ.filter (fun x : Fin k => (T k).degree x=1)).card) →
    IsPacking n (Set.Icc 2 n) T

/-- Perfect packing with vertex-disjoint bare paths and a separate parity family. -/
def H2 : Prop :=
  ∃ c : ℝ, 0<c ∧ ∀ᶠ n : ℕ in atTop, ∀ (T : (k : ℕ) → SimpleGraph (Fin k))
    (J K : Finset ℕ), (∀ k ∈ Set.Icc 2 n, (T k).IsTree ∧
      ((T k).maxDegree:ℝ) ≤ c*n/Real.log n) →
    J ⊆ Icc ((n+3)/4) (n/2) → J.card=n/1000 →
    (∀ k ∈ J, ∃ f : Fin (n/1000) × Fin 12 → Fin k, Function.Injective f ∧
      (∀ i (j : Fin 11), (T k).Adj (f (i,j.castSucc)) (f (i,j.succ))) ∧
      (∀ i j, (T k).degree (f (i,j))=2)) →
    K ⊆ Icc 3 (3*n/4) → Disjoint J K → 4*n ≤ 3*(2*K.card) → 2 ≤ c*n/Real.log n →
    (∀ k ∈ K, ∃ x y : Fin k, x ≠ y ∧ (T k).degree x=1 ∧
      (T k).degree y=1 ∧ ¬ (T k).Adj x y) → IsPacking n (Set.Icc 2 n) T

section StructuralLemmas

private lemma tree_degree_accounting {k : ℕ} (hk : 2 ≤ k) (G : SimpleGraph (Fin k))
    (hT : G.IsTree) :
    let L := (Finset.univ.filter (fun v : Fin k => G.degree v = 1)).card
    let B := Finset.univ.filter (fun v : Fin k => G.degree v ≠ 2)
    B.card ≤ 2 * L ∧ ∑ v ∈ B, G.degree v ≤ 4 * L := by
  intro L B
  have : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.mpr hk
  have hmin : G.minDegree = 1 := hT.minDegree_eq_one_of_nontrivial
  have hdeg_pos : ∀ v : Fin k, 1 ≤ G.degree v := fun v => by
    rw [← hmin]
    exact G.minDegree_le_degree v
  have hedge : G.edgeFinset.card + 1 = k := by
    simpa only [Fintype.card_fin] using hT.card_edgeFinset
  have hsum_all : ∑ v : Fin k, G.degree v = 2 * G.edgeFinset.card :=
    G.sum_degrees_eq_twice_card_edges
  have hsum_tot : ∑ v : Fin k, G.degree v + 2 = 2 * k := by omega
  let D2 := Finset.univ.filter (fun v : Fin k => G.degree v = 2)
  have hdisj_BD2 : Disjoint B D2 := by
    rw [Finset.disjoint_filter]
    intro v _ h1 h2
    exact h1 h2
  have hunion_BD2 : B ∪ D2 = Finset.univ := by
    ext v
    simp only [B, D2, mem_union, mem_filter, mem_univ, true_and, iff_true]
    exact em' _
  have hcard_BD2 : B.card + D2.card = k := by
    rw [← Finset.card_union_of_disjoint hdisj_BD2, hunion_BD2, Finset.card_univ, Fintype.card_fin]
  have hsum_D2 : ∑ v ∈ D2, G.degree v = 2 * D2.card := by
    calc
      ∑ v ∈ D2, G.degree v = ∑ _v ∈ D2, 2 :=
        Finset.sum_congr rfl (fun v hv => (Finset.mem_filter.mp hv).2)
      _ = 2 * D2.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have hsum_split : ∑ v ∈ B, G.degree v + ∑ v ∈ D2, G.degree v = ∑ v : Fin k, G.degree v := by
    rw [← Finset.sum_union hdisj_BD2, hunion_BD2]
  have hsum_B_eq : ∑ v ∈ B, G.degree v + 2 = 2 * B.card := by omega
  let B1 := Finset.univ.filter (fun v : Fin k => G.degree v = 1)
  let B3 := Finset.univ.filter (fun v : Fin k => 3 ≤ G.degree v)
  have hdisj_13 : Disjoint B1 B3 := by
    rw [Finset.disjoint_filter]
    intro v _ h1 h3
    omega
  have hunion_13 : B1 ∪ B3 = B := by
    ext v
    simp only [B, B1, B3, mem_union, mem_filter, mem_univ, true_and]
    have := hdeg_pos v
    omega
  have hcard_B : B.card = L + B3.card := by
    rw [← hunion_13, Finset.card_union_of_disjoint hdisj_13]
  have hsum_B1 : ∑ v ∈ B1, G.degree v = L := by
    calc
      ∑ v ∈ B1, G.degree v = ∑ _v ∈ B1, 1 :=
        Finset.sum_congr rfl (fun v hv => (Finset.mem_filter.mp hv).2)
      _ = L := by rw [Finset.sum_const, smul_eq_mul, mul_one]
  have hsum_B3 : 3 * B3.card ≤ ∑ v ∈ B3, G.degree v := by
    calc
      3 * B3.card = ∑ _v ∈ B3, 3 := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ v ∈ B3, G.degree v :=
        Finset.sum_le_sum (fun v hv => (Finset.mem_filter.mp hv).2)
  have hsum_B_split : ∑ v ∈ B, G.degree v = L + ∑ v ∈ B3, G.degree v := by
    rw [← hunion_13, Finset.sum_union hdisj_13, hsum_B1]
  have hB3_le : B3.card + 2 ≤ L := by omega
  constructor <;> omega

/-- Part 2: Bare-path extraction for a tree on `Fin k` (`k ≥ 2`).
If `12 * r + 24 * L ≤ k`, then `G` contains `r` vertex-disjoint paths of `12` vertices
all having degree `2` in `G`. -/
private lemma tree_extract_bare_paths {k r : ℕ} (hk : 2 ≤ k) (G : SimpleGraph (Fin k))
    (hT : G.IsTree)
    (hbound : 12 * r + 24 * (Finset.univ.filter (fun v : Fin k => G.degree v = 1)).card ≤ k) :
    ∃ f : Fin r × Fin 12 → Fin k,
      Function.Injective f ∧
      (∀ i (j : Fin 11), G.Adj (f (i, j.castSucc)) (f (i, j.succ))) ∧
      (∀ i j, G.degree (f (i, j)) = 2) := by
  have : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.mpr hk
  obtain ⟨root, hroot_deg⟩ := hT.exists_vert_degree_one_of_nontrivial
  let B := Finset.univ.filter (fun v : Fin k => G.degree v ≠ 2)
  let D2 := Finset.univ.filter (fun v : Fin k => G.degree v = 2)
  have hB_le : B.card ≤ 2 * (Finset.univ.filter (fun v : Fin k => G.degree v = 1)).card :=
    (tree_degree_accounting hk G hT).1
  choose p hp hp_uniq using (fun v : Fin k => hT.existsUnique_path v root)
  let par : Fin k → Fin k := fun v => (p v).snd
  have hp_root : p root = Walk.nil := (hp_uniq root Walk.nil Walk.IsPath.nil).symm
  have hpar_adj : ∀ v : Fin k, v ≠ root → G.Adj v (par v) := fun v hv =>
    (p v).adj_snd (Walk.not_nil_of_ne hv)
  have hp_cons : ∀ (v : Fin k) (hv : v ≠ root),
      p v = Walk.cons (hpar_adj v hv) (p (par v)) := by
    intro v hv
    have hnil : ¬ (p v).Nil := Walk.not_nil_of_ne hv
    have htail_eq : Walk.cons ((p v).adj_snd hnil) (p v).tail = p v :=
      (p v).cons_tail_eq hnil
    have htail_path : (p v).tail.IsPath := by
      have h1 : (Walk.cons ((p v).adj_snd hnil) (p v).tail).IsPath := by
        rw [htail_eq]
        exact hp v
      exact (Walk.cons_isPath_iff _ _).mp h1 |>.1
    have htail_p : (p v).tail = p (par v) := hp_uniq (par v) (p v).tail htail_path
    rw [← htail_eq, htail_p]
  have hpar_len : ∀ v : Fin k, v ≠ root → (p v).length = (p (par v)).length + 1 := by
    intro v hv
    conv_lhs => rw [hp_cons v hv]
    simp only [Walk.length_cons]
  have hadj_other : ∀ {v u : Fin k}, G.Adj v u → u ≠ par v →
      u ≠ root ∧ par u = v ∧ (p u).length = (p v).length + 1 := by
    intro v u hadj hne
    have hu_not : u ∉ (p v).support := by
      intro hmem
      exact hne (hT.isAcyclic.eq_snd_of_adj_start (hp v) hadj hmem)
    have hq_path : (Walk.cons hadj.symm (p v)).IsPath :=
      (Walk.cons_isPath_iff hadj.symm (p v)).mpr ⟨hp v, hu_not⟩
    have hpu : p u = Walk.cons hadj.symm (p v) :=
      (hp_uniq u (Walk.cons hadj.symm (p v)) hq_path).symm
    have hu_ne : u ≠ root := by
      intro hEq
      have hlen : (p u).length = 0 := by rw [hEq, hp_root]; rfl
      rw [hpu] at hlen
      simp only [Walk.length_cons, Nat.add_eq_zero_iff, one_ne_zero, and_false] at hlen
    refine ⟨hu_ne, ?_, ?_⟩
    · simp only [par, hpu, Walk.snd_cons]
    · simp only [hpu, Walk.length_cons]
  -- Define child function on D2 (the unique neighbor of v other than par v)
  have hex_ch : ∀ v : Fin k, v ∈ D2 → ∃ u : Fin k, G.Adj v u ∧ u ≠ par v := by
    intro v hv
    have hv_deg : G.degree v = 2 := (Finset.mem_filter.mp hv).2
    have hv_ne : v ≠ root := by
      intro h; rw [h] at hv_deg; omega
    have hpar_mem : par v ∈ G.neighborFinset v := by
      rw [SimpleGraph.mem_neighborFinset]
      exact hpar_adj v hv_ne
    have hcard_erase : ((G.neighborFinset v).erase (par v)).card = 1 := by
      rw [Finset.card_erase_of_mem hpar_mem, SimpleGraph.card_neighborFinset_eq_degree, hv_deg]
    obtain ⟨u, hu⟩ := Finset.card_pos.mp (by omega : 0 < ((G.neighborFinset v).erase (par v)).card)
    rw [Finset.mem_erase, SimpleGraph.mem_neighborFinset] at hu
    exact ⟨u, hu.2, hu.1⟩
  let ch : Fin k → Fin k := fun v =>
    if hv : v ∈ D2 then Classical.choose (hex_ch v hv) else root
  have hch_spec : ∀ {v : Fin k}, v ∈ D2 → G.Adj v (ch v) ∧ ch v ≠ par v := by
    intro v hv
    simp only [ch, dif_pos hv]
    exact Classical.choose_spec (hex_ch v hv)
  have hch_par : ∀ {v : Fin k}, v ∈ D2 → ch v ≠ root ∧ par (ch v) = v := by
    intro v hv
    have hs := hch_spec hv
    have ho := hadj_other hs.1 hs.2
    exact ⟨ho.1, ho.2.1⟩
  have hch_inj : ∀ {v₁ v₂ : Fin k}, v₁ ∈ D2 → v₂ ∈ D2 → ch v₁ = ch v₂ → v₁ = v₂ := by
    intro v₁ v₂ hv₁ hv₂ heq
    have h1 := (hch_par hv₁).2
    have h2 := (hch_par hv₂).2
    rw [← h1, heq, h2]
  have hpar_inj_D2 : ∀ {w₁ w₂ : Fin k}, w₁ ≠ root → w₂ ≠ root →
      par w₁ = par w₂ → par w₁ ∈ D2 → w₁ = w₂ := by
    intro w₁ w₂ hw₁ hw₂ heq hyD2
    let y := par w₁
    have hy_deg : G.degree y = 2 := (Finset.mem_filter.mp hyD2).2
    have hy_ne : y ≠ root := by
      intro h
      rw [h] at hy_deg
      omega
    have hadj1 : G.Adj y w₁ := (hpar_adj w₁ hw₁).symm
    have hadj2 : G.Adj y w₂ := by
      have h2 := (hpar_adj w₂ hw₂).symm
      rwa [← heq] at h2
    have hne1 : w₁ ≠ par y := by
      intro h
      have hl1 : (p w₁).length = (p y).length + 1 := hpar_len w₁ hw₁
      have hl2 : (p y).length = (p (par y)).length + 1 := hpar_len y hy_ne
      rw [h] at hl1
      omega
    have hne2 : w₂ ≠ par y := by
      intro h
      have hl1 : (p w₂).length = (p y).length + 1 := by
        have h2 := hpar_len w₂ hw₂
        rwa [← heq] at h2
      have hl2 : (p y).length = (p (par y)).length + 1 := hpar_len y hy_ne
      rw [h] at hl1
      omega
    have hmem1 : w₁ ∈ (G.neighborFinset y).erase (par y) := by
      rw [Finset.mem_erase, SimpleGraph.mem_neighborFinset]
      exact ⟨hne1, hadj1⟩
    have hmem2 : w₂ ∈ (G.neighborFinset y).erase (par y) := by
      rw [Finset.mem_erase, SimpleGraph.mem_neighborFinset]
      exact ⟨hne2, hadj2⟩
    have hpar_mem : par y ∈ G.neighborFinset y := by
      rw [SimpleGraph.mem_neighborFinset]
      exact hpar_adj y hy_ne
    have hcard_one : ((G.neighborFinset y).erase (par y)).card = 1 := by
      rw [Finset.card_erase_of_mem hpar_mem, SimpleGraph.card_neighborFinset_eq_degree, hy_deg]
    exact Finset.card_le_one.mp (le_of_eq hcard_one) w₁ hmem1 w₂ hmem2
  -- Define upward D2-chain length `d v` using `List.takeWhile` on `(p v).support.tail`
  let d : Fin k → ℕ := fun v =>
    ((p v).support.tail.takeWhile (fun x => decide (G.degree x = 2))).length
  have hsupp_cons : ∀ {a b : Fin k} (w : G.Walk a b), w.support = a :: w.support.tail := by
    intro a b w
    cases w <;> rfl
  have hd_step : ∀ {v : Fin k}, v ∈ D2 →
      (par v ∈ D2 → d v = d (par v) + 1) ∧ (par v ∉ D2 → d v = 0) := by
    intro v hv
    have hv_ne : v ≠ root := by
      intro h
      have hdeg := (Finset.mem_filter.mp hv).2
      rw [h] at hdeg
      omega
    have hsupp : (p v).support.tail = (p (par v)).support := by
      conv_lhs => rw [hp_cons v hv_ne]
      simp only [Walk.support_cons, List.tail_cons]
    constructor
    · intro hparD2
      have hdeg : G.degree (par v) = 2 := (Finset.mem_filter.mp hparD2).2
      change ((p v).support.tail.takeWhile (fun x => decide (G.degree x = 2))).length =
        ((p (par v)).support.tail.takeWhile (fun x => decide (G.degree x = 2))).length + 1
      rw [hsupp, hsupp_cons (p (par v)), List.takeWhile_cons]
      simp only [hdeg, decide_true, ↓reduceIte, List.length_cons, List.tail_cons]
    · intro hparND2
      have hdeg : G.degree (par v) ≠ 2 := fun h =>
        hparND2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
      change ((p v).support.tail.takeWhile (fun x => decide (G.degree x = 2))).length = 0
      rw [hsupp, hsupp_cons (p (par v)), List.takeWhile_cons]
      simp only [hdeg, decide_false, Bool.false_eq_true, ↓reduceIte, List.length_nil]
  -- Define Bot := {v ∈ D2 | ch v ∈ B}
  let Bot := D2.filter (fun v => ch v ∈ B)
  have hBot_le : Bot.card ≤ B.card := by
    have hmaps : ∀ v ∈ Bot, ch v ∈ B := fun v hv => (Finset.mem_filter.mp hv).2
    have hinj : Set.InjOn ch (Bot : Set (Fin k)) := by
      intro v₁ hv₁ v₂ hv₂ heq
      rw [Finset.mem_coe] at hv₁ hv₂
      exact hch_inj (Finset.mem_filter.mp hv₁).1 (Finset.mem_filter.mp hv₂).1 heq
    exact Finset.card_le_card_of_injOn ch hmaps hinj
  -- Residue classes C t := {v ∈ D2 | d v % 12 = t}
  let C : ℕ → Finset (Fin k) := fun t => D2.filter (fun v => d v % 12 = t)
  have hC_step : ∀ t < 11, (C t).card ≤ (C (t + 1)).card + (C t ∩ Bot).card := by
    intro t ht
    have hsplit : (C t).card = (C t \ Bot).card + (C t ∩ Bot).card := by
      rw [add_comm, Finset.card_inter_add_card_sdiff]
    rw [hsplit]
    have hle : (C t \ Bot).card ≤ (C (t + 1)).card := by
      refine Finset.card_le_card_of_injOn ch ?_ ?_
      · intro v hv
        rw [Finset.mem_coe, Finset.mem_sdiff] at hv
        rw [Finset.mem_coe]
        have hvD2 : v ∈ D2 := (Finset.mem_filter.mp hv.1).1
        have hmod : d v % 12 = t := (Finset.mem_filter.mp hv.1).2
        have hch_notB : ch v ∉ B := by
          intro hB
          exact hv.2 (Finset.mem_filter.mpr ⟨hvD2, hB⟩)
        have hchD2 : ch v ∈ D2 := by
          simp only [B, mem_filter, mem_univ, true_and, not_not] at hch_notB
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hch_notB⟩
        have hpar_ch : par (ch v) = v := (hch_par hvD2).2
        have hd_ch : d (ch v) = d v + 1 := by
          have := (hd_step hchD2).1
          rw [hpar_ch] at this
          exact this hvD2
        refine Finset.mem_filter.mpr ⟨hchD2, ?_⟩
        rw [hd_ch]
        omega
      · intro v₁ hv₁ v₂ hv₂ heq
        rw [Finset.mem_coe, Finset.mem_sdiff] at hv₁ hv₂
        exact hch_inj (Finset.mem_filter.mp hv₁.1).1 (Finset.mem_filter.mp hv₂.1).1 heq
    omega
  have hC_chain : ∀ t ≤ 11, (C t).card ≤ (C 11).card + ∑ s ∈ Finset.Ico t 11, (C s ∩ Bot).card := by
    intro t ht
    have haux : ∀ m, m ≤ 11 →
        (C (11 - m)).card ≤ (C 11).card + ∑ s ∈ Finset.Ico (11 - m) 11, (C s ∩ Bot).card := by
      intro m
      induction m with
      | zero =>
        intro _
        simp only [Nat.sub_zero, Finset.Ico_self, Finset.sum_empty, add_zero, le_refl]
      | succ m ih =>
        intro hm
        have hm1 : 11 - (m + 1) < 11 := by omega
        have hm2 : 11 - (m + 1) + 1 = 11 - m := by omega
        have hstep := hC_step (11 - (m + 1)) hm1
        rw [hm2] at hstep
        have hih := ih (by omega)
        have hico : Finset.Ico (11 - (m + 1)) 11 =
            insert (11 - (m + 1)) (Finset.Ico (11 - m) 11) := by
          ext x
          simp only [mem_Ico, mem_insert]
          omega
        have hsum_ico :
            ∑ s ∈ Finset.Ico (11 - (m + 1)) 11, (C s ∩ Bot).card =
            (C (11 - (m + 1)) ∩ Bot).card + ∑ s ∈ Finset.Ico (11 - m) 11, (C s ∩ Bot).card := by
          rw [hico, Finset.sum_insert (by simp only [mem_Ico]; omega)]
        omega
    have := haux (11 - t) (by omega)
    have hsub : 11 - (11 - t) = t := by omega
    rwa [hsub] at this
  have hsum_Bot : ∑ s ∈ Finset.range 12, (C s ∩ Bot).card = Bot.card := by
    have hdisj : Set.PairwiseDisjoint (Finset.range 12 : Set ℕ) (fun s => C s ∩ Bot) := by
      intro s₁ _ s₂ _ hne
      show Disjoint (C s₁ ∩ Bot) (C s₂ ∩ Bot)
      rw [Finset.disjoint_left]
      intro v hv₁ hv₂
      rw [Finset.mem_inter] at hv₁ hv₂
      have h1 := (Finset.mem_filter.mp hv₁.1).2
      have h2 := (Finset.mem_filter.mp hv₂.1).2
      omega
    rw [← Finset.card_biUnion hdisj]
    apply congrArg Finset.card
    ext v
    simp only [mem_biUnion, mem_range, mem_inter, C, mem_filter]
    constructor
    · rintro ⟨_, _, _, hv⟩; exact hv
    · intro hv
      exact ⟨d v % 12, Nat.mod_lt _ (by omega), ⟨(Finset.mem_filter.mp hv).1, rfl⟩, hv⟩
  have hC_le_11 : ∀ t ∈ Finset.range 11, (C t).card ≤ (C 11).card + Bot.card := by
    intro t ht
    rw [Finset.mem_range] at ht
    have h1 := hC_chain t (by omega)
    have hsub : Finset.Ico t 11 ⊆ Finset.range 12 := by
      intro s hs
      rw [Finset.mem_Ico] at hs
      rw [Finset.mem_range]
      omega
    have h2 : ∑ s ∈ Finset.Ico t 11, (C s ∩ Bot).card ≤ ∑ s ∈ Finset.range 12, (C s ∩ Bot).card :=
      Finset.sum_le_sum_of_subset hsub
    omega
  have hD2_sum : D2.card = ∑ t ∈ Finset.range 12, (C t).card := by
    have hdisj : Set.PairwiseDisjoint (Finset.range 12 : Set ℕ) C := by
      intro s₁ _ s₂ _ hne
      show Disjoint (C s₁) (C s₂)
      rw [Finset.disjoint_left]
      intro v hv₁ hv₂
      have h1 := (Finset.mem_filter.mp hv₁).2
      have h2 := (Finset.mem_filter.mp hv₂).2
      omega
    rw [← Finset.card_biUnion hdisj]
    apply congrArg Finset.card
    ext v
    simp only [mem_biUnion, mem_range, C, mem_filter]
    constructor
    · intro hv; exact ⟨d v % 12, Nat.mod_lt _ (by omega), hv, rfl⟩
    · rintro ⟨_, _, hv, _⟩; exact hv
  have hD2_bound : D2.card ≤ 12 * (C 11).card + 11 * Bot.card := by
    rw [hD2_sum, Finset.sum_range_succ]
    have hsum11 : ∑ t ∈ Finset.range 11, (C t).card ≤ ∑ _t ∈ Finset.range 11, ((C 11).card + Bot.card) :=
      Finset.sum_le_sum hC_le_11
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at hsum11
    omega
  have hcard_BD2 : B.card + D2.card = k := by
    have hdisj : Disjoint B D2 := by
      rw [Finset.disjoint_filter]
      intro v _ h1 h2; exact h1 h2
    have hunion : B ∪ D2 = Finset.univ := by
      ext v
      simp only [B, D2, mem_union, mem_filter, mem_univ, true_and, iff_true]
      exact em' _
    rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ, Fintype.card_fin]
  have hr_le : r ≤ (C 11).card := by omega
  -- Construct the r disjoint 12-bare-paths by walking UP from elements of C 11 via `par`
  have hiter_props : ∀ (v : Fin k), v ∈ D2 → ∀ j ≤ d v,
      par^[j] v ∈ D2 ∧ d (par^[j] v) = d v - j := by
    intro v hv j
    induction j with
    | zero =>
      intro _
      simp only [Function.iterate_zero, id_eq, Nat.sub_zero, hv, and_self]
    | succ j ih =>
      intro hj
      obtain ⟨hxD2, hdx⟩ := ih (by omega)
      have hparD2 : par (par^[j] v) ∈ D2 := by
        by_contra hnot
        have h0 := (hd_step hxD2).2 hnot
        omega
      have hdp := (hd_step hxD2).1 hparD2
      rw [Function.iterate_succ_apply']
      exact ⟨hparD2, by omega⟩
  have hiter_inj : ∀ (m : ℕ) (x₁ x₂ : Fin k), x₁ ∈ D2 → x₂ ∈ D2 →
      m ≤ d x₁ → m ≤ d x₂ → par^[m] x₁ = par^[m] x₂ → x₁ = x₂ := by
    intro m
    induction m with
    | zero =>
      intro x₁ x₂ _ _ _ _ h
      simpa only [Function.iterate_zero, id_eq] using h
    | succ m ih =>
      intro x₁ x₂ hx₁ hx₂ hm₁ hm₂ h
      have hpx₁_D2 : par x₁ ∈ D2 := by
        by_contra hnot
        have h0 := (hd_step hx₁).2 hnot
        omega
      have hpx₂_D2 : par x₂ ∈ D2 := by
        by_contra hnot
        have h0 := (hd_step hx₂).2 hnot
        omega
      have hdx₁ := (hd_step hx₁).1 hpx₁_D2
      have hdx₂ := (hd_step hx₂).1 hpx₂_D2
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply] at h
      have hpar_eq : par x₁ = par x₂ := ih (par x₁) (par x₂) hpx₁_D2 hpx₂_D2 (by omega) (by omega) h
      have hx₁_ne : x₁ ≠ root := by
        intro heq; have hdeg := (Finset.mem_filter.mp hx₁).2; rw [heq] at hdeg; omega
      have hx₂_ne : x₂ ≠ root := by
        intro heq; have hdeg := (Finset.mem_filter.mp hx₂).2; rw [heq] at hdeg; omega
      exact hpar_inj_D2 hx₁_ne hx₂_ne hpar_eq hpx₁_D2
  -- Pick an injection e : Fin r → Fin k with image in C 11
  let e_equiv := (C 11).equivFin.symm
  let e : Fin r → Fin k := fun i => (e_equiv ⟨i.val, lt_of_lt_of_le i.isLt hr_le⟩).val
  have he_mem : ∀ i : Fin r, e i ∈ C 11 := fun i =>
    (e_equiv ⟨i.val, lt_of_lt_of_le i.isLt hr_le⟩).property
  have he_inj : Function.Injective e := by
    intro i₁ i₂ h
    have hsub : e_equiv ⟨i₁.val, lt_of_lt_of_le i₁.isLt hr_le⟩ =
        e_equiv ⟨i₂.val, lt_of_lt_of_le i₂.isLt hr_le⟩ := Subtype.ext h
    have hfin := e_equiv.injective hsub
    exact Fin.ext (congrArg (fun x : Fin (C 11).card => x.val) hfin)
  refine ⟨fun p => par^[p.2.val] (e p.1), ?_, ?_, ?_⟩
  · -- Injectivity
    rintro ⟨i₁, j₁⟩ ⟨i₂, j₂⟩ h
    dsimp only at h
    have h1D2 : e i₁ ∈ D2 := (Finset.mem_filter.mp (he_mem i₁)).1
    have h2D2 : e i₂ ∈ D2 := (Finset.mem_filter.mp (he_mem i₂)).1
    have h1mod : d (e i₁) % 12 = 11 := (Finset.mem_filter.mp (he_mem i₁)).2
    have h2mod : d (e i₂) % 12 = 11 := (Finset.mem_filter.mp (he_mem i₂)).2
    have h1ge : 11 ≤ d (e i₁) := by omega
    have h2ge : 11 ≤ d (e i₂) := by omega
    have hd1 := (hiter_props (e i₁) h1D2 j₁.val (by omega)).2
    have hd2 := (hiter_props (e i₂) h2D2 j₂.val (by omega)).2
    have hdeq : d (e i₁) - j₁.val = d (e i₂) - j₂.val := by
      rw [← hd1, h, hd2]
    have hj_eq : j₁ = j₂ := by
      apply Fin.ext
      have hj1 : j₁.val < 12 := j₁.isLt
      have hj2 : j₂.val < 12 := j₂.isLt
      omega
    subst hj_eq
    have hi_eq : e i₁ = e i₂ :=
      hiter_inj j₁.val (e i₁) (e i₂) h1D2 h2D2 (by omega) (by omega) h
    exact Prod.ext (he_inj hi_eq) rfl
  · -- Adjacency
    intro i j
    have hiD2 : e i ∈ D2 := (Finset.mem_filter.mp (he_mem i)).1
    have himod : d (e i) % 12 = 11 := (Finset.mem_filter.mp (he_mem i)).2
    have hjD2 : par^[j.val] (e i) ∈ D2 :=
      (hiter_props (e i) hiD2 j.val (by omega)).1
    have hj_ne : par^[j.val] (e i) ≠ root := by
      intro heq
      have hdeg := (Finset.mem_filter.mp hjD2).2
      rw [heq] at hdeg
      omega
    change G.Adj (par^[j.val] (e i)) (par^[j.val + 1] (e i))
    rw [Function.iterate_succ_apply']
    exact hpar_adj (par^[j.val] (e i)) hj_ne
  · -- Degree 2
    intro i j
    have hiD2 : e i ∈ D2 := (Finset.mem_filter.mp (he_mem i)).1
    have himod : d (e i) % 12 = 11 := (Finset.mem_filter.mp (he_mem i)).2
    have hjD2 : par^[j.val] (e i) ∈ D2 :=
      (hiter_props (e i) hiD2 j.val (by omega)).1
    exact (Finset.mem_filter.mp hjD2).2

theorem independent_leaf_pair {k : ℕ} (G : SimpleGraph (Fin k)) (hT : G.IsTree) (hk : 3 ≤ k) :
    ∃ x y : Fin k, x ≠ y ∧ G.degree x = 1 ∧ G.degree y = 1 ∧ ¬ G.Adj x y := by
  let : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.mpr (by omega)
  obtain ⟨x,y,hxy,hx,hy⟩ := hT.exists_ne_and_degree_eq_one
  refine ⟨x,y,hxy,hx,hy,?_⟩
  intro adjacent
  obtain ⟨_,_,ux⟩ := degree_eq_one_iff_existsUnique_adj.mp hx
  obtain ⟨_,_,uy⟩ := degree_eq_one_iff_existsUnique_adj.mp hy
  have closed {a b : Fin k} (hab : G.Adj a b) (ha : a=x ∨ a=y) : b=x ∨ b=y := by
    rcases ha with rfl | rfl
    · exact Or.inr ((ux _ hab).trans (ux _ adjacent).symm)
    · exact Or.inl ((uy _ hab).trans (uy _ adjacent.symm).symm)
  have stays {a b : Fin k} (w : G.Walk a b) : a=x ∨ a=y → b=x ∨ b=y := by
    induction w with
    | nil => exact id
    | cons h _ ih => exact fun ha => ih (closed h ha)
  have cover : (univ : Finset (Fin k)) ⊆ {x,y} := by
    intro b _
    obtain ⟨w⟩ := hT.connected.preconnected x b
    simpa using stays w (Or.inl rfl)
  have hc := card_le_card cover
  simp [hxy] at hc
  omega

theorem odd_reservoir {n : ℕ} (hn : 1000 ≤ n) (J : Finset ℕ) (hJ : J.card ≤ n/16)
    (T : (k : ℕ) → SimpleGraph (Fin k)) (hT : ∀ k ∈ Set.Icc 2 n, (T k).IsTree) :
    ∃ K : Finset ℕ, K ⊆ Icc 3 (3*n/4) ∧ Disjoint J K ∧
      4*n ≤ 3*(2*K.card) ∧ ∀ k ∈ K, ∃ x y : Fin k,
        x ≠ y ∧ (T k).degree x=1 ∧ (T k).degree y=1 ∧ ¬ (T k).Adj x y := by
  let S := Icc 3 (3*n/4)
  let K := S \ J
  have cover : S ⊆ K ∪ J := by
    intro k hk
    by_cases hj : k ∈ J
    · exact mem_union_right _ hj
    · exact mem_union_left _ (mem_sdiff.mpr ⟨hk,hj⟩)
  have count := (card_le_card cover).trans (card_union_le K J)
  have size : S.card=3*n/4+1-3 := Nat.card_Icc _ _
  have sub : K ⊆ S := sdiff_subset
  refine ⟨K,sub,?_,by omega,?_⟩
  · rw [Finset.disjoint_left]
    intro k hj hk
    exact (mem_sdiff.mp hk).2 hj
  · intro k hk
    obtain ⟨lo,hi⟩ := mem_Icc.mp (sub hk)
    exact independent_leaf_pair (T k) (hT k ⟨by omega,by omega⟩) lo

theorem leaf_mass {n : ℕ} (hn : 1000 ≤ n) (J : Finset ℕ) (leafCount : ℕ → ℕ)
    (hJ : J.card = n/1000) (hl : ∀ k ∈ J, n/1000 ≤ leafCount k) :
    n^2 ≤ 4000000 * (∑ k ∈ J, leafCount k) := by
  have lower : (n/1000)^2 ≤ ∑ k ∈ J, leafCount k := by
    calc
      (n/1000)^2 = ∑ _k ∈ J, n/1000 := by simp [hJ,pow_two]
      _ ≤ _ := sum_le_sum hl
  have bound : n ≤ 2000*(n/1000) := by omega
  calc
    n^2 ≤ (2000*(n/1000))^2 := Nat.pow_le_pow_left bound 2
    _ = 4000000*(n/1000)^2 := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ lower

theorem two_le_tree_maxDegree {k : ℕ} (hk : 3 ≤ k) (G : SimpleGraph (Fin k)) (hG : G.IsTree) :
    2 ≤ G.maxDegree := by
  by_contra! bad
  have hsum : ∑ v : Fin k, G.degree v ≤ k := by
    calc
      _ ≤ ∑ _v : Fin k, 1 := sum_le_sum (fun v _ => (G.degree_le_maxDegree v).trans (by omega))
      _ = k := by simp
  have ee := hG.card_edgeFinset
  simp only [Fintype.card_fin] at ee
  have tt := G.sum_degrees_eq_twice_card_edges
  omega

end StructuralLemmas

theorem main : H1 → H2 → type_of% @Erdos743.erdos_743.variants.almost_linear_degree := by
  rintro ⟨c₁, hc₁, hleaf⟩ ⟨c₂, hc₂, hbare⟩
  refine ⟨min c₁ c₂, lt_min hc₁ hc₂,?_⟩
  filter_upwards [hleaf,hbare,eventually_ge_atTop 1000] with n h₁ h₂ hn
  intro T hT
  have logpos : 0 ≤ Real.log (n:ℝ) := Real.log_nonneg (by exact_mod_cast (show 1≤n by omega))
  have weaken (d : ℝ) (hd : min c₁ c₂ ≤ d) (k : ℕ) (hk : k ∈ Set.Icc 2 n) :
      (T k).IsTree ∧ ((T k).maxDegree:ℝ) ≤ d*n/Real.log n :=
    ⟨(hT k hk).1, (hT k hk).2.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hd (Nat.cast_nonneg n)) logpos)⟩
  let M := Icc ((n+3)/4) (n/2)
  let leaves (k : ℕ) := (univ.filter (fun x : Fin k => (T k).degree x=1)).card
  let L := M.filter (fun k => n/1000 ≤ leaves k)
  have ls : L ⊆ M := filter_subset _ _
  have big : 2*(n/1000) ≤ M.card := by dsimp [M]; rw [Nat.card_Icc]; omega
  by_cases many : n/1000 ≤ L.card
  · obtain ⟨J,hJ,card⟩ := exists_subset_card_eq many
    exact h₁ T J (weaken c₁ (min_le_left _ _)) (hJ.trans ls)
      (leaf_mass hn J leaves card (fun k hk => (mem_filter.mp (hJ hk)).2))
  · have enough : n/1000 ≤ (M \ L).card := by
      rw [card_sdiff_of_subset ls]
      omega
    obtain ⟨J,hJ,card⟩ := exists_subset_card_eq enough
    have jm : J ⊆ M := hJ.trans sdiff_subset
    obtain ⟨K,ks,dis,cap,oddpair⟩ := odd_reservoir hn J (by rw [card]; omega) T
      (fun k hk => (hT k hk).1)
    have tree3 := weaken c₂ (min_le_right _ _) 3 ⟨by omega,by omega⟩
    have limit : (2:ℝ) ≤ c₂*n/Real.log n := le_trans
      (by exact_mod_cast two_le_tree_maxDegree (k:=3) (by decide) (T 3) tree3.1) tree3.2
    apply h₂ T J K (weaken c₂ (min_le_right _ _)) jm card _ ks dis cap limit oddpair
    intro k hk
    obtain ⟨lo,hi⟩ := mem_Icc.mp (jm hk)
    have small : leaves k < n/1000 := by
      by_contra! bad
      exact (mem_sdiff.mp (hJ hk)).2 (mem_filter.mpr ⟨jm hk,bad⟩)
    refine tree_extract_bare_paths (by omega) (T k) (hT k ⟨by omega,by omega⟩).1 ?_
    change 12*(n/1000)+24*leaves k ≤ k
    omega

end OMA.R_Erdos743_erdos_743_variants_almost_linear_degree_R2
