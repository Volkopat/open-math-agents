import OMAReductions.R_Arxiv_2001_02665_kotzig_conjecture_large_R1
import Mathlib

/-!
Deterministic rainbow embedding of large Case C trees into the near-distance coloured complete
graph on 2n + 1 vertices, following Section 7 and Theorem 2.2 of Montgomery, Pokrovskiy, and
Sudakov (2020).
-/

namespace KotzigCaseCEmbedding

open SimpleGraph

-- ============================================================================
-- Section 1: Arithmetic Helpers and Near-Distance Edge Colours
-- ============================================================================

private def distNat (a b : ℕ) : ℕ := (a - b) + (b - a)

private lemma distNat_comm (a b : ℕ) : distNat a b = distNat b a := by
  dsimp [distNat]; omega

private lemma distNat_pos_of_ne {a b : ℕ} (h : a ≠ b) : 1 ≤ distNat a b := by
  dsimp [distNat]; omega

private lemma distNat_sols {x y c : ℕ} (h : distNat x y = c) : y = x + c ∨ y = x - c := by
  dsimp [distNat] at h; omega

private lemma distNat_mod_two_odd {x y : ℕ} (h : y % 2 ≠ x % 2) : distNat x y % 2 = 1 := by
  dsimp [distNat]; omega

private def ndColor {n : ℕ} (x y : Fin (2 * n + 1)) : ℕ :=
  min (x - y).val (y - x).val

private lemma ndColor_symm {n : ℕ} (x y : Fin (2 * n + 1)) :
    ndColor x y = ndColor y x :=
  Nat.min_comm _ _

private lemma ndColor_eq_of_sub_eq {n : ℕ} {x₁ y₁ x₂ y₂ : Fin (2 * n + 1)}
    (h : x₁ - y₁ = x₂ - y₂ ∨ x₁ - y₁ = y₂ - x₂) :
    ndColor x₁ y₁ = ndColor x₂ y₂ := by
  rcases h with h1 | h2
  · have hneg : y₁ - x₁ = y₂ - x₂ := by
      calc y₁ - x₁ = -(x₁ - y₁) := (neg_sub x₁ y₁).symm
        _ = -(x₂ - y₂) := by rw [h1]
        _ = y₂ - x₂ := neg_sub x₂ y₂
    simp only [ndColor, h1, hneg]
  · have hneg : y₁ - x₁ = x₂ - y₂ := by
      calc y₁ - x₁ = -(x₁ - y₁) := (neg_sub x₁ y₁).symm
        _ = -(y₂ - x₂) := by rw [h2]
        _ = x₂ - y₂ := neg_sub y₂ x₂
    simp only [ndColor, h2, hneg, Nat.min_comm]

private lemma ndColor_of_lt_le {n a b : ℕ} (ha : a < 2 * n + 1) (hb : b < 2 * n + 1)
    (hlt : a < b) (hle : b - a ≤ n) :
    ndColor (n := n) ⟨a, ha⟩ ⟨b, hb⟩ = b - a := by
  let x : Fin (2 * n + 1) := ⟨a, ha⟩
  let y : Fin (2 * n + 1) := ⟨b, hb⟩
  let d := b - a
  have hyx : y - x = ⟨d, by omega⟩ := by
    apply sub_eq_iff_eq_add.mpr
    apply Fin.ext
    simp only [Fin.val_add, x, y, d]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have hxy : x - y = ⟨2 * n + 1 - d, by omega⟩ := by
    apply sub_eq_iff_eq_add.mpr
    apply Fin.ext
    simp only [Fin.val_add, x, y, d]
    have hsum : (2 * n + 1 - (b - a)) + b = (2 * n + 1) + a := by omega
    rw [hsum, Nat.add_mod_left, Nat.mod_eq_of_lt ha]
  change min (x - y).val (y - x).val = d
  rw [hxy, hyx]
  dsimp only [d]
  omega

private lemma ndColor_eq_distNat {n a b : ℕ} (ha : a < 2 * n + 1) (hb : b < 2 * n + 1)
    (hne : a ≠ b) (hle : distNat a b ≤ n) :
    ndColor (n := n) ⟨a, ha⟩ ⟨b, hb⟩ = distNat a b := by
  rcases lt_trichotomy a b with hlt | rfl | hgt
  · have hd : distNat a b = b - a := by dsimp [distNat]; omega
    rw [hd]
    exact ndColor_of_lt_le ha hb hlt (by omega)
  · exact absurd rfl hne
  · have hd : distNat a b = a - b := by dsimp [distNat]; omega
    rw [ndColor_symm, hd]
    exact ndColor_of_lt_le hb ha hgt (by omega)

private lemma ndColor_zero_wrap {n c : ℕ} (hc1 : 1 ≤ c) (hcn : c ≤ n) :
    ndColor (n := n) ⟨0, by omega⟩ ⟨2 * n + 1 - c, by omega⟩ = c := by
  let x : Fin (2 * n + 1) := ⟨0, by omega⟩
  let y : Fin (2 * n + 1) := ⟨2 * n + 1 - c, by omega⟩
  have hyx : y - x = y := sub_zero y
  have hxy : x - y = ⟨c, by omega⟩ := by
    apply sub_eq_iff_eq_add.mpr
    apply Fin.ext
    simp only [Fin.val_add, x, y]
    have hsum : c + (2 * n + 1 - c) = 2 * n + 1 := by omega
    rw [hsum, Nat.mod_self]
  change min (x - y).val (y - x).val = c
  rw [hxy, hyx]
  dsimp only [y]
  omega

private lemma two_mul_add_three_le_two_pow : ∀ r : ℕ, 4 ≤ r → 2 * r + 3 ≤ 2 ^ r := by
  intro r hr
  induction r, hr using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have h4 : 4 ≤ 2 ^ k := by
      calc 4 ≤ 2 * 4 + 3 := by omega
        _ ≤ 2 * k + 3 := by omega
        _ ≤ 2 ^ k := ih
    calc 2 * (k + 1) + 3 = (2 * k + 3) + 2 := by ring
      _ ≤ 2 ^ k + 2 ^ k := by omega
      _ = 2 ^ (k + 1) := by ring

private lemma sq_succ_le_two_pow_sub_two : ∀ r : ℕ, 14 ≤ r → (r + 1) ^ 2 ≤ 2 ^ r - 2 := by
  intro r hr
  induction r, hr using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have hlin : 2 * k + 3 ≤ 2 ^ k := two_mul_add_three_le_two_pow k (by omega)
    have h2pow : 4 ≤ 2 ^ k := by omega
    have hstep : (k + 1 + 1) ^ 2 = (k + 1) ^ 2 + (2 * k + 3) := by ring
    have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
    omega

private lemma large_n_params {n : ℕ} (hn : 2 ^ 196 ≤ n) :
    let r := Nat.sqrt (Nat.log 2 n)
    let L := 2 ^ r
    14 ≤ r ∧ 16384 ≤ L ∧ 10000000000 ≤ n / 100 ∧ n < 2 ^ (L - 2) := by
  dsimp only
  set r := Nat.sqrt (Nat.log 2 n) with hr_def
  set L := 2 ^ r with hL_def
  have hlog : 196 ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num) hn
  have hr : 14 ≤ r := by
    rw [hr_def, Nat.le_sqrt]
    omega
  have hL : 16384 ≤ L := by
    calc 16384 = 2 ^ 14 := by norm_num
      _ ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) hr
  have hq : 10000000000 ≤ n / 100 := by
    have hbig : 1000000000000 ≤ 2 ^ 196 := by norm_num
    omega
  have hn_lt_log : n < 2 ^ (Nat.log 2 n + 1) :=
    Nat.lt_pow_succ_log_self (by norm_num) n
  have hlog_lt : Nat.log 2 n < (r + 1) ^ 2 := by
    have := Nat.lt_succ_sqrt (Nat.log 2 n)
    simpa [pow_two, ← hr_def] using this
  have hsq_le : (r + 1) ^ 2 ≤ L - 2 := sq_succ_le_two_pow_sub_two r hr
  have hn_lt_L : n < 2 ^ (L - 2) := by
    refine lt_of_lt_of_le hn_lt_log ?_
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  exact ⟨hr, hL, hq, hn_lt_L⟩

-- ============================================================================
-- Section 2: Rooted Tree Ordering and Core-Leaf Rainbow Decomposition
-- ============================================================================

private lemma card_coe_set_eq {α : Type*} [Fintype α] [DecidableEq α] (s : Finset α)
    [Fintype ↥(s : Set α)] :
    Fintype.card ↥(s : Set α) = s.card := by
  rw [← Fintype.card_coe s]
  exact Fintype.card_congr (Equiv.refl _)

private lemma walk_boundary_edge {U : Type*} {G : SimpleGraph U} {s : Set U}
    {x y : U} (q : G.Walk x y) (hx : x ∉ s) (hy : y ∈ s) :
    ∃ a b : U, G.Adj a b ∧ a ∉ s ∧ b ∈ s := by
  induction q with
  | nil => exact absurd hy hx
  | @cons u v w hadj _ ih =>
    by_cases hv : v ∈ s
    · exact ⟨u, v, hadj, hx, hv⟩
    · exact ih hv hy

private structure RootedOrder {V : Type*} [Fintype V] (G : SimpleGraph V) (r₀ : V) where
  ord : Fin (Fintype.card V) ≃ V
  root_eq : ord ⟨0, Fintype.card_pos_iff.mpr ⟨r₀⟩⟩ = r₀
  par : (i : Fin (Fintype.card V)) → 0 < i.val → Fin (Fintype.card V)
  par_lt : ∀ i hi, (par i hi).val < i.val
  par_adj : ∀ i hi, G.Adj (ord (par i hi)) (ord i)

private noncomputable def buildRootedOrder {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsTree) (r₀ : V) :
    RootedOrder G r₀ := by
  classical
  set m := Fintype.card V with hm_def
  have hm_pos : 0 < m := Fintype.card_pos_iff.mpr ⟨r₀⟩
  have hstep : ∀ (k : ℕ), 1 ≤ k → k ≤ m →
      ∃ f : Fin k → V,
        Function.Injective f ∧
        (∀ hk0 : 0 < k, f ⟨0, hk0⟩ = r₀) ∧
        (∀ (i : Fin k), 0 < i.val → ∃ j : Fin k, j.val < i.val ∧ G.Adj (f j) (f i)) := by
    intro k hk1
    induction k, hk1 using Nat.le_induction with
    | base =>
      intro _
      refine ⟨fun _ => r₀, ?_, ?_, ?_⟩
      · intro a b _; exact Subsingleton.elim a b
      · intro _; rfl
      · intro i hi; omega
    | succ k hk1 ih =>
      intro hk_le
      obtain ⟨f, hfinj, hf0, hfpar⟩ := ih (by omega)
      let S : Finset V := Finset.univ.image f
      have hS_card : S.card = k := by
        rw [Finset.card_image_of_injective _ hfinj, Finset.card_fin]
      have hnot_all : ∃ z : V, z ∉ S := by
        by_contra hall
        push Not at hall
        have hsub : (Finset.univ : Finset V) ⊆ S := fun z _ => hall z
        have hle := Finset.card_le_card hsub
        have huniv_c : (Finset.univ : Finset V).card = m := Finset.card_univ
        omega
      obtain ⟨z, hz⟩ := hnot_all
      have hr0_mem : r₀ ∈ S := by
        rw [← hf0 (by omega)]
        exact Finset.mem_image_of_mem f (Finset.mem_univ (⟨0, by omega⟩ : Fin k))
      obtain ⟨q⟩ := hG.connected z r₀
      obtain ⟨a, b, hab, ha_not, hb_mem⟩ :=
        walk_boundary_edge (s := (S : Set V)) q
          (by simpa using hz) (by simpa using hr0_mem)
      have hb_S : b ∈ S := by simpa using hb_mem
      have ha_S : a ∉ S := by simpa using ha_not
      obtain ⟨j₀, _, rfl⟩ := Finset.mem_image.mp hb_S
      let f' : Fin (k + 1) → V := fun i =>
        if h : i.val < k then f ⟨i.val, h⟩ else a
      refine ⟨f', ?_, ?_, ?_⟩
      · intro i₁ i₂ heq
        dsimp only [f'] at heq
        by_cases h1 : i₁.val < k <;> by_cases h2 : i₂.val < k
        · rw [dif_pos h1, dif_pos h2] at heq
          have hsub : (⟨i₁.val, h1⟩ : Fin k) = ⟨i₂.val, h2⟩ := hfinj heq
          exact Fin.ext (congrArg (Fin.val : Fin k → ℕ) hsub)
        · rw [dif_pos h1, dif_neg h2] at heq
          exact absurd (heq ▸ Finset.mem_image_of_mem f (Finset.mem_univ (⟨i₁.val, h1⟩ : Fin k))) ha_S
        · rw [dif_neg h1, dif_pos h2] at heq
          exact absurd (heq.symm ▸ Finset.mem_image_of_mem f (Finset.mem_univ (⟨i₂.val, h2⟩ : Fin k))) ha_S
        · exact Fin.ext (by omega)
      · intro _
        dsimp only [f']
        rw [dif_pos (by omega)]
        exact hf0 (by omega)
      · intro i hi
        by_cases hlt : i.val < k
        · obtain ⟨j, hjlt, hjadj⟩ := hfpar ⟨i.val, hlt⟩ hi
          refine ⟨⟨j.val, by omega⟩, hjlt, ?_⟩
          dsimp only [f']
          rw [dif_pos j.isLt, dif_pos hlt]
          exact hjadj
        · have hj0_lt : j₀.val < k := j₀.isLt
          refine ⟨⟨j₀.val, by omega⟩, by dsimp; omega, ?_⟩
          dsimp only [f']
          rw [dif_pos hj0_lt, dif_neg hlt]
          exact hab.symm
  let hfin := hstep m (Nat.succ_le_of_lt hm_pos) (le_refl m)
  let f := hfin.choose
  have hf_spec := hfin.choose_spec
  have hf_bij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr ⟨hf_spec.1, Fintype.card_fin m⟩
  let ord : Fin m ≃ V := Equiv.ofBijective f hf_bij
  exact {
    ord := ord
    root_eq := hf_spec.2.1 hm_pos
    par := fun i hi => (hf_spec.2.2 i hi).choose
    par_lt := fun i hi => (hf_spec.2.2 i hi).choose_spec.1
    par_adj := fun i hi => (hf_spec.2.2 i hi).choose_spec.2
  }

private lemma rootedOrder_surj_edges {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsTree) {r₀ : V}
    (R : RootedOrder G r₀) {u v : V} (huv : G.Adj u v) :
    ∃ t : Fin (Fintype.card V - 1),
      s(u, v) = s(R.ord (R.par ⟨t.val + 1, by omega⟩ (by simp)),
                  R.ord ⟨t.val + 1, by omega⟩) := by
  classical
  set m := Fintype.card V with hm_def
  let idx : Fin (m - 1) → Fin m := fun t => ⟨t.val + 1, by omega⟩
  let treeEdge : Fin (m - 1) → Sym2 V := fun t =>
    s(R.ord (R.par (idx t) (by simp [idx])), R.ord (idx t))
  have hinj : Function.Injective treeEdge := by
    intro t₁ t₂ heq
    dsimp only [treeEdge] at heq
    rw [Sym2.eq_iff] at heq
    rcases heq with ⟨_, h2⟩ | ⟨h1, h2⟩
    · have hi := R.ord.injective h2
      have hval := congrArg (Fin.val : Fin m → ℕ) hi
      dsimp [idx] at hval
      exact Fin.ext (by omega)
    · have hp1 := R.ord.injective h1
      have hp2 := R.ord.injective h2
      have hlt1 := R.par_lt (idx t₁) (by simp [idx])
      have hlt2 := R.par_lt (idx t₂) (by simp [idx])
      rw [hp1] at hlt1
      rw [← hp2] at hlt2
      omega
  have hsub : Finset.univ.image treeEdge ⊆ G.edgeFinset := by
    intro e he
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp he
    exact G.mem_edgeFinset.mpr (R.par_adj (idx t) (by simp [idx]))
  have hm_pos : 0 < m := Fintype.card_pos_iff.mpr ⟨r₀⟩
  have hcard_G : G.edgeFinset.card = m - 1 := by
    have := hG.card_edgeFinset
    omega
  have hcard_img : (Finset.univ.image treeEdge).card = m - 1 := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_fin]
  have heq_set : Finset.univ.image treeEdge = G.edgeFinset :=
    Finset.eq_of_subset_of_card_le hsub (by omega)
  have hmem : s(u, v) ∈ Finset.univ.image treeEdge := by
    rw [heq_set]
    exact G.mem_edgeFinset.mpr huv
  obtain ⟨t, _, ht⟩ := Finset.mem_image.mp hmem
  exact ⟨t, ht.symm⟩

private lemma induce_compl_leaves_isTree {n : ℕ}
    (T : SimpleGraph (Fin (n + 1))) [DecidableRel T.Adj] (hT : T.IsTree)
    (core : Finset (Fin (n + 1))) (hcore_pos : 0 < core.card)
    (hrem_leaf : ∀ w : Fin (n + 1), w ∉ core → T.degree w = 1) :
    (T.induce (core : Set (Fin (n + 1)))).IsTree := by
  have hpre : (T.induce (core : Set (Fin (n + 1)))).Preconnected := by
    refine hT.connected.preconnected.induce_of_degree_eq_one ?_
    intro w hw
    have hdeg1 : T.degree w = 1 := hrem_leaf w (by simpa using hw)
    obtain ⟨u, _, hu⟩ := degree_eq_one_iff_existsUnique_adj.mp hdeg1
    intro a ha b hb
    exact (hu a ha).trans (hu b hb).symm
  obtain ⟨w₀, hw₀⟩ := Finset.card_pos.mp hcore_pos
  let _ : Nonempty ↥(core : Set (Fin (n + 1))) := ⟨⟨w₀, hw₀⟩⟩
  exact ⟨⟨hpre⟩, hT.isAcyclic.induce _⟩

private lemma ndColor_eq_of_sym2_eq {n : ℕ} (g : Fin (n + 1) → Fin (2 * n + 1))
    {a b c d : Fin (n + 1)} (h : s(a, b) = s(c, d)) :
    ndColor (g a) (g b) = ndColor (g c) (g d) := by
  rw [Sym2.eq_iff] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact ndColor_symm _ _

private lemma rainbow_of_core_and_leaves {n : ℕ}
    (T : SimpleGraph (Fin (n + 1))) [DecidableRel T.Adj] (hT : T.IsTree)
    (core : Finset (Fin (n + 1)))
    (r₀ : ↥(core : Set (Fin (n + 1))))
    (R : RootedOrder (T.induce (core : Set (Fin (n + 1)))) r₀)
    (hubOf : (w : Fin (n + 1)) → w ∉ core → Fin (n + 1))
    (hhub_mem : ∀ w hw, hubOf w hw ∈ core)
    (hrem_deg : ∀ w, w ∉ core → T.degree w = 1)
    (hhub_adj : ∀ w hw, T.Adj (hubOf w hw) w)
    (g : Fin (n + 1) ↪ Fin (2 * n + 1))
    (C_core : Finset ℕ)
    (hecCore_mem : ∀ t : Fin (Fintype.card ↥(core : Set (Fin (n + 1))) - 1),
      ndColor (g (R.ord (R.par ⟨t.val + 1, by omega⟩ (by simp))).val)
              (g (R.ord ⟨t.val + 1, by omega⟩).val) ∈ C_core)
    (hecCore_inj : Function.Injective
      (fun t : Fin (Fintype.card ↥(core : Set (Fin (n + 1))) - 1) =>
        ndColor (g (R.ord (R.par ⟨t.val + 1, by omega⟩ (by simp))).val)
                (g (R.ord ⟨t.val + 1, by omega⟩).val)))
    (hecLeaf_notMem : ∀ w : {w : Fin (n + 1) // w ∉ core},
      ndColor (g (hubOf w.val w.property)) (g w.val) ∉ C_core)
    (hecLeaf_inj : Function.Injective
      (fun w : {w : Fin (n + 1) // w ∉ core} =>
        ndColor (g (hubOf w.val w.property)) (g w.val))) :
    ∀ u₁ v₁ u₂ v₂, T.Adj u₁ v₁ → T.Adj u₂ v₂ →
      (g u₁ - g v₁ = g u₂ - g v₂ ∨ g u₁ - g v₁ = g v₂ - g u₂) →
      s(u₁, v₁) = s(u₂, v₂) := by
  classical
  have hT'_tree : (T.induce (core : Set (Fin (n + 1)))).IsTree :=
    induce_compl_leaves_isTree T hT core
      (Finset.card_pos.mpr ⟨r₀.val, r₀.property⟩) hrem_deg
  have hedge_decomp : ∀ a b : Fin (n + 1), T.Adj a b →
      (∃ t : Fin (Fintype.card ↥(core : Set (Fin (n + 1))) - 1),
        s(a, b) = s((R.ord (R.par ⟨t.val + 1, by omega⟩ (by simp))).val,
                    (R.ord ⟨t.val + 1, by omega⟩).val)) ∨
      (∃ w : {w : Fin (n + 1) // w ∉ core},
        s(a, b) = s(hubOf w.val w.property, w.val)) := by
    intro a b hab
    by_cases ha : a ∈ core <;> by_cases hb : b ∈ core
    · left
      have hadj' : (T.induce (core : Set (Fin (n + 1)))).Adj ⟨a, ha⟩ ⟨b, hb⟩ := hab
      obtain ⟨t, ht⟩ := rootedOrder_surj_edges _ hT'_tree R hadj'
      refine ⟨t, ?_⟩
      rw [Sym2.eq_iff] at ht ⊢
      rcases ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨congrArg Subtype.val h1, congrArg Subtype.val h2⟩
      · exact Or.inr ⟨congrArg Subtype.val h1, congrArg Subtype.val h2⟩
    · right
      obtain ⟨u, _, hu⟩ := degree_eq_one_iff_existsUnique_adj.mp (hrem_deg b hb)
      have ha_eq : a = hubOf b hb :=
        (hu a hab.symm).trans (hu (hubOf b hb) (hhub_adj b hb).symm).symm
      exact ⟨⟨b, hb⟩, by rw [ha_eq]⟩
    · right
      obtain ⟨u, _, hu⟩ := degree_eq_one_iff_existsUnique_adj.mp (hrem_deg a ha)
      have hb_eq : b = hubOf a ha :=
        (hu b hab).trans (hu (hubOf a ha) (hhub_adj a ha).symm).symm
      refine ⟨⟨a, ha⟩, ?_⟩
      rw [hb_eq, Sym2.eq_swap]
    · obtain ⟨u, _, hu⟩ := degree_eq_one_iff_existsUnique_adj.mp (hrem_deg a ha)
      have hb_eq : b = hubOf a ha :=
        (hu b hab).trans (hu (hubOf a ha) (hhub_adj a ha).symm).symm
      exact absurd (hb_eq ▸ hhub_mem a ha) hb
  intro u₁ v₁ u₂ v₂ h1 h2 hdiff
  have hcol : ndColor (g u₁) (g v₁) = ndColor (g u₂) (g v₂) :=
    ndColor_eq_of_sub_eq hdiff
  rcases hedge_decomp u₁ v₁ h1 with ⟨t₁, ht₁⟩ | ⟨w₁, hw₁⟩ <;>
    rcases hedge_decomp u₂ v₂ h2 with ⟨t₂, ht₂⟩ | ⟨w₂, hw₂⟩
  · have hc1 := ndColor_eq_of_sym2_eq g ht₁
    have hc2 := ndColor_eq_of_sym2_eq g ht₂
    have heq_t : t₁ = t₂ := hecCore_inj (hc1.symm.trans (hcol.trans hc2))
    rw [ht₁, ht₂, heq_t]
  · have hc1 := ndColor_eq_of_sym2_eq g ht₁
    have hc2 := ndColor_eq_of_sym2_eq g hw₂
    have hmem : ndColor (g (hubOf w₂.val w₂.property)) (g w₂.val) ∈ C_core := by
      rw [← hc2, ← hcol, hc1]
      exact hecCore_mem t₁
    exact absurd hmem (hecLeaf_notMem w₂)
  · have hc1 := ndColor_eq_of_sym2_eq g hw₁
    have hc2 := ndColor_eq_of_sym2_eq g ht₂
    have hmem : ndColor (g (hubOf w₁.val w₁.property)) (g w₁.val) ∈ C_core := by
      rw [← hc1, hcol, hc2]
      exact hecCore_mem t₂
    exact absurd hmem (hecLeaf_notMem w₁)
  · have hc1 := ndColor_eq_of_sym2_eq g hw₁
    have hc2 := ndColor_eq_of_sym2_eq g hw₂
    have heq_w : w₁ = w₂ := hecLeaf_inj (hc1.symm.trans (hcol.trans hc2))
    rw [hw₁, hw₂, heq_w]

-- ============================================================================
-- Section 3: Subcase 1 — Trees With One Very High Leaf-Degree Vertex
-- ============================================================================

private def leafNbrs {n : ℕ} (T : SimpleGraph (Fin (n + 1))) [DecidableRel T.Adj]
    (v : Fin (n + 1)) : Finset (Fin (n + 1)) :=
  Finset.univ.filter (fun u => T.Adj v u ∧ T.degree u = 1)

private lemma subcase_large_hub {n : ℕ} (hn : 10000 ≤ n)
    (T : SimpleGraph (Fin (n + 1))) [DecidableRel T.Adj] (hT : T.IsTree)
    (v₁ : Fin (n + 1)) (hv₁_deg : 75 * (n / 100) ≤ (leafNbrs T v₁).card) :
    ∃ g : Fin (n + 1) ↪ Fin (2 * n + 1),
      ∀ u₁ v₁' u₂ v₂', T.Adj u₁ v₁' → T.Adj u₂ v₂' →
        (g u₁ - g v₁' = g u₂ - g v₂' ∨ g u₁ - g v₁' = g v₂' - g u₂) →
        s(u₁, v₁') = s(u₂, v₂') := by
  classical
  set q0 := n / 100 with hq0_def
  have hn_div_lb : 100 * q0 ≤ n := Nat.mul_div_le n 100
  have hn_div_ub : n < 100 * q0 + 100 := by
    have := Nat.div_add_mod n 100
    have := Nat.mod_lt n (by positivity : 0 < 100)
    omega
  let M : Finset (Fin (n + 1)) := Finset.univ \ leafNbrs T v₁
  have hv₁_not_leaf : v₁ ∉ leafNbrs T v₁ := by
    simp [leafNbrs]
  have hv₁_M : v₁ ∈ M := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hv₁_not_leaf⟩
  have hM_card_sum : M.card + (leafNbrs T v₁).card = n + 1 := by
    have := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (leafNbrs T v₁))
    simpa [M] using this
  have hM_bound : 3 * M.card + 5 ≤ n := by omega
  have hrem_deg : ∀ w : Fin (n + 1), w ∉ M → T.degree w = 1 := by
    intro w hw
    have hw_in : w ∈ leafNbrs T v₁ := by
      by_contra hnot
      exact hw (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hnot⟩)
    exact (Finset.mem_filter.mp hw_in).2.2
  have hrem_adj : ∀ w : Fin (n + 1), w ∉ M → T.Adj v₁ w := by
    intro w hw
    have hw_in : w ∈ leafNbrs T v₁ := by
      by_contra hnot
      exact hw (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hnot⟩)
    exact (Finset.mem_filter.mp hw_in).2.1
  have hT₁ : (T.induce (M : Set (Fin (n + 1)))).IsTree :=
    induce_compl_leaves_isTree T hT M (Finset.card_pos.mpr ⟨v₁, hv₁_M⟩) hrem_deg
  let r₀ : ↥(M : Set (Fin (n + 1))) := ⟨v₁, hv₁_M⟩
  let R := buildRootedOrder (T.induce (M : Set (Fin (n + 1)))) hT₁ r₀
  set m := Fintype.card ↥(M : Set (Fin (n + 1))) with hm_def
  have hm_eq : m = M.card := card_coe_set_eq M
  have hm_pos : 1 ≤ m := Finset.card_pos.mpr ⟨v₁, hv₁_M⟩ |> fun h => by omega
  have hgreedy : ∀ (k : ℕ) (_hk1 : 1 ≤ k) (hk_le : k ≤ m),
      ∃ f : Fin k → ℕ,
        Function.Injective f ∧
        (∀ hk0 : 0 < k, f ⟨0, hk0⟩ = 0) ∧
        (∀ i : Fin k, f i ≤ n - 1) ∧
        Function.Injective (fun t : Fin (k - 1) =>
          distNat (f ⟨(R.par ⟨t.val + 1, by omega⟩ (by simp)).val,
            lt_trans (R.par_lt ⟨t.val + 1, by omega⟩ (by simp))
              (by simp; omega)⟩)
                  (f ⟨t.val + 1, by omega⟩)) := by
    intro k hk1
    induction k, hk1 using Nat.le_induction with
    | base =>
      intro _
      refine ⟨fun _ => 0, ?_, ?_, ?_, ?_⟩
      · intro a b _; exact Subsingleton.elim a b
      · intro _; rfl
      · intro _; dsimp; omega
      · intro t; exact Fin.elim0 t
    | succ k hk1 ih =>
      intro hk_le
      obtain ⟨f, hfinj, hf0, hfle, hcol_inj⟩ := ih (by omega)
      let pFull := R.par ⟨k, by omega⟩ (by simp; omega)
      have hp_lt : pFull.val < k := R.par_lt ⟨k, by omega⟩ (by simp; omega)
      let p : Fin k := ⟨pFull.val, hp_lt⟩
      let x := f p
      let UsedPos : Finset ℕ := Finset.univ.image f
      let ecPrev : Fin (k - 1) → ℕ := fun t =>
        distNat (f ⟨(R.par ⟨t.val + 1, by omega⟩ (by simp)).val,
          lt_trans (R.par_lt ⟨t.val + 1, by omega⟩ (by simp))
            (by simp; omega)⟩)
                (f ⟨t.val + 1, by omega⟩)
      let UsedCol : Finset ℕ := Finset.univ.image ecPrev
      let BadColPos : Finset ℕ := UsedCol.biUnion (fun c => ({x + c, x - c} : Finset ℕ))
      let Bad : Finset ℕ := UsedPos ∪ BadColPos
      have hUsedPos_card : UsedPos.card ≤ k := by
        calc UsedPos.card ≤ (Finset.univ : Finset (Fin k)).card := Finset.card_image_le
          _ = k := Finset.card_fin k
      have hUsedCol_card : UsedCol.card ≤ k - 1 := by
        calc UsedCol.card ≤ (Finset.univ : Finset (Fin (k - 1))).card := Finset.card_image_le
          _ = k - 1 := Finset.card_fin (k - 1)
      have hBadCol_card : BadColPos.card ≤ 2 * (k - 1) := by
        calc BadColPos.card ≤ ∑ _c ∈ UsedCol, 2 := by
              refine (Finset.card_biUnion_le).trans ?_
              exact Finset.sum_le_sum fun c _ => Finset.card_le_two
          _ = 2 * UsedCol.card := by simp [Nat.mul_comm]
          _ ≤ 2 * (k - 1) := Nat.mul_le_mul_left 2 hUsedCol_card
      have hBad_card : Bad.card < (Finset.Icc 1 (n - 1)).card := by
        have h1 : Bad.card ≤ UsedPos.card + BadColPos.card := Finset.card_union_le _ _
        have h2 : (Finset.Icc 1 (n - 1)).card = n - 1 := by simp
        omega
      have hCand_ne : (Finset.Icc 1 (n - 1) \ Bad).Nonempty :=
        Finset.sdiff_nonempty.mpr (fun hsub =>
          not_le_of_gt hBad_card (Finset.card_le_card hsub))
      let y := (Finset.Icc 1 (n - 1) \ Bad).min' hCand_ne
      have hy_mem : y ∈ Finset.Icc 1 (n - 1) ∧ y ∉ Bad :=
        Finset.mem_sdiff.mp (Finset.min'_mem _ hCand_ne)
      have hy_Icc : 1 ≤ y ∧ y ≤ n - 1 := Finset.mem_Icc.mp hy_mem.1
      have hy_not_pos : y ∉ UsedPos := fun h => hy_mem.2 (Finset.mem_union_left _ h)
      have hy_not_col : ∀ c ∈ UsedCol, distNat x y ≠ c := by
        intro c hc heq
        apply hy_mem.2
        apply Finset.mem_union_right
        refine Finset.mem_biUnion.mpr ⟨c, hc, ?_⟩
        rcases distNat_sols heq with hy_eq | hy_eq
        · exact Finset.mem_insert.mpr (Or.inl hy_eq)
        · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr hy_eq))
      let f' : Fin (k + 1) → ℕ := fun i =>
        if h : i.val < k then f ⟨i.val, h⟩ else y
      refine ⟨f', ?_, ?_, ?_, ?_⟩
      · intro i₁ i₂ heq
        dsimp only [f'] at heq
        by_cases h1 : i₁.val < k <;> by_cases h2 : i₂.val < k
        · rw [dif_pos h1, dif_pos h2] at heq
          have hsub : (⟨i₁.val, h1⟩ : Fin k) = ⟨i₂.val, h2⟩ := hfinj heq
          exact Fin.ext (congrArg (Fin.val : Fin k → ℕ) hsub)
        · rw [dif_pos h1, dif_neg h2] at heq
          exact absurd (heq ▸ Finset.mem_image_of_mem f (Finset.mem_univ (⟨i₁.val, h1⟩ : Fin k))) hy_not_pos
        · rw [dif_neg h1, dif_pos h2] at heq
          exact absurd (heq.symm ▸ Finset.mem_image_of_mem f (Finset.mem_univ (⟨i₂.val, h2⟩ : Fin k))) hy_not_pos
        · exact Fin.ext (by omega)
      · intro _
        dsimp only [f']
        rw [dif_pos (by omega)]
        exact hf0 (by omega)
      · intro i
        dsimp only [f']
        split_ifs with h
        · exact hfle ⟨i.val, h⟩
        · exact hy_Icc.2
      · intro t₁ t₂ heq
        dsimp only [f'] at heq
        have hpar_lt_k : ∀ t : Fin k,
            (R.par ⟨t.val + 1, by omega⟩ (by simp)).val < k := by
          intro t
          have := R.par_lt ⟨t.val + 1, by omega⟩ (by simp)
          simp at this; omega
        by_cases ht1 : t₁.val + 1 < k <;> by_cases ht2 : t₂.val + 1 < k
        · rw [dif_pos (hpar_lt_k ⟨t₁.val, by omega⟩), dif_pos ht1,
              dif_pos (hpar_lt_k ⟨t₂.val, by omega⟩), dif_pos ht2] at heq
          have hsub : (⟨t₁.val, by omega⟩ : Fin (k - 1)) = ⟨t₂.val, by omega⟩ :=
            @hcol_inj ⟨t₁.val, by omega⟩ ⟨t₂.val, by omega⟩ heq
          exact Fin.ext (congrArg (Fin.val : Fin (k - 1) → ℕ) hsub)
        · have ht2_eq : t₂.val + 1 = k := by omega
          rw [dif_pos (hpar_lt_k ⟨t₁.val, by omega⟩), dif_pos ht1,
              dif_pos (hpar_lt_k ⟨t₂.val, by omega⟩), dif_neg ht2] at heq
          have hpar2_eq : (⟨(R.par ⟨t₂.val + 1, by omega⟩ (by simp)).val,
              hpar_lt_k ⟨t₂.val, by omega⟩⟩ : Fin k) = p := by
            apply Fin.ext; dsimp [p, pFull]; congr 2; exact Fin.ext ht2_eq
          rw [hpar2_eq] at heq
          have hmem_col : ecPrev ⟨t₁.val, by omega⟩ ∈ UsedCol :=
            Finset.mem_image_of_mem ecPrev (Finset.mem_univ (⟨t₁.val, by omega⟩ : Fin (k - 1)))
          exact absurd heq.symm (hy_not_col _ hmem_col)
        · have ht1_eq : t₁.val + 1 = k := by omega
          rw [dif_pos (hpar_lt_k ⟨t₁.val, by omega⟩), dif_neg ht1,
              dif_pos (hpar_lt_k ⟨t₂.val, by omega⟩), dif_pos ht2] at heq
          have hpar1_eq : (⟨(R.par ⟨t₁.val + 1, by omega⟩ (by simp)).val,
              hpar_lt_k ⟨t₁.val, by omega⟩⟩ : Fin k) = p := by
            apply Fin.ext; dsimp [p, pFull]; congr 2; exact Fin.ext ht1_eq
          rw [hpar1_eq] at heq
          have hmem_col : ecPrev ⟨t₂.val, by omega⟩ ∈ UsedCol :=
            Finset.mem_image_of_mem ecPrev (Finset.mem_univ (⟨t₂.val, by omega⟩ : Fin (k - 1)))
          exact absurd heq (hy_not_col _ hmem_col)
        · exact Fin.ext (by omega)
  obtain ⟨f, hfinj, hf0, hfle, hcol_inj⟩ := hgreedy m hm_pos (le_refl m)
  let ecCoreNat : Fin (m - 1) → ℕ := fun t =>
    distNat (f (R.par ⟨t.val + 1, by omega⟩ (by simp))) (f ⟨t.val + 1, by omega⟩)
  have hecCoreNat_inj : Function.Injective ecCoreNat := hcol_inj
  let C_core : Finset ℕ := Finset.univ.image ecCoreNat
  have hC_core_sub : C_core ⊆ Finset.Icc 1 n := by
    intro c hc
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hc
    refine Finset.mem_Icc.mpr ⟨?_, ?_⟩
    · apply distNat_pos_of_ne
      intro heq
      have hfeq := hfinj heq
      have hlt := R.par_lt ⟨t.val + 1, by omega⟩ (by simp)
      rw [hfeq] at hlt
      omega
    · have h1 := hfle (R.par ⟨t.val + 1, by omega⟩ (by simp))
      have h2 := hfle ⟨t.val + 1, by omega⟩
      dsimp [ecCoreNat, distNat]; omega
  have hC_core_card : C_core.card = m - 1 := by
    rw [Finset.card_image_of_injective _ hecCoreNat_inj, Finset.card_fin]
  set C_rem : Finset ℕ := Finset.Icc 1 n \ C_core
  have hC_rem_card : C_rem.card = (leafNbrs T v₁).card := by
    have h1 : C_rem.card + C_core.card = (Finset.Icc 1 n).card :=
      Finset.card_sdiff_add_card_eq_card hC_core_sub
    have h2 : (Finset.Icc 1 n).card = n := by simp
    omega
  have hcompl_card : Fintype.card {w : Fin (n + 1) // w ∉ M} = Fintype.card ↥C_rem := by
    have h1 : Fintype.card {w : Fin (n + 1) // w ∉ M} = Fintype.card ↥(leafNbrs T v₁) :=
      Fintype.card_congr
        { toFun := fun w => ⟨w.val, by
            by_contra hnot
            exact w.property (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hnot⟩)⟩
          invFun := fun w => ⟨w.val, fun hM => (Finset.mem_sdiff.mp hM).2 w.property⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
    rw [h1, Fintype.card_coe, Fintype.card_coe, hC_rem_card]
  let bijLeaf : {w : Fin (n + 1) // w ∉ M} ≃ ↥C_rem :=
    Fintype.equivOfCardEq hcompl_card
  let gNat : Fin (n + 1) → ℕ := fun u =>
    if hu : u ∈ M then f (R.ord.symm ⟨u, hu⟩) else 2 * n + 1 - (bijLeaf ⟨u, hu⟩).val
  have hgNat_lt : ∀ u, gNat u < 2 * n + 1 := by
    intro u
    dsimp only [gNat]
    split_ifs with hu
    · have := hfle (R.ord.symm ⟨u, hu⟩); omega
    · have hc := (Finset.mem_Icc.mp (Finset.mem_sdiff.mp (bijLeaf ⟨u, hu⟩).property).1)
      omega
  have hgNat_inj : Function.Injective gNat := by
    intro u₁ u₂ heq
    dsimp only [gNat] at heq
    by_cases h1 : u₁ ∈ M <;> by_cases h2 : u₂ ∈ M
    · rw [dif_pos h1, dif_pos h2] at heq
      have := R.ord.symm.injective (hfinj heq)
      exact congrArg Subtype.val this
    · rw [dif_pos h1, dif_neg h2] at heq
      have ha := hfle (R.ord.symm ⟨u₁, h1⟩)
      have hc := (Finset.mem_Icc.mp (Finset.mem_sdiff.mp (bijLeaf ⟨u₂, h2⟩).property).1)
      omega
    · rw [dif_neg h1, dif_pos h2] at heq
      have ha := hfle (R.ord.symm ⟨u₂, h2⟩)
      have hc := (Finset.mem_Icc.mp (Finset.mem_sdiff.mp (bijLeaf ⟨u₁, h1⟩).property).1)
      omega
    · rw [dif_neg h1, dif_neg h2] at heq
      have hc1 := (Finset.mem_Icc.mp (Finset.mem_sdiff.mp (bijLeaf ⟨u₁, h1⟩).property).1)
      have hc2 := (Finset.mem_Icc.mp (Finset.mem_sdiff.mp (bijLeaf ⟨u₂, h2⟩).property).1)
      have hc_eq : (bijLeaf ⟨u₁, h1⟩).val = (bijLeaf ⟨u₂, h2⟩).val := by omega
      have hsub := bijLeaf.injective (Subtype.ext hc_eq)
      exact congrArg Subtype.val hsub
  let g : Fin (n + 1) ↪ Fin (2 * n + 1) :=
    ⟨fun u => ⟨gNat u, hgNat_lt u⟩, fun u₁ u₂ h => hgNat_inj (congrArg Fin.val h)⟩
  have hg_v₁ : g v₁ = ⟨0, by omega⟩ := by
    apply Fin.ext
    change gNat v₁ = 0
    dsimp only [gNat]
    rw [dif_pos hv₁_M]
    have hsymm : R.ord.symm ⟨v₁, hv₁_M⟩ = ⟨0, by omega⟩ := by
      apply R.ord.injective
      rw [R.ord.apply_symm_apply]
      exact R.root_eq.symm
    rw [hsymm]
    exact hf0 (by omega)
  have hecCore_eq : ∀ t : Fin (m - 1),
      ndColor (g (R.ord (R.par ⟨t.val + 1, by omega⟩ (by simp))).val)
              (g (R.ord ⟨t.val + 1, by omega⟩).val) = ecCoreNat t := by
    intro t
    let aIdx := R.par ⟨t.val + 1, by omega⟩ (by simp)
    let bIdx : Fin m := ⟨t.val + 1, by omega⟩
    have ha_M : (R.ord aIdx).val ∈ M := (R.ord aIdx).property
    have hb_M : (R.ord bIdx).val ∈ M := (R.ord bIdx).property
    have ha_eq : gNat (R.ord aIdx).val = f aIdx := by
      dsimp only [gNat]
      rw [dif_pos ha_M]
      simp
    have hb_eq : gNat (R.ord bIdx).val = f bIdx := by
      dsimp only [gNat]
      rw [dif_pos hb_M]
      simp
    change ndColor ⟨gNat (R.ord aIdx).val, _⟩ ⟨gNat (R.ord bIdx).val, _⟩ = distNat (f aIdx) (f bIdx)
    have hne : f aIdx ≠ f bIdx := by
      intro heq
      have hfeq := hfinj heq
      have hlt := R.par_lt bIdx (by simp [bIdx])
      change aIdx.val < bIdx.val at hlt
      rw [hfeq] at hlt
      omega
    have hle1 := hfle aIdx
    have hle2 := hfle bIdx
    have hdist_le : distNat (f aIdx) (f bIdx) ≤ n := by dsimp [distNat]; omega
    have := ndColor_eq_distNat (n := n) (a := gNat (R.ord aIdx).val) (b := gNat (R.ord bIdx).val)
      (hgNat_lt _) (hgNat_lt _) (by rw [ha_eq, hb_eq]; exact hne) (by rw [ha_eq, hb_eq]; exact hdist_le)
    rw [this, ha_eq, hb_eq]
  have hecLeaf_eq : ∀ w : {w : Fin (n + 1) // w ∉ M},
      ndColor (g v₁) (g w.val) = (bijLeaf w).val := by
    intro w
    rw [hg_v₁]
    have hw_g : g w.val = ⟨2 * n + 1 - (bijLeaf w).val, by
        have hc := Finset.mem_Icc.mp (Finset.mem_sdiff.mp (bijLeaf w).property).1
        omega⟩ := by
      apply Fin.ext
      change gNat w.val = _
      dsimp only [gNat]
      rw [dif_neg w.property]
    rw [hw_g]
    have hc := Finset.mem_Icc.mp (Finset.mem_sdiff.mp (bijLeaf w).property).1
    exact ndColor_zero_wrap hc.1 hc.2
  refine ⟨g, rainbow_of_core_and_leaves T hT M r₀ R (fun _ _ => v₁)
    (fun _ _ => hv₁_M) hrem_deg hrem_adj g C_core ?_ ?_ ?_ ?_⟩
  · intro t
    rw [hecCore_eq t]
    exact Finset.mem_image_of_mem ecCoreNat (Finset.mem_univ t)
  · intro t₁ t₂ heq
    dsimp only at heq
    rw [hecCore_eq t₁, hecCore_eq t₂] at heq
    exact hecCoreNat_inj heq
  · intro w
    rw [hecLeaf_eq w]
    exact (Finset.mem_sdiff.mp (bijLeaf w).property).2
  · intro w₁ w₂ heq
    dsimp only at heq
    rw [hecLeaf_eq w₁, hecLeaf_eq w₂] at heq
    exact bijLeaf.injective (Subtype.ext heq)

-- ============================================================================
-- Section 4: Controlled Embedding of the Pruned Core Tree (MPS Lemma 7.1)
-- ============================================================================

private def pickModPoint (M x b r₀ : ℕ) : ℕ :=
  if x < b then
    b + (M + r₀ - (b - x) % M) % M
  else
    b + (M + (x - b) % M - r₀) % M

private lemma pickModPoint_spec {M x b r₀ : ℕ} (hM : 0 < M) (hr₀ : r₀ < M)
    (hx : x < b ∨ b + M ≤ x) :
    pickModPoint M x b r₀ ∈ Finset.Ico b (b + M) ∧
    distNat x (pickModPoint M x b r₀) % M = r₀ := by
  dsimp only [pickModPoint]
  rcases hx with hlt | hge
  · rw [if_pos hlt]
    set u := (b - x) % M
    have hu : u < M := Nat.mod_lt _ hM
    set δ := (M + r₀ - u) % M
    have hδ : δ < M := Nat.mod_lt _ hM
    refine ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩, ?_⟩
    have hdist : distNat x (b + δ) = (b - x) + δ := by dsimp [distNat]; omega
    rw [hdist, Nat.add_mod]
    change (u + δ % M) % M = r₀
    rw [Nat.mod_eq_of_lt hδ]
    by_cases hru : u ≤ r₀
    · have hmr : M + r₀ - u = M + (r₀ - u) := by omega
      have hd_eq : δ = r₀ - u := by
        dsimp [δ]; rw [hmr, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
      rw [hd_eq]
      have : u + (r₀ - u) = r₀ := by omega
      rw [this, Nat.mod_eq_of_lt hr₀]
    · have hd_eq : δ = M + r₀ - u := by
        dsimp [δ]; exact Nat.mod_eq_of_lt (by omega)
      rw [hd_eq]
      have : u + (M + r₀ - u) = M + r₀ := by omega
      rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt hr₀]
  · rw [if_neg (by omega)]
    set v := (x - b) % M
    have hv : v < M := Nat.mod_lt _ hM
    set δ := (M + v - r₀) % M
    have hδ : δ < M := Nat.mod_lt _ hM
    refine ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩, ?_⟩
    have hdist : distNat x (b + δ) = (x - b) - δ := by dsimp [distNat]; omega
    rw [hdist]
    set q := (x - b) / M
    have hq : 1 ≤ q := Nat.div_pos (by omega : M ≤ x - b) hM
    have hdiv : M * q + v = x - b := Nat.div_add_mod (x - b) M
    by_cases hrv : r₀ ≤ v
    · have hd_eq : δ = v - r₀ := by
        dsimp [δ]
        have : M + v - r₀ = M + (v - r₀) := by omega
        rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
      have hsub : (x - b) - δ = r₀ + M * q := by
        rw [← hdiv, hd_eq]; omega
      rw [hsub, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr₀]
    · have hd_eq : δ = M + v - r₀ := by
        dsimp [δ]; exact Nat.mod_eq_of_lt (by omega)
      have hmq : M * q = M + M * (q - 1) := by
        rcases Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0) with ⟨q', hq'⟩
        rw [hq']; simp [Nat.mul_succ]; ring
      have hsub : (x - b) - δ = r₀ + M * (q - 1) := by
        rw [← hdiv, hmq, hd_eq]; omega
      rw [hsub, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr₀]

private structure SmallTreeResult {n : ℕ}
    (T : SimpleGraph (Fin (n + 1))) [DecidableRel T.Adj]
    (core V_0 V_1 V_2 : Finset (Fin (n + 1)))
    (r₀ : ↥(core : Set (Fin (n + 1)))) (L : ℕ) where
  R : RootedOrder (T.induce (core : Set (Fin (n + 1)))) r₀
  posCore : ↥(core : Set (Fin (n + 1))) → ℕ
  posCore_inj : Function.Injective posCore
  pos_V0 : ∀ x : ↥(core : Set (Fin (n + 1))), x.val ∈ V_0 →
    posCore x ∈ Finset.Ico (90 * (n / 100)) (97 * (n / 100))
  z : Fin V_1.card ≃ ↥V_1
  z_mem_core : ∀ q : Fin V_1.card, (z q).val ∈ core
  pos_z : ∀ q : Fin V_1.card,
    posCore ⟨(z q).val, z_mem_core q⟩ ∈
      Finset.Ico (77 * (n / 100) + q.val * (8 * L)) (77 * (n / 100) + q.val * (8 * L) + 8 * L)
  w : Fin V_2.card ≃ ↥V_2
  w_mem_core : ∀ q : Fin V_2.card, (w q).val ∈ core
  pos_w : ∀ q : Fin V_2.card,
    posCore ⟨(w q).val, w_mem_core q⟩ ∈
      Finset.Ico (98 * (n / 100) + q.val * (8 * L)) (98 * (n / 100) + q.val * (8 * L) + 8 * L)
  C_core : Finset ℕ
  C_core_sub : C_core ⊆ Finset.Icc 1 n
  C_core_card : C_core.card = Fintype.card ↥(core : Set (Fin (n + 1))) - 1
  ecCore_mem : ∀ t : Fin (Fintype.card ↥(core : Set (Fin (n + 1))) - 1),
    distNat (posCore (R.ord (R.par ⟨t.val + 1, by omega⟩ (by simp))))
            (posCore (R.ord ⟨t.val + 1, by omega⟩)) ∈ C_core
  ecCore_inj : Function.Injective
    (fun t : Fin (Fintype.card ↥(core : Set (Fin (n + 1))) - 1) =>
      distNat (posCore (R.ord (R.par ⟨t.val + 1, by omega⟩ (by simp))))
              (posCore (R.ord ⟨t.val + 1, by omega⟩)))

private lemma subIco_disj {base L m : ℕ} {j₁ j₂ : Fin m} {y : ℕ}
    (h1 : y ∈ Finset.Ico (base + j₁.val * (8 * L)) (base + j₁.val * (8 * L) + 8 * L))
    (h2 : y ∈ Finset.Ico (base + j₂.val * (8 * L)) (base + j₂.val * (8 * L) + 8 * L)) :
    j₁ = j₂ := by
  have h1' := Finset.mem_Ico.mp h1
  have h2' := Finset.mem_Ico.mp h2
  by_contra hne
  rcases lt_trichotomy j₁.val j₂.val with hlt | heq | hgt
  · have hstep_mul : j₁.val * (8 * L) + 8 * L ≤ j₂.val * (8 * L) := by
      calc j₁.val * (8 * L) + 8 * L = (j₁.val + 1) * (8 * L) := (Nat.succ_mul _ _).symm
        _ ≤ j₂.val * (8 * L) := Nat.mul_le_mul_right _ hlt
    omega
  · exact hne (Fin.ext heq)
  · have hstep_mul : j₂.val * (8 * L) + 8 * L ≤ j₁.val * (8 * L) := by
      calc j₂.val * (8 * L) + 8 * L = (j₂.val + 1) * (8 * L) := (Nat.succ_mul _ _).symm
        _ ≤ j₁.val * (8 * L) := Nat.mul_le_mul_right _ hgt
    omega

private lemma free_subinterval_choice {base L m : ℕ} (hL : 0 < L)
    (F : Finset (Fin m)) (UsedCol : Finset ℕ) (x r₀ : ℕ)
    (hr₀ : r₀ < 4 * L)
    (hx_out : x ∉ F.biUnion (fun j =>
      Finset.Ico (base + j.val * (8 * L)) (base + j.val * (8 * L) + 8 * L)))
    (hcol_lt : (UsedCol.filter (fun c => c % (4 * L) = r₀)).card < F.card) :
    ∃ j ∈ F, ∃ y ∈ Finset.Ico (base + j.val * (8 * L)) (base + j.val * (8 * L) + 8 * L),
      distNat x y % (4 * L) = r₀ ∧ distNat x y ∉ UsedCol := by
  classical
  let cand : Fin m × Bool → ℕ := fun jb =>
    pickModPoint (4 * L) x (base + jb.1.val * (8 * L) + (if jb.2 then 4 * L else 0)) r₀
  let Dom : Finset (Fin m × Bool) := F ×ˢ Finset.univ
  have hcand_spec : ∀ jb ∈ Dom,
      cand jb ∈ Finset.Ico (base + jb.1.val * (8 * L)) (base + jb.1.val * (8 * L) + 8 * L) ∧
      distNat x (cand jb) % (4 * L) = r₀ := by
    intro jb hjb
    have hjF : jb.1 ∈ F := (Finset.mem_product.mp hjb).1
    have hx_not_j := (Finset.mem_Ico (a := base + jb.1.val * (8 * L))
      (b := base + jb.1.val * (8 * L) + 8 * L) (x := x)).not.mp
      (fun h => hx_out (Finset.mem_biUnion.mpr ⟨jb.1, hjF, h⟩))
    set b0 := base + jb.1.val * (8 * L) + (if jb.2 then 4 * L else 0) with hb0_def
    have hxb0 : x < b0 ∨ b0 + 4 * L ≤ x := by
      cases hbool : jb.2 <;> simp [hb0_def, hbool] <;> omega
    have hsp := pickModPoint_spec (M := 4 * L) (x := x) (b := b0) (r₀ := r₀)
      (by omega) hr₀ hxb0
    refine ⟨?_, hsp.2⟩
    have hIco := Finset.mem_Ico.mp hsp.1
    change pickModPoint (4 * L) x b0 r₀ ∈
      Finset.Ico (base + jb.1.val * (8 * L)) (base + jb.1.val * (8 * L) + 8 * L)
    refine Finset.mem_Ico.mpr ?_
    rw [hb0_def] at hIco ⊢
    cases hbool : jb.2 <;> simp [hbool] at hIco ⊢ <;> omega
  have hcand_inj : Set.InjOn cand (Dom : Set (Fin m × Bool)) := by
    intro jb1 h1 jb2 h2 heq
    have hs1 := (hcand_spec jb1 h1).1
    have hs2 := heq ▸ (hcand_spec jb2 h2).1
    have hj_eq : jb1.1 = jb2.1 := subIco_disj hs1 hs2
    have hb_eq : jb1.2 = jb2.2 := by
      by_contra hbne
      set b1 := base + jb1.1.val * (8 * L) + (if jb1.2 then 4 * L else 0) with hb1_def
      set b2 := base + jb2.1.val * (8 * L) + (if jb2.2 then 4 * L else 0) with hb2_def
      have hI1 : cand jb1 ∈ Finset.Ico b1 (b1 + 4 * L) := by
        have hjF : jb1.1 ∈ F := (Finset.mem_product.mp h1).1
        have hx_not_j := (Finset.mem_Ico (a := base + jb1.1.val * (8 * L))
          (b := base + jb1.1.val * (8 * L) + 8 * L) (x := x)).not.mp
          (fun h => hx_out (Finset.mem_biUnion.mpr ⟨jb1.1, hjF, h⟩))
        have hxb : x < b1 ∨ b1 + 4 * L ≤ x := by
          cases hbool : jb1.2 <;> simp [hb1_def, hbool] <;> omega
        exact (pickModPoint_spec (by omega) hr₀ hxb).1
      have hI2 : cand jb2 ∈ Finset.Ico b2 (b2 + 4 * L) := by
        have hjF : jb2.1 ∈ F := (Finset.mem_product.mp h2).1
        have hx_not_j := (Finset.mem_Ico (a := base + jb2.1.val * (8 * L))
          (b := base + jb2.1.val * (8 * L) + 8 * L) (x := x)).not.mp
          (fun h => hx_out (Finset.mem_biUnion.mpr ⟨jb2.1, hjF, h⟩))
        have hxb : x < b2 ∨ b2 + 4 * L ≤ x := by
          cases hbool : jb2.2 <;> simp [hb2_def, hbool] <;> omega
        exact (pickModPoint_spec (by omega) hr₀ hxb).1
      rw [heq] at hI1
      have h1' := Finset.mem_Ico.mp hI1
      have h2' := Finset.mem_Ico.mp hI2
      rw [hb1_def, hj_eq] at h1'
      rw [hb2_def] at h2'
      cases hjb1 : jb1.2 <;> cases hjb2 : jb2.2
      · exact hbne (hjb1.trans hjb2.symm)
      · simp [hjb1, hjb2] at h1' h2'; omega
      · simp [hjb1, hjb2] at h1' h2'; omega
      · exact hbne (hjb1.trans hjb2.symm)
    exact Prod.ext hj_eq hb_eq
  let CandSet := Dom.image cand
  have hCand_card : CandSet.card = 2 * F.card := by
    rw [Finset.card_image_of_injOn hcand_inj, Finset.card_product, Finset.card_univ,
        Fintype.card_bool, Nat.mul_comm]
  set UsedS := UsedCol.filter (fun c => c % (4 * L) = r₀)
  let BadS := UsedS.biUnion (fun c => ({x + c, x - c} : Finset ℕ))
  have hBadS_card : BadS.card < CandSet.card := by
    have hle : BadS.card ≤ 2 * UsedS.card := by
      calc BadS.card ≤ ∑ _c ∈ UsedS, 2 :=
            (Finset.card_biUnion_le).trans (Finset.sum_le_sum fun _ _ => Finset.card_le_two)
        _ = 2 * UsedS.card := by simp [Nat.mul_comm]
    omega
  have hne : (CandSet \ BadS).Nonempty :=
    Finset.sdiff_nonempty.mpr (fun hsub => not_le_of_gt hBadS_card (Finset.card_le_card hsub))
  obtain ⟨y, hy⟩ := hne
  obtain ⟨hy_cand, hy_not_bad⟩ := Finset.mem_sdiff.mp hy
  obtain ⟨jb, hjb_dom, rfl⟩ := Finset.mem_image.mp hy_cand
  have hjF : jb.1 ∈ F := (Finset.mem_product.mp hjb_dom).1
  have hsp := hcand_spec jb hjb_dom
  refine ⟨jb.1, hjF, cand jb, hsp.1, hsp.2, ?_⟩
  intro hmem_col
  apply hy_not_bad
  refine Finset.mem_biUnion.mpr ⟨distNat x (cand jb),
    Finset.mem_filter.mpr ⟨hmem_col, hsp.2⟩, ?_⟩
  rcases distNat_sols (rfl : distNat x (cand jb) = distNat x (cand jb)) with hsol | hsol
  · exact Finset.mem_insert.mpr (Or.inl hsol)
  · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr hsol))

private lemma small_tree_step {n L : ℕ}
    (hL : 16384 ≤ L) (hq0 : 10000000000 ≤ n / 100)
    (T : SimpleGraph (Fin (n + 1))) [DecidableRel T.Adj]
    (core V_0 V_1 V_2 : Finset (Fin (n + 1)))
    (hcore_le : core.card ≤ n / 100)
    (hpart : ∀ x ∈ core, (x ∈ V_0 ∧ x ∉ V_1 ∧ x ∉ V_2) ∨
                         (x ∉ V_0 ∧ x ∈ V_1 ∧ x ∉ V_2) ∨
                         (x ∉ V_0 ∧ x ∉ V_1 ∧ x ∈ V_2))
    (hV1_width : V_1.card * (8 * L) ≤ n / 100)
    (hV2_width : V_2.card * (8 * L) ≤ n / 100)
    (hV1_pow : V_1.card < 2 ^ (L - 2))
    (hV2_pow : V_2.card < 2 ^ (L - 2))
    (r₀ : ↥(core : Set (Fin (n + 1))))
    (R : RootedOrder (T.induce (core : Set (Fin (n + 1)))) r₀) :
    ∀ (k : ℕ) (_hk1 : 1 ≤ k) (hk_le : k ≤ Fintype.card ↥(core : Set (Fin (n + 1)))),
      ∃ (f : Fin k → ℕ) (U1 : Finset (Fin V_1.card)) (U2 : Finset (Fin V_2.card)),
        Function.Injective f ∧
        (∀ i : Fin k, (R.ord ⟨i.val, by omega⟩).val ∈ V_0 →
          f i ∈ Finset.Ico (90 * (n / 100)) (97 * (n / 100))) ∧
        (∀ i : Fin k, (R.ord ⟨i.val, by omega⟩).val ∈ V_1 →
          ∃ j ∈ U1, f i ∈
            Finset.Ico (77 * (n / 100) + j.val * (8 * L))
                       (77 * (n / 100) + j.val * (8 * L) + 8 * L)) ∧
        (∀ i : Fin k, (R.ord ⟨i.val, by omega⟩).val ∈ V_2 →
          ∃ j ∈ U2, f i ∈
            Finset.Ico (98 * (n / 100) + j.val * (8 * L))
                       (98 * (n / 100) + j.val * (8 * L) + 8 * L)) ∧
        (∀ i₁ i₂ : Fin k, ∀ j : Fin V_1.card,
          f i₁ ∈ Finset.Ico (77 * (n / 100) + j.val * (8 * L))
                            (77 * (n / 100) + j.val * (8 * L) + 8 * L) →
          f i₂ ∈ Finset.Ico (77 * (n / 100) + j.val * (8 * L))
                            (77 * (n / 100) + j.val * (8 * L) + 8 * L) →
          i₁ = i₂) ∧
        (∀ i₁ i₂ : Fin k, ∀ j : Fin V_2.card,
          f i₁ ∈ Finset.Ico (98 * (n / 100) + j.val * (8 * L))
                            (98 * (n / 100) + j.val * (8 * L) + 8 * L) →
          f i₂ ∈ Finset.Ico (98 * (n / 100) + j.val * (8 * L))
                            (98 * (n / 100) + j.val * (8 * L) + 8 * L) →
          i₁ = i₂) ∧
        U1.card = (Finset.univ.filter (fun i : Fin k => (R.ord ⟨i.val, by omega⟩).val ∈ V_1)).card ∧
        U2.card = (Finset.univ.filter (fun i : Fin k => (R.ord ⟨i.val, by omega⟩).val ∈ V_2)).card ∧
        Function.Injective (fun t : Fin (k - 1) =>
          distNat (f ⟨(R.par ⟨t.val + 1, by omega⟩ (by simp)).val,
            lt_trans (R.par_lt ⟨t.val + 1, by omega⟩ (by simp)) (by simp; omega)⟩)
                  (f ⟨t.val + 1, by omega⟩)) ∧
        (∀ s < L, ((Finset.univ.image (fun t : Fin (k - 1) =>
            distNat (f ⟨(R.par ⟨t.val + 1, by omega⟩ (by simp)).val,
              lt_trans (R.par_lt ⟨t.val + 1, by omega⟩ (by simp)) (by simp; omega)⟩)
                    (f ⟨t.val + 1, by omega⟩))).filter
            (fun c => c % (4 * L) = 2 * s)).card ≤ V_1.card / 2 ^ s - (V_1.card - U1.card)) ∧
        (∀ s < L, ((Finset.univ.image (fun t : Fin (k - 1) =>
            distNat (f ⟨(R.par ⟨t.val + 1, by omega⟩ (by simp)).val,
              lt_trans (R.par_lt ⟨t.val + 1, by omega⟩ (by simp)) (by simp; omega)⟩)
                    (f ⟨t.val + 1, by omega⟩))).filter
            (fun c => c % (4 * L) = 2 * (L + s))).card ≤ V_2.card / 2 ^ s - (V_2.card - U2.card)) := by
  classical
  set q0 := n / 100 with hq0_def
  set mCore := Fintype.card ↥(core : Set (Fin (n + 1))) with hmCore_def
  have hmCore_eq : mCore = core.card := card_coe_set_eq core
  have hmCore_pos : 1 ≤ mCore := Fintype.card_pos_iff.mpr ⟨r₀⟩
  let sub1 : Fin V_1.card → Finset ℕ := fun j =>
    Finset.Ico (77 * q0 + j.val * (8 * L)) (77 * q0 + j.val * (8 * L) + 8 * L)
  let sub2 : Fin V_2.card → Finset ℕ := fun j =>
    Finset.Ico (98 * q0 + j.val * (8 * L)) (98 * q0 + j.val * (8 * L) + 8 * L)
  let I0 : Finset ℕ := Finset.Ico (90 * q0) (97 * q0)
  have hsub1_in : ∀ (j : Fin V_1.card) {y : ℕ}, y ∈ sub1 j →
      77 * q0 ≤ y ∧ y < 78 * q0 := by
    intro j y hy
    have hy' := Finset.mem_Ico.mp hy
    have hj : j.val * (8 * L) + 8 * L ≤ V_1.card * (8 * L) := by
      calc j.val * (8 * L) + 8 * L = (j.val + 1) * (8 * L) := (Nat.succ_mul _ _).symm
        _ ≤ V_1.card * (8 * L) := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt j.isLt)
    omega
  have hsub2_in : ∀ (j : Fin V_2.card) {y : ℕ}, y ∈ sub2 j →
      98 * q0 ≤ y ∧ y < 99 * q0 := by
    intro j y hy
    have hy' := Finset.mem_Ico.mp hy
    have hj : j.val * (8 * L) + 8 * L ≤ V_2.card * (8 * L) := by
      calc j.val * (8 * L) + 8 * L = (j.val + 1) * (8 * L) := (Nat.succ_mul _ _).symm
        _ ≤ V_2.card * (8 * L) := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt j.isLt)
    omega
  intro k hk1
  induction k, hk1 using Nat.le_induction with
  | base =>
    intro hk_le
    let v0 := (R.ord ⟨0, hmCore_pos⟩).val
    have hv0_core : v0 ∈ core := (R.ord ⟨0, hmCore_pos⟩).property
    have hi0_val : ∀ i : Fin 1, (R.ord ⟨i.val, by omega⟩).val = v0 := by
      intro i
      have hi0 : i.val = 0 := by omega
      dsimp only [v0]
      congr 2
      exact Fin.ext hi0
    rcases hpart v0 hv0_core with ⟨hv0, hv1n, hv2n⟩ | ⟨hv0n, hv1, hv2n⟩ | ⟨hv0n, hv1n, hv2⟩
    · refine ⟨fun _ => 90 * q0, ∅, ∅, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro a b _; exact Subsingleton.elim a b
      · intro _ _; dsimp only; exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
      · intro i hi; rw [hi0_val i] at hi; exact absurd hi hv1n
      · intro i hi; rw [hi0_val i] at hi; exact absurd hi hv2n
      · intro i₁ i₂ _ _ _; exact Subsingleton.elim i₁ i₂
      · intro i₁ i₂ _ _ _; exact Subsingleton.elim i₁ i₂
      · symm; rw [Finset.card_empty, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro i _; rw [hi0_val i]; exact hv1n
      · symm; rw [Finset.card_empty, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro i _; rw [hi0_val i]; exact hv2n
      · intro t; exact Fin.elim0 t
      · intro _ _; simp
      · intro _ _; simp
    · have hV1_pos : 0 < V_1.card := Finset.card_pos.mpr ⟨v0, hv1⟩
      let j0 : Fin V_1.card := ⟨0, hV1_pos⟩
      refine ⟨fun _ => 77 * q0, {j0}, ∅, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro a b _; exact Subsingleton.elim a b
      · intro i hi; rw [hi0_val i] at hi; exact absurd hi hv0n
      · intro _ _; refine ⟨j0, Finset.mem_singleton_self _, Finset.mem_Ico.mpr ⟨?_, ?_⟩⟩
        · simp only [j0, Nat.zero_mul, Nat.add_zero]; omega
        · simp only [j0, Nat.zero_mul, Nat.add_zero]; omega
      · intro i hi; rw [hi0_val i] at hi; exact absurd hi hv2n
      · intro i₁ i₂ _ _ _; exact Subsingleton.elim i₁ i₂
      · intro i₁ i₂ _ _ _; exact Subsingleton.elim i₁ i₂
      · have hflt : (Finset.univ.filter (fun i : Fin 1 =>
            (R.ord ⟨i.val, by omega⟩).val ∈ V_1)) = Finset.univ := by
          ext i
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
          rw [hi0_val i]; exact hv1
        rw [hflt]; simp
      · symm; rw [Finset.card_empty, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro i _; rw [hi0_val i]; exact hv2n
      · intro t; exact Fin.elim0 t
      · intro _ _; simp
      · intro _ _; simp
    · have hV2_pos : 0 < V_2.card := Finset.card_pos.mpr ⟨v0, hv2⟩
      let j0 : Fin V_2.card := ⟨0, hV2_pos⟩
      refine ⟨fun _ => 98 * q0, ∅, {j0}, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro a b _; exact Subsingleton.elim a b
      · intro i hi; rw [hi0_val i] at hi; exact absurd hi hv0n
      · intro i hi; rw [hi0_val i] at hi; exact absurd hi hv1n
      · intro _ _; refine ⟨j0, Finset.mem_singleton_self _, Finset.mem_Ico.mpr ⟨?_, ?_⟩⟩
        · simp only [j0, Nat.zero_mul, Nat.add_zero]; omega
        · simp only [j0, Nat.zero_mul, Nat.add_zero]; omega
      · intro i₁ i₂ _ _ _; exact Subsingleton.elim i₁ i₂
      · intro i₁ i₂ _ _ _; exact Subsingleton.elim i₁ i₂
      · symm; rw [Finset.card_empty, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro i _; rw [hi0_val i]; exact hv1n
      · have hflt : (Finset.univ.filter (fun i : Fin 1 =>
            (R.ord ⟨i.val, by omega⟩).val ∈ V_2)) = Finset.univ := by
          ext i
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
          rw [hi0_val i]; exact hv2
        rw [hflt]; simp
      · intro t; exact Fin.elim0 t
      · intro _ _; simp
      · intro _ _; simp
  | succ k hk1 ih =>
    intro hk_le
    obtain ⟨f, U1, U2, hfinj, hf0_in, hf1_in, hf2_in, huniq1, huniq2,
      hU1_card, hU2_card, hcol_inj, hinv1, hinv2⟩ := ih (by omega)
    let pFull := R.par ⟨k, by omega⟩ (by simp; omega)
    have hp_lt : pFull.val < k := R.par_lt ⟨k, by omega⟩ (by simp; omega)
    let p : Fin k := ⟨pFull.val, hp_lt⟩
    let x := f p
    let ecPrev : Fin (k - 1) → ℕ := fun t =>
      distNat (f ⟨(R.par ⟨t.val + 1, by omega⟩ (by simp)).val,
        lt_trans (R.par_lt ⟨t.val + 1, by omega⟩ (by simp)) (by simp; omega)⟩)
              (f ⟨t.val + 1, by omega⟩)
    set UsedCol : Finset ℕ := Finset.univ.image ecPrev
    set UsedPos : Finset ℕ := Finset.univ.image f
    have hf_loc : ∀ i : Fin k,
        f i ∈ I0 ∨ (∃ j ∈ U1, f i ∈ sub1 j) ∨ (∃ j ∈ U2, f i ∈ sub2 j) := by
      intro i
      rcases hpart (R.ord ⟨i.val, by omega⟩).val
        (R.ord ⟨i.val, by omega⟩).property with
        ⟨h0, _, _⟩ | ⟨_, h1, _⟩ | ⟨_, _, h2⟩
      · exact Or.inl (hf0_in i h0)
      · exact Or.inr (Or.inl (hf1_in i h1))
      · exact Or.inr (Or.inr (hf2_in i h2))
    have hf_not_sub1_of_not_U1 : ∀ (i : Fin k) {j : Fin V_1.card}, j ∉ U1 → f i ∉ sub1 j := by
      intro i j hj hmem
      have hb := hsub1_in j hmem
      rcases hf_loc i with h0 | ⟨j', hj'U, hj'sub⟩ | ⟨j', _, hj'sub⟩
      · have := Finset.mem_Ico.mp h0; omega
      · exact hj (subIco_disj hmem hj'sub ▸ hj'U)
      · have := hsub2_in j' hj'sub; omega
    have hf_not_sub2_of_not_U2 : ∀ (i : Fin k) {j : Fin V_2.card}, j ∉ U2 → f i ∉ sub2 j := by
      intro i j hj hmem
      have hb := hsub2_in j hmem
      rcases hf_loc i with h0 | ⟨j', _, hj'sub⟩ | ⟨j', hj'U, hj'sub⟩
      · have := Finset.mem_Ico.mp h0; omega
      · have := hsub1_in j' hj'sub; omega
      · exact hj (subIco_disj hmem hj'sub ▸ hj'U)
    have hfree1_disj_pos : ∀ {j : Fin V_1.card}, j ∉ U1 → ∀ {y : ℕ}, y ∈ sub1 j → y ∉ UsedPos := by
      intro j hj y hy hmem
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hmem
      exact hf_not_sub1_of_not_U1 i hj hy
    have hfree2_disj_pos : ∀ {j : Fin V_2.card}, j ∉ U2 → ∀ {y : ℕ}, y ∈ sub2 j → y ∉ UsedPos := by
      intro j hj y hy hmem
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hmem
      exact hf_not_sub2_of_not_U2 i hj hy
    have hextend_inj : ∀ {y : ℕ}, y ∉ UsedPos →
        Function.Injective (fun i : Fin (k + 1) => if h : i.val < k then f ⟨i.val, h⟩ else y) := by
      intro y hy_not i₁ i₂ heq
      dsimp only at heq
      by_cases h1 : i₁.val < k <;> by_cases h2 : i₂.val < k
      · rw [dif_pos h1, dif_pos h2] at heq
        have hsub : (⟨i₁.val, h1⟩ : Fin k) = ⟨i₂.val, h2⟩ := hfinj heq
        exact Fin.ext (congrArg (Fin.val : Fin k → ℕ) hsub)
      · rw [dif_pos h1, dif_neg h2] at heq
        exact absurd (heq ▸ Finset.mem_image_of_mem f (Finset.mem_univ (⟨i₁.val, h1⟩ : Fin k))) hy_not
      · rw [dif_neg h1, dif_pos h2] at heq
        exact absurd (heq.symm ▸ Finset.mem_image_of_mem f (Finset.mem_univ (⟨i₂.val, h2⟩ : Fin k))) hy_not
      · exact Fin.ext (by omega)
    have hextend_col : ∀ {y : ℕ}, distNat x y ∉ UsedCol →
        let f' : Fin (k + 1) → ℕ := fun i => if h : i.val < k then f ⟨i.val, h⟩ else y
        Function.Injective (fun t : Fin k =>
          distNat (f' ⟨(R.par ⟨t.val + 1, by omega⟩ (by simp)).val,
            lt_trans (R.par_lt ⟨t.val + 1, by omega⟩ (by simp)) (by simp)⟩)
                  (f' ⟨t.val + 1, by omega⟩)) ∧
        Finset.univ.image (fun t : Fin k =>
          distNat (f' ⟨(R.par ⟨t.val + 1, by omega⟩ (by simp)).val,
            lt_trans (R.par_lt ⟨t.val + 1, by omega⟩ (by simp)) (by simp)⟩)
                  (f' ⟨t.val + 1, by omega⟩)) = insert (distNat x y) UsedCol := by
      intro y hy_ncol f'
      have hpar_lt_k : ∀ t : Fin k,
          (R.par ⟨t.val + 1, by omega⟩ (by simp)).val < k := by
        intro t
        have := R.par_lt ⟨t.val + 1, by omega⟩ (by simp)
        simp at this; omega
      have hec_val : ∀ t : Fin k,
          distNat (f' ⟨(R.par ⟨t.val + 1, by omega⟩ (by simp)).val,
            lt_trans (R.par_lt ⟨t.val + 1, by omega⟩ (by simp)) (by simp)⟩)
                  (f' ⟨t.val + 1, by omega⟩) =
          if ht : t.val + 1 < k then ecPrev ⟨t.val, by omega⟩ else distNat x y := by
        intro t
        dsimp only [f']
        by_cases ht : t.val + 1 < k
        · have ht' : (⟨t.val + 1, by omega⟩ : Fin (k + 1)).val < k := ht
          rw [dif_pos (hpar_lt_k t), dif_pos ht', dif_pos ht]
        · have ht_eq : t.val + 1 = k := by omega
          have ht' : ¬ (⟨t.val + 1, by omega⟩ : Fin (k + 1)).val < k := ht
          rw [dif_pos (hpar_lt_k t), dif_neg ht', dif_neg ht]
          have hpar_eq : (⟨(R.par ⟨t.val + 1, by omega⟩ (by simp)).val,
              hpar_lt_k t⟩ : Fin k) = p := by
            apply Fin.ext; dsimp [p, pFull]; congr 2; exact Fin.ext ht_eq
          rw [hpar_eq]
      refine ⟨?_, ?_⟩
      · intro t₁ t₂ heq
        dsimp only at heq
        rw [hec_val t₁, hec_val t₂] at heq
        by_cases ht1 : t₁.val + 1 < k <;> by_cases ht2 : t₂.val + 1 < k
        · rw [dif_pos ht1, dif_pos ht2] at heq
          have hsub : (⟨t₁.val, by omega⟩ : Fin (k - 1)) = ⟨t₂.val, by omega⟩ :=
            @hcol_inj ⟨t₁.val, by omega⟩ ⟨t₂.val, by omega⟩ heq
          exact Fin.ext (congrArg (Fin.val : Fin (k - 1) → ℕ) hsub)
        · rw [dif_pos ht1, dif_neg ht2] at heq
          exact absurd (heq ▸ Finset.mem_image_of_mem ecPrev
            (Finset.mem_univ (⟨t₁.val, by omega⟩ : Fin (k - 1)))) hy_ncol
        · rw [dif_neg ht1, dif_pos ht2] at heq
          exact absurd (heq.symm ▸ Finset.mem_image_of_mem ecPrev
            (Finset.mem_univ (⟨t₂.val, by omega⟩ : Fin (k - 1)))) hy_ncol
        · exact Fin.ext (by omega)
      · ext c
        simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert, UsedCol]
        constructor
        · rintro ⟨t, rfl⟩
          rw [hec_val t]
          split_ifs with ht
          · exact Or.inr ⟨⟨t.val, by omega⟩, rfl⟩
          · exact Or.inl rfl
        · rintro (rfl | ⟨t', rfl⟩)
          · refine ⟨⟨k - 1, by omega⟩, ?_⟩
            rw [hec_val ⟨k - 1, by omega⟩, dif_neg (by simp; omega)]
          · have ht'_lt : t'.val < k - 1 := t'.isLt
            refine ⟨⟨t'.val, by omega⟩, ?_⟩
            rw [hec_val ⟨t'.val, by omega⟩, dif_pos (by simp; omega)]
    set vk := (R.ord ⟨k, by omega⟩).val with hvk_def
    have hvk_core : vk ∈ core := (R.ord ⟨k, by omega⟩).property
    have hfilter_eq : ∀ (S : Finset (Fin (n + 1))),
        (Finset.univ.filter (fun i : Fin (k + 1) =>
          (R.ord ⟨i.val, by omega⟩).val ∈ S)).card =
        (Finset.univ.filter (fun i : Fin k =>
          (R.ord ⟨i.val, by omega⟩).val ∈ S)).card +
          (if vk ∈ S then 1 else 0) := by
      intro S
      let Sk1 := Finset.univ.filter (fun i : Fin (k + 1) => (R.ord ⟨i.val, by omega⟩).val ∈ S)
      let Sk := Finset.univ.filter (fun i : Fin k => (R.ord ⟨i.val, by omega⟩).val ∈ S)
      let ik : Fin (k + 1) := ⟨k, by omega⟩
      have herase_bij : (Sk1.erase ik).card = Sk.card := by
        refine Finset.card_bij (fun i hi => (⟨i.val, by
          have hne : i ≠ ik := (Finset.mem_erase.mp hi).1
          have hlt : i.val < k + 1 := i.isLt
          have hnev : i.val ≠ k := fun h => hne (Fin.ext h)
          omega⟩ : Fin k)) ?_ ?_ ?_
        · intro i hi
          have hiS : (R.ord ⟨i.val, by omega⟩).val ∈ S :=
            (Finset.mem_filter.mp (Finset.mem_erase.mp hi).2).2
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hiS⟩
        · intro a _ b _ h
          exact Fin.ext (congrArg (Fin.val : Fin k → ℕ) h)
        · intro j hj
          have hjS : (R.ord ⟨j.val, by omega⟩).val ∈ S := (Finset.mem_filter.mp hj).2
          have hj_lt : j.val < k := j.isLt
          refine ⟨⟨j.val, by omega⟩, Finset.mem_erase.mpr ⟨?_, ?_⟩, Fin.ext rfl⟩
          · intro h; have hv := congrArg (Fin.val : Fin (k + 1) → ℕ) h; dsimp [ik] at hv; omega
          · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjS⟩
      change Sk1.card = Sk.card + (if vk ∈ S then 1 else 0)
      by_cases hvkS : vk ∈ S
      · have hik_mem : ik ∈ Sk1 := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvkS⟩
        have hadd : (Sk1.erase ik).card + 1 = Sk1.card := Finset.card_erase_add_one hik_mem
        have hrhs : (if vk ∈ S then 1 else 0) = 1 := if_pos hvkS
        omega
      · have hik_nmem : ik ∉ Sk1 := fun h => hvkS (Finset.mem_filter.mp h).2
        have her_eq : (Sk1.erase ik).card = Sk1.card := by
          rw [Finset.erase_eq_of_notMem hik_nmem]
        have hrhs : (if vk ∈ S then 1 else 0) = 0 := if_neg hvkS
        omega
    rcases hpart vk hvk_core with ⟨hvk0, hvk1n, hvk2n⟩ | ⟨hvk0n, hvk1, hvk2n⟩ | ⟨hvk0n, hvk1n, hvk2⟩
    · -- Case 1: vk ∈ V_0
      let cand0 : ℕ → ℕ := fun t => 90 * q0 + 2 * t + (1 - x % 2)
      set Cand0 := (Finset.range (3 * q0 + 2)).image cand0
      have hcand0_inj : Function.Injective cand0 := by
        intro a b h; dsimp [cand0] at h; omega
      have hCand0_card : Cand0.card = 3 * q0 + 2 := by
        rw [Finset.card_image_of_injective _ hcand0_inj, Finset.card_range]
      set Bad := UsedPos ∪ UsedCol.biUnion (fun c => ({x + c, x - c} : Finset ℕ))
      have hBad_card : Bad.card < Cand0.card := by
        have h1 : UsedPos.card ≤ k := Finset.card_image_le.trans (by simp)
        have h2 : UsedCol.card ≤ k - 1 := Finset.card_image_le.trans (by simp)
        have h3 : (UsedCol.biUnion (fun c => ({x + c, x - c} : Finset ℕ))).card ≤ 2 * UsedCol.card := by
          calc _ ≤ ∑ _c ∈ UsedCol, 2 :=
                (Finset.card_biUnion_le).trans (Finset.sum_le_sum fun _ _ => Finset.card_le_two)
            _ = 2 * UsedCol.card := by simp [Nat.mul_comm]
        have h4 : Bad.card ≤ UsedPos.card + (UsedCol.biUnion (fun c => ({x + c, x - c} : Finset ℕ))).card :=
          Finset.card_union_le _ _
        omega
      have hne : (Cand0 \ Bad).Nonempty :=
        Finset.sdiff_nonempty.mpr (fun hsub => not_le_of_gt hBad_card (Finset.card_le_card hsub))
      let y := (Cand0 \ Bad).min' hne
      obtain ⟨hy_cand, hy_nbad⟩ : y ∈ Cand0 ∧ y ∉ Bad :=
        Finset.mem_sdiff.mp (Finset.min'_mem _ hne)
      obtain ⟨t0, ht0_mem, ht0_eq⟩ := Finset.mem_image.mp hy_cand
      have ht0_lt : t0 < 3 * q0 + 2 := Finset.mem_range.mp ht0_mem
      have hy_eq_c : y = cand0 t0 := ht0_eq.symm
      have hy_I0 : y ∈ I0 := by
        rw [hy_eq_c]; refine Finset.mem_Ico.mpr ?_; dsimp [cand0]; omega
      have hy_odd : distNat x y % 2 = 1 := by
        apply distNat_mod_two_odd
        rw [hy_eq_c]; dsimp [cand0]; omega
      have hy_not_even_mod : ∀ m : ℕ, distNat x y % (4 * L) ≠ 2 * m := by
        intro m hm
        have h1 : (distNat x y % (4 * L)) % 2 = (2 * m) % 2 := congrArg (· % 2) hm
        rw [Nat.mod_mod_of_dvd _ (by omega : 2 ∣ 4 * L)] at h1
        omega
      have hy_npos : y ∉ UsedPos := fun h => hy_nbad (Finset.mem_union_left _ h)
      have hy_ncol : distNat x y ∉ UsedCol := by
        intro hc
        apply hy_nbad
        apply Finset.mem_union_right
        refine Finset.mem_biUnion.mpr ⟨distNat x y, hc, ?_⟩
        rcases distNat_sols (rfl : distNat x y = distNat x y) with hs | hs
        · exact Finset.mem_insert.mpr (Or.inl hs)
        · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr hs))
      let f' : Fin (k + 1) → ℕ := fun i => if h : i.val < k then f ⟨i.val, h⟩ else y
      obtain ⟨hcol', himg'⟩ := hextend_col hy_ncol
      refine ⟨f', U1, U2, hextend_inj hy_npos, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hcol', ?_, ?_⟩
      · intro i hi; dsimp only [f']; split_ifs with h
        · exact hf0_in ⟨i.val, h⟩ hi
        · exact hy_I0
      · intro i hi; dsimp only [f']; split_ifs with h
        · exact hf1_in ⟨i.val, h⟩ hi
        · have hik : i.val = k := by omega
          have hvk_eq : (R.ord ⟨i.val, by omega⟩).val = vk := by
            rw [hvk_def]; congr 2; exact Fin.ext hik
          rw [hvk_eq] at hi; exact absurd hi hvk1n
      · intro i hi; dsimp only [f']; split_ifs with h
        · exact hf2_in ⟨i.val, h⟩ hi
        · have hik : i.val = k := by omega
          have hvk_eq : (R.ord ⟨i.val, by omega⟩).val = vk := by
            rw [hvk_def]; congr 2; exact Fin.ext hik
          rw [hvk_eq] at hi; exact absurd hi hvk2n
      · intro i₁ i₂ j hm1 hm2
        dsimp only [f'] at hm1 hm2
        have hy_not_sub1 : y ∉ sub1 j := by
          intro hys; have := hsub1_in j hys; have := Finset.mem_Ico.mp hy_I0; omega
        by_cases h1 : i₁.val < k <;> by_cases h2 : i₂.val < k
        · rw [dif_pos h1] at hm1; rw [dif_pos h2] at hm2
          have hsub := huniq1 ⟨i₁.val, h1⟩ ⟨i₂.val, h2⟩ j hm1 hm2
          exact Fin.ext (congrArg (Fin.val : Fin k → ℕ) hsub)
        · rw [dif_neg h2] at hm2; exact absurd hm2 hy_not_sub1
        · rw [dif_neg h1] at hm1; exact absurd hm1 hy_not_sub1
        · exact Fin.ext (by omega)
      · intro i₁ i₂ j hm1 hm2
        dsimp only [f'] at hm1 hm2
        have hy_not_sub2 : y ∉ sub2 j := by
          intro hys; have := hsub2_in j hys; have := Finset.mem_Ico.mp hy_I0; omega
        by_cases h1 : i₁.val < k <;> by_cases h2 : i₂.val < k
        · rw [dif_pos h1] at hm1; rw [dif_pos h2] at hm2
          have hsub := huniq2 ⟨i₁.val, h1⟩ ⟨i₂.val, h2⟩ j hm1 hm2
          exact Fin.ext (congrArg (Fin.val : Fin k → ℕ) hsub)
        · rw [dif_neg h2] at hm2; exact absurd hm2 hy_not_sub2
        · rw [dif_neg h1] at hm1; exact absurd hm1 hy_not_sub2
        · exact Fin.ext (by omega)
      · have hf1 := hfilter_eq V_1; rw [if_neg hvk1n] at hf1; omega
      · have hf2 := hfilter_eq V_2; rw [if_neg hvk2n] at hf2; omega
      · intro s hs
        have himg_eq : Finset.univ.image (fun t : Fin (k + 1 - 1) =>
            distNat (f' ⟨(R.par ⟨t.val + 1, by omega⟩ (by simp)).val,
              lt_trans (R.par_lt ⟨t.val + 1, by omega⟩ (by simp)) (by simp)⟩)
                    (f' ⟨t.val + 1, by omega⟩)) = insert (distNat x y) UsedCol := himg'
        rw [himg_eq, Finset.filter_insert, if_neg (hy_not_even_mod s)]
        exact hinv1 s hs
      · intro s hs
        have himg_eq : Finset.univ.image (fun t : Fin (k + 1 - 1) =>
            distNat (f' ⟨(R.par ⟨t.val + 1, by omega⟩ (by simp)).val,
              lt_trans (R.par_lt ⟨t.val + 1, by omega⟩ (by simp)) (by simp)⟩)
                    (f' ⟨t.val + 1, by omega⟩)) = insert (distNat x y) UsedCol := himg'
        rw [himg_eq, Finset.filter_insert, if_neg (hy_not_even_mod (L + s))]
        exact hinv2 s hs
    · -- Case 2: vk ∈ V_1
      set F1 : Finset (Fin V_1.card) := Finset.univ \ U1
      have hU1_lt : U1.card < V_1.card := by
        have hcard_le : (Finset.univ.filter (fun i : Fin k =>
            (R.ord ⟨i.val, by omega⟩).val ∈ V_1)).card ≤
            (V_1.erase vk).card := by
          refine Finset.card_le_card_of_injOn
            (fun i : Fin k => (R.ord ⟨i.val, by omega⟩).val) ?_ ?_
          · intro i hi
            have hiV1 : (R.ord ⟨i.val, by omega⟩).val ∈ V_1 :=
              (Finset.mem_filter.mp hi).2
            refine Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨?_, hiV1⟩)
            intro heq
            rw [hvk_def] at heq
            have hord := R.ord.injective (Subtype.ext heq)
            have hval := congrArg (Fin.val : Fin mCore → ℕ) hord
            dsimp at hval; omega
          · intro a _ b _ heq
            have hord := R.ord.injective (Subtype.ext heq)
            have hval := congrArg (Fin.val : Fin mCore → ℕ) hord
            dsimp at hval; exact Fin.ext hval
        have herase := Finset.card_erase_of_mem hvk1
        have hpos_V1 : 0 < V_1.card := Finset.card_pos.mpr ⟨vk, hvk1⟩
        omega
      have hF1_card : F1.card = V_1.card - U1.card := by
        have hsd : F1.card + U1.card = (Finset.univ : Finset (Fin V_1.card)).card :=
          Finset.card_sdiff_add_card_eq_card (Finset.subset_univ U1)
        simp only [Finset.card_univ, Fintype.card_fin] at hsd
        omega
      have hx_out1 : x ∉ F1.biUnion sub1 := by
        intro hmem
        obtain ⟨j, hjF, hjx⟩ := Finset.mem_biUnion.mp hmem
        exact hf_not_sub1_of_not_U1 p (Finset.mem_sdiff.mp hjF).2 hjx
      have hex_s : ∃ s : ℕ, s < L ∧
          (UsedCol.filter (fun c => c % (4 * L) = 2 * s)).card < F1.card := by
        refine ⟨L - 2, by omega, ?_⟩
        have hdiv0 : V_1.card / 2 ^ (L - 2) = 0 := Nat.div_eq_of_lt hV1_pow
        have h0 := hinv1 (L - 2) (by omega)
        rw [hdiv0] at h0
        omega
      set s₀ := Nat.find hex_s
      obtain ⟨hs₀_lt, hs₀_col⟩ := Nat.find_spec hex_s
      obtain ⟨j₀, hj₀_F, y, hy_sub, hy_mod, hy_ncol⟩ :=
        free_subinterval_choice (base := 77 * q0) (by omega : 0 < L)
          F1 UsedCol x (2 * s₀) (by omega) hx_out1 hs₀_col
      have hj₀_not_U1 : j₀ ∉ U1 := (Finset.mem_sdiff.mp hj₀_F).2
      have hy_npos : y ∉ UsedPos := hfree1_disj_pos hj₀_not_U1 hy_sub
      let f' : Fin (k + 1) → ℕ := fun i => if h : i.val < k then f ⟨i.val, h⟩ else y
      let U1' : Finset (Fin V_1.card) := insert j₀ U1
      have hU1'_card : U1'.card = U1.card + 1 := Finset.card_insert_of_notMem hj₀_not_U1
      obtain ⟨hcol', himg'⟩ := hextend_col hy_ncol
      refine ⟨f', U1', U2, hextend_inj hy_npos, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hcol', ?_, ?_⟩
      · intro i hi; dsimp only [f']; split_ifs with h
        · exact hf0_in ⟨i.val, h⟩ hi
        · have hik : i.val = k := by omega
          have hvk_eq : (R.ord ⟨i.val, by omega⟩).val = vk := by
            rw [hvk_def]; congr 2; exact Fin.ext hik
          rw [hvk_eq] at hi; exact absurd hi hvk0n
      · intro i hi; dsimp only [f']; split_ifs with h
        · obtain ⟨j, hjU, hjs⟩ := hf1_in ⟨i.val, h⟩ hi
          exact ⟨j, Finset.mem_insert_of_mem hjU, hjs⟩
        · exact ⟨j₀, Finset.mem_insert_self _ _, hy_sub⟩
      · intro i hi; dsimp only [f']; split_ifs with h
        · exact hf2_in ⟨i.val, h⟩ hi
        · have hik : i.val = k := by omega
          have hvk_eq : (R.ord ⟨i.val, by omega⟩).val = vk := by
            rw [hvk_def]; congr 2; exact Fin.ext hik
          rw [hvk_eq] at hi; exact absurd hi hvk2n
      · intro i₁ i₂ j hm1 hm2
        dsimp only [f'] at hm1 hm2
        by_cases h1 : i₁.val < k <;> by_cases h2 : i₂.val < k
        · rw [dif_pos h1] at hm1; rw [dif_pos h2] at hm2
          have hsub := huniq1 ⟨i₁.val, h1⟩ ⟨i₂.val, h2⟩ j hm1 hm2
          exact Fin.ext (congrArg (Fin.val : Fin k → ℕ) hsub)
        · rw [dif_pos h1] at hm1; rw [dif_neg h2] at hm2
          have hjeq : j = j₀ := subIco_disj hm2 hy_sub
          exact absurd (hjeq ▸ hm1) (hf_not_sub1_of_not_U1 _ hj₀_not_U1)
        · rw [dif_neg h1] at hm1; rw [dif_pos h2] at hm2
          have hjeq : j = j₀ := subIco_disj hm1 hy_sub
          exact absurd (hjeq ▸ hm2) (hf_not_sub1_of_not_U1 _ hj₀_not_U1)
        · exact Fin.ext (by omega)
      · intro i₁ i₂ j hm1 hm2
        dsimp only [f'] at hm1 hm2
        have hy_not_sub2 : y ∉ sub2 j := by
          intro hys; have := hsub2_in j hys; have := hsub1_in j₀ hy_sub; omega
        by_cases h1 : i₁.val < k <;> by_cases h2 : i₂.val < k
        · rw [dif_pos h1] at hm1; rw [dif_pos h2] at hm2
          have hsub := huniq2 ⟨i₁.val, h1⟩ ⟨i₂.val, h2⟩ j hm1 hm2
          exact Fin.ext (congrArg (Fin.val : Fin k → ℕ) hsub)
        · rw [dif_neg h2] at hm2; exact absurd hm2 hy_not_sub2
        · rw [dif_neg h1] at hm1; exact absurd hm1 hy_not_sub2
        · exact Fin.ext (by omega)
      · have hf1 := hfilter_eq V_1; rw [if_pos hvk1] at hf1; omega
      · have hf2 := hfilter_eq V_2; rw [if_neg hvk2n] at hf2; omega
      · intro s hs
        have himg_eq : Finset.univ.image (fun t : Fin (k + 1 - 1) =>
            distNat (f' ⟨(R.par ⟨t.val + 1, by omega⟩ (by simp)).val,
              lt_trans (R.par_lt ⟨t.val + 1, by omega⟩ (by simp)) (by simp)⟩)
                    (f' ⟨t.val + 1, by omega⟩)) = insert (distNat x y) UsedCol := himg'
        rw [himg_eq, Finset.filter_insert, hU1'_card]
        by_cases hss : s = s₀
        · subst hss
          rw [if_pos hy_mod, Finset.card_insert_of_notMem
            (fun h => hy_ncol (Finset.mem_filter.mp h).1)]
          have hprev := hinv1 s₀ hs
          by_cases hs0 : s₀ = 0
          · rw [hs0] at hprev ⊢; simp at hprev ⊢; omega
          · have hf_le_div : V_1.card - U1.card ≤ V_1.card / 2 ^ s₀ := by
              by_contra hgt
              have hprev_pred := hinv1 (s₀ - 1) (by omega)
              have hdiv_two : V_1.card / 2 ^ s₀ = (V_1.card / 2 ^ (s₀ - 1)) / 2 := by
                rw [Nat.div_div_eq_div_mul]
                congr 1
                rcases Nat.exists_eq_succ_of_ne_zero hs0 with ⟨s', hsq⟩
                rw [hsq]; simp [pow_succ]
              have hlt_pred : (UsedCol.filter (fun c => c % (4 * L) = 2 * (s₀ - 1))).card <
                  F1.card := by omega
              exact Nat.find_min hex_s (by omega : s₀ - 1 < s₀) ⟨by omega, hlt_pred⟩
            omega
        · rw [if_neg (by omega)]
          have hprev := hinv1 s hs
          omega
      · intro s hs
        have himg_eq : Finset.univ.image (fun t : Fin (k + 1 - 1) =>
            distNat (f' ⟨(R.par ⟨t.val + 1, by omega⟩ (by simp)).val,
              lt_trans (R.par_lt ⟨t.val + 1, by omega⟩ (by simp)) (by simp)⟩)
                    (f' ⟨t.val + 1, by omega⟩)) = insert (distNat x y) UsedCol := himg'
        rw [himg_eq, Finset.filter_insert, if_neg (by omega)]
        exact hinv2 s hs
    · -- Case 3: vk ∈ V_2
      set F2 : Finset (Fin V_2.card) := Finset.univ \ U2
      have hU2_lt : U2.card < V_2.card := by
        have hcard_le : (Finset.univ.filter (fun i : Fin k =>
            (R.ord ⟨i.val, by omega⟩).val ∈ V_2)).card ≤
            (V_2.erase vk).card := by
          refine Finset.card_le_card_of_injOn
            (fun i : Fin k => (R.ord ⟨i.val, by omega⟩).val) ?_ ?_
          · intro i hi
            have hiV2 : (R.ord ⟨i.val, by omega⟩).val ∈ V_2 :=
              (Finset.mem_filter.mp hi).2
            refine Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨?_, hiV2⟩)
            intro heq
            rw [hvk_def] at heq
            have hord := R.ord.injective (Subtype.ext heq)
            have hval := congrArg (Fin.val : Fin mCore → ℕ) hord
            dsimp at hval; omega
          · intro a _ b _ heq
            have hord := R.ord.injective (Subtype.ext heq)
            have hval := congrArg (Fin.val : Fin mCore → ℕ) hord
            dsimp at hval; exact Fin.ext hval
        have herase := Finset.card_erase_of_mem hvk2
        have hpos_V2 : 0 < V_2.card := Finset.card_pos.mpr ⟨vk, hvk2⟩
        omega
      have hF2_card : F2.card = V_2.card - U2.card := by
        have hsd : F2.card + U2.card = (Finset.univ : Finset (Fin V_2.card)).card :=
          Finset.card_sdiff_add_card_eq_card (Finset.subset_univ U2)
        simp only [Finset.card_univ, Fintype.card_fin] at hsd
        omega
      have hx_out2 : x ∉ F2.biUnion sub2 := by
        intro hmem
        obtain ⟨j, hjF, hjx⟩ := Finset.mem_biUnion.mp hmem
        exact hf_not_sub2_of_not_U2 p (Finset.mem_sdiff.mp hjF).2 hjx
      have hex_s : ∃ s : ℕ, s < L ∧
          (UsedCol.filter (fun c => c % (4 * L) = 2 * (L + s))).card < F2.card := by
        refine ⟨L - 2, by omega, ?_⟩
        have hdiv0 : V_2.card / 2 ^ (L - 2) = 0 := Nat.div_eq_of_lt hV2_pow
        have h0 := hinv2 (L - 2) (by omega)
        rw [hdiv0] at h0
        omega
      set s₀ := Nat.find hex_s
      obtain ⟨hs₀_lt, hs₀_col⟩ := Nat.find_spec hex_s
      obtain ⟨j₀, hj₀_F, y, hy_sub, hy_mod, hy_ncol⟩ :=
        free_subinterval_choice (base := 98 * q0) (by omega : 0 < L)
          F2 UsedCol x (2 * (L + s₀)) (by omega) hx_out2 hs₀_col
      have hj₀_not_U2 : j₀ ∉ U2 := (Finset.mem_sdiff.mp hj₀_F).2
      have hy_npos : y ∉ UsedPos := hfree2_disj_pos hj₀_not_U2 hy_sub
      let f' : Fin (k + 1) → ℕ := fun i => if h : i.val < k then f ⟨i.val, h⟩ else y
      let U2' : Finset (Fin V_2.card) := insert j₀ U2
      have hU2'_card : U2'.card = U2.card + 1 := Finset.card_insert_of_notMem hj₀_not_U2
      obtain ⟨hcol', himg'⟩ := hextend_col hy_ncol
      refine ⟨f', U1, U2', hextend_inj hy_npos, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hcol', ?_, ?_⟩
      · intro i hi; dsimp only [f']; split_ifs with h
        · exact hf0_in ⟨i.val, h⟩ hi
        · have hik : i.val = k := by omega
          have hvk_eq : (R.ord ⟨i.val, by omega⟩).val = vk := by
            rw [hvk_def]; congr 2; exact Fin.ext hik
          rw [hvk_eq] at hi; exact absurd hi hvk0n
      · intro i hi; dsimp only [f']; split_ifs with h
        · exact hf1_in ⟨i.val, h⟩ hi
        · have hik : i.val = k := by omega
          have hvk_eq : (R.ord ⟨i.val, by omega⟩).val = vk := by
            rw [hvk_def]; congr 2; exact Fin.ext hik
          rw [hvk_eq] at hi; exact absurd hi hvk1n
      · intro i hi; dsimp only [f']; split_ifs with h
        · obtain ⟨j, hjU, hjs⟩ := hf2_in ⟨i.val, h⟩ hi
          exact ⟨j, Finset.mem_insert_of_mem hjU, hjs⟩
        · exact ⟨j₀, Finset.mem_insert_self _ _, hy_sub⟩
      · intro i₁ i₂ j hm1 hm2
        dsimp only [f'] at hm1 hm2
        have hy_not_sub1 : y ∉ sub1 j := by
          intro hys; have := hsub1_in j hys; have := hsub2_in j₀ hy_sub; omega
        by_cases h1 : i₁.val < k <;> by_cases h2 : i₂.val < k
        · rw [dif_pos h1] at hm1; rw [dif_pos h2] at hm2
          have hsub := huniq1 ⟨i₁.val, h1⟩ ⟨i₂.val, h2⟩ j hm1 hm2
          exact Fin.ext (congrArg (Fin.val : Fin k → ℕ) hsub)
        · rw [dif_neg h2] at hm2; exact absurd hm2 hy_not_sub1
        · rw [dif_neg h1] at hm1; exact absurd hm1 hy_not_sub1
        · exact Fin.ext (by omega)
      · intro i₁ i₂ j hm1 hm2
        dsimp only [f'] at hm1 hm2
        by_cases h1 : i₁.val < k <;> by_cases h2 : i₂.val < k
        · rw [dif_pos h1] at hm1; rw [dif_pos h2] at hm2
          have hsub := huniq2 ⟨i₁.val, h1⟩ ⟨i₂.val, h2⟩ j hm1 hm2
          exact Fin.ext (congrArg (Fin.val : Fin k → ℕ) hsub)
        · rw [dif_pos h1] at hm1; rw [dif_neg h2] at hm2
          have hjeq : j = j₀ := subIco_disj hm2 hy_sub
          exact absurd (hjeq ▸ hm1) (hf_not_sub2_of_not_U2 _ hj₀_not_U2)
        · rw [dif_neg h1] at hm1; rw [dif_pos h2] at hm2
          have hjeq : j = j₀ := subIco_disj hm1 hy_sub
          exact absurd (hjeq ▸ hm2) (hf_not_sub2_of_not_U2 _ hj₀_not_U2)
        · exact Fin.ext (by omega)
      · have hf1 := hfilter_eq V_1; rw [if_neg hvk1n] at hf1; omega
      · have hf2 := hfilter_eq V_2; rw [if_pos hvk2] at hf2; omega
      · intro s hs
        have himg_eq : Finset.univ.image (fun t : Fin (k + 1 - 1) =>
            distNat (f' ⟨(R.par ⟨t.val + 1, by omega⟩ (by simp)).val,
              lt_trans (R.par_lt ⟨t.val + 1, by omega⟩ (by simp)) (by simp)⟩)
                    (f' ⟨t.val + 1, by omega⟩)) = insert (distNat x y) UsedCol := himg'
        rw [himg_eq, Finset.filter_insert, if_neg (by omega)]
        exact hinv1 s hs
      · intro s hs
        have himg_eq : Finset.univ.image (fun t : Fin (k + 1 - 1) =>
            distNat (f' ⟨(R.par ⟨t.val + 1, by omega⟩ (by simp)).val,
              lt_trans (R.par_lt ⟨t.val + 1, by omega⟩ (by simp)) (by simp)⟩)
                    (f' ⟨t.val + 1, by omega⟩)) = insert (distNat x y) UsedCol := himg'
        rw [himg_eq, Finset.filter_insert, hU2'_card]
        by_cases hss : s = s₀
        · subst hss
          rw [if_pos hy_mod, Finset.card_insert_of_notMem
            (fun h => hy_ncol (Finset.mem_filter.mp h).1)]
          have hprev := hinv2 s₀ hs
          by_cases hs0 : s₀ = 0
          · rw [hs0] at hprev ⊢; simp at hprev ⊢; omega
          · have hf_le_div : V_2.card - U2.card ≤ V_2.card / 2 ^ s₀ := by
              by_contra hgt
              have hprev_pred := hinv2 (s₀ - 1) (by omega)
              have hdiv_two : V_2.card / 2 ^ s₀ = (V_2.card / 2 ^ (s₀ - 1)) / 2 := by
                rw [Nat.div_div_eq_div_mul]
                congr 1
                rcases Nat.exists_eq_succ_of_ne_zero hs0 with ⟨s', hsq⟩
                rw [hsq]; simp [pow_succ]
              have hlt_pred : (UsedCol.filter (fun c => c % (4 * L) = 2 * (L + (s₀ - 1)))).card <
                  F2.card := by omega
              exact Nat.find_min hex_s (by omega : s₀ - 1 < s₀) ⟨by omega, hlt_pred⟩
            omega
        · rw [if_neg (by omega)]
          have hprev := hinv2 s hs
          omega

private lemma exists_small_tree_embed {n L : ℕ}
    (hL : 16384 ≤ L) (hq0 : 10000000000 ≤ n / 100)
    (T : SimpleGraph (Fin (n + 1))) [DecidableRel T.Adj]
    (core V_0 V_1 V_2 : Finset (Fin (n + 1)))
    (hcore_le : core.card ≤ n / 100)
    (hV1_sub : V_1 ⊆ core) (hV2_sub : V_2 ⊆ core)
    (hpart : ∀ x ∈ core, (x ∈ V_0 ∧ x ∉ V_1 ∧ x ∉ V_2) ∨
                         (x ∉ V_0 ∧ x ∈ V_1 ∧ x ∉ V_2) ∨
                         (x ∉ V_0 ∧ x ∉ V_1 ∧ x ∈ V_2))
    (hV1_width : V_1.card * (8 * L) ≤ n / 100)
    (hV2_width : V_2.card * (8 * L) ≤ n / 100)
    (hV1_pow : V_1.card < 2 ^ (L - 2))
    (hV2_pow : V_2.card < 2 ^ (L - 2))
    (r₀ : ↥(core : Set (Fin (n + 1))))
    (R : RootedOrder (T.induce (core : Set (Fin (n + 1)))) r₀) :
    Nonempty (SmallTreeResult T core V_0 V_1 V_2 r₀ L) := by
  classical
  set q0 := n / 100 with hq0_def
  have hn_q0 : 100 * q0 ≤ n := Nat.mul_div_le n 100
  set mCore := Fintype.card ↥(core : Set (Fin (n + 1))) with hmCore_def
  have hmCore_pos : 1 ≤ mCore := Fintype.card_pos_iff.mpr ⟨r₀⟩
  let sub1 : Fin V_1.card → Finset ℕ := fun j =>
    Finset.Ico (77 * q0 + j.val * (8 * L)) (77 * q0 + j.val * (8 * L) + 8 * L)
  let sub2 : Fin V_2.card → Finset ℕ := fun j =>
    Finset.Ico (98 * q0 + j.val * (8 * L)) (98 * q0 + j.val * (8 * L) + 8 * L)
  let I0 : Finset ℕ := Finset.Ico (90 * q0) (97 * q0)
  have hsub1_in : ∀ (j : Fin V_1.card) {y : ℕ}, y ∈ sub1 j →
      77 * q0 ≤ y ∧ y < 78 * q0 := by
    intro j y hy
    have hy' := Finset.mem_Ico.mp hy
    have hj : j.val * (8 * L) + 8 * L ≤ V_1.card * (8 * L) := by
      calc j.val * (8 * L) + 8 * L = (j.val + 1) * (8 * L) := (Nat.succ_mul _ _).symm
        _ ≤ V_1.card * (8 * L) := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt j.isLt)
    omega
  have hsub2_in : ∀ (j : Fin V_2.card) {y : ℕ}, y ∈ sub2 j →
      98 * q0 ≤ y ∧ y < 99 * q0 := by
    intro j y hy
    have hy' := Finset.mem_Ico.mp hy
    have hj : j.val * (8 * L) + 8 * L ≤ V_2.card * (8 * L) := by
      calc j.val * (8 * L) + 8 * L = (j.val + 1) * (8 * L) := (Nat.succ_mul _ _).symm
        _ ≤ V_2.card * (8 * L) := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt j.isLt)
    omega
  obtain ⟨f, _, _, hfinj, hf0_in, hf1_in, hf2_in, huniq1, huniq2, _, _, hcol_inj, _, _⟩ :=
    small_tree_step hL hq0 T core V_0 V_1 V_2 hcore_le hpart hV1_width hV2_width
      hV1_pow hV2_pow r₀ R mCore hmCore_pos (le_refl mCore)
  let posCore : ↥(core : Set (Fin (n + 1))) → ℕ := fun x => f (R.ord.symm x)
  have hposCore_inj : Function.Injective posCore :=
    fun _ _ h => R.ord.symm.injective (hfinj h)
  have hord_symm_eq : ∀ x : ↥(core : Set (Fin (n + 1))),
      R.ord ⟨(R.ord.symm x).val, (R.ord.symm x).isLt⟩ = x := by
    intro x
    have h1 : (⟨(R.ord.symm x).val, (R.ord.symm x).isLt⟩ : Fin mCore) = R.ord.symm x := rfl
    rw [h1, R.ord.apply_symm_apply]
  have hpos_V0 : ∀ x : ↥(core : Set (Fin (n + 1))), x.val ∈ V_0 → posCore x ∈ I0 := by
    intro x hx
    exact hf0_in (R.ord.symm x) (by rw [hord_symm_eq x]; exact hx)
  have hslot1_ex : ∀ v : ↥V_1,
      ∃ j : Fin V_1.card, posCore ⟨v.val, hV1_sub v.property⟩ ∈ sub1 j := by
    intro v
    obtain ⟨j, _, hj⟩ := hf1_in (R.ord.symm ⟨v.val, hV1_sub v.property⟩)
      (by rw [hord_symm_eq]; exact v.property)
    exact ⟨j, hj⟩
  let slot1 : ↥V_1 → Fin V_1.card := fun v => (hslot1_ex v).choose
  have hslot1_spec : ∀ v, posCore ⟨v.val, hV1_sub v.property⟩ ∈ sub1 (slot1 v) :=
    fun v => (hslot1_ex v).choose_spec
  have hslot1_inj : Function.Injective slot1 := by
    intro v₁ v₂ heq
    have hs1 := hslot1_spec v₁
    have hs2 := heq ▸ hslot1_spec v₂
    have hi := huniq1 _ _ (slot1 v₁) hs1 hs2
    have hsub : (⟨v₁.val, hV1_sub v₁.property⟩ : ↥(core : Set (Fin (n + 1)))) =
        ⟨v₂.val, hV1_sub v₂.property⟩ := R.ord.symm.injective hi
    exact Subtype.ext (congrArg (Subtype.val : ↥(core : Set (Fin (n + 1))) → Fin (n + 1)) hsub)
  have hslot1_bij : Function.Bijective slot1 :=
    (Fintype.bijective_iff_injective_and_card slot1).mpr ⟨hslot1_inj, by simp [Fintype.card_coe]⟩
  let zEquiv : Fin V_1.card ≃ ↥V_1 := (Equiv.ofBijective slot1 hslot1_bij).symm
  have hpos_z : ∀ q : Fin V_1.card,
      posCore ⟨(zEquiv q).val, hV1_sub (zEquiv q).property⟩ ∈ sub1 q := by
    intro q
    have h := hslot1_spec (zEquiv q)
    have hsq : slot1 (zEquiv q) = q := Equiv.ofBijective_apply_symm_apply slot1 hslot1_bij q
    rwa [hsq] at h
  have hslot2_ex : ∀ v : ↥V_2,
      ∃ j : Fin V_2.card, posCore ⟨v.val, hV2_sub v.property⟩ ∈ sub2 j := by
    intro v
    obtain ⟨j, _, hj⟩ := hf2_in (R.ord.symm ⟨v.val, hV2_sub v.property⟩)
      (by rw [hord_symm_eq]; exact v.property)
    exact ⟨j, hj⟩
  let slot2 : ↥V_2 → Fin V_2.card := fun v => (hslot2_ex v).choose
  have hslot2_spec : ∀ v, posCore ⟨v.val, hV2_sub v.property⟩ ∈ sub2 (slot2 v) :=
    fun v => (hslot2_ex v).choose_spec
  have hslot2_inj : Function.Injective slot2 := by
    intro v₁ v₂ heq
    have hs1 := hslot2_spec v₁
    have hs2 := heq ▸ hslot2_spec v₂
    have hi := huniq2 _ _ (slot2 v₁) hs1 hs2
    have hsub : (⟨v₁.val, hV2_sub v₁.property⟩ : ↥(core : Set (Fin (n + 1)))) =
        ⟨v₂.val, hV2_sub v₂.property⟩ := R.ord.symm.injective hi
    exact Subtype.ext (congrArg (Subtype.val : ↥(core : Set (Fin (n + 1))) → Fin (n + 1)) hsub)
  have hslot2_bij : Function.Bijective slot2 :=
    (Fintype.bijective_iff_injective_and_card slot2).mpr ⟨hslot2_inj, by simp [Fintype.card_coe]⟩
  let wEquiv : Fin V_2.card ≃ ↥V_2 := (Equiv.ofBijective slot2 hslot2_bij).symm
  have hpos_w : ∀ q : Fin V_2.card,
      posCore ⟨(wEquiv q).val, hV2_sub (wEquiv q).property⟩ ∈ sub2 q := by
    intro q
    have h := hslot2_spec (wEquiv q)
    have hsq : slot2 (wEquiv q) = q := Equiv.ofBijective_apply_symm_apply slot2 hslot2_bij q
    rwa [hsq] at h
  have hpos_bounds : ∀ x : ↥(core : Set (Fin (n + 1))),
      77 * q0 ≤ posCore x ∧ posCore x < 99 * q0 := by
    intro x
    rcases hpart x.val x.property with ⟨h0, _, _⟩ | ⟨_, h1, _⟩ | ⟨_, _, h2⟩
    · have := Finset.mem_Ico.mp (hpos_V0 x h0); omega
    · obtain ⟨j, _, hj⟩ := hf1_in (R.ord.symm x) (by rw [hord_symm_eq x]; exact h1)
      have hb : 77 * q0 ≤ posCore x ∧ posCore x < 78 * q0 := hsub1_in j hj
      omega
    · obtain ⟨j, _, hj⟩ := hf2_in (R.ord.symm x) (by rw [hord_symm_eq x]; exact h2)
      have hb : 98 * q0 ≤ posCore x ∧ posCore x < 99 * q0 := hsub2_in j hj
      omega
  let ecCore : Fin (mCore - 1) → ℕ := fun t =>
    distNat (posCore (R.ord (R.par ⟨t.val + 1, by omega⟩ (by simp))))
            (posCore (R.ord ⟨t.val + 1, by omega⟩))
  have hecCore_eq : ∀ t : Fin (mCore - 1),
      ecCore t = distNat (f (R.par ⟨t.val + 1, by omega⟩ (by simp)))
                         (f ⟨t.val + 1, by omega⟩) := by
    intro t; dsimp [ecCore, posCore]; simp
  have hecCore_inj : Function.Injective ecCore := by
    intro t₁ t₂ h
    rw [hecCore_eq t₁, hecCore_eq t₂] at h
    exact hcol_inj h
  let C_core := Finset.univ.image ecCore
  have hC_core_sub : C_core ⊆ Finset.Icc 1 n := by
    intro c hc
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hc
    refine Finset.mem_Icc.mpr ⟨?_, ?_⟩
    · apply distNat_pos_of_ne
      intro heq
      have hord := R.ord.injective (hposCore_inj heq)
      have hlt := R.par_lt ⟨t.val + 1, by omega⟩ (by simp)
      rw [hord] at hlt
      omega
    · have hb1 := hpos_bounds (R.ord (R.par ⟨t.val + 1, by omega⟩ (by simp)))
      have hb2 := hpos_bounds (R.ord ⟨t.val + 1, by omega⟩)
      dsimp [ecCore, distNat]; omega
  exact ⟨{
    R := R
    posCore := posCore
    posCore_inj := hposCore_inj
    pos_V0 := hpos_V0
    z := zEquiv
    z_mem_core := fun q => hV1_sub (zEquiv q).property
    pos_z := hpos_z
    w := wEquiv
    w_mem_core := fun q => hV2_sub (wEquiv q).property
    pos_w := hpos_w
    C_core := C_core
    C_core_sub := hC_core_sub
    C_core_card := by rw [Finset.card_image_of_injective _ hecCore_inj, Finset.card_fin]
    ecCore_mem := fun t => Finset.mem_image_of_mem ecCore (Finset.mem_univ t)
    ecCore_inj := hecCore_inj
  }⟩

-- ============================================================================
-- Section 5: Subcase 2 — Bounded Leaf-Degrees and Zig-Zag Leaf Attachment
-- ============================================================================

private lemma orderEmb_sub_ge {C_rem : Finset ℕ} {N : ℕ} (hN : C_rem.card = N)
    (t₁ t₂ : Fin N) (hle : t₁.val ≤ t₂.val) :
    t₂.val - t₁.val ≤ (C_rem.orderEmbOfFin hN) t₂ - (C_rem.orderEmbOfFin hN) t₁ := by
  set e := C_rem.orderEmbOfFin hN
  have ht2_lt : t₂.val < N := t₂.isLt
  have hstep : ∀ d : ℕ, ∀ (h : t₁.val + d < N),
      d ≤ e ⟨t₁.val + d, h⟩ - e t₁ := by
    intro d
    induction d with
    | zero => intro _; simp
    | succ d ih =>
      intro h
      let id0 : Fin N := ⟨t₁.val + d, by omega⟩
      let id1 : Fin N := ⟨t₁.val + (d + 1), h⟩
      have ih' : d ≤ e id0 - e t₁ := ih id0.isLt
      have hle0 : e t₁ ≤ e id0 := e.monotone (by dsimp [id0]; rw [Fin.le_def]; dsimp; omega)
      have hlt : id0 < id1 := by simp [id0, id1, Fin.lt_def]
      have hel : e id0 < e id1 := e.strictMono hlt
      change d + 1 ≤ e id1 - e t₁
      omega
  have hd_lt : t₁.val + (t₂.val - t₁.val) < N := by omega
  have hres := hstep (t₂.val - t₁.val) hd_lt
  have heq : (⟨t₁.val + (t₂.val - t₁.val), hd_lt⟩ : Fin N) = t₂ := Fin.ext (by dsimp; omega)
  rwa [heq] at hres

private lemma orderEmb_bounds {n N : ℕ} {C_core : Finset ℕ}
    (hN : (Finset.Icc 1 n \ C_core).card = N) (t : Fin N) :
    let e := (Finset.Icc 1 n \ C_core).orderEmbOfFin hN
    t.val + 1 ≤ e t ∧ e t ≤ n ∧ e t ≤ t.val + 1 + C_core.card ∧ e t ∉ C_core := by
  classical
  dsimp only
  have hN_pos : 0 < N := Nat.zero_lt_of_lt t.isLt
  set C_rem := Finset.Icc 1 n \ C_core
  set e := C_rem.orderEmbOfFin hN
  have ht_mem : e t ∈ C_rem := Finset.orderEmbOfFin_mem C_rem hN t
  obtain ⟨ht_Icc, ht_not_core⟩ := Finset.mem_sdiff.mp ht_mem
  obtain ⟨_, ht_le_n⟩ := Finset.mem_Icc.mp ht_Icc
  have h0_mem : e ⟨0, hN_pos⟩ ∈ C_rem := Finset.orderEmbOfFin_mem C_rem hN ⟨0, hN_pos⟩
  have h0_ge1 : 1 ≤ e ⟨0, hN_pos⟩ := (Finset.mem_Icc.mp (Finset.mem_sdiff.mp h0_mem).1).1
  have hge : t.val + 1 ≤ e t := by
    have hsub := orderEmb_sub_ge hN ⟨0, hN_pos⟩ t (by simp)
    change t.val - 0 ≤ e t - e ⟨0, hN_pos⟩ at hsub
    omega
  set Init := (Finset.univ.filter (fun i : Fin N => i ≤ t)).image e
  have hsub_Icc : Finset.Icc 1 (e t) ⊆ C_core ∪ Init := by
    intro x hx
    by_cases hxc : x ∈ C_core
    · exact Finset.mem_union_left _ hxc
    · apply Finset.mem_union_right
      have hx_rem : x ∈ C_rem := Finset.mem_sdiff.mpr ⟨
        Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hx).1, (Finset.mem_Icc.mp hx).2.trans ht_le_n⟩, hxc⟩
      have hrange : Set.range e = (C_rem : Set ℕ) := Finset.range_orderEmbOfFin C_rem hN
      have hx_rng : x ∈ Set.range e := by rw [hrange]; exact hx_rem
      obtain ⟨i, rfl⟩ := hx_rng
      have hit : i ≤ t := e.le_iff_le.mp (Finset.mem_Icc.mp hx).2
      exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hit⟩, rfl⟩
  have hInit_card : Init.card ≤ t.val + 1 := by
    calc Init.card ≤ (Finset.univ.filter (fun i : Fin N => i ≤ t)).card := Finset.card_image_le
      _ ≤ (Finset.range (t.val + 1)).card := by
        refine Finset.card_le_card_of_injOn (fun i : Fin N => i.val) ?_ ?_
        · intro i hi
          have hle : i ≤ t := (Finset.mem_filter.mp hi).2
          exact Finset.mem_coe.mpr (Finset.mem_range.mpr (Nat.lt_succ_of_le hle))
        · intro a _ b _ h; exact Fin.ext h
      _ = t.val + 1 := Finset.card_range _
  have hcard_Icc : (Finset.Icc 1 (e t)).card ≤ (C_core ∪ Init).card := Finset.card_le_card hsub_Icc
  have hcard_union : (C_core ∪ Init).card ≤ C_core.card + Init.card := Finset.card_union_le C_core Init
  rw [Nat.card_Icc] at hcard_Icc
  exact ⟨hge, ht_le_n, by omega, ht_not_core⟩

private def zigMap (m : ℕ) (j : Fin m) : Fin m :=
  if j.val % 2 = 0 then ⟨j.val / 2, by omega⟩ else ⟨m - 1 - j.val / 2, by omega⟩

private lemma zigMap_injective (m : ℕ) : Function.Injective (zigMap m) := by
  intro j₁ j₂ heq
  have hval := congrArg (Fin.val : Fin m → ℕ) heq
  dsimp only [zigMap] at hval
  by_cases h1 : j₁.val % 2 = 0 <;> by_cases h2 : j₂.val % 2 = 0 <;>
    simp only [h1, h2, ↓reduceIte] at hval <;> exact Fin.ext (by omega)

-- Attach leaves of Hubs around an abstract SmallTreeResult S
private lemma attach_hub_leaves {n L : ℕ}
    (hL : 16384 ≤ L) (_hq0 : 10000000000 ≤ n / 100)
    (T : SimpleGraph (Fin (n + 1))) [DecidableRel T.Adj] (hT : T.IsTree)
    (core Hubs V_1 : Finset (Fin (n + 1)))
    (hcore_le : core.card ≤ n / 100)
    (hHubs_sub : Hubs ⊆ core)
    (hV1_Hubs : V_1 ⊆ Hubs)
    (hpart : ∀ x ∈ core, (x ∈ core \ Hubs ∧ x ∉ V_1 ∧ x ∉ Hubs \ V_1) ∨
                         (x ∉ core \ Hubs ∧ x ∈ V_1 ∧ x ∉ Hubs \ V_1) ∨
                         (x ∉ core \ Hubs ∧ x ∉ V_1 ∧ x ∈ Hubs \ V_1))
    (hrem_spec : ∀ w : Fin (n + 1), w ∉ core ↔ ∃ v ∈ Hubs, w ∈ leafNbrs T v)
    (hrem_deg : ∀ w : Fin (n + 1), w ∉ core → T.degree w = 1)
    (hHubs_L4 : ∀ v ∈ Hubs, L ^ 4 ≤ (leafNbrs T v).card)
    (hsum_Hubs : ∑ v ∈ Hubs, (leafNbrs T v).card = n + 1 - core.card)
    (hV1_width : V_1.card * (8 * L) ≤ n / 100)
    (hV2_width : (Hubs \ V_1).card * (8 * L) ≤ n / 100)
    (hm_pos : 1 ≤ V_1.card)
    (hV1_gt5 : 5 * (n / 100) < ∑ v ∈ V_1, (leafNbrs T v).card)
    (hV1_cases : (V_1.card = 1 ∧ ∑ v ∈ V_1, (leafNbrs T v).card < 75 * (n / 100)) ∨
                 (2 ≤ V_1.card ∧ ∑ v ∈ V_1, (leafNbrs T v).card ≤ 10 * (n / 100)))
    (r₀ : ↥(core : Set (Fin (n + 1))))
    (S : SmallTreeResult T core (core \ Hubs) V_1 (Hubs \ V_1) r₀ L) :
    ∃ g : Fin (n + 1) ↪ Fin (2 * n + 1),
      ∀ u₁ v₁ u₂ v₂, T.Adj u₁ v₁ → T.Adj u₂ v₂ →
        (g u₁ - g v₁ = g u₂ - g v₂ ∨ g u₁ - g v₁ = g v₂ - g u₂) →
        s(u₁, v₁) = s(u₂, v₂) := by
  classical
  set q0 := n / 100 with hq0_def
  have hn_q0 : 100 * q0 ≤ n := Nat.mul_div_le n 100
  set m := V_1.card with hm_def
  set ℓ := Hubs.card with hℓ_def
  have hm_add_V2 : (Hubs \ V_1).card + m = ℓ :=
    Finset.card_sdiff_add_card_eq_card hV1_Hubs
  have hm_le_ℓ : m ≤ ℓ := by omega
  let zigEquiv : Fin m ≃ Fin m :=
    Equiv.ofBijective (zigMap m)
      ((Fintype.bijective_iff_injective_and_card (zigMap m)).mpr ⟨zigMap_injective m, rfl⟩)
  let uFun : Fin ℓ → ↥Hubs := fun idx =>
    if h : idx.val < m then
      ⟨(S.z (zigEquiv ⟨idx.val, h⟩)).val, hV1_Hubs (S.z (zigEquiv ⟨idx.val, h⟩)).property⟩
    else
      ⟨(S.w ⟨idx.val - m, by omega⟩).val,
        (Finset.mem_sdiff.mp (S.w ⟨idx.val - m, by omega⟩).property).1⟩
  have huFun_inj : Function.Injective uFun := by
    intro i₁ i₂ heq
    have hval := congrArg Subtype.val heq
    dsimp only [uFun] at hval
    by_cases h1 : i₁.val < m <;> by_cases h2 : i₂.val < m
    · rw [dif_pos h1, dif_pos h2] at hval
      have hz := S.z.injective (Subtype.ext hval)
      have hzg := zigEquiv.injective hz
      exact Fin.ext (congrArg (Fin.val : Fin m → ℕ) hzg)
    · rw [dif_pos h1, dif_neg h2] at hval
      have hv1 := (S.z (zigEquiv ⟨i₁.val, h1⟩)).property
      have hv2 := (Finset.mem_sdiff.mp (S.w ⟨i₂.val - m, by omega⟩).property).2
      exact absurd (hval ▸ hv1) hv2
    · rw [dif_neg h1, dif_pos h2] at hval
      have hv1 := (Finset.mem_sdiff.mp (S.w ⟨i₁.val - m, by omega⟩).property).2
      have hv2 := (S.z (zigEquiv ⟨i₂.val, h2⟩)).property
      exact absurd (hval.symm ▸ hv2) hv1
    · rw [dif_neg h1, dif_neg h2] at hval
      have hw := S.w.injective (Subtype.ext hval)
      have hwv := congrArg (Fin.val : Fin (Hubs \ V_1).card → ℕ) hw
      dsimp at hwv
      exact Fin.ext (by omega)
  let uEquiv : Fin ℓ ≃ ↥Hubs :=
    Equiv.ofBijective uFun ((Fintype.bijective_iff_injective_and_card uFun).mpr
      ⟨huFun_inj, by simp [hℓ_def, Fintype.card_coe]⟩)
  let d : Fin ℓ → ℕ := fun idx => (leafNbrs T (uEquiv idx).val).card
  have hd_ge_L4 : ∀ idx : Fin ℓ, L ^ 4 ≤ d idx :=
    fun idx => hHubs_L4 (uEquiv idx).val (uEquiv idx).property
  let cum : ℕ → ℕ := fun k =>
    ∑ idx ∈ Finset.univ.filter (fun idx : Fin ℓ => idx.val < k), d idx
  have hcum_step : ∀ (k : ℕ) (hk : k < ℓ), cum (k + 1) = cum k + d ⟨k, hk⟩ := by
    intro k hk
    dsimp only [cum]
    have hflt : Finset.univ.filter (fun idx : Fin ℓ => idx.val < k + 1) =
        insert ⟨k, hk⟩ (Finset.univ.filter (fun idx : Fin ℓ => idx.val < k)) := by
      ext idx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      constructor
      · intro h; by_cases hik : idx.val = k
        · exact Or.inl (Fin.ext hik)
        · exact Or.inr (by omega)
      · rintro (rfl | h)
        · simp
        · omega
    rw [hflt, Finset.sum_insert]
    · ring
    · simp
  have hcum_gap : ∀ a k : ℕ, a + k ≤ ℓ → cum a + k * L ^ 4 ≤ cum (a + k) := by
    intro a k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hle
      have ih' := ih (by omega)
      have hst := hcum_step (a + k) (by omega)
      have hd_lb := hd_ge_L4 ⟨a + k, by omega⟩
      have hring : (k + 1) * L ^ 4 = k * L ^ 4 + L ^ 4 := by ring
      have heq_ak : a + (k + 1) = a + k + 1 := by omega
      rw [heq_ak, hst, hring]
      omega
  have hcum_mono : ∀ {a b : ℕ}, a ≤ b → b ≤ ℓ → cum a ≤ cum b := by
    intro a b hab hbl
    have h := hcum_gap a (b - a) (by omega)
    have heq : a + (b - a) = b := by omega
    rw [heq] at h
    omega
  have hcum_all : cum ℓ = n + 1 - core.card := by
    dsimp only [cum, d]
    have hflt : Finset.univ.filter (fun idx : Fin ℓ => idx.val < ℓ) = Finset.univ := by
      ext idx; simp
    rw [hflt, ← hsum_Hubs, ← Finset.sum_coe_sort Hubs]
    exact Fintype.sum_equiv uEquiv _ _ (fun _ => rfl)
  have hcum_m : cum m = ∑ v ∈ V_1, (leafNbrs T v).card := by
    dsimp only [cum, d]
    let eSub : Fin m ≃ {idx : Fin ℓ // idx ∈ Finset.univ.filter (fun idx : Fin ℓ => idx.val < m)} :=
      { toFun := fun j => ⟨⟨j.val, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, j.isLt⟩⟩
        invFun := fun idx => ⟨idx.1.val, (Finset.mem_filter.mp idx.2).2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [← Finset.sum_coe_sort, ← Fintype.sum_equiv eSub _ _ (fun _ => rfl)]
    have hval_eq : ∀ j : Fin m, (uEquiv (eSub j).1).val = (S.z (zigEquiv j)).val := by
      intro j
      change (uFun ⟨j.val, by omega⟩).val = _
      dsimp only [uFun]
      rw [dif_pos j.isLt]
    have hsum_congr : ∑ j : Fin m, (leafNbrs T (uEquiv (eSub j).1).val).card =
        ∑ j : Fin m, (leafNbrs T (S.z (zigEquiv j)).val).card :=
      Fintype.sum_congr _ _ (fun j => by rw [hval_eq j])
    rw [hsum_congr, ← Finset.sum_coe_sort V_1]
    exact Fintype.sum_equiv (zigEquiv.trans S.z) _ _ (fun _ => rfl)
  set C_rem := Finset.Icc 1 n \ S.C_core
  have hcore_coe_card : Fintype.card ↥(core : Set (Fin (n + 1))) = core.card :=
    card_coe_set_eq core
  have hC_rem_card : C_rem.card = cum ℓ := by
    have h1 : C_rem.card + S.C_core.card = (Finset.Icc 1 n).card :=
      Finset.card_sdiff_add_card_eq_card S.C_core_sub
    have h2 : (Finset.Icc 1 n).card = n := by simp
    have hpos_core : 1 ≤ core.card := Finset.card_pos.mpr ⟨r₀.val, r₀.property⟩
    rw [S.C_core_card, hcore_coe_card, h2] at h1
    omega
  let eCol := C_rem.orderEmbOfFin hC_rem_card
  have hhub_ex : ∀ w : Fin (n + 1), w ∉ core → ∃ v ∈ Hubs, w ∈ leafNbrs T v :=
    fun w hw => (hrem_spec w).mp hw
  let hubOf : (w : Fin (n + 1)) → w ∉ core → Fin (n + 1) :=
    fun w hw => (hhub_ex w hw).choose
  have hhub_Hubs : ∀ w hw, hubOf w hw ∈ Hubs :=
    fun w hw => (hhub_ex w hw).choose_spec.1
  have hhub_leaf : ∀ w hw, w ∈ leafNbrs T (hubOf w hw) :=
    fun w hw => (hhub_ex w hw).choose_spec.2
  have hhub_adj : ∀ w hw, T.Adj (hubOf w hw) w :=
    fun w hw => (Finset.mem_filter.mp (hhub_leaf w hw)).2.1
  let locEquiv : ∀ idx : Fin ℓ, ↥(leafNbrs T (uEquiv idx).val) ≃ Fin (d idx) :=
    fun idx => Fintype.equivFinOfCardEq (Fintype.card_coe _)
  let rIdx : {w : Fin (n + 1) // w ∉ core} → Fin ℓ :=
    fun w => uEquiv.symm ⟨hubOf w.val w.property, hhub_Hubs w.val w.property⟩
  have hrIdx_val : ∀ w : {w : Fin (n + 1) // w ∉ core},
      (uEquiv (rIdx w)).val = hubOf w.val w.property := by
    intro w
    dsimp [rIdx]
    rw [uEquiv.apply_symm_apply]
  let aIdx : (w : {w : Fin (n + 1) // w ∉ core}) → Fin (d (rIdx w)) :=
    fun w => locEquiv (rIdx w) ⟨w.val, by rw [hrIdx_val w]; exact hhub_leaf w.val w.property⟩
  have hrk_lt : ∀ w : {w : Fin (n + 1) // w ∉ core},
      cum (rIdx w).val + (aIdx w).val < cum ℓ := by
    intro w
    have hst := hcum_step (rIdx w).val (rIdx w).isLt
    have hm_mo := hcum_mono (by have := (rIdx w).isLt; omega : (rIdx w).val + 1 ≤ ℓ) (le_refl ℓ)
    have ha : (aIdx w).val < d (rIdx w) := (aIdx w).isLt
    have hd_eq : d ⟨(rIdx w).val, (rIdx w).isLt⟩ = d (rIdx w) := rfl
    rw [hd_eq] at hst
    omega
  let rk : {w : Fin (n + 1) // w ∉ core} → Fin (cum ℓ) :=
    fun w => ⟨cum (rIdx w).val + (aIdx w).val, hrk_lt w⟩
  have hrk_val : ∀ w, (rk w).val = cum (rIdx w).val + (aIdx w).val := fun _ => rfl
  have hrk_inj : Function.Injective rk := by
    intro w₁ w₂ heq
    have hval := congrArg (Fin.val : Fin (cum ℓ) → ℕ) heq
    rw [hrk_val w₁, hrk_val w₂] at hval
    have hr_eq : rIdx w₁ = rIdx w₂ := by
      by_contra hne
      rcases lt_trichotomy (rIdx w₁).val (rIdx w₂).val with hlt | h0 | hgt
      · have hst := hcum_step (rIdx w₁).val (rIdx w₁).isLt
        have hd_eq : d ⟨(rIdx w₁).val, (rIdx w₁).isLt⟩ = d (rIdx w₁) := rfl
        rw [hd_eq] at hst
        have hm_mo := hcum_mono (by omega : (rIdx w₁).val + 1 ≤ (rIdx w₂).val) (le_of_lt (rIdx w₂).isLt)
        have ha : (aIdx w₁).val < d (rIdx w₁) := (aIdx w₁).isLt
        omega
      · exact hne (Fin.ext h0)
      · have hst := hcum_step (rIdx w₂).val (rIdx w₂).isLt
        have hd_eq : d ⟨(rIdx w₂).val, (rIdx w₂).isLt⟩ = d (rIdx w₂) := rfl
        rw [hd_eq] at hst
        have hm_mo := hcum_mono (by omega : (rIdx w₂).val + 1 ≤ (rIdx w₁).val) (le_of_lt (rIdx w₁).isLt)
        have ha : (aIdx w₂).val < d (rIdx w₂) := (aIdx w₂).isLt
        omega
    have hcum_eq : cum (rIdx w₁).val = cum (rIdx w₂).val := by rw [hr_eq]
    have ha_val : (aIdx w₁).val = (aIdx w₂).val := by omega
    have hloc1 : ∀ (w : {w : Fin (n + 1) // w ∉ core}) (idx : Fin ℓ) (h : rIdx w = idx),
        ((locEquiv idx) ⟨w.val, by rw [← h, hrIdx_val w]; exact hhub_leaf w.val w.property⟩).val =
          (aIdx w).val := by
      intro w idx h; subst h; rfl
    have heq_loc : (locEquiv (rIdx w₂)) ⟨w₁.val, by
          rw [← hr_eq, hrIdx_val w₁]; exact hhub_leaf w₁.val w₁.property⟩ =
        (locEquiv (rIdx w₂)) ⟨w₂.val, by
          rw [hrIdx_val w₂]; exact hhub_leaf w₂.val w₂.property⟩ := by
      apply Fin.ext
      rw [hloc1 w₁ (rIdx w₂) hr_eq, hloc1 w₂ (rIdx w₂) rfl, ha_val]
    have hw_sub := (locEquiv (rIdx w₂)).injective heq_loc
    exact Subtype.ext
      (congrArg (Subtype.val : ↥(leafNbrs T (uEquiv (rIdx w₂)).val) → Fin (n + 1)) hw_sub)
  let colLeaf : {w : Fin (n + 1) // w ∉ core} → ℕ := fun w => eCol (rk w)
  have hcolLeaf_inj : Function.Injective colLeaf :=
    fun _ _ h => hrk_inj (eCol.injective h)
  have hcolLeaf_bounds : ∀ w : {w : Fin (n + 1) // w ∉ core},
      (rk w).val + 1 ≤ colLeaf w ∧ colLeaf w ≤ n ∧
      colLeaf w ≤ (rk w).val + 1 + S.C_core.card ∧ colLeaf w ∉ S.C_core :=
    fun w => orderEmb_bounds hC_rem_card (rk w)
  let hPos : Fin ℓ → ℕ := fun idx =>
    S.posCore ⟨(uEquiv idx).val, hHubs_sub (uEquiv idx).property⟩
  let leafPos : {w : Fin (n + 1) // w ∉ core} → ℕ := fun w =>
    if (rIdx w).val < m ∧ (rIdx w).val % 2 = 0 then
      hPos (rIdx w) - colLeaf w
    else
      hPos (rIdx w) + colLeaf w
  have hhPos_V1 : ∀ (j : ℕ) (hj : j < m),
      hPos ⟨j, by omega⟩ ∈
        Finset.Ico (77 * q0 + (zigMap m ⟨j, hj⟩).val * (8 * L))
                   (77 * q0 + (zigMap m ⟨j, hj⟩).val * (8 * L) + 8 * L) := by
    intro j hj
    have hu_eq : (uEquiv ⟨j, by omega⟩).val = (S.z (zigMap m ⟨j, hj⟩)).val := by
      change (uFun ⟨j, by omega⟩).val = _
      dsimp only [uFun, zigEquiv]
      rw [dif_pos hj]
      rfl
    have hsub_eq : (⟨(uEquiv ⟨j, by omega⟩).val, hHubs_sub (uEquiv ⟨j, by omega⟩).property⟩ :
        ↥(core : Set (Fin (n + 1)))) =
        ⟨(S.z (zigMap m ⟨j, hj⟩)).val, S.z_mem_core (zigMap m ⟨j, hj⟩)⟩ := Subtype.ext hu_eq
    dsimp only [hPos]
    rw [hsub_eq]
    exact S.pos_z (zigMap m ⟨j, hj⟩)
  have hhPos_V1_in : ∀ (idx : Fin ℓ), idx.val < m → 77 * q0 ≤ hPos idx ∧ hPos idx < 78 * q0 := by
    intro idx hlt
    have hI := Finset.mem_Ico.mp (hhPos_V1 idx.val hlt)
    have hj_ub : (zigMap m ⟨idx.val, hlt⟩).val * (8 * L) + 8 * L ≤ m * (8 * L) := by
      calc (zigMap m ⟨idx.val, hlt⟩).val * (8 * L) + 8 * L =
            ((zigMap m ⟨idx.val, hlt⟩).val + 1) * (8 * L) := (Nat.succ_mul _ _).symm
        _ ≤ m * (8 * L) := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt (zigMap m ⟨idx.val, hlt⟩).isLt)
    have hi_eq : (⟨idx.val, by omega⟩ : Fin ℓ) = idx := Fin.ext rfl
    rw [hi_eq] at hI
    omega
  have hhPos_V2 : ∀ (idx : Fin ℓ), ¬ idx.val < m →
      hPos idx ∈ Finset.Ico (98 * q0 + (idx.val - m) * (8 * L))
                            (98 * q0 + (idx.val - m) * (8 * L) + 8 * L) := by
    intro idx hnlt
    have hu_eq : (uEquiv idx).val = (S.w ⟨idx.val - m, by omega⟩).val := by
      change (uFun idx).val = _
      dsimp only [uFun]
      rw [dif_neg hnlt]
    have hsub_eq : (⟨(uEquiv idx).val, hHubs_sub (uEquiv idx).property⟩ :
        ↥(core : Set (Fin (n + 1)))) =
        ⟨(S.w ⟨idx.val - m, by omega⟩).val, S.w_mem_core ⟨idx.val - m, by omega⟩⟩ :=
      Subtype.ext hu_eq
    dsimp only [hPos]
    rw [hsub_eq]
    exact S.pos_w ⟨idx.val - m, by omega⟩
  have hhPos_V2_in : ∀ (idx : Fin ℓ), ¬ idx.val < m → 98 * q0 ≤ hPos idx ∧ hPos idx < 99 * q0 := by
    intro idx hnlt
    have hI := Finset.mem_Ico.mp (hhPos_V2 idx hnlt)
    have hj_ub : (idx.val - m) * (8 * L) + 8 * L ≤ (Hubs \ V_1).card * (8 * L) := by
      calc (idx.val - m) * (8 * L) + 8 * L = (idx.val - m + 1) * (8 * L) := (Nat.succ_mul _ _).symm
        _ ≤ (Hubs \ V_1).card * (8 * L) := Nat.mul_le_mul_right _ (by omega)
    omega
  have hcol_V1_ub : ∀ w : {w : Fin (n + 1) // w ∉ core}, (rIdx w).val < m →
      (m = 1 ∧ colLeaf w ≤ 76 * q0) ∨ (2 ≤ m ∧ colLeaf w ≤ 11 * q0) := by
    intro w hlt
    have hob := hcolLeaf_bounds w
    have hrk_ub : (rk w).val < cum m := by
      have hst := hcum_step (rIdx w).val (rIdx w).isLt
      have hd_eq : d ⟨(rIdx w).val, (rIdx w).isLt⟩ = d (rIdx w) := rfl
      rw [hd_eq] at hst
      have hm_mo := hcum_mono (by omega : (rIdx w).val + 1 ≤ m) hm_le_ℓ
      have ha : (aIdx w).val < d (rIdx w) := (aIdx w).isLt
      rw [hrk_val w]; omega
    have hcore_card_ub : S.C_core.card ≤ q0 := by
      rw [S.C_core_card, hcore_coe_card]
      omega
    rcases hV1_cases with ⟨hm1, hsum75⟩ | ⟨hm2, hsum10⟩
    · rw [← hcum_m] at hsum75
      exact Or.inl ⟨hm1, by omega⟩
    · rw [← hcum_m] at hsum10
      exact Or.inr ⟨hm2, by omega⟩
  have hL4_gt_16L : 16 * L < L ^ 4 := by
    have h16 : 16 < L ^ 3 := by
      calc 16 < 16384 ^ 3 := by norm_num
        _ ≤ L ^ 3 := Nat.pow_le_pow_left hL 3
    calc 16 * L < L ^ 3 * L := Nat.mul_lt_mul_of_pos_right h16 (by omega)
      _ = L ^ 4 := by ring
  have htype1_lt : ∀ (w₁ w₂ : {w : Fin (n + 1) // w ∉ core}),
      (rIdx w₁).val < m → (rIdx w₁).val % 2 = 0 →
      (rIdx w₂).val < m → (rIdx w₂).val % 2 = 0 →
      (rIdx w₁).val < (rIdx w₂).val →
      leafPos w₂ < leafPos w₁ := by
    intro w₁ w₂ hm1 he1 hm2 he2 hlt
    set q₁ := (rIdx w₁).val / 2 with hq1_def
    set q₂ := (rIdx w₂).val / 2 with hq2_def
    have hq_lt : q₁ < q₂ := by omega
    have h1_I := Finset.mem_Ico.mp (hhPos_V1 (rIdx w₁).val hm1)
    have h2_I := Finset.mem_Ico.mp (hhPos_V1 (rIdx w₂).val hm2)
    have hi1_eq : (⟨(rIdx w₁).val, by omega⟩ : Fin ℓ) = rIdx w₁ := Fin.ext rfl
    have hi2_eq : (⟨(rIdx w₂).val, by omega⟩ : Fin ℓ) = rIdx w₂ := Fin.ext rfl
    rw [hi1_eq] at h1_I; rw [hi2_eq] at h2_I
    have hzg1 : (zigMap m ⟨(rIdx w₁).val, hm1⟩).val = q₁ := by simp [zigMap, he1, hq1_def]
    have hzg2 : (zigMap m ⟨(rIdx w₂).val, hm2⟩).val = q₂ := by simp [zigMap, he2, hq2_def]
    rw [hzg1] at h1_I; rw [hzg2] at h2_I
    have hpos_diff : hPos (rIdx w₂) - hPos (rIdx w₁) < (q₂ - q₁) * L ^ 4 := by
      have hmul1 : q₂ * (8 * L) + 8 * L = q₁ * (8 * L) + (q₂ + 1 - q₁) * (8 * L) := by
        have hq_eq : q₂ + 1 = q₁ + (q₂ + 1 - q₁) := by omega
        calc q₂ * (8 * L) + 8 * L = (q₂ + 1) * (8 * L) := (Nat.succ_mul _ _).symm
          _ = (q₁ + (q₂ + 1 - q₁)) * (8 * L) := congrArg (· * (8 * L)) hq_eq
          _ = q₁ * (8 * L) + (q₂ + 1 - q₁) * (8 * L) := Nat.add_mul _ _ _
      have hu_pos : 8 * L ≤ (q₂ + 1 - q₁) * (8 * L) := by
        simpa using Nat.mul_le_mul_right (8 * L) (by omega : 1 ≤ q₂ + 1 - q₁)
      have hd1 : hPos (rIdx w₂) - hPos (rIdx w₁) < (q₂ + 1 - q₁) * (8 * L) := by omega
      have hd2 : (q₂ + 1 - q₁) * (8 * L) ≤ (q₂ - q₁) * (16 * L) := by
        have hle_q : q₂ + 1 - q₁ ≤ 2 * (q₂ - q₁) := by omega
        calc (q₂ + 1 - q₁) * (8 * L) ≤ (2 * (q₂ - q₁)) * (8 * L) := Nat.mul_le_mul_right _ hle_q
          _ = (q₂ - q₁) * (16 * L) := by ring
      have hd3 : (q₂ - q₁) * (16 * L) < (q₂ - q₁) * L ^ 4 :=
        Nat.mul_lt_mul_of_pos_left hL4_gt_16L (by omega)
      omega
    have hrk_diff : (q₂ - q₁) * L ^ 4 < colLeaf w₂ - colLeaf w₁ := by
      have hst1 := hcum_step (rIdx w₁).val (rIdx w₁).isLt
      have hd_eq : d ⟨(rIdx w₁).val, (rIdx w₁).isLt⟩ = d (rIdx w₁) := rfl
      rw [hd_eq] at hst1
      have hgap := hcum_gap ((rIdx w₁).val + 1) ((rIdx w₂).val - ((rIdx w₁).val + 1)) (by omega)
      have heq_r2 : (rIdx w₁).val + 1 + ((rIdx w₂).val - ((rIdx w₁).val + 1)) = (rIdx w₂).val := by omega
      rw [heq_r2] at hgap
      have hmul_ge : (q₂ - q₁) * L ^ 4 ≤ ((rIdx w₂).val - ((rIdx w₁).val + 1)) * L ^ 4 :=
        Nat.mul_le_mul_right _ (by omega)
      have ha1 : (aIdx w₁).val < d (rIdx w₁) := (aIdx w₁).isLt
      have hrk_le : (rk w₁).val ≤ (rk w₂).val := by rw [hrk_val w₁, hrk_val w₂]; omega
      have hcol_ge := orderEmb_sub_ge hC_rem_card (rk w₁) (rk w₂) hrk_le
      change (rk w₂).val - (rk w₁).val ≤ colLeaf w₂ - colLeaf w₁ at hcol_ge
      rw [hrk_val w₁, hrk_val w₂] at hcol_ge
      omega
    have hc1_ub := hcol_V1_ub w₁ hm1
    have hc2_ub := hcol_V1_ub w₂ hm2
    have hp1_b := hhPos_V1_in (rIdx w₁) hm1
    have hp2_b := hhPos_V1_in (rIdx w₂) hm2
    dsimp only [leafPos]
    rw [if_pos ⟨hm2, he2⟩, if_pos ⟨hm1, he1⟩]
    rcases hc1_ub with ⟨_, h1b⟩ | ⟨_, h1b⟩ <;> rcases hc2_ub with ⟨_, h2b⟩ | ⟨_, h2b⟩ <;> omega
  have htype2_lt : ∀ (w₁ w₂ : {w : Fin (n + 1) // w ∉ core}),
      (rIdx w₁).val < m → (rIdx w₁).val % 2 ≠ 0 →
      (rIdx w₂).val < m → (rIdx w₂).val % 2 ≠ 0 →
      (rIdx w₁).val < (rIdx w₂).val →
      leafPos w₁ < leafPos w₂ := by
    intro w₁ w₂ hm1 ho1 hm2 ho2 hlt
    set q₁ := (rIdx w₁).val / 2 with hq1_def
    set q₂ := (rIdx w₂).val / 2 with hq2_def
    have hq_lt : q₁ < q₂ := by omega
    have h1_I := Finset.mem_Ico.mp (hhPos_V1 (rIdx w₁).val hm1)
    have h2_I := Finset.mem_Ico.mp (hhPos_V1 (rIdx w₂).val hm2)
    have hi1_eq : (⟨(rIdx w₁).val, by omega⟩ : Fin ℓ) = rIdx w₁ := Fin.ext rfl
    have hi2_eq : (⟨(rIdx w₂).val, by omega⟩ : Fin ℓ) = rIdx w₂ := Fin.ext rfl
    rw [hi1_eq] at h1_I; rw [hi2_eq] at h2_I
    set s₁ := m - 1 - q₁ with hs1_def
    set s₂ := m - 1 - q₂ with hs2_def
    have hzg1 : (zigMap m ⟨(rIdx w₁).val, hm1⟩).val = s₁ := by simp [zigMap, ho1, hs1_def, hq1_def]
    have hzg2 : (zigMap m ⟨(rIdx w₂).val, hm2⟩).val = s₂ := by simp [zigMap, ho2, hs2_def, hq2_def]
    rw [hzg1] at h1_I; rw [hzg2] at h2_I
    have hpos_diff : hPos (rIdx w₁) - hPos (rIdx w₂) < (q₂ - q₁) * L ^ 4 := by
      have hs_diff : s₁ + 1 - s₂ ≤ 2 * (q₂ - q₁) := by omega
      have hmul1 : s₁ * (8 * L) + 8 * L = s₂ * (8 * L) + (s₁ + 1 - s₂) * (8 * L) := by
        have hs_eq : s₁ + 1 = s₂ + (s₁ + 1 - s₂) := by omega
        calc s₁ * (8 * L) + 8 * L = (s₁ + 1) * (8 * L) := (Nat.succ_mul _ _).symm
          _ = (s₂ + (s₁ + 1 - s₂)) * (8 * L) := congrArg (· * (8 * L)) hs_eq
          _ = s₂ * (8 * L) + (s₁ + 1 - s₂) * (8 * L) := Nat.add_mul _ _ _
      have hu_pos : 8 * L ≤ (s₁ + 1 - s₂) * (8 * L) := by
        simpa using Nat.mul_le_mul_right (8 * L) (by omega : 1 ≤ s₁ + 1 - s₂)
      have hd1 : hPos (rIdx w₁) - hPos (rIdx w₂) < (s₁ + 1 - s₂) * (8 * L) := by omega
      have hd2 : (s₁ + 1 - s₂) * (8 * L) ≤ (q₂ - q₁) * (16 * L) := by
        calc (s₁ + 1 - s₂) * (8 * L) ≤ (2 * (q₂ - q₁)) * (8 * L) := Nat.mul_le_mul_right _ hs_diff
          _ = (q₂ - q₁) * (16 * L) := by ring
      have hd3 : (q₂ - q₁) * (16 * L) < (q₂ - q₁) * L ^ 4 :=
        Nat.mul_lt_mul_of_pos_left hL4_gt_16L (by omega)
      omega
    have hrk_diff : (q₂ - q₁) * L ^ 4 < colLeaf w₂ - colLeaf w₁ := by
      have hst1 := hcum_step (rIdx w₁).val (rIdx w₁).isLt
      have hd_eq : d ⟨(rIdx w₁).val, (rIdx w₁).isLt⟩ = d (rIdx w₁) := rfl
      rw [hd_eq] at hst1
      have hgap := hcum_gap ((rIdx w₁).val + 1) ((rIdx w₂).val - ((rIdx w₁).val + 1)) (by omega)
      have heq_r2 : (rIdx w₁).val + 1 + ((rIdx w₂).val - ((rIdx w₁).val + 1)) = (rIdx w₂).val := by omega
      rw [heq_r2] at hgap
      have hmul_ge : (q₂ - q₁) * L ^ 4 ≤ ((rIdx w₂).val - ((rIdx w₁).val + 1)) * L ^ 4 :=
        Nat.mul_le_mul_right _ (by omega)
      have ha1 : (aIdx w₁).val < d (rIdx w₁) := (aIdx w₁).isLt
      have hrk_le : (rk w₁).val ≤ (rk w₂).val := by rw [hrk_val w₁, hrk_val w₂]; omega
      have hcol_ge := orderEmb_sub_ge hC_rem_card (rk w₁) (rk w₂) hrk_le
      change (rk w₂).val - (rk w₁).val ≤ colLeaf w₂ - colLeaf w₁ at hcol_ge
      rw [hrk_val w₁, hrk_val w₂] at hcol_ge
      omega
    dsimp only [leafPos]
    rw [if_neg (by omega), if_neg (by omega)]
    omega
  have hleaf_type1_bounds : ∀ w : {w : Fin (n + 1) // w ∉ core},
      (rIdx w).val < m → (rIdx w).val % 2 = 0 →
      q0 ≤ leafPos w ∧ leafPos w < hPos ⟨0, by omega⟩ := by
    intro w hlt hev
    have hcol_pos : 1 ≤ colLeaf w := by have := (hcolLeaf_bounds w).1; omega
    have hpb := hhPos_V1_in (rIdx w) hlt
    have hcub := hcol_V1_ub w hlt
    have hlb : q0 ≤ leafPos w := by
      dsimp only [leafPos]
      rw [if_pos ⟨hlt, hev⟩]
      rcases hcub with ⟨_, hb⟩ | ⟨_, hb⟩ <;> omega
    refine ⟨hlb, ?_⟩
    by_cases hr0 : (rIdx w).val = 0
    · have hr_eq : rIdx w = ⟨0, by omega⟩ := Fin.ext hr0
      dsimp only [leafPos]
      rw [if_pos ⟨hlt, hev⟩, hr_eq]
      have hp0 := hhPos_V1_in ⟨0, by omega⟩ hm_pos
      omega
    · have hd0_pos : 0 < d ⟨0, by omega⟩ := by
        have := hd_ge_L4 ⟨0, by omega⟩
        have : 1 ≤ L ^ 4 := Nat.one_le_pow 4 L (by omega)
        omega
      let w0_sub := (locEquiv ⟨0, by omega⟩).symm ⟨0, hd0_pos⟩
      have hw0_not_core : w0_sub.val ∉ core :=
        (hrem_spec w0_sub.val).mpr ⟨(uEquiv ⟨0, by omega⟩).val,
          (uEquiv ⟨0, by omega⟩).property, w0_sub.property⟩
      let w0 : {w : Fin (n + 1) // w ∉ core} := ⟨w0_sub.val, hw0_not_core⟩
      have hr_w0 : rIdx w0 = ⟨0, by omega⟩ := by
        apply uEquiv.injective
        apply Subtype.ext
        rw [hrIdx_val w0]
        obtain ⟨_, hadj1, hd1⟩ := Finset.mem_filter.mp w0_sub.property
        have hadj2 := hhub_adj w0.val w0.property
        obtain ⟨u, _, hu⟩ := degree_eq_one_iff_existsUnique_adj.mp hd1
        exact (hu _ hadj2.symm).trans (hu _ hadj1.symm).symm
      have hlt_w0 : leafPos w < leafPos w0 :=
        htype1_lt w0 w (by rw [hr_w0]; exact hm_pos) (by rw [hr_w0]; simp) hlt hev
          (by rw [hr_w0]; simp; omega)
      have hcol0_pos : 1 ≤ colLeaf w0 := by have := (hcolLeaf_bounds w0).1; omega
      have hp0 := hhPos_V1_in ⟨0, by omega⟩ hm_pos
      have hl0_lt : leafPos w0 < hPos ⟨0, by omega⟩ := by
        dsimp only [leafPos]
        rw [if_pos ⟨by rw [hr_w0]; exact hm_pos, by rw [hr_w0]; simp⟩, hr_w0]
        omega
      omega
  have hleaf_type2_bounds : ∀ w : {w : Fin (n + 1) // w ∉ core},
      (rIdx w).val < m → (rIdx w).val % 2 ≠ 0 →
      ∃ _hm2 : 2 ≤ m, hPos ⟨1, by omega⟩ < leafPos w ∧ leafPos w < 89 * q0 := by
    intro w hlt hodd
    have hm2 : 2 ≤ m := by omega
    refine ⟨hm2, ?_, ?_⟩
    · by_cases hr1 : (rIdx w).val = 1
      · have hr_eq : rIdx w = ⟨1, by omega⟩ := Fin.ext hr1
        have hcol_pos : 1 ≤ colLeaf w := by have := (hcolLeaf_bounds w).1; omega
        dsimp only [leafPos]
        rw [if_neg (by omega), hr_eq]
        omega
      · have hd1_pos : 0 < d ⟨1, by omega⟩ := by
          have := hd_ge_L4 ⟨1, by omega⟩
          have : 1 ≤ L ^ 4 := Nat.one_le_pow 4 L (by omega)
          omega
        let w1_sub := (locEquiv ⟨1, by omega⟩).symm ⟨0, hd1_pos⟩
        have hw1_not_core : w1_sub.val ∉ core :=
          (hrem_spec w1_sub.val).mpr ⟨(uEquiv ⟨1, by omega⟩).val,
            (uEquiv ⟨1, by omega⟩).property, w1_sub.property⟩
        let w1 : {w : Fin (n + 1) // w ∉ core} := ⟨w1_sub.val, hw1_not_core⟩
        have hr_w1 : rIdx w1 = ⟨1, by omega⟩ := by
          apply uEquiv.injective
          apply Subtype.ext
          rw [hrIdx_val w1]
          obtain ⟨_, hadj1, hd1⟩ := Finset.mem_filter.mp w1_sub.property
          have hadj2 := hhub_adj w1.val w1.property
          obtain ⟨u, _, hu⟩ := degree_eq_one_iff_existsUnique_adj.mp hd1
          exact (hu _ hadj2.symm).trans (hu _ hadj1.symm).symm
        have hlt_w1 : leafPos w1 < leafPos w :=
          htype2_lt w1 w (by rw [hr_w1]; exact hm2) (by rw [hr_w1]; simp) hlt hodd
            (by rw [hr_w1]; simp; omega)
        have hcol1_pos : 1 ≤ colLeaf w1 := by have := (hcolLeaf_bounds w1).1; omega
        have hl1_gt : hPos ⟨1, by omega⟩ < leafPos w1 := by
          dsimp only [leafPos]
          rw [if_neg (by rw [hr_w1]; simp), hr_w1]
          omega
        omega
    · have hpb := hhPos_V1_in (rIdx w) hlt
      have hcub := hcol_V1_ub w hlt
      dsimp only [leafPos]
      rw [if_neg (by omega)]
      rcases hcub with ⟨hm1, _⟩ | ⟨_, hb⟩ <;> omega
  have hleaf_type3_bounds : ∀ w : {w : Fin (n + 1) // w ∉ core},
      ¬ (rIdx w).val < m →
      103 * q0 < leafPos w ∧ leafPos w < 2 * n := by
    intro w hnlt
    have hob := hcolLeaf_bounds w
    have hpb := hhPos_V2_in (rIdx w) hnlt
    have hrk_ge_m : cum m ≤ (rk w).val := by
      have hm_mo := hcum_mono (not_lt.mp hnlt) (le_of_lt (rIdx w).isLt)
      rw [hrk_val w]; omega
    have hcol_gt5 : 5 * q0 < colLeaf w := by
      rw [hcum_m] at hrk_ge_m
      omega
    have hcol_le_n : colLeaf w ≤ n := hob.2.1
    dsimp only [leafPos]
    rw [if_neg (by omega)]
    omega
  have hcore_V1_bounds : ∀ x : ↥(core : Set (Fin (n + 1))), x.val ∈ V_1 →
      (m = 1 ∧ S.posCore x = hPos ⟨0, by omega⟩) ∨
      (∃ _hm2 : 2 ≤ m, hPos ⟨0, by omega⟩ ≤ S.posCore x ∧ S.posCore x ≤ hPos ⟨1, by omega⟩ ∧
        hPos ⟨1, by omega⟩ < 78 * q0) := by
    intro x hx1
    let q := S.z.symm ⟨x.val, hx1⟩
    have hxq : (S.z q).val = x.val := congrArg Subtype.val (S.z.apply_symm_apply ⟨x.val, hx1⟩)
    have hx_sub : x = ⟨(S.z q).val, S.z_mem_core q⟩ := Subtype.ext hxq.symm
    have hpos_q := Finset.mem_Ico.mp (S.pos_z q)
    rw [← hx_sub, ← hq0_def] at hpos_q
    by_cases hm1 : m = 1
    · left
      refine ⟨hm1, ?_⟩
      have hq0_eq : q = zigMap m ⟨0, by omega⟩ := by
        have hlt_q : q.val < V_1.card := q.isLt
        have hlt_z : (zigMap m ⟨0, by omega⟩).val < m := (zigMap m ⟨0, by omega⟩).isLt
        exact Fin.ext (by omega)
      have hu0_eq : (uEquiv ⟨0, by omega⟩).val = (S.z q).val := by
        rw [hq0_eq]
        change (uFun ⟨0, by omega⟩).val = _
        dsimp only [uFun, zigEquiv]; rw [dif_pos (by omega : 0 < m)]; rfl
      dsimp only [hPos]
      exact congrArg S.posCore (Subtype.ext (hxq.symm.trans hu0_eq.symm))
    · right
      have hm2 : 2 ≤ m := by omega
      have hp1_ub := (hhPos_V1_in ⟨1, by omega⟩ hm2).2
      refine ⟨hm2, ?_, ?_, hp1_ub⟩
      · by_cases hq0_case : q.val = 0
        · have hqz : q = zigMap m ⟨0, by omega⟩ := by apply Fin.ext; simp [zigMap, hq0_case]
          have hu0_eq : (uEquiv ⟨0, by omega⟩).val = (S.z q).val := by
            rw [hqz]
            change (uFun ⟨0, by omega⟩).val = _
            dsimp only [uFun, zigEquiv]; rw [dif_pos (by omega : 0 < m)]; rfl
          have heq_pos : S.posCore x = hPos ⟨0, by omega⟩ :=
            congrArg S.posCore (Subtype.ext (hxq.symm.trans hu0_eq.symm))
          omega
        · have hp0_I := Finset.mem_Ico.mp (hhPos_V1 0 (by omega))
          have hz0 : (zigMap m ⟨0, by omega⟩).val = 0 := by simp [zigMap]
          rw [hz0, Nat.zero_mul, Nat.add_zero] at hp0_I
          have h1L : 8 * L ≤ q.val * (8 * L) := by
            calc 8 * L = 1 * (8 * L) := (Nat.one_mul _).symm
              _ ≤ q.val * (8 * L) := Nat.mul_le_mul_right _ (by omega)
          omega
      · by_cases hqm_case : q.val = m - 1
        · have hqz : q = zigMap m ⟨1, by omega⟩ := by apply Fin.ext; simp [zigMap, hqm_case]
          have hu1_eq : (uEquiv ⟨1, by omega⟩).val = (S.z q).val := by
            rw [hqz]
            change (uFun ⟨1, by omega⟩).val = _
            dsimp only [uFun, zigEquiv]; rw [dif_pos (by omega : 1 < m)]; rfl
          have heq_pos : S.posCore x = hPos ⟨1, by omega⟩ :=
            congrArg S.posCore (Subtype.ext (hxq.symm.trans hu1_eq.symm))
          omega
        · have hp1_I := Finset.mem_Ico.mp (hhPos_V1 1 (by omega))
          have hz1 : (zigMap m ⟨1, by omega⟩).val = m - 1 := by simp [zigMap]
          rw [hz1] at hp1_I
          have hq_lt_m1 : q.val + 1 ≤ m - 1 := by
            have hlt : q.val < V_1.card := q.isLt
            omega
          have hle_m : q.val * (8 * L) + 8 * L ≤ (m - 1) * (8 * L) := by
            calc q.val * (8 * L) + 8 * L = (q.val + 1) * (8 * L) := (Nat.succ_mul _ _).symm
              _ ≤ (m - 1) * (8 * L) := Nat.mul_le_mul_right _ hq_lt_m1
          omega
  have hcore_V02_bounds : ∀ x : ↥(core : Set (Fin (n + 1))), x.val ∉ V_1 →
      90 * q0 ≤ S.posCore x ∧ S.posCore x < 99 * q0 := by
    intro x hx1n
    rcases hpart x.val x.property with ⟨h0, _, _⟩ | ⟨_, h1, _⟩ | ⟨_, _, h2⟩
    · have hI := Finset.mem_Ico.mp (S.pos_V0 x h0)
      rw [← hq0_def] at hI; omega
    · exact absurd h1 hx1n
    · let q := S.w.symm ⟨x.val, h2⟩
      have hxq : (S.w q).val = x.val := congrArg Subtype.val (S.w.apply_symm_apply ⟨x.val, h2⟩)
      have hx_sub : x = ⟨(S.w q).val, S.w_mem_core q⟩ := Subtype.ext hxq.symm
      have hpos_q := Finset.mem_Ico.mp (S.pos_w q)
      rw [← hx_sub, ← hq0_def] at hpos_q
      have hj_ub : q.val * (8 * L) + 8 * L ≤ (Hubs \ V_1).card * (8 * L) := by
        calc q.val * (8 * L) + 8 * L = (q.val + 1) * (8 * L) := (Nat.succ_mul _ _).symm
          _ ≤ (Hubs \ V_1).card * (8 * L) := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt q.isLt)
      omega
  have hleafPos_inj : Function.Injective leafPos := by
    intro w₁ w₂ heq
    by_cases hm1 : (rIdx w₁).val < m <;> by_cases hm2 : (rIdx w₂).val < m
    · by_cases he1 : (rIdx w₁).val % 2 = 0 <;> by_cases he2 : (rIdx w₂).val % 2 = 0
      · rcases lt_trichotomy (rIdx w₁).val (rIdx w₂).val with hlt | hr_eq | hgt
        · have := htype1_lt w₁ w₂ hm1 he1 hm2 he2 hlt; omega
        · have hr_fin : rIdx w₁ = rIdx w₂ := Fin.ext hr_eq
          dsimp only [leafPos] at heq
          rw [if_pos ⟨hm1, he1⟩, if_pos ⟨hm2, he2⟩, hr_fin] at heq
          have hp := hhPos_V1_in (rIdx w₂) hm2
          have hc1 := hcol_V1_ub w₁ hm1
          have hc2 := hcol_V1_ub w₂ hm2
          have hcol_eq : colLeaf w₁ = colLeaf w₂ := by
            rcases hc1 with ⟨_, b1⟩ | ⟨_, b1⟩ <;> rcases hc2 with ⟨_, b2⟩ | ⟨_, b2⟩ <;> omega
          exact hcolLeaf_inj hcol_eq
        · have := htype1_lt w₂ w₁ hm2 he2 hm1 he1 hgt; omega
      · have hb1 := hleaf_type1_bounds w₁ hm1 he1
        obtain ⟨hm_ge2, hb2, _⟩ := hleaf_type2_bounds w₂ hm2 he2
        have hp0_I := Finset.mem_Ico.mp (hhPos_V1 0 (by omega))
        have hp1_I := Finset.mem_Ico.mp (hhPos_V1 1 (by omega))
        have hz0 : (zigMap m ⟨0, by omega⟩).val = 0 := by simp [zigMap]
        have hz1 : (zigMap m ⟨1, by omega⟩).val = m - 1 := by simp [zigMap]
        rw [hz0, Nat.zero_mul, Nat.add_zero] at hp0_I
        rw [hz1] at hp1_I
        have h1L : 8 * L ≤ (m - 1) * (8 * L) := by
          calc 8 * L = 1 * (8 * L) := (Nat.one_mul _).symm
            _ ≤ (m - 1) * (8 * L) := Nat.mul_le_mul_right _ (by omega)
        omega
      · obtain ⟨hm_ge2, hb1, _⟩ := hleaf_type2_bounds w₁ hm1 he1
        have hb2 := hleaf_type1_bounds w₂ hm2 he2
        have hp0_I := Finset.mem_Ico.mp (hhPos_V1 0 (by omega))
        have hp1_I := Finset.mem_Ico.mp (hhPos_V1 1 (by omega))
        have hz0 : (zigMap m ⟨0, by omega⟩).val = 0 := by simp [zigMap]
        have hz1 : (zigMap m ⟨1, by omega⟩).val = m - 1 := by simp [zigMap]
        rw [hz0, Nat.zero_mul, Nat.add_zero] at hp0_I
        rw [hz1] at hp1_I
        have h1L : 8 * L ≤ (m - 1) * (8 * L) := by
          calc 8 * L = 1 * (8 * L) := (Nat.one_mul _).symm
            _ ≤ (m - 1) * (8 * L) := Nat.mul_le_mul_right _ (by omega)
        omega
      · rcases lt_trichotomy (rIdx w₁).val (rIdx w₂).val with hlt | hr_eq | hgt
        · have := htype2_lt w₁ w₂ hm1 he1 hm2 he2 hlt; omega
        · have hr_fin : rIdx w₁ = rIdx w₂ := Fin.ext hr_eq
          dsimp only [leafPos] at heq
          rw [if_neg (by omega), if_neg (by omega), hr_fin] at heq
          exact hcolLeaf_inj (by omega)
        · have := htype2_lt w₂ w₁ hm2 he2 hm1 he1 hgt; omega
    · have hb2 := hleaf_type3_bounds w₂ hm2
      by_cases he1 : (rIdx w₁).val % 2 = 0
      · have hb1 := hleaf_type1_bounds w₁ hm1 he1
        have hp0 := hhPos_V1_in ⟨0, by omega⟩ hm_pos
        omega
      · obtain ⟨_, _, hb1⟩ := hleaf_type2_bounds w₁ hm1 he1
        omega
    · have hb1 := hleaf_type3_bounds w₁ hm1
      by_cases he2 : (rIdx w₂).val % 2 = 0
      · have hb2 := hleaf_type1_bounds w₂ hm2 he2
        have hp0 := hhPos_V1_in ⟨0, by omega⟩ hm_pos
        omega
      · obtain ⟨_, _, hb2⟩ := hleaf_type2_bounds w₂ hm2 he2
        omega
    · dsimp only [leafPos] at heq
      rw [if_neg (by omega), if_neg (by omega)] at heq
      rcases lt_trichotomy (rIdx w₁).val (rIdx w₂).val with hlt | hr_eq | hgt
      · have hp1_I := Finset.mem_Ico.mp (hhPos_V2 (rIdx w₁) hm1)
        have hp2_I := Finset.mem_Ico.mp (hhPos_V2 (rIdx w₂) hm2)
        have hsub_le : ((rIdx w₁).val - m) * (8 * L) + 8 * L ≤ ((rIdx w₂).val - m) * (8 * L) := by
          calc ((rIdx w₁).val - m) * (8 * L) + 8 * L =
                ((rIdx w₁).val - m + 1) * (8 * L) := (Nat.succ_mul _ _).symm
            _ ≤ ((rIdx w₂).val - m) * (8 * L) := Nat.mul_le_mul_right _ (by omega)
        have hpos_lt : hPos (rIdx w₁) < hPos (rIdx w₂) := by omega
        have hrk_lt' : rk w₁ < rk w₂ := by
          have hst := hcum_step (rIdx w₁).val (rIdx w₁).isLt
          have hd_eq : d ⟨(rIdx w₁).val, (rIdx w₁).isLt⟩ = d (rIdx w₁) := rfl
          rw [hd_eq] at hst
          have hm_mo := hcum_mono (by omega : (rIdx w₁).val + 1 ≤ (rIdx w₂).val) (le_of_lt (rIdx w₂).isLt)
          have ha : (aIdx w₁).val < d (rIdx w₁) := (aIdx w₁).isLt
          rw [Fin.lt_def, hrk_val w₁, hrk_val w₂]; omega
        have hcol_lt : colLeaf w₁ < colLeaf w₂ := eCol.strictMono hrk_lt'
        omega
      · have hr_fin : rIdx w₁ = rIdx w₂ := Fin.ext hr_eq
        rw [hr_fin] at heq
        exact hcolLeaf_inj (by omega)
      · have hp1_I := Finset.mem_Ico.mp (hhPos_V2 (rIdx w₁) hm1)
        have hp2_I := Finset.mem_Ico.mp (hhPos_V2 (rIdx w₂) hm2)
        have hsub_le : ((rIdx w₂).val - m) * (8 * L) + 8 * L ≤ ((rIdx w₁).val - m) * (8 * L) := by
          calc ((rIdx w₂).val - m) * (8 * L) + 8 * L =
                ((rIdx w₂).val - m + 1) * (8 * L) := (Nat.succ_mul _ _).symm
            _ ≤ ((rIdx w₁).val - m) * (8 * L) := Nat.mul_le_mul_right _ (by omega)
        have hpos_lt : hPos (rIdx w₂) < hPos (rIdx w₁) := by omega
        have hrk_lt' : rk w₂ < rk w₁ := by
          have hst := hcum_step (rIdx w₂).val (rIdx w₂).isLt
          have hd_eq : d ⟨(rIdx w₂).val, (rIdx w₂).isLt⟩ = d (rIdx w₂) := rfl
          rw [hd_eq] at hst
          have hm_mo := hcum_mono (by omega : (rIdx w₂).val + 1 ≤ (rIdx w₁).val) (le_of_lt (rIdx w₁).isLt)
          have ha : (aIdx w₂).val < d (rIdx w₂) := (aIdx w₂).isLt
          rw [Fin.lt_def, hrk_val w₂, hrk_val w₁]; omega
        have hcol_lt : colLeaf w₂ < colLeaf w₁ := eCol.strictMono hrk_lt'
        omega
  have hcore_leaf_ne : ∀ (x : ↥(core : Set (Fin (n + 1)))) (w : {w : Fin (n + 1) // w ∉ core}),
      S.posCore x ≠ leafPos w := by
    intro x w
    by_cases hx1 : x.val ∈ V_1
    · rcases hcore_V1_bounds x hx1 with ⟨hm1, hxeq⟩ | ⟨hm2, hxlb, hxub, hp1_ub⟩
      · by_cases hmw : (rIdx w).val < m
        · have hr0 : (rIdx w).val % 2 = 0 := by omega
          have hb := hleaf_type1_bounds w hmw hr0
          omega
        · have hb := hleaf_type3_bounds w hmw
          have hp0 := hhPos_V1_in ⟨0, by omega⟩ hm_pos
          omega
      · by_cases hmw : (rIdx w).val < m
        · by_cases hevw : (rIdx w).val % 2 = 0
          · have hb := hleaf_type1_bounds w hmw hevw; omega
          · obtain ⟨_, hb1, _⟩ := hleaf_type2_bounds w hmw hevw; omega
        · have hb := hleaf_type3_bounds w hmw; omega
    · have hxb := hcore_V02_bounds x hx1
      by_cases hmw : (rIdx w).val < m
      · by_cases hevw : (rIdx w).val % 2 = 0
        · have hb := hleaf_type1_bounds w hmw hevw
          have hp0 := hhPos_V1_in ⟨0, by omega⟩ hm_pos
          omega
        · obtain ⟨_, _, hb2⟩ := hleaf_type2_bounds w hmw hevw
          omega
      · have hb := hleaf_type3_bounds w hmw
        omega
  let gNat : Fin (n + 1) → ℕ := fun u =>
    if hu : u ∈ core then S.posCore ⟨u, hu⟩ else leafPos ⟨u, hu⟩
  have hgNat_lt : ∀ u : Fin (n + 1), gNat u < 2 * n + 1 := by
    intro u
    dsimp only [gNat]
    split_ifs with hu
    · by_cases hx1 : u ∈ V_1
      · rcases hcore_V1_bounds ⟨u, hu⟩ hx1 with ⟨_, hxeq⟩ | ⟨_, _, hxub, hp1_ub⟩
        · have hp0 := hhPos_V1_in ⟨0, by omega⟩ hm_pos; omega
        · omega
      · have hb := hcore_V02_bounds ⟨u, hu⟩ hx1; omega
    · by_cases hmw : (rIdx ⟨u, hu⟩).val < m
      · by_cases hevw : (rIdx ⟨u, hu⟩).val % 2 = 0
        · have hb := hleaf_type1_bounds ⟨u, hu⟩ hmw hevw
          have hp0 := hhPos_V1_in ⟨0, by omega⟩ hm_pos; omega
        · obtain ⟨_, _, hb2⟩ := hleaf_type2_bounds ⟨u, hu⟩ hmw hevw; omega
      · have hb := hleaf_type3_bounds ⟨u, hu⟩ hmw; omega
  have hgNat_inj : Function.Injective gNat := by
    intro u₁ u₂ heq
    dsimp only [gNat] at heq
    by_cases h1 : u₁ ∈ core <;> by_cases h2 : u₂ ∈ core
    · rw [dif_pos h1, dif_pos h2] at heq
      exact congrArg Subtype.val (S.posCore_inj heq)
    · rw [dif_pos h1, dif_neg h2] at heq
      exact absurd heq (hcore_leaf_ne ⟨u₁, h1⟩ ⟨u₂, h2⟩)
    · rw [dif_neg h1, dif_pos h2] at heq
      exact absurd heq.symm (hcore_leaf_ne ⟨u₂, h2⟩ ⟨u₁, h1⟩)
    · rw [dif_neg h1, dif_neg h2] at heq
      exact congrArg Subtype.val (hleafPos_inj heq)
  let g : Fin (n + 1) ↪ Fin (2 * n + 1) :=
    ⟨fun u => ⟨gNat u, hgNat_lt u⟩, fun u₁ u₂ h => hgNat_inj (congrArg Fin.val h)⟩
  set mCore := Fintype.card ↥(core : Set (Fin (n + 1))) with hmCore_def
  have hcore_pos_all : ∀ x : ↥(core : Set (Fin (n + 1))), S.posCore x < 99 * q0 := by
    intro x
    by_cases hx1 : x.val ∈ V_1
    · rcases hcore_V1_bounds x hx1 with ⟨_, hxeq⟩ | ⟨_, _, hxub, hp1_ub⟩
      · have hp0 := hhPos_V1_in ⟨0, by omega⟩ hm_pos; omega
      · omega
    · exact (hcore_V02_bounds x hx1).2
  have hecCore_nd : ∀ t : Fin (mCore - 1),
      ndColor (g (S.R.ord (S.R.par ⟨t.val + 1, by omega⟩ (by simp))).val)
              (g (S.R.ord ⟨t.val + 1, by omega⟩).val) =
      distNat (S.posCore (S.R.ord (S.R.par ⟨t.val + 1, by omega⟩ (by simp))))
              (S.posCore (S.R.ord ⟨t.val + 1, by omega⟩)) := by
    intro t
    let aX := S.R.ord (S.R.par ⟨t.val + 1, by omega⟩ (by simp))
    let bX := S.R.ord ⟨t.val + 1, by omega⟩
    have ha_c : aX.val ∈ core := aX.property
    have hb_c : bX.val ∈ core := bX.property
    have ha_g : gNat aX.val = S.posCore aX := by dsimp [gNat]; rw [dif_pos ha_c]
    have hb_g : gNat bX.val = S.posCore bX := by dsimp [gNat]; rw [dif_pos hb_c]
    have hne : S.posCore aX ≠ S.posCore bX := by
      intro heq
      have hord := S.R.ord.injective (S.posCore_inj heq)
      have hlt := S.R.par_lt ⟨t.val + 1, by omega⟩ (by simp)
      rw [hord] at hlt
      omega
    have ha_ub := hcore_pos_all aX
    have hb_ub := hcore_pos_all bX
    have hdist_le : distNat (S.posCore aX) (S.posCore bX) ≤ n := by
      dsimp [distNat]; omega
    change ndColor ⟨gNat aX.val, _⟩ ⟨gNat bX.val, _⟩ = distNat (S.posCore aX) (S.posCore bX)
    have := ndColor_eq_distNat (n := n) (hgNat_lt aX.val) (hgNat_lt bX.val)
      (by rw [ha_g, hb_g]; exact hne) (by rw [ha_g, hb_g]; exact hdist_le)
    rw [this, ha_g, hb_g]
  have hecLeaf_nd : ∀ w : {w : Fin (n + 1) // w ∉ core},
      ndColor (g (hubOf w.val w.property)) (g w.val) = colLeaf w := by
    intro w
    have hhub_c : hubOf w.val w.property ∈ core := hHubs_sub (hhub_Hubs w.val w.property)
    have hhub_g : gNat (hubOf w.val w.property) = hPos (rIdx w) := by
      dsimp only [gNat, hPos]
      rw [dif_pos hhub_c]
      congr 1
      exact Subtype.ext (hrIdx_val w).symm
    have hw_g : gNat w.val = leafPos w := by
      dsimp only [gNat]
      rw [dif_neg w.property]
    have hob := hcolLeaf_bounds w
    have hc_pos : 1 ≤ colLeaf w := by omega
    have hc_le_n : colLeaf w ≤ n := hob.2.1
    have hdist_eq : distNat (hPos (rIdx w)) (leafPos w) = colLeaf w := by
      dsimp only [leafPos]
      split_ifs with htype1
      · have hpb := hhPos_V1_in (rIdx w) htype1.1
        have hcub := hcol_V1_ub w htype1.1
        dsimp [distNat]
        rcases hcub with ⟨_, hb⟩ | ⟨_, hb⟩ <;> omega
      · dsimp [distNat]; omega
    have hne : hPos (rIdx w) ≠ leafPos w := by
      intro heq
      rw [heq] at hdist_eq
      dsimp [distNat] at hdist_eq
      omega
    change ndColor ⟨gNat (hubOf w.val w.property), _⟩ ⟨gNat w.val, _⟩ = colLeaf w
    have := ndColor_eq_distNat (n := n) (hgNat_lt (hubOf w.val w.property)) (hgNat_lt w.val)
      (by rw [hhub_g, hw_g]; exact hne) (by rw [hhub_g, hw_g, hdist_eq]; exact hc_le_n)
    rw [this, hhub_g, hw_g, hdist_eq]
  refine ⟨g, rainbow_of_core_and_leaves T hT core r₀ S.R hubOf
    (fun w hw => hHubs_sub (hhub_Hubs w hw)) hrem_deg hhub_adj g S.C_core ?_ ?_ ?_ ?_⟩
  · intro t
    rw [hecCore_nd t]
    exact S.ecCore_mem t
  · intro t₁ t₂ heq
    dsimp only at heq
    rw [hecCore_nd t₁, hecCore_nd t₂] at heq
    exact S.ecCore_inj heq
  · intro w
    rw [hecLeaf_nd w]
    exact (hcolLeaf_bounds w).2.2.2
  · intro w₁ w₂ heq
    dsimp only at heq
    rw [hecLeaf_nd w₁, hecLeaf_nd w₂] at heq
    exact hcolLeaf_inj heq

private lemma subcase_bounded_hubs {n : ℕ} (hn : 2 ^ 196 ≤ n)
    (T : SimpleGraph (Fin (n + 1))) [DecidableRel T.Adj] (hT : T.IsTree)
    (hcore_le : (Finset.univ.filter (fun w : Fin (n + 1) =>
      ¬ (T.degree w = 1 ∧ ∃ v, T.Adj v w ∧
        (2 ^ Nat.sqrt (Nat.log 2 n)) ^ 4 ≤ (leafNbrs T v).card))).card ≤ n / 100)
    (hmax_deg : ∀ v : Fin (n + 1), (leafNbrs T v).card < 75 * (n / 100)) :
    ∃ g : Fin (n + 1) ↪ Fin (2 * n + 1),
      ∀ u₁ v₁ u₂ v₂, T.Adj u₁ v₁ → T.Adj u₂ v₂ →
        (g u₁ - g v₁ = g u₂ - g v₂ ∨ g u₁ - g v₁ = g v₂ - g u₂) →
        s(u₁, v₁) = s(u₂, v₂) := by
  classical
  obtain ⟨hr, hL, hq0, hn_lt_L⟩ := large_n_params hn
  set r := Nat.sqrt (Nat.log 2 n) with hr_def
  set L := 2 ^ r with hL_def
  set q0 := n / 100 with hq0_def
  have hn_q0 : 100 * q0 ≤ n := Nat.mul_div_le n 100
  let core := Finset.univ.filter (fun w : Fin (n + 1) =>
    ¬ (T.degree w = 1 ∧ ∃ v, T.Adj v w ∧ L ^ 4 ≤ (leafNbrs T v).card))
  have hcore_le' : core.card ≤ q0 := hcore_le
  let Hubs := Finset.univ.filter (fun v : Fin (n + 1) => L ^ 4 ≤ (leafNbrs T v).card)
  have hHubs_sub : Hubs ⊆ core := by
    intro v hv
    have hge : L ^ 4 ≤ (leafNbrs T v).card := (Finset.mem_filter.mp hv).2
    have hsub_nb : leafNbrs T v ⊆ T.neighborFinset v := by
      intro u hu
      exact (T.mem_neighborFinset v u).mpr (Finset.mem_filter.mp hu).2.1
    have hdeg_ge : L ^ 4 ≤ T.degree v := by
      rw [← T.card_neighborFinset_eq_degree]
      exact hge.trans (Finset.card_le_card hsub_nb)
    have hL4_ge2 : 2 ≤ L ^ 4 := by
      calc 2 ≤ 16384 ^ 4 := by norm_num
        _ ≤ L ^ 4 := Nat.pow_le_pow_left hL 4
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rintro ⟨hd1, _⟩
    omega
  have hrem_spec : ∀ w : Fin (n + 1), w ∉ core ↔ ∃ v ∈ Hubs, w ∈ leafNbrs T v := by
    intro w
    constructor
    · intro hnot
      have hP : T.degree w = 1 ∧ ∃ v, T.Adj v w ∧ L ^ 4 ≤ (leafNbrs T v).card := by
        by_contra hneg
        exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ w, hneg⟩)
      rcases hP with ⟨hd1, v, hvw, hge⟩
      exact ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ v, hge⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ w, hvw, hd1⟩⟩
    · rintro ⟨v, hvH, hwL⟩ hmem
      have hge : L ^ 4 ≤ (leafNbrs T v).card := (Finset.mem_filter.mp hvH).2
      obtain ⟨_, hvw, hd1⟩ := Finset.mem_filter.mp hwL
      exact (Finset.mem_filter.mp hmem).2 ⟨hd1, v, hvw, hge⟩
  have hcore_pos : 0 < core.card := by
    by_cases h0 : (0 : Fin (n + 1)) ∈ core
    · exact Finset.card_pos.mpr ⟨0, h0⟩
    · obtain ⟨v, hvH, _⟩ := (hrem_spec 0).mp h0
      exact Finset.card_pos.mpr ⟨v, hHubs_sub hvH⟩
  have hrem_deg : ∀ w : Fin (n + 1), w ∉ core → T.degree w = 1 := by
    intro w hw
    obtain ⟨v, _, hwv⟩ := (hrem_spec w).mp hw
    exact (Finset.mem_filter.mp hwv).2.2
  have hHubs_disj : Set.PairwiseDisjoint (Hubs : Set (Fin (n + 1))) (leafNbrs T) := by
    intro v₁ _ v₂ _ hne
    change Disjoint (leafNbrs T v₁) (leafNbrs T v₂)
    rw [Finset.disjoint_left]
    intro w hw1 hw2
    obtain ⟨_, hadj1, hd1⟩ := Finset.mem_filter.mp hw1
    obtain ⟨_, hadj2, _⟩ := Finset.mem_filter.mp hw2
    obtain ⟨u, _, hu⟩ := degree_eq_one_iff_existsUnique_adj.mp hd1
    exact hne ((hu v₁ hadj1.symm).trans (hu v₂ hadj2.symm).symm)
  have hcompl_eq : Finset.univ \ core = Hubs.biUnion (leafNbrs T) := by
    ext w
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_biUnion]
    exact hrem_spec w
  have hsum_Hubs : ∑ v ∈ Hubs, (leafNbrs T v).card = n + 1 - core.card := by
    have h1 : (Hubs.biUnion (leafNbrs T)).card = ∑ v ∈ Hubs, (leafNbrs T v).card :=
      Finset.card_biUnion hHubs_disj
    have h2 := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ core)
    rw [hcompl_eq, h1] at h2
    simp only [Finset.card_univ, Fintype.card_fin] at h2
    omega
  have hHubs_mul : Hubs.card * L ^ 4 ≤ n := by
    have hle : Hubs.card * L ^ 4 ≤ ∑ v ∈ Hubs, (leafNbrs T v).card := by
      calc Hubs.card * L ^ 4 = ∑ _v ∈ Hubs, L ^ 4 := by simp
        _ ≤ ∑ v ∈ Hubs, (leafNbrs T v).card :=
          Finset.sum_le_sum fun v hv => (Finset.mem_filter.mp hv).2
    omega
  have hHubs_width : Hubs.card * (8 * L) ≤ q0 := by
    have h800 : 800 * L ≤ L ^ 4 := by
      have hL3 : 800 ≤ L ^ 3 := by
        calc 800 ≤ 16384 ^ 3 := by norm_num
          _ ≤ L ^ 3 := Nat.pow_le_pow_left hL 3
      calc 800 * L ≤ L ^ 3 * L := Nat.mul_le_mul_right L hL3
        _ = L ^ 4 := by ring
    have h100 : 100 * (Hubs.card * (8 * L)) ≤ n := by
      calc 100 * (Hubs.card * (8 * L)) = Hubs.card * (800 * L) := by ring
        _ ≤ Hubs.card * L ^ 4 := Nat.mul_le_mul_left _ h800
        _ ≤ n := hHubs_mul
    omega
  have hV1_split : ∃ V_1 : Finset (Fin (n + 1)),
      V_1 ⊆ Hubs ∧
      1 ≤ V_1.card ∧
      5 * q0 < ∑ v ∈ V_1, (leafNbrs T v).card ∧
      ((V_1.card = 1 ∧ ∑ v ∈ V_1, (leafNbrs T v).card < 75 * q0) ∨
       (2 ≤ V_1.card ∧ ∑ v ∈ V_1, (leafNbrs T v).card ≤ 10 * q0)) := by
    by_cases hbig5 : ∃ v ∈ Hubs, 5 * q0 < (leafNbrs T v).card
    · obtain ⟨v₀, hv₀H, hv₀gt⟩ := hbig5
      refine ⟨{v₀}, Finset.singleton_subset_iff.mpr hv₀H, by simp, by simpa using hv₀gt,
        Or.inl ⟨by simp, by simpa using hmax_deg v₀⟩⟩
    · push Not at hbig5
      set ℓ := Hubs.card with hℓ_def
      let eH : Fin ℓ ≃ ↥Hubs :=
        (Fintype.equivFinOfCardEq (Fintype.card_coe Hubs)).symm
      let ps : ℕ → ℕ := fun k =>
        ∑ i ∈ Finset.univ.filter (fun i : Fin ℓ => i.val < k), (leafNbrs T (eH i).val).card
      have hps_step : ∀ (k : ℕ) (hk : k < ℓ),
          ps (k + 1) = ps k + (leafNbrs T (eH ⟨k, hk⟩).val).card := by
        intro k hk
        dsimp only [ps]
        have hflt : Finset.univ.filter (fun i : Fin ℓ => i.val < k + 1) =
            insert ⟨k, hk⟩ (Finset.univ.filter (fun i : Fin ℓ => i.val < k)) := by
          ext i
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
          constructor
          · intro h; by_cases hik : i.val = k
            · exact Or.inl (Fin.ext hik)
            · exact Or.inr (by omega)
          · rintro (rfl | h)
            · simp
            · omega
        rw [hflt, Finset.sum_insert]
        · ring
        · simp
      have hps_all : ps ℓ = ∑ v ∈ Hubs, (leafNbrs T v).card := by
        dsimp only [ps]
        have hflt : Finset.univ.filter (fun i : Fin ℓ => i.val < ℓ) = Finset.univ := by
          ext i; simp
        rw [hflt, ← Finset.sum_coe_sort Hubs]
        exact Fintype.sum_equiv eH _ _ (fun _ => rfl)
      have hex_k : ∃ k : ℕ, k ≤ ℓ ∧ 5 * q0 < ps k := ⟨ℓ, le_refl ℓ, by omega⟩
      let m := Nat.find hex_k
      have hm_spec : m ≤ ℓ ∧ 5 * q0 < ps m := Nat.find_spec hex_k
      have hm_le : m ≤ ℓ := hm_spec.1
      have hm_gt : 5 * q0 < ps m := hm_spec.2
      have hm_ne0 : m ≠ 0 := by
        intro hm0
        have hp0 : ps 0 = 0 := by simp [ps]
        rw [hm0, hp0] at hm_gt
        omega
      have hm_ne1 : m ≠ 1 := by
        intro hm1
        have h0_lt : 0 < ℓ := by omega
        have hp1 : ps 1 = (leafNbrs T (eH ⟨0, h0_lt⟩).val).card := by
          rw [hps_step 0 h0_lt]; simp [ps]
        have hle5 := hbig5 (eH ⟨0, h0_lt⟩).val (eH ⟨0, h0_lt⟩).property
        rw [hm1, hp1] at hm_gt
        omega
      have hprev_le : ps (m - 1) ≤ 5 * q0 := by
        by_contra hgt
        exact Nat.find_min hex_k (by omega : m - 1 < m) ⟨by omega, not_le.mp hgt⟩
      have hm_le10 : ps m ≤ 10 * q0 := by
        have hstep_m := hps_step (m - 1) (by omega)
        have h1 : m - 1 + 1 = m := by omega
        rw [h1] at hstep_m
        have hle5 := hbig5 (eH ⟨m - 1, by omega⟩).val (eH ⟨m - 1, by omega⟩).property
        omega
      let IdxM := Finset.univ.filter (fun i : Fin ℓ => i.val < m)
      let V_1 := IdxM.image (fun i => (eH i).val)
      have hinj_eH : Set.InjOn (fun i : Fin ℓ => (eH i).val) (IdxM : Set (Fin ℓ)) := by
        intro a _ b _ h
        exact eH.injective (Subtype.ext h)
      have hV1_card : V_1.card = m := by
        rw [Finset.card_image_of_injOn hinj_eH]
        have hbij : IdxM.card = (Finset.range m).card := by
          refine Finset.card_bij (fun i _ => i.val) ?_ ?_ ?_
          · intro i hi; exact Finset.mem_range.mpr (Finset.mem_filter.mp hi).2
          · intro a _ b _ h; exact Fin.ext h
          · intro j hj
            have hjlt : j < m := Finset.mem_range.mp hj
            exact ⟨⟨j, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjlt⟩, rfl⟩
        rw [hbij, Finset.card_range]
      have hV1_sum : ∑ v ∈ V_1, (leafNbrs T v).card = ps m := by
        dsimp only [V_1, ps]
        exact Finset.sum_image hinj_eH
      have hV1_sub_H : V_1 ⊆ Hubs := by
        intro v hv
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
        exact (eH i).property
      exact ⟨V_1, hV1_sub_H, by omega, by omega, Or.inr ⟨by omega, by omega⟩⟩
  obtain ⟨V_1, hV1_Hubs, hm_pos, hV1_gt5, hV1_cases⟩ := hV1_split
  have hV1_sub : V_1 ⊆ core := hV1_Hubs.trans hHubs_sub
  have hV2_sub : Hubs \ V_1 ⊆ core := Finset.sdiff_subset.trans hHubs_sub
  have hpart : ∀ x ∈ core, (x ∈ core \ Hubs ∧ x ∉ V_1 ∧ x ∉ Hubs \ V_1) ∨
                           (x ∉ core \ Hubs ∧ x ∈ V_1 ∧ x ∉ Hubs \ V_1) ∨
                           (x ∉ core \ Hubs ∧ x ∉ V_1 ∧ x ∈ Hubs \ V_1) := by
    intro x hx
    by_cases hxH : x ∈ Hubs
    · by_cases hx1 : x ∈ V_1
      · exact Or.inr (Or.inl ⟨fun h => (Finset.mem_sdiff.mp h).2 hxH, hx1,
          fun h => (Finset.mem_sdiff.mp h).2 hx1⟩)
      · exact Or.inr (Or.inr ⟨fun h => (Finset.mem_sdiff.mp h).2 hxH, hx1,
          Finset.mem_sdiff.mpr ⟨hxH, hx1⟩⟩)
    · exact Or.inl ⟨Finset.mem_sdiff.mpr ⟨hx, hxH⟩, fun h => hxH (hV1_Hubs h),
        fun h => hxH (Finset.mem_sdiff.mp h).1⟩
  have hT'_tree : (T.induce (core : Set (Fin (n + 1)))).IsTree :=
    induce_compl_leaves_isTree T hT core hcore_pos hrem_deg
  obtain ⟨w₀, hw₀⟩ := Finset.card_pos.mp hcore_pos
  let r₀ : ↥(core : Set (Fin (n + 1))) := ⟨w₀, hw₀⟩
  have hV1_width : V_1.card * (8 * L) ≤ q0 :=
    (Nat.mul_le_mul_right _ (Finset.card_le_card hV1_Hubs)).trans hHubs_width
  have hV2_width : (Hubs \ V_1).card * (8 * L) ≤ q0 :=
    (Nat.mul_le_mul_right _ (Finset.card_le_card Finset.sdiff_subset)).trans hHubs_width
  have hV1_pow : V_1.card < 2 ^ (L - 2) := by
    have hle := (Finset.card_le_card hV1_sub).trans hcore_le'
    omega
  have hV2_pow : (Hubs \ V_1).card < 2 ^ (L - 2) := by
    have hle := (Finset.card_le_card hV2_sub).trans hcore_le'
    omega
  obtain ⟨S⟩ := exists_small_tree_embed hL hq0 T core (core \ Hubs) V_1 (Hubs \ V_1)
    hcore_le' hV1_sub hV2_sub hpart hV1_width hV2_width hV1_pow hV2_pow r₀
    (buildRootedOrder (T.induce (core : Set (Fin (n + 1)))) hT'_tree r₀)
  exact attach_hub_leaves hL hq0 T hT core Hubs V_1 hcore_le' hHubs_sub hV1_Hubs
    hpart hrem_spec hrem_deg (fun v hv => (Finset.mem_filter.mp hv).2) hsum_Hubs
    hV1_width hV2_width hm_pos hV1_gt5 hV1_cases r₀ S

end KotzigCaseCEmbedding

-- ============================================================================
-- Section 6: Final Solution Entrypoint
-- ============================================================================

theorem OMA.solution : OMA.R_Arxiv_2001_02665_kotzig_conjecture_large_R1.H3 := by
  filter_upwards [Filter.eventually_ge_atTop (2 ^ 196)] with n hn
  intro T _ hT hcore_le
  by_cases hbig : ∃ v : Fin (n + 1),
      75 * (n / 100) ≤ (KotzigCaseCEmbedding.leafNbrs T v).card
  · obtain ⟨v₁, hv₁⟩ := hbig
    have hn10000 : 10000 ≤ n := by
      have hpow : 10000 ≤ 2 ^ 196 := by norm_num
      omega
    exact KotzigCaseCEmbedding.subcase_large_hub hn10000 T hT v₁ hv₁
  · push Not at hbig
    exact KotzigCaseCEmbedding.subcase_bounded_hubs hn T hT hcore_le hbig
