import OMAReductions.R_Erdos743_erdos_743_variants_largest_trees_R1
import Mathlib

/-!
# Proof of `Erdos743.erdos_743.variants.largest_trees.R1.H2`

Formalizes the single-tree embedding lemma (Janzer–Montgomery `arXiv:2403.10515`
Section 5, Lemma 5.1) for `OMA.R_Erdos743_erdos_743_variants_largest_trees_R1.H2`.
-/

open Filter SimpleGraph Finset
open scoped Classical

namespace Erdos743H2

/- ## Section 1: Tree decomposition and degree bounds -/

lemma tree_sum_degree_le {k : ℕ} {T : SimpleGraph (Fin k)} (hT : T.IsTree)
    {a b : Fin k} (hab : a ≠ b) :
    T.degree a + T.degree b ≤ k := by
  let Ea : Finset (Sym2 (Fin k)) := (T.neighborFinset a).image (fun z => s(a, z))
  let Eb : Finset (Sym2 (Fin k)) := (T.neighborFinset b).image (fun w => s(b, w))
  have hEa_sub : Ea ⊆ T.edgeFinset := by
    intro e he
    rcases mem_image.mp he with ⟨z, hz, rfl⟩
    exact mem_edgeFinset.mpr ((mem_neighborFinset T a z).mp hz)
  have hEb_sub : Eb ⊆ T.edgeFinset := by
    intro e he
    rcases mem_image.mp he with ⟨w, hw, rfl⟩
    exact mem_edgeFinset.mpr ((mem_neighborFinset T b w).mp hw)
  have hEa_card : Ea.card = T.degree a := by
    rw [← card_neighborFinset_eq_degree]
    refine card_image_of_injOn (fun z₁ hz₁ z₂ _ h => ?_)
    have hne : z₁ ≠ a := ((mem_neighborFinset T a z₁).mp hz₁).ne.symm
    rcases Sym2.eq_iff.mp h with ⟨_, h2⟩ | ⟨_, h2⟩
    · exact h2
    · exact absurd h2 hne
  have hEb_card : Eb.card = T.degree b := by
    rw [← card_neighborFinset_eq_degree]
    refine card_image_of_injOn (fun w₁ hw₁ w₂ _ h => ?_)
    have hne : w₁ ≠ b := ((mem_neighborFinset T b w₁).mp hw₁).ne.symm
    rcases Sym2.eq_iff.mp h with ⟨_, h2⟩ | ⟨_, h2⟩
    · exact h2
    · exact absurd h2 hne
  have h_inter : Ea ∩ Eb ⊆ {s(a, b)} := by
    intro e he
    rcases mem_inter.mp he with ⟨he1, he2⟩
    rcases mem_image.mp he1 with ⟨z, _, rfl⟩
    rcases mem_image.mp he2 with ⟨w, _, hw⟩
    rw [mem_singleton]
    rcases Sym2.eq_iff.mp hw with ⟨h1, _⟩ | ⟨h1, h2⟩
    · exact absurd h1 hab.symm
    · rw [h1, ← h2]
  have h_edge : T.edgeFinset.card + 1 = k := by
    simpa using hT.card_edgeFinset
  have h_union : (Ea ∪ Eb).card ≤ T.edgeFinset.card :=
    card_le_card (union_subset hEa_sub hEb_sub)
  have h_inter_card : (Ea ∩ Eb).card ≤ 1 :=
    (card_le_card h_inter).trans (by simp)
  have h_add := card_union_add_card_inter Ea Eb
  omega

lemma tree_two_mul_degree_le_add_leafDeg {k : ℕ} {T : SimpleGraph (Fin k)} (hT : T.IsTree)
    (x : Fin k) :
    2 * T.degree x ≤ k - 1 + ((Finset.univ.filter (fun v => T.degree v = 1)).filter (T.Adj x)).card := by
  let Leaves : Finset (Fin k) := Finset.univ.filter (fun v => T.degree v = 1)
  let leafNbrs : Finset (Fin k) := Leaves.filter (T.Adj x)
  let nonLeafNbrs : Finset (Fin k) := (T.neighborFinset x).filter (fun y => T.degree y ≠ 1)
  have h_split : T.degree x = leafNbrs.card + nonLeafNbrs.card := by
    rw [← card_neighborFinset_eq_degree]
    have h_eq : leafNbrs = (T.neighborFinset x).filter (fun y => T.degree y = 1) := by
      ext y
      simp [leafNbrs, Leaves, mem_neighborFinset, and_comm]
    rw [h_eq]
    exact (Finset.card_filter_add_card_filter_not (s := T.neighborFinset x)
      (p := fun y => T.degree y = 1)).symm
  have h_nonleaf_ge2 : ∀ y ∈ nonLeafNbrs, ∃ z : Fin k, z ≠ x ∧ T.Adj y z := by
    intro y hy
    rcases mem_filter.mp hy with ⟨hy_nbr, hy_ne1⟩
    have hadj_xy : T.Adj x y := (mem_neighborFinset T x y).mp hy_nbr
    have hdeg_pos : 0 < T.degree y := by
      rw [← card_neighborFinset_eq_degree]
      exact Finset.card_pos.mpr ⟨x, (mem_neighborFinset T y x).mpr hadj_xy.symm⟩
    have hdeg_ge2 : 2 ≤ T.degree y := by omega
    have h_erase : ((T.neighborFinset y).erase x).Nonempty := by
      rw [← Finset.card_pos]
      have hcard := card_erase_of_mem ((mem_neighborFinset T y x).mpr hadj_xy.symm)
      rw [card_neighborFinset_eq_degree] at hcard
      omega
    rcases h_erase with ⟨z, hz⟩
    exact ⟨z, (mem_erase.mp hz).1, (mem_neighborFinset T y z).mp (mem_erase.mp hz).2⟩
  choose z hz_ne hz_adj using h_nonleaf_ge2
  let Ex : Finset (Sym2 (Fin k)) := (T.neighborFinset x).image (fun w => s(x, w))
  let E_nl : Finset (Sym2 (Fin k)) := nonLeafNbrs.attach.image (fun y => s(y.1, z y.1 y.2))
  have hEx_sub : Ex ⊆ T.edgeFinset := by
    intro e he
    rcases mem_image.mp he with ⟨w, hw, rfl⟩
    exact mem_edgeFinset.mpr ((mem_neighborFinset T x w).mp hw)
  have hEx_card : Ex.card = T.degree x := by
    rw [← card_neighborFinset_eq_degree]
    refine card_image_of_injOn (fun w₁ hw₁ w₂ _ h => ?_)
    have hne : w₁ ≠ x := ((mem_neighborFinset T x w₁).mp hw₁).ne.symm
    rcases Sym2.eq_iff.mp h with ⟨_, h2⟩ | ⟨_, h2⟩
    · exact h2
    · exact absurd h2 hne
  have hEnl_sub : E_nl ⊆ T.edgeFinset \ Ex := by
    intro e he
    rcases mem_image.mp he with ⟨⟨y, hy⟩, _, rfl⟩
    refine mem_sdiff.mpr ⟨mem_edgeFinset.mpr (hz_adj y hy), ?_⟩
    intro hEx
    rcases mem_image.mp hEx with ⟨w, _, h_eq⟩
    have hadj_xy : T.Adj x y := (mem_neighborFinset T x y).mp (mem_filter.mp hy).1
    rcases Sym2.eq_iff.mp h_eq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact hadj_xy.ne h1
    · exact (hz_ne y hy) h1.symm
  have hEnl_card : E_nl.card = nonLeafNbrs.card := by
    rw [← Finset.card_attach (s := nonLeafNbrs)]
    refine card_image_of_injOn (fun ⟨y₁, hy₁⟩ _ ⟨y₂, hy₂⟩ _ h_eq => ?_)
    by_contra hne
    have hy12 : y₁ ≠ y₂ := fun h => hne (Subtype.ext h)
    have hadj_xy1 : T.Adj x y₁ := (mem_neighborFinset T x y₁).mp (mem_filter.mp hy₁).1
    have hadj_xy2 : T.Adj x y₂ := (mem_neighborFinset T x y₂).mp (mem_filter.mp hy₂).1
    have hadj_12 : T.Adj y₁ y₂ := by
      rcases Sym2.eq_iff.mp h_eq with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact absurd h1 hy12
      · have h1' : y₁ = z y₂ hy₂ := h1
        rw [h1']
        exact (hz_adj y₂ hy₂).symm
    let p1 : T.Walk y₁ y₂ := Walk.cons hadj_12 .nil
    let p2 : T.Walk y₁ y₂ := Walk.cons hadj_xy1.symm (Walk.cons hadj_xy2 .nil)
    have hp1 : p1.IsPath := by simp [p1, hadj_12.ne]
    have hp2 : p2.IsPath := by simp [p2, hadj_xy1.ne.symm, hadj_xy2.ne, hy12]
    have h_eq_p := hT.isAcyclic.subsingleton_path y₁ y₂ |>.elim ⟨p1, hp1⟩ ⟨p2, hp2⟩
    have h_len := congrArg (fun p : T.Path y₁ y₂ => p.1.length) h_eq_p
    simp [p1, p2] at h_len
  have h_edge : T.edgeFinset.card + 1 = k := by
    simpa using hT.card_edgeFinset
  have h_le : E_nl.card + Ex.card ≤ k - 1 := by
    have h1 := card_le_card hEnl_sub
    rw [card_sdiff_of_subset hEx_sub] at h1
    have h_ex_le : Ex.card ≤ T.edgeFinset.card := card_le_card hEx_sub
    omega
  have h_ex_split : Ex.card = leafNbrs.card + E_nl.card := by
    rw [hEx_card, hEnl_card, h_split]
  dsimp only [leafNbrs, Leaves] at h_ex_split
  rw [← hEx_card]
  omega

lemma tree_deg_le_of_ne_maxLeafDeg {k : ℕ} {T : SimpleGraph (Fin k)} (hT : T.IsTree)
    (t₁ : Fin k)
    (ht₁ : ∀ x : Fin k, ((Finset.univ.filter (fun v => T.degree v = 1)).filter (T.Adj x)).card ≤
      ((Finset.univ.filter (fun v => T.degree v = 1)).filter (T.Adj t₁)).card)
    {x : Fin k} (hx : x ≠ t₁) :
    3 * T.degree x ≤ 2 * k - 1 := by
  have h1 := tree_two_mul_degree_le_add_leafDeg hT x
  have h2 := ht₁ x
  have h3 : ((Finset.univ.filter (fun v => T.degree v = 1)).filter (T.Adj t₁)).card ≤ T.degree t₁ := by
    rw [← card_neighborFinset_eq_degree]
    refine card_le_card (fun v hv => ?_)
    exact (mem_neighborFinset T t₁ v).mpr (mem_filter.mp hv).2
  have h4 := tree_sum_degree_le hT hx.symm
  omega

/-- Ordering of `L_setᶜ` rooted at `t₁` where each vertex after index `0` has a unique earlier neighbor. -/
lemma tree_ordering_after_removing_leaves {k : ℕ} {T : SimpleGraph (Fin k)} (hT : T.IsTree)
    (t₁ : Fin k) (L_set : Finset (Fin k))
    (hL_sub : ∀ ℓ ∈ L_set, T.degree ℓ = 1) (ht₁ : t₁ ∉ L_set) :
    ∃ (m : ℕ) (_hm : m = k - L_set.card) (hm_pos : 0 < m)
      (t_seq : Fin m ↪ Fin k)
      (par : ∀ i : Fin m, 0 < i.1 → Fin m),
      (Set.range t_seq = ((L_setᶜ : Finset (Fin k)) : Set (Fin k))) ∧
      t_seq ⟨0, hm_pos⟩ = t₁ ∧
      (∀ i (hi : 0 < i.1), (par i hi).1 < i.1 ∧ T.Adj (t_seq (par i hi)) (t_seq i)) ∧
      (∀ i (hi : 0 < i.1) (j : Fin m), j.1 < i.1 → T.Adj (t_seq j) (t_seq i) → j = par i hi) := by
  classical
  let V' : Finset (Fin k) := L_setᶜ
  have ht₁_mem : t₁ ∈ V' := mem_compl.mpr ht₁
  have hcard : V'.card = k - L_set.card := by
    rw [card_compl, Fintype.card_fin]
  have hm_pos : 0 < k - L_set.card := by
    rw [← hcard]
    exact Finset.card_pos.mpr ⟨t₁, ht₁_mem⟩
  let pathTo : ∀ v : Fin k, {p : T.Walk t₁ v // p.IsPath} := fun v =>
    ⟨(hT.existsUnique_path t₁ v).choose, (hT.existsUnique_path t₁ v).choose_spec.1⟩
  let dist : Fin k → ℕ := fun v => (pathTo v).1.length
  let key : Fin k ↪ ℕ ×ₗ Fin k :=
    ⟨fun v => toLex (dist v, v), fun a b h => by
      have h' : (dist a, a) = (dist b, b) := ofLex_inj.mp h
      exact (Prod.ext_iff.mp h').2⟩
  let K' : Finset (ℕ ×ₗ Fin k) := V'.image key
  have hK'_card : K'.card = k - L_set.card := by
    rw [card_image_of_injective _ key.injective, hcard]
  let iso : Fin (k - L_set.card) ≃o K' := K'.orderIsoOfFin hK'_card
  let t_seq : Fin (k - L_set.card) ↪ Fin k :=
    ⟨fun i => (ofLex (iso i).1).2, fun i j h => by
      dsimp only at h
      have hmem_i := (iso i).2
      have hmem_j := (iso j).2
      rcases mem_image.mp hmem_i with ⟨vi, _, hvi⟩
      rcases mem_image.mp hmem_j with ⟨vj, _, hvj⟩
      have hi_eq : (ofLex (iso i).1).2 = vi := by rw [← hvi]; rfl
      have hj_eq : (ofLex (iso j).1).2 = vj := by rw [← hvj]; rfl
      have hv_eq : vi = vj := by rw [← hi_eq, ← hj_eq, h]
      apply iso.injective
      exact Subtype.ext (by rw [← hvi, ← hvj, hv_eq])⟩
  have h_key_t : ∀ i : Fin (k - L_set.card), key (t_seq i) = (iso i).1 := by
    intro i
    rcases mem_image.mp (iso i).2 with ⟨v, _, hv⟩
    have hv_eq : t_seq i = v := by change (ofLex (iso i).1).2 = v; rw [← hv]; rfl
    rw [hv_eq, hv]
  have h_mem_V' : ∀ i : Fin (k - L_set.card), t_seq i ∈ V' := by
    intro i
    rcases mem_image.mp (iso i).2 with ⟨v, hv_mem, hv⟩
    have hv_eq : t_seq i = v := by change (ofLex (iso i).1).2 = v; rw [← hv]; rfl
    rwa [hv_eq]
  have h_range : Set.range t_seq = (V' : Set (Fin k)) := by
    ext v
    constructor
    · rintro ⟨i, rfl⟩
      exact h_mem_V' i
    · intro hv
      have hk_mem : key v ∈ K' := mem_image_of_mem key hv
      refine ⟨iso.symm ⟨key v, hk_mem⟩, ?_⟩
      change (ofLex (iso (iso.symm ⟨key v, hk_mem⟩)).1).2 = v
      rw [OrderIso.apply_symm_apply]
      rfl
  have h_dist_zero : dist t₁ = 0 := by
    have hnil : (pathTo t₁).1 = Walk.nil :=
      (hT.existsUnique_path t₁ t₁).unique (pathTo t₁).2 Walk.IsPath.nil
    simp [dist, hnil]
  have h_dist_pos : ∀ v, v ≠ t₁ → 0 < dist v := by
    intro v hv
    exact Walk.not_nil_iff_lt_length.mp (Walk.not_nil_of_ne hv.symm)
  have h_mono : ∀ {i j : Fin (k - L_set.card)}, i < j →
      dist (t_seq i) < dist (t_seq j) ∨ (dist (t_seq i) = dist (t_seq j) ∧ t_seq i < t_seq j) := by
    intro i j hij
    have h_lt : (iso i).1 < (iso j).1 := iso.strictMono hij
    rw [← h_key_t i, ← h_key_t j] at h_lt
    exact Prod.Lex.lt_iff.mp h_lt
  have h_t0 : t_seq ⟨0, hm_pos⟩ = t₁ := by
    by_contra hne
    have h_pos : 0 < dist (t_seq ⟨0, hm_pos⟩) := h_dist_pos _ hne
    have ht1_range : t₁ ∈ Set.range t_seq := h_range ▸ ht₁_mem
    rcases ht1_range with ⟨j, hj⟩
    have hj_ne : j ≠ ⟨0, hm_pos⟩ := by
      intro heq; exact hne (heq ▸ hj)
    have hj_pos : 0 < j.1 := Nat.pos_of_ne_zero (fun h => hj_ne (Fin.ext h))
    have hr := h_mono (show ⟨0, hm_pos⟩ < j from hj_pos)
    rw [hj, h_dist_zero] at hr
    omega
  have h_penult : ∀ i : Fin (k - L_set.card), 0 < i.1 →
      ∃ j : Fin (k - L_set.card), j.1 < i.1 ∧ T.Adj (t_seq j) (t_seq i) ∧
      t_seq j = (pathTo (t_seq i)).1.penultimate := by
    intro i hi
    have hne : t_seq i ≠ t₁ := by
      intro heq
      rw [← h_t0] at heq
      have h_eq := t_seq.injective heq
      have : i.1 = 0 := congrArg Fin.val h_eq
      omega
    have hnil : ¬(pathTo (t_seq i)).1.Nil := Walk.not_nil_of_ne hne.symm
    let w := (pathTo (t_seq i)).1.penultimate
    have hadj : T.Adj w (t_seq i) := (pathTo (t_seq i)).1.adj_penultimate hnil
    have hw_mem_supp : w ∈ (pathTo (t_seq i)).1.support :=
      List.dropLast_subset _ ((pathTo (t_seq i)).1.penultimate_mem_dropLast_support hnil)
    have hw_mem : w ∈ V' := by
      rw [mem_compl]
      intro hwL
      have hdeg := hL_sub w hwL
      rw [degree_eq_one_iff_existsUnique_adj] at hdeg
      rcases hdeg with ⟨u₀, hu₀, huniq⟩
      have hw_ne : w ≠ t₁ := fun h => ht₁ (h ▸ hwL)
      have hnil_w : ¬(pathTo w).1.Nil := Walk.not_nil_of_ne hw_ne.symm
      let w' := (pathTo w).1.penultimate
      have hadj_w' : T.Adj w w' := ((pathTo w).1.adj_penultimate hnil_w).symm
      have hw'_eq := huniq w' hadj_w'
      have hti_eq := huniq (t_seq i) hadj
      have hw'_eq_ti : w' = t_seq i := hw'_eq.trans hti_eq.symm
      have hti_mem_pw : t_seq i ∈ (pathTo w).1.support := by
        rw [← hw'_eq_ti]
        exact List.dropLast_subset _ ((pathTo w).1.penultimate_mem_dropLast_support hnil_w)
      have hw_not_mem := hT.isAcyclic.ne_mem_support_of_support_of_adj_of_isPath
        (pathTo (t_seq i)).2 (pathTo w).2 hadj.symm hw_mem_supp
      exact hw_not_mem hti_mem_pw
    have hw_range : w ∈ Set.range t_seq := h_range ▸ hw_mem
    rcases hw_range with ⟨j, hj⟩
    have hj_dist : dist w + 1 = dist (t_seq i) := by
      have h_concat : (pathTo (t_seq i)).1 = (pathTo w).1.concat hadj :=
        hT.isAcyclic.path_concat (pathTo w).2 (pathTo (t_seq i)).2 hadj hw_mem_supp
      have hlen := congrArg Walk.length h_concat
      simpa [dist] using hlen.symm
    have hj_lt : j.1 < i.1 := by
      by_contra hge
      rcases eq_or_lt_of_le (not_lt.mp hge) with heq | hlt
      · have hij : i = j := Fin.ext heq
        rw [hij, hj] at hj_dist
        omega
      · have hr := h_mono (show i < j from hlt)
        rw [hj] at hr
        omega
    exact ⟨j, hj_lt, hj ▸ hadj, hj⟩
  choose par hpar_lt hpar_adj hpar_pen using h_penult
  refine ⟨k - L_set.card, rfl, hm_pos, t_seq, par, h_range, h_t0,
    fun i hi => ⟨hpar_lt i hi, hpar_adj i hi⟩, ?_⟩
  intro i hi j hj_lt hadj_j
  by_contra hj_ne
  have hj_dist : dist (t_seq j) ≤ dist (t_seq i) := by
    have hr := h_mono (show j < i from hj_lt)
    omega
  by_cases hsupp : t_seq j ∈ (pathTo (t_seq i)).1.support
  · have h_eq_pen : t_seq j = (pathTo (t_seq i)).1.penultimate :=
      hT.isAcyclic.eq_penultimate_of_adj_end (pathTo (t_seq i)).2 hadj_j.symm hsupp
    have h_eq_par := h_eq_pen.trans (hpar_pen i hi).symm
    exact hj_ne (t_seq.injective h_eq_par)
  · have h_concat := (pathTo (t_seq i)).2.concat hsupp hadj_j.symm
    have h_eq_pj : (pathTo (t_seq j)).1 = (pathTo (t_seq i)).1.concat hadj_j.symm :=
      (hT.existsUnique_path t₁ (t_seq j)).unique (pathTo (t_seq j)).2 h_concat
    have hlen : dist (t_seq j) = dist (t_seq i) + 1 := by
      simpa [dist] using congrArg Walk.length h_eq_pj
    omega

/- ## Section 2: Low-degree set `U_low` and `A`-neighborhood estimates -/

lemma card_filter_adj_ge_of_neighborSet {n k r : ℕ} {G : SimpleGraph (Fin n)}
    {A : Finset (Fin n)} (hA : A.card = k) (hk_n : k ≤ n) (hkr : n < k + r)
    {v : Fin n} (hv_deg : n / 8 ≤ (G.neighborSet v).ncard) :
    n / 8 - r ≤ (A.filter (G.Adj v)).card := by
  have hsub : G.neighborFinset v ⊆ A.filter (G.Adj v) ∪ Aᶜ := by
    intro w hw
    have hadj : G.Adj v w := (mem_neighborFinset G v w).mp hw
    by_cases hwA : w ∈ A
    · exact mem_union_left _ (mem_filter.mpr ⟨hwA, hadj⟩)
    · exact mem_union_right _ (mem_compl.mpr hwA)
  have hcard1 : (G.neighborFinset v).card ≤ (A.filter (G.Adj v)).card + Aᶜ.card :=
    (card_le_card hsub).trans (card_union_le _ _)
  have hcard2 : (G.neighborFinset v).card = (G.neighborSet v).ncard := by
    rw [neighborFinset_def, Set.ncard_eq_toFinset_card']
  have hAc : Aᶜ.card = n - k := by
    rw [card_compl, Fintype.card_fin, hA]
  omega

lemma ulow_card_le {n k r : ℕ} {μ : ℝ} (hμ_pos : 0 < μ) (hk_pos : 0 < k)
    (hk_ge : (20 : ℝ) ≤ μ * k)
    {G : SimpleGraph (Fin n)} (hGc : Gᶜ.edgeSet.ncard ≤ r * n)
    {u : Fin n} {A W : Finset (Fin n)} (hA : A.card = k) (hW : W.card ≤ r) :
    let U_deg := (A.erase u).filter (fun v => ((A.filter (G.Adj v)).card : ℝ) < (1 - μ / 10) * k)
    let U_low := U_deg ∪ (W ∩ A)
    (U_low.card : ℝ) ≤ (40 * n / (μ * k) + 1) * r := by
  intro U_deg U_low
  let S : Finset (Fin n × Fin n) := (U_deg ×ˢ A).filter (fun p => p.1 ≠ p.2 ∧ ¬ G.Adj p.1 p.2)
  have hS_lower : (U_deg.card : ℝ) * (μ * k / 20) ≤ S.card := by
    have h_each : ∀ v ∈ U_deg, (μ * k / 20 : ℝ) ≤
        ((A.filter (fun w => w ≠ v ∧ ¬ G.Adj v w)).card : ℝ) := by
      intro v hv
      have hv_mem := mem_filter.mp hv
      have hvA : v ∈ A := mem_of_mem_erase hv_mem.1
      have hv_lt : ((A.filter (G.Adj v)).card : ℝ) < (1 - μ / 10) * k := hv_mem.2
      have h_split : A.card = 1 + (A.filter (G.Adj v)).card +
          (A.filter (fun w => w ≠ v ∧ ¬ G.Adj v w)).card := by
        have h1 : A \ {v} = A.filter (fun w => w ≠ v) := by
          ext w; simp [and_comm]
        have h2 : (A.filter (fun w => w ≠ v)).card =
            (A.filter (G.Adj v)).card + (A.filter (fun w => w ≠ v ∧ ¬ G.Adj v w)).card := by
          have h_eq1 : (A.filter (fun w => w ≠ v)).filter (G.Adj v) = A.filter (G.Adj v) := by
            ext w; simp only [mem_filter]
            exact ⟨fun ⟨⟨hwA, _⟩, hadj⟩ => ⟨hwA, hadj⟩,
              fun ⟨hwA, hadj⟩ => ⟨⟨hwA, hadj.ne.symm⟩, hadj⟩⟩
          have h_eq2 : (A.filter (fun w => w ≠ v)).filter (fun w => ¬ G.Adj v w) =
              A.filter (fun w => w ≠ v ∧ ¬ G.Adj v w) := by
            ext w; simp [and_assoc]
          rw [← h_eq1, ← h_eq2]
          exact (Finset.card_filter_add_card_filter_not (s := A.filter (fun w => w ≠ v))
            (p := G.Adj v)).symm
        have h3 := card_sdiff_add_card_eq_card (singleton_subset_iff.mpr hvA)
        rw [card_singleton, h1, h2] at h3
        omega
      rw [hA] at h_split
      have h_splitR : (k : ℝ) = 1 + (A.filter (G.Adj v)).card +
          (A.filter (fun w => w ≠ v ∧ ¬ G.Adj v w)).card := by exact_mod_cast h_split
      linarith
    have h_sum_le : (U_deg.card : ℝ) * (μ * k / 20) ≤
        ∑ v ∈ U_deg, ((A.filter (fun w => w ≠ v ∧ ¬ G.Adj v w)).card : ℝ) := by
      rw [← nsmul_eq_mul, ← Finset.sum_const]
      exact Finset.sum_le_sum h_each
    have hS_eq : S.card = ∑ v ∈ U_deg, (A.filter (fun w => w ≠ v ∧ ¬ G.Adj v w)).card := by
      have h_eq : S = U_deg.biUnion (fun v =>
          (A.filter (fun w => w ≠ v ∧ ¬ G.Adj v w)).image (fun w => (v, w))) := by
        ext ⟨v, w⟩
        simp only [S, mem_filter, mem_product, mem_biUnion, mem_image, Prod.mk.injEq]
        constructor
        · rintro ⟨⟨hv, hw⟩, hne, hnadj⟩
          exact ⟨v, hv, w, ⟨hw, hne.symm, hnadj⟩, rfl, rfl⟩
        · rintro ⟨v', hv', w', ⟨hw', hne, hnadj⟩, rfl, rfl⟩
          exact ⟨⟨hv', hw'⟩, hne.symm, hnadj⟩
      rw [h_eq, card_biUnion]
      · refine Finset.sum_congr rfl (fun v _ => ?_)
        refine card_image_of_injOn (fun w₁ _ w₂ _ h => (Prod.mk.inj h).2)
      · intro v₁ _ v₂ _ hne
        rw [Function.onFun, Finset.disjoint_left]
        intro ⟨a, b⟩ ha hb
        rcases mem_image.mp ha with ⟨_, _, h1⟩
        rcases mem_image.mp hb with ⟨_, _, h2⟩
        exact hne ((Prod.mk.inj h1).1.trans (Prod.mk.inj h2).1.symm)
    have hS_eqR : (S.card : ℝ) =
        ∑ v ∈ U_deg, ((A.filter (fun w => w ≠ v ∧ ¬ G.Adj v w)).card : ℝ) := by
      exact_mod_cast hS_eq
    linarith
  have hS_upper : S.card ≤ 2 * r * n := by
    let S1 := S.filter (fun p => p.1 < p.2)
    let S2 := S.filter (fun p => p.2 < p.1)
    have hS_sub : S ⊆ S1 ∪ S2 := by
      intro p hp
      have hne : p.1 ≠ p.2 := (mem_filter.mp hp).2.1
      rcases lt_or_gt_of_ne hne with h | h
      · exact mem_union_left _ (mem_filter.mpr ⟨hp, h⟩)
      · exact mem_union_right _ (mem_filter.mpr ⟨hp, h⟩)
    have h_map1 : S1.card ≤ Gᶜ.edgeFinset.card := by
      refine card_le_card_of_injOn (fun p => s(p.1, p.2)) ?_ ?_
      · intro p hp
        rcases mem_filter.mp hp with ⟨hpS, _⟩
        rcases mem_filter.mp hpS with ⟨_, hne, hnadj⟩
        exact mem_edgeFinset.mpr ⟨hne, hnadj⟩
      · intro p₁ hp₁ p₂ hp₂ heq
        have h1 : p₁.1 < p₁.2 := (mem_filter.mp hp₁).2
        have h2 : p₂.1 < p₂.2 := (mem_filter.mp hp₂).2
        rcases Sym2.eq_iff.mp heq with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · exact Prod.ext ha hb
        · omega
    have h_map2 : S2.card ≤ Gᶜ.edgeFinset.card := by
      refine card_le_card_of_injOn (fun p => s(p.1, p.2)) ?_ ?_
      · intro p hp
        rcases mem_filter.mp hp with ⟨hpS, _⟩
        rcases mem_filter.mp hpS with ⟨_, hne, hnadj⟩
        exact mem_edgeFinset.mpr ⟨hne, hnadj⟩
      · intro p₁ hp₁ p₂ hp₂ heq
        have h1 : p₁.2 < p₁.1 := (mem_filter.mp hp₁).2
        have h2 : p₂.2 < p₂.1 := (mem_filter.mp hp₂).2
        rcases Sym2.eq_iff.mp heq with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · exact Prod.ext ha hb
        · omega
    have hGc_eq : Gᶜ.edgeFinset.card = Gᶜ.edgeSet.ncard := by
      rw [edgeFinset_card, Set.ncard_eq_toFinset_card', ← Set.toFinset_card]
    have h1 := (card_le_card hS_sub).trans (card_union_le S1 S2)
    have h_two : S1.card + S2.card ≤ 2 * Gᶜ.edgeFinset.card := by omega
    have h_mul : 2 * Gᶜ.edgeFinset.card ≤ 2 * (r * n) :=
      Nat.mul_le_mul_left 2 (hGc_eq ▸ hGc)
    calc S.card ≤ S1.card + S2.card := h1
      _ ≤ 2 * Gᶜ.edgeFinset.card := h_two
      _ ≤ 2 * (r * n) := h_mul
      _ = 2 * r * n := by ring
  have h_pos_denom : 0 < μ * k / 20 := by positivity
  have hU_deg_le : (U_deg.card : ℝ) ≤ (40 * n / (μ * k)) * r := by
    have hS_upperR : (S.card : ℝ) ≤ 2 * r * n := by exact_mod_cast hS_upper
    have h1 : (U_deg.card : ℝ) * (μ * k / 20) ≤ 2 * r * n := hS_lower.trans hS_upperR
    have h2 : (U_deg.card : ℝ) ≤ (2 * r * n) / (μ * k / 20) := (le_div_iff₀ h_pos_denom).mpr h1
    linarith [show (2 * (r : ℝ) * n) / (μ * k / 20) = (40 * n / (μ * k)) * r by ring]
  have hWA_le : ((W ∩ A).card : ℝ) ≤ r := by
    have h1 : (W ∩ A).card ≤ W.card := card_le_card inter_subset_left
    exact_mod_cast h1.trans hW
  have hU_low_le : (U_low.card : ℝ) ≤ U_deg.card + (W ∩ A).card := by
    exact_mod_cast card_union_le U_deg (W ∩ A)
  linarith

/- ## Section 3: Large-star Branch A (`μ * k ≤ d`) -/

lemma branchA_embed {n k : ℕ} {μ : ℝ} (hμ_pos : 0 < μ) (hμ_lt : μ < 1 / 100)
    (hk_pos : 0 < k) (h_kn : 99 * (n : ℝ) ≤ 100 * k)
    {T : SimpleGraph (Fin k)} (hT : T.IsTree)
    (t₁ : Fin k)
    (ht₁ : ∀ x : Fin k, ((Finset.univ.filter (fun v => T.degree v = 1)).filter (T.Adj x)).card ≤
      ((Finset.univ.filter (fun v => T.degree v = 1)).filter (T.Adj t₁)).card)
    (hd_ge : μ * k ≤ (((Finset.univ.filter (fun v => T.degree v = 1)).filter (T.Adj t₁)).card : ℝ))
    {G : SimpleGraph (Fin n)} {u : Fin n} {A W : Finset (Fin n)}
    (hA : A.card = k) (huA : u ∈ A) (hu_adj : ∀ v ∈ A, v ≠ u → G.Adj u v)
    (_huW : u ∉ W)
    {U_low : Finset (Fin n)} (_hU_sub : U_low ⊆ A) (hu_not_U : u ∉ U_low)
    (hWA_sub : W ∩ A ⊆ U_low)
    (hU_deg : ∀ v ∈ A \ U_low, ((A.filter (G.Adj v)).card : ℝ) ≥ (1 - μ / 10) * k)
    (hU_card : (U_low.card : ℝ) ≤ μ * k / 10) :
    ∃ f : Fin k ↪ Fin n, let U := T.map f
      (∀ x, f x ∈ A) ∧ U ≤ G ∧
      (∀ w ∈ W, ∀ x y, U.Adj w x → U.Adj w y → x = y) ∧
      (∀ v ≠ u, min ((G.neighborSet v).ncard - 1) (n / 5) ≤ ((G \ U).neighborSet v).ncard) ∧
      (n / 5 ≤ ((G \ U).neighborSet u).ncard ∨ ∀ w ∈ W, ∀ x, U.Adj w x → x = u) := by
  classical
  let Leaves : Finset (Fin k) := Finset.univ.filter (fun v => T.degree v = 1)
  let L₀ : Finset (Fin k) := Leaves.filter (T.Adj t₁)
  have hL₀_sub : ∀ ℓ ∈ L₀, T.degree ℓ = 1 := fun ℓ hℓ =>
    (mem_filter.mp (mem_filter.mp hℓ).1).2
  have ht₁_not_L₀ : t₁ ∉ L₀ := fun h => (T.ne_of_adj (mem_filter.mp h).2) rfl
  obtain ⟨m, hm_eq, hm_pos, t_seq, par, h_range, h_t0, hpar, hpar_uniq⟩ :=
    tree_ordering_after_removing_leaves hT t₁ L₀ hL₀_sub ht₁_not_L₀
  -- Step-by-step greedy embedding of `t_seq 0, ..., t_seq (m-1)` into `A \ U_low`
  let State (r : ℕ) := { g : ∀ i : Fin m, i.1 < r → Fin n //
    (∀ i hi, g i hi ∈ A \ U_low) ∧
    (∀ i₁ hi₁ i₂ hi₂, g i₁ hi₁ = g i₂ hi₂ → i₁ = i₂) ∧
    (∀ (hi0 : 0 < r), g ⟨0, hm_pos⟩ hi0 = u) ∧
    (∀ i hi (hi_pos : 0 < i.1), G.Adj (g (par i hi_pos) ((hpar i hi_pos).1.trans hi)) (g i hi)) }
  have h_build : ∀ r : ℕ, r ≤ m → Nonempty (State r) := by
    intro r hr
    induction r with
    | zero =>
      refine ⟨⟨fun i hi => absurd hi (Nat.not_lt_zero _),
        fun i hi => absurd hi (Nat.not_lt_zero _),
        fun i₁ hi₁ => absurd hi₁ (Nat.not_lt_zero _),
        fun h => absurd h (Nat.not_lt_zero _),
        fun i hi => absurd hi (Nat.not_lt_zero _)⟩⟩
    | succ r ih =>
      obtain ⟨⟨g, hg_mem, hg_inj, hg_0, hg_adj⟩⟩ := ih (Nat.le_of_succ_le hr)
      by_cases hr0 : r = 0
      · subst hr0
        refine ⟨⟨fun i _ => u, fun i _ => mem_sdiff.mpr ⟨huA, hu_not_U⟩,
          fun i₁ hi₁ i₂ hi₂ _ => Fin.ext (by omega),
          fun _ => rfl,
          fun i hi hi_pos => by omega⟩⟩
      · have hr_pos : 0 < r := Nat.pos_of_ne_zero hr0
        let i₀ : Fin m := ⟨r, hr⟩
        let p₀ : Fin m := par i₀ hr_pos
        have hp₀_lt : p₀.1 < r := (hpar i₀ hr_pos).1
        let vp := g p₀ hp₀_lt
        have hvp_mem : vp ∈ A \ U_low := hg_mem p₀ hp₀_lt
        let Im_prev : Finset (Fin n) := (Finset.univ.filter (fun i : Fin m => i.1 < r)).image
          (fun i => if hi : i.1 < r then g i hi else u)
        have hIm_card : Im_prev.card ≤ r := by
          refine (Finset.card_image_le).trans ?_
          have h_inj : (Finset.univ.filter (fun i : Fin m => i.1 < r)).card ≤ (Finset.univ : Finset (Fin r)).card := by
            refine card_le_card_of_injOn (fun i : Fin m => (⟨i.1 % r, Nat.mod_lt _ hr_pos⟩ : Fin r)) ?_ ?_
            · intro i _; exact mem_univ _
            · intro i₁ hi₁ i₂ hi₂ h
              have h1 : i₁.1 < r := (mem_filter.mp hi₁).2
              have h2 : i₂.1 < r := (mem_filter.mp hi₂).2
              have hv : i₁.1 % r = i₂.1 % r := congrArg Fin.val h
              rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at hv
              exact Fin.ext hv
          exact h_inj.trans (by rw [card_fin])
        let Cand := (A.filter (G.Adj vp)) \ (U_low ∪ Im_prev)
        have hCand_nonempty : Cand.Nonempty := by
          rw [← Finset.card_pos]
          have h1 := hU_deg vp hvp_mem
          have h_diff_le : (A.filter (G.Adj vp)).card - (U_low.card + Im_prev.card) ≤ Cand.card := by
            have h2 : (A.filter (G.Adj vp)).card ≤ Cand.card + (U_low ∪ Im_prev).card :=
              card_le_card_sdiff_add_card
            have h3 := card_union_le U_low Im_prev
            omega
          have hL₀_le : L₀.card ≤ k := by
            have := card_le_univ L₀
            rwa [Fintype.card_fin] at this
          have h_r_le : r ≤ k - L₀.card - 1 := by omega
          have h_Im_le : (Im_prev.card : ℝ) ≤ (k : ℝ) - L₀.card - 1 := by
            have h1' : (Im_prev.card : ℝ) ≤ ((k - L₀.card - 1 : ℕ) : ℝ) := by
              exact_mod_cast hIm_card.trans h_r_le
            have hL₀_lt : L₀.card + 1 ≤ k := by omega
            have h2' : ((k - L₀.card - 1 : ℕ) : ℝ) = (k : ℝ) - L₀.card - 1 := by
              have hsub1 : (k - L₀.card - 1 : ℕ) = k - (L₀.card + 1) := by omega
              rw [hsub1, Nat.cast_sub hL₀_lt, Nat.cast_add, Nat.cast_one]
              ring
            linarith
          have h_posR : (0 : ℝ) < ((A.filter (G.Adj vp)).card : ℝ) - (U_low.card + Im_prev.card) := by
            linarith
          have h_posN : 0 < (A.filter (G.Adj vp)).card - (U_low.card + Im_prev.card) := by
            by_contra h0
            have : (A.filter (G.Adj vp)).card ≤ U_low.card + Im_prev.card := by omega
            have : ((A.filter (G.Adj vp)).card : ℝ) ≤ U_low.card + Im_prev.card := by exact_mod_cast this
            linarith
          omega
        let v_new := hCand_nonempty.choose
        have hv_new : v_new ∈ Cand := hCand_nonempty.choose_spec
        have hv_adj : G.Adj vp v_new := (mem_filter.mp (mem_sdiff.mp hv_new).1).2
        have hv_A : v_new ∈ A := (mem_filter.mp (mem_sdiff.mp hv_new).1).1
        have hv_not_U : v_new ∉ U_low := fun h => (mem_sdiff.mp hv_new).2 (mem_union_left _ h)
        have hv_not_Im : v_new ∉ Im_prev := fun h => (mem_sdiff.mp hv_new).2 (mem_union_right _ h)
        let g' : ∀ i : Fin m, i.1 < r + 1 → Fin n := fun i hi =>
          if h_lt : i.1 < r then g i h_lt else v_new
        refine ⟨⟨g', ?_, ?_, ?_, ?_⟩⟩
        · intro i hi
          dsimp only [g']
          split_ifs with h_lt
          · exact hg_mem i h_lt
          · exact mem_sdiff.mpr ⟨hv_A, hv_not_U⟩
        · intro i₁ hi₁ i₂ hi₂ heq
          dsimp only [g'] at heq
          by_cases h1 : i₁.1 < r <;> by_cases h2 : i₂.1 < r
          · rw [dif_pos h1, dif_pos h2] at heq
            exact hg_inj i₁ h1 i₂ h2 heq
          · exfalso
            rw [dif_pos h1, dif_neg h2] at heq
            apply hv_not_Im
            rw [← heq]
            exact mem_image.mpr ⟨i₁, mem_filter.mpr ⟨mem_univ _, h1⟩, dif_pos h1⟩
          · exfalso
            rw [dif_neg h1, dif_pos h2] at heq
            apply hv_not_Im
            rw [heq]
            exact mem_image.mpr ⟨i₂, mem_filter.mpr ⟨mem_univ _, h2⟩, dif_pos h2⟩
          · exact Fin.ext (by omega)
        · intro _
          dsimp only [g']
          rw [dif_pos hr_pos]
          exact hg_0 hr_pos
        · intro i hi hi_pos
          dsimp only [g']
          by_cases h_lt : i.1 < r
          · have h_lt_p : (par i hi_pos).1 < r := (hpar i hi_pos).1.trans h_lt
            rw [dif_pos h_lt, dif_pos h_lt_p]
            exact hg_adj i h_lt hi_pos
          · have hi_val : i.1 = r := by omega
            have hi_eq : i = i₀ := Fin.ext hi_val
            subst hi_eq
            have h_lt_p : (par i₀ hi_pos).1 < r := (hpar i₀ hi_pos).1
            rw [dif_neg h_lt, dif_pos h_lt_p]
            exact hv_adj
  obtain ⟨⟨g, hg_mem, hg_inj, hg_0, hg_adj⟩⟩ := h_build m le_rfl
  let ψ : Fin m ↪ Fin n :=
    ⟨fun i => g i i.2, fun i₁ i₂ h => hg_inj i₁ i₁.2 i₂ i₂.2 h⟩
  have hψ0 : ψ ⟨0, hm_pos⟩ = u := hg_0 hm_pos
  have hψ_mem : ∀ i, ψ i ∈ A \ U_low := fun i => hg_mem i i.2
  have hψ_adj : ∀ i j : Fin m, T.Adj (t_seq i) (t_seq j) → G.Adj (ψ i) (ψ j) := by
    intro i j hadj
    rcases lt_trichotomy i.1 j.1 with hij | hij | hij
    · have hj_pos : 0 < j.1 := by omega
      have h_eq := hpar_uniq j hj_pos i hij hadj
      subst h_eq
      exact hg_adj j j.2 hj_pos
    · have hij' : i = j := Fin.ext hij
      subst hij'
      exact absurd hadj (fun h => T.ne_of_adj h rfl)
    · have hi_pos : 0 < i.1 := by omega
      have h_eq := hpar_uniq i hi_pos j hij hadj.symm
      subst h_eq
      exact (hg_adj i i.2 hi_pos).symm
  -- Bijection between `L₀` and `B := A \ Im(ψ)`
  let Imψ : Finset (Fin n) := Finset.univ.image ψ
  let B : Finset (Fin n) := A \ Imψ
  have hImψ_sub : Imψ ⊆ A := by
    intro v hv
    rcases mem_image.mp hv with ⟨i, _, rfl⟩
    exact (mem_sdiff.mp (hψ_mem i)).1
  have hImψ_card : Imψ.card = m := by
    rw [card_image_of_injective _ ψ.injective, card_fin]
  have hB_card : B.card = L₀.card := by
    have h1 : B.card = A.card - Imψ.card := card_sdiff_of_subset hImψ_sub
    have hL₀_le : L₀.card ≤ k := by
      have := card_le_univ L₀
      rwa [Fintype.card_fin] at this
    omega
  let bij : L₀ ≃ B := (L₀.equivFin).trans ((Fin.castOrderIso hB_card.symm).toEquiv.trans B.equivFin.symm)
  have h_inv_t : ∀ x : Fin k, x ∉ L₀ → ∃ i : Fin m, t_seq i = x := by
    intro x hx
    have hx_mem : x ∈ ((L₀ᶜ : Finset (Fin k)) : Set (Fin k)) := mem_compl.mpr hx
    rw [← h_range] at hx_mem
    exact hx_mem
  let fFun : Fin k → Fin n := fun x =>
    if hx : x ∈ L₀ then (bij ⟨x, hx⟩).1
    else ψ (h_inv_t x hx).choose
  have hf_inj : Function.Injective fFun := by
    intro x₁ x₂ heq
    dsimp only [fFun] at heq
    by_cases h1 : x₁ ∈ L₀ <;> by_cases h2 : x₂ ∈ L₀
    · rw [dif_pos h1, dif_pos h2] at heq
      have hsub : (⟨x₁, h1⟩ : L₀) = ⟨x₂, h2⟩ := bij.injective (Subtype.ext heq)
      exact congrArg Subtype.val hsub
    · exfalso
      rw [dif_pos h1, dif_neg h2] at heq
      have hB_mem := (bij ⟨x₁, h1⟩).2
      rw [heq] at hB_mem
      exact (mem_sdiff.mp hB_mem).2 (mem_image_of_mem ψ (mem_univ _))
    · exfalso
      rw [dif_neg h1, dif_pos h2] at heq
      have hB_mem := (bij ⟨x₂, h2⟩).2
      rw [← heq] at hB_mem
      exact (mem_sdiff.mp hB_mem).2 (mem_image_of_mem ψ (mem_univ _))
    · rw [dif_neg h1, dif_neg h2] at heq
      have hi := ψ.injective heq
      have h1' := (h_inv_t x₁ h1).choose_spec
      have h2' := (h_inv_t x₂ h2).choose_spec
      rw [← h1', ← h2', hi]
  let f : Fin k ↪ Fin n := ⟨fFun, hf_inj⟩
  have hf_L₀ : ∀ x (hx : x ∈ L₀), f x = (bij ⟨x, hx⟩).1 := fun x hx => dif_pos hx
  have hf_not_L₀ : ∀ x (hx : x ∉ L₀), ∃ i : Fin m, f x = ψ i ∧ t_seq i = x := by
    intro x hx
    refine ⟨(h_inv_t x hx).choose, dif_neg hx, (h_inv_t x hx).choose_spec⟩
  have hf_t₁ : f t₁ = u := by
    obtain ⟨i, hfi, hti⟩ := hf_not_L₀ t₁ ht₁_not_L₀
    have hi0 : i = ⟨0, hm_pos⟩ := t_seq.injective (hti.trans h_t0.symm)
    rw [hfi, hi0, hψ0]
  have hf_A : ∀ x, f x ∈ A := by
    intro x
    by_cases hx : x ∈ L₀
    · rw [hf_L₀ x hx]
      exact (mem_sdiff.mp (bij ⟨x, hx⟩).2).1
    · obtain ⟨i, hfi, _⟩ := hf_not_L₀ x hx
      rw [hfi]
      exact (mem_sdiff.mp (hψ_mem i)).1
  have hU_le_G : T.map f ≤ G := by
    intro a b hab
    rcases (map_adj f T a b).mp hab with ⟨x, y, hadj, rfl, rfl⟩
    by_cases hx : x ∈ L₀ <;> by_cases hy : y ∈ L₀
    · exfalso
      have hdeg := hL₀_sub x hx
      rw [degree_eq_one_iff_existsUnique_adj] at hdeg
      rcases hdeg with ⟨w, _, huniq⟩
      have h1 : w = t₁ := (huniq t₁ (mem_filter.mp hx).2.symm).symm
      have h2 : w = y := (huniq y hadj).symm
      exact ht₁_not_L₀ (h1 ▸ h2 ▸ hy)
    · have hdeg := hL₀_sub x hx
      rw [degree_eq_one_iff_existsUnique_adj] at hdeg
      rcases hdeg with ⟨_, _, huniq⟩
      have hy_eq : y = t₁ := (huniq y hadj).trans (huniq t₁ (mem_filter.mp hx).2.symm).symm
      subst hy_eq
      rw [hf_t₁]
      exact (hu_adj (f x) (hf_A x) (hf_t₁ ▸ f.injective.ne (T.ne_of_adj hadj))).symm
    · have hdeg := hL₀_sub y hy
      rw [degree_eq_one_iff_existsUnique_adj] at hdeg
      rcases hdeg with ⟨_, _, huniq⟩
      have hx_eq : x = t₁ := (huniq x hadj.symm).trans (huniq t₁ (mem_filter.mp hy).2.symm).symm
      subst hx_eq
      rw [hf_t₁]
      exact hu_adj (f y) (hf_A y) (hf_t₁ ▸ f.injective.ne (T.ne_of_adj hadj.symm))
    · obtain ⟨i, hfi, hti⟩ := hf_not_L₀ x hx
      obtain ⟨j, hfj, htj⟩ := hf_not_L₀ y hy
      rw [hfi, hfj]
      exact hψ_adj i j (hti ▸ htj ▸ hadj)
  have hW_to_u : ∀ w ∈ W, ∀ y, (T.map f).Adj w y → y = u := by
    intro w hw y hadj
    rcases (map_adj f T w y).mp hadj with ⟨x, x', hTx, hfx, rfl⟩
    have hx_L₀ : x ∈ L₀ := by
      by_contra hx_not
      obtain ⟨i, hfi, _⟩ := hf_not_L₀ x hx_not
      have hw_not_U : w ∉ U_low := by
        rw [← hfx, hfi]
        exact (mem_sdiff.mp (hψ_mem i)).2
      have hw_A : w ∈ A := hfx ▸ hf_A x
      exact hw_not_U (hWA_sub (mem_inter.mpr ⟨hw, hw_A⟩))
    have hdeg := hL₀_sub x hx_L₀
    rw [degree_eq_one_iff_existsUnique_adj] at hdeg
    rcases hdeg with ⟨_, _, huniq⟩
    have hx'_eq : x' = t₁ := (huniq x' hTx).trans (huniq t₁ (mem_filter.mp hx_L₀).2.symm).symm
    rw [hx'_eq, hf_t₁]
  refine ⟨f, hf_A, hU_le_G, ?_, ?_, Or.inr hW_to_u⟩
  · intro w hw x y hwx hwy
    exact (hW_to_u w hw x hwx).trans (hW_to_u w hw y hwy).symm
  · intro v hvu
    have h_diff_eq : ((G \ T.map f).neighborSet v).ncard =
        (G.neighborSet v).ncard - ((T.map f).neighborSet v).ncard := by
      have h_sub : (T.map f).neighborFinset v ⊆ G.neighborFinset v := by
        intro z hz
        exact (mem_neighborFinset G v z).mpr (hU_le_G ((mem_neighborFinset (T.map f) v z).mp hz))
      have h_eq : (G \ T.map f).neighborFinset v = G.neighborFinset v \ (T.map f).neighborFinset v := by
        ext z; simp [mem_neighborFinset]
      have hc1 : ((G \ T.map f).neighborSet v).ncard = ((G \ T.map f).neighborFinset v).card := by
        rw [← Set.ncard_coe_finset ((G \ T.map f).neighborFinset v), coe_neighborFinset]
      have hc2 : (G.neighborSet v).ncard = (G.neighborFinset v).card := by
        rw [← Set.ncard_coe_finset (G.neighborFinset v), coe_neighborFinset]
      have hc3 : ((T.map f).neighborSet v).ncard = ((T.map f).neighborFinset v).card := by
        rw [← Set.ncard_coe_finset ((T.map f).neighborFinset v), coe_neighborFinset]
      rw [hc1, hc2, hc3, h_eq, card_sdiff_of_subset h_sub]
    by_cases hv_range : v ∈ Set.range f
    · rcases hv_range with ⟨x, rfl⟩
      have h_map_deg : ((T.map f).neighborSet (f x)).ncard = T.degree x := by
        have hc : (T.neighborSet x).ncard = (T.neighborFinset x).card := by
          rw [← Set.ncard_coe_finset (T.neighborFinset x), coe_neighborFinset]
        rw [neighborSet_map, Set.ncard_image_of_injective _ f.injective, hc]
        convert card_neighborFinset_eq_degree (G := T) (v := x)
      rw [h_diff_eq, h_map_deg]
      by_cases hx : x ∈ L₀
      · have hdeg1 : T.degree x = 1 := hL₀_sub x hx
        rw [hdeg1]
        exact min_le_left _ _
      · obtain ⟨i, hfi, hti⟩ := hf_not_L₀ x hx
        have hx_ne_t1 : x ≠ t₁ := fun h => hvu (by rw [h, hf_t₁])
        have h_deg_x : 3 * T.degree x ≤ 2 * k - 1 := tree_deg_le_of_ne_maxLeafDeg hT t₁ ht₁ hx_ne_t1
        have hv_not_U : f x ∈ A \ U_low := by rw [hfi]; exact hψ_mem i
        have hG_deg : ((A.filter (G.Adj (f x))).card : ℝ) ≥ (1 - μ / 10) * k := hU_deg (f x) hv_not_U
        have hG_ncard : (A.filter (G.Adj (f x))).card ≤ (G.neighborSet (f x)).ncard := by
          have hc : (G.neighborSet (f x)).ncard = (G.neighborFinset (f x)).card := by
            rw [← Set.ncard_coe_finset (G.neighborFinset (f x)), coe_neighborFinset]
          rw [hc]
          exact card_le_card (fun z hz => (mem_neighborFinset G (f x) z).mpr (mem_filter.mp hz).2)
        have h_n5 : n / 5 ≤ (G.neighborSet (f x)).ncard - T.degree x := by
          have hG_R : ((1 - μ / 10) * k : ℝ) ≤ (G.neighborSet (f x)).ncard :=
            hG_deg.trans (by exact_mod_cast hG_ncard)
          have hT_R : (T.degree x : ℝ) ≤ (2 * k : ℝ) / 3 := by
            have : (3 * T.degree x : ℝ) ≤ 2 * k := by exact_mod_cast (by omega : 3 * T.degree x ≤ 2 * k)
            linarith
          have hk_nR : (0.99 : ℝ) * n ≤ k := by linarith
          have hn5 : ((n / 5 : ℕ) : ℝ) ≤ (n : ℝ) / 5 := by
            have : ((n / 5 : ℕ) : ℝ) * 5 ≤ n := by exact_mod_cast Nat.div_mul_le_self n 5
            linarith
          have h_add_R : ((n / 5 + T.degree x : ℕ) : ℝ) ≤ ((G.neighborSet (f x)).ncard : ℝ) := by
            rw [Nat.cast_add]
            nlinarith
          have h_add_N : n / 5 + T.degree x ≤ (G.neighborSet (f x)).ncard := by
            exact_mod_cast h_add_R
          omega
        exact le_trans (min_le_right _ _) h_n5
    · have hU_empty : (T.map f).neighborSet v = ∅ := by
        ext z
        simp only [mem_neighborSet, map_adj, Set.mem_empty_iff_false, iff_false, not_exists, not_and]
        intro x _ _ hfx _
        exact hv_range ⟨x, hfx⟩
      rw [h_diff_eq, hU_empty, Set.ncard_empty, Nat.sub_zero]
      exact le_trans (min_le_left _ _) (Nat.sub_le _ _)

/- ## Section 4: Random greedy process, MGF bounds, Hall, and Branch B (`d < μ * k`) -/

lemma exp_le_quadratic_of_abs_le_one {x : ℝ} (hx : |x| ≤ 1) :
    Real.exp x ≤ 1 + x + x ^ 2 := by
  have h := (abs_sub_le_iff.mp (Real.abs_exp_sub_one_sub_id_le hx)).1
  linarith

lemma exp_neg_inv_le_factorial_bound {x : ℝ} (hx : 0 < x) {p : ℕ} (_hp : 0 < p) :
    Real.exp (-x) ≤ (p.factorial : ℝ) / x ^ p := by
  have h_sum := Real.sum_le_exp_of_nonneg hx.le (p + 1)
  have h_term : x ^ p / (p.factorial : ℝ) ≤ ∑ i ∈ Finset.range (p + 1), x ^ i / (i.factorial : ℝ) := by
    refine Finset.single_le_sum (fun i _ => div_nonneg (pow_nonneg hx.le i) (Nat.cast_nonneg _)) ?_
    exact Finset.mem_range.mpr (Nat.lt_succ_self p)
  have h_le : x ^ p / (p.factorial : ℝ) ≤ Real.exp x := h_term.trans h_sum
  have hxp_pos : 0 < x ^ p := pow_pos hx p
  rw [Real.exp_neg, le_div_iff₀ hxp_pos]
  calc (Real.exp x)⁻¹ * x ^ p
      = (Real.exp x)⁻¹ * (x ^ p / (p.factorial : ℝ)) * (p.factorial : ℝ) := by field_simp
    _ ≤ (Real.exp x)⁻¹ * Real.exp x * (p.factorial : ℝ) := by
        gcongr
    _ = (p.factorial : ℝ) := by rw [inv_mul_cancel₀ (Real.exp_pos x).ne', one_mul]

section RandomGreedy

variable {n m : ℕ}

noncomputable def stepCand (A U_low : Finset (Fin n)) (G : SimpleGraph (Fin n))
    (par : ∀ i : Fin m, 0 < i.1 → Fin m)
    (ψ : Fin m → Fin n) (i : Fin m) (hi : 0 < i.1) : Finset (Fin n) :=
  (A.filter (G.Adj (ψ (par i hi)))) \ (U_low ∪ (Finset.univ.filter (fun j : Fin m => j.1 < i.1)).image ψ)

lemma stepCand_update_of_lt {A U_low : Finset (Fin n)} {G : SimpleGraph (Fin n)}
    {par : ∀ i : Fin m, 0 < i.1 → Fin m} (hpar : ∀ i hi, (par i hi).1 < i.1)
    {ψ : Fin m → Fin n} {i₀ : Fin m} {v : Fin n}
    {i : Fin m} (hi : 0 < i.1) (hi_le : i.1 ≤ i₀.1) :
    stepCand A U_low G par (Function.update ψ i₀ v) i hi = stepCand A U_low G par ψ i hi := by
  have hp_ne : par i hi ≠ i₀ := by
    intro heq
    have h1 := hpar i hi
    rw [heq] at h1
    omega
  simp only [stepCand, Function.update_of_ne hp_ne]
  congr 2
  refine Finset.image_congr (fun j hj => ?_)
  have hj_lt : j.1 < i.1 := (mem_filter.mp hj).2
  have hj_ne : j ≠ i₀ := fun heq => by rw [heq] at hj_lt; omega
  exact Function.update_of_ne hj_ne v ψ

noncomputable def expValFrom (A U_low : Finset (Fin n)) (G : SimpleGraph (Fin n))
    (par : ∀ i : Fin m, 0 < i.1 → Fin m) :
    ℕ → ((Fin m → Fin n) → ℝ) → (Fin m → Fin n) → ℝ
  | 0, f, ψ => f ψ
  | t + 1, f, ψ =>
    let r := m - (t + 1)
    if hr : r < m then
      if hr0 : 0 < r then
        let i : Fin m := ⟨r, hr⟩
        let C := stepCand A U_low G par ψ i hr0
        if C.Nonempty then
          (∑ v ∈ C, expValFrom A U_low G par t f (Function.update ψ i v)) / (C.card : ℝ)
        else 0
      else 0
    else 0

lemma expValFrom_add (A U_low : Finset (Fin n)) (G : SimpleGraph (Fin n))
    (par : ∀ i : Fin m, 0 < i.1 → Fin m) :
    ∀ t (f g : (Fin m → Fin n) → ℝ) (ψ : Fin m → Fin n),
      expValFrom A U_low G par t (fun x => f x + g x) ψ =
        expValFrom A U_low G par t f ψ + expValFrom A U_low G par t g ψ := by
  intro t
  induction t with
  | zero => intro f g ψ; rfl
  | succ t ih =>
    intro f g ψ
    dsimp only [expValFrom]
    split_ifs with hr hr0 hne
    · simp_rw [ih, Finset.sum_add_distrib, add_div]
    · simp
    · simp
    · simp

lemma expValFrom_smul (A U_low : Finset (Fin n)) (G : SimpleGraph (Fin n))
    (par : ∀ i : Fin m, 0 < i.1 → Fin m) :
    ∀ t (c : ℝ) (f : (Fin m → Fin n) → ℝ) (ψ : Fin m → Fin n),
      expValFrom A U_low G par t (fun x => c * f x) ψ =
        c * expValFrom A U_low G par t f ψ := by
  intro t
  induction t with
  | zero => intro c f ψ; rfl
  | succ t ih =>
    intro c f ψ
    dsimp only [expValFrom]
    split_ifs with hr hr0 hne
    · simp_rw [ih, ← Finset.mul_sum, mul_div_assoc]
    · simp
    · simp
    · simp

lemma expValFrom_sum {ι : Type*} (S : Finset ι)
    (A U_low : Finset (Fin n)) (G : SimpleGraph (Fin n))
    (par : ∀ i : Fin m, 0 < i.1 → Fin m) :
    ∀ t (f : ι → (Fin m → Fin n) → ℝ) (ψ : Fin m → Fin n),
      expValFrom A U_low G par t (fun x => ∑ s ∈ S, f s x) ψ =
        ∑ s ∈ S, expValFrom A U_low G par t (f s) ψ := by
  intro t f ψ
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    clear f
    induction t generalizing ψ with
    | zero => rfl
    | succ t ih =>
      dsimp only [expValFrom]
      split_ifs with hr hr0 hne
      · simp_rw [ih, Finset.sum_const_zero, zero_div]
      · rfl
      · rfl
      · rfl
  | insert a S ha ihS =>
    simp only [Finset.sum_insert ha]
    rw [expValFrom_add, ihS]

def ValidPrefix (A U_low : Finset (Fin n)) (G : SimpleGraph (Fin n)) (u : Fin n)
    (hm_pos : 0 < m) (par : ∀ i : Fin m, 0 < i.1 → Fin m)
    (r : ℕ) (ψ : Fin m → Fin n) : Prop :=
  ψ ⟨0, hm_pos⟩ = u ∧
  (∀ j : Fin m, j.1 < r → ψ j ∈ A \ U_low) ∧
  (∀ j₁ j₂ : Fin m, j₁.1 < r → j₂.1 < r → ψ j₁ = ψ j₂ → j₁ = j₂) ∧
  (∀ j : Fin m, j.1 < r → (hj : 0 < j.1) → G.Adj (ψ (par j hj)) (ψ j))

lemma validPrefix_update {A U_low : Finset (Fin n)} {G : SimpleGraph (Fin n)} {u : Fin n}
    {hm_pos : 0 < m} {par : ∀ i : Fin m, 0 < i.1 → Fin m}
    (hpar : ∀ i hi, (par i hi).1 < i.1)
    {r : ℕ} (hr : r < m) (hr0 : 0 < r) {ψ : Fin m → Fin n}
    (hval : ValidPrefix A U_low G u hm_pos par r ψ)
    {v : Fin n} (hv : v ∈ stepCand A U_low G par ψ ⟨r, hr⟩ hr0) :
    ValidPrefix A U_low G u hm_pos par (r + 1) (Function.update ψ ⟨r, hr⟩ v) := by
  rcases hval with ⟨h0, hmem, hinj, hadj⟩
  have hne0 : (⟨0, hm_pos⟩ : Fin m) ≠ ⟨r, hr⟩ := by
    intro h; have := congrArg Fin.val h; dsimp at this; omega
  have hv_mem : v ∈ A \ U_low := by
    refine Finset.mem_sdiff.mpr ⟨(mem_filter.mp (Finset.mem_sdiff.mp hv).1).1, ?_⟩
    intro hu
    exact (Finset.mem_sdiff.mp hv).2 (mem_union_left _ hu)
  have hv_adj : G.Adj (ψ (par ⟨r, hr⟩ hr0)) v := (mem_filter.mp (Finset.mem_sdiff.mp hv).1).2
  have hv_not_im : ∀ j : Fin m, j.1 < r → ψ j ≠ v := by
    intro j hj heq
    apply (Finset.mem_sdiff.mp hv).2
    refine mem_union_right _ (mem_image.mpr ⟨j, mem_filter.mpr ⟨mem_univ _, hj⟩, heq⟩)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rwa [Function.update_of_ne hne0]
  · intro j hj
    by_cases hjr : j.1 < r
    · have hne : j ≠ ⟨r, hr⟩ := fun h => by have := congrArg Fin.val h; dsimp at this; omega
      rw [Function.update_of_ne hne]
      exact hmem j hjr
    · have hj_val : j.1 = r := by omega
      have hj_eq : j = ⟨r, hr⟩ := Fin.ext hj_val
      rw [hj_eq, Function.update_self]
      exact hv_mem
  · intro j₁ j₂ h1 h2 heq
    by_cases hj1 : j₁.1 < r <;> by_cases hj2 : j₂.1 < r
    · have hn1 : j₁ ≠ ⟨r, hr⟩ := fun h => by have := congrArg Fin.val h; dsimp at this; omega
      have hn2 : j₂ ≠ ⟨r, hr⟩ := fun h => by have := congrArg Fin.val h; dsimp at this; omega
      rw [Function.update_of_ne hn1, Function.update_of_ne hn2] at heq
      exact hinj j₁ j₂ hj1 hj2 heq
    · exfalso
      have hn1 : j₁ ≠ ⟨r, hr⟩ := fun h => by have := congrArg Fin.val h; dsimp at this; omega
      have hj2_val : j₂.1 = r := by omega
      have hj2_eq : j₂ = ⟨r, hr⟩ := Fin.ext hj2_val
      rw [Function.update_of_ne hn1, hj2_eq, Function.update_self] at heq
      exact hv_not_im j₁ hj1 heq
    · exfalso
      have hn2 : j₂ ≠ ⟨r, hr⟩ := fun h => by have := congrArg Fin.val h; dsimp at this; omega
      have hj1_val : j₁.1 = r := by omega
      have hj1_eq : j₁ = ⟨r, hr⟩ := Fin.ext hj1_val
      rw [hj1_eq, Function.update_self, Function.update_of_ne hn2] at heq
      exact hv_not_im j₂ hj2 heq.symm
    · exact Fin.ext (by omega)
  · intro j hj hj0
    by_cases hjr : j.1 < r
    · have hn : j ≠ ⟨r, hr⟩ := fun h => by have := congrArg Fin.val h; dsimp at this; omega
      have hpr : (par j hj0).1 < r := (hpar j hj0).trans hjr
      have hnp : par j hj0 ≠ ⟨r, hr⟩ := fun h => by have := congrArg Fin.val h; dsimp at this; omega
      rw [Function.update_of_ne hnp, Function.update_of_ne hn]
      exact hadj j hjr hj0
    · have hj_val : j.1 = r := by omega
      have hj_eq : j = ⟨r, hr⟩ := Fin.ext hj_val
      subst hj_eq
      have hpr : (par ⟨r, hr⟩ hj0).1 < r := hpar ⟨r, hr⟩ hj0
      have hnp : par ⟨r, hr⟩ hj0 ≠ ⟨r, hr⟩ := fun h => by have := congrArg Fin.val h; dsimp at this; omega
      rw [Function.update_of_ne hnp, Function.update_self]
      exact hv_adj

lemma expValFrom_mono (A U_low : Finset (Fin n)) (G : SimpleGraph (Fin n)) (u : Fin n)
    (hm_pos : 0 < m) (par : ∀ i : Fin m, 0 < i.1 → Fin m)
    (hpar : ∀ i hi, (par i hi).1 < i.1)
    (f g : (Fin m → Fin n) → ℝ)
    (hfg : ∀ ψ, ValidPrefix A U_low G u hm_pos par m ψ → f ψ ≤ g ψ) :
    ∀ t r (_hr : r + t = m) (_hr1 : 1 ≤ r) (ψ : Fin m → Fin n),
      ValidPrefix A U_low G u hm_pos par r ψ →
      expValFrom A U_low G par t f ψ ≤ expValFrom A U_low G par t g ψ := by
  intro t
  induction t with
  | zero =>
    intro r hr _ ψ hval
    have hrm : r = m := by omega
    subst hrm
    exact hfg ψ hval
  | succ t ih =>
    intro r hr hr1 ψ hval
    dsimp only [expValFrom]
    have hr_lt : m - (t + 1) < m := by omega
    have hr0 : 0 < m - (t + 1) := by omega
    have h_eq : m - (t + 1) = r := by omega
    rw [dif_pos hr_lt, dif_pos hr0]
    split_ifs with hne
    · refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
      refine Finset.sum_le_sum (fun v hv => ?_)
      have hval' : ValidPrefix A U_low G u hm_pos par (m - (t + 1) + 1)
          (Function.update ψ ⟨m - (t + 1), hr_lt⟩ v) :=
        validPrefix_update hpar hr_lt hr0 (h_eq ▸ hval) hv
      exact ih (m - (t + 1) + 1) (by omega) (by omega) _ hval'
    · exact le_rfl

lemma expValFrom_exists_le (A U_low : Finset (Fin n)) (G : SimpleGraph (Fin n)) (u : Fin n)
    (hm_pos : 0 < m) (par : ∀ i : Fin m, 0 < i.1 → Fin m)
    (hpar : ∀ i hi, (par i hi).1 < i.1)
    (h_ne : ∀ r (hr : r < m) (hr0 : 0 < r) ψ,
      ValidPrefix A U_low G u hm_pos par r ψ →
      (stepCand A U_low G par ψ ⟨r, hr⟩ hr0).Nonempty)
    (f : (Fin m → Fin n) → ℝ) :
    ∀ t r (_hr : r + t = m) (_hr1 : 1 ≤ r) (ψ : Fin m → Fin n),
      ValidPrefix A U_low G u hm_pos par r ψ →
      ∃ ψ', ValidPrefix A U_low G u hm_pos par m ψ' ∧ f ψ' ≤ expValFrom A U_low G par t f ψ := by
  intro t
  induction t with
  | zero =>
    intro r hr _ ψ hval
    have hrm : r = m := by omega
    subst hrm
    exact ⟨ψ, hval, le_rfl⟩
  | succ t ih =>
    intro r hr hr1 ψ hval
    have hr_lt : m - (t + 1) < m := by omega
    have hr0 : 0 < m - (t + 1) := by omega
    have h_eq : m - (t + 1) = r := by omega
    have hval_r : ValidPrefix A U_low G u hm_pos par (m - (t + 1)) ψ := h_eq ▸ hval
    have hne := h_ne (m - (t + 1)) hr_lt hr0 ψ hval_r
    let C := stepCand A U_low G par ψ ⟨m - (t + 1), hr_lt⟩ hr0
    have h_avg_eq : expValFrom A U_low G par (t + 1) f ψ =
        (∑ v ∈ C, expValFrom A U_low G par t f (Function.update ψ ⟨m - (t + 1), hr_lt⟩ v)) / (C.card : ℝ) := by
      dsimp only [expValFrom]
      rw [dif_pos hr_lt, dif_pos hr0, if_pos hne]
    obtain ⟨v₀, hv₀, hv₀_le⟩ : ∃ v₀ ∈ C,
        expValFrom A U_low G par t f (Function.update ψ ⟨m - (t + 1), hr_lt⟩ v₀) ≤
        (∑ v ∈ C, expValFrom A U_low G par t f (Function.update ψ ⟨m - (t + 1), hr_lt⟩ v)) / (C.card : ℝ) := by
      by_contra hall
      push Not at hall
      have hC_pos : (0 : ℝ) < C.card := Nat.cast_pos.mpr (Finset.card_pos.mpr hne)
      have h_sum_gt : (∑ v ∈ C, (∑ w ∈ C, expValFrom A U_low G par t f
          (Function.update ψ ⟨m - (t + 1), hr_lt⟩ w)) / (C.card : ℝ)) <
          ∑ v ∈ C, expValFrom A U_low G par t f (Function.update ψ ⟨m - (t + 1), hr_lt⟩ v) :=
        Finset.sum_lt_sum_of_nonempty hne (fun v hv => hall v hv)
      rw [Finset.sum_const, nsmul_eq_mul, mul_div_cancel₀ _ hC_pos.ne'] at h_sum_gt
      exact lt_irrefl _ h_sum_gt
    have hval' := validPrefix_update hpar hr_lt hr0 hval_r hv₀
    obtain ⟨ψ', hψ'_val, hψ'_le⟩ := ih (m - (t + 1) + 1) (by omega) (by omega) _ hval'
    exact ⟨ψ', hψ'_val, hψ'_le.trans (hv₀_le.trans_eq h_avg_eq.symm)⟩

lemma expValFrom_mgf_telescope (A U_low : Finset (Fin n)) (G : SimpleGraph (Fin n)) (u : Fin n)
    (hm_pos : 0 < m) (par : ∀ i : Fin m, 0 < i.1 → Fin m)
    (hpar : ∀ i hi, (par i hi).1 < i.1)
    (h_ne : ∀ r (hr : r < m) (hr0 : 0 < r) ψ,
      ValidPrefix A U_low G u hm_pos par r ψ →
      (stepCand A U_low G par ψ ⟨r, hr⟩ hr0).Nonempty)
    (M : ℕ → (Fin m → Fin n) → ℝ) (factor : ℕ → ℝ)
    (hf_nonneg : ∀ r, 0 ≤ factor r)
    (r₀ : ℕ) (hr₀ : 1 ≤ r₀)
    (h_step : ∀ r (hr : r < m) (hr0 : r₀ ≤ r) ψ,
      ValidPrefix A U_low G u hm_pos par r ψ →
      (∑ v ∈ stepCand A U_low G par ψ ⟨r, hr⟩ (Nat.lt_of_lt_of_le hr₀ hr0),
        M (r + 1) (Function.update ψ ⟨r, hr⟩ v)) /
        ((stepCand A U_low G par ψ ⟨r, hr⟩ (Nat.lt_of_lt_of_le hr₀ hr0)).card : ℝ) ≤ M r ψ * factor r) :
    ∀ t r (_hr : r + t = m) (_hr_ge : r₀ ≤ r) (ψ : Fin m → Fin n),
      ValidPrefix A U_low G u hm_pos par r ψ →
      expValFrom A U_low G par t (M m) ψ ≤ M r ψ * ∏ j ∈ Finset.Ico r m, factor j := by
  intro t
  induction t with
  | zero =>
    intro r hr _ ψ _
    have hrm : r = m := by omega
    subst hrm
    simp [expValFrom]
  | succ t ih =>
    intro r hr hr_ge ψ hval
    have hr_lt : m - (t + 1) < m := by omega
    have hr0 : 0 < m - (t + 1) := by omega
    have h_eq : m - (t + 1) = r := by omega
    have hval_r : ValidPrefix A U_low G u hm_pos par (m - (t + 1)) ψ := h_eq ▸ hval
    have hne := h_ne (m - (t + 1)) hr_lt hr0 ψ hval_r
    let C := stepCand A U_low G par ψ ⟨m - (t + 1), hr_lt⟩ hr0
    have h_avg_eq : expValFrom A U_low G par (t + 1) (M m) ψ =
        (∑ v ∈ C, expValFrom A U_low G par t (M m) (Function.update ψ ⟨m - (t + 1), hr_lt⟩ v)) / (C.card : ℝ) := by
      dsimp only [expValFrom]
      rw [dif_pos hr_lt, dif_pos hr0, if_pos hne]
    rw [h_avg_eq]
    have h_prod_nonneg : 0 ≤ ∏ j ∈ Finset.Ico (r + 1) m, factor j :=
      Finset.prod_nonneg (fun j _ => hf_nonneg j)
    have h_sum_le : (∑ v ∈ C, expValFrom A U_low G par t (M m) (Function.update ψ ⟨m - (t + 1), hr_lt⟩ v)) / (C.card : ℝ) ≤
        (∑ v ∈ C, M (r + 1) (Function.update ψ ⟨m - (t + 1), hr_lt⟩ v) * ∏ j ∈ Finset.Ico (r + 1) m, factor j) / (C.card : ℝ) := by
      refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
      refine Finset.sum_le_sum (fun v hv => ?_)
      have hval' : ValidPrefix A U_low G u hm_pos par (m - (t + 1) + 1)
          (Function.update ψ ⟨m - (t + 1), hr_lt⟩ v) :=
        validPrefix_update hpar hr_lt hr0 hval_r hv
      have h_ih := ih (m - (t + 1) + 1) (by omega) (by omega) _ hval'
      simpa [h_eq] using h_ih
    have h_factor_out : (∑ v ∈ C, M (r + 1) (Function.update ψ ⟨m - (t + 1), hr_lt⟩ v) *
        ∏ j ∈ Finset.Ico (r + 1) m, factor j) / (C.card : ℝ) =
        ((∑ v ∈ C, M (r + 1) (Function.update ψ ⟨m - (t + 1), hr_lt⟩ v)) / (C.card : ℝ)) *
        ∏ j ∈ Finset.Ico (r + 1) m, factor j := by
      rw [← Finset.sum_mul, div_mul_eq_mul_div]
    have h_step_r := h_step r (by omega) hr_ge ψ hval
    have h_C_eq : (⟨m - (t + 1), hr_lt⟩ : Fin m) = ⟨r, by omega⟩ := Fin.ext h_eq
    have h_step_r'' : (∑ v ∈ C, M (r + 1) (Function.update ψ ⟨m - (t + 1), hr_lt⟩ v)) / (C.card : ℝ) ≤ M r ψ * factor r := by
      dsimp only [C]
      simpa only [h_C_eq] using h_step_r
    have h_prod_split : factor r * ∏ j ∈ Finset.Ico (r + 1) m, factor j = ∏ j ∈ Finset.Ico r m, factor j := by
      exact (Finset.prod_eq_prod_Ico_succ_bot (by omega : r < m) factor).symm
    calc (∑ v ∈ C, expValFrom A U_low G par t (M m) (Function.update ψ ⟨m - (t + 1), hr_lt⟩ v)) / (C.card : ℝ)
        ≤ ((∑ v ∈ C, M (r + 1) (Function.update ψ ⟨m - (t + 1), hr_lt⟩ v)) / (C.card : ℝ)) *
          ∏ j ∈ Finset.Ico (r + 1) m, factor j := h_sum_le.trans_eq h_factor_out
      _ ≤ (M r ψ * factor r) * ∏ j ∈ Finset.Ico (r + 1) m, factor j :=
          mul_le_mul_of_nonneg_right h_step_r'' h_prod_nonneg
      _ = M r ψ * (factor r * ∏ j ∈ Finset.Ico (r + 1) m, factor j) := mul_assoc _ _ _
      _ = M r ψ * ∏ j ∈ Finset.Ico r m, factor j := by rw [h_prod_split]

end RandomGreedy

/- Branch B (`d < μ * k`) via Claim 5.2 and Hall's Marriage Theorem -/

section BranchBHelpers

noncomputable def ImFinset {n m : ℕ} (r : ℕ) (ψ : Fin m → Fin n) : Finset (Fin n) :=
  (Finset.univ.filter (fun j : Fin m => j.1 < r)).image ψ

lemma imFinset_update_of_le {n m : ℕ} {r : ℕ} {ψ : Fin m → Fin n} {i₀ : Fin m} {v : Fin n}
    (hri : r ≤ i₀.1) :
    ImFinset r (Function.update ψ i₀ v) = ImFinset r ψ := by
  refine Finset.image_congr (fun j hj => ?_)
  have hj_lt : j.1 < r := (mem_filter.mp hj).2
  have hne : j ≠ i₀ := fun heq => by rw [heq] at hj_lt; omega
  exact Function.update_of_ne hne v ψ

lemma imFinset_succ_update {n m : ℕ} {r : ℕ} (hr : r < m) (ψ : Fin m → Fin n) (v : Fin n) :
    ImFinset (r + 1) (Function.update ψ ⟨r, hr⟩ v) = insert v (ImFinset r ψ) := by
  ext w
  simp only [ImFinset, mem_image, mem_filter, mem_univ, true_and, mem_insert]
  constructor
  · rintro ⟨j, hj, rfl⟩
    by_cases hjr : j.1 < r
    · have hne : j ≠ ⟨r, hr⟩ := fun h => by have := congrArg Fin.val h; dsimp at this; omega
      rw [Function.update_of_ne hne]
      exact Or.inr ⟨j, hjr, rfl⟩
    · have hj_val : j.1 = r := by omega
      have hj_eq : j = ⟨r, hr⟩ := Fin.ext hj_val
      rw [hj_eq, Function.update_self]
      exact Or.inl rfl
  · rintro (rfl | ⟨j, hj, rfl⟩)
    · exact ⟨⟨r, hr⟩, Nat.lt_succ_self r, Function.update_self _ _ _⟩
    · have hne : j ≠ ⟨r, hr⟩ := fun h => by have := congrArg Fin.val h; dsimp at this; omega
      exact ⟨j, by omega, Function.update_of_ne hne _ _⟩

lemma imFinset_card_le {n m : ℕ} (r : ℕ) (ψ : Fin m → Fin n) :
    (ImFinset r ψ).card ≤ r := by
  refine Finset.card_image_le.trans ?_
  by_cases hr0 : r = 0
  · subst hr0; simp
  · have hr_pos : 0 < r := Nat.pos_of_ne_zero hr0
    have h_inj : (Finset.univ.filter (fun j : Fin m => j.1 < r)).card ≤ (Finset.univ : Finset (Fin r)).card := by
      refine card_le_card_of_injOn (fun j : Fin m => (⟨j.1 % r, Nat.mod_lt _ hr_pos⟩ : Fin r)) ?_ ?_
      · intro j _; exact mem_univ _
      · intro j₁ hj₁ j₂ hj₂ h
        have h1 : j₁.1 < r := (mem_filter.mp hj₁).2
        have h2 : j₂.1 < r := (mem_filter.mp hj₂).2
        have hv : j₁.1 % r = j₂.1 % r := congrArg Fin.val h
        rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at hv
        exact Fin.ext hv
    exact h_inj.trans (by rw [card_fin])

lemma imFinset_card_eq {n m : ℕ} {A U_low : Finset (Fin n)} {G : SimpleGraph (Fin n)} {u : Fin n}
    {hm_pos : 0 < m} {par : ∀ i : Fin m, 0 < i.1 → Fin m}
    {r : ℕ} (hr : r ≤ m) {ψ : Fin m → Fin n}
    (hval : ValidPrefix A U_low G u hm_pos par r ψ) :
    (ImFinset r ψ).card = r ∧ ImFinset r ψ ⊆ A := by
  rcases hval with ⟨_, hmem, hinj, _⟩
  refine ⟨?_, ?_⟩
  · rw [ImFinset, Finset.card_image_of_injOn (fun j₁ hj₁ j₂ hj₂ heq =>
      hinj j₁ j₂ (mem_filter.mp hj₁).2 (mem_filter.mp hj₂).2 heq)]
    have h_bij : (Finset.univ.filter (fun j : Fin m => j.1 < r)).card = (Finset.univ : Finset (Fin r)).card := by
      refine Finset.card_bij (fun j hj => (⟨j.1, (mem_filter.mp hj).2⟩ : Fin r)) ?_ ?_ ?_
      · intro _ _; exact mem_univ _
      · intro j₁ _ j₂ _ h; exact Fin.ext (congrArg (Fin.val : Fin r → ℕ) h)
      · intro b _; exact ⟨⟨b.1, lt_of_lt_of_le b.2 hr⟩, mem_filter.mpr ⟨mem_univ _, b.2⟩, Fin.ext rfl⟩
    rw [h_bij, card_fin]
  · intro w hw
    rcases mem_image.mp hw with ⟨j, hj, rfl⟩
    exact (Finset.mem_sdiff.mp (hmem j (mem_filter.mp hj).2)).1

noncomputable def Rseq {n m : ℕ} (Y : ℕ → (Fin m → Fin n) → ℝ) (thresh : ℝ) (i₀ : ℕ) :
    ℕ → (Fin m → Fin n) → ℝ
  | 0, ψ => Y i₀ ψ
  | t + 1, ψ => if Rseq Y thresh i₀ t ψ ≤ thresh then Y (i₀ + t + 1) ψ else Rseq Y thresh i₀ t ψ

lemma rseq_le_imp {n m : ℕ} (Y : ℕ → (Fin m → Fin n) → ℝ) (thresh : ℝ) (i₀ : ℕ) :
    ∀ t ψ, Rseq Y thresh i₀ t ψ ≤ thresh →
      Rseq Y thresh i₀ t ψ = Y (i₀ + t) ψ ∧ ∀ s ≤ t, Y (i₀ + s) ψ ≤ thresh := by
  intro t
  induction t with
  | zero =>
    intro ψ h
    exact ⟨rfl, fun s hs => by
      have : s = 0 := by omega
      subst this
      exact h⟩
  | succ t ih =>
    intro ψ h
    dsimp only [Rseq] at h ⊢
    by_cases hprev : Rseq Y thresh i₀ t ψ ≤ thresh
    · rw [if_pos hprev] at h ⊢
      obtain ⟨_, h_all⟩ := ih ψ hprev
      refine ⟨by ring_nf, fun s hs => ?_⟩
      by_cases hst : s ≤ t
      · exact h_all s hst
      · have hs_eq : s = t + 1 := by omega
        subst hs_eq
        simpa [add_assoc] using h
    · rw [if_neg hprev] at h
      exact absurd h hprev

lemma rseq_of_forall_le {n m : ℕ} (Y : ℕ → (Fin m → Fin n) → ℝ) (thresh : ℝ) (i₀ : ℕ) :
    ∀ t ψ, (∀ s ≤ t, Y (i₀ + s) ψ ≤ thresh) → Rseq Y thresh i₀ t ψ = Y (i₀ + t) ψ := by
  intro t
  induction t with
  | zero => intro ψ _; rfl
  | succ t ih =>
    intro ψ h_all
    dsimp only [Rseq]
    have h_t : Rseq Y thresh i₀ t ψ = Y (i₀ + t) ψ := ih ψ (fun s hs => h_all s (by omega))
    have h_le : Rseq Y thresh i₀ t ψ ≤ thresh := h_t ▸ h_all t (Nat.le_succ t)
    rw [if_pos h_le, add_assoc]

lemma rseq_update_of_le {n m : ℕ} (Y : ℕ → (Fin m → Fin n) → ℝ) (thresh : ℝ) (i₀ : ℕ) :
    ∀ t (ψ : Fin m → Fin n) (i : Fin m) (v : Fin n),
      (∀ r ≤ i₀ + t, Y r (Function.update ψ i v) = Y r ψ) →
      Rseq Y thresh i₀ t (Function.update ψ i v) = Rseq Y thresh i₀ t ψ := by
  intro t
  induction t with
  | zero => intro ψ i v hY; exact hY i₀ (by omega)
  | succ t ih =>
    intro ψ i v hY
    dsimp only [Rseq]
    have h_prev := ih ψ i v (fun r hr => hY r (by omega))
    rw [h_prev, hY (i₀ + t + 1) (by omega)]

end BranchBHelpers

lemma param_bounds {L n k r : ℕ} (hL : 2 ≤ L)
    (hn_ge : 10 ^ 105 * L ^ 18 ≤ n)
    (hDr : 10 ^ 28 * L ^ 4 * r ≤ n)
    (_hk_le : k ≤ n) (hkr : n < k + r) :
    let μ : ℝ := 1 / (10 ^ 12 * (L : ℝ) ^ 2)
    let s : ℕ := k / (2 * L)
    n ≤ 2 * k ∧
    10 ^ 104 * L ^ 18 ≤ k ∧
    0 < k ∧
    99 * (n : ℝ) ≤ 100 * k ∧
    (r : ℝ) ≤ n / (10 ^ 28 * (L : ℝ) ^ 4) ∧
    (k : ℝ) / (3 * L) ≤ s ∧
    (s : ℝ) ≤ k / (2 * L) ∧
    0 < s ∧
    (10 ^ 90 : ℝ) ≤ μ * k ∧
    μ * k ≤ (s : ℝ) / 100 := by
  intro μ s
  have hL_pos : 0 < L := by omega
  have hL4_pos : 1 ≤ L ^ 4 := Nat.one_le_pow 4 L hL_pos
  have hL18_pos : 1 ≤ L ^ 18 := Nat.one_le_pow 18 L hL_pos
  have h_r_le_n : 10 ^ 28 * r ≤ n := by
    have h1 : 10 ^ 28 * r ≤ 10 ^ 28 * L ^ 4 * r := by nlinarith
    exact h1.trans hDr
  have hk_ge_n2 : n ≤ 2 * k := by omega
  have hk_ge_big : 10 ^ 104 * L ^ 18 ≤ k := by omega
  have hk_pos : 0 < k := by
    have h_pos : 0 < 10 ^ 104 * L ^ 18 := Nat.mul_pos (by positivity) hL18_pos
    exact lt_of_lt_of_le h_pos hk_ge_big
  have hL_R : (2 : ℝ) ≤ L := by exact_mod_cast hL
  have hL4R : (1 : ℝ) ≤ (L : ℝ) ^ 4 := by exact_mod_cast hL4_pos
  have hr_le_nD : (r : ℝ) ≤ (n : ℝ) / (10 ^ 28 * (L : ℝ) ^ 4) := by
    have h1 : (10 ^ 28 * (L : ℝ) ^ 4) * r ≤ n := by exact_mod_cast hDr
    rw [le_div_iff₀ (by positivity)]
    linarith
  have h_kn99 : 99 * (n : ℝ) ≤ 100 * k := by
    have h1 : (n : ℝ) < k + r := by exact_mod_cast hkr
    have h2 : (r : ℝ) ≤ n / 100 := by
      have h3 : 100 * (r : ℝ) ≤ 10 ^ 28 * (L : ℝ) ^ 4 * r := by nlinarith
      have h4 : (10 ^ 28 * (L : ℝ) ^ 4 * r : ℝ) ≤ n := by exact_mod_cast hDr
      linarith
    linarith
  have hk_R : (10 ^ 104 * (L : ℝ) ^ 18) ≤ k := by exact_mod_cast hk_ge_big
  have h2L_le_k : 2 * L ≤ k := by
    have h1 : 2 * L ≤ 10 ^ 104 * L ^ 18 := by
      have : L ≤ L ^ 18 := Nat.le_self_pow (by omega : 18 ≠ 0) L
      nlinarith
    exact h1.trans hk_ge_big
  have hs_lower : (k : ℝ) / (3 * L) ≤ s := by
    have h_div : k - 2 * L ≤ (k / (2 * L)) * (2 * L) := by
      have hdm := Nat.div_add_mod k (2 * L)
      have hml := Nat.mod_lt k (by omega : 0 < 2 * L)
      have h_comm : 2 * L * (k / (2 * L)) = (k / (2 * L)) * (2 * L) := mul_comm _ _
      omega
    have h_divR : (k : ℝ) - 2 * L ≤ (s : ℝ) * (2 * L) := by
      have h1 : ((k - 2 * L : ℕ) : ℝ) ≤ ((k / (2 * L) * (2 * L) : ℕ) : ℝ) := by
        exact_mod_cast h_div
      rw [Nat.cast_sub h2L_le_k, Nat.cast_mul, Nat.cast_mul] at h1
      simpa [s] using h1
    have hk_6L : (6 : ℝ) * L ≤ k := by
      have : L ≤ (L : ℝ) ^ 18 := by exact_mod_cast Nat.le_self_pow (by omega : 18 ≠ 0) L
      nlinarith
    have h_mul : (k : ℝ) / (3 * L) * (2 * L) ≤ (s : ℝ) * (2 * L) := by
      have h_eq : (k : ℝ) / (3 * L) * (2 * L) = 2 * k / 3 := by field_simp
      rw [h_eq]
      linarith
    exact le_of_mul_le_mul_right h_mul (by positivity)
  have hs_upper : (s : ℝ) ≤ k / (2 * L) := by
    have h_div : (k / (2 * L)) * (2 * L) ≤ k := Nat.div_mul_le_self k (2 * L)
    have h_divR : (s : ℝ) * (2 * L) ≤ k := by exact_mod_cast h_div
    rw [le_div_iff₀ (by positivity)]
    exact h_divR
  have hs_pos : 0 < s := by
    have : (0 : ℝ) < s := lt_of_lt_of_le (by positivity) hs_lower
    exact_mod_cast this
  have h_μk_ge : (10 ^ 90 : ℝ) ≤ μ * k := by
    have h1 : (10 ^ 104 * (L : ℝ) ^ 18) / (10 ^ 12 * (L : ℝ) ^ 2) ≤ k / (10 ^ 12 * (L : ℝ) ^ 2) :=
      div_le_div_of_nonneg_right hk_R (by positivity)
    have h2 : (10 ^ 92 : ℝ) * (L : ℝ) ^ 16 = (10 ^ 104 * (L : ℝ) ^ 18) / (10 ^ 12 * (L : ℝ) ^ 2) := by
      field_simp
    have hL16 : (1 : ℝ) ≤ (L : ℝ) ^ 16 := one_le_pow₀ (by linarith)
    have h_eq : μ * k = k / (10 ^ 12 * (L : ℝ) ^ 2) := by dsimp only [μ]; ring
    rw [h_eq]
    nlinarith
  have h_μk_le_s : μ * k ≤ (s : ℝ) / 100 := by
    have h_s_100 : (k : ℝ) / (300 * L) ≤ (s : ℝ) / 100 := by
      have h_eq : (k : ℝ) / (300 * L) = ((k : ℝ) / (3 * L)) / 100 := by ring
      rw [h_eq]
      exact div_le_div_of_nonneg_right hs_lower (by norm_num)
    have h_cmp : μ * k ≤ k / (300 * L) := by
      have h_eq : μ * k = k / (10 ^ 12 * (L : ℝ) ^ 2) := by dsimp only [μ]; ring
      rw [h_eq]
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      nlinarith
    exact h_cmp.trans h_s_100
  exact ⟨hk_ge_n2, hk_ge_big, hk_pos, h_kn99, hr_le_nD, hs_lower, hs_upper, hs_pos, h_μk_ge, h_μk_le_s⟩

lemma cand_bounds_of_valid {n k m s : ℕ} {μ : ℝ} (hs_pos : 0 < s) (h_μk_le_s : μ * k ≤ (s : ℝ) / 100)
    (hm_eq : m = k - s) {G : SimpleGraph (Fin n)} {u : Fin n}
    {A U_low : Finset (Fin n)} (hA : A.card = k)
    (hU_deg : ∀ v ∈ A \ U_low, ((A.filter (G.Adj v)).card : ℝ) ≥ (1 - μ / 10) * k)
    (hU_card : (U_low.card : ℝ) ≤ μ * k / 10)
    (hm_pos : 0 < m) (par : ∀ i : Fin m, 0 < i.1 → Fin m) (hpar : ∀ i hi, (par i hi).1 < i.1)
    {r' : ℕ} (hr' : r' < m) (hr0' : 0 < r') {ψ : Fin m → Fin n}
    (hval : ValidPrefix A U_low G u hm_pos par r' ψ) :
    let C := stepCand A U_low G par ψ ⟨r', hr'⟩ hr0'
    ((k - r' : ℝ) - μ * k / 5 ≤ C.card) ∧ (C.card ≤ k - r') ∧ C.Nonempty := by
  intro C
  obtain ⟨hIm_card, hIm_sub⟩ := imFinset_card_eq hr'.le hval
  have hC_sub : C ⊆ A \ ImFinset r' ψ := by
    intro w hw
    have hw' := Finset.mem_sdiff.mp hw
    refine Finset.mem_sdiff.mpr ⟨(mem_filter.mp hw'.1).1, ?_⟩
    intro him
    exact hw'.2 (mem_union_right _ him)
  have hC_upper : C.card ≤ k - r' := by
    have h1 := card_le_card hC_sub
    rw [card_sdiff_of_subset hIm_sub, hA, hIm_card] at h1
    exact h1
  have hp_mem : ψ (par ⟨r', hr'⟩ hr0') ∈ A \ U_low := hval.2.1 _ (hpar ⟨r', hr'⟩ hr0')
  have h_adj_card : (1 - μ / 10) * k ≤ ((A.filter (G.Adj (ψ (par ⟨r', hr'⟩ hr0')))).card : ℝ) :=
    hU_deg _ hp_mem
  have h_sdiff_ge : (A.filter (G.Adj (ψ (par ⟨r', hr'⟩ hr0')))).card ≤
      C.card + U_low.card + (ImFinset r' ψ).card := by
    have h1 : (A.filter (G.Adj (ψ (par ⟨r', hr'⟩ hr0')))).card ≤
        C.card + (U_low ∪ ImFinset r' ψ).card := card_le_card_sdiff_add_card
    have h2 := card_union_le U_low (ImFinset r' ψ)
    omega
  have hC_lower : (k - r' : ℝ) - μ * k / 5 ≤ C.card := by
    have h_sdiffR : ((A.filter (G.Adj (ψ (par ⟨r', hr'⟩ hr0')))).card : ℝ) ≤
        C.card + U_low.card + (ImFinset r' ψ).card := by exact_mod_cast h_sdiff_ge
    rw [hIm_card] at h_sdiffR
    linarith
  have hkr_ge_s : (s : ℝ) ≤ k - r' := by
    have : r' + s ≤ k := by omega
    have : (r' : ℝ) + s ≤ k := by exact_mod_cast this
    linarith
  have hs_R : (0 : ℝ) < s := Nat.cast_pos.mpr hs_pos
  have hC_pos : (0 : ℝ) < C.card := by linarith
  have hC_ne : C.Nonempty := Finset.card_pos.mp (by exact_mod_cast hC_pos)
  exact ⟨hC_lower, hC_upper, hC_ne⟩

noncomputable def XVal {n m : ℕ} (A U_low : Finset (Fin n)) (G : SimpleGraph (Fin n))
    (v₀ : Fin n) (k : ℕ) (d_seq : Fin m → ℕ) (i : Fin m) (ψ : Fin m → Fin n) : ℝ :=
  if G.Adj v₀ (ψ i) ∨
    (((A.filter (G.Adj v₀)) \ (U_low ∪ ImFinset i.1 ψ)).card : ℝ) ≤ (k - i.1 : ℝ) / 25
  then (d_seq i : ℝ) else 0

noncomputable def MX {n m : ℕ} (A U_low : Finset (Fin n)) (G : SimpleGraph (Fin n))
    (v₀ : Fin n) (k : ℕ) (d_seq : Fin m → ℕ) (θ_X : ℝ) (r' : ℕ) (ψ : Fin m → Fin n) : ℝ :=
  Real.exp (-θ_X * ∑ i ∈ Finset.univ.filter (fun i : Fin m => i.1 < r'),
    (XVal A U_low G v₀ k d_seq i ψ - (d_seq i : ℝ) / 50))

noncomputable def FactorX {m : ℕ} (d_seq : Fin m → ℕ) (θ_X : ℝ) (r' : ℕ) : ℝ :=
  if hr' : r' < m then Real.exp ((θ_X * d_seq ⟨r', hr'⟩) ^ 2) else 1

lemma xVal_update_of_lt {n m : ℕ} (A U_low : Finset (Fin n)) (G : SimpleGraph (Fin n))
    (v₀ : Fin n) (k : ℕ) (d_seq : Fin m → ℕ)
    (j i : Fin m) (ψ : Fin m → Fin n) (v : Fin n) (hji : j.1 < i.1) :
    XVal A U_low G v₀ k d_seq j (Function.update ψ i v) = XVal A U_low G v₀ k d_seq j ψ := by
  have hne : j ≠ i := fun h => by rw [h] at hji; omega
  simp only [XVal, Function.update_of_ne hne, imFinset_update_of_le hji.le]

lemma mgf_X_step {k m s d : ℕ} {μ : ℝ} (_hμ_pos : 0 < μ)
    (hs_pos : 0 < s) (hm_eq : m = k - s) (hm_pos : 0 < m)
    (hd_pos : 1 ≤ d) (h_μk_le_s : μ * k ≤ (s : ℝ) / 100)
    {n : ℕ} {G : SimpleGraph (Fin n)} {u : Fin n} {A U_low : Finset (Fin n)}
    (hA : A.card = k) (hU_deg : ∀ v ∈ A \ U_low, ((A.filter (G.Adj v)).card : ℝ) ≥ (1 - μ / 10) * k)
    (hU_card : (U_low.card : ℝ) ≤ μ * k / 10)
    (par : ∀ i : Fin m, 0 < i.1 → Fin m) (hpar : ∀ i hi, (par i hi).1 < i.1)
    (d_seq : Fin m → ℕ) (hd_le : ∀ i, d_seq i ≤ d) (v₀ : Fin n) :
    let θ_X : ℝ := 1 / (400 * d : ℝ)
    ∀ r' (hr' : r' < m) (hr0' : 1 ≤ r') ψ,
      ValidPrefix A U_low G u hm_pos par r' ψ →
      (∑ v ∈ stepCand A U_low G par ψ ⟨r', hr'⟩ (Nat.lt_of_lt_of_le (by norm_num) hr0'),
        MX A U_low G v₀ k d_seq θ_X (r' + 1) (Function.update ψ ⟨r', hr'⟩ v)) /
        ((stepCand A U_low G par ψ ⟨r', hr'⟩ (Nat.lt_of_lt_of_le (by norm_num) hr0')).card : ℝ) ≤
      MX A U_low G v₀ k d_seq θ_X r' ψ * FactorX d_seq θ_X r' := by
  intro θ_X r' hr' hr0' ψ hval
  have hθ_pos : 0 < θ_X := by positivity
  set C := stepCand A U_low G par ψ ⟨r', hr'⟩ (Nat.lt_of_lt_of_le (by norm_num) hr0')
  have h_C_b := cand_bounds_of_valid hs_pos h_μk_le_s hm_eq hA hU_deg hU_card hm_pos par hpar
    hr' (Nat.lt_of_lt_of_le (by norm_num) hr0') hval
  have hC_pos : (0 : ℝ) < C.card := Nat.cast_pos.mpr (Finset.card_pos.mpr h_C_b.2.2)
  let i₀ : Fin m := ⟨r', hr'⟩
  have h_filter_split : Finset.univ.filter (fun i : Fin m => i.1 < r' + 1) =
      insert i₀ (Finset.univ.filter (fun i : Fin m => i.1 < r')) := by
    ext i; simp only [mem_filter, mem_univ, true_and, mem_insert, Fin.ext_iff]; dsimp [i₀]; omega
  have hi₀_not_mem : i₀ ∉ Finset.univ.filter (fun i : Fin m => i.1 < r') := by
    intro h; have := (mem_filter.mp h).2; dsimp [i₀] at this; omega
  have h_M_split : ∀ v : Fin n,
      MX A U_low G v₀ k d_seq θ_X (r' + 1) (Function.update ψ i₀ v) =
      MX A U_low G v₀ k d_seq θ_X r' ψ *
        Real.exp (-θ_X * (XVal A U_low G v₀ k d_seq i₀ (Function.update ψ i₀ v) - (d_seq i₀ : ℝ) / 50)) := by
    intro v
    dsimp only [MX]
    rw [h_filter_split, Finset.sum_insert hi₀_not_mem]
    have h_sum_eq : ∑ i ∈ Finset.univ.filter (fun i : Fin m => i.1 < r'),
        (XVal A U_low G v₀ k d_seq i (Function.update ψ i₀ v) - (d_seq i : ℝ) / 50) =
        ∑ i ∈ Finset.univ.filter (fun i : Fin m => i.1 < r'),
          (XVal A U_low G v₀ k d_seq i ψ - (d_seq i : ℝ) / 50) :=
      Finset.sum_congr rfl (fun j hj => by rw [xVal_update_of_lt _ _ _ _ _ _ j i₀ ψ v (mem_filter.mp hj).2])
    rw [h_sum_eq, mul_add, Real.exp_add, mul_comm (Real.exp _)]
  change (∑ v ∈ C, MX A U_low G v₀ k d_seq θ_X (r' + 1) (Function.update ψ i₀ v)) / (C.card : ℝ) ≤
    MX A U_low G v₀ k d_seq θ_X r' ψ * FactorX d_seq θ_X r'
  simp_rw [h_M_split]
  rw [← Finset.mul_sum, mul_div_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  rw [show FactorX d_seq θ_X r' = Real.exp ((θ_X * d_seq i₀) ^ 2) from dif_pos hr']
  let z : ℝ := θ_X * d_seq i₀
  have hz0 : 0 ≤ z := by positivity
  have hz_le : z ≤ 1 / 400 := by
    have hd_i : (d_seq i₀ : ℝ) ≤ d := by exact_mod_cast hd_le i₀
    have hd_p : (0 : ℝ) < d := by exact_mod_cast hd_pos
    dsimp only [z, θ_X]
    rw [one_div_mul_eq_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have h_im_eq : ∀ v : Fin n, ImFinset r' (Function.update ψ i₀ v) = ImFinset r' ψ := fun v =>
    imFinset_update_of_le (i₀ := i₀) (by dsimp [i₀]; exact le_refl r')
  by_cases h_small : (((A.filter (G.Adj v₀)) \ (U_low ∪ ImFinset r' ψ)).card : ℝ) ≤ (k - r' : ℝ) / 25
  · have h_all_eq : ∀ v ∈ C, XVal A U_low G v₀ k d_seq i₀ (Function.update ψ i₀ v) = (d_seq i₀ : ℝ) := by
      intro v _
      dsimp only [XVal]
      rw [if_pos (Or.inr (by dsimp [i₀]; rw [h_im_eq v]; exact h_small))]
    have h_sum_c : (∑ v ∈ C, Real.exp (-θ_X * (XVal A U_low G v₀ k d_seq i₀ (Function.update ψ i₀ v) - (d_seq i₀ : ℝ) / 50))) / C.card =
        Real.exp (-49 / 50 * z) := by
      have h_eq : ∀ v ∈ C, Real.exp (-θ_X * (XVal A U_low G v₀ k d_seq i₀ (Function.update ψ i₀ v) - (d_seq i₀ : ℝ) / 50)) =
          Real.exp (-49 / 50 * z) := fun v hv => by rw [h_all_eq v hv]; congr 1; dsimp only [z]; ring
      rw [Finset.sum_congr rfl h_eq, Finset.sum_const, nsmul_eq_mul, mul_div_cancel_left₀ _ hC_pos.ne']
    rw [h_sum_c]
    exact Real.exp_le_exp.mpr (by nlinarith)
  · push Not at h_small
    let C₁ := C.filter (G.Adj v₀)
    let C₀ := C.filter (fun v => ¬ G.Adj v₀ v)
    have h_C_split : C.card = C₁.card + C₀.card := (Finset.card_filter_add_card_filter_not (s := C) (p := G.Adj v₀)).symm
    have h_val_C1 : ∀ v ∈ C₁, Real.exp (-θ_X * (XVal A U_low G v₀ k d_seq i₀ (Function.update ψ i₀ v) - (d_seq i₀ : ℝ) / 50)) =
        Real.exp (-49 / 50 * z) := by
      intro v hv
      have hadj : G.Adj v₀ v := (mem_filter.mp hv).2
      have hX_eq : XVal A U_low G v₀ k d_seq i₀ (Function.update ψ i₀ v) = d_seq i₀ := by
        dsimp only [XVal]; rw [if_pos (Or.inl (by simp [Function.update_self, hadj]))]
      rw [hX_eq]; congr 1; dsimp only [z]; ring
    have h_val_C0 : ∀ v ∈ C₀, Real.exp (-θ_X * (XVal A U_low G v₀ k d_seq i₀ (Function.update ψ i₀ v) - (d_seq i₀ : ℝ) / 50)) =
        Real.exp (1 / 50 * z) := by
      intro v hv
      have hnadj : ¬ G.Adj v₀ v := (mem_filter.mp hv).2
      have hX_eq : XVal A U_low G v₀ k d_seq i₀ (Function.update ψ i₀ v) = 0 := by
        dsimp only [XVal]
        rw [if_neg (by push Not; exact ⟨by simp [Function.update_self, hnadj],
          by dsimp [i₀]; rw [h_im_eq v]; exact h_small⟩)]
      rw [hX_eq]; congr 1; dsimp only [z]; ring
    have h_sum_split : ∑ v ∈ C, Real.exp (-θ_X * (XVal A U_low G v₀ k d_seq i₀ (Function.update ψ i₀ v) - (d_seq i₀ : ℝ) / 50)) =
        (C₁.card : ℝ) * Real.exp (-49 / 50 * z) + (C₀.card : ℝ) * Real.exp (1 / 50 * z) := by
      rw [← Finset.sum_filter_add_sum_filter_not (s := C) (p := G.Adj v₀),
        Finset.sum_congr rfl h_val_C1, Finset.sum_congr rfl h_val_C0,
        Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
    have hp_ge : (1 : ℝ) / 50 ≤ (C₁.card : ℝ) / C.card := by
      let vp := ψ (par i₀ (Nat.lt_of_lt_of_le (by norm_num) hr0'))
      have hvp_mem : vp ∈ A \ U_low := hval.2.1 _ (hpar i₀ (Nat.lt_of_lt_of_le (by norm_num) hr0'))
      have h_nonadj_R : ((A.filter (fun w => ¬ G.Adj vp w)).card : ℝ) ≤ μ * k / 10 := by
        have h1 : ((A.filter (G.Adj vp)).card : ℝ) ≥ (1 - μ / 10) * k := hU_deg vp hvp_mem
        have h2 : ((A.filter (G.Adj vp)).card : ℝ) + ((A.filter (fun w => ¬ G.Adj vp w)).card : ℝ) = k := by
          have := Finset.card_filter_add_card_filter_not (s := A) (p := G.Adj vp)
          rw [hA] at this; exact_mod_cast this
        linarith
      have h_sub_v0 : ((A.filter (G.Adj v₀)) \ (U_low ∪ ImFinset r' ψ)) ⊆
          C₁ ∪ (A.filter (fun w => ¬ G.Adj vp w)) := by
        intro w hw
        have hw' := Finset.mem_sdiff.mp hw
        have hwA : w ∈ A := (mem_filter.mp hw'.1).1
        have hw_v0 : G.Adj v₀ w := (mem_filter.mp hw'.1).2
        by_cases hw_vp : G.Adj vp w
        · exact mem_union_left _ (mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨mem_filter.mpr ⟨hwA, hw_vp⟩, hw'.2⟩, hw_v0⟩)
        · exact mem_union_right _ (mem_filter.mpr ⟨hwA, hw_vp⟩)
      have h_C1_ge : (k - r' : ℝ) / 25 - μ * k / 10 ≤ C₁.card := by
        have h1 : (((A.filter (G.Adj v₀)) \ (U_low ∪ ImFinset r' ψ)).card : ℝ) ≤
            C₁.card + (A.filter (fun w => ¬ G.Adj vp w)).card := by
          exact_mod_cast (card_le_card h_sub_v0).trans (card_union_le _ _)
        linarith
      have hkr_ge_s : (s : ℝ) ≤ k - r' := by
        have : r' + s ≤ k := by omega
        have : (r' : ℝ) + s ≤ k := by exact_mod_cast this
        linarith
      have h_rk : r' ≤ k := by omega
      have h_C_le : (C.card : ℝ) ≤ k - r' := by
        have h1 : (C.card : ℝ) ≤ ((k - r' : ℕ) : ℝ) := by exact_mod_cast h_C_b.2.1
        rw [Nat.cast_sub h_rk] at h1
        exact h1
      rw [le_div_iff₀ hC_pos]
      linarith
    have h_exp1 : Real.exp (-49 / 50 * z) ≤ 1 - 49 / 50 * z + z ^ 2 := by
      have h1 := exp_le_quadratic_of_abs_le_one (x := -49 / 50 * z) (by rw [abs_le]; constructor <;> linarith)
      nlinarith
    have h_exp2 : Real.exp (1 / 50 * z) ≤ 1 + 1 / 50 * z + z ^ 2 := by
      have h1 := exp_le_quadratic_of_abs_le_one (x := 1 / 50 * z) (by rw [abs_le]; constructor <;> linarith)
      nlinarith
    have hC0_eq : (C₀.card : ℝ) = C.card - C₁.card := by
      have : (C.card : ℝ) = C₁.card + C₀.card := by exact_mod_cast h_C_split
      linarith
    rw [h_sum_split, div_le_iff₀ hC_pos]
    have hp' : (C.card : ℝ) ≤ 50 * C₁.card := by rw [le_div_iff₀ hC_pos] at hp_ge; linarith
    have h_comb : (C₁.card : ℝ) * Real.exp (-49 / 50 * z) + (C₀.card : ℝ) * Real.exp (1 / 50 * z) ≤
        (C₁.card : ℝ) * (1 - 49 / 50 * z + z ^ 2) + (C₀.card : ℝ) * (1 + 1 / 50 * z + z ^ 2) := by
      gcongr
    have h_lin : (C₁.card : ℝ) * (1 - 49 / 50 * z + z ^ 2) + (C₀.card : ℝ) * (1 + 1 / 50 * z + z ^ 2) =
        C.card * (1 + z ^ 2) + (C.card / 50 - C₁.card) * z := by
      rw [hC0_eq]; ring
    have h_nonpos : (C.card / 50 - C₁.card) * z ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) hz0
    have h_add_exp : 1 + z ^ 2 ≤ Real.exp (z ^ 2) := by linarith [Real.add_one_le_exp (z ^ 2)]
    calc (C₁.card : ℝ) * Real.exp (-49 / 50 * z) + (C₀.card : ℝ) * Real.exp (1 / 50 * z)
        ≤ C.card * (1 + z ^ 2) + (C.card / 50 - C₁.card) * z := h_comb.trans_eq h_lin
      _ ≤ C.card * (1 + z ^ 2) := by linarith
      _ ≤ C.card * Real.exp (z ^ 2) := mul_le_mul_of_nonneg_left h_add_exp hC_pos.le
      _ = Real.exp (z ^ 2) * C.card := mul_comm _ _

lemma mgf_X_bound {L k m s d : ℕ} (hL : 2 ≤ L)
    {μ : ℝ} (hμ_def : μ = 1 / (10 ^ 12 * (L : ℝ) ^ 2))
    (hk_pos : 0 < k) (hs_pos : 0 < s) (hs_lower : (k : ℝ) / (3 * L) ≤ s)
    (hm_eq : m = k - s) (hm_pos : 0 < m)
    (hd_pos : 1 ≤ d) (hd_lt : (d : ℝ) < μ * k)
    (h_μk_le_s : μ * k ≤ (s : ℝ) / 100)
    {n : ℕ} {G : SimpleGraph (Fin n)} {u : Fin n} {A U_low : Finset (Fin n)}
    (hA : A.card = k) (huA : u ∈ A) (hu_not_U : u ∉ U_low)
    (hU_deg : ∀ v ∈ A \ U_low, ((A.filter (G.Adj v)).card : ℝ) ≥ (1 - μ / 10) * k)
    (hU_card : (U_low.card : ℝ) ≤ μ * k / 10)
    (par : ∀ i : Fin m, 0 < i.1 → Fin m) (hpar : ∀ i hi, (par i hi).1 < i.1)
    (d_seq : Fin m → ℕ) (hd_sum : ∑ i : Fin m, d_seq i = s)
    (hd_0 : d_seq ⟨0, hm_pos⟩ = d) (hd_le : ∀ i, d_seq i ≤ d)
    (v₀ : Fin n) (hv₀_adj_u : G.Adj v₀ u) :
    expValFrom A U_low G par (m - 1)
      (fun ψ => if (∑ i : Fin m, XVal A U_low G v₀ k d_seq i ψ) ≤ (s : ℝ) / 100 then 1 else 0) (fun _ => u) ≤
      (d : ℝ) / (4 * k) := by
  have hμ_pos : 0 < μ := by rw [hμ_def]; positivity
  have hL_pos : (0 : ℝ) < L := by positivity
  have h_ne : ∀ r' (hr' : r' < m) (hr0' : 0 < r') ψ,
      ValidPrefix A U_low G u hm_pos par r' ψ →
      (stepCand A U_low G par ψ ⟨r', hr'⟩ hr0').Nonempty :=
    fun r' hr' hr0' ψ hval =>
      (cand_bounds_of_valid hs_pos h_μk_le_s hm_eq hA hU_deg hU_card hm_pos par hpar hr' hr0' hval).2.2
  have hψ₀_val : ValidPrefix A U_low G u hm_pos par 1 (fun _ => u) :=
    ⟨rfl, fun _ _ => Finset.mem_sdiff.mpr ⟨huA, hu_not_U⟩,
      fun j₁ j₂ h1 h2 _ => Fin.ext (by omega), fun j hj hj0 => by omega⟩
  let θ_X : ℝ := 1 / (400 * d : ℝ)
  have hθ_pos : 0 < θ_X := by positivity
  have h_X_step := mgf_X_step hμ_pos hs_pos hm_eq hm_pos hd_pos h_μk_le_s (u := u) hA hU_deg hU_card par hpar d_seq hd_le v₀
  have h_tel := expValFrom_mgf_telescope A U_low G u hm_pos par hpar h_ne
    (MX A U_low G v₀ k d_seq θ_X) (FactorX d_seq θ_X)
    (fun r' => by dsimp only [FactorX]; split_ifs <;> positivity)
    1 le_rfl h_X_step (m - 1) 1 (by omega) le_rfl (fun _ => u) hψ₀_val
  have h_M1_le : MX A U_low G v₀ k d_seq θ_X 1 (fun _ => u) ≤ 1 := by
    have h_f1 : Finset.univ.filter (fun i : Fin m => i.1 < 1) = {⟨0, hm_pos⟩} := by
      ext i; simp only [mem_filter, mem_univ, true_and, mem_singleton, Fin.ext_iff]; omega
    have hX0 : XVal A U_low G v₀ k d_seq ⟨0, hm_pos⟩ (fun _ => u) = d := by
      dsimp only [XVal]; rw [if_pos (Or.inl hv₀_adj_u), hd_0]
    dsimp only [MX]
    rw [h_f1, Finset.sum_singleton, hX0, hd_0]
    exact Real.exp_le_one_iff.mpr (by have : (0 : ℝ) ≤ d := Nat.cast_nonneg _; nlinarith)
  have h_prod_le : ∏ j ∈ Finset.Ico 1 m, FactorX d_seq θ_X j ≤ Real.exp (θ_X ^ 2 * d * s) := by
    have h_le_exp : ∏ j ∈ Finset.Ico 1 m, FactorX d_seq θ_X j =
        Real.exp (∑ j ∈ (Finset.Ico 1 m).attach, (θ_X * d_seq ⟨j.1, (mem_Ico.mp j.2).2⟩) ^ 2) := by
      rw [Real.exp_sum]
      symm
      refine Finset.prod_bij (fun j _ => j.1) (fun j _ => j.2) (fun j₁ _ j₂ _ h => Subtype.ext h)
        (fun b hb => ⟨⟨b, hb⟩, mem_attach _ _, rfl⟩)
        (fun j _ => by dsimp only [FactorX]; rw [dif_pos (mem_Ico.mp j.2).2])
    rw [h_le_exp]
    apply Real.exp_le_exp.mpr
    have h_sum_term : ∑ j ∈ (Finset.Ico 1 m).attach, (θ_X * d_seq ⟨j.1, (mem_Ico.mp j.2).2⟩) ^ 2 ≤
        ∑ j ∈ (Finset.Ico 1 m).attach, θ_X ^ 2 * (d * (d_seq ⟨j.1, (mem_Ico.mp j.2).2⟩ : ℝ)) := by
      refine Finset.sum_le_sum (fun j _ => ?_)
      have hd_i : (d_seq ⟨j.1, (mem_Ico.mp j.2).2⟩ : ℝ) ≤ d := by exact_mod_cast hd_le _
      have hd_0' : (0 : ℝ) ≤ d_seq ⟨j.1, (mem_Ico.mp j.2).2⟩ := Nat.cast_nonneg _
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_left (by rw [sq]; exact mul_le_mul_of_nonneg_right hd_i hd_0') (sq_nonneg θ_X)
    let img := (Finset.Ico 1 m).attach.image (fun j => (⟨j.1, (mem_Ico.mp j.2).2⟩ : Fin m))
    have h_eq_img : ∑ j ∈ (Finset.Ico 1 m).attach, θ_X ^ 2 * (d * (d_seq ⟨j.1, (mem_Ico.mp j.2).2⟩ : ℝ)) =
        ∑ i ∈ img, θ_X ^ 2 * (d * (d_seq i : ℝ)) := by
      symm; refine Finset.sum_image (fun j₁ _ j₂ _ h => Subtype.ext (congrArg Fin.val h))
    have h_inj_sum : ∑ i ∈ img, θ_X ^ 2 * (d * (d_seq i : ℝ)) ≤
        ∑ i : Fin m, θ_X ^ 2 * (d * (d_seq i : ℝ)) :=
      Finset.sum_le_univ_sum_of_nonneg (fun i => by positivity)
    have h_tot : ∑ i : Fin m, θ_X ^ 2 * (d * (d_seq i : ℝ)) = θ_X ^ 2 * d * s := by
      rw [← Finset.mul_sum, ← Finset.mul_sum]
      have hs_sum : ∑ i : Fin m, (d_seq i : ℝ) = s := by exact_mod_cast hd_sum
      rw [hs_sum]; ring
    linarith
  have h_pt : ∀ ψ, ValidPrefix A U_low G u hm_pos par m ψ →
      (if (∑ i : Fin m, XVal A U_low G v₀ k d_seq i ψ) ≤ (s : ℝ) / 100 then (1 : ℝ) else 0) ≤
      Real.exp (-θ_X * s / 100) * MX A U_low G v₀ k d_seq θ_X m ψ := by
    intro ψ _
    by_cases hsum : (∑ i : Fin m, XVal A U_low G v₀ k d_seq i ψ) ≤ (s : ℝ) / 100
    · rw [if_pos hsum]
      have h_flt : Finset.univ.filter (fun i : Fin m => i.1 < m) = Finset.univ := by ext i; simp
      have h_sum_diff : ∑ i : Fin m, (XVal A U_low G v₀ k d_seq i ψ - (d_seq i : ℝ) / 50) ≤ -(s : ℝ) / 100 := by
        rw [Finset.sum_sub_distrib, ← Finset.sum_div]
        have hs_sum : ∑ i : Fin m, (d_seq i : ℝ) = s := by exact_mod_cast hd_sum
        rw [hs_sum]; linarith
      have h_exp_ge : Real.exp (θ_X * s / 100) ≤ MX A U_low G v₀ k d_seq θ_X m ψ := by
        dsimp only [MX]; rw [h_flt]; apply Real.exp_le_exp.mpr; nlinarith
      have h_eq1 : Real.exp (-θ_X * s / 100) * Real.exp (θ_X * s / 100) = 1 := by
        rw [← Real.exp_add, show -θ_X * s / 100 + θ_X * s / 100 = 0 by ring, Real.exp_zero]
      calc (1 : ℝ) = Real.exp (-θ_X * s / 100) * Real.exp (θ_X * s / 100) := h_eq1.symm
        _ ≤ Real.exp (-θ_X * s / 100) * MX A U_low G v₀ k d_seq θ_X m ψ :=
          mul_le_mul_of_nonneg_left h_exp_ge (Real.exp_pos _).le
    · rw [if_neg hsum]; exact mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
  have h_markov : expValFrom A U_low G par (m - 1)
      (fun ψ => if (∑ i : Fin m, XVal A U_low G v₀ k d_seq i ψ) ≤ (s : ℝ) / 100 then 1 else 0) (fun _ => u) ≤
      Real.exp (-θ_X * s / 100) * expValFrom A U_low G par (m - 1) (MX A U_low G v₀ k d_seq θ_X m) (fun _ => u) :=
    (expValFrom_mono A U_low G u hm_pos par hpar _ _ h_pt (m - 1) 1 (by omega) le_rfl (fun _ => u) hψ₀_val).trans_eq
      (expValFrom_smul A U_low G par (m - 1) (Real.exp (-θ_X * s / 100)) (MX A U_low G v₀ k d_seq θ_X m) (fun _ => u))
  have h_alg : Real.exp (-θ_X * s / 100) *
      (MX A U_low G v₀ k d_seq θ_X 1 (fun _ => u) * ∏ j ∈ Finset.Ico 1 m, FactorX d_seq θ_X j) ≤
      (d : ℝ) / (4 * k) := by
    have h_prod_nonneg : 0 ≤ ∏ j ∈ Finset.Ico 1 m, FactorX d_seq θ_X j :=
      Finset.prod_nonneg (fun _ _ => by dsimp only [FactorX]; split_ifs <;> positivity)
    have h1 : MX A U_low G v₀ k d_seq θ_X 1 (fun _ => u) * ∏ j ∈ Finset.Ico 1 m, FactorX d_seq θ_X j ≤
        Real.exp (θ_X ^ 2 * d * s) :=
      (mul_le_mul_of_nonneg_right h_M1_le h_prod_nonneg).trans (by simpa only [one_mul] using h_prod_le)
    have h2 : Real.exp (-θ_X * s / 100) * Real.exp (θ_X ^ 2 * d * s) =
        Real.exp (θ_X ^ 2 * d * s - θ_X * s / 100) := by rw [← Real.exp_add]; congr 1; ring
    have h3 : θ_X ^ 2 * d * s - θ_X * s / 100 ≤ -((s : ℝ) / (80000 * d)) := by
      have hd_p : (0 : ℝ) < d := by exact_mod_cast hd_pos
      dsimp only [θ_X]
      have h_eq : (1 / (400 * (d : ℝ))) ^ 2 * d * s - (1 / (400 * d)) * s / 100 =
          -3 * (s : ℝ) / (160000 * d) := by field_simp; ring
      rw [h_eq]
      have : (0 : ℝ) ≤ s := Nat.cast_nonneg _
      have h_neg : -3 * (s : ℝ) / (160000 * d) = -(3 * (s : ℝ) / (160000 * d)) := by ring
      rw [h_neg, neg_le_neg_iff, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have h_comb : Real.exp (-θ_X * s / 100) *
        (MX A U_low G v₀ k d_seq θ_X 1 (fun _ => u) * ∏ j ∈ Finset.Ico 1 m, FactorX d_seq θ_X j) ≤
        Real.exp (-((s : ℝ) / (80000 * d))) :=
      (mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le).trans (h2 ▸ Real.exp_le_exp.mpr h3)
    have h_exp_b := exp_neg_inv_le_factorial_bound (x := (s : ℝ) / (80000 * d)) (by positivity) (p := 2) (by norm_num)
    have h_final_alg : (Nat.factorial 2 : ℝ) / ((s : ℝ) / (80000 * d)) ^ 2 ≤ (d : ℝ) / (4 * k) := by
      have hd_p : (0 : ℝ) < d := by exact_mod_cast hd_pos
      have hs_p : (0 : ℝ) < s := by exact_mod_cast hs_pos
      have h_lhs : (Nat.factorial 2 : ℝ) / ((s : ℝ) / (80000 * d)) ^ 2 =
          12800000000 * (d : ℝ) ^ 2 / (s : ℝ) ^ 2 := by norm_num [Nat.factorial]; field_simp; ring
      rw [h_lhs, div_le_div_iff₀ (by positivity) (by positivity)]
      have hd_le_μk : (d : ℝ) ≤ μ * k := hd_lt.le
      have h_s_sq : (k : ℝ) ^ 2 / (9 * (L : ℝ) ^ 2) ≤ (s : ℝ) ^ 2 := by
        have h2' : ((k : ℝ) / (3 * L)) ^ 2 ≤ (s : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hs_lower 2
        linarith [show ((k : ℝ) / (3 * L)) ^ 2 = (k : ℝ) ^ 2 / (9 * (L : ℝ) ^ 2) by ring]
      have h_μ_cmp : 51200000000 * (d : ℝ) * k ≤ (k : ℝ) ^ 2 / (9 * (L : ℝ) ^ 2) := by
        have h1' : 51200000000 * (d : ℝ) * k ≤ 51200000000 * (μ * k) * k :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hd_le_μk (by norm_num)) (by positivity)
        have h2' : 51200000000 * (μ * (k : ℝ)) * k = (51200000000 / 10 ^ 12) * ((k : ℝ) ^ 2 / (L : ℝ) ^ 2) := by
          rw [hμ_def]; ring
        have h3' : (51200000000 / 10 ^ 12 : ℝ) ≤ 1 / 9 := by norm_num
        have h4' : (0 : ℝ) ≤ (k : ℝ) ^ 2 / (L : ℝ) ^ 2 := by positivity
        linarith [show (k : ℝ) ^ 2 / (9 * (L : ℝ) ^ 2) = (1 / 9 : ℝ) * ((k : ℝ) ^ 2 / (L : ℝ) ^ 2) by ring,
          mul_le_mul_of_nonneg_right h3' h4']
      have h_mul_d : 51200000000 * (d : ℝ) ^ 2 * k ≤ (d : ℝ) * (s : ℝ) ^ 2 := by
        have : 51200000000 * (d : ℝ) ^ 2 * k = (d : ℝ) * (51200000000 * d * k) := by ring
        rw [this]; exact mul_le_mul_of_nonneg_left (h_μ_cmp.trans h_s_sq) hd_p.le
      nlinarith
    exact h_comb.trans (h_exp_b.trans h_final_alg)
  exact h_markov.trans ((mul_le_mul_of_nonneg_left h_tel (Real.exp_pos _).le).trans h_alg)

noncomputable def YVal {n m : ℕ} (A : Finset (Fin n)) (G : SimpleGraph (Fin n))
    (v₀ : Fin n) (k r' : ℕ) (ψ : Fin m → Fin n) : ℝ :=
  (((A.filter (G.Adj v₀)) \ ImFinset r' ψ).card : ℝ) - (k - r' : ℝ) / 10

noncomputable def MR {n m : ℕ} (A : Finset (Fin n)) (G : SimpleGraph (Fin n))
    (v₀ : Fin n) (k : ℕ) (μ θ_Y : ℝ) (i₀ j₀ r' : ℕ) (ψ : Fin m → Fin n) : ℝ :=
  if r' ≤ i₀ then 1
  else Real.exp (-θ_Y * (Rseq (YVal A G v₀ k) (-μ * k) i₀ (min r' j₀ - i₀) ψ -
    Rseq (YVal A G v₀ k) (-μ * k) i₀ 0 ψ))

noncomputable def FactorR (θ_Y : ℝ) (i₀ j₀ r' : ℕ) : ℝ :=
  if i₀ ≤ r' ∧ r' < j₀ then Real.exp (θ_Y ^ 2) else 1

lemma yVal_update_of_le {n m : ℕ} (A : Finset (Fin n)) (G : SimpleGraph (Fin n)) (v₀ : Fin n) (k : ℕ)
    (r' : ℕ) (ψ : Fin m → Fin n) (i : Fin m) (v : Fin n) (hri : r' ≤ i.1) :
    YVal A G v₀ k r' (Function.update ψ i v) = YVal A G v₀ k r' ψ := by
  simp only [YVal, imFinset_update_of_le hri]

lemma yVal_step {n m : ℕ} (A U_low : Finset (Fin n)) (G : SimpleGraph (Fin n)) (v₀ : Fin n) (k : ℕ)
    (par : ∀ i : Fin m, 0 < i.1 → Fin m)
    (r' : ℕ) (hr' : r' < m) (hr0' : 0 < r') (ψ : Fin m → Fin n)
    (v : Fin n) (hv : v ∈ stepCand A U_low G par ψ ⟨r', hr'⟩ hr0') :
    YVal A G v₀ k (r' + 1) (Function.update ψ ⟨r', hr'⟩ v) - YVal A G v₀ k r' ψ =
      if G.Adj v₀ v then -9 / 10 else 1 / 10 := by
  have h_im_succ := imFinset_succ_update hr' ψ v
  have hv_A : v ∈ A := (mem_filter.mp (Finset.mem_sdiff.mp hv).1).1
  have hv_not_im : v ∉ ImFinset r' ψ := fun h => (Finset.mem_sdiff.mp hv).2 (mem_union_right _ h)
  have h_sdiff_succ : (A.filter (G.Adj v₀)) \ insert v (ImFinset r' ψ) =
      ((A.filter (G.Adj v₀)) \ ImFinset r' ψ).erase v := by
    ext w; simp [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert]; tauto
  have h_card_diff : (((A.filter (G.Adj v₀)) \ ImFinset (r' + 1) (Function.update ψ ⟨r', hr'⟩ v)).card : ℝ) =
      (((A.filter (G.Adj v₀)) \ ImFinset r' ψ).card : ℝ) - (if G.Adj v₀ v then 1 else 0) := by
    rw [h_im_succ, h_sdiff_succ]
    by_cases hadj : G.Adj v₀ v
    · rw [if_pos hadj]
      have hv_in : v ∈ (A.filter (G.Adj v₀)) \ ImFinset r' ψ :=
        Finset.mem_sdiff.mpr ⟨mem_filter.mpr ⟨hv_A, hadj⟩, hv_not_im⟩
      have hc := card_erase_of_mem hv_in
      have hpos : 1 ≤ ((A.filter (G.Adj v₀)) \ ImFinset r' ψ).card := Finset.card_pos.mpr ⟨v, hv_in⟩
      rw [hc, Nat.cast_sub hpos, Nat.cast_one]
    · rw [if_neg hadj]
      have hv_not : v ∉ (A.filter (G.Adj v₀)) \ ImFinset r' ψ := fun h =>
        hadj (mem_filter.mp (Finset.mem_sdiff.mp h).1).2
      rw [erase_eq_of_notMem hv_not]; ring
  dsimp only [YVal]
  rw [h_card_diff, Nat.cast_add, Nat.cast_one]
  split_ifs <;> ring

lemma mgf_R_step {k m s : ℕ} {μ : ℝ} (hs_pos : 0 < s) (hm_eq : m = k - s) (hm_pos : 0 < m)
    (h_μk_le_s : μ * k ≤ (s : ℝ) / 100)
    {n : ℕ} {G : SimpleGraph (Fin n)} {u : Fin n} {A U_low : Finset (Fin n)}
    (hA : A.card = k) (hU_deg : ∀ v ∈ A \ U_low, ((A.filter (G.Adj v)).card : ℝ) ≥ (1 - μ / 10) * k)
    (hU_card : (U_low.card : ℝ) ≤ μ * k / 10)
    (par : ∀ i : Fin m, 0 < i.1 → Fin m) (hpar : ∀ i hi, (par i hi).1 < i.1)
    (v₀ : Fin n) {i₀ j₀ : ℕ} (hij : i₀ < j₀) (θ_Y : ℝ) (hθ_pos : 0 < θ_Y) (hθ_le : θ_Y ≤ 1) :
    ∀ r' (hr' : r' < m) (hr0' : 1 ≤ r') ψ,
      ValidPrefix A U_low G u hm_pos par r' ψ →
      (∑ v ∈ stepCand A U_low G par ψ ⟨r', hr'⟩ (Nat.lt_of_lt_of_le (by norm_num) hr0'),
        MR A G v₀ k μ θ_Y i₀ j₀ (r' + 1) (Function.update ψ ⟨r', hr'⟩ v)) /
        ((stepCand A U_low G par ψ ⟨r', hr'⟩ (Nat.lt_of_lt_of_le (by norm_num) hr0')).card : ℝ) ≤
      MR A G v₀ k μ θ_Y i₀ j₀ r' ψ * FactorR θ_Y i₀ j₀ r' := by
  intro r' hr' hr0' ψ hval
  set C := stepCand A U_low G par ψ ⟨r', hr'⟩ (Nat.lt_of_lt_of_le (by norm_num) hr0')
  have h_C_b := cand_bounds_of_valid hs_pos h_μk_le_s hm_eq hA hU_deg hU_card hm_pos par hpar
    hr' (Nat.lt_of_lt_of_le (by norm_num) hr0') hval
  have hC_pos : (0 : ℝ) < C.card := Nat.cast_pos.mpr (Finset.card_pos.mpr h_C_b.2.2)
  by_cases h_lt_i0 : r' < i₀
  · have h_r1 : r' + 1 ≤ i₀ := h_lt_i0
    have h_r0 : r' ≤ i₀ := h_lt_i0.le
    have h_fac : FactorR θ_Y i₀ j₀ r' = 1 := if_neg (by omega)
    have h_sum_1 : (∑ v ∈ C, MR A G v₀ k μ θ_Y i₀ j₀ (r' + 1) (Function.update ψ ⟨r', hr'⟩ v)) / (C.card : ℝ) = 1 := by
      have h_eq : ∀ v ∈ C, MR A G v₀ k μ θ_Y i₀ j₀ (r' + 1) (Function.update ψ ⟨r', hr'⟩ v) = 1 :=
        fun v _ => if_pos h_r1
      rw [Finset.sum_congr rfl h_eq, Finset.sum_const, nsmul_eq_mul, mul_one, div_self hC_pos.ne']
    rw [h_sum_1]; dsimp only [MR]; rw [if_pos h_r0, h_fac, mul_one]
  · by_cases h_ge_j0 : j₀ ≤ r'
    · have h_not_r1 : ¬ (r' + 1 ≤ i₀) := by omega
      have h_not_r0 : ¬ (r' ≤ i₀) := by omega
      have h_fac : FactorR θ_Y i₀ j₀ r' = 1 := if_neg (by omega)
      have h_min1 : min (r' + 1) j₀ = j₀ := min_eq_right (by omega)
      have h_min0 : min r' j₀ = j₀ := min_eq_right h_ge_j0
      have h_upd_eq : ∀ v ∈ C, MR A G v₀ k μ θ_Y i₀ j₀ (r' + 1) (Function.update ψ ⟨r', hr'⟩ v) =
          MR A G v₀ k μ θ_Y i₀ j₀ r' ψ := by
        intro v _
        dsimp only [MR]
        rw [if_neg h_not_r1, if_neg h_not_r0, h_min1, h_min0]
        have h_rseq1 := rseq_update_of_le (YVal A G v₀ k) (-μ * k) i₀ (j₀ - i₀) ψ ⟨r', hr'⟩ v
          (fun r'' hr'' => yVal_update_of_le A G v₀ k r'' ψ ⟨r', hr'⟩ v (by dsimp; omega))
        have h_rseq0 := rseq_update_of_le (YVal A G v₀ k) (-μ * k) i₀ 0 ψ ⟨r', hr'⟩ v
          (fun r'' hr'' => yVal_update_of_le A G v₀ k r'' ψ ⟨r', hr'⟩ v (by dsimp; omega))
        rw [h_rseq1, h_rseq0]
      rw [Finset.sum_congr rfl h_upd_eq, Finset.sum_const, nsmul_eq_mul,
        mul_div_cancel_left₀ _ hC_pos.ne', h_fac, mul_one]
    · have hr'_ge : i₀ ≤ r' := by omega
      have hr'_lt : r' < j₀ := by omega
      have h_fac : FactorR θ_Y i₀ j₀ r' = Real.exp (θ_Y ^ 2) := if_pos ⟨hr'_ge, hr'_lt⟩
      have h_not_r1 : ¬ (r' + 1 ≤ i₀) := by omega
      have h_min1 : min (r' + 1) j₀ = r' + 1 := min_eq_left (by omega)
      have h_min0 : min r' j₀ = r' := min_eq_left (by omega)
      have h_MR_r' : MR A G v₀ k μ θ_Y i₀ j₀ r' ψ =
          Real.exp (-θ_Y * (Rseq (YVal A G v₀ k) (-μ * k) i₀ (r' - i₀) ψ - Rseq (YVal A G v₀ k) (-μ * k) i₀ 0 ψ)) := by
        dsimp only [MR]
        by_cases h_eq : r' = i₀
        · subst h_eq; rw [if_pos le_rfl]; simp
        · rw [if_neg (by omega), h_min0]
      have h_upd0 : ∀ v, Rseq (YVal A G v₀ k) (-μ * k) i₀ 0 (Function.update ψ ⟨r', hr'⟩ v) =
          Rseq (YVal A G v₀ k) (-μ * k) i₀ 0 ψ :=
        fun v => rseq_update_of_le (YVal A G v₀ k) (-μ * k) i₀ 0 ψ ⟨r', hr'⟩ v
          (fun r'' hr'' => yVal_update_of_le A G v₀ k r'' ψ ⟨r', hr'⟩ v (by dsimp; omega))
      have h_upd0' : ∀ v, YVal A G v₀ k i₀ (Function.update ψ ⟨r', hr'⟩ v) = YVal A G v₀ k i₀ ψ :=
        fun v => yVal_update_of_le A G v₀ k i₀ ψ ⟨r', hr'⟩ v (by dsimp; omega)
      have h_upd_prev : ∀ v, Rseq (YVal A G v₀ k) (-μ * k) i₀ (r' - i₀) (Function.update ψ ⟨r', hr'⟩ v) =
          Rseq (YVal A G v₀ k) (-μ * k) i₀ (r' - i₀) ψ :=
        fun v => rseq_update_of_le (YVal A G v₀ k) (-μ * k) i₀ (r' - i₀) ψ ⟨r', hr'⟩ v
          (fun r'' hr'' => yVal_update_of_le A G v₀ k r'' ψ ⟨r', hr'⟩ v (by dsimp; omega))
      have h_sub1 : r' + 1 - i₀ = (r' - i₀) + 1 := by omega
      have h_MR_nonneg : 0 ≤ MR A G v₀ k μ θ_Y i₀ j₀ r' ψ := by dsimp only [MR]; split_ifs <;> positivity
      by_cases h_le_thresh : Rseq (YVal A G v₀ k) (-μ * k) i₀ (r' - i₀) ψ ≤ -μ * k
      · obtain ⟨h_rseq_eq_Y, _⟩ := rseq_le_imp (YVal A G v₀ k) (-μ * k) i₀ (r' - i₀) ψ h_le_thresh
        have h_idx : i₀ + (r' - i₀) = r' := by omega
        have h_Y_le : YVal A G v₀ k r' ψ ≤ -μ * k := by rw [← h_idx, ← h_rseq_eq_Y]; exact h_le_thresh
        have h_M_split : ∀ v ∈ C, MR A G v₀ k μ θ_Y i₀ j₀ (r' + 1) (Function.update ψ ⟨r', hr'⟩ v) =
            MR A G v₀ k μ θ_Y i₀ j₀ r' ψ * Real.exp (-θ_Y * (if G.Adj v₀ v then -9 / 10 else 1 / 10)) := by
          intro v hv
          rw [h_MR_r']
          dsimp only [MR]
          rw [if_neg h_not_r1, h_min1, h_sub1]
          dsimp only [Rseq]
          rw [h_upd_prev v, if_pos h_le_thresh, h_upd0' v]
          have h_add1 : i₀ + (r' - i₀) + 1 = r' + 1 := by omega
          rw [h_add1]
          have h_Y_diff := yVal_step A U_low G v₀ k par r' hr' (Nat.lt_of_lt_of_le (by norm_num) hr0') ψ v hv
          have h_eq_R : Rseq (YVal A G v₀ k) (-μ * k) i₀ (r' - i₀) ψ = YVal A G v₀ k r' ψ :=
            h_rseq_eq_Y.trans (by rw [h_idx])
          rw [h_eq_R, ← Real.exp_add]
          congr 1; rw [← mul_add]; congr 1; linarith
        rw [Finset.sum_congr rfl h_M_split, ← Finset.mul_sum, mul_div_assoc, h_fac]
        refine mul_le_mul_of_nonneg_left ?_ h_MR_nonneg
        let C₁ := C.filter (G.Adj v₀)
        let C₀ := C.filter (fun v => ¬ G.Adj v₀ v)
        have h_C_split : C.card = C₁.card + C₀.card := (Finset.card_filter_add_card_filter_not (s := C) (p := G.Adj v₀)).symm
        have h_sum_split : ∑ v ∈ C, Real.exp (-θ_Y * (if G.Adj v₀ v then -9 / 10 else 1 / 10)) =
            (C₁.card : ℝ) * Real.exp (9 / 10 * θ_Y) + (C₀.card : ℝ) * Real.exp (-1 / 10 * θ_Y) := by
          rw [← Finset.sum_filter_add_sum_filter_not (s := C) (p := G.Adj v₀)]
          have h1 : ∀ v ∈ C₁, Real.exp (-θ_Y * (if G.Adj v₀ v then -9 / 10 else 1 / 10)) = Real.exp (9 / 10 * θ_Y) := by
            intro v hv; rw [if_pos (mem_filter.mp hv).2]; congr 1; ring
          have h0 : ∀ v ∈ C₀, Real.exp (-θ_Y * (if G.Adj v₀ v then -9 / 10 else 1 / 10)) = Real.exp (-1 / 10 * θ_Y) := by
            intro v hv; rw [if_neg (mem_filter.mp hv).2]; congr 1; ring
          rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h0,
            Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
        have hp_le : (C₁.card : ℝ) ≤ (C.card : ℝ) / 10 := by
          have h_sub_C1 : C₁ ⊆ (A.filter (G.Adj v₀)) \ ImFinset r' ψ := by
            intro w hw
            have hw' := Finset.mem_sdiff.mp (mem_filter.mp hw).1
            exact Finset.mem_sdiff.mpr ⟨mem_filter.mpr ⟨(mem_filter.mp hw'.1).1, (mem_filter.mp hw).2⟩,
              fun him => hw'.2 (mem_union_right _ him)⟩
          have h_C1_le : (C₁.card : ℝ) ≤ (k - r' : ℝ) / 10 - μ * k := by
            have h1 : (C₁.card : ℝ) ≤ ((A.filter (G.Adj v₀)) \ ImFinset r' ψ).card :=
              by exact_mod_cast card_le_card h_sub_C1
            dsimp only [YVal] at h_Y_le; linarith
          linarith [h_C_b.1]
        have hC0_eq : (C₀.card : ℝ) = C.card - C₁.card := by
          have : (C.card : ℝ) = C₁.card + C₀.card := by exact_mod_cast h_C_split
          linarith
        have h_exp_ge : Real.exp (-1 / 10 * θ_Y) ≤ Real.exp (9 / 10 * θ_Y) := Real.exp_le_exp.mpr (by linarith)
        have h_exp_pos_le : Real.exp (9 / 10 * θ_Y) ≤ 1 + 9 / 10 * θ_Y + 81 / 100 * θ_Y ^ 2 := by
          have h1 := exp_le_quadratic_of_abs_le_one (x := 9 / 10 * θ_Y) (by rw [abs_le]; constructor <;> linarith)
          linarith [show (9 / 10 * θ_Y) ^ 2 = 81 / 100 * θ_Y ^ 2 by ring]
        have h_exp_neg_le : Real.exp (-1 / 10 * θ_Y) ≤ 1 - 1 / 10 * θ_Y + 1 / 100 * θ_Y ^ 2 := by
          have h1 := exp_le_quadratic_of_abs_le_one (x := -1 / 10 * θ_Y) (by rw [abs_le]; constructor <;> linarith)
          linarith [show (-1 / 10 * θ_Y) ^ 2 = 1 / 100 * θ_Y ^ 2 by ring]
        rw [h_sum_split, div_le_iff₀ hC_pos]
        have h_mono_p : (C₁.card : ℝ) * Real.exp (9 / 10 * θ_Y) + (C₀.card : ℝ) * Real.exp (-1 / 10 * θ_Y) ≤
            (C.card / 10) * Real.exp (9 / 10 * θ_Y) + (9 * C.card / 10) * Real.exp (-1 / 10 * θ_Y) := by
          have h1 : (C₁.card : ℝ) * Real.exp (9 / 10 * θ_Y) + (C.card - C₁.card) * Real.exp (-1 / 10 * θ_Y) =
              C.card * Real.exp (-1 / 10 * θ_Y) + C₁.card * (Real.exp (9 / 10 * θ_Y) - Real.exp (-1 / 10 * θ_Y)) := by ring
          have h2 : (C.card / 10) * Real.exp (9 / 10 * θ_Y) + (9 * C.card / 10) * Real.exp (-1 / 10 * θ_Y) =
              C.card * Real.exp (-1 / 10 * θ_Y) + (C.card / 10) * (Real.exp (9 / 10 * θ_Y) - Real.exp (-1 / 10 * θ_Y)) := by ring
          rw [hC0_eq, h1, h2]; gcongr
        have h_quad : (C.card / 10) * Real.exp (9 / 10 * θ_Y) + (9 * C.card / 10) * Real.exp (-1 / 10 * θ_Y) ≤
            C.card * (1 + θ_Y ^ 2) := by
          have h1 : (C.card / 10) * (1 + 9 / 10 * θ_Y + 81 / 100 * θ_Y ^ 2) +
              (9 * C.card / 10) * (1 - 1 / 10 * θ_Y + 1 / 100 * θ_Y ^ 2) =
              C.card * (1 + 9 / 100 * θ_Y ^ 2) := by ring
          have h2 : C.card * (1 + 9 / 100 * θ_Y ^ 2) ≤ C.card * (1 + θ_Y ^ 2) := by gcongr; nlinarith
          calc (C.card / 10) * Real.exp (9 / 10 * θ_Y) + (9 * C.card / 10) * Real.exp (-1 / 10 * θ_Y)
              ≤ (C.card / 10) * (1 + 9 / 10 * θ_Y + 81 / 100 * θ_Y ^ 2) +
                (9 * C.card / 10) * (1 - 1 / 10 * θ_Y + 1 / 100 * θ_Y ^ 2) := by gcongr
            _ = C.card * (1 + 9 / 100 * θ_Y ^ 2) := h1
            _ ≤ C.card * (1 + θ_Y ^ 2) := h2
        have h_add_exp : 1 + θ_Y ^ 2 ≤ Real.exp (θ_Y ^ 2) := by linarith [Real.add_one_le_exp (θ_Y ^ 2)]
        calc (C₁.card : ℝ) * Real.exp (9 / 10 * θ_Y) + (C₀.card : ℝ) * Real.exp (-1 / 10 * θ_Y)
            ≤ (C.card / 10) * Real.exp (9 / 10 * θ_Y) + (9 * C.card / 10) * Real.exp (-1 / 10 * θ_Y) := h_mono_p
          _ ≤ C.card * (1 + θ_Y ^ 2) := h_quad
          _ ≤ C.card * Real.exp (θ_Y ^ 2) := mul_le_mul_of_nonneg_left h_add_exp hC_pos.le
          _ = Real.exp (θ_Y ^ 2) * C.card := mul_comm _ _
      · have h_upd_eq : ∀ v ∈ C, MR A G v₀ k μ θ_Y i₀ j₀ (r' + 1) (Function.update ψ ⟨r', hr'⟩ v) =
            MR A G v₀ k μ θ_Y i₀ j₀ r' ψ := by
          intro v _
          rw [h_MR_r']
          dsimp only [MR]
          rw [if_neg h_not_r1, h_min1, h_sub1]
          dsimp only [Rseq]
          rw [h_upd_prev v, if_neg h_le_thresh, h_upd0' v]
        rw [Finset.sum_congr rfl h_upd_eq, Finset.sum_const, nsmul_eq_mul,
          mul_div_cancel_left₀ _ hC_pos.ne', h_fac]
        exact le_mul_of_one_le_right h_MR_nonneg (Real.one_le_exp (sq_nonneg θ_Y))

lemma mgf_R_bound {L k m s : ℕ} (hL : 2 ≤ L)
    {μ : ℝ} (hμ_def : μ = 1 / (10 ^ 12 * (L : ℝ) ^ 2))
    (hk_ge_big : 10 ^ 104 * L ^ 18 ≤ k) (hk_pos : 0 < k)
    (hs_pos : 0 < s) (hs_upper : (s : ℝ) ≤ k / (2 * L))
    (hm_eq : m = k - s) (hm_pos : 0 < m)
    (h_μk_le_s : μ * k ≤ (s : ℝ) / 100)
    {n : ℕ} {G : SimpleGraph (Fin n)} {u : Fin n} {A U_low : Finset (Fin n)}
    (hA : A.card = k) (huA : u ∈ A) (hu_not_U : u ∉ U_low)
    (hU_deg : ∀ v ∈ A \ U_low, ((A.filter (G.Adj v)).card : ℝ) ≥ (1 - μ / 10) * k)
    (hU_card : (U_low.card : ℝ) ≤ μ * k / 10)
    (par : ∀ i : Fin m, 0 < i.1 → Fin m) (hpar : ∀ i hi, (par i hi).1 < i.1)
    (v₀ : Fin n) {i₀ j₀ : ℕ} (hi₀_ge : 1 ≤ i₀) (hij : i₀ < j₀) (hj₀_lt : j₀ < m) :
    expValFrom A U_low G par (m - 1)
      (fun ψ => if Rseq (YVal A G v₀ k) (-μ * k) i₀ (j₀ - i₀) ψ - Rseq (YVal A G v₀ k) (-μ * k) i₀ 0 ψ ≤ -μ * k / 2 then 1 else 0)
      (fun _ => u) ≤
      1 / (4 * (k : ℝ) ^ 3) := by
  have hμ_pos : 0 < μ := by rw [hμ_def]; positivity
  have hL_pos : (0 : ℝ) < L := by positivity
  have hL_R : (2 : ℝ) ≤ L := by exact_mod_cast hL
  have hk_R : (10 ^ 104 * (L : ℝ) ^ 18) ≤ k := by exact_mod_cast hk_ge_big
  have hm_bounds : (3 * (k : ℝ) / 4 ≤ m) ∧ ((m : ℝ) ≤ k) := by
    have hs_le_k4 : (s : ℝ) ≤ k / 4 :=
      hs_upper.trans (div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith))
    have hs_le_k : s ≤ k := by
      have : (s : ℝ) ≤ k := by linarith [show (0 : ℝ) ≤ k from Nat.cast_nonneg _]
      exact_mod_cast this
    have hm_R : (m : ℝ) = k - s := by rw [hm_eq, Nat.cast_sub hs_le_k]
    exact ⟨by linarith, by linarith [show (0 : ℝ) ≤ s from Nat.cast_nonneg _]⟩
  have h_ne : ∀ r' (hr' : r' < m) (hr0' : 0 < r') ψ,
      ValidPrefix A U_low G u hm_pos par r' ψ →
      (stepCand A U_low G par ψ ⟨r', hr'⟩ hr0').Nonempty :=
    fun r' hr' hr0' ψ hval =>
      (cand_bounds_of_valid hs_pos h_μk_le_s hm_eq hA hU_deg hU_card hm_pos par hpar hr' hr0' hval).2.2
  have hψ₀_val : ValidPrefix A U_low G u hm_pos par 1 (fun _ => u) :=
    ⟨rfl, fun _ _ => Finset.mem_sdiff.mpr ⟨huA, hu_not_U⟩,
      fun j₁ j₂ h1 h2 _ => Fin.ext (by omega), fun j hj hj0 => by omega⟩
  let θ_Y : ℝ := μ * k / (4 * m)
  have hm_posR : (0 : ℝ) < m := Nat.cast_pos.mpr hm_pos
  have hθ_pos : 0 < θ_Y := by positivity
  have hθ_le : θ_Y ≤ 1 := by
    dsimp only [θ_Y]
    rw [div_le_one (by positivity)]
    have h1 : μ * k ≤ 1 / (4 * 10 ^ 12) * k := by
      rw [hμ_def]
      have : 1 / (10 ^ 12 * (L : ℝ) ^ 2) ≤ 1 / (4 * 10 ^ 12) :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity) (by nlinarith)
      exact mul_le_mul_of_nonneg_right this (Nat.cast_nonneg _)
    linarith [hm_bounds.1]
  have h_R_step := mgf_R_step hs_pos hm_eq hm_pos h_μk_le_s (u := u) hA hU_deg hU_card par hpar v₀ hij θ_Y hθ_pos hθ_le
  have h_tel := expValFrom_mgf_telescope A U_low G u hm_pos par hpar h_ne
    (MR A G v₀ k μ θ_Y i₀ j₀) (FactorR θ_Y i₀ j₀)
    (fun r' => by dsimp only [FactorR]; split_ifs <;> positivity)
    1 le_rfl h_R_step (m - 1) 1 (by omega) le_rfl (fun _ => u) hψ₀_val
  have h_M1 : MR A G v₀ k μ θ_Y i₀ j₀ 1 (fun _ : Fin m => u) = 1 := by
    dsimp only [MR]; exact if_pos hi₀_ge
  have h_prod_le : ∏ j ∈ Finset.Ico 1 m, FactorR θ_Y i₀ j₀ j ≤ Real.exp (m * θ_Y ^ 2) := by
    have h_le_exp : ∀ j ∈ Finset.Ico 1 m, FactorR θ_Y i₀ j₀ j ≤ Real.exp (θ_Y ^ 2) := fun j _ => by
      dsimp only [FactorR]; split_ifs; exact le_rfl; exact Real.one_le_exp (sq_nonneg θ_Y)
    calc ∏ j ∈ Finset.Ico 1 m, FactorR θ_Y i₀ j₀ j
        ≤ ∏ _j ∈ Finset.Ico 1 m, Real.exp (θ_Y ^ 2) :=
            Finset.prod_le_prod (fun j _ => by dsimp only [FactorR]; split_ifs <;> positivity) h_le_exp
      _ = Real.exp ((Finset.Ico 1 m).card * θ_Y ^ 2) := by rw [Finset.prod_const, ← Real.exp_nat_mul]
      _ ≤ Real.exp (m * θ_Y ^ 2) := by
          apply Real.exp_le_exp.mpr
          have hcard_N : (Finset.Ico 1 m).card ≤ m :=
            (Finset.card_le_card (fun x hx => Finset.mem_range.mpr (mem_Ico.mp hx).2)).trans_eq (Finset.card_range m)
          have hcard : ((Finset.Ico 1 m).card : ℝ) ≤ m := by exact_mod_cast hcard_N
          gcongr
  have h_pt : ∀ ψ, ValidPrefix A U_low G u hm_pos par m ψ →
      (if Rseq (YVal A G v₀ k) (-μ * k) i₀ (j₀ - i₀) ψ - Rseq (YVal A G v₀ k) (-μ * k) i₀ 0 ψ ≤ -μ * k / 2 then (1 : ℝ) else 0) ≤
      Real.exp (-θ_Y * (μ * k / 2)) * MR A G v₀ k μ θ_Y i₀ j₀ m ψ := by
    intro ψ _
    by_cases h_bad : Rseq (YVal A G v₀ k) (-μ * k) i₀ (j₀ - i₀) ψ - Rseq (YVal A G v₀ k) (-μ * k) i₀ 0 ψ ≤ -μ * k / 2
    · rw [if_pos h_bad]
      have h_MR_m : Real.exp (θ_Y * (μ * k / 2)) ≤ MR A G v₀ k μ θ_Y i₀ j₀ m ψ := by
        dsimp only [MR]
        rw [if_neg (by omega), min_eq_right hj₀_lt.le]
        apply Real.exp_le_exp.mpr; nlinarith
      have h_eq1 : Real.exp (-θ_Y * (μ * k / 2)) * Real.exp (θ_Y * (μ * k / 2)) = 1 := by
        rw [← Real.exp_add, show -θ_Y * (μ * k / 2) + θ_Y * (μ * k / 2) = 0 by ring, Real.exp_zero]
      calc (1 : ℝ) = Real.exp (-θ_Y * (μ * k / 2)) * Real.exp (θ_Y * (μ * k / 2)) := h_eq1.symm
        _ ≤ Real.exp (-θ_Y * (μ * k / 2)) * MR A G v₀ k μ θ_Y i₀ j₀ m ψ :=
          mul_le_mul_of_nonneg_left h_MR_m (Real.exp_pos _).le
    · rw [if_neg h_bad]
      exact mul_nonneg (Real.exp_pos _).le (by dsimp only [MR]; split_ifs <;> positivity)
  have h_markov : expValFrom A U_low G par (m - 1)
      (fun ψ => if Rseq (YVal A G v₀ k) (-μ * k) i₀ (j₀ - i₀) ψ - Rseq (YVal A G v₀ k) (-μ * k) i₀ 0 ψ ≤ -μ * k / 2 then 1 else 0)
      (fun _ => u) ≤
      Real.exp (-θ_Y * (μ * k / 2)) * expValFrom A U_low G par (m - 1) (MR A G v₀ k μ θ_Y i₀ j₀ m) (fun _ => u) :=
    (expValFrom_mono A U_low G u hm_pos par hpar _ _ h_pt (m - 1) 1 (by omega) le_rfl (fun _ => u) hψ₀_val).trans_eq
      (expValFrom_smul A U_low G par (m - 1) (Real.exp (-θ_Y * (μ * k / 2))) (MR A G v₀ k μ θ_Y i₀ j₀ m) (fun _ => u))
  have h_alg : Real.exp (-θ_Y * (μ * k / 2)) *
      (MR A G v₀ k μ θ_Y i₀ j₀ 1 (fun _ : Fin m => u) * ∏ j ∈ Finset.Ico 1 m, FactorR θ_Y i₀ j₀ j) ≤
      1 / (4 * (k : ℝ) ^ 3) := by
    have h1 : MR A G v₀ k μ θ_Y i₀ j₀ 1 (fun _ : Fin m => u) * ∏ j ∈ Finset.Ico 1 m, FactorR θ_Y i₀ j₀ j ≤
        Real.exp (m * θ_Y ^ 2) := by
      rw [h_M1, one_mul]; exact h_prod_le
    have h2 : Real.exp (-θ_Y * (μ * k / 2)) * Real.exp (m * θ_Y ^ 2) =
        Real.exp (m * θ_Y ^ 2 - θ_Y * (μ * k / 2)) := by rw [← Real.exp_add]; congr 1; ring
    have h3 : m * θ_Y ^ 2 - θ_Y * (μ * k / 2) ≤ -(μ ^ 2 * k / 16) := by
      have h_eq : m * θ_Y ^ 2 - θ_Y * (μ * k / 2) = -(μ ^ 2 * (k : ℝ) ^ 2 / (16 * m)) := by
        dsimp only [θ_Y]; field_simp; ring
      rw [h_eq, neg_le_neg_iff, div_le_div_iff₀ (by norm_num) (by positivity)]
      have : (m : ℝ) ≤ k := hm_bounds.2
      nlinarith [sq_nonneg (μ * k)]
    have h_comb : Real.exp (-θ_Y * (μ * k / 2)) *
        (MR A G v₀ k μ θ_Y i₀ j₀ 1 (fun _ : Fin m => u) * ∏ j ∈ Finset.Ico 1 m, FactorR θ_Y i₀ j₀ j) ≤
        Real.exp (-(μ ^ 2 * k / 16)) :=
      (mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le).trans (h2 ▸ Real.exp_le_exp.mpr h3)
    have h_exp_b := exp_neg_inv_le_factorial_bound (x := μ ^ 2 * k / 16) (by positivity) (p := 4) (by norm_num)
    have h_final_alg : (Nat.factorial 4 : ℝ) / (μ ^ 2 * k / 16) ^ 4 ≤ 1 / (4 * (k : ℝ) ^ 3) := by
      have h_lhs : (Nat.factorial 4 : ℝ) / (μ ^ 2 * k / 16) ^ 4 =
          (24 * 65536 : ℝ) / (μ ^ 8 * (k : ℝ) ^ 4) := by norm_num [Nat.factorial]; field_simp; ring
      rw [h_lhs, div_le_div_iff₀ (by positivity) (by positivity)]
      have h_k_big : (4 * 24 * 65536 : ℝ) / μ ^ 8 ≤ k := by
        have h_eq : (4 * 24 * 65536 : ℝ) / μ ^ 8 = (6291456 : ℝ) * 10 ^ 96 * (L : ℝ) ^ 16 := by
          rw [hμ_def]; simp only [one_div, inv_pow, div_inv_eq_mul]; ring
        rw [h_eq]
        have hL16 : (L : ℝ) ^ 16 ≤ (L : ℝ) ^ 18 := pow_le_pow_right₀ (by linarith) (by norm_num)
        nlinarith
      have h_mul : (4 * 24 * 65536 : ℝ) * (k : ℝ) ^ 3 ≤ μ ^ 8 * (k : ℝ) ^ 4 := by
        have h1' : (4 * 24 * 65536 : ℝ) ≤ (k : ℝ) * μ ^ 8 := (div_le_iff₀ (by positivity)).mp h_k_big
        have : (0 : ℝ) ≤ (k : ℝ) ^ 3 := by positivity
        nlinarith
      linarith
    exact h_comb.trans (h_exp_b.trans h_final_alg)
  exact h_markov.trans ((mul_le_mul_of_nonneg_left h_tel (Real.exp_pos _).le).trans h_alg)

lemma per_vertex_bad_bound {L n k r m s d : ℕ} (hL : 2 ≤ L)
    {μ : ℝ} (hμ_def : μ = 1 / (10 ^ 12 * (L : ℝ) ^ 2))
    (hDr : 10 ^ 28 * L ^ 4 * r ≤ n) (hk_le : k ≤ n) (hkr : n < k + r)
    (hk_ge_big : 10 ^ 104 * L ^ 18 ≤ k) (hk_pos : 0 < k)
    (hs_pos : 0 < s) (hs_lower : (k : ℝ) / (3 * L) ≤ s) (hs_upper : (s : ℝ) ≤ k / (2 * L))
    (hm_eq : m = k - s) (hm_pos : 0 < m)
    (hd_pos : 1 ≤ d) (hd_lt : (d : ℝ) < μ * k)
    (h_μk_ge : (10 ^ 90 : ℝ) ≤ μ * k) (h_μk_le_s : μ * k ≤ (s : ℝ) / 100)
    (_hr_le_nD : (r : ℝ) ≤ n / (10 ^ 28 * (L : ℝ) ^ 4))
    {G : SimpleGraph (Fin n)} {u : Fin n} {A U_low : Finset (Fin n)}
    (hA : A.card = k) (huA : u ∈ A) (hv_deg : ∀ v ∈ A, n / 8 ≤ (G.neighborSet v).ncard)
    (hu_not_U : u ∉ U_low)
    (hU_deg : ∀ v ∈ A \ U_low, ((A.filter (G.Adj v)).card : ℝ) ≥ (1 - μ / 10) * k)
    (hU_card : (U_low.card : ℝ) ≤ μ * k / 10)
    (par : ∀ i : Fin m, 0 < i.1 → Fin m) (hpar : ∀ i hi, (par i hi).1 < i.1)
    (d_seq : Fin m → ℕ) (hd_sum : ∑ i : Fin m, d_seq i = s)
    (hd_0 : d_seq ⟨0, hm_pos⟩ = d) (hd_le : ∀ i, d_seq i ≤ d)
    (v₀ : Fin n) (hv₀_A : v₀ ∈ A) (hv₀_adj_u : G.Adj v₀ u) :
    expValFrom A U_low G par (m - 1)
      (fun ψ => if (((Finset.univ.filter (fun i : Fin m => G.Adj v₀ (ψ i))).sum d_seq : ℕ) : ℝ) < (s : ℝ) / 100 then 1 else 0)
      (fun _ => u) ≤
      (d : ℝ) / (2 * k) := by
  classical
  have hμ_pos : 0 < μ := by rw [hμ_def]; positivity
  have hL_R : (2 : ℝ) ≤ L := by exact_mod_cast hL
  have hL4_pos : 1 ≤ L ^ 4 := Nat.one_le_pow 4 L (by omega)
  let X_val : Fin m → (Fin m → Fin n) → ℝ := XVal A U_low G v₀ k d_seq
  let Y_val : ℕ → (Fin m → Fin n) → ℝ := YVal A G v₀ k
  let B_sum : (Fin m → Fin n) → ℝ := fun ψ =>
    (if (∑ i : Fin m, X_val i ψ) ≤ (s : ℝ) / 100 then 1 else 0) +
    ∑ i₀ ∈ Finset.Ico 1 m, ∑ j₀ ∈ Finset.Ico (i₀ + 1) m,
      (if Rseq Y_val (-μ * k) i₀ (j₀ - i₀) ψ - Rseq Y_val (-μ * k) i₀ 0 ψ ≤ -μ * k / 2 then 1 else 0)
  have hψ₀_val : ValidPrefix A U_low G u hm_pos par 1 (fun _ => u) :=
    ⟨rfl, fun _ _ => Finset.mem_sdiff.mpr ⟨huA, hu_not_U⟩,
      fun j₁ j₂ h1 h2 _ => Fin.ext (by omega), fun j hj hj0 => by omega⟩
  have hY1_nonneg : ∀ ψ, ValidPrefix A U_low G u hm_pos par 1 ψ → 0 ≤ Y_val 1 ψ := by
    intro ψ hval
    have h_im1 : ImFinset 1 ψ = {u} := by
      ext w; simp only [ImFinset, mem_image, mem_filter, mem_univ, true_and, mem_singleton]
      constructor
      · rintro ⟨j, hj, rfl⟩; have hj0 : j = ⟨0, hm_pos⟩ := Fin.ext (Nat.lt_one_iff.mp hj); rw [hj0, hval.1]
      · rintro rfl; exact ⟨⟨0, hm_pos⟩, zero_lt_one, hval.1⟩
    have h_card_ge := card_filter_adj_ge_of_neighborSet hA hk_le hkr (hv_deg v₀ hv₀_A)
    have h_sdiff_ge : (A.filter (G.Adj v₀)).card - 1 ≤ ((A.filter (G.Adj v₀)) \ ImFinset 1 ψ).card := by
      rw [h_im1]
      have h1 : (A.filter (G.Adj v₀)).card ≤ ((A.filter (G.Adj v₀)) \ {u}).card + ({u} : Finset (Fin n)).card :=
        card_le_card_sdiff_add_card
      rw [card_singleton] at h1; omega
    have hL4R : (1 : ℝ) ≤ (L : ℝ) ^ 4 := by exact_mod_cast hL4_pos
    have h_r_R : (r : ℝ) ≤ n / 100 := by
      have h1 : 100 * (r : ℝ) ≤ 10 ^ 28 * (L : ℝ) ^ 4 * r := by nlinarith
      have h2 : (10 ^ 28 * (L : ℝ) ^ 4 * r : ℝ) ≤ n := by exact_mod_cast hDr
      linarith
    have h_n8 : (n / 8 : ℝ) - 1 ≤ (n / 8 : ℕ) := by
      have hdm := Nat.div_add_mod n 8
      have hml := Nat.mod_lt n (by omega : 0 < 8)
      have hn8 : 8 ≤ n := by
        have : 10 ^ 104 * L ^ 18 ≤ n := hk_ge_big.trans hk_le
        have : 1 ≤ L ^ 18 := Nat.one_le_pow 18 L (by omega)
        nlinarith
      have h1 : n - 8 ≤ (n / 8) * 8 := by omega
      have h2 : ((n - 8 : ℕ) : ℝ) ≤ ((n / 8 * 8 : ℕ) : ℝ) := by exact_mod_cast h1
      rw [Nat.cast_sub hn8, Nat.cast_mul] at h2
      linarith
    have h_sub : (n : ℝ) / 8 - r - 2 ≤ (((A.filter (G.Adj v₀)) \ ImFinset 1 ψ).card : ℝ) := by
      by_cases h1 : r + 1 ≤ n / 8
      · have h_nat : n / 8 - (r + 1) ≤ ((A.filter (G.Adj v₀)) \ ImFinset 1 ψ).card := by omega
        have h_real : ((n / 8 - (r + 1) : ℕ) : ℝ) ≤ ((A.filter (G.Adj v₀)) \ ImFinset 1 ψ).card := by
          exact_mod_cast h_nat
        rw [Nat.cast_sub h1, Nat.cast_add, Nat.cast_one] at h_real
        linarith
      · have h_lt : (n / 8 : ℕ) < r + 1 := Nat.lt_of_not_ge h1
        have h_ltR : ((n / 8 : ℕ) : ℝ) < r + 1 := by exact_mod_cast h_lt
        have h_nonneg : (0 : ℝ) ≤ ((A.filter (G.Adj v₀)) \ ImFinset 1 ψ).card := Nat.cast_nonneg _
        linarith
    have hn_ge_1000 : (1000 : ℝ) ≤ n := by
      have : 1 ≤ L ^ 18 := Nat.one_le_pow 18 L (by omega)
      have h1 : 10 ^ 104 ≤ n := by nlinarith [hk_ge_big.trans hk_le]
      exact_mod_cast (by omega : 1000 ≤ n)
    dsimp only [Y_val, YVal]
    have hk_n_R : (k : ℝ) ≤ n := by exact_mod_cast hk_le
    linarith
  have hY_step : ∀ r' (hr' : r' < m) (hr0' : 0 < r') ψ,
      ValidPrefix A U_low G u hm_pos par r' ψ →
      ∀ v ∈ stepCand A U_low G par ψ ⟨r', hr'⟩ hr0',
      Y_val (r' + 1) (Function.update ψ ⟨r', hr'⟩ v) - Y_val r' ψ =
        if G.Adj v₀ v then -9 / 10 else 1 / 10 := by
    intro r' hr' hr0' ψ hval v hv
    have h_im_succ := imFinset_succ_update hr' ψ v
    have hv_A : v ∈ A := (mem_filter.mp (Finset.mem_sdiff.mp hv).1).1
    have hv_not_im : v ∉ ImFinset r' ψ := fun h => (Finset.mem_sdiff.mp hv).2 (mem_union_right _ h)
    have h_sdiff_succ : (A.filter (G.Adj v₀)) \ insert v (ImFinset r' ψ) =
        ((A.filter (G.Adj v₀)) \ ImFinset r' ψ).erase v := by
      ext w; simp [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert]; tauto
    have h_card_diff : (((A.filter (G.Adj v₀)) \ ImFinset (r' + 1) (Function.update ψ ⟨r', hr'⟩ v)).card : ℝ) =
        (((A.filter (G.Adj v₀)) \ ImFinset r' ψ).card : ℝ) - (if G.Adj v₀ v then 1 else 0) := by
      rw [h_im_succ, h_sdiff_succ]
      by_cases hadj : G.Adj v₀ v
      · rw [if_pos hadj]
        have hv_in : v ∈ (A.filter (G.Adj v₀)) \ ImFinset r' ψ :=
          Finset.mem_sdiff.mpr ⟨mem_filter.mpr ⟨hv_A, hadj⟩, hv_not_im⟩
        have hc := card_erase_of_mem hv_in
        have hpos : 1 ≤ ((A.filter (G.Adj v₀)) \ ImFinset r' ψ).card := Finset.card_pos.mpr ⟨v, hv_in⟩
        rw [hc, Nat.cast_sub hpos, Nat.cast_one]
      · rw [if_neg hadj]
        have hv_not : v ∉ (A.filter (G.Adj v₀)) \ ImFinset r' ψ := fun h =>
          hadj (mem_filter.mp (Finset.mem_sdiff.mp h).1).2
        rw [erase_eq_of_notMem hv_not]; ring
    dsimp only [Y_val, YVal]
    rw [h_card_diff, Nat.cast_add, Nat.cast_one]
    split_ifs <;> ring
  have h_pointwise : ∀ ψ, ValidPrefix A U_low G u hm_pos par m ψ →
      (if (((Finset.univ.filter (fun i : Fin m => G.Adj v₀ (ψ i))).sum d_seq : ℕ) : ℝ) < (s : ℝ) / 100 then (1 : ℝ) else 0) ≤
      B_sum ψ := by
    intro ψ hval
    by_cases h_bad : (((Finset.univ.filter (fun i : Fin m => G.Adj v₀ (ψ i))).sum d_seq : ℕ) : ℝ) < (s : ℝ) / 100
    · rw [if_pos h_bad]
      by_cases h_all_Y : ∀ r' ∈ Finset.Ico 1 m, -2 * μ * k < Y_val r' ψ
      · have hX_eq : ∀ i : Fin m, X_val i ψ = if G.Adj v₀ (ψ i) then (d_seq i : ℝ) else 0 := by
          intro i
          by_cases hi0 : i.1 = 0
          · have hi_eq : i = ⟨0, hm_pos⟩ := Fin.ext hi0
            rw [hi_eq]; dsimp only [X_val, XVal]
            rw [if_pos (Or.inl (hval.1 ▸ hv₀_adj_u)), if_pos (hval.1 ▸ hv₀_adj_u)]
          · have hi_mem : i.1 ∈ Finset.Ico 1 m := mem_Ico.mpr ⟨by omega, i.2⟩
            have hY_i := h_all_Y i.1 hi_mem
            have h_cand_gt : (k - i.1 : ℝ) / 25 < (((A.filter (G.Adj v₀)) \ (U_low ∪ ImFinset i.1 ψ)).card : ℝ) := by
              have h_sdiff_ge : ((A.filter (G.Adj v₀)) \ ImFinset i.1 ψ).card ≤
                  ((A.filter (G.Adj v₀)) \ (U_low ∪ ImFinset i.1 ψ)).card + U_low.card := by
                have h1 : ((A.filter (G.Adj v₀)) \ ImFinset i.1 ψ) ⊆
                    ((A.filter (G.Adj v₀)) \ (U_low ∪ ImFinset i.1 ψ)) ∪ U_low := by
                  intro w hw
                  have hw' := Finset.mem_sdiff.mp hw
                  by_cases hwU : w ∈ U_low
                  · exact mem_union_right _ hwU
                  · exact mem_union_left _ (Finset.mem_sdiff.mpr ⟨hw'.1, fun h => by
                      rcases mem_union.mp h with hU | hIm; exact hwU hU; exact hw'.2 hIm⟩)
                exact (card_le_card h1).trans (card_union_le _ _)
              have h_sdiff_R : (((A.filter (G.Adj v₀)) \ ImFinset i.1 ψ).card : ℝ) ≤
                  (((A.filter (G.Adj v₀)) \ (U_low ∪ ImFinset i.1 ψ)).card : ℝ) + U_low.card := by
                exact_mod_cast h_sdiff_ge
              have h_ki_ge_s : (s : ℝ) ≤ k - i.1 := by
                have h_im : i.1 < m := i.2
                have : i.1 + s ≤ k := by omega
                have : (i.1 : ℝ) + s ≤ k := by exact_mod_cast this
                linarith
              dsimp only [Y_val, YVal] at hY_i
              linarith
            dsimp only [X_val, XVal]
            by_cases hadj : G.Adj v₀ (ψ i)
            · rw [if_pos (Or.inl hadj), if_pos hadj]
            · rw [if_neg (by push Not; exact ⟨hadj, h_cand_gt⟩), if_neg hadj]
        have h_sum_X_le : (∑ i : Fin m, X_val i ψ) ≤ (s : ℝ) / 100 := by
          have h1 : ∑ i : Fin m, X_val i ψ =
              (((Finset.univ.filter (fun i : Fin m => G.Adj v₀ (ψ i))).sum d_seq : ℕ) : ℝ) := by
            simp_rw [hX_eq]
            rw [← Finset.sum_filter, Nat.cast_sum]
          linarith
        dsimp only [B_sum]
        rw [if_pos h_sum_X_le]
        have h_nonneg : 0 ≤ ∑ i₀ ∈ Finset.Ico 1 m, ∑ j₀ ∈ Finset.Ico (i₀ + 1) m,
            (if Rseq Y_val (-μ * k) i₀ (j₀ - i₀) ψ - Rseq Y_val (-μ * k) i₀ 0 ψ ≤ -μ * k / 2 then (1 : ℝ) else 0) :=
          Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num))
        linarith
      · push Not at h_all_Y
        obtain ⟨j₀, hj₀_mem, hj₀_le⟩ := h_all_Y
        have hj₀_ge1 : 1 ≤ j₀ := (mem_Ico.mp hj₀_mem).1
        have hj₀_lt : j₀ < m := (mem_Ico.mp hj₀_mem).2
        have hval1 : ValidPrefix A U_low G u hm_pos par 1 ψ :=
          ⟨hval.1, fun j hj => hval.2.1 j (by omega), fun j₁ j₂ h1 h2 => hval.2.2.1 j₁ j₂ (by omega) (by omega),
            fun j hj => hval.2.2.2 j (by omega)⟩
        have hY1 := hY1_nonneg ψ hval1
        let S := (Finset.Icc 1 j₀).filter (fun r' => -μ * k < Y_val r' ψ)
        have hS_ne : S.Nonempty := ⟨1, mem_filter.mpr ⟨mem_Icc.mpr ⟨le_rfl, hj₀_ge1⟩, by linarith⟩⟩
        let r_last := S.max' hS_ne
        have hr_last_mem : r_last ∈ S := S.max'_mem hS_ne
        have hr_last_lt : r_last < j₀ := by
          have h1 : r_last ≤ j₀ := (mem_Icc.mp (mem_filter.mp hr_last_mem).1).2
          have hj₀_not : j₀ ∉ S := fun h => by linarith [(mem_filter.mp h).2]
          rcases eq_or_lt_of_le h1 with heq | hlt
          · exact absurd (heq ▸ hr_last_mem) hj₀_not
          · exact hlt
        let i₀ := r_last + 1
        have hi₀_ge1 : 1 ≤ i₀ := by omega
        have hi₀_le_j₀ : i₀ ≤ j₀ := hr_last_lt
        have hY_diff_last : Y_val i₀ ψ ≥ Y_val r_last ψ - 1 := by
          have hval_r : ValidPrefix A U_low G u hm_pos par r_last ψ :=
            ⟨hval.1, fun j hj => hval.2.1 j (by omega), fun j₁ j₂ h1 h2 => hval.2.2.1 j₁ j₂ (by omega) (by omega),
              fun j hj => hval.2.2.2 j (by omega)⟩
          have h_rlast_lt : r_last < m := lt_of_lt_of_le hr_last_lt hj₀_lt.le
          have h_rlast_pos : 0 < r_last := (mem_Icc.mp (mem_filter.mp hr_last_mem).1).1
          have h_in_C : ψ ⟨r_last, h_rlast_lt⟩ ∈ stepCand A U_low G par ψ ⟨r_last, h_rlast_lt⟩ h_rlast_pos := by
            have h_mem_r : ψ ⟨r_last, h_rlast_lt⟩ ∈ A \ U_low := hval.2.1 _ (by dsimp; omega)
            have h_adj_r : G.Adj (ψ (par ⟨r_last, h_rlast_lt⟩ h_rlast_pos)) (ψ ⟨r_last, h_rlast_lt⟩) :=
              hval.2.2.2 _ (by dsimp; omega) h_rlast_pos
            refine Finset.mem_sdiff.mpr ⟨mem_filter.mpr ⟨(Finset.mem_sdiff.mp h_mem_r).1, h_adj_r⟩, ?_⟩
            intro hu
            rcases mem_union.mp hu with hU | hIm
            · exact (Finset.mem_sdiff.mp h_mem_r).2 hU
            · rcases mem_image.mp hIm with ⟨j, hj, heq⟩
              have hj_lt : j.1 < r_last := (mem_filter.mp hj).2
              have h_eq := hval.2.2.1 j ⟨r_last, h_rlast_lt⟩ (by omega) (by dsimp; omega) heq
              rw [h_eq] at hj_lt; dsimp at hj_lt; omega
          have h_upd_id : Function.update ψ ⟨r_last, h_rlast_lt⟩ (ψ ⟨r_last, h_rlast_lt⟩) = ψ :=
            Function.update_eq_self _ _
          have h_step_eq := hY_step r_last h_rlast_lt h_rlast_pos ψ hval_r _ h_in_C
          rw [h_upd_id] at h_step_eq
          split_ifs at h_step_eq <;> linarith
        have hi₀_lt_j₀ : i₀ < j₀ := by
          by_contra h_ge
          have h_eq : i₀ = j₀ := le_antisymm hi₀_le_j₀ (not_lt.mp h_ge)
          have hr_gt := (mem_filter.mp hr_last_mem).2
          linarith [h_eq ▸ hY_diff_last]
        have h_all_le : ∀ t ≤ j₀ - i₀, Y_val (i₀ + t) ψ ≤ -μ * k := by
          intro t ht
          by_contra h_gt
          push Not at h_gt
          have h_in_S : i₀ + t ∈ S := mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, by omega⟩, h_gt⟩
          have h_le_max := S.le_max' (i₀ + t) h_in_S
          omega
        have h_rseq_end := rseq_of_forall_le Y_val (-μ * k) i₀ (j₀ - i₀) ψ h_all_le
        have h_end_idx : i₀ + (j₀ - i₀) = j₀ := by omega
        rw [h_end_idx] at h_rseq_end
        have h_diff_bad : Rseq Y_val (-μ * k) i₀ (j₀ - i₀) ψ - Rseq Y_val (-μ * k) i₀ 0 ψ ≤ -μ * k / 2 := by
          have hr_gt := (mem_filter.mp hr_last_mem).2
          have h_rseq_start : Rseq Y_val (-μ * k) i₀ 0 ψ = Y_val i₀ ψ := rfl
          linarith
        have h_term_1 : (1 : ℝ) ≤ ∑ i₀' ∈ Finset.Ico 1 m, ∑ j₀' ∈ Finset.Ico (i₀' + 1) m,
            (if Rseq Y_val (-μ * k) i₀' (j₀' - i₀') ψ - Rseq Y_val (-μ * k) i₀' 0 ψ ≤ -μ * k / 2 then 1 else 0) := by
          have hi₀_mem : i₀ ∈ Finset.Ico 1 m := mem_Ico.mpr ⟨hi₀_ge1, lt_trans hi₀_lt_j₀ hj₀_lt⟩
          have hj₀_mem' : j₀ ∈ Finset.Ico (i₀ + 1) m := mem_Ico.mpr ⟨hi₀_lt_j₀, hj₀_lt⟩
          have h_inner : (1 : ℝ) ≤ ∑ j₀' ∈ Finset.Ico (i₀ + 1) m,
              (if Rseq Y_val (-μ * k) i₀ (j₀' - i₀) ψ - Rseq Y_val (-μ * k) i₀ 0 ψ ≤ -μ * k / 2 then 1 else 0) := by
            have h_s := Finset.single_le_sum (f := fun j₀' =>
              if Rseq Y_val (-μ * k) i₀ (j₀' - i₀) ψ - Rseq Y_val (-μ * k) i₀ 0 ψ ≤ -μ * k / 2 then (1 : ℝ) else 0)
              (fun _ _ => by split_ifs <;> norm_num) hj₀_mem'
            rwa [if_pos h_diff_bad] at h_s
          have h_outer := Finset.single_le_sum (f := fun i₀' => ∑ j₀' ∈ Finset.Ico (i₀' + 1) m,
            if Rseq Y_val (-μ * k) i₀' (j₀' - i₀') ψ - Rseq Y_val (-μ * k) i₀' 0 ψ ≤ -μ * k / 2 then (1 : ℝ) else 0)
            (fun _ _ => Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num)) hi₀_mem
          exact h_inner.trans h_outer
        dsimp only [B_sum]
        have h_x_nonneg : (0 : ℝ) ≤ if (∑ i : Fin m, X_val i ψ) ≤ (s : ℝ) / 100 then 1 else 0 := by
          split_ifs <;> norm_num
        linarith
    · rw [if_neg h_bad]
      dsimp only [B_sum]
      have h_x_nonneg : (0 : ℝ) ≤ if (∑ i : Fin m, X_val i ψ) ≤ (s : ℝ) / 100 then 1 else 0 := by
        split_ifs <;> norm_num
      have h_nonneg : 0 ≤ ∑ i₀ ∈ Finset.Ico 1 m, ∑ j₀ ∈ Finset.Ico (i₀ + 1) m,
          (if Rseq Y_val (-μ * k) i₀ (j₀ - i₀) ψ - Rseq Y_val (-μ * k) i₀ 0 ψ ≤ -μ * k / 2 then (1 : ℝ) else 0) :=
        Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num))
      linarith
  have h_X_b := mgf_X_bound hL hμ_def hk_pos hs_pos hs_lower hm_eq hm_pos hd_pos hd_lt h_μk_le_s
    hA huA hu_not_U hU_deg hU_card par hpar d_seq hd_sum hd_0 hd_le v₀ hv₀_adj_u
  have h_exp_B : expValFrom A U_low G par (m - 1) B_sum (fun _ => u) ≤ (d : ℝ) / (2 * k) := by
    have h_sum_R : ∑ i₀ ∈ Finset.Ico 1 m, ∑ j₀ ∈ Finset.Ico (i₀ + 1) m,
        expValFrom A U_low G par (m - 1)
          (fun ψ => if Rseq Y_val (-μ * k) i₀ (j₀ - i₀) ψ - Rseq Y_val (-μ * k) i₀ 0 ψ ≤ -μ * k / 2 then 1 else 0)
          (fun _ => u) ≤
        ∑ _i₀ ∈ Finset.Ico 1 m, ∑ _j₀ ∈ Finset.Ico (_i₀ + 1) m, (1 / (4 * (k : ℝ) ^ 3)) := by
      refine Finset.sum_le_sum (fun i₀ hi₀ => Finset.sum_le_sum (fun j₀ hj₀ => ?_))
      exact mgf_R_bound hL hμ_def hk_ge_big hk_pos hs_pos hs_upper hm_eq hm_pos h_μk_le_s
        hA huA hu_not_U hU_deg hU_card par hpar v₀ (mem_Ico.mp hi₀).1 (mem_Ico.mp hj₀).1 (mem_Ico.mp hj₀).2
    have h_count_R : (∑ _i₀ ∈ Finset.Ico 1 m, ∑ _j₀ ∈ Finset.Ico (_i₀ + 1) m, (1 / (4 * (k : ℝ) ^ 3))) ≤
        (d : ℝ) / (4 * k) := by
      have h1 : ∀ i₀ ∈ Finset.Ico 1 m, ∑ _j₀ ∈ Finset.Ico (i₀ + 1) m, (1 / (4 * (k : ℝ) ^ 3)) ≤
          (m : ℝ) * (1 / (4 * (k : ℝ) ^ 3)) := by
        intro i₀ _
        rw [Finset.sum_const, nsmul_eq_mul]
        have hcN : (Finset.Ico (i₀ + 1) m).card ≤ m :=
          (Finset.card_le_card (fun x hx => Finset.mem_range.mpr (mem_Ico.mp hx).2)).trans_eq (Finset.card_range m)
        have hc : ((Finset.Ico (i₀ + 1) m).card : ℝ) ≤ m := by exact_mod_cast hcN
        gcongr
      calc ∑ i₀ ∈ Finset.Ico 1 m, ∑ _j₀ ∈ Finset.Ico (i₀ + 1) m, (1 / (4 * (k : ℝ) ^ 3))
          ≤ ∑ _i₀ ∈ Finset.Ico 1 m, (m : ℝ) * (1 / (4 * (k : ℝ) ^ 3)) := Finset.sum_le_sum h1
        _ = ((Finset.Ico 1 m).card : ℝ) * ((m : ℝ) * (1 / (4 * (k : ℝ) ^ 3))) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (m : ℝ) * ((m : ℝ) * (1 / (4 * (k : ℝ) ^ 3))) := by
            have hcN : (Finset.Ico 1 m).card ≤ m :=
              (Finset.card_le_card (fun x hx => Finset.mem_range.mpr (mem_Ico.mp hx).2)).trans_eq (Finset.card_range m)
            have hc : ((Finset.Ico 1 m).card : ℝ) ≤ m := by exact_mod_cast hcN
            gcongr
        _ = (m : ℝ) ^ 2 * (1 / (4 * (k : ℝ) ^ 3)) := by ring
        _ ≤ (d : ℝ) / (4 * k) := by
          have hm_le_k : (m : ℝ) ≤ k := by
            have : m ≤ k := by omega
            exact_mod_cast this
          have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd_pos
          have hk_p : (0 : ℝ) < k := by exact_mod_cast hk_pos
          calc (m : ℝ) ^ 2 * (1 / (4 * (k : ℝ) ^ 3))
              ≤ (k : ℝ) ^ 2 * (1 / (4 * (k : ℝ) ^ 3)) := by gcongr
            _ = 1 / (4 * (k : ℝ)) := by field_simp
            _ ≤ (d : ℝ) / (4 * k) := div_le_div_of_nonneg_right hd1 (by positivity)
    calc expValFrom A U_low G par (m - 1) B_sum (fun _ => u)
        = expValFrom A U_low G par (m - 1) (fun ψ => if (∑ i : Fin m, X_val i ψ) ≤ (s : ℝ) / 100 then 1 else 0) (fun _ => u) +
          ∑ i₀ ∈ Finset.Ico 1 m, ∑ j₀ ∈ Finset.Ico (i₀ + 1) m,
            expValFrom A U_low G par (m - 1)
              (fun ψ => if Rseq Y_val (-μ * k) i₀ (j₀ - i₀) ψ - Rseq Y_val (-μ * k) i₀ 0 ψ ≤ -μ * k / 2 then 1 else 0)
              (fun _ => u) := by
            dsimp only [B_sum]; rw [expValFrom_add, expValFrom_sum]; simp_rw [expValFrom_sum]
      _ ≤ (d : ℝ) / (4 * k) + (d : ℝ) / (4 * k) := add_le_add h_X_b (h_sum_R.trans h_count_R)
      _ = (d : ℝ) / (2 * k) := by ring
  exact (expValFrom_mono A U_low G u hm_pos par hpar _ _ h_pointwise (m - 1) 1 (by omega) le_rfl (fun _ => u) hψ₀_val).trans h_exp_B

lemma branchB_partial_exists {L n k r m s d : ℕ} (hL : 2 ≤ L)
    {μ : ℝ} (hμ_def : μ = 1 / (10 ^ 12 * (L : ℝ) ^ 2))
    (hn_ge : 10 ^ 105 * L ^ 18 ≤ n)
    (hDr : 10 ^ 28 * L ^ 4 * r ≤ n)
    (hk_le : k ≤ n) (hkr : n < k + r)
    (hs_eq : s = k / (2 * L)) (hm_eq : m = k - s) (hm_pos : 0 < m)
    (hd_pos : 1 ≤ d) (hd_lt : (d : ℝ) < μ * k)
    {G : SimpleGraph (Fin n)} {u : Fin n} {A U_low : Finset (Fin n)}
    (hA : A.card = k) (huA : u ∈ A) (hu_adj : ∀ v ∈ A, v ≠ u → G.Adj u v)
    (hv_deg : ∀ v ∈ A, n / 8 ≤ (G.neighborSet v).ncard)
    (hu_not_U : u ∉ U_low)
    (hU_deg : ∀ v ∈ A \ U_low, ((A.filter (G.Adj v)).card : ℝ) ≥ (1 - μ / 10) * k)
    (hU_card : (U_low.card : ℝ) ≤ μ * k / 10)
    (par : ∀ i : Fin m, 0 < i.1 → Fin m) (hpar : ∀ i hi, (par i hi).1 < i.1)
    (d_seq : Fin m → ℕ) (hd_sum : ∑ i : Fin m, d_seq i = s)
    (hd_0 : d_seq ⟨0, hm_pos⟩ = d) (hd_le : ∀ i, d_seq i ≤ d) :
    ∃ ψ : Fin m → Fin n,
      ValidPrefix A U_low G u hm_pos par m ψ ∧
      ((A.erase u).filter (fun v₀ =>
        (((Finset.univ.filter (fun i : Fin m => G.Adj v₀ (ψ i))).sum d_seq : ℕ) : ℝ) < (s : ℝ) / 100)).card ≤ d := by
  classical
  obtain ⟨_, hk_ge_big, hk_pos, _, hr_le_nD, hs_lower, hs_upper, hs_pos, h_μk_ge, h_μk_le_s⟩ :=
    param_bounds hL hn_ge hDr hk_le hkr
  rw [← hμ_def] at h_μk_ge h_μk_le_s
  rw [← hs_eq] at hs_lower hs_upper hs_pos h_μk_le_s
  have h_ne : ∀ r' (hr' : r' < m) (hr0' : 0 < r') ψ,
      ValidPrefix A U_low G u hm_pos par r' ψ →
      (stepCand A U_low G par ψ ⟨r', hr'⟩ hr0').Nonempty :=
    fun r' hr' hr0' ψ hval =>
      (cand_bounds_of_valid hs_pos h_μk_le_s hm_eq hA hU_deg hU_card hm_pos par hpar hr' hr0' hval).2.2
  let badInd : Fin n → (Fin m → Fin n) → ℝ := fun v₀ ψ =>
    if (((Finset.univ.filter (fun i : Fin m => G.Adj v₀ (ψ i))).sum d_seq : ℕ) : ℝ) < (s : ℝ) / 100 then 1 else 0
  let ψ₀ : Fin m → Fin n := fun _ => u
  have hψ₀_val : ValidPrefix A U_low G u hm_pos par 1 ψ₀ :=
    ⟨rfl, fun _ _ => Finset.mem_sdiff.mpr ⟨huA, hu_not_U⟩,
      fun j₁ j₂ h1 h2 _ => Fin.ext (by omega), fun j hj hj0 => by omega⟩
  have h_per_vertex : ∀ v₀ ∈ A.erase u, expValFrom A U_low G par (m - 1) (badInd v₀) ψ₀ ≤ (d : ℝ) / (2 * k) := by
    intro v₀ hv₀
    exact per_vertex_bad_bound hL hμ_def hDr hk_le hkr hk_ge_big hk_pos hs_pos hs_lower hs_upper
      hm_eq hm_pos hd_pos hd_lt h_μk_ge h_μk_le_s hr_le_nD hA huA hv_deg hu_not_U hU_deg hU_card
      par hpar d_seq hd_sum hd_0 hd_le v₀ (mem_of_mem_erase hv₀)
      (hu_adj v₀ (mem_of_mem_erase hv₀) (mem_erase.mp hv₀).1).symm
  have h_total_exp : expValFrom A U_low G par (m - 1) (fun ψ => ∑ v₀ ∈ A.erase u, badInd v₀ ψ) ψ₀ ≤ (d : ℝ) / 2 := by
    rw [expValFrom_sum]
    calc ∑ v₀ ∈ A.erase u, expValFrom A U_low G par (m - 1) (badInd v₀) ψ₀
        ≤ ∑ _v₀ ∈ A.erase u, ((d : ℝ) / (2 * k)) := Finset.sum_le_sum h_per_vertex
      _ = ((A.erase u).card : ℝ) * ((d : ℝ) / (2 * k)) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (k : ℝ) * ((d : ℝ) / (2 * k)) := by
          gcongr
          have h1 : (A.erase u).card ≤ A.card := card_erase_le
          rw [hA] at h1; exact_mod_cast h1
      _ = (d : ℝ) / 2 := by field_simp
  obtain ⟨ψ, hψ_val, hψ_le⟩ := expValFrom_exists_le A U_low G u hm_pos par hpar h_ne
    (fun ψ => ∑ v₀ ∈ A.erase u, badInd v₀ ψ) (m - 1) 1 (by omega) le_rfl ψ₀ hψ₀_val
  have h_bad_card : ((A.erase u).filter (fun v₀ =>
      (((Finset.univ.filter (fun i : Fin m => G.Adj v₀ (ψ i))).sum d_seq : ℕ) : ℝ) < (s : ℝ) / 100)).card ≤ d := by
    have h_eq_card : (((A.erase u).filter (fun v₀ =>
        (((Finset.univ.filter (fun i : Fin m => G.Adj v₀ (ψ i))).sum d_seq : ℕ) : ℝ) < (s : ℝ) / 100)).card : ℝ) =
        ∑ v₀ ∈ A.erase u, badInd v₀ ψ := by
      dsimp only [badInd]
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    have h_le_R : (((A.erase u).filter (fun v₀ =>
        (((Finset.univ.filter (fun i : Fin m => G.Adj v₀ (ψ i))).sum d_seq : ℕ) : ℝ) < (s : ℝ) / 100)).card : ℝ) ≤ d := by
      have : (d : ℝ) / 2 ≤ d := by linarith [show (0 : ℝ) ≤ d from Nat.cast_nonneg _]
      linarith
    exact_mod_cast h_le_R
  exact ⟨ψ, hψ_val, h_bad_card⟩

lemma branchB_hall_extend {n k m s d : ℕ} {μ : ℝ}
    (hm_eq : m = k - s) (hm_pos : 0 < m) (hs_le_k : s ≤ k)
    (h_μk_le_s : μ * k ≤ (s : ℝ) / 100)
    {T : SimpleGraph (Fin k)} {G : SimpleGraph (Fin n)} {u : Fin n} {A W U_low : Finset (Fin n)}
    (hA : A.card = k) (hu_adj : ∀ v ∈ A, v ≠ u → G.Adj u v) (hWA_sub : W ∩ A ⊆ U_low)
    (hU_deg : ∀ v ∈ A \ U_low, ((A.filter (G.Adj v)).card : ℝ) ≥ (1 - μ / 10) * k)
    {t₁ : Fin k} {L_set : Finset (Fin k)}
    (hL_set_card : L_set.card = s) (hL_sub_deg1 : ∀ ℓ ∈ L_set, T.degree ℓ = 1)
    (ht₁_not_L : t₁ ∉ L_set)
    {t_seq : Fin m ↪ Fin k} {par : ∀ i : Fin m, 0 < i.1 → Fin m}
    (h_range : Set.range t_seq = ((L_setᶜ : Finset (Fin k)) : Set (Fin k)))
    (h_t0 : t_seq ⟨0, hm_pos⟩ = t₁)
    (hpar_uniq : ∀ i (hi : 0 < i.1) (j : Fin m), j.1 < i.1 → T.Adj (t_seq j) (t_seq i) → j = par i hi)
    (h_leaf_nbr_not_L : ∀ ℓ ∈ L_set, ∃! i : Fin m, T.Adj (t_seq i) ℓ)
    {d_seq : Fin m → ℕ} (hd_seq_def : ∀ i, d_seq i = (L_set.filter (T.Adj (t_seq i))).card)
    (hd_sum : ∑ i : Fin m, d_seq i = s) (hd_0 : d_seq ⟨0, hm_pos⟩ = d)
    {ψ : Fin m → Fin n} (hψ_val : ValidPrefix A U_low G u hm_pos par m ψ)
    (hψ_bad : ((A.erase u).filter (fun v₀ =>
      (((Finset.univ.filter (fun i : Fin m => G.Adj v₀ (ψ i))).sum d_seq : ℕ) : ℝ) < (s : ℝ) / 100)).card ≤ d) :
    ∃ f : Fin k ↪ Fin n,
      (∀ x, f x ∈ A) ∧ T.map f ≤ G ∧ f t₁ = u ∧
      (∀ x, x ∉ L_set → f x ∈ A \ U_low) ∧
      (∀ w ∈ W, ∀ x y, (T.map f).Adj w x → (T.map f).Adj w y → x = y) := by
  classical
  let Imψ : Finset (Fin n) := Finset.univ.image ψ
  let B : Finset (Fin n) := A \ Imψ
  have hImψ_sub : Imψ ⊆ A := by
    intro v hv
    rcases mem_image.mp hv with ⟨i, _, rfl⟩
    exact (Finset.mem_sdiff.mp (hψ_val.2.1 i i.2)).1
  have hψ_inj : Function.Injective ψ := fun i₁ i₂ h => hψ_val.2.2.1 i₁ i₂ i₁.2 i₂.2 h
  have hImψ_card : Imψ.card = m := by rw [card_image_of_injective _ hψ_inj, card_fin]
  have hB_card : B.card = s := by
    have h1 := card_sdiff_of_subset hImψ_sub
    rw [h1, hA, hImψ_card, hm_eq]
    omega
  let α := Σ i : Fin m, { ℓ : Fin k // ℓ ∈ L_set ∧ T.Adj (t_seq i) ℓ }
  let hallSets : α → Finset B := fun a => B.attach.filter (fun b => G.Adj (ψ a.1) b.1)
  have h_hall : ∀ S : Finset α, S.card ≤ (S.biUnion hallSets).card := by
    intro S
    let I : Finset (Fin m) := S.image Sigma.fst
    have hS_le_I : S.card ≤ ∑ i ∈ I, d_seq i := by
      have h_part : S = I.biUnion (fun i => S.filter (fun a => a.1 = i)) := by
        ext ⟨i, ⟨ℓ, hℓ⟩⟩
        simp only [mem_biUnion, mem_filter]
        exact ⟨fun h => ⟨i, mem_image_of_mem _ h, h, rfl⟩, fun ⟨_, _, h, _⟩ => h⟩
      have h_disj : (I : Set (Fin m)).PairwiseDisjoint (fun i => S.filter (fun a => a.1 = i)) := by
        intro i₁ _ i₂ _ hne
        rw [Function.onFun, Finset.disjoint_left]
        intro a h1 h2
        exact hne ((mem_filter.mp h1).2.symm.trans (mem_filter.mp h2).2)
      conv_lhs => rw [h_part, card_biUnion h_disj]
      refine Finset.sum_le_sum (fun i _ => ?_)
      rw [hd_seq_def]
      refine card_le_card_of_injOn (fun a => a.2.1)
        (fun a ha => mem_filter.mpr ⟨a.2.2.1, (mem_filter.mp ha).2 ▸ a.2.2.2⟩)
        (fun a₁ ha₁ a₂ ha₂ h => by
          have h1 : a₁.1 = i := (mem_filter.mp ha₁).2
          have h2 : a₂.1 = i := (mem_filter.mp ha₂).2
          rcases a₁ with ⟨i₁, ⟨ℓ₁, hℓ₁⟩⟩
          rcases a₂ with ⟨i₂, ⟨ℓ₂, hℓ₂⟩⟩
          dsimp at h1 h2 h
          subst h1 h2 h
          rfl)
    by_cases hI_empty : I = ∅
    · have hS0 : S = ∅ := by
        ext a; simp only [Finset.notMem_empty, iff_false]; intro ha
        have := mem_image_of_mem Sigma.fst ha
        change a.1 ∈ I at this
        rw [hI_empty] at this
        exact Finset.notMem_empty _ this
      rw [hS0]; simp
    have hI_ne : I.Nonempty := Finset.nonempty_iff_ne_empty.mpr hI_empty
    by_cases h_case1 : (∑ i ∈ I, d_seq i : ℝ) ≤ 99 * (s : ℝ) / 100
    · obtain ⟨j, hj⟩ := hI_ne
      obtain ⟨a₀, ha₀_S, _⟩ := mem_image.mp hj
      have h_sub_j : hallSets a₀ ⊆ S.biUnion hallSets := subset_biUnion_of_mem hallSets ha₀_S
      have h_j_card : (99 * (s : ℝ) / 100) ≤ (hallSets a₀).card := by
        have h_ψj_mem : ψ a₀.1 ∈ A \ U_low := hψ_val.2.1 a₀.1 a₀.1.2
        have h_deg_j : (1 - μ / 10) * k ≤ ((A.filter (G.Adj (ψ a₀.1))).card : ℝ) := hU_deg _ h_ψj_mem
        have h_nonadj : ((B.filter (fun b => ¬ G.Adj (ψ a₀.1) b)).card : ℝ) ≤ μ * k / 10 := by
          have hsub : B.filter (fun b => ¬ G.Adj (ψ a₀.1) b) ⊆ A.filter (fun b => ¬ G.Adj (ψ a₀.1) b) := by
            intro b hb; exact mem_filter.mpr ⟨(Finset.mem_sdiff.mp (mem_filter.mp hb).1).1, (mem_filter.mp hb).2⟩
          have h1 : (A.filter (fun b => ¬ G.Adj (ψ a₀.1) b)).card + (A.filter (G.Adj (ψ a₀.1))).card = k := by
            rw [add_comm, Finset.card_filter_add_card_filter_not, hA]
          have h2 : ((B.filter (fun b => ¬ G.Adj (ψ a₀.1) b)).card : ℝ) ≤
              (A.filter (fun b => ¬ G.Adj (ψ a₀.1) b)).card := by exact_mod_cast card_le_card hsub
          have h3 : ((A.filter (fun b => ¬ G.Adj (ψ a₀.1) b)).card : ℝ) + ((A.filter (G.Adj (ψ a₀.1))).card : ℝ) = k := by
            exact_mod_cast h1
          linarith
        have h_split_B : (hallSets a₀).card + (B.filter (fun b => ¬ G.Adj (ψ a₀.1) b)).card = s := by
          have h_eq1 : (hallSets a₀).card = (B.filter (G.Adj (ψ a₀.1))).card := by
            dsimp only [hallSets]
            refine Finset.card_bij (fun b _ => b.1) (fun b hb => mem_filter.mpr ⟨b.2, (mem_filter.mp hb).2⟩)
              (fun _ _ _ _ h => Subtype.ext h)
              (fun w hw => ⟨⟨w, (mem_filter.mp hw).1⟩, mem_filter.mpr ⟨mem_attach _ _, (mem_filter.mp hw).2⟩, rfl⟩)
          rw [h_eq1, Finset.card_filter_add_card_filter_not, hB_card]
        have h_split_BR : ((hallSets a₀).card : ℝ) + ((B.filter (fun b => ¬ G.Adj (ψ a₀.1) b)).card : ℝ) = s := by
          exact_mod_cast h_split_B
        have h_μk_10 : μ * k / 10 ≤ (s : ℝ) / 100 := by linarith
        linarith
      have h_le_R : (S.card : ℝ) ≤ (S.biUnion hallSets).card := by
        have hS_R : (S.card : ℝ) ≤ ∑ i ∈ I, (d_seq i : ℝ) := by exact_mod_cast hS_le_I
        have h_bi_R : ((hallSets a₀).card : ℝ) ≤ (S.biUnion hallSets).card := by exact_mod_cast card_le_card h_sub_j
        linarith
      exact_mod_cast h_le_R
    · push Not at h_case1
      by_cases h_case2 : ∑ i ∈ I, d_seq i ≤ s - d
      · let GoodB := B.filter (fun v₀ =>
          (s : ℝ) / 100 ≤ (((Finset.univ.filter (fun i : Fin m => G.Adj v₀ (ψ i))).sum d_seq : ℕ) : ℝ))
        have h_GoodB_card : s - d ≤ GoodB.card := by
          have h_bad_sub : B.filter (fun v₀ =>
              (((Finset.univ.filter (fun i : Fin m => G.Adj v₀ (ψ i))).sum d_seq : ℕ) : ℝ) < (s : ℝ) / 100) ⊆
              (A.erase u).filter (fun v₀ =>
                (((Finset.univ.filter (fun i : Fin m => G.Adj v₀ (ψ i))).sum d_seq : ℕ) : ℝ) < (s : ℝ) / 100) := by
            intro v₀ hv₀
            have hv₀' := mem_filter.mp hv₀
            have hv₀_B := Finset.mem_sdiff.mp hv₀'.1
            have hv₀_ne_u : v₀ ≠ u := fun h => hv₀_B.2 (h ▸ mem_image.mpr ⟨⟨0, hm_pos⟩, mem_univ _, hψ_val.1⟩)
            exact mem_filter.mpr ⟨mem_erase.mpr ⟨hv₀_ne_u, hv₀_B.1⟩, hv₀'.2⟩
          have h_bad_le : (B.filter (fun v₀ =>
              (((Finset.univ.filter (fun i : Fin m => G.Adj v₀ (ψ i))).sum d_seq : ℕ) : ℝ) < (s : ℝ) / 100)).card ≤ d :=
            (card_le_card h_bad_sub).trans hψ_bad
          have h_split := Finset.card_filter_add_card_filter_not (s := B)
            (p := fun v₀ => (((Finset.univ.filter (fun i : Fin m => G.Adj v₀ (ψ i))).sum d_seq : ℕ) : ℝ) < (s : ℝ) / 100)
          have h_eq_G : GoodB = B.filter (fun v₀ =>
              ¬ (((Finset.univ.filter (fun i : Fin m => G.Adj v₀ (ψ i))).sum d_seq : ℕ) : ℝ) < (s : ℝ) / 100) := by
            ext v₀; simp [GoodB]
          rw [← h_eq_G, hB_card] at h_split
          omega
        have h_GoodB_sub : GoodB ⊆ (S.biUnion hallSets).image Subtype.val := by
          intro v₀ hv₀
          have hv₀_B : v₀ ∈ B := (mem_filter.mp hv₀).1
          have hv₀_sum : (s : ℝ) / 100 ≤ (((Finset.univ.filter (fun i : Fin m => G.Adj v₀ (ψ i))).sum d_seq : ℕ) : ℝ) :=
            (mem_filter.mp hv₀).2
          by_contra hv₀_not
          have h_no_adj : ∀ i ∈ I, ¬ G.Adj v₀ (ψ i) := by
            intro i hi hadj
            obtain ⟨a, haS, ha_fst⟩ := mem_image.mp hi
            apply hv₀_not
            refine mem_image.mpr ⟨⟨v₀, hv₀_B⟩, mem_biUnion.mpr ⟨a, haS, ?_⟩, rfl⟩
            exact mem_filter.mpr ⟨mem_attach _ _, ha_fst ▸ hadj.symm⟩
          have h_sub_compl : Finset.univ.filter (fun i : Fin m => G.Adj v₀ (ψ i)) ⊆ Finset.univ \ I := by
            intro i hi
            exact Finset.mem_sdiff.mpr ⟨mem_univ _, fun hiI => h_no_adj i hiI (mem_filter.mp hi).2⟩
          have h_sum_compl : (Finset.univ.filter (fun i : Fin m => G.Adj v₀ (ψ i))).sum d_seq ≤
              (Finset.univ \ I).sum d_seq :=
            Finset.sum_le_sum_of_subset_of_nonneg h_sub_compl (fun _ _ _ => Nat.zero_le _)
          have h_split_sumR : (((Finset.univ \ I).sum d_seq : ℕ) : ℝ) + ∑ i ∈ I, (d_seq i : ℝ) = s := by
            rw [← Nat.cast_sum]
            exact_mod_cast (by rw [← hd_sum]; exact Finset.sum_sdiff (subset_univ I) (f := d_seq))
          have h_le_sdiffR : (((Finset.univ.filter (fun i : Fin m => G.Adj v₀ (ψ i))).sum d_seq : ℕ) : ℝ) ≤
              (((Finset.univ \ I).sum d_seq : ℕ) : ℝ) := by exact_mod_cast h_sum_compl
          linarith
        have h_GoodB_le : GoodB.card ≤ (S.biUnion hallSets).card :=
          (card_le_card h_GoodB_sub).trans Finset.card_image_le
        exact hS_le_I.trans (h_case2.trans (h_GoodB_card.trans h_GoodB_le))
      · have h0_in_I : ⟨0, hm_pos⟩ ∈ I := by
          by_contra h0_not
          have h_sub : I ⊆ Finset.univ.erase ⟨0, hm_pos⟩ :=
            fun i hi => mem_erase.mpr ⟨fun h => h0_not (h ▸ hi), mem_univ _⟩
          have h_sum_le : ∑ i ∈ I, d_seq i ≤ ∑ i ∈ Finset.univ.erase ⟨0, hm_pos⟩, d_seq i :=
            Finset.sum_le_sum_of_subset_of_nonneg h_sub (fun _ _ _ => Nat.zero_le _)
          have h_erase_sum := Finset.add_sum_erase Finset.univ d_seq (mem_univ ⟨0, hm_pos⟩)
          rw [hd_sum, hd_0] at h_erase_sum
          omega
        obtain ⟨a₀, ha₀_S, ha₀_fst⟩ := mem_image.mp h0_in_I
        have h_all_B : B.card ≤ (S.biUnion hallSets).card := by
          have h_eq_univ : hallSets a₀ = Finset.univ := by
            ext b
            simp only [hallSets, mem_filter, mem_attach, true_and, mem_univ, iff_true]
            rw [ha₀_fst, hψ_val.1]
            have hb_A : b.1 ∈ A := (Finset.mem_sdiff.mp b.2).1
            have hb_ne_u : b.1 ≠ u := fun h => (Finset.mem_sdiff.mp b.2).2 (h ▸ mem_image.mpr ⟨⟨0, hm_pos⟩, mem_univ _, hψ_val.1⟩)
            exact hu_adj b.1 hb_A hb_ne_u
          have h1 : (Finset.univ : Finset B).card ≤ (S.biUnion hallSets).card :=
            h_eq_univ ▸ card_le_card (subset_biUnion_of_mem hallSets ha₀_S)
          simpa using h1
        have h_sum_le_s : ∑ i ∈ I, d_seq i ≤ s := by
          rw [← hd_sum]
          exact Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => Nat.zero_le _)
        exact hS_le_I.trans (h_sum_le_s.trans (hB_card ▸ h_all_B))
  obtain ⟨g, hg_inj, hg_mem⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' hallSets).mp h_hall
  have hg_adj : ∀ a : α, G.Adj (ψ a.1) (g a).1 := fun a => (mem_filter.mp (hg_mem a)).2
  have h_inv_t : ∀ x : Fin k, x ∉ L_set → ∃ i : Fin m, t_seq i = x := by
    intro x hx
    have hx_mem : x ∈ ((L_setᶜ : Finset (Fin k)) : Set (Fin k)) := mem_compl.mpr hx
    rw [← h_range] at hx_mem
    exact hx_mem
  let fFun : Fin k → Fin n := fun x =>
    if hx : x ∈ L_set then
      let i := (h_leaf_nbr_not_L x hx).choose
      (g ⟨i, x, hx, (h_leaf_nbr_not_L x hx).choose_spec.1⟩).1
    else ψ (h_inv_t x hx).choose
  have hf_inj : Function.Injective fFun := by
    intro x₁ x₂ heq
    dsimp only [fFun] at heq
    by_cases h1 : x₁ ∈ L_set <;> by_cases h2 : x₂ ∈ L_set
    · rw [dif_pos h1, dif_pos h2] at heq
      exact congrArg (fun a : α => a.2.1) (hg_inj (Subtype.ext heq))
    · exfalso
      rw [dif_pos h1, dif_neg h2] at heq
      have hB_mem := (g ⟨_, x₁, h1, (h_leaf_nbr_not_L x₁ h1).choose_spec.1⟩).2
      rw [heq] at hB_mem
      exact (Finset.mem_sdiff.mp hB_mem).2 (mem_image_of_mem ψ (mem_univ _))
    · exfalso
      rw [dif_neg h1, dif_pos h2] at heq
      have hB_mem := (g ⟨_, x₂, h2, (h_leaf_nbr_not_L x₂ h2).choose_spec.1⟩).2
      rw [← heq] at hB_mem
      exact (Finset.mem_sdiff.mp hB_mem).2 (mem_image_of_mem ψ (mem_univ _))
    · rw [dif_neg h1, dif_neg h2] at heq
      have hi := hψ_inj heq
      have h1' := (h_inv_t x₁ h1).choose_spec
      have h2' := (h_inv_t x₂ h2).choose_spec
      rw [← h1', ← h2', hi]
  let f : Fin k ↪ Fin n := ⟨fFun, hf_inj⟩
  have hf_L : ∀ x (hx : x ∈ L_set), ∃ (i : Fin m) (hadj : T.Adj (t_seq i) x),
      f x = (g ⟨i, x, hx, hadj⟩).1 := fun x hx =>
    ⟨(h_leaf_nbr_not_L x hx).choose, (h_leaf_nbr_not_L x hx).choose_spec.1, dif_pos hx⟩
  have hf_not_L : ∀ x (hx : x ∉ L_set), ∃ i : Fin m, f x = ψ i ∧ t_seq i = x := fun x hx =>
    ⟨(h_inv_t x hx).choose, dif_neg hx, (h_inv_t x hx).choose_spec⟩
  have hf_t₁ : f t₁ = u := by
    obtain ⟨i, hfi, hti⟩ := hf_not_L t₁ ht₁_not_L
    have hi0 : i = ⟨0, hm_pos⟩ := t_seq.injective (hti.trans h_t0.symm)
    rw [hfi, hi0, hψ_val.1]
  have hf_A : ∀ x, f x ∈ A := by
    intro x
    by_cases hx : x ∈ L_set
    · obtain ⟨i, hadj, hfx⟩ := hf_L x hx
      rw [hfx]
      exact (Finset.mem_sdiff.mp (g ⟨i, x, hx, hadj⟩).2).1
    · obtain ⟨i, hfi, _⟩ := hf_not_L x hx
      rw [hfi]
      exact (Finset.mem_sdiff.mp (hψ_val.2.1 i i.2)).1
  have hψ_adj : ∀ i j : Fin m, T.Adj (t_seq i) (t_seq j) → G.Adj (ψ i) (ψ j) := by
    intro i j hadj
    rcases lt_trichotomy i.1 j.1 with hij | hij | hij
    · have hj_pos : 0 < j.1 := by omega
      have h_eq := hpar_uniq j hj_pos i hij hadj
      subst h_eq
      exact hψ_val.2.2.2 j j.2 hj_pos
    · have hij' : i = j := Fin.ext hij
      subst hij'
      exact absurd hadj (fun h => T.ne_of_adj h rfl)
    · have hi_pos : 0 < i.1 := by omega
      have h_eq := hpar_uniq i hi_pos j hij hadj.symm
      subst h_eq
      exact (hψ_val.2.2.2 i i.2 hi_pos).symm
  have hU_le_G : T.map f ≤ G := by
    intro a b hab
    rcases (map_adj f T a b).mp hab with ⟨x, y, hadj, rfl, rfl⟩
    by_cases hx : x ∈ L_set <;> by_cases hy : y ∈ L_set
    · exfalso
      obtain ⟨i, hi_adj, _⟩ := h_leaf_nbr_not_L x hx
      have hdeg := hL_sub_deg1 x hx
      rw [degree_eq_one_iff_existsUnique_adj] at hdeg
      rcases hdeg with ⟨w, _, hw_uniq⟩
      have hy_eq : y = t_seq i := (hw_uniq y hadj).trans (hw_uniq (t_seq i) hi_adj.symm).symm
      have hy_not : y ∉ L_set := by
        have : t_seq i ∈ ((L_setᶜ : Finset (Fin k)) : Set (Fin k)) := h_range ▸ Set.mem_range_self i
        exact hy_eq ▸ mem_compl.mp this
      exact hy_not hy
    · obtain ⟨i, h_iadj, hfx⟩ := hf_L x hx
      obtain ⟨j, hfy, htj⟩ := hf_not_L y hy
      have hij : j = i := by
        obtain ⟨_, _, huniq⟩ := h_leaf_nbr_not_L x hx
        exact (huniq j (show T.Adj (t_seq j) x by rw [htj]; exact hadj.symm)).trans
          (huniq i h_iadj).symm
      rw [hfx, hfy, hij]
      exact (hg_adj ⟨i, x, hx, h_iadj⟩).symm
    · obtain ⟨i, hfx, hti⟩ := hf_not_L x hx
      obtain ⟨j, h_jadj, hfy⟩ := hf_L y hy
      have hij : i = j := by
        obtain ⟨_, _, huniq⟩ := h_leaf_nbr_not_L y hy
        exact (huniq i (show T.Adj (t_seq i) y by rw [hti]; exact hadj)).trans
          (huniq j h_jadj).symm
      rw [hfx, hfy, hij]
      exact hg_adj ⟨j, y, hy, h_jadj⟩
    · obtain ⟨i, hfi, hti⟩ := hf_not_L x hx
      obtain ⟨j, hfj, htj⟩ := hf_not_L y hy
      rw [hfi, hfj]
      exact hψ_adj i j (hti ▸ htj ▸ hadj)
  have hf_notL_mem : ∀ x, x ∉ L_set → f x ∈ A \ U_low := by
    intro x hx
    obtain ⟨i, hfi, _⟩ := hf_not_L x hx
    rw [hfi]
    exact hψ_val.2.1 i i.2
  have hW_uniq : ∀ w ∈ W, ∀ x y, (T.map f).Adj w x → (T.map f).Adj w y → x = y := by
    intro w hw x y hwx hwy
    rcases (map_adj f T w x).mp hwx with ⟨a, a', hTa, hfa, rfl⟩
    rcases (map_adj f T w y).mp hwy with ⟨b, b', hTb, hfb, rfl⟩
    have ha_eq_b : a = b := f.injective (hfa.trans hfb.symm)
    subst ha_eq_b
    have ha_L : a ∈ L_set := by
      by_contra ha_not
      have hw_not_U : w ∉ U_low := (Finset.mem_sdiff.mp (hfa ▸ hf_notL_mem a ha_not)).2
      have hw_A : w ∈ A := hfa ▸ hf_A a
      exact hw_not_U (hWA_sub (mem_inter.mpr ⟨hw, hw_A⟩))
    have hdeg := hL_sub_deg1 a ha_L
    rw [degree_eq_one_iff_existsUnique_adj] at hdeg
    rcases hdeg with ⟨_, _, huniq⟩
    rw [(huniq a' hTa).trans (huniq b' hTb).symm]
  exact ⟨f, hf_A, hU_le_G, hf_t₁, hf_notL_mem, hW_uniq⟩

lemma branchB_embed {L n k r : ℕ} (hL : 2 ≤ L)
    {μ : ℝ} (hμ_def : μ = 1 / (10 ^ 12 * (L : ℝ) ^ 2))
    (hn_ge : 10 ^ 105 * L ^ 18 ≤ n)
    (hDr : 10 ^ 28 * L ^ 4 * r ≤ n)
    (hk_le : k ≤ n) (hkr : n < k + r)
    {T : SimpleGraph (Fin k)} (hT : T.IsTree)
    (hLeaves_gt : n / L < (Finset.univ.filter (fun v => T.degree v = 1)).card)
    (t₁ : Fin k)
    (ht₁ : ∀ x : Fin k, ((Finset.univ.filter (fun v => T.degree v = 1)).filter (T.Adj x)).card ≤
      ((Finset.univ.filter (fun v => T.degree v = 1)).filter (T.Adj t₁)).card)
    (hd_lt : (((Finset.univ.filter (fun v => T.degree v = 1)).filter (T.Adj t₁)).card : ℝ) < μ * k)
    {G : SimpleGraph (Fin n)} {u : Fin n} {A W : Finset (Fin n)}
    (hA : A.card = k) (huA : u ∈ A) (hu_adj : ∀ v ∈ A, v ≠ u → G.Adj u v)
    (hv_deg : ∀ v ∈ A, n / 8 ≤ (G.neighborSet v).ncard)
    (_huW : u ∉ W)
    {U_low : Finset (Fin n)} (_hU_sub : U_low ⊆ A) (hu_not_U : u ∉ U_low)
    (hWA_sub : W ∩ A ⊆ U_low)
    (hU_deg : ∀ v ∈ A \ U_low, ((A.filter (G.Adj v)).card : ℝ) ≥ (1 - μ / 10) * k)
    (hU_card : (U_low.card : ℝ) ≤ μ * k / 10) :
    ∃ f : Fin k ↪ Fin n, let U := T.map f
      (∀ x, f x ∈ A) ∧ U ≤ G ∧
      (∀ w ∈ W, ∀ x y, U.Adj w x → U.Adj w y → x = y) ∧
      (∀ v ≠ u, min ((G.neighborSet v).ncard - 1) (n / 5) ≤ ((G \ U).neighborSet v).ncard) ∧
      (n / 5 ≤ ((G \ U).neighborSet u).ncard ∨ ∀ w ∈ W, ∀ x, U.Adj w x → x = u) := by
  classical
  obtain ⟨hk_ge_n2, hk_ge_big, hk_pos, h_kn99, hr_le_nD, hs_lower, hs_upper, hs_pos, _, h_μk_le_s⟩ :=
    param_bounds hL hn_ge hDr hk_le hkr
  rw [← hμ_def] at h_μk_le_s
  have hμ_pos : 0 < μ := by rw [hμ_def]; positivity
  let Leaves : Finset (Fin k) := Finset.univ.filter (fun v => T.degree v = 1)
  let L₀ : Finset (Fin k) := Leaves.filter (T.Adj t₁)
  let d : ℕ := L₀.card
  have hk_ge_2 : 2 ≤ k := by
    have : 1 ≤ L ^ 18 := Nat.one_le_pow 18 L (by omega)
    nlinarith
  have hd_pos : 1 ≤ d := by
    have : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.mpr hk_ge_2
    obtain ⟨ℓ, hℓ⟩ := hT.exists_vert_degree_one_of_nontrivial
    have hℓ_mem : ℓ ∈ Leaves := mem_filter.mpr ⟨mem_univ _, hℓ⟩
    have h_nbr : (T.neighborFinset ℓ).Nonempty := by
      rw [← Finset.card_pos, card_neighborFinset_eq_degree, hℓ]; exact zero_lt_one
    rcases h_nbr with ⟨t, ht⟩
    have hadj : T.Adj t ℓ := ((mem_neighborFinset T ℓ t).mp ht).symm
    have hle1 : 1 ≤ (Leaves.filter (T.Adj t)).card :=
      Finset.card_pos.mpr ⟨ℓ, mem_filter.mpr ⟨hℓ_mem, hadj⟩⟩
    exact hle1.trans (ht₁ t)
  let s : ℕ := k / (2 * L)
  have hd_lt_s : d < s := by
    have h1 : (d : ℝ) < μ * k := hd_lt
    have h2 : μ * k < (k : ℝ) / (3 * L) := by
      rw [hμ_def]
      have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast hL
      have : 3 * (L : ℝ) < 10 ^ 12 * (L : ℝ) ^ 2 := by nlinarith
      rw [mul_comm, ← div_eq_mul_one_div]
      exact div_lt_div_of_pos_left (by positivity) (by positivity) this
    exact_mod_cast (h1.trans h2).trans_le hs_lower
  have hs_le_erase : s ≤ (Leaves.erase t₁).card := by
    have h_k_div : k / L ≤ n / L := Nat.div_le_div_right hk_le
    have h_L_gt : k / L + 1 ≤ Leaves.card := Nat.lt_of_le_of_lt h_k_div hLeaves_gt
    have h_erase : k / L ≤ (Leaves.erase t₁).card := by
      by_cases ht1_L : t₁ ∈ Leaves
      · have h2 := card_erase_of_mem ht1_L; omega
      · rw [erase_eq_of_notMem ht1_L]; omega
    have h_s_le : s ≤ k / L := Nat.div_le_div_left (by omega : L ≤ 2 * L) (by omega)
    exact h_s_le.trans h_erase
  have hL₀_sub_erase : L₀ ⊆ Leaves.erase t₁ := by
    intro ℓ hℓ
    have hℓ' := mem_filter.mp hℓ
    exact mem_erase.mpr ⟨(T.ne_of_adj hℓ'.2).symm, hℓ'.1⟩
  obtain ⟨L_rem, hL_rem_sub, hL_rem_card⟩ :=
    Finset.exists_subset_card_eq (show s - d ≤ ((Leaves.erase t₁) \ L₀).card by
      rw [card_sdiff_of_subset hL₀_sub_erase]; omega)
  let L_set : Finset (Fin k) := L₀ ∪ L_rem
  have hL_set_sub : L_set ⊆ Leaves.erase t₁ := union_subset hL₀_sub_erase (hL_rem_sub.trans sdiff_subset)
  have hL_set_card : L_set.card = s := by
    rw [card_union_of_disjoint (Finset.disjoint_left.mpr fun ℓ h1 h2 =>
      (Finset.mem_sdiff.mp (hL_rem_sub h2)).2 h1), hL_rem_card]
    omega
  have hL_sub_deg1 : ∀ ℓ ∈ L_set, T.degree ℓ = 1 := fun ℓ hℓ =>
    (mem_filter.mp (mem_of_mem_erase (hL_set_sub hℓ))).2
  have ht₁_not_L : t₁ ∉ L_set := fun h => (mem_erase.mp (hL_set_sub h)).1 rfl
  obtain ⟨m, hm_eq, hm_pos, t_seq, par, h_range, h_t0, hpar, hpar_uniq⟩ :=
    tree_ordering_after_removing_leaves hT t₁ L_set hL_sub_deg1 ht₁_not_L
  rw [hL_set_card] at hm_eq
  have h_leaf_nbr_not_L : ∀ ℓ ∈ L_set, ∃! i : Fin m, T.Adj (t_seq i) ℓ := by
    intro ℓ hℓ
    have hdeg := hL_sub_deg1 ℓ hℓ
    rw [degree_eq_one_iff_existsUnique_adj] at hdeg
    rcases hdeg with ⟨x, hTx, huniq⟩
    have hx_not_L : x ∉ L_set := by
      intro hxL
      have hx_deg := hL_sub_deg1 x hxL
      rw [degree_eq_one_iff_existsUnique_adj] at hx_deg
      rcases hx_deg with ⟨_, _, hx_uniq⟩
      have hk_ge_3 : 3 ≤ k := by
        have : 1 ≤ L ^ 18 := Nat.one_le_pow 18 L (by omega)
        nlinarith
      have h_exists_z : ∃ z : Fin k, z ≠ ℓ ∧ z ≠ x := by
        have h_nonempty : (Finset.univ \ ({ℓ, x} : Finset (Fin k))).Nonempty := by
          rw [← Finset.card_pos, card_sdiff_of_subset (subset_univ _), card_fin]
          have h_card : ({ℓ, x} : Finset (Fin k)).card ≤ 2 := (card_insert_le _ _).trans (by simp)
          omega
        obtain ⟨z, hz⟩ := h_nonempty
        have hz' := Finset.mem_sdiff.mp hz
        exact ⟨z, fun h => hz'.2 (by simp [h]), fun h => hz'.2 (by simp [h])⟩
      rcases h_exists_z with ⟨z, hz_l, hz_x⟩
      obtain ⟨p, hp⟩ := (hT.existsUnique_path ℓ z).exists
      have h_nodup := hp.support_nodup
      cases p with
      | nil => exact absurd rfl hz_l.symm
      | cons h1 q =>
        have hv1 := huniq _ h1
        cases q with
        | nil => exact hz_x hv1
        | cons h2 r =>
          have hv2 := (hx_uniq _ (hv1 ▸ h2)).trans (hx_uniq ℓ hTx.symm).symm
          rw [Walk.support_cons, List.nodup_cons] at h_nodup
          exact h_nodup.1 (by rw [Walk.support_cons, List.mem_cons]; exact Or.inr (hv2 ▸ r.start_mem_support))
    have hx_mem : x ∈ ((L_setᶜ : Finset (Fin k)) : Set (Fin k)) := mem_compl.mpr hx_not_L
    rw [← h_range] at hx_mem
    rcases hx_mem with ⟨i, rfl⟩
    refine ⟨i, hTx.symm, fun j hj => t_seq.injective (huniq (t_seq j) hj.symm)⟩
  let d_seq : Fin m → ℕ := fun i => (L_set.filter (T.Adj (t_seq i))).card
  have hd_sum : ∑ i : Fin m, d_seq i = s := by
    have h_part : L_set = Finset.univ.biUnion (fun i : Fin m => L_set.filter (T.Adj (t_seq i))) := by
      ext ℓ
      simp only [mem_biUnion, mem_univ, true_and, mem_filter]
      constructor
      · intro hℓ
        obtain ⟨i, hi, _⟩ := h_leaf_nbr_not_L ℓ hℓ
        exact ⟨i, hℓ, hi⟩
      · rintro ⟨i, hℓ, _⟩; exact hℓ
    have h_disj : ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint
        (fun i => L_set.filter (T.Adj (t_seq i))) := by
      intro i₁ _ i₂ _ hne
      rw [Function.onFun, Finset.disjoint_left]
      intro ℓ h1 h2
      obtain ⟨_, _, huniq⟩ := h_leaf_nbr_not_L ℓ (mem_filter.mp h1).1
      exact hne ((huniq i₁ (mem_filter.mp h1).2).trans (huniq i₂ (mem_filter.mp h2).2).symm)
    rw [← hL_set_card]
    change (∑ i : Fin m, (L_set.filter (T.Adj (t_seq i))).card) = L_set.card
    rw [← Finset.card_biUnion h_disj, ← h_part]
  have hd_0 : d_seq ⟨0, hm_pos⟩ = d := by
    dsimp only [d_seq, d]
    rw [h_t0]
    congr 1
    ext ℓ
    simp only [mem_filter, L₀, Leaves, mem_univ, true_and]
    exact ⟨fun ⟨hℓ, hadj⟩ => ⟨hL_sub_deg1 ℓ hℓ, hadj⟩,
           fun ⟨hdeg, hadj⟩ => ⟨mem_union_left _ (mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, hdeg⟩, hadj⟩), hadj⟩⟩
  have hd_le : ∀ i : Fin m, d_seq i ≤ d := by
    intro i
    dsimp only [d_seq, d]
    have h_sub : L_set.filter (T.Adj (t_seq i)) ⊆ Leaves.filter (T.Adj (t_seq i)) := by
      intro ℓ hℓ
      have hℓ' := mem_filter.mp hℓ
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ ℓ, hL_sub_deg1 ℓ hℓ'.1⟩, hℓ'.2⟩
    exact (card_le_card h_sub).trans (ht₁ (t_seq i))
  obtain ⟨ψ, hψ_val, hψ_bad⟩ := branchB_partial_exists hL hμ_def hn_ge hDr hk_le hkr
    rfl hm_eq hm_pos hd_pos hd_lt hA huA hu_adj hv_deg hu_not_U hU_deg hU_card par
    (fun i hi => (hpar i hi).1) d_seq hd_sum hd_0 hd_le
  have hs_le_k : s ≤ k := Nat.div_le_self k (2 * L)
  obtain ⟨f, hf_A, hU_le_G, hf_t₁, hf_notL_mem, hW_uniq⟩ := branchB_hall_extend
    hm_eq hm_pos hs_le_k h_μk_le_s hA hu_adj hWA_sub hU_deg hL_set_card hL_sub_deg1 ht₁_not_L
    h_range h_t0 hpar_uniq h_leaf_nbr_not_L (fun _ => rfl) hd_sum hd_0 hψ_val hψ_bad
  have hT_deg_all : ∀ x : Fin k, (T.degree x : ℝ) < 3 * (k : ℝ) / 5 := by
    intro x
    have h1 := tree_two_mul_degree_le_add_leafDeg hT x
    change 2 * T.degree x ≤ k - 1 + (Leaves.filter (T.Adj x)).card at h1
    have h2 : ((Leaves.filter (T.Adj x)).card : ℝ) < μ * k :=
      (by exact_mod_cast ht₁ x : (((Leaves.filter (T.Adj x)).card : ℝ) ≤ L₀.card)).trans_lt hd_lt
    have h1R : 2 * (T.degree x : ℝ) ≤ k + ((Leaves.filter (T.Adj x)).card : ℝ) := by
      exact_mod_cast (by omega : 2 * T.degree x ≤ k + (Leaves.filter (T.Adj x)).card)
    have hμ_small : μ * k ≤ k / 10 := by
      rw [hμ_def]
      have : 1 / (10 ^ 12 * (L : ℝ) ^ 2) ≤ 1 / 10 :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity) (by
          have : (2 : ℝ) ≤ L := by exact_mod_cast hL
          nlinarith)
      exact (mul_le_mul_of_nonneg_right this (Nat.cast_nonneg k)).trans_eq (by ring)
    linarith
  have h_diff_eq : ∀ v : Fin n, ((G \ T.map f).neighborSet v).ncard =
      (G.neighborSet v).ncard - ((T.map f).neighborSet v).ncard := by
    intro v
    have h_sub : (T.map f).neighborFinset v ⊆ G.neighborFinset v := fun z hz =>
      (mem_neighborFinset G v z).mpr (hU_le_G ((mem_neighborFinset (T.map f) v z).mp hz))
    have h_eq : (G \ T.map f).neighborFinset v = G.neighborFinset v \ (T.map f).neighborFinset v := by
      ext z; simp [mem_neighborFinset]
    have hc1 : ((G \ T.map f).neighborSet v).ncard = ((G \ T.map f).neighborFinset v).card := by
      rw [← Set.ncard_coe_finset ((G \ T.map f).neighborFinset v), coe_neighborFinset]
    have hc2 : (G.neighborSet v).ncard = (G.neighborFinset v).card := by
      rw [← Set.ncard_coe_finset (G.neighborFinset v), coe_neighborFinset]
    have hc3 : ((T.map f).neighborSet v).ncard = ((T.map f).neighborFinset v).card := by
      rw [← Set.ncard_coe_finset ((T.map f).neighborFinset v), coe_neighborFinset]
    rw [hc1, hc2, hc3, h_eq, card_sdiff_of_subset h_sub]
  have h_map_deg : ∀ x : Fin k, ((T.map f).neighborSet (f x)).ncard = T.degree x := by
    intro x
    have hc : (T.neighborSet x).ncard = (T.neighborFinset x).card := by
      rw [← Set.ncard_coe_finset (T.neighborFinset x), coe_neighborFinset]
    rw [neighborSet_map, Set.ncard_image_of_injective _ f.injective, hc]
    convert card_neighborFinset_eq_degree (G := T) (v := x)
  have hμk_100 : μ * k ≤ k / 100 := by
    rw [hμ_def]
    have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast hL
    have h1 : 1 / (10 ^ 12 * (L : ℝ) ^ 2) ≤ 1 / 100 :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) (by nlinarith)
    exact (mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg k)).trans_eq (by ring)
  have hn5_le : ((n / 5 : ℕ) : ℝ) ≤ (n : ℝ) / 5 := by
    have : ((n / 5 : ℕ) : ℝ) * 5 ≤ n := by exact_mod_cast Nat.div_mul_le_self n 5
    linarith
  refine ⟨f, hf_A, hU_le_G, hW_uniq, ?_, Or.inl ?_⟩
  · intro v _
    by_cases hv_range : v ∈ Set.range f
    · rcases hv_range with ⟨x, rfl⟩
      rw [h_diff_eq, h_map_deg]
      by_cases hx : x ∈ L_set
      · rw [hL_sub_deg1 x hx]; exact min_le_left _ _
      · have hG_deg : ((A.filter (G.Adj (f x))).card : ℝ) ≥ k - μ * k / 10 := by
          have := hU_deg (f x) (hf_notL_mem x hx)
          linarith
        have hG_ncard : (A.filter (G.Adj (f x))).card ≤ (G.neighborSet (f x)).ncard := by
          have hc : (G.neighborSet (f x)).ncard = (G.neighborFinset (f x)).card := by
            rw [← Set.ncard_coe_finset (G.neighborFinset (f x)), coe_neighborFinset]
          rw [hc]
          exact card_le_card (fun z hz => (mem_neighborFinset G (f x) z).mpr (mem_filter.mp hz).2)
        have hG_R : (k : ℝ) - μ * k / 10 ≤ (G.neighborSet (f x)).ncard :=
          hG_deg.trans (by exact_mod_cast hG_ncard)
        have hT_R := hT_deg_all x
        have h_add_R : ((n / 5 + T.degree x : ℕ) : ℝ) ≤ ((G.neighborSet (f x)).ncard : ℝ) := by
          rw [Nat.cast_add]; linarith
        have h_add_N : n / 5 + T.degree x ≤ (G.neighborSet (f x)).ncard := by exact_mod_cast h_add_R
        exact le_trans (min_le_right _ _) (by omega)
    · have hU_empty : (T.map f).neighborSet v = ∅ := by
        ext z
        simp only [mem_neighborSet, map_adj, Set.mem_empty_iff_false, iff_false, not_exists, not_and]
        intro x _ _ hfx _
        exact hv_range ⟨x, hfx⟩
      rw [h_diff_eq, hU_empty, Set.ncard_empty, Nat.sub_zero]
      exact le_trans (min_le_left _ _) (Nat.sub_le _ _)
  · rw [← hf_t₁, h_diff_eq, h_map_deg]
    have hGu_ge : k - 1 ≤ (G.neighborSet (f t₁)).ncard := by
      have hc : (G.neighborSet (f t₁)).ncard = (G.neighborFinset (f t₁)).card := by
        rw [← Set.ncard_coe_finset (G.neighborFinset (f t₁)), coe_neighborFinset]
      rw [hc]
      have h_sub : A.erase u ⊆ G.neighborFinset (f t₁) := by
        intro v hv
        rw [hf_t₁]
        exact (mem_neighborFinset G u v).mpr (hu_adj v (mem_of_mem_erase hv) (mem_erase.mp hv).1)
      have h1 := card_le_card h_sub
      rw [card_erase_of_mem huA, hA] at h1
      exact h1
    have hT_R := hT_deg_all t₁
    have hGu_R : (k : ℝ) - 1 ≤ (G.neighborSet (f t₁)).ncard := by
      have h1 : ((k - 1 : ℕ) : ℝ) ≤ (G.neighborSet (f t₁)).ncard := by exact_mod_cast hGu_ge
      rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one] at h1
      exact h1
    have hk_ge_100_N : 100 ≤ k := by
      have h1 : 1 ≤ L ^ 18 := Nat.one_le_pow 18 L (by omega)
      have h2 : 100 ≤ 10 ^ 104 * L ^ 18 := Nat.le_trans (by norm_num) (Nat.le_mul_of_pos_right (10 ^ 104) h1)
      exact le_trans h2 hk_ge_big
    have hk_ge_100 : (100 : ℝ) ≤ k := by exact_mod_cast hk_ge_100_N
    have h_add_R : ((n / 5 + T.degree t₁ : ℕ) : ℝ) ≤ ((G.neighborSet (f t₁)).ncard : ℝ) := by
      rw [Nat.cast_add]; linarith
    have h_add_N : n / 5 + T.degree t₁ ≤ (G.neighborSet (f t₁)).ncard := by exact_mod_cast h_add_R
    omega

end Erdos743H2

theorem OMA.solution : OMA.R_Erdos743_erdos_743_variants_largest_trees_R1.H2 := by
  classical
  intro L hL
  refine ⟨10 ^ 28 * L ^ 4, by positivity, ?_⟩
  rw [Filter.eventually_atTop]
  refine ⟨10 ^ 105 * L ^ 18, fun n hn_ge r k hDr _ hk_le hkr T hT hLeaves_gt G u A W hGc hA huA hu_adj hv_deg hW huW _ => ?_⟩
  let μ : ℝ := 1 / (10 ^ 12 * (L : ℝ) ^ 2)
  have hμ_def : μ = 1 / (10 ^ 12 * (L : ℝ) ^ 2) := rfl
  have hμ_pos : 0 < μ := by positivity
  have hμ_lt : μ < 1 / 100 := by
    have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast hL
    rw [hμ_def, div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  obtain ⟨hk_ge_n2, _, hk_pos, h_kn99, hr_le_nD, _, _, _, h_μk_ge, _⟩ :=
    Erdos743H2.param_bounds hL hn_ge hDr hk_le hkr
  rw [← hμ_def] at h_μk_ge
  have hk_ge_20 : (20 : ℝ) ≤ μ * k := by linarith
  let U_deg := (A.erase u).filter (fun v => ((A.filter (G.Adj v)).card : ℝ) < (1 - μ / 10) * k)
  let U_low := U_deg ∪ (W ∩ A)
  have hU_sub : U_low ⊆ A := union_subset ((filter_subset _ _).trans (erase_subset _ _)) inter_subset_right
  have hu_not_U : u ∉ U_low := by
    intro hu
    rcases mem_union.mp hu with h1 | h2
    · exact (mem_erase.mp (mem_filter.mp h1).1).1 rfl
    · exact huW (mem_inter.mp h2).1
  have hWA_sub : W ∩ A ⊆ U_low := subset_union_right
  have hU_deg : ∀ v ∈ A \ U_low, ((A.filter (G.Adj v)).card : ℝ) ≥ (1 - μ / 10) * k := by
    intro v hv
    have hvA : v ∈ A := (Finset.mem_sdiff.mp hv).1
    have hv_not : v ∉ U_low := (Finset.mem_sdiff.mp hv).2
    by_cases hvu : v = u
    · rw [hvu]
      have h_sub : A.erase u ⊆ A.filter (G.Adj u) := fun w hw =>
        mem_filter.mpr ⟨mem_of_mem_erase hw, hu_adj w (mem_of_mem_erase hw) (mem_erase.mp hw).1⟩
      have h1 : k - 1 ≤ (A.filter (G.Adj u)).card := by
        have h2 := card_le_card h_sub
        rw [card_erase_of_mem huA, hA] at h2
        exact h2
      have h1R : (k : ℝ) - 1 ≤ (A.filter (G.Adj u)).card := by
        have h2 : ((k - 1 : ℕ) : ℝ) ≤ (A.filter (G.Adj u)).card := by exact_mod_cast h1
        rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one] at h2
        exact h2
      linarith
    · by_contra hlt
      push Not at hlt
      exact hv_not (mem_union_left _ (mem_filter.mpr ⟨mem_erase.mpr ⟨hvu, hvA⟩, hlt⟩))
  have hU_card : (U_low.card : ℝ) ≤ μ * k / 10 := by
    have h1 := Erdos743H2.ulow_card_le hμ_pos hk_pos hk_ge_20 hGc (u := u) hA hW
    have hn_le_2k : (n : ℝ) ≤ 2 * k := by exact_mod_cast hk_ge_n2
    have h_40 : 40 * (n : ℝ) / (μ * k) + 1 ≤ 81 / μ := by
      have h_n_k : 40 * (n : ℝ) / (μ * k) ≤ 80 / μ := by
        rw [div_le_div_iff₀ (by positivity) hμ_pos]
        nlinarith
      have h_1_μ : (1 : ℝ) ≤ 1 / μ := by rw [le_div_iff₀ hμ_pos]; linarith
      linarith [show (80 : ℝ) / μ + 1 / μ = 81 / μ by ring]
    have h_r_nonneg : (0 : ℝ) ≤ r := Nat.cast_nonneg _
    have h_prod : (40 * (n : ℝ) / (μ * k) + 1) * r ≤ (81 / μ) * ((2 * k) / (10 ^ 28 * (L : ℝ) ^ 4)) :=
      mul_le_mul h_40 (hr_le_nD.trans (div_le_div_of_nonneg_right hn_le_2k (by positivity))) h_r_nonneg (by positivity)
    have h_const : (81 / μ) * ((2 * k) / (10 ^ 28 * (L : ℝ) ^ 4)) ≤ μ * k / 10 := by
      have h_eq1 : (81 / μ) * ((2 * k) / (10 ^ 28 * (L : ℝ) ^ 4)) =
          (162 * 10 ^ 12 * (L : ℝ) ^ 2 / (10 ^ 28 * (L : ℝ) ^ 4)) * k := by
        dsimp only [μ]; field_simp; ring
      have h_eq2 : μ * k / 10 = (1 / (10 ^ 13 * (L : ℝ) ^ 2)) * k := by
        dsimp only [μ]; field_simp
      rw [h_eq1, h_eq2]
      refine mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast hL
      have : (1 : ℝ) ≤ (L : ℝ) ^ 4 := one_le_pow₀ (by linarith)
      nlinarith [show (0 : ℝ) ≤ (L : ℝ) ^ 2 from sq_nonneg _]
    exact h1.trans (h_prod.trans h_const)
  let Leaves : Finset (Fin k) := Finset.univ.filter (fun v => T.degree v = 1)
  have : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp hk_pos
  obtain ⟨t₁, _, ht₁_mem⟩ := Finset.exists_max_image Finset.univ
    (fun x : Fin k => (Leaves.filter (T.Adj x)).card) Finset.univ_nonempty
  have ht₁ : ∀ x : Fin k, (Leaves.filter (T.Adj x)).card ≤ (Leaves.filter (T.Adj t₁)).card :=
    fun x => ht₁_mem x (mem_univ x)
  by_cases hd_ge : μ * k ≤ (((Leaves.filter (T.Adj t₁)).card : ℝ))
  · exact Erdos743H2.branchA_embed hμ_pos hμ_lt hk_pos h_kn99 hT t₁ ht₁ hd_ge
      hA huA hu_adj huW hU_sub hu_not_U hWA_sub hU_deg hU_card
  · push Not at hd_ge
    exact Erdos743H2.branchB_embed hL hμ_def hn_ge hDr hk_le hkr hT hLeaves_gt t₁ ht₁ hd_ge
      hA huA hu_adj hv_deg huW hU_sub hu_not_U hWA_sub hU_deg hU_card