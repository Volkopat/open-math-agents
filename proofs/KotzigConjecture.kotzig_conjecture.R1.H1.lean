import OMAReductions.R_KotzigConjecture_kotzig_conjecture_R1

/-!
# Proof of `KotzigConjecture.kotzig_conjecture.R1.H1`

Proves Rosa's (1967) theorem for paths, which is the maximum-degree-at-most-2 case of Kotzig's
conjecture: every finite tree `T` with maximum degree at most 2 and `n` edges decomposes
`K_{2n+1}` into `2n + 1` edge-disjoint copies via cyclic shifts `f i v = f 0 v + i` in
`Fin (2 * n + 1)`.

The proof has two parts:
1. By induction on the number of edges `n`, every finite tree of maximum degree at most 2 with `n`
   edges is isomorphic to the path graph on `Fin (n + 1)` (removing a leaf of degree 1 yields a
   smaller tree whose path endpoints include the leaf's unique neighbor).
2. Rosa's zigzag graceful labeling `k ↦ if k % 2 = 0 then k / 2 else n - k / 2` embeds
   `Fin (n + 1)` into `Fin (2 * n + 1)` with edge lengths `{1, ..., n}` occurring once each, so
   every edge of `K_{2n+1}` lies in a unique cyclic shift `T.map (f i)`.
-/

namespace KotzigConjectureR1H1Proof

open SimpleGraph

private lemma fin_sub_val_of_le {m : ℕ} [NeZero m] {a b : Fin m} (h : b.val ≤ a.val) :
    (a - b).val = a.val - b.val := by
  rw [Fin.sub_def]
  have h1 : (m - b.val + a.val) = (a.val - b.val) + m := by omega
  dsimp only
  rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

private lemma fin_sub_val_of_lt {m : ℕ} [NeZero m] {a b : Fin m} (h : a.val < b.val) :
    (a - b).val = m + a.val - b.val := by
  rw [Fin.sub_def]
  dsimp only
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

private lemma fin_sub_val_add_symm {m : ℕ} [NeZero m] {a b : Fin m} (hne : a ≠ b) :
    (b - a).val + (a - b).val = m ∧ 0 < (b - a).val ∧ 0 < (a - b).val := by
  have hne' : a.val ≠ b.val := fun h => hne (Fin.ext h)
  rcases lt_or_gt_of_ne hne' with hlt | hgt
  · rw [fin_sub_val_of_le (le_of_lt hlt), fin_sub_val_of_lt hlt]
    omega
  · rw [fin_sub_val_of_lt hgt, fin_sub_val_of_le (le_of_lt hgt)]
    omega

private lemma edgeSet_ncard_eq_card_edgeFinset {V : Type} [Fintype V] (T : SimpleGraph V)
    [DecidableRel T.Adj] : T.edgeSet.ncard = T.edgeFinset.card :=
  Set.ncard_eq_toFinset_card' T.edgeSet

private lemma card_vertices_of_isTree {V : Type} [Fintype V] (T : SimpleGraph V)
    (hT : T.IsTree) {n : ℕ} (hn : T.edgeSet.ncard = n) : Fintype.card V = n + 1 := by
  classical
  have h1 := hT.card_edgeFinset
  have h2 := edgeSet_ncard_eq_card_edgeFinset T
  omega

private lemma tree_maxDeg_le_two_iso_path :
    ∀ (n : ℕ) {V : Type} [Finite V] (T : SimpleGraph V),
      T.IsTree → (∀ v, (T.neighborSet v).ncard ≤ 2) → T.edgeSet.ncard = n →
      ∃ e : Fin (n + 1) ≃ V,
        ∀ a b : Fin (n + 1), T.Adj (e a) (e b) ↔ a.val + 1 = b.val ∨ b.val + 1 = a.val
  | 0, V, _, T, hT, _, hn => by
    have : Fintype V := Fintype.ofFinite V
    have hcard : Fintype.card V = 1 := card_vertices_of_isTree T hT hn
    refine ⟨(Fintype.equivFinOfCardEq hcard).symm, fun a b => ?_⟩
    have hab : a = b := Fin.ext (by omega)
    subst hab
    simp
  | n + 1, V, _, T, hT, hdeg, hn => by
    have : Fintype V := Fintype.ofFinite V
    classical
    have hcard : Fintype.card V = n + 2 := card_vertices_of_isTree T hT hn
    have : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    obtain ⟨v, hv⟩ := hT.exists_vert_degree_one_of_nontrivial
    obtain ⟨u, hvu, hu_uniq⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hv
    have huv_ne : u ≠ v := hvu.ne'
    let V' : Type := ({v}ᶜ : Set V)
    let T' : SimpleGraph V' := T.induce {v}ᶜ
    have hT' : T'.IsTree :=
      ⟨hT.connected.induce_compl_singleton_of_degree_eq_one hv, hT.isAcyclic.induce _⟩
    have hcard' : Fintype.card V' = n + 1 := by
      have hsub : Fintype.card V' = Fintype.card V - 1 := by
        change Fintype.card {x : V // x ∉ ({v} : Set V)} = Fintype.card V - 1
        rw [Fintype.card_subtype_compl]
        simp
      omega
    have hn' : T'.edgeSet.ncard = n := by
      have h1 := hT'.card_edgeFinset
      have h2 := edgeSet_ncard_eq_card_edgeFinset T'
      omega
    have hdeg' : ∀ w : V', (T'.neighborSet w).ncard ≤ 2 := by
      intro w
      have hsub : Subtype.val '' (T'.neighborSet w) ⊆ T.neighborSet w.1 := by
        rintro x ⟨y, hy, rfl⟩
        exact hy
      have hle : (T'.neighborSet w).ncard ≤ (T.neighborSet w.1).ncard := by
        rw [← Set.ncard_image_of_injective _ Subtype.val_injective]
        exact Set.ncard_le_ncard hsub (Set.toFinite _)
      exact hle.trans (hdeg w.1)
    obtain ⟨e0, he0⟩ := tree_maxDeg_le_two_iso_path n T' hT' hdeg' hn'
    let u' : V' := ⟨u, huv_ne⟩
    let k : Fin (n + 1) := e0.symm u'
    have hk_end : k.val = 0 ∨ k.val = n := by
      by_contra hne_end
      have hk_gt : 0 < k.val := by omega
      have hk_lt : k.val < n := by omega
      let k1 : Fin (n + 1) := ⟨k.val - 1, by omega⟩
      let k2 : Fin (n + 1) := ⟨k.val + 1, by omega⟩
      have hadj1 : T.Adj u (e0 k1).1 := by
        have h := (he0 k k1).mpr (Or.inr (by simp [k1]; omega))
        simpa [k, u', T'] using h
      have hadj2 : T.Adj u (e0 k2).1 := by
        have h := (he0 k k2).mpr (Or.inl (by simp [k2]))
        simpa [k, u', T'] using h
      have hne1 : v ≠ (e0 k1).1 := fun h => (e0 k1).2 h.symm
      have hne2 : v ≠ (e0 k2).1 := fun h => (e0 k2).2 h.symm
      have hne12 : (e0 k1).1 ≠ (e0 k2).1 := by
        intro hEq
        have hkEq : k1 = k2 := e0.injective (Subtype.ext hEq)
        have : k1.val = k2.val := congrArg Fin.val hkEq
        simp [k1, k2] at this
      have hsub3 : ({v, (e0 k1).1, (e0 k2).1} : Set V) ⊆ T.neighborSet u := by
        intro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl | rfl
        · exact hvu.symm
        · exact hadj1
        · exact hadj2
      have hcard3 : ({v, (e0 k1).1, (e0 k2).1} : Set V).ncard = 3 := by
        rw [Set.ncard_insert_of_notMem (by simp [hne1, hne2]),
          Set.ncard_insert_of_notMem (by simp [hne12]), Set.ncard_singleton]
      have hle3 : 3 ≤ (T.neighborSet u).ncard := by
        rw [← hcard3]
        exact Set.ncard_le_ncard hsub3 (Set.toFinite _)
      have hle2 := hdeg u
      omega
    have hex_end : ∃ e' : Fin (n + 1) ≃ V',
        (∀ a b : Fin (n + 1), T'.Adj (e' a) (e' b) ↔ a.val + 1 = b.val ∨ b.val + 1 = a.val) ∧
        e' ⟨n, by omega⟩ = u' := by
      rcases hk_end with hk0 | hkn
      · let rev : Fin (n + 1) ≃ Fin (n + 1) :=
          { toFun := fun i => ⟨n - i.val, by omega⟩
            invFun := fun i => ⟨n - i.val, by omega⟩
            left_inv := fun i => Fin.ext (by dsimp; omega)
            right_inv := fun i => Fin.ext (by dsimp; omega) }
        refine ⟨rev.trans e0, fun a b => ?_, ?_⟩
        · simp only [Equiv.trans_apply, he0, rev, Equiv.coe_fn_mk]
          omega
        · simp only [Equiv.trans_apply, rev, Equiv.coe_fn_mk, Nat.sub_self]
          have h0 : (⟨0, by omega⟩ : Fin (n + 1)) = k := Fin.ext hk0.symm
          rw [h0]
          exact e0.apply_symm_apply u'
      · refine ⟨e0, he0, ?_⟩
        have hnEq : (⟨n, by omega⟩ : Fin (n + 1)) = k := Fin.ext hkn.symm
        rw [hnEq]
        exact e0.apply_symm_apply u'
    obtain ⟨e', he', he'_end⟩ := hex_end
    let e : Fin (n + 2) ≃ V :=
      { toFun := fun i =>
          if hi : i.val < n + 1 then (e' ⟨i.val, hi⟩).1 else v
        invFun := fun w =>
          if hw : w = v then ⟨n + 1, by omega⟩ else ⟨(e'.symm ⟨w, hw⟩).val, by omega⟩
        left_inv := fun i => by
          by_cases hi : i.val < n + 1
          · simp only [dif_pos hi]
            have hne : (e' ⟨i.val, hi⟩).1 ≠ v := (e' ⟨i.val, hi⟩).2
            rw [dif_neg hne]
            apply Fin.ext
            simp
          · dsimp only
            rw [dif_neg hi, dif_pos rfl]
            apply Fin.ext
            dsimp only
            omega
        right_inv := fun w => by
          by_cases hw : w = v
          · simp [hw]
          · dsimp only
            rw [dif_neg hw]
            have hlt : (e'.symm ⟨w, hw⟩).val < n + 1 := (e'.symm ⟨w, hw⟩).isLt
            rw [dif_pos hlt]
            have hEq : e' ⟨(e'.symm ⟨w, hw⟩).val, hlt⟩ = ⟨w, hw⟩ :=
              e'.apply_symm_apply ⟨w, hw⟩
            exact congrArg Subtype.val hEq }
    refine ⟨e, fun a b => ?_⟩
    by_cases ha : a.val < n + 1 <;> by_cases hb : b.val < n + 1
    · have h1 : T.Adj (e a) (e b) ↔ T'.Adj (e' ⟨a.val, ha⟩) (e' ⟨b.val, hb⟩) := by
        simp only [e, Equiv.coe_fn_mk, dif_pos ha, dif_pos hb, T', SimpleGraph.comap_adj,
          Function.Embedding.coe_subtype]
      rw [h1, he']
    · have hbe : b.val = n + 1 := by omega
      have h1 : T.Adj (e a) (e b) ↔ T.Adj v (e' ⟨a.val, ha⟩).1 := by
        simp only [e, Equiv.coe_fn_mk, dif_pos ha, dif_neg hb]
        exact T.adj_comm _ _
      rw [h1]
      constructor
      · intro hadj
        have hEq : (e' ⟨a.val, ha⟩).1 = u := hu_uniq _ hadj
        have hEq' : e' ⟨a.val, ha⟩ = e' ⟨n, by omega⟩ := by
          rw [he'_end]
          exact Subtype.ext hEq
        have hIdx : (⟨a.val, ha⟩ : Fin (n + 1)) = ⟨n, by omega⟩ := e'.injective hEq'
        have ha_eq : a.val = n := congrArg Fin.val hIdx
        omega
      · intro hstep
        have ha_eq : a.val = n := by omega
        have hIdx : (⟨a.val, ha⟩ : Fin (n + 1)) = ⟨n, by omega⟩ := Fin.ext ha_eq
        rw [hIdx, he'_end]
        exact hvu
    · have hae : a.val = n + 1 := by omega
      have h1 : T.Adj (e a) (e b) ↔ T.Adj v (e' ⟨b.val, hb⟩).1 := by
        simp only [e, Equiv.coe_fn_mk, dif_neg ha, dif_pos hb]
      rw [h1]
      constructor
      · intro hadj
        have hEq : (e' ⟨b.val, hb⟩).1 = u := hu_uniq _ hadj
        have hEq' : e' ⟨b.val, hb⟩ = e' ⟨n, by omega⟩ := by
          rw [he'_end]
          exact Subtype.ext hEq
        have hIdx : (⟨b.val, hb⟩ : Fin (n + 1)) = ⟨n, by omega⟩ := e'.injective hEq'
        have hb_eq : b.val = n := congrArg Fin.val hIdx
        omega
      · intro hstep
        have hb_eq : b.val = n := by omega
        have hIdx : (⟨b.val, hb⟩ : Fin (n + 1)) = ⟨n, by omega⟩ := Fin.ext hb_eq
        rw [hIdx, he'_end]
        exact hvu
    · have hae : a.val = n + 1 := by omega
      have hbe : b.val = n + 1 := by omega
      have h1 : e a = v := by simp only [e, Equiv.coe_fn_mk, dif_neg ha]
      have h2 : e b = v := by simp only [e, Equiv.coe_fn_mk, dif_neg hb]
      rw [h1, h2]
      exact ⟨fun h => (T.irrefl h).elim, fun h => by omega⟩

private def zigzagNat (n k : ℕ) : ℕ :=
  if k % 2 = 0 then k / 2 else n - k / 2

private lemma zigzagNat_le {n k : ℕ} (hk : k ≤ n) : zigzagNat n k ≤ n := by
  unfold zigzagNat
  split_ifs <;> omega

private lemma zigzagNat_inj {n a b : ℕ} (ha : a ≤ n) (hb : b ≤ n)
    (hab : zigzagNat n a = zigzagNat n b) : a = b := by
  unfold zigzagNat at hab
  split_ifs at hab <;> omega

private def zigzag (n : ℕ) : Fin (n + 1) ↪ Fin (2 * n + 1) where
  toFun k := ⟨zigzagNat n k.val, by
    have := zigzagNat_le (n := n) (k := k.val) (by omega)
    omega⟩
  inj' a b hab := Fin.ext (zigzagNat_inj (by omega) (by omega) (congrArg Fin.val hab))

private lemma zigzag_sub_even {n k : ℕ} (hk : k < n) (heven : k % 2 = 0) :
    (zigzag n ⟨k + 1, by omega⟩ - zigzag n ⟨k, by omega⟩).val = n - k := by
  have hle : (zigzag n ⟨k, by omega⟩).val ≤ (zigzag n ⟨k + 1, by omega⟩).val := by
    simp only [zigzag, Function.Embedding.coeFn_mk, zigzagNat, heven, ↓reduceIte]
    have hodd : (k + 1) % 2 ≠ 0 := by omega
    rw [if_neg hodd]
    omega
  rw [fin_sub_val_of_le hle]
  simp only [zigzag, Function.Embedding.coeFn_mk, zigzagNat, heven, ↓reduceIte]
  have hodd : (k + 1) % 2 ≠ 0 := by omega
  rw [if_neg hodd]
  omega

private lemma zigzag_sub_even_rev {n k : ℕ} (hk : k < n) (heven : k % 2 = 0) :
    (zigzag n ⟨k, by omega⟩ - zigzag n ⟨k + 1, by omega⟩).val = n + 1 + k := by
  have hlt : (zigzag n ⟨k, by omega⟩).val < (zigzag n ⟨k + 1, by omega⟩).val := by
    simp only [zigzag, Function.Embedding.coeFn_mk, zigzagNat, heven, ↓reduceIte]
    have hodd : (k + 1) % 2 ≠ 0 := by omega
    rw [if_neg hodd]
    omega
  rw [fin_sub_val_of_lt hlt]
  simp only [zigzag, Function.Embedding.coeFn_mk, zigzagNat, heven, ↓reduceIte]
  have hodd : (k + 1) % 2 ≠ 0 := by omega
  rw [if_neg hodd]
  omega

private lemma zigzag_sub_odd {n k : ℕ} (hk : k < n) (hodd : k % 2 = 1) :
    (zigzag n ⟨k, by omega⟩ - zigzag n ⟨k + 1, by omega⟩).val = n - k := by
  have hle : (zigzag n ⟨k + 1, by omega⟩).val ≤ (zigzag n ⟨k, by omega⟩).val := by
    simp only [zigzag, Function.Embedding.coeFn_mk, zigzagNat]
    have hne : k % 2 ≠ 0 := by omega
    have hev : (k + 1) % 2 = 0 := by omega
    rw [if_neg hne, if_pos hev]
    omega
  rw [fin_sub_val_of_le hle]
  simp only [zigzag, Function.Embedding.coeFn_mk, zigzagNat]
  have hne : k % 2 ≠ 0 := by omega
  have hev : (k + 1) % 2 = 0 := by omega
  rw [if_neg hne, if_pos hev]
  omega

private lemma zigzag_sub_odd_rev {n k : ℕ} (hk : k < n) (hodd : k % 2 = 1) :
    (zigzag n ⟨k + 1, by omega⟩ - zigzag n ⟨k, by omega⟩).val = n + 1 + k := by
  have hlt : (zigzag n ⟨k + 1, by omega⟩).val < (zigzag n ⟨k, by omega⟩).val := by
    simp only [zigzag, Function.Embedding.coeFn_mk, zigzagNat]
    have hne : k % 2 ≠ 0 := by omega
    have hev : (k + 1) % 2 = 0 := by omega
    rw [if_neg hne, if_pos hev]
    omega
  rw [fin_sub_val_of_lt hlt]
  simp only [zigzag, Function.Embedding.coeFn_mk, zigzagNat]
  have hne : k % 2 ≠ 0 := by omega
  have hev : (k + 1) % 2 = 0 := by omega
  rw [if_neg hne, if_pos hev]
  omega

private lemma map_adj_iff_oriented {V : Type} (T : SimpleGraph V) (n : ℕ)
    (e : Fin (n + 1) ≃ V)
    (he : ∀ a b : Fin (n + 1), T.Adj (e a) (e b) ↔ a.val + 1 = b.val ∨ b.val + 1 = a.val)
    (f : Fin (2 * n + 1) → (V ↪ Fin (2 * n + 1)))
    (hf : ∀ i v, f i v = zigzag n (e.symm v) + i)
    (i x y : Fin (2 * n + 1)) (hpos : 0 < (y - x).val) (hle : (y - x).val ≤ n) :
    (T.map (f i)).Adj x y ↔
      ((n - (y - x).val) % 2 = 0 ∧ x = zigzag n ⟨n - (y - x).val, by omega⟩ + i) ∨
      ((n - (y - x).val) % 2 = 1 ∧ x = zigzag n ⟨n - (y - x).val + 1, by omega⟩ + i) := by
  set d := (y - x).val
  set k := n - d
  have hk_lt : k < n := by omega
  have hnk : n - k = d := by omega
  rw [SimpleGraph.map_adj]
  constructor
  · rintro ⟨u, v, huv, hfu, hfv⟩
    let a : Fin (n + 1) := e.symm u
    let b : Fin (n + 1) := e.symm v
    have hab_adj : a.val + 1 = b.val ∨ b.val + 1 = a.val := by
      rw [← he a b, e.apply_symm_apply, e.apply_symm_apply]
      exact huv
    have hxa : zigzag n a + i = x := by
      simpa [hf, a] using hfu
    have hyb : zigzag n b + i = y := by
      simpa [hf, b] using hfv
    have hdiff : y - x = zigzag n b - zigzag n a := by
      rw [← hyb, ← hxa, add_sub_add_right_eq_sub]
    rcases hab_adj with hab | hba
    · have ha_lt : a.val < n := by omega
      have hb_eq : b = ⟨a.val + 1, by omega⟩ := Fin.ext hab.symm
      by_cases hev : a.val % 2 = 0
      · have hd_eq : d = n - a.val := by
          change (y - x).val = n - a.val
          rw [hdiff, hb_eq]
          exact zigzag_sub_even ha_lt hev
        have hak : a.val = k := by omega
        refine Or.inl ⟨by omega, hxa.symm.trans ?_⟩
        congr 2
        exact Fin.ext hak
      · have hodd : a.val % 2 = 1 := by omega
        have hd_eq : d = n + 1 + a.val := by
          change (y - x).val = n + 1 + a.val
          rw [hdiff, hb_eq]
          exact zigzag_sub_odd_rev ha_lt hodd
        omega
    · have hb_lt : b.val < n := by omega
      have ha_eq : a = ⟨b.val + 1, by omega⟩ := Fin.ext hba.symm
      by_cases hev : b.val % 2 = 0
      · have hd_eq : d = n + 1 + b.val := by
          change (y - x).val = n + 1 + b.val
          rw [hdiff, ha_eq]
          exact zigzag_sub_even_rev hb_lt hev
        omega
      · have hodd : b.val % 2 = 1 := by omega
        have hd_eq : d = n - b.val := by
          change (y - x).val = n - b.val
          rw [hdiff, ha_eq]
          exact zigzag_sub_odd hb_lt hodd
        have hbk : b.val = k := by omega
        refine Or.inr ⟨by omega, hxa.symm.trans ?_⟩
        congr 2
        exact Fin.ext (show a.val = k + 1 by omega)
  · rintro (⟨hev, hx⟩ | ⟨hodd, hx⟩)
    · refine ⟨e ⟨k, by omega⟩, e ⟨k + 1, by omega⟩, (he _ _).mpr (Or.inl rfl), ?_, ?_⟩
      · rw [hf, Equiv.symm_apply_apply]
        exact hx.symm
      · simp only [hf, Equiv.symm_apply_apply]
        have hsub : zigzag n ⟨k + 1, by omega⟩ - zigzag n ⟨k, by omega⟩ = y - x :=
          Fin.ext (by rw [zigzag_sub_even hk_lt hev, hnk])
        calc
          zigzag n ⟨k + 1, by omega⟩ + i
              = (zigzag n ⟨k + 1, by omega⟩ - zigzag n ⟨k, by omega⟩) +
                (zigzag n ⟨k, by omega⟩ + i) := by abel
          _ = (y - x) + x := by rw [hsub, ← hx]
          _ = y := by abel
    · refine ⟨e ⟨k + 1, by omega⟩, e ⟨k, by omega⟩, (he _ _).mpr (Or.inr rfl), ?_, ?_⟩
      · rw [hf, Equiv.symm_apply_apply]
        exact hx.symm
      · simp only [hf, Equiv.symm_apply_apply]
        have hsub : zigzag n ⟨k, by omega⟩ - zigzag n ⟨k + 1, by omega⟩ = y - x :=
          Fin.ext (by rw [zigzag_sub_odd hk_lt hodd, hnk])
        calc
          zigzag n ⟨k, by omega⟩ + i
              = (zigzag n ⟨k, by omega⟩ - zigzag n ⟨k + 1, by omega⟩) +
                (zigzag n ⟨k + 1, by omega⟩ + i) := by abel
          _ = (y - x) + x := by rw [hsub, ← hx]
          _ = y := by abel

end KotzigConjectureR1H1Proof

theorem OMA.solution : OMA.R_KotzigConjecture_kotzig_conjecture_R1.H1 := by
  intro V _ T hT hdeg n hn
  obtain ⟨e, he⟩ := KotzigConjectureR1H1Proof.tree_maxDeg_le_two_iso_path n T hT hdeg hn
  let f0 : V ↪ Fin (2 * n + 1) := e.symm.toEmbedding.trans (KotzigConjectureR1H1Proof.zigzag n)
  let f : Fin (2 * n + 1) → (V ↪ Fin (2 * n + 1)) :=
    fun i => f0.trans (Equiv.addRight i).toEmbedding
  have hf_val : ∀ i v, f i v = KotzigConjectureR1H1Proof.zigzag n (e.symm v) + i := by
    intro i v
    rfl
  refine ⟨f, ?_, ?_, ?_⟩
  · intro i v
    simp [f]
  · intro i j hij
    rw [Set.disjoint_left]
    intro s hsi hsj
    induction s using Sym2.ind with
    | _ x y =>
      have hxi : (T.map (f i)).Adj x y := hsi
      have hxj : (T.map (f j)).Adj x y := hsj
      have hne : x ≠ y := hxi.ne
      have ⟨hsum, hpos1, hpos2⟩ := KotzigConjectureR1H1Proof.fin_sub_val_add_symm hne
      have h_eq_of_le : ∀ {a b : Fin (2 * n + 1)},
          0 < (b - a).val → (b - a).val ≤ n →
          (T.map (f i)).Adj a b → (T.map (f j)).Adj a b → i = j := by
        intro a b hpos hle hai haj
        rw [KotzigConjectureR1H1Proof.map_adj_iff_oriented T n e he f hf_val i a b hpos hle] at hai
        rw [KotzigConjectureR1H1Proof.map_adj_iff_oriented T n e he f hf_val j a b hpos hle] at haj
        rcases hai with ⟨h0, hi⟩ | ⟨h1, hi⟩ <;> rcases haj with ⟨_, hj⟩ | ⟨_, hj⟩
        · exact add_left_cancel (hi.symm.trans hj)
        · omega
        · omega
        · exact add_left_cancel (hi.symm.trans hj)
      by_cases hle : (y - x).val ≤ n
      · exact hij (h_eq_of_le hpos1 hle hxi hxj)
      · exact hij (h_eq_of_le hpos2 (by omega) hxi.symm hxj.symm)
  · refine le_antisymm le_top ?_
    intro x y hxy
    have hne : x ≠ y := hxy
    have ⟨hsum, hpos1, hpos2⟩ := KotzigConjectureR1H1Proof.fin_sub_val_add_symm hne
    have hex_of_le : ∀ {a b : Fin (2 * n + 1)},
        0 < (b - a).val → (b - a).val ≤ n → ∃ i, (T.map (f i)).Adj a b := by
      intro a b hpos hle
      by_cases hev : (n - (b - a).val) % 2 = 0
      · refine ⟨a - KotzigConjectureR1H1Proof.zigzag n ⟨n - (b - a).val, by omega⟩, ?_⟩
        rw [KotzigConjectureR1H1Proof.map_adj_iff_oriented T n e he f hf_val _ a b hpos hle]
        exact Or.inl ⟨hev, by abel⟩
      · refine ⟨a - KotzigConjectureR1H1Proof.zigzag n ⟨n - (b - a).val + 1, by omega⟩, ?_⟩
        rw [KotzigConjectureR1H1Proof.map_adj_iff_oriented T n e he f hf_val _ a b hpos hle]
        exact Or.inr ⟨by omega, by abel⟩
    rw [SimpleGraph.iSup_adj]
    by_cases hle : (y - x).val ≤ n
    · exact hex_of_le hpos1 hle
    · obtain ⟨i, hi⟩ := hex_of_le hpos2 (by omega)
      exact ⟨i, hi.symm⟩
