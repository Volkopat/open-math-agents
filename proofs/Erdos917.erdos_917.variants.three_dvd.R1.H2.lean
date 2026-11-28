import OMAReductions.R_Erdos917_erdos_917_variants_three_dvd_R1
-- Step Erdos917.erdos_917.variants.three_dvd.R1.H2: hypothesis H2 of reduction Erdos917.erdos_917.variants.three_dvd.R1
-- Credit: @Raimo33
-- Proof adapted from the merged proof of Erdos917.erdos_917.variants.lower_construction.R1.H2 (same statement word for word).

/-! Dirac's join construction, using the join and transport lemmas from
@mattdorman's existing proof of Erdős 917 part (i). -/

namespace OMA.DiracJoin
open Finset SimpleGraph

lemma colorable_of {V : Type*} (H : SimpleGraph V) (K : ℕ) (col : V → ℕ)
    (hb : ∀ x, col x < K) (hp : ∀ x y, H.Adj x y → col x ≠ col y) : H.Colorable K :=
  ⟨Coloring.mk (fun x => ⟨col x, hb x⟩) (fun {x y} h heq => hp x y h (congrArg Fin.val heq))⟩

lemma isKCritical_of_edge_critical {V : Type*} (G : SimpleGraph V) {k : ℕ} (hk : 1 ≤ k)
    (hcol : G.Colorable k) (hnot : ¬ G.Colorable (k - 1))
    (hdeg : ∀ v : V, ∃ w : V, G.Adj v w)
    (hedge : ∀ u w : V, G.Adj u w → (G.deleteEdges {s(u, w)}).Colorable (k - 1)) :
    Erdos917.IsKCritical G k := by
  have hle_chi : (k : ℕ∞) ≤ G.chromaticNumber := by
    rw [le_chromaticNumber_iff_not_colorable (by omega)]
    exact hnot
  have hchi : G.chromaticNumber = (k : ℕ∞) :=
    le_antisymm hcol.chromaticNumber_le hle_chi
  refine ⟨⟨hchi, ?_⟩, ?_⟩
  · intro v
    unfold Subgraph.IsCriticalVertex Subgraph.IsCriticalVerts
    obtain ⟨w, hvw⟩ := hdeg v
    obtain ⟨C⟩ := hedge v w hvw
    have hdel : ((⊤ : G.Subgraph).deleteVerts {v}).coe.Colorable (k - 1) := by
      refine ⟨Coloring.mk (fun a => C a.val) ?_⟩
      intro a b hab
      rw [Subgraph.coe_adj, Subgraph.deleteVerts_adj] at hab
      obtain ⟨_, ha, _, hb, hab⟩ := hab
      rw [Subgraph.top_adj] at hab
      apply C.valid
      rw [deleteEdges_adj]
      refine ⟨hab, ?_⟩
      rw [Set.mem_singleton_iff, Sym2.eq_iff]
      rintro (⟨h1, -⟩ | ⟨-, h2⟩)
      · exact ha (Set.mem_singleton_iff.mpr h1)
      · exact hb (Set.mem_singleton_iff.mpr h2)
    have htop_le : (k : ℕ∞) ≤ (⊤ : G.Subgraph).coe.chromaticNumber := by
      rw [le_chromaticNumber_iff_not_colorable (by omega)]
      rintro ⟨C'⟩
      exact hnot ⟨Coloring.mk (fun x => C' ⟨x, trivial⟩) (fun h => C'.valid (by simpa using h))⟩
    exact lt_of_le_of_lt hdel.chromaticNumber_le
      (lt_of_lt_of_le (by exact_mod_cast (by omega : k - 1 < k)) htop_le)
  · intro e he
    unfold IsCriticalEdge IsCriticalEdges
    revert he
    refine Sym2.ind (fun u w huw => ?_) e
    rw [mem_edgeSet] at huw
    exact lt_of_le_of_lt (hedge u w huw).chromaticNumber_le
      (lt_of_lt_of_le (by exact_mod_cast (by omega : k - 1 < k)) hle_chi)

lemma isKCritical_transport {V W : Type*} (G : SimpleGraph V) (e : V ≃ W) {k : ℕ} (hk : 1 ≤ k)
    (hcol : G.Colorable k) (hnot : ¬ G.Colorable (k - 1))
    (hdeg : ∀ v : V, ∃ w : V, G.Adj v w)
    (hedge : ∀ u w : V, G.Adj u w → (G.deleteEdges {s(u, w)}).Colorable (k - 1)) :
    Erdos917.IsKCritical (G.map e.toEmbedding) k := by
  refine isKCritical_of_edge_critical _ hk ?_ ?_ ?_ ?_
  · obtain ⟨C⟩ := hcol
    refine ⟨Coloring.mk (fun w => C (e.symm w)) ?_⟩
    intro x y hxy
    rw [map_adj] at hxy
    obtain ⟨u, v, huv, rfl, rfl⟩ := hxy
    simpa using C.valid huv
  · rintro ⟨C⟩
    exact hnot ⟨Coloring.mk (fun v => C (e v)) fun {u v} huv =>
      C.valid (by rw [map_adj]; exact ⟨u, v, huv, rfl, rfl⟩)⟩
  · intro w
    obtain ⟨u, hu⟩ := hdeg (e.symm w)
    refine ⟨e u, ?_⟩
    rw [map_adj]
    exact ⟨e.symm w, u, hu, e.apply_symm_apply w, rfl⟩
  · intro x y hxy
    rw [map_adj] at hxy
    obtain ⟨u, v, huv, rfl, rfl⟩ := hxy
    obtain ⟨C⟩ := hedge u v huv
    refine ⟨Coloring.mk (fun w => C (e.symm w)) ?_⟩
    intro a b hab
    rw [deleteEdges_adj, map_adj] at hab
    obtain ⟨⟨u', v', huv', rfl, rfl⟩, hne⟩ := hab
    simp only [Equiv.toEmbedding_apply, Equiv.symm_apply_apply]
    apply C.valid
    rw [deleteEdges_adj]
    refine ⟨huv', ?_⟩
    intro heq
    apply hne
    rw [Set.mem_singleton_iff] at heq ⊢
    rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact Sym2.eq_swap

lemma ncard_edgeSet_map {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (e : V ≃ W)
    [DecidableRel (G.map e.toEmbedding).Adj] :
    (G.map e.toEmbedding).edgeSet.ncard = G.edgeSet.ncard := by
  rw [← coe_edgeFinset, ← coe_edgeFinset, Set.ncard_coe_finset, Set.ncard_coe_finset]
  have hdeg : ∀ v : V, (G.map e.toEmbedding).degree (e v) = G.degree v := by
    intro v
    rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree,
      neighborFinset_eq_filter, neighborFinset_eq_filter]
    refine card_bij (fun w _ => e.symm w) ?_ ?_ ?_
    · intro w hw
      rw [mem_filter] at hw ⊢
      refine ⟨mem_univ _, ?_⟩
      have hwadj := hw.2
      rw [map_adj] at hwadj
      obtain ⟨a, b, hab, ha, hb⟩ := hwadj
      have h1 : a = v := e.injective ha
      have h2 : b = e.symm w := by
        apply e.injective
        simpa using hb
      rwa [← h1, ← h2]
    · intro w₁ _ w₂ _ h
      exact e.symm.injective h
    · intro u hu
      rw [mem_filter] at hu
      refine ⟨e u, ?_, e.symm_apply_apply u⟩
      rw [mem_filter]
      refine ⟨mem_univ _, ?_⟩
      rw [map_adj]
      exact ⟨v, u, hu.2, rfl, rfl⟩
  have hsum1 := sum_degrees_eq_twice_card_edges (G.map e.toEmbedding)
  have hsum2 := sum_degrees_eq_twice_card_edges G
  have hsum_eq : ∑ w : W, (G.map e.toEmbedding).degree w = ∑ v : V, G.degree v := by
    rw [← e.sum_comp]
    exact sum_congr rfl fun v _ => hdeg v
  omega

def joinSum {V₁ V₂ : Type*} (G₁ : SimpleGraph V₁) (G₂ : SimpleGraph V₂) :
    SimpleGraph (V₁ ⊕ V₂) where
  Adj
    | .inl x, .inl y => G₁.Adj x y
    | .inr x, .inr y => G₂.Adj x y
    | .inl _, .inr _ => True
    | .inr _, .inl _ => True
  symm := ⟨fun u v h => by
    cases u <;> cases v <;> simp only at h ⊢
    · exact h.symm
    · exact h.symm⟩
  loopless := ⟨fun u h => by
    cases u <;> simp only at h
    · exact G₁.ne_of_adj h rfl
    · exact G₂.ne_of_adj h rfl⟩

lemma isKCritical_colorable {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (hG : Erdos917.IsKCritical G k) : G.Colorable k :=
  chromaticNumber_le_iff_colorable.mp hG.1.1.le

lemma isKCritical_not_colorable {V : Type*} {G : SimpleGraph V} {k : ℕ} (hk : 1 ≤ k)
    (hG : Erdos917.IsKCritical G k) : ¬ G.Colorable (k - 1) := by
  intro hc
  have hlt : (k - 1 : ℕ∞) < (k : ℕ∞) := by exact_mod_cast (by omega : k - 1 < k)
  exact not_le_of_gt hlt (hG.1.1.symm.trans_le hc.chromaticNumber_le)

lemma isKCritical_nonempty {V : Type*} {G : SimpleGraph V} {k : ℕ} (hk : 1 ≤ k)
    (hG : Erdos917.IsKCritical G k) : Nonempty V := by
  by_contra hemp
  rw [not_nonempty_iff] at hemp
  exact isKCritical_not_colorable hk hG
    ⟨Coloring.mk (fun v => (IsEmpty.false v).elim) (fun {v} => (IsEmpty.false v).elim)⟩

lemma isKCritical_del_edge_colorable {V : Type*} {G : SimpleGraph V} {k : ℕ} (hk : 1 ≤ k)
    (hG : Erdos917.IsKCritical G k) {u w : V} (huw : G.Adj u w) :
    (G.deleteEdges {s(u, w)}).Colorable (k - 1) := by
  have he : s(u, w) ∈ G.edgeSet := huw
  have hlt := hG.2 _ he
  unfold IsCriticalEdge IsCriticalEdges at hlt
  rw [hG.1.1] at hlt
  by_contra hnc
  exact not_lt_of_ge ((le_chromaticNumber_iff_not_colorable (by omega)).mpr hnc) hlt

lemma isKCritical_del_vert_colorable {V : Type*} {G : SimpleGraph V} {k : ℕ} (hk : 1 ≤ k)
    (hG : Erdos917.IsKCritical G k) (v : V) :
    ∃ col : V → ℕ, (∀ x, x ≠ v → col x < k - 1) ∧
      ∀ x y, x ≠ v → y ≠ v → G.Adj x y → col x ≠ col y := by
  classical
  have hlt := hG.1.2 v
  unfold Subgraph.IsCriticalVertex Subgraph.IsCriticalVerts at hlt
  have htop_le : (⊤ : G.Subgraph).coe.chromaticNumber ≤ G.chromaticNumber := by
    obtain ⟨C⟩ := isKCritical_colorable hG
    rw [hG.1.1]
    exact (Colorable.chromaticNumber_le
      ⟨Coloring.mk (fun x => C x.val) (fun {a b} h => C.valid (by simpa using h))⟩)
  have hlt' : ((⊤ : G.Subgraph).deleteVerts {v}).coe.chromaticNumber < (k : ℕ∞) :=
    lt_of_lt_of_le hlt (htop_le.trans_eq hG.1.1)
  have hcol : ((⊤ : G.Subgraph).deleteVerts {v}).coe.Colorable (k - 1) := by
    by_contra hnc
    exact not_lt_of_ge ((le_chromaticNumber_iff_not_colorable (by omega)).mpr hnc) hlt'
  obtain ⟨C⟩ := hcol
  refine ⟨fun x => if hx : x ≠ v then (C ⟨x, by simp [hx]⟩).val else 0, ?_, ?_⟩
  · intro x hx
    dsimp only
    rw [dif_pos hx]
    exact (C _).isLt
  · intro x y hx hy hadj heq
    dsimp only at heq
    rw [dif_pos hx, dif_pos hy] at heq
    have hadj' : ((⊤ : G.Subgraph).deleteVerts {v}).coe.Adj ⟨x, by simp [hx]⟩ ⟨y, by simp [hy]⟩ := by
      rw [Subgraph.coe_adj, Subgraph.deleteVerts_adj]
      exact ⟨trivial, by simp [hx], trivial, by simp [hy], hadj⟩
    exact C.valid hadj' (Fin.ext heq)

def joinGraph {n₁ n₂ : ℕ} (G₁ : SimpleGraph (Fin n₁)) (G₂ : SimpleGraph (Fin n₂)) :
    SimpleGraph (Fin (n₁ + n₂)) :=
  (joinSum G₁ G₂).map finSumFinEquiv.toEmbedding

lemma joinGraph_critical {n₁ n₂ k₁ k₂ : ℕ} {G₁ : SimpleGraph (Fin n₁)} {G₂ : SimpleGraph (Fin n₂)}
    (hk₁ : 1 ≤ k₁) (hk₂ : 1 ≤ k₂)
    (h₁ : Erdos917.IsKCritical G₁ k₁) (h₂ : Erdos917.IsKCritical G₂ k₂) :
    Erdos917.IsKCritical (joinGraph G₁ G₂) (k₁ + k₂) := by
  classical
  obtain ⟨v₁₀⟩ := isKCritical_nonempty hk₁ h₁
  obtain ⟨v₂₀⟩ := isKCritical_nonempty hk₂ h₂
  refine isKCritical_transport (joinSum G₁ G₂) finSumFinEquiv (by omega) ?_ ?_ ?_ ?_
  · obtain ⟨C₁⟩ := isKCritical_colorable h₁
    obtain ⟨C₂⟩ := isKCritical_colorable h₂
    refine colorable_of _ (k₁ + k₂)
      (Sum.elim (fun x => (C₁ x).val) (fun y => k₁ + (C₂ y).val))
      (fun u => by
        cases u with
        | inl x => simp only [Sum.elim_inl]; have := (C₁ x).isLt; omega
        | inr y => simp only [Sum.elim_inr]; have := (C₂ y).isLt; omega)
      ?_
    intro u v huv
    rcases u with x | x <;> rcases v with y | y <;>
      simp only [joinSum, Sum.elim_inl, Sum.elim_inr] at huv ⊢
    · intro heq; exact C₁.valid huv (Fin.ext heq)
    · have := (C₁ x).isLt; omega
    · have := (C₁ y).isLt; omega
    · intro heq; exact C₂.valid huv (Fin.ext (by omega))
  · rintro ⟨C⟩
    let S₁ : Finset (Fin (k₁ + k₂ - 1)) := univ.image (fun x : Fin n₁ => C (.inl x))
    let S₂ : Finset (Fin (k₁ + k₂ - 1)) := univ.image (fun y : Fin n₂ => C (.inr y))
    have hdisj : Disjoint S₁ S₂ := by
      rw [Finset.disjoint_left]
      intro c hc₁ hc₂
      obtain ⟨x, _, rfl⟩ := mem_image.mp hc₁
      obtain ⟨y, _, hy⟩ := mem_image.mp hc₂
      exact C.valid (show (joinSum G₁ G₂).Adj (.inl x) (.inr y) from trivial) hy.symm
    have hcard : S₁.card + S₂.card ≤ k₁ + k₂ - 1 := by
      rw [← card_union_of_disjoint hdisj]
      exact (card_le_univ _).trans_eq (Fintype.card_fin _)
    by_cases hle₁ : S₁.card ≤ k₁ - 1
    · apply isKCritical_not_colorable hk₁ h₁
      let eqv := S₁.equivFin
      refine ⟨Coloring.mk (fun x => (eqv ⟨C (.inl x), mem_image_of_mem _ (mem_univ x)⟩).castLE hle₁) ?_⟩
      intro a b hab heq
      have hval := Fin.castLE_injective hle₁ heq
      have hsub := eqv.injective hval
      exact C.valid (show (joinSum G₁ G₂).Adj (.inl a) (.inl b) from hab) (congrArg Subtype.val hsub)
    · have hle₂ : S₂.card ≤ k₂ - 1 := by omega
      apply isKCritical_not_colorable hk₂ h₂
      let eqv := S₂.equivFin
      refine ⟨Coloring.mk (fun y => (eqv ⟨C (.inr y), mem_image_of_mem _ (mem_univ y)⟩).castLE hle₂) ?_⟩
      intro a b hab heq
      have hval := Fin.castLE_injective hle₂ heq
      have hsub := eqv.injective hval
      exact C.valid (show (joinSum G₁ G₂).Adj (.inr a) (.inr b) from hab) (congrArg Subtype.val hsub)
  · intro v
    cases v with
    | inl _ => exact ⟨.inr v₂₀, trivial⟩
    | inr _ => exact ⟨.inl v₁₀, trivial⟩
  · intro u w huw
    cases u <;> cases w <;> simp only [joinSum] at huw
    · rename_i x y
      obtain ⟨C₁⟩ := isKCritical_del_edge_colorable hk₁ h₁ huw
      obtain ⟨C₂⟩ := isKCritical_colorable h₂
      refine colorable_of _ (k₁ + k₂ - 1)
        (Sum.elim (fun a => (C₁ a).val) (fun b => (k₁ - 1) + (C₂ b).val))
        (fun z => by
          cases z with
          | inl a => simp only [Sum.elim_inl]; have := (C₁ a).isLt; omega
          | inr b => simp only [Sum.elim_inr]; have := (C₂ b).isLt; omega)
        ?_
      intro a b hab
      rw [deleteEdges_adj] at hab
      obtain ⟨hadj, hne⟩ := hab
      rcases a with a₁ | a₂ <;> rcases b with b₁ | b₂ <;>
        simp only [joinSum, Sum.elim_inl, Sum.elim_inr] at hadj ⊢
      · intro heq
        have hadj' : (G₁.deleteEdges {s(x, y)}).Adj a₁ b₁ := by
          rw [deleteEdges_adj]
          refine ⟨hadj, ?_⟩
          intro hs
          apply hne
          rw [Set.mem_singleton_iff] at hs ⊢
          rcases Sym2.eq_iff.mp hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · rfl
          · exact Sym2.eq_swap
        exact C₁.valid hadj' (Fin.ext heq)
      · have := (C₁ a₁).isLt; omega
      · have := (C₁ b₁).isLt; omega
      · intro heq; exact C₂.valid hadj (Fin.ext (by omega))
    · rename_i x y
      obtain ⟨c₁, hc₁_lt, hc₁_p⟩ := isKCritical_del_vert_colorable hk₁ h₁ x
      obtain ⟨c₂, hc₂_lt, hc₂_p⟩ := isKCritical_del_vert_colorable hk₂ h₂ y
      refine colorable_of _ (k₁ + k₂ - 1)
        (Sum.elim (fun a => if a = x then k₁ + k₂ - 2 else c₁ a)
          (fun b => if b = y then k₁ + k₂ - 2 else (k₁ - 1) + c₂ b))
        (fun z => by
          cases z with
          | inl a =>
            simp only [Sum.elim_inl]
            by_cases ha : a = x
            · simp [ha]; omega
            · simp [ha]; have := hc₁_lt a ha; omega
          | inr b =>
            simp only [Sum.elim_inr]
            by_cases hb : b = y
            · simp [hb]; omega
            · simp [hb]; have := hc₂_lt b hb; omega)
        ?_
      intro a b hab
      rw [deleteEdges_adj] at hab
      obtain ⟨hadj, hne⟩ := hab
      rcases a with a₁ | a₂ <;> rcases b with b₁ | b₂ <;>
        simp only [joinSum, Sum.elim_inl, Sum.elim_inr] at hadj ⊢
      · by_cases ha : a₁ = x
        · have hb : b₁ ≠ x := by rintro rfl; exact G₁.ne_of_adj hadj ha
          simp only [ha, hb, ↓reduceIte]; have := hc₁_lt b₁ hb; omega
        · by_cases hb : b₁ = x
          · simp only [ha, hb, ↓reduceIte]; have := hc₁_lt a₁ ha; omega
          · simp only [ha, hb, ↓reduceIte]; exact hc₁_p a₁ b₁ ha hb hadj
      · by_cases ha : a₁ = x
        · by_cases hb : b₂ = y
          · exfalso; exact hne (by subst ha hb; exact Set.mem_singleton _)
          · simp only [ha, hb, ↓reduceIte]; have := hc₂_lt b₂ hb; omega
        · by_cases hb : b₂ = y
          · simp only [ha, hb, ↓reduceIte]; have := hc₁_lt a₁ ha; omega
          · simp only [ha, hb, ↓reduceIte]; have := hc₁_lt a₁ ha; omega
      · by_cases ha : a₂ = y
        · by_cases hb : b₁ = x
          · exfalso; exact hne (by subst ha hb; rw [Sym2.eq_swap]; exact Set.mem_singleton _)
          · simp only [ha, hb, ↓reduceIte]; have := hc₁_lt b₁ hb; omega
        · by_cases hb : b₁ = x
          · simp only [ha, hb, ↓reduceIte]; have := hc₂_lt a₂ ha; omega
          · simp only [ha, hb, ↓reduceIte]; have := hc₁_lt b₁ hb; omega
      · by_cases ha : a₂ = y
        · have hb : b₂ ≠ y := by rintro rfl; exact G₂.ne_of_adj hadj ha
          simp only [ha, hb, ↓reduceIte]; have := hc₂_lt b₂ hb; omega
        · by_cases hb : b₂ = y
          · simp only [ha, hb, ↓reduceIte]; have := hc₂_lt a₂ ha; omega
          · simp only [ha, hb, ↓reduceIte]; intro heq; exact hc₂_p a₂ b₂ ha hb hadj (by omega)
    · rename_i y x
      rw [Sym2.eq_swap]
      obtain ⟨c₁, hc₁_lt, hc₁_p⟩ := isKCritical_del_vert_colorable hk₁ h₁ x
      obtain ⟨c₂, hc₂_lt, hc₂_p⟩ := isKCritical_del_vert_colorable hk₂ h₂ y
      refine colorable_of _ (k₁ + k₂ - 1)
        (Sum.elim (fun a => if a = x then k₁ + k₂ - 2 else c₁ a)
          (fun b => if b = y then k₁ + k₂ - 2 else (k₁ - 1) + c₂ b))
        (fun z => by
          cases z with
          | inl a =>
            simp only [Sum.elim_inl]
            by_cases ha : a = x
            · simp [ha]; omega
            · simp [ha]; have := hc₁_lt a ha; omega
          | inr b =>
            simp only [Sum.elim_inr]
            by_cases hb : b = y
            · simp [hb]; omega
            · simp [hb]; have := hc₂_lt b hb; omega)
        ?_
      intro a b hab
      rw [deleteEdges_adj] at hab
      obtain ⟨hadj, hne⟩ := hab
      rcases a with a₁ | a₂ <;> rcases b with b₁ | b₂ <;>
        simp only [joinSum, Sum.elim_inl, Sum.elim_inr] at hadj ⊢
      · by_cases ha : a₁ = x
        · have hb : b₁ ≠ x := by rintro rfl; exact G₁.ne_of_adj hadj ha
          simp only [ha, hb, ↓reduceIte]; have := hc₁_lt b₁ hb; omega
        · by_cases hb : b₁ = x
          · simp only [ha, hb, ↓reduceIte]; have := hc₁_lt a₁ ha; omega
          · simp only [ha, hb, ↓reduceIte]; exact hc₁_p a₁ b₁ ha hb hadj
      · by_cases ha : a₁ = x
        · by_cases hb : b₂ = y
          · exfalso; exact hne (by subst ha hb; exact Set.mem_singleton _)
          · simp only [ha, hb, ↓reduceIte]; have := hc₂_lt b₂ hb; omega
        · by_cases hb : b₂ = y
          · simp only [ha, hb, ↓reduceIte]; have := hc₁_lt a₁ ha; omega
          · simp only [ha, hb, ↓reduceIte]; have := hc₁_lt a₁ ha; omega
      · by_cases ha : a₂ = y
        · by_cases hb : b₁ = x
          · exfalso; exact hne (by subst ha hb; rw [Sym2.eq_swap]; exact Set.mem_singleton _)
          · simp only [ha, hb, ↓reduceIte]; have := hc₁_lt b₁ hb; omega
        · by_cases hb : b₁ = x
          · simp only [ha, hb, ↓reduceIte]; have := hc₂_lt a₂ ha; omega
          · simp only [ha, hb, ↓reduceIte]; have := hc₁_lt b₁ hb; omega
      · by_cases ha : a₂ = y
        · have hb : b₂ ≠ y := by rintro rfl; exact G₂.ne_of_adj hadj ha
          simp only [ha, hb, ↓reduceIte]; have := hc₂_lt b₂ hb; omega
        · by_cases hb : b₂ = y
          · simp only [ha, hb, ↓reduceIte]; have := hc₂_lt a₂ ha; omega
          · simp only [ha, hb, ↓reduceIte]; intro heq; exact hc₂_p a₂ b₂ ha hb hadj (by omega)
    · rename_i x y
      obtain ⟨C₁⟩ := isKCritical_colorable h₁
      obtain ⟨C₂⟩ := isKCritical_del_edge_colorable hk₂ h₂ huw
      refine colorable_of _ (k₁ + k₂ - 1)
        (Sum.elim (fun a => (C₁ a).val) (fun b => k₁ + (C₂ b).val))
        (fun z => by
          cases z with
          | inl a => simp only [Sum.elim_inl]; have := (C₁ a).isLt; omega
          | inr b => simp only [Sum.elim_inr]; have := (C₂ b).isLt; omega)
        ?_
      intro a b hab
      rw [deleteEdges_adj] at hab
      obtain ⟨hadj, hne⟩ := hab
      rcases a with a₁ | a₂ <;> rcases b with b₁ | b₂ <;>
        simp only [joinSum, Sum.elim_inl, Sum.elim_inr] at hadj ⊢
      · intro heq; exact C₁.valid hadj (Fin.ext heq)
      · have := (C₁ a₁).isLt; omega
      · have := (C₁ b₁).isLt; omega
      · intro heq
        have hadj' : (G₂.deleteEdges {s(x, y)}).Adj a₂ b₂ := by
          rw [deleteEdges_adj]
          refine ⟨hadj, ?_⟩
          intro hs
          apply hne
          rw [Set.mem_singleton_iff] at hs ⊢
          rcases Sym2.eq_iff.mp hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · rfl
          · exact Sym2.eq_swap
        exact C₂.valid hadj' (Fin.ext (by omega))

lemma joinGraph_ncard_edges {n₁ n₂ : ℕ} (G₁ : SimpleGraph (Fin n₁)) (G₂ : SimpleGraph (Fin n₂)) :
    (joinGraph G₁ G₂).edgeSet.ncard = G₁.edgeSet.ncard + G₂.edgeSet.ncard + n₁ * n₂ := by
  classical
  unfold joinGraph
  rw [ncard_edgeSet_map, ← coe_edgeFinset, ← coe_edgeFinset, ← coe_edgeFinset,
    Set.ncard_coe_finset, Set.ncard_coe_finset, Set.ncard_coe_finset]
  have hdeg_inl : ∀ x : Fin n₁, (joinSum G₁ G₂).degree (.inl x) = G₁.degree x + n₂ := by
    intro x
    rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree,
      neighborFinset_eq_filter, neighborFinset_eq_filter]
    have hset : univ.filter (fun z : Fin n₁ ⊕ Fin n₂ => (joinSum G₁ G₂).Adj (.inl x) z) =
        ((univ.filter (fun y : Fin n₁ => G₁.Adj x y)).image Sum.inl) ∪ (univ.image Sum.inr) := by
      ext z
      simp only [mem_union, mem_filter, mem_univ, true_and, mem_image]
      cases z <;> simp [joinSum]
    rw [hset, card_union_of_disjoint, card_image_of_injective _ Sum.inl_injective,
      card_image_of_injective _ Sum.inr_injective, card_univ, Fintype.card_fin]
    rw [Finset.disjoint_left]
    intro z hz₁ hz₂
    obtain ⟨_, _, rfl⟩ := mem_image.mp hz₁
    obtain ⟨_, _, h⟩ := mem_image.mp hz₂
    cases h
  have hdeg_inr : ∀ y : Fin n₂, (joinSum G₁ G₂).degree (.inr y) = n₁ + G₂.degree y := by
    intro y
    rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree,
      neighborFinset_eq_filter, neighborFinset_eq_filter]
    have hset : univ.filter (fun z : Fin n₁ ⊕ Fin n₂ => (joinSum G₁ G₂).Adj (.inr y) z) =
        (univ.image Sum.inl) ∪ ((univ.filter (fun w : Fin n₂ => G₂.Adj y w)).image Sum.inr) := by
      ext z
      simp only [mem_union, mem_filter, mem_univ, true_and, mem_image]
      cases z <;> simp [joinSum]
    rw [hset, card_union_of_disjoint, card_image_of_injective _ Sum.inl_injective,
      card_image_of_injective _ Sum.inr_injective, card_univ, Fintype.card_fin]
    rw [Finset.disjoint_left]
    intro z hz₁ hz₂
    obtain ⟨_, _, rfl⟩ := mem_image.mp hz₁
    obtain ⟨_, _, h⟩ := mem_image.mp hz₂
    cases h
  have h1 := sum_degrees_eq_twice_card_edges (joinSum G₁ G₂)
  have h2 := sum_degrees_eq_twice_card_edges G₁
  have h3 := sum_degrees_eq_twice_card_edges G₂
  have hsum : ∑ z : Fin n₁ ⊕ Fin n₂, (joinSum G₁ G₂).degree z =
      (∑ x : Fin n₁, (G₁.degree x + n₂)) + (∑ y : Fin n₂, (n₁ + G₂.degree y)) := by
    rw [Fintype.sum_sum_type]
    congr 1
    · exact sum_congr rfl fun x _ => hdeg_inl x
    · exact sum_congr rfl fun y _ => hdeg_inr y
  rw [sum_add_distrib, sum_add_distrib] at hsum
  simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at hsum
  have hcomm : n₂ * n₁ = n₁ * n₂ := Nat.mul_comm n₂ n₁
  omega

end OMA.DiracJoin

open OMA.DiracJoin

theorem OMA.solution : OMA.R_Erdos917_erdos_917_variants_three_dvd_R1.H2 := by
  rintro k₁ k₂ n₁ n₂ e₁ e₂ hk₁ hk₂ ⟨G,hG,rfl⟩ ⟨H,hH,rfl⟩
  exact ⟨joinGraph G H, joinGraph_critical (by omega) (by omega) hG hH,
    joinGraph_ncard_edges G H⟩

