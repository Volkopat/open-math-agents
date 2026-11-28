import OMAReductions.R_Erdos626_erdos_626_parts_i_R1

-- Step Erdos626.erdos_626.parts.i.R1.H2: hypothesis H2 of reduction Erdos626.erdos_626.parts.i.R1
-- Credit: @nnkostov
-- H2 := ∀ k : ℕ, 4 ≤ k → ∃ B : ℝ, ∀ i : ℕ, 0 < i →     (g k (2^i) : ℝ) ≤ B * i

/-!
# Linear bound in the dyadic exponent for `Erdos626.g` (`Erdos626.erdos_626.parts.i.R1.H2`)

We prove the Moore-type upper bound `Erdos626.g k (2 ^ i) ≤ 2 * i + 1 ≤ 3 * i` for every
`k ≥ 4` and `i > 0`, giving the explicit witness `B = 3`.

1. Any finite graph `G` with `G.chromaticNumber = k ≥ 4` admits a minimal non-`(k - 1)`-colorable
   induced subgraph `H = G.induce S` whose vertices are nonempty, have minimum degree at least
   `k - 1 ≥ 3`, and whose extended girth satisfies `G.egirth ≤ H.egirth`.
2. When `(2 * r : ℕ∞) < H.egirth`, extending a simple path of length `< r` to any neighbor
   other than its penultimate vertex yields a simple path, and two simple paths of length `≤ r`
   from the same root to the same endpoint must be equal.
3. Consequently, BFS layers of paths of length `t ≤ r` double at each step (`2 ^ t ≤ (layer t).card`),
   forcing `2 ^ r ≤ S.card ≤ 2 ^ i`, so `g k (2 ^ i) ≤ 2 * i + 1 ≤ 3 * i`.
-/

namespace OMA.Erdos626R1H2

open SimpleGraph Finset
open scoped Classical

/- Section 1: Minimal non-(k-1)-colorable induced subgraph -/

private lemma exists_critical_subgraph {n k : ℕ} (hk : 4 ≤ k) (G : SimpleGraph (Fin n))
    (hG : G.chromaticNumber = k) :
    ∃ (S : Finset (Fin n)), S.Nonempty ∧
      (∀ v : ↥(S : Set (Fin n)), k - 1 ≤ ((G.induce (S : Set (Fin n))).neighborFinset v).card) ∧
      G.egirth ≤ (G.induce (S : Set (Fin n))).egirth := by
  have hnot : ¬ G.Colorable (k - 1) := by
    intro hcol
    have hle := hcol.chromaticNumber_le
    rw [hG] at hle
    have hnat : k ≤ k - 1 := by exact_mod_cast hle
    omega
  let ℱ : Finset (Finset (Fin n)) :=
    Finset.univ.filter fun S => ¬ (G.induce (S : Set (Fin n))).Colorable (k - 1)
  have huniv : Finset.univ ∈ ℱ := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun hcol => hnot ?_⟩
    obtain ⟨c⟩ := hcol
    exact ⟨c.comp ⟨fun v => ⟨v, Finset.mem_univ v⟩, fun h => h⟩⟩
  obtain ⟨S, hSmem, hSmin⟩ := Finset.exists_min_image ℱ Finset.card ⟨Finset.univ, huniv⟩
  have hSnot : ¬ (G.induce (S : Set (Fin n))).Colorable (k - 1) :=
    (Finset.mem_filter.mp hSmem).2
  have hSne : S.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    subst hemp
    apply hSnot
    refine ⟨⟨fun v => False.elim (Finset.notMem_empty v.1 v.2), fun {v} =>
      False.elim (Finset.notMem_empty v.1 v.2)⟩⟩
  have hdeg : ∀ v : ↥(S : Set (Fin n)),
      k - 1 ≤ ((G.induce (S : Set (Fin n))).neighborFinset v).card := by
    intro v
    by_contra! hlt
    let S' := S.erase v.1
    have hcard_lt : S'.card < S.card := Finset.card_erase_lt_of_mem v.2
    have hS'not : S' ∉ ℱ := fun hm => (hSmin S' hm).not_gt hcard_lt
    have hS'col : (G.induce (S' : Set (Fin n))).Colorable (k - 1) := by
      by_contra hn
      exact hS'not (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩)
    obtain ⟨c⟩ := hS'col
    let Nv := (G.induce (S : Set (Fin n))).neighborFinset v
    let toS' : ∀ w ∈ Nv, ↥(S' : Set (Fin n)) := fun w hw =>
      ⟨w.1, Finset.mem_erase.mpr
        ⟨fun heq => ((G.induce _).ne_of_adj ((mem_neighborFinset _ _ _).mp hw))
          (Subtype.ext heq).symm, w.2⟩⟩
    let used : Finset (Fin (k - 1)) := Nv.attach.image fun w => c (toS' w.1 w.2)
    have hused_lt : used.card < k - 1 := by
      have h1 : used.card ≤ Nv.attach.card := Finset.card_image_le
      rw [Finset.card_attach] at h1
      exact h1.trans_lt hlt
    have hrem : (Finset.univ \ used).Nonempty := by
      apply Finset.card_pos.mp
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
      omega
    obtain ⟨col, hcol⟩ := hrem
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hcol
    apply hSnot
    refine ⟨⟨fun x => if hx : x = v then col else
        c ⟨x.1, Finset.mem_erase.mpr ⟨fun heq => hx (Subtype.ext heq), x.2⟩⟩, ?_⟩⟩
    intro x y hxy
    have hne : x ≠ y := (G.induce _).ne_of_adj hxy
    by_cases hx : x = v
    · have hy : y ≠ v := hx ▸ hne.symm
      simp only [dif_pos hx, dif_neg hy]
      intro heq
      apply hcol
      refine Finset.mem_image.mpr ⟨⟨y, (mem_neighborFinset _ _ _).mpr (hx ▸ hxy)⟩,
        Finset.mem_attach _ _, ?_⟩
      exact heq.symm
    · by_cases hy : y = v
      · simp only [dif_neg hx, dif_pos hy]
        intro heq
        apply hcol
        refine Finset.mem_image.mpr ⟨⟨x, (mem_neighborFinset _ _ _).mpr (hy ▸ hxy.symm)⟩,
          Finset.mem_attach _ _, ?_⟩
        exact heq
      · simp only [dif_neg hx, dif_neg hy]
        exact c.valid hxy
  have hgirth : G.egirth ≤ (G.induce (S : Set (Fin n))).egirth := by
    apply SimpleGraph.le_egirth.mpr
    intro a w hw
    let f : G.induce (S : Set (Fin n)) →g G := ⟨Subtype.val, fun h => h⟩
    have hmap : (w.map f).IsCycle := hw.map Subtype.val_injective
    have hlen : (w.map f).length = w.length := by simp
    rw [← hlen]
    exact SimpleGraph.egirth_le_length hmap
  exact ⟨S, hSne, hdeg, hgirth⟩

/- Section 2: Path extension and uniqueness below half girth -/

private lemma walk_eq_of_length_eq_zero {V : Type*} {H : SimpleGraph V} {u v : V}
    (q : H.Walk u v) (hq : q.length = 0) : u = v := by
  cases q with
  | nil => rfl
  | cons _ _ => simp at hq

private lemma isPath_concat_of_lt_egirth {V : Type*} {H : SimpleGraph V} {r : ℕ}
    (hgirth : (2 * r : ℕ∞) < H.egirth) {v₀ u w : V} {p : H.Walk v₀ u}
    (hp : p.IsPath) (ht : p.length < r) (hadj : H.Adj u w) (hpen : w ≠ p.penultimate) :
    (p.concat hadj).IsPath := by
  have hw_not : w ∉ p.support := by
    intro hx
    let q : H.Walk w u := p.dropUntil w hx
    have hq_path : q.IsPath := hp.dropUntil hx
    have hq_le : q.length ≤ p.length := Walk.length_dropUntil_le_length p hx
    have hq_ne0 : q.length ≠ 0 := by
      intro h0
      exact H.ne_of_adj hadj (walk_eq_of_length_eq_zero q h0).symm
    have hq_ne1 : q.length ≠ 1 := by
      intro h1
      have hspec := p.take_spec hx
      have hlen : (p.takeUntil w hx).length + q.length = p.length := by
        have := congrArg Walk.length hspec
        rwa [Walk.length_append] at this
      have hp_sub : p.length - 1 = (p.takeUntil w hx).length := by omega
      have hpen_eq : p.penultimate = w := by
        change p.getVert (p.length - 1) = w
        rw [hp_sub]
        conv_lhs => arg 1; rw [← hspec]
        rw [Walk.getVert_append]
        simp
      exact hpen hpen_eq.symm
    have hcyc : (Walk.cons hadj q).IsCycle := by
      rw [Walk.isCycle_def, Walk.isTrail_cons]
      refine ⟨⟨hq_path.isTrail, ?_⟩, by simp, hq_path.support_nodup⟩
      intro he
      have he' : s(w, u) ∈ q.edges := by rwa [Sym2.eq_swap]
      exact hq_ne1 (hq_path.length_eq_one_of_mem_edges he')
    have hle_girth : H.egirth ≤ ((Walk.cons hadj q).length : ℕ∞) :=
      SimpleGraph.egirth_le_length hcyc
    have hlen_le : (Walk.cons hadj q).length ≤ 2 * r := by
      rw [Walk.length_cons]
      omega
    have hle_2r : ((Walk.cons hadj q).length : ℕ∞) ≤ (2 * r : ℕ∞) := by
      exact_mod_cast hlen_le
    exact not_lt_of_ge (hle_girth.trans hle_2r) hgirth
  rw [Walk.isPath_def, Walk.support_concat, List.nodup_append]
  exact ⟨hp.support_nodup, List.nodup_singleton w,
    fun _ ha _ hb heq => hw_not ((heq.trans (List.mem_singleton.mp hb)) ▸ ha)⟩

private lemma eq_of_isPath_length_le {V : Type*} {H : SimpleGraph V} {r : ℕ}
    (hgirth : (2 * r : ℕ∞) < H.egirth) {v₀ u : V} {p q : H.Walk v₀ u}
    (hp : p.IsPath) (hq : q.IsPath) (hplen : p.length ≤ r) (hqlen : q.length ≤ r) :
    p = q := by
  by_contra hne
  obtain ⟨u', v', p', q', hp', hq', hcyc⟩ := Walk.IsPath.exists_isCycle_of_ne hp hq hne
  have hle_girth : H.egirth ≤ ((p'.append q'.reverse).length : ℕ∞) :=
    SimpleGraph.egirth_le_length hcyc
  have hp'_le : p'.length ≤ p.length := Walk.length_le_of_isSubwalk hp'
  have hq'_le : q'.length ≤ q.length := Walk.length_le_of_isSubwalk hq'
  have hlen_le : (p'.append q'.reverse).length ≤ 2 * r := by
    rw [Walk.length_append, Walk.length_reverse]
    omega
  have hle_2r : ((p'.append q'.reverse).length : ℕ∞) ≤ (2 * r : ℕ∞) := by
    exact_mod_cast hlen_le
  exact not_lt_of_ge (hle_girth.trans hle_2r) hgirth

/- Section 3: Moore exponential layer growth -/

private lemma moore_bound {V : Type*} [Fintype V] (H : SimpleGraph V) (v₀ : V) (r : ℕ)
    (hdeg : ∀ v : V, 3 ≤ (H.neighborFinset v).card) (hgirth : (2 * r : ℕ∞) < H.egirth) :
    2 ^ r ≤ Fintype.card V := by
  let layer (t : ℕ) : Finset V :=
    Finset.univ.filter fun u => ∃ p : H.Walk v₀ u, p.IsPath ∧ p.length = t
  have hgrow : ∀ t ≤ r, 2 ^ t ≤ (layer t).card := by
    intro t ht
    induction t with
    | zero =>
      have hv0 : v₀ ∈ layer 0 :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, Walk.nil, Walk.IsPath.nil, rfl⟩
      exact Finset.card_pos.mpr ⟨v₀, hv0⟩
    | succ t ih =>
      have htr : t < r := by omega
      have ih_t : 2 ^ t ≤ (layer t).card := ih htr.le
      let children (u : V) : Finset V :=
        if hu : u ∈ layer t then
          (H.neighborFinset u).erase (Classical.choose (Finset.mem_filter.mp hu).2).penultimate
        else ∅
      have hch_card : ∀ u ∈ layer t, 2 ≤ (children u).card := by
        intro u hu
        dsimp only [children]
        rw [dif_pos hu]
        have hpred := Finset.pred_card_le_card_erase (s := H.neighborFinset u)
          (a := (Classical.choose (Finset.mem_filter.mp hu).2).penultimate)
        have hd := hdeg u
        omega
      have hch_sub : (layer t).biUnion children ⊆ layer (t + 1) := by
        intro w hw
        obtain ⟨u, hu, hwu⟩ := Finset.mem_biUnion.mp hw
        dsimp only [children] at hwu
        rw [dif_pos hu] at hwu
        obtain ⟨hw_ne, hw_mem⟩ := Finset.mem_erase.mp hwu
        have hadj : H.Adj u w := (mem_neighborFinset H u w).mp hw_mem
        let p := Classical.choose (Finset.mem_filter.mp hu).2
        have hpspec : p.IsPath ∧ p.length = t :=
          Classical.choose_spec (Finset.mem_filter.mp hu).2
        have hpath' : (p.concat hadj).IsPath :=
          isPath_concat_of_lt_egirth hgirth hpspec.1 (by rw [hpspec.2]; exact htr) hadj hw_ne
        have hlen' : (p.concat hadj).length = t + 1 := by
          rw [Walk.length_concat, hpspec.2]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, p.concat hadj, hpath', hlen'⟩
      have hch_disj : ((layer t : Set V)).PairwiseDisjoint children := by
        intro u₁ hu₁ u₂ hu₂ hne
        change Disjoint (children u₁) (children u₂)
        rw [Finset.disjoint_left]
        intro w hw₁ hw₂
        have hu₁' : u₁ ∈ layer t := hu₁
        have hu₂' : u₂ ∈ layer t := hu₂
        dsimp only [children] at hw₁ hw₂
        rw [dif_pos hu₁'] at hw₁
        rw [dif_pos hu₂'] at hw₂
        obtain ⟨hpen₁, hw_mem₁⟩ := Finset.mem_erase.mp hw₁
        obtain ⟨hpen₂, hw_mem₂⟩ := Finset.mem_erase.mp hw₂
        have hadj₁ : H.Adj u₁ w := (mem_neighborFinset H u₁ w).mp hw_mem₁
        have hadj₂ : H.Adj u₂ w := (mem_neighborFinset H u₂ w).mp hw_mem₂
        let p₁ := Classical.choose (Finset.mem_filter.mp hu₁').2
        let p₂ := Classical.choose (Finset.mem_filter.mp hu₂').2
        have hs₁ : p₁.IsPath ∧ p₁.length = t :=
          Classical.choose_spec (Finset.mem_filter.mp hu₁').2
        have hs₂ : p₂.IsPath ∧ p₂.length = t :=
          Classical.choose_spec (Finset.mem_filter.mp hu₂').2
        have hp₁ : (p₁.concat hadj₁).IsPath :=
          isPath_concat_of_lt_egirth hgirth hs₁.1 (by rw [hs₁.2]; exact htr) hadj₁ hpen₁
        have hp₂ : (p₂.concat hadj₂).IsPath :=
          isPath_concat_of_lt_egirth hgirth hs₂.1 (by rw [hs₂.2]; exact htr) hadj₂ hpen₂
        have heq_walk : p₁.concat hadj₁ = p₂.concat hadj₂ :=
          eq_of_isPath_length_le hgirth hp₁ hp₂
            (by rw [Walk.length_concat, hs₁.2]; exact ht)
            (by rw [Walk.length_concat, hs₂.2]; exact ht)
        have heq_pen : (p₁.concat hadj₁).penultimate = (p₂.concat hadj₂).penultimate :=
          congrArg Walk.penultimate heq_walk
        rw [Walk.penultimate_concat, Walk.penultimate_concat] at heq_pen
        exact hne heq_pen
      calc
        2 ^ (t + 1) = (2 : ℕ) * 2 ^ t := by rw [pow_succ, mul_comm]
        _ ≤ 2 * (layer t).card := Nat.mul_le_mul_left 2 ih_t
        _ = ∑ _u ∈ layer t, 2 := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
        _ ≤ ∑ u ∈ layer t, (children u).card := Finset.sum_le_sum hch_card
        _ = ((layer t).biUnion children).card := (Finset.card_biUnion hch_disj).symm
        _ ≤ (layer (t + 1)).card := Finset.card_le_card hch_sub
  exact (hgrow r le_rfl).trans (Finset.card_le_univ (layer r))

/- Section 4: Conclusion for Erdos626.g -/

private lemma g_le_three_mul (k i : ℕ) (hk : 4 ≤ k) (hi : 0 < i) :
    Erdos626.g k (2 ^ i) ≤ 3 * i := by
  unfold Erdos626.g
  apply csSup_le'
  rintro m ⟨G, hG, hm⟩
  obtain ⟨S, ⟨v₀, hv₀⟩, hdeg, hgirth_le⟩ := exists_critical_subgraph hk G hG
  set H := G.induce (S : Set (Fin (2 ^ i)))
  have hgirth_m : (m : ℕ∞) < H.egirth := lt_of_lt_of_le hm hgirth_le
  let r := m / 2
  have h2r_le : (2 * r : ℕ∞) ≤ (m : ℕ∞) := by
    exact_mod_cast (by omega : 2 * r ≤ m)
  have hgirth_2r : (2 * r : ℕ∞) < H.egirth := lt_of_le_of_lt h2r_le hgirth_m
  have hdeg3 : ∀ v : ↥(S : Set (Fin (2 ^ i))), 3 ≤ (H.neighborFinset v).card := fun v => by
    have hv : k - 1 ≤ (H.neighborFinset v).card := hdeg v
    omega
  have hcard : 2 ^ r ≤ Fintype.card ↥(S : Set (Fin (2 ^ i))) :=
    moore_bound H ⟨v₀, hv₀⟩ r hdeg3 hgirth_2r
  have hcard_le : Fintype.card ↥(S : Set (Fin (2 ^ i))) ≤ 2 ^ i := by
    rw [show Fintype.card ↥(S : Set (Fin (2 ^ i))) = S.card from Fintype.card_coe S]
    exact (Finset.card_le_univ S).trans_eq (Fintype.card_fin (2 ^ i))
  have hr_le : r ≤ i := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp (hcard.trans hcard_le)
  omega

private lemma main_proof : OMA.R_Erdos626_erdos_626_parts_i_R1.H2 := by
  intro k hk
  refine ⟨3, fun i hi => ?_⟩
  exact_mod_cast g_le_three_mul k i hk hi

end OMA.Erdos626R1H2

theorem OMA.solution : OMA.R_Erdos626_erdos_626_parts_i_R1.H2 := OMA.Erdos626R1H2.main_proof
