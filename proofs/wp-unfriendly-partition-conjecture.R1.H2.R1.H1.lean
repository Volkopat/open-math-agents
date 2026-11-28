import OMAReductions.R_wp_unfriendly_partition_conjecture_R1_H2_R1
import Mathlib

/-!
# Aharoni-Milner-Prikry (1990): Countable graphs with finitely many infinite-degree vertices

Let `I` be the finite set of vertices of infinite degree in a countable simple graph `G`,
and `L = V \ I` the vertices of finite degree. Following Aharoni, Milner, and Prikry (1990):
1. Pinning `I` to `false` and maximizing finite cuts via Tychonoff compactness on `V → Bool`
   produces `c : V → Bool` with `c|_I = false` and nonpositive boundary flip gain `gain N F c ≤ 0`
   for every finite `F : Finset V` disjoint from `I`.
2. Flipping `B = {b ∈ I | {w | G.Adj b w ∧ c w = true}.Finite}` gives `c'` under which every
   `b ∈ I` has infinitely many opposite-colored neighbors, while increasing `gain N F` by at most
   a fixed finite bound `K` independent of `F`.
3. Choosing `F_*` disjoint from `I` maximizing `gain N F_* c'` and flipping `F_*` preserves
   infinite opposite-colored neighborhoods on `I` and makes every `x ∉ I` unfriendly by
   symmetric-difference telescoping `gain N {x} (flip F_* c') = gain N (symmDiff F_* {x}) c' - gain N F_* c' ≤ 0`.
-/

-- Credit: @qu1r0ra

namespace OMA.AMPFiniteInfiniteDegree

open SimpleGraph Finset

private def neighborSubtypeEquiv {V : Type} (G : SimpleGraph V) (N : V → Finset V)
    {v : V} (hNv : ∀ w, w ∈ N v ↔ G.Adj v w) (P : V → Prop) [DecidablePred P] :
    {w : V // G.Adj v w ∧ P w} ≃ ↥((N v).filter P) where
  toFun x := ⟨x.1, Finset.mem_filter.mpr ⟨(hNv x.1).mpr x.2.1, x.2.2⟩⟩
  invFun y := ⟨y.1, (hNv y.1).mp (Finset.mem_filter.mp y.2).1, (Finset.mem_filter.mp y.2).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private def UnfriendlyAt {V : Type} (N : V → Finset V) (f : V → Bool) (v : V) : Prop :=
  ((N v).filter fun w => f w = f v).card ≤ ((N v).filter fun w => f w ≠ f v).card

private lemma cardinal_le_of_unfriendlyAt {V : Type} (G : SimpleGraph V) (N : V → Finset V)
    {v : V} (hNv : ∀ w, w ∈ N v ↔ G.Adj v w) (f : V → Bool)
    (h : UnfriendlyAt N f v) :
    Cardinal.mk {w : V // G.Adj v w ∧ f w = f v} ≤
      Cardinal.mk {w : V // G.Adj v w ∧ f w ≠ f v} := by
  rw [Cardinal.mk_congr (neighborSubtypeEquiv G N hNv (fun w => f w = f v)),
      Cardinal.mk_congr (neighborSubtypeEquiv G N hNv (fun w => f w ≠ f v))]
  simp only [Cardinal.mk_fintype, Fintype.card_coe, Nat.cast_le]
  exact h

private lemma cardinal_le_of_infinite_diff {V : Type} [Countable V] (G : SimpleGraph V)
    (f : V → Bool) (v : V)
    (hinf : ({w : V | G.Adj v w ∧ f w ≠ f v} : Set V).Infinite) :
    Cardinal.mk {w : V // G.Adj v w ∧ f w = f v} ≤
      Cardinal.mk {w : V // G.Adj v w ∧ f w ≠ f v} := by
  have : Infinite {w : V // G.Adj v w ∧ f w ≠ f v} := hinf.to_subtype
  rw [Cardinal.mk_eq_aleph0 {w : V // G.Adj v w ∧ f w ≠ f v}]
  exact Cardinal.mk_le_aleph0

private def flip {V : Type} [DecidableEq V] (A : Finset V) (c : V → Bool) : V → Bool :=
  fun v => if v ∈ A then !c v else c v

private lemma flip_flip_symmDiff {V : Type} [DecidableEq V] (A B : Finset V) (c : V → Bool) :
    flip B (flip A c) = flip (symmDiff A B) c := by
  ext v
  by_cases hA : v ∈ A <;> by_cases hB : v ∈ B <;>
    simp [flip, Finset.mem_symmDiff, hA, hB]

private def edgeGain {V : Type} [DecidableEq V] (F : Finset V) (c : V → Bool) (x y : V) : ℤ :=
  if y ∉ F then (if c y = c x then 1 else -1) else 0

private def gain {V : Type} [DecidableEq V] (N : V → Finset V) (F : Finset V) (c : V → Bool) : ℤ :=
  ∑ x ∈ F, ∑ y ∈ N x, edgeGain F c x y

private lemma gain_empty {V : Type} [DecidableEq V] (N : V → Finset V) (c : V → Bool) :
    gain N ∅ c = 0 := by
  simp [gain]

private lemma unfriendlyAt_of_gain_singleton_le_zero {V : Type} [DecidableEq V] (G : SimpleGraph V)
    (N : V → Finset V) {x : V} (hNx : ∀ y, y ∈ N x ↔ G.Adj x y) (c : V → Bool)
    (h : gain N {x} c ≤ 0) :
    UnfriendlyAt N c x := by
  have hsum : gain N {x} c =
      (((N x).filter fun y => c y = c x).card : ℤ) -
        (((N x).filter fun y => c y ≠ c x).card : ℤ) := by
    unfold gain edgeGain
    rw [Finset.sum_singleton]
    rw [Finset.card_filter, Finset.card_filter]
    push_cast
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun y hy => ?_
    have hyx : y ≠ x := ((hNx y).mp hy).ne'
    have hnot : y ∉ ({x} : Finset V) := by simp [hyx]
    by_cases hcy : c y = c x <;> simp [hnot, hcy]
  rw [hsum] at h
  unfold UnfriendlyAt
  omega

private def cutScore {V : Type} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (f : V → Bool) : ℕ :=
  ∑ u ∈ S, ∑ w ∈ S, if G.Adj u w ∧ f u ≠ f w then 1 else 0

private def pairDelta {V : Type} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (F : Finset V) (h : V → Bool) (u w : V) : ℤ :=
  (if G.Adj u w ∧ flip F h u ≠ flip F h w then 1 else 0) -
    (if G.Adj u w ∧ h u ≠ h w then 1 else 0)

private lemma pairDelta_symm {V : Type} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (F : Finset V) (h : V → Bool) (u w : V) :
    pairDelta G F h u w = pairDelta G F h w u := by
  unfold pairDelta
  simp [G.adj_comm, ne_comm]

private lemma pairDelta_mem_mem {V : Type} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (F : Finset V) (h : V → Bool) {u w : V} (hu : u ∈ F) (hw : w ∈ F) :
    pairDelta G F h u w = 0 := by
  unfold pairDelta flip
  simp only [if_pos hu, if_pos hw]
  have hne : ((!h u) ≠ (!h w)) ↔ (h u ≠ h w) := by
    cases h u <;> cases h w <;> decide
  simp [hne]

private lemma pairDelta_notMem_notMem {V : Type} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (F : Finset V) (h : V → Bool) {u w : V} (hu : u ∉ F) (hw : w ∉ F) :
    pairDelta G F h u w = 0 := by
  unfold pairDelta flip
  simp [if_neg hu, if_neg hw]

private lemma pairDelta_mem_notMem {V : Type} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (F : Finset V) (h : V → Bool) {u w : V} (hu : u ∈ F) (hw : w ∉ F) :
    pairDelta G F h u w = if G.Adj u w then edgeGain F h u w else 0 := by
  unfold pairDelta flip edgeGain
  have hnw : ¬ (w ∈ F) := hw
  simp only [if_pos hu, if_neg hnw, if_pos hw]
  by_cases hadj : G.Adj u w
  · simp only [hadj, true_and, ite_true]
    cases h u <;> cases h w <;> decide
  · simp [hadj]

private lemma cutScore_flip_sub {V : Type} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (N : V → Finset V) {F S : Finset V}
    (hNF : ∀ x ∈ F, ∀ y, y ∈ N x ↔ G.Adj x y)
    (hFS : F ⊆ S) (hNS : ∀ x ∈ F, N x ⊆ S) (h : V → Bool) :
    (cutScore G S (flip F h) : ℤ) - (cutScore G S h : ℤ) = 2 * gain N F h := by
  have hcast : (cutScore G S (flip F h) : ℤ) - (cutScore G S h : ℤ) =
      ∑ u ∈ S, ∑ w ∈ S, pairDelta G F h u w := by
    unfold cutScore pairDelta
    push_cast
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [← Finset.sum_sub_distrib]
  rw [hcast]
  have hS_in : S.filter (fun x => x ∈ F) = F := by
    ext x
    simp only [Finset.mem_filter]
    exact ⟨fun hx => hx.2, fun hx => ⟨hFS hx, hx⟩⟩
  let SF := S.filter (fun x => x ∉ F)
  have hsplit_outer :
      (∑ u ∈ S, ∑ w ∈ S, pairDelta G F h u w) =
        (∑ u ∈ F, ∑ w ∈ S, pairDelta G F h u w) +
          (∑ u ∈ SF, ∑ w ∈ S, pairDelta G F h u w) := by
    have := (Finset.sum_filter_add_sum_filter_not S (fun u => u ∈ F)
      (fun u => ∑ w ∈ S, pairDelta G F h u w)).symm
    simpa [hS_in, SF] using this
  have h_in : ∀ u ∈ F, (∑ w ∈ S, pairDelta G F h u w) = ∑ w ∈ N u, edgeGain F h u w := by
    intro u hu
    have hsplit_inner :
        (∑ w ∈ S, pairDelta G F h u w) =
          (∑ w ∈ F, pairDelta G F h u w) + (∑ w ∈ SF, pairDelta G F h u w) := by
      have := (Finset.sum_filter_add_sum_filter_not S (fun w => w ∈ F)
        (fun w => pairDelta G F h u w)).symm
      simpa [hS_in, SF] using this
    have hz : (∑ w ∈ F, pairDelta G F h u w) = 0 :=
      Finset.sum_eq_zero fun w hw => pairDelta_mem_mem G F h hu hw
    rw [hsplit_inner, hz, zero_add]
    have h1 : (∑ w ∈ SF, pairDelta G F h u w) =
        ∑ w ∈ SF, if G.Adj u w then edgeGain F h u w else 0 := by
      refine Finset.sum_congr rfl fun w hw => ?_
      exact pairDelta_mem_notMem G F h hu (Finset.mem_filter.mp hw).2
    rw [h1, ← Finset.sum_filter]
    have h2 : (∑ w ∈ N u, edgeGain F h u w) =
        ∑ w ∈ (N u).filter (fun w => w ∉ F), edgeGain F h u w := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun w _ => ?_
      unfold edgeGain
      by_cases hwF : w ∈ F <;> simp [hwF]
    rw [h2]
    congr 1
    ext w
    simp only [SF, Finset.mem_filter]
    constructor
    · rintro ⟨⟨_, hwF⟩, hadj⟩
      exact ⟨(hNF u hu w).mpr hadj, hwF⟩
    · rintro ⟨hwN, hwF⟩
      exact ⟨⟨hNS u hu hwN, hwF⟩, (hNF u hu w).mp hwN⟩
  have h_out : (∑ u ∈ SF, ∑ w ∈ S, pairDelta G F h u w) =
      ∑ w ∈ F, ∑ u ∈ N w, edgeGain F h w u := by
    have hstep : ∀ u ∈ SF, (∑ w ∈ S, pairDelta G F h u w) = ∑ w ∈ F, pairDelta G F h w u := by
      intro u hu
      have huF : u ∉ F := (Finset.mem_filter.mp hu).2
      have hsplit_inner :
          (∑ w ∈ S, pairDelta G F h u w) =
            (∑ w ∈ F, pairDelta G F h u w) + (∑ w ∈ SF, pairDelta G F h u w) := by
        have := (Finset.sum_filter_add_sum_filter_not S (fun w => w ∈ F)
          (fun w => pairDelta G F h u w)).symm
        simpa [hS_in, SF] using this
      have hz : (∑ w ∈ SF, pairDelta G F h u w) = 0 :=
        Finset.sum_eq_zero fun w hw =>
          pairDelta_notMem_notMem G F h huF (Finset.mem_filter.mp hw).2
      rw [hsplit_inner, hz, add_zero]
      exact Finset.sum_congr rfl fun w _ => pairDelta_symm G F h u w
    rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
    refine Finset.sum_congr rfl fun w hw => ?_
    have h1 : (∑ u ∈ SF, pairDelta G F h w u) =
        ∑ u ∈ SF, if G.Adj w u then edgeGain F h w u else 0 := by
      refine Finset.sum_congr rfl fun u hu => ?_
      exact pairDelta_mem_notMem G F h hw (Finset.mem_filter.mp hu).2
    rw [h1, ← Finset.sum_filter]
    have h2 : (∑ u ∈ N w, edgeGain F h w u) =
        ∑ u ∈ (N w).filter (fun u => u ∉ F), edgeGain F h w u := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun u _ => ?_
      unfold edgeGain
      by_cases huF : u ∈ F <;> simp [huF]
    rw [h2]
    congr 1
    ext u
    simp only [SF, Finset.mem_filter]
    constructor
    · rintro ⟨⟨_, huF⟩, hadj⟩
      exact ⟨(hNF w hw u).mpr hadj, huF⟩
    · rintro ⟨huN, huF⟩
      exact ⟨⟨hNS w hw huN, huF⟩, (hNF w hw u).mp huN⟩
  rw [hsplit_outer, Finset.sum_congr rfl h_in, h_out]
  unfold gain
  omega

private lemma gain_singleton_flip {V : Type} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (N : V → Finset V) (I F : Finset V) {x : V}
    (hN : ∀ v, v ∉ I → ∀ y, y ∈ N v ↔ G.Adj v y)
    (hFI : Disjoint F I) (hxI : x ∉ I) (c : V → Bool) :
    gain N {x} (flip F c) = gain N (symmDiff F {x}) c - gain N F c := by
  let U : Finset V := insert x F
  have hUI : ∀ z ∈ U, z ∉ I := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hzF
    · exact hxI
    · exact Finset.disjoint_left.mp hFI hzF
  let S : Finset V := U ∪ U.biUnion N
  have hU_sub : U ⊆ S := Finset.subset_union_left
  have hN_sub : ∀ z ∈ U, N z ⊆ S := fun z hz y hy =>
    Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨z, hz, hy⟩)
  have hF_U : F ⊆ U := Finset.subset_insert x F
  have hx_U : ({x} : Finset V) ⊆ U := Finset.singleton_subset_iff.mpr (Finset.mem_insert_self x F)
  have hsd_U : symmDiff F {x} ⊆ U := by
    intro z hz
    rcases Finset.mem_symmDiff.mp hz with ⟨hzF, _⟩ | ⟨hzx, _⟩
    · exact Finset.mem_insert_of_mem hzF
    · exact Finset.mem_insert.mpr (Or.inl (Finset.mem_singleton.mp hzx))
  have e1 := cutScore_flip_sub G N (fun z hz => hN z (hUI z (hF_U hz)))
    (hF_U.trans hU_sub) (fun z hz => hN_sub z (hF_U hz)) c
  have e2 := cutScore_flip_sub G N (fun z hz => hN z (hUI z (hx_U hz)))
    (hx_U.trans hU_sub) (fun z hz => hN_sub z (hx_U hz)) (flip F c)
  have e3 := cutScore_flip_sub G N (fun z hz => hN z (hUI z (hsd_U hz)))
    (hsd_U.trans hU_sub) (fun z hz => hN_sub z (hsd_U hz)) c
  rw [flip_flip_symmDiff] at e2
  omega

private lemma exists_max_pinned_cutScore {V : Type} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (I S : Finset V) :
    ∃ f : V → Bool, (∀ b ∈ I, f b = false) ∧
      ∀ f' : V → Bool, (∀ b ∈ I, f' b = false) → cutScore G S f' ≤ cutScore G S f := by
  have hbdd : ∀ f' : V → Bool, cutScore G S f' ≤ S.card * S.card := by
    intro f'
    unfold cutScore
    calc
      (∑ u ∈ S, ∑ w ∈ S, if G.Adj u w ∧ f' u ≠ f' w then 1 else 0)
        ≤ ∑ _u ∈ S, ∑ _w ∈ S, 1 := by
          refine Finset.sum_le_sum fun _ _ => Finset.sum_le_sum fun _ _ => ?_
          split_ifs <;> omega
      _ = S.card * S.card := by simp
  let P : ℕ → Prop := fun k => ∃ f : V → Bool, (∀ b ∈ I, f b = false) ∧ cutScore G S f = k
  let _ : DecidablePred P := Classical.decPred P
  let scores : Finset ℕ := (Finset.Iic (S.card * S.card)).filter P
  have hne : scores.Nonempty := by
    refine ⟨cutScore G S (fun _ => false), Finset.mem_filter.mpr ?_⟩
    exact ⟨Finset.mem_Iic.mpr (hbdd _), ⟨fun _ => false, fun _ _ => rfl, rfl⟩⟩
  obtain ⟨m, hm⟩ := Finset.max_of_nonempty hne
  obtain ⟨_, f, hfI, hfm⟩ := Finset.mem_filter.mp (Finset.mem_of_max hm)
  refine ⟨f, hfI, fun f' hf'I => ?_⟩
  rw [hfm]
  have hf'_mem : cutScore G S f' ∈ scores :=
    Finset.mem_filter.mpr ⟨Finset.mem_Iic.mpr (hbdd f'), ⟨f', hf'I, rfl⟩⟩
  exact Finset.le_max_of_eq hf'_mem hm

private theorem isClosed_pinned_gain_le_zero {V : Type} [DecidableEq V]
    (N : V → Finset V) (I F : Finset V) :
    IsClosed {f : V → Bool | (∀ b ∈ I, f b = false) ∧ gain N F f ≤ 0} := by
  let K : Finset V := I ∪ (F ∪ F.biUnion N)
  let res : (V → Bool) → (↥K → Bool) := fun f x => f x.1
  have hcont : Continuous res := continuous_pi fun x => continuous_apply x.1
  have hI_K : ∀ b ∈ I, b ∈ K := fun b hb => Finset.mem_union_left _ hb
  have hF_K : ∀ x ∈ F, x ∈ K := fun x hx =>
    Finset.mem_union_right _ (Finset.mem_union_left _ hx)
  have hN_K : ∀ x ∈ F, ∀ y ∈ N x, y ∈ K := fun x hx y hy =>
    Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨x, hx, hy⟩))
  let good : Set (↥K → Bool) :=
    {g | (∀ b : ↥I, g ⟨b.1, hI_K b.1 b.2⟩ = false) ∧
      (∑ x ∈ F.attach, ∑ y ∈ (N x.1).attach,
        if y.1 ∉ F then
          (if g ⟨y.1, hN_K x.1 x.2 y.1 y.2⟩ = g ⟨x.1, hF_K x.1 x.2⟩ then (1 : ℤ) else -1)
        else 0) ≤ 0}
  have hclosed_good : IsClosed good := isClosed_discrete good
  have heq : {f : V → Bool | (∀ b ∈ I, f b = false) ∧ gain N F f ≤ 0} = res ⁻¹' good := by
    ext f
    change ((∀ b ∈ I, f b = false) ∧ gain N F f ≤ 0) ↔
      ((∀ b : ↥I, f b.1 = false) ∧
        (∑ x ∈ F.attach, ∑ y ∈ (N x.1).attach, edgeGain F f x.1 y.1) ≤ 0)
    have h1 : (∀ b ∈ I, f b = false) ↔ (∀ b : ↥I, f b.1 = false) :=
      ⟨fun h b => h b.1 b.2, fun h b hb => h ⟨b, hb⟩⟩
    have h2 : (∑ x ∈ F.attach, ∑ y ∈ (N x.1).attach, edgeGain F f x.1 y.1) = gain N F f := by
      unfold gain
      rw [Finset.sum_attach F (fun x => ∑ y ∈ (N x).attach, edgeGain F f x y)]
      refine Finset.sum_congr rfl fun x _ => ?_
      exact Finset.sum_attach (N x) (fun y => edgeGain F f x y)
    rw [h1, h2]
  rw [heq]
  exact hclosed_good.preimage hcont

private lemma exists_pinned_nonpos_gain {V : Type} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (N : V → Finset V) (I : Finset V)
    (hN : ∀ v, v ∉ I → ∀ y, y ∈ N v ↔ G.Adj v y) :
    ∃ c : V → Bool, (∀ b ∈ I, c b = false) ∧
      ∀ F : Finset V, Disjoint F I → gain N F c ≤ 0 := by
  let Idx := {F : Finset V // Disjoint F I}
  let C : Idx → Set (V → Bool) := fun idx =>
    {f | (∀ b ∈ I, f b = false) ∧ gain N idx.1 f ≤ 0}
  have hclosed : ∀ idx : Idx, IsClosed (C idx) := fun idx =>
    isClosed_pinned_gain_le_zero N I idx.1
  have hfip : ∀ ℱ : Finset Idx, (Set.univ ∩ ⋂ idx ∈ ℱ, C idx).Nonempty := by
    intro ℱ
    let U : Finset V := ℱ.biUnion fun idx => idx.1
    let S : Finset V := I ∪ (U ∪ U.biUnion N)
    obtain ⟨f, hfI, hmax⟩ := exists_max_pinned_cutScore G I S
    refine ⟨f, Set.mem_univ f, Set.mem_iInter₂.mpr ?_⟩
    intro idx hidx
    refine ⟨hfI, ?_⟩
    have hflipI : ∀ b ∈ I, flip idx.1 f b = false := by
      intro b hb
      have hbF : b ∉ idx.1 := Finset.disjoint_right.mp idx.2 hb
      simp [flip, hbF, hfI b hb]
    have hle : cutScore G S (flip idx.1 f) ≤ cutScore G S f := hmax (flip idx.1 f) hflipI
    have hFU : idx.1 ⊆ U := fun x hx => Finset.mem_biUnion.mpr ⟨idx, hidx, hx⟩
    have hFS : idx.1 ⊆ S := fun x hx =>
      Finset.mem_union_right _ (Finset.mem_union_left _ (hFU hx))
    have hNS : ∀ x ∈ idx.1, N x ⊆ S := fun x hx y hy =>
      Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨x, hFU hx, hy⟩))
    have hNF : ∀ x ∈ idx.1, ∀ y, y ∈ N x ↔ G.Adj x y := fun x hx =>
      hN x (Finset.disjoint_left.mp idx.2 hx)
    have hsub := cutScore_flip_sub G N hNF hFS hNS f
    omega
  obtain ⟨c, -, hc⟩ := isCompact_univ.inter_iInter_nonempty C hclosed hfip
  have hc0 : c ∈ C ⟨∅, Finset.disjoint_empty_left I⟩ := Set.mem_iInter.mp hc ⟨∅, _⟩
  refine ⟨c, hc0.1, fun F hFI => ?_⟩
  exact (Set.mem_iInter.mp hc ⟨F, hFI⟩).2

private lemma edgeGain_flip_B_sub_le {V : Type} [DecidableEq V] (G : SimpleGraph V)
    (I B F : Finset V) (c : V → Bool)
    (hBI : B ⊆ I) (hcI : ∀ b ∈ I, c b = false) (hFI : Disjoint F I)
    {x y : V} (hxF : x ∈ F) (hadj : G.Adj x y)
    (hnot_bad : ¬ (y ∈ B ∧ G.Adj y x ∧ c x = true)) :
    edgeGain F (flip B c) x y ≤ edgeGain F c x y := by
  have hxB : x ∉ B := fun hxB => Finset.disjoint_left.mp hFI hxF (hBI hxB)
  unfold edgeGain
  by_cases hyF : y ∈ F
  · simp [hyF]
  · simp only [hyF, not_false_eq_true, ite_true]
    by_cases hyB : y ∈ B
    · have hcy : c y = false := hcI y (hBI hyB)
      have hcx : c x = false := by
        cases hval : c x
        · rfl
        · exfalso
          exact hnot_bad ⟨hyB, hadj.symm, hval⟩
      simp [flip, hxB, hyB, hcy, hcx]
    · simp [flip, hxB, hyB]

private lemma edgeGain_sub_le_two {V : Type} [DecidableEq V] (F : Finset V)
    (c₁ c₂ : V → Bool) (x y : V) :
    edgeGain F c₁ x y - edgeGain F c₂ x y ≤ 2 := by
  unfold edgeGain
  by_cases hyF : y ∈ F
  · simp [hyF]
  · simp only [hyF, not_false_eq_true, ite_true]
    split_ifs <;> omega

private lemma infinite_diff_after_flips {V : Type} (G : SimpleGraph V) [DecidableEq V]
    (I B F : Finset V) (c : V → Bool)
    (hcI : ∀ b ∈ I, c b = false)
    (hB_iff : ∀ b ∈ I, b ∈ B ↔ ({w : V | G.Adj b w ∧ c w = true} : Set V).Finite)
    (hFI : Disjoint F I) {b : V} (hbI : b ∈ I)
    (hbinf : (G.neighborSet b).Infinite) :
    ({w : V | G.Adj b w ∧ flip F (flip B c) w ≠ flip F (flip B c) b} : Set V).Infinite := by
  have hbF : b ∉ F := Finset.disjoint_right.mp hFI hbI
  let A : Finset V := B ∪ F
  have hAf : (A : Set V).Finite := A.finite_toSet
  by_cases hbB : b ∈ B
  · have hS1_fin : ({w : V | G.Adj b w ∧ c w = true} : Set V).Finite :=
      (hB_iff b hbI).mp hbB
    have hS0_inf : ({w : V | G.Adj b w ∧ c w = false} : Set V).Infinite := by
      intro hS0_fin
      apply hbinf
      have hunion : G.neighborSet b =
          ({w : V | G.Adj b w ∧ c w = true} : Set V) ∪
            ({w : V | G.Adj b w ∧ c w = false} : Set V) := by
        ext w
        simp only [SimpleGraph.mem_neighborSet, Set.mem_union]
        change G.Adj b w ↔ (G.Adj b w ∧ c w = true) ∨ (G.Adj b w ∧ c w = false)
        cases c w <;> simp
      rw [hunion]
      exact hS1_fin.union hS0_fin
    have hdiff_inf : (({w : V | G.Adj b w ∧ c w = false} : Set V) \ (A : Set V)).Infinite :=
      hS0_inf.sdiff hAf
    refine hdiff_inf.mono ?_
    intro w ⟨⟨hadj, hcw⟩, hwA⟩
    have hwB : w ∉ B := fun h => hwA (Finset.mem_coe.mpr (Finset.mem_union_left _ h))
    have hwF : w ∉ F := fun h => hwA (Finset.mem_coe.mpr (Finset.mem_union_right _ h))
    refine ⟨hadj, ?_⟩
    simp [flip, hbF, hbB, hwF, hwB, hcw, hcI b hbI]
  · have hS1_inf : ({w : V | G.Adj b w ∧ c w = true} : Set V).Infinite :=
      fun hfin => hbB ((hB_iff b hbI).mpr hfin)
    have hdiff_inf : (({w : V | G.Adj b w ∧ c w = true} : Set V) \ (A : Set V)).Infinite :=
      hS1_inf.sdiff hAf
    refine hdiff_inf.mono ?_
    intro w ⟨⟨hadj, hcw⟩, hwA⟩
    have hwB : w ∉ B := fun h => hwA (Finset.mem_coe.mpr (Finset.mem_union_left _ h))
    have hwF : w ∉ F := fun h => hwA (Finset.mem_coe.mpr (Finset.mem_union_right _ h))
    refine ⟨hadj, ?_⟩
    simp [flip, hbF, hbB, hwF, hwB, hcw, hcI b hbI]

private lemma finish_from_pinned {V : Type} [Countable V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (N : V → Finset V) (I B M₀ : Finset V) (c : V → Bool)
    (hI_mem : ∀ v : V, v ∈ I ↔ (G.neighborSet v).Infinite)
    (hN : ∀ v, v ∉ I → ∀ y, y ∈ N v ↔ G.Adj v y)
    (hcI : ∀ b ∈ I, c b = false)
    (hgain_c : ∀ F : Finset V, Disjoint F I → gain N F c ≤ 0)
    (hBI : B ⊆ I)
    (hB_iff : ∀ b ∈ I, b ∈ B ↔ ({w : V | G.Adj b w ∧ c w = true} : Set V).Finite)
    (hM₀ : ∀ x, x ∉ I → ∀ y ∈ B, G.Adj y x → c x = true → x ∈ M₀) :
    ∃ f : V → Bool, OMA.S_wp_unfriendly_partition_conjecture.IsUnfriendlyPartition G f := by
  have hgain_bdd : ∀ F : Finset V, Disjoint F I →
      gain N F (flip B c) ≤ ((∑ x ∈ M₀, 2 * (N x).card : ℕ) : ℤ) := by
    intro F hFI
    have hdiff_le : gain N F (flip B c) - gain N F c ≤ ((∑ x ∈ M₀, 2 * (N x).card : ℕ) : ℤ) := by
      unfold gain
      rw [← Finset.sum_sub_distrib]
      have hterm_le : ∀ x ∈ F,
          (∑ y ∈ N x, edgeGain F (flip B c) x y) - (∑ y ∈ N x, edgeGain F c x y) ≤
            if x ∈ M₀ then (2 * (N x).card : ℤ) else 0 := by
        intro x hxF
        rw [← Finset.sum_sub_distrib]
        by_cases hxM : x ∈ M₀
        · rw [if_pos hxM]
          calc
            (∑ y ∈ N x, (edgeGain F (flip B c) x y - edgeGain F c x y))
              ≤ ∑ _y ∈ N x, (2 : ℤ) :=
                Finset.sum_le_sum fun y _ => edgeGain_sub_le_two F (flip B c) c x y
            _ = (2 * (N x).card : ℤ) := by simp [mul_comm]
        · rw [if_neg hxM]
          refine Finset.sum_nonpos fun y hyN => ?_
          have hxI : x ∉ I := Finset.disjoint_left.mp hFI hxF
          have hadj : G.Adj x y := (hN x hxI y).mp hyN
          have hnot_bad : ¬ (y ∈ B ∧ G.Adj y x ∧ c x = true) := by
            rintro ⟨hyB, hyx, hcx⟩
            exact hxM (hM₀ x hxI y hyB hyx hcx)
          have hle := edgeGain_flip_B_sub_le G I B F c hBI hcI hFI hxF hadj hnot_bad
          omega
      calc
        (∑ x ∈ F, ((∑ y ∈ N x, edgeGain F (flip B c) x y) - (∑ y ∈ N x, edgeGain F c x y)))
          ≤ ∑ x ∈ F, if x ∈ M₀ then (2 * (N x).card : ℤ) else 0 :=
            Finset.sum_le_sum hterm_le
        _ = ∑ x ∈ F.filter (fun x => x ∈ M₀), (2 * (N x).card : ℤ) := by
            rw [Finset.sum_filter]
        _ ≤ ∑ x ∈ M₀, (2 * (N x).card : ℤ) := by
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => by positivity
            intro x hx
            exact (Finset.mem_filter.mp hx).2
        _ = ((∑ x ∈ M₀, 2 * (N x).card : ℕ) : ℤ) := by
            push_cast
            rfl
    have hc_le : gain N F c ≤ 0 := hgain_c F hFI
    omega
  let K : ℕ := ∑ x ∈ M₀, 2 * (N x).card
  let Q : ℤ → Prop := fun z => ∃ F : Finset V, Disjoint F I ∧ gain N F (flip B c) = z
  let _ : DecidablePred Q := Classical.decPred Q
  let scores : Finset ℤ := (Finset.Icc (0 : ℤ) (K : ℤ)).filter Q
  have h0_mem : (0 : ℤ) ∈ scores := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_rfl, Nat.cast_nonneg K⟩, ?_⟩
    exact ⟨∅, Finset.disjoint_empty_left I, gain_empty N (flip B c)⟩
  obtain ⟨m, hm⟩ := Finset.max_of_nonempty ⟨0, h0_mem⟩
  obtain ⟨hm_Icc, F_star, hF_star_I, hF_star_eq⟩ := Finset.mem_filter.mp (Finset.mem_of_max hm)
  have hm_nonneg : (0 : ℤ) ≤ m := (Finset.mem_Icc.mp hm_Icc).1
  have hF_star_max : ∀ F : Finset V, Disjoint F I →
      gain N F (flip B c) ≤ gain N F_star (flip B c) := by
    intro F hFI
    rw [hF_star_eq]
    by_cases h0 : 0 ≤ gain N F (flip B c)
    · have hmem : gain N F (flip B c) ∈ scores :=
        Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨h0, hgain_bdd F hFI⟩, ⟨F, hFI, rfl⟩⟩
      exact Finset.le_max_of_eq hmem hm
    · omega
  refine ⟨flip F_star (flip B c), fun v => ?_⟩
  by_cases hvI : v ∈ I
  · have hvinf : (G.neighborSet v).Infinite := (hI_mem v).mp hvI
    have hdiff_inf := infinite_diff_after_flips G I B F_star c hcI hB_iff hF_star_I hvI hvinf
    exact cardinal_le_of_infinite_diff G (flip F_star (flip B c)) v hdiff_inf
  · have hsd_I : Disjoint (symmDiff F_star {v}) I := by
      rw [Finset.disjoint_left]
      intro z hz
      rcases Finset.mem_symmDiff.mp hz with ⟨hzF, _⟩ | ⟨hzv, _⟩
      · exact Finset.disjoint_left.mp hF_star_I hzF
      · rw [Finset.mem_singleton.mp hzv]
        exact hvI
    have htele := gain_singleton_flip G N I F_star hN hF_star_I hvI (flip B c)
    have hmax_sd := hF_star_max (symmDiff F_star {v}) hsd_I
    have hle0 : gain N {v} (flip F_star (flip B c)) ≤ 0 := by omega
    have hunf := unfriendlyAt_of_gain_singleton_le_zero G N (hN v hvI) (flip F_star (flip B c)) hle0
    exact cardinal_le_of_unfriendlyAt G N (hN v hvI) (flip F_star (flip B c)) hunf

end OMA.AMPFiniteInfiniteDegree

theorem OMA.solution : OMA.R_wp_unfriendly_partition_conjecture_R1_H2_R1.H1 := by
  intro V _ G hI_fin
  let _ : DecidableEq V := Classical.decEq V
  let _ : DecidableRel G.Adj := Classical.decRel G.Adj
  let I : Finset V := hI_fin.toFinset
  have hI_mem : ∀ v : V, v ∈ I ↔ (G.neighborSet v).Infinite := fun v => by simp [I]
  let _ : DecidablePred (fun v : V => (G.neighborSet v).Finite) := Classical.decPred _
  let N : V → Finset V := fun v =>
    if hv : (G.neighborSet v).Finite then hv.toFinset else ∅
  have hN : ∀ v, v ∉ I → ∀ y, y ∈ N v ↔ G.Adj v y := by
    intro v hvI y
    have hvfin : (G.neighborSet v).Finite := by
      by_contra hinf
      exact hvI ((hI_mem v).mpr hinf)
    simp [N, hvfin]
  obtain ⟨c, hcI, hgain_c⟩ := OMA.AMPFiniteInfiniteDegree.exists_pinned_nonpos_gain G N I hN
  let P_B : V → Prop := fun b => ({w : V | G.Adj b w ∧ c w = true} : Set V).Finite
  let _ : DecidablePred P_B := Classical.decPred P_B
  let B : Finset V := I.filter P_B
  have hBI : B ⊆ I := Finset.filter_subset P_B I
  have hB_iff : ∀ b ∈ I, b ∈ B ↔ ({w : V | G.Adj b w ∧ c w = true} : Set V).Finite := by
    intro b hbI
    simp [B, P_B, hbI]
  let T : V → Finset V := fun b =>
    if hb : P_B b then hb.toFinset else ∅
  let M₀ : Finset V := (B.biUnion T).filter (fun x => x ∉ I)
  have hM₀ : ∀ x, x ∉ I → ∀ y ∈ B, G.Adj y x → c x = true → x ∈ M₀ := by
    intro x hxI y hyB hyx hcx
    have hy_fin : P_B y := (Finset.mem_filter.mp hyB).2
    have hxT : x ∈ T y := by simp [T, hy_fin, P_B, hyx, hcx]
    exact Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr ⟨y, hyB, hxT⟩, hxI⟩
  exact OMA.AMPFiniteInfiniteDegree.finish_from_pinned G N I B M₀ c
    hI_mem hN hcI hgain_c hBI hB_iff hM₀
