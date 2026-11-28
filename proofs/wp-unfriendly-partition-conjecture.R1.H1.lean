import OMAReductions.R_wp_unfriendly_partition_conjecture_R1
import Mathlib

/-!
# Locally finite graphs admit an unfriendly 2-partition

For any finite set of vertices `F`, maximizing the number of bichromatic edges inside
`F ∪ ⋃_{v ∈ F} N(v)` produces a 2-coloring that is unfriendly at every vertex of `F`
(flipping a vertex of `F` swaps its same-color and opposite-color incident edges).
Equipping `V → Bool` with the product topology (compact by Tychonoff's theorem), each
vertex's unfriendliness condition depends only on finitely many coordinates and is
therefore closed; the finite intersection property yields a global unfriendly partition.
-/

-- Credit: @qu1r0ra

namespace OMA.UnfriendlyProof

open SimpleGraph Finset

private def neighborSubtypeEquiv {V : Type} (G : SimpleGraph V) (N : V → Finset V)
    (hN : ∀ v w, w ∈ N v ↔ G.Adj v w) (v : V) (P : V → Prop) [DecidablePred P] :
    {w : V // G.Adj v w ∧ P w} ≃ ↥((N v).filter P) :=
  Equiv.subtypeEquivRight fun w => by simp only [Finset.mem_filter, hN]

private def UnfriendlyAt {V : Type} (N : V → Finset V) (f : V → Bool) (v : V) : Prop :=
  ((N v).filter fun w => f w = f v).card ≤ ((N v).filter fun w => f w ≠ f v).card

private lemma cardinal_le_of_unfriendlyAt {V : Type} (G : SimpleGraph V) (N : V → Finset V)
    (hN : ∀ v w, w ∈ N v ↔ G.Adj v w) (f : V → Bool) (v : V)
    (h : UnfriendlyAt N f v) :
    Cardinal.mk {w : V // G.Adj v w ∧ f w = f v} ≤
      Cardinal.mk {w : V // G.Adj v w ∧ f w ≠ f v} := by
  rw [Cardinal.mk_congr (neighborSubtypeEquiv G N hN v (fun w => f w = f v)),
      Cardinal.mk_congr (neighborSubtypeEquiv G N hN v (fun w => f w ≠ f v))]
  simp only [Cardinal.mk_fintype, Fintype.card_coe, Nat.cast_le]
  exact h

private def cutScore {V : Type} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (f : V → Bool) : ℕ :=
  ∑ u ∈ S, ∑ w ∈ S, if G.Adj u w ∧ f u ≠ f w then 1 else 0

private lemma cutScore_split {V : Type} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) {v : V} (hv : v ∈ S) (h : V → Bool) :
    cutScore G S h =
      (∑ u ∈ S.erase v, ∑ w ∈ S.erase v, if G.Adj u w ∧ h u ≠ h w then 1 else 0) +
        2 * (∑ w ∈ S.erase v, if G.Adj v w ∧ h v ≠ h w then 1 else 0) := by
  unfold cutScore
  rw [← Finset.sum_erase_add _ _ hv]
  have h1 : (∑ u ∈ S.erase v, ∑ w ∈ S, if G.Adj u w ∧ h u ≠ h w then 1 else 0) =
      (∑ u ∈ S.erase v, ∑ w ∈ S.erase v, if G.Adj u w ∧ h u ≠ h w then 1 else 0) +
        (∑ u ∈ S.erase v, if G.Adj u v ∧ h u ≠ h v then 1 else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [← Finset.sum_erase_add _ _ hv]
  have h2 : (∑ w ∈ S, if G.Adj v w ∧ h v ≠ h w then 1 else 0) =
      (∑ w ∈ S.erase v, if G.Adj v w ∧ h v ≠ h w then 1 else 0) := by
    rw [← Finset.sum_erase_add _ _ hv]
    simp
  have h3 : (∑ u ∈ S.erase v, if G.Adj u v ∧ h u ≠ h v then 1 else 0) =
      (∑ w ∈ S.erase v, if G.Adj v w ∧ h v ≠ h w then 1 else 0) := by
    refine Finset.sum_congr rfl fun w _ => ?_
    simp [G.adj_comm, ne_comm]
  rw [h1, h2, h3]
  omega

private lemma bool_not_ne_iff (a b : Bool) : (b ≠ !a) ↔ b = a := by
  cases a <;> cases b <;> decide

private lemma unfriendly_of_max_cutScore {V : Type} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (N : V → Finset V) (hN : ∀ v w, w ∈ N v ↔ G.Adj v w)
    (S : Finset V) (f : V → Bool)
    (hmax : ∀ f' : V → Bool, cutScore G S f' ≤ cutScore G S f)
    {v : V} (hvS : v ∈ S) (hNS : N v ⊆ S) :
    UnfriendlyAt N f v := by
  let flip (w : V) := if w = v then !f v else f w
  have hle := hmax flip
  have hrest :
      (∑ u ∈ S.erase v, ∑ w ∈ S.erase v, if G.Adj u w ∧ flip u ≠ flip w then 1 else 0) =
        (∑ u ∈ S.erase v, ∑ w ∈ S.erase v, if G.Adj u w ∧ f u ≠ f w then 1 else 0) := by
    refine Finset.sum_congr rfl fun u hu => Finset.sum_congr rfl fun w hw => ?_
    simp [flip, Finset.ne_of_mem_erase hu, Finset.ne_of_mem_erase hw]
  have hmem (w : V) : (w ∈ S.erase v ∧ G.Adj v w) ↔ w ∈ N v := by
    rw [hN]
    exact ⟨And.right, fun hvw => ⟨Finset.mem_erase.mpr ⟨hvw.ne', hNS ((hN v w).mpr hvw)⟩, hvw⟩⟩
  have incident (g : V → Bool) :
      (∑ w ∈ S.erase v, if G.Adj v w ∧ g v ≠ g w then 1 else 0) =
        ((N v).filter fun w => g w ≠ g v).card := by
    rw [Finset.card_filter, ← Finset.sum_filter, ← Finset.sum_filter]
    congr 1
    ext w
    simp only [Finset.mem_filter, ← and_assoc, hmem, ne_comm]
  have hflip : ((N v).filter fun w => flip w ≠ flip v) =
      ((N v).filter fun w => f w = f v) := by
    ext w
    simp only [Finset.mem_filter]
    apply and_congr_right
    intro hw
    simpa only [flip, if_pos rfl, if_neg ((hN v w).mp hw).ne'] using
      bool_not_ne_iff (f v) (f w)
  rw [cutScore_split G S hvS flip, cutScore_split G S hvS f,
    hrest, incident flip, incident f, hflip] at hle
  unfold UnfriendlyAt
  omega

private lemma exists_max_cutScore {V : Type} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (S : Finset V) :
    ∃ f : V → Bool, ∀ f' : V → Bool, cutScore G S f' ≤ cutScore G S f := by
  have hbdd : ∀ f' : V → Bool, cutScore G S f' ≤ S.card * S.card := by
    intro f'
    unfold cutScore
    calc
      (∑ u ∈ S, ∑ w ∈ S, if G.Adj u w ∧ f' u ≠ f' w then 1 else 0)
        ≤ ∑ _u ∈ S, ∑ _w ∈ S, 1 := by
          refine Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun w _ => ?_
          split_ifs <;> omega
      _ = S.card * S.card := by simp
  let P : ℕ → Prop := fun k => ∃ f : V → Bool, cutScore G S f = k
  letI : DecidablePred P := Classical.decPred P
  let scores : Finset ℕ := (Finset.Iic (S.card * S.card)).filter P
  have hne : scores.Nonempty := by
    refine ⟨cutScore G S (fun _ => false), Finset.mem_filter.mpr ?_⟩
    exact ⟨Finset.mem_Iic.mpr (hbdd _), ⟨fun _ => false, rfl⟩⟩
  obtain ⟨m, hm⟩ := Finset.max_of_nonempty hne
  have hm_mem : m ∈ scores := Finset.mem_of_max hm
  obtain ⟨_, f, hf⟩ := Finset.mem_filter.mp hm_mem
  refine ⟨f, fun f' => ?_⟩
  rw [hf]
  have hf'_mem : cutScore G S f' ∈ scores :=
    Finset.mem_filter.mpr ⟨Finset.mem_Iic.mpr (hbdd f'), ⟨f', rfl⟩⟩
  exact Finset.le_max_of_eq hf'_mem hm

private lemma exists_unfriendly_finset {V : Type} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (N : V → Finset V) (hN : ∀ v w, w ∈ N v ↔ G.Adj v w) (F : Finset V) :
    ∃ f : V → Bool, ∀ v ∈ F, UnfriendlyAt N f v := by
  let S : Finset V := F ∪ F.biUnion N
  obtain ⟨f, hmax⟩ := exists_max_cutScore G S
  refine ⟨f, fun v hvF => ?_⟩
  have hvS : v ∈ S := Finset.mem_union_left _ hvF
  have hNS : N v ⊆ S := fun w hw =>
    Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨v, hvF, hw⟩)
  exact unfriendly_of_max_cutScore G N hN S f hmax hvS hNS

private theorem isClosed_unfriendlyAt {V : Type} [DecidableEq V] (N : V → Finset V) (v : V) :
    IsClosed {f : V → Bool | UnfriendlyAt N f v} := by
  let K : Finset V := insert v (N v)
  let res : (V → Bool) → (↥K → Bool) := fun f x => f x.1
  have hcont : Continuous res := continuous_pi fun x => continuous_apply x.1
  let good : Set (↥K → Bool) :=
    {g | ((N v).attach.filter fun w =>
            g ⟨w.1, Finset.mem_insert_of_mem w.2⟩ = g ⟨v, Finset.mem_insert_self v (N v)⟩).card ≤
          ((N v).attach.filter fun w =>
            g ⟨w.1, Finset.mem_insert_of_mem w.2⟩ ≠ g ⟨v, Finset.mem_insert_self v (N v)⟩).card}
  have hclosed_good : IsClosed good := isClosed_discrete good
  have heq : {f : V → Bool | UnfriendlyAt N f v} = res ⁻¹' good := by
    ext f
    change UnfriendlyAt N f v ↔
      ((N v).attach.filter fun w => f w.1 = f v).card ≤
        ((N v).attach.filter fun w => f w.1 ≠ f v).card
    unfold UnfriendlyAt
    have card_attach (P : V → Prop) [DecidablePred P] :
        ((N v).attach.filter fun w => P w.1).card = ((N v).filter P).card := by
      rw [← Finset.card_map ⟨Subtype.val, Subtype.val_injective⟩]
      congr 1
      ext x
      simp [and_comm]
    rw [card_attach (fun w => f w = f v), card_attach (fun w => f w ≠ f v)]
  rw [heq]
  exact hclosed_good.preimage hcont

end OMA.UnfriendlyProof

theorem OMA.solution : OMA.R_wp_unfriendly_partition_conjecture_R1.H1 := by
  intro V G hfin
  classical
  let N : V → Finset V := fun v => (hfin v).toFinset
  have hN : ∀ v w, w ∈ N v ↔ G.Adj v w := by
    intro v w
    simp [N]
  let C : V → Set (V → Bool) := fun v => {f | OMA.UnfriendlyProof.UnfriendlyAt N f v}
  have hclosed : ∀ v, IsClosed (C v) := fun v => OMA.UnfriendlyProof.isClosed_unfriendlyAt N v
  have hfip : ∀ F : Finset V, (Set.univ ∩ ⋂ v ∈ F, C v).Nonempty := by
    intro F
    obtain ⟨f, hf⟩ := OMA.UnfriendlyProof.exists_unfriendly_finset G N hN F
    refine ⟨f, Set.mem_univ f, Set.mem_iInter₂.mpr ?_⟩
    intro v hv
    exact hf v hv
  obtain ⟨f, -, hf⟩ := isCompact_univ.inter_iInter_nonempty C hclosed hfip
  refine ⟨f, fun v => ?_⟩
  have hfv : OMA.UnfriendlyProof.UnfriendlyAt N f v := Set.mem_iInter.mp hf v
  exact OMA.UnfriendlyProof.cardinal_le_of_unfriendlyAt G N hN f v hfv
