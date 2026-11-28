import OMAReductions.R_Erdos1191_erdos_1191_parts_ii_R2
import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan

/-!
# Thinning finite Sidon blocks with sparse repeated differences

Only differences of length at least `2^(j/2) * (j+1)^2` need an estimate.
At scale `j`, each such length shared with a lower block costs only one
edge of a graph on the marks, even when several lower blocks realize it.
A polynomial bound on the number of these lengths per mark therefore
suffices. One can thin all the blocks independently, since the forbidden
lists refer to the original blocks.
-/

-- Credit: @ellisjr

namespace OMA.R_Erdos1191_erdos_1191_parts_ii_R2_H1_R1

/-- A family of dense finite rulers with a polynomial allowance per mark
for long differences shared with any smaller block. -/
def H1 : Prop :=
  ∃ d k J : ℕ, ∀ N : ℕ, ∃ B : ℕ → Finset ℕ,
    (∀ j, B j ⊆ Finset.Ico (2 ^ j) (2 ^ (j + 1))) ∧
    (∀ j, IsSidon (B j : Set ℕ)) ∧
    ∀ j, J ≤ j → j ≤ N →
      2 ^ j ≤ (B j).card ^ 2 * (j + 1) ^ (2 * (d + 1)) ∧
      ∃ F : Finset ℕ, F.card ≤ (B j).card * (j + 1) ^ k ∧
        ∀ i, i < j → ∀ a ∈ B i, ∀ b ∈ B i, ∀ u ∈ B j, ∀ v ∈ B j,
          b < a → v < u → a - b = u - v →
          2 ^ (j / 2) * (j + 1) ^ 2 ≤ u - v → u - v ∈ F

/-- A finite Sidon set admits a large subset avoiding a given list of
forbidden differences. The loss is linear in the list length per mark. -/
def H2 : Prop :=
  ∀ (S F : Finset ℕ) (k : ℕ), IsSidon (S : Set ℕ) → F.card ≤ S.card * k →
    ∃ T ⊆ S, S.card ≤ T.card * (2 * k + 1) ∧
      ∀ a ∈ T, ∀ b ∈ T, b < a → a - b ∉ F

open Finset SimpleGraph

/-- Turán's theorem on the complement, in average-degree form. -/
lemma large_independent_set {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (k : ℕ) (he : G.edgeFinset.card ≤ Fintype.card V * k) :
    ∃ T : Finset V, G.IsIndepSet (T : Set V) ∧ Fintype.card V ≤ T.card * (2 * k + 1) := by
  classical
  obtain ⟨T, hT⟩ := G.exists_isNIndepSet_indepNum
  refine ⟨T, hT.isIndepSet, ?_⟩
  let n := Fintype.card V
  let r := G.indepNum
  rw [hT.card_eq]
  change n ≤ r * (2 * k + 1)
  by_cases hn : n = 0
  · simp [hn]
  have hn' : 0 < n := by omega
  have hfree : Gᶜ.CliqueFree (r + 1) := by
    intro U hU
    have hI : G.IsNIndepSet (r + 1) U := (G.isNClique_compl).mp hU
    have hc := hI.isIndepSet.card_le_indepNum
    rw [hI.card_eq] at hc
    change r + 1 ≤ r at hc
    omega
  have hr : 0 < r := by
    by_contra! h
    have h0 : r = 0 := by omega
    have hempty := cliqueFree_one.mp (show Gᶜ.CliqueFree 1 by simpa [h0] using hfree)
    exact hn (Fintype.card_eq_zero_iff.mpr hempty)
  obtain ⟨H, _, hH⟩ := exists_isTuranMaximal (V := V) hr
  have hmax : Gᶜ.edgeFinset.card ≤ (turanGraph n r).edgeFinset.card := by
    exact (hH.2 hfree).trans_eq hH.nonempty_iso_turanGraph.some.card_edgeFinset_eq
  have htur : 2 * r * Gᶜ.edgeFinset.card ≤ (r - 1) * n ^ 2 :=
    (Nat.mul_le_mul_left _ hmax).trans mul_card_edgeFinset_turanGraph_le
  have hjoint : G.edgeFinset.card + Gᶜ.edgeFinset.card = n.choose 2 := by
    have htop : (G ⊔ Gᶜ).edgeFinset = (⊤ : SimpleGraph V).edgeFinset :=
      edgeFinset_inj.mpr sup_compl_eq_top
    rw [← Finset.card_union_of_disjoint (disjoint_edgeFinset.mpr disjoint_compl_right),
      ← edgeFinset_sup, htop, card_edgeFinset_top_eq_card_choose_two]
  have hbalance : 2 * G.edgeFinset.card + 2 * Gᶜ.edgeFinset.card + n = n ^ 2 := by
    rw [Nat.choose_two_right] at hjoint
    have heven := Nat.div_mul_cancel (Nat.even_mul_pred_self n).two_dvd
    have hpred : n - 1 + 1 = n := by omega
    nlinarith only [hjoint, heven, congrArg (n * ·) hpred]
  have hratio : n ^ 2 ≤ r * (2 * G.edgeFinset.card + n) := by
    have hpred : r - 1 + 1 = r := by omega
    nlinarith only [htur, congrArg (r * ·) hbalance, congrArg (· * n ^ 2) hpred]
  have hdegree : 2 * G.edgeFinset.card + n ≤ 2 * (n * k) + n := by
    change G.edgeFinset.card ≤ n * k at he
    omega
  apply Nat.le_of_mul_le_mul_left (a := n)
  · calc
      n * n = n ^ 2 := (sq n).symm
      _ ≤ _ := hratio
      _ ≤ r * (2 * (n * k) + n) := Nat.mul_le_mul_left _ hdegree
      _ = n * (r * (2 * k + 1)) := by ring
  · exact hn'

/-- Each forbidden positive difference produces at most one edge on a Sidon set. -/
theorem thin_forbidden (S F : Finset ℕ) (k : ℕ) (hS : IsSidon (S : Set ℕ))
    (hF : F.card ≤ S.card * k) :
    ∃ T ⊆ S, S.card ≤ T.card * (2 * k + 1) ∧
      ∀ a ∈ T, ∀ b ∈ T, b < a → a - b ∉ F := by
  classical
  let G : SimpleGraph S := {
    Adj := fun x y ↦ x ≠ y ∧ Nat.dist x.val y.val ∈ F
    symm := ⟨fun x y h ↦ ⟨h.1.symm, by rw [Nat.dist_comm]; exact h.2⟩⟩
    loopless := ⟨fun x h ↦ h.1 rfl⟩ }
  let P := (Finset.univ : Finset (S × S)).filter
    (fun p ↦ p.2.val < p.1.val ∧ p.1.val - p.2.val ∈ F)
  have hp : P.card ≤ F.card := by
    apply Finset.card_le_card_of_injOn (fun p : S × S ↦ p.1.val - p.2.val)
    · intro p h
      exact (Finset.mem_filter.mp h).2.2
    · intro p hp q hq heq
      obtain ⟨hx, hy⟩ := OMA.R_Erdos1191_erdos_1191_parts_ii_R2.sidon_positive_difference_unique
        S hS p.1.property p.2.property q.1.property q.2.property
        (Finset.mem_filter.mp hp).2.1 (Finset.mem_filter.mp hq).2.1 heq
      exact Prod.ext (Subtype.ext hx) (Subtype.ext hy)
  have hedges : G.edgeFinset.card ≤ P.card := by
    apply Finset.card_le_card_of_surjOn (fun p : S × S ↦ s(p.1, p.2))
    intro z hz
    induction z using Sym2.inductionOn with
    | _ x y =>
      have hxy : G.Adj x y := (SimpleGraph.mem_edgeFinset.mp hz)
      change x ≠ y ∧ Nat.dist x.val y.val ∈ F at hxy
      by_cases hlt : y.val < x.val
      · exact ⟨(x,y), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt,
          by simpa [Nat.dist_eq_sub_of_le_right hlt.le] using hxy.2⟩, rfl⟩
      · have hlt' : x.val < y.val := lt_of_le_of_ne (Nat.le_of_not_gt hlt)
            (fun h ↦ hxy.1 (Subtype.ext h))
        exact ⟨(y,x), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt',
          by simpa [Nat.dist_eq_sub_of_le hlt'.le] using hxy.2⟩, Sym2.eq_swap⟩
  obtain ⟨U, hU, hsize⟩ := large_independent_set G k
    (by simpa only [Fintype.card_coe] using hedges.trans (hp.trans hF))
  let f : S ↪ ℕ := ⟨Subtype.val, Subtype.val_injective⟩
  refine ⟨U.map f, ?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨x, _, rfl⟩ := Finset.mem_map.mp ha
    exact x.property
  · simpa only [Finset.card_map, Fintype.card_coe] using hsize
  · intro a ha b hb hba hbad
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp ha
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hb
    change y.val < x.val at hba
    have hne : x ≠ y := fun h ↦ (ne_of_gt hba) (congrArg Subtype.val h)
    exact (G.isIndepSet_iff.mp hU hx hy hne) ⟨hne, by rwa [Nat.dist_eq_sub_of_le_right hba.le]⟩

lemma finite_thinning : H2 := thin_forbidden

lemma half_scale_le {j m d : ℕ} (h : 2 ^ j ≤ m ^ 2 * (j + 1) ^ (2 * (d + 1))) :
    2 ^ (j / 2) ≤ m * (j + 1) ^ (d + 1) := by
  have hs : (2 ^ (j / 2)) ^ 2 ≤ (m * (j + 1) ^ (d + 1)) ^ 2 := by
    rw [← pow_mul, mul_pow, ← pow_mul, Nat.mul_comm (d + 1) 2]
    exact (Nat.pow_le_pow_right (by decide) (by omega)).trans h
  exact (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp hs

theorem main : H1 → H2 → OMA.R_Erdos1191_erdos_1191_parts_ii_R2.H1 := by
  classical
  rintro ⟨d, k, J, hfamily⟩ hthin
  let e := d + k + 3
  refine ⟨d + e + 1, max J 4, fun N ↦ ?_⟩
  obtain ⟨B, hpos, hsid, hdata⟩ := hfamily N
  have select (j : ℕ) : ∃ T ⊆ B j,
      (max J 4 ≤ j → j ≤ N →
        2 ^ j ≤ T.card ^ 2 * (j + 1) ^ (2 * (d + e + 1 + 1))) ∧
      ∀ i, i < j → ∀ a ∈ B i, ∀ b ∈ B i, ∀ u ∈ T, ∀ v ∈ T,
        b < a → v < u → a - b ≠ u - v := by
    by_cases active : max J 4 ≤ j ∧ j ≤ N
    · obtain ⟨hcount, F, hF, hlong⟩ := hdata j ((le_max_left ..).trans active.1) active.2
      let t := 2 ^ (j / 2) * (j + 1) ^ 2
      let D := F ∪ Finset.range t
      let L := (j + 1) ^ e
      have hbase : 1 ≤ j + 1 := by omega
      have ht : t ≤ (B j).card * L := by
        calc
          t ≤ ((B j).card * (j + 1) ^ (d + 1)) * (j + 1) ^ 2 :=
            Nat.mul_le_mul_right _ (half_scale_le hcount)
          _ = (B j).card * (j + 1) ^ (d + 3) := by rw [mul_assoc, ← pow_add]
          _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hbase (by dsimp [e]; omega))
      have hF' : F.card ≤ (B j).card * L :=
        hF.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hbase (by dsimp [e]; omega)))
      have hD : D.card ≤ (B j).card * (2 * L) := by
        have hu := Finset.card_union_le F (Finset.range t)
        rw [Finset.card_range] at hu
        dsimp [D]
        nlinarith only [hu, ht, hF']
      obtain ⟨T, hT, hsize, havoid⟩ := hthin (B j) D (2 * L) (hsid j) hD
      refine ⟨T, hT, fun _ _ ↦ ?_, ?_⟩
      · have hL : 0 < L := by dsimp [L]; positivity
        have h5 : 5 ≤ j + 1 := by have := le_max_right J 4; omega
        have hfactor : 2 * (2 * L) + 1 ≤ (j + 1) ^ (e + 1) := by
          rw [pow_succ]
          exact (show 2 * (2 * L) + 1 ≤ L * 5 by omega).trans (Nat.mul_le_mul_left L h5)
        have hm := hsize.trans (Nat.mul_le_mul_left _ hfactor)
        calc
          2 ^ j ≤ (B j).card ^ 2 * (j + 1) ^ (2 * (d + 1)) := hcount
          _ ≤ (T.card * (j + 1) ^ (e + 1)) ^ 2 * (j + 1) ^ (2 * (d + 1)) :=
            Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hm 2)
          _ = _ := by
            rw [mul_pow, ← pow_mul, mul_assoc, ← pow_add]
            congr 2
            ring
      · intro i hij a ha b hb u hu v hv hba hvu heq
        apply havoid u hu v hv hvu
        by_cases hshort : u - v < t
        · exact Finset.mem_union_right _ (Finset.mem_range.mpr hshort)
        · exact Finset.mem_union_left _ (hlong i hij a ha b hb u (hT hu) v (hT hv)
            hba hvu heq (Nat.le_of_not_gt hshort))
    · exact ⟨∅, Finset.empty_subset _, fun hj hjN ↦ (active ⟨hj, hjN⟩).elim, by simp⟩
  choose T hsub hcount hsep using select
  refine ⟨T, fun j ↦ (hsub j).trans (hpos j), ?_, hcount, ?_⟩
  · intro j a ha b hb u hu v hv h
    exact hsid j a (hsub j ha) u (hsub j hu) b (hsub j hb) v (hsub j hv) h
  · intro i j _ hij a ha b hb
    exact hsep j i hij a (hsub i ha) b (hsub i hb)

/-- Only the estimate for long repeated differences remains. -/
theorem of_sparse_repetitions (h : H1) : OMA.R_Erdos1191_erdos_1191_parts_ii_R2.H1 :=
  main h finite_thinning

/-- A packing with exact separation has an empty list of long repeated differences. -/
theorem sparse_iff : H1 ↔ OMA.R_Erdos1191_erdos_1191_parts_ii_R2.H1 := by
  refine ⟨of_sparse_repetitions, ?_⟩
  rintro ⟨d, J, hpack⟩
  refine ⟨d, 0, J, fun N ↦ ?_⟩
  obtain ⟨B, hpos, hsid, hcount, hsep⟩ := hpack N
  refine ⟨B, hpos, fun j a ha u hu b hb v hv ↦ hsid j a ha b hb u hu v hv, ?_⟩
  intro j hj hjN
  refine ⟨hcount j hj hjN, ∅, by simp, ?_⟩
  intro i hij a ha b hb u hu v hv hba hvu heq hlong
  by_cases hnear : j / 3 < i
  · exact (hsep i j hnear hij a ha b hb u hu v hv hba hvu heq).elim
  · have ha' := (Finset.mem_Ico.mp (hpos i ha)).2
    have hb' := (Finset.mem_Ico.mp (hpos i hb)).1
    rw [pow_succ] at ha'
    have hdiff : a - b < 2 ^ i := by omega
    have hsmall : (2 : ℕ) ^ i ≤ 2 ^ (j / 2) := Nat.pow_le_pow_right (by decide) (by omega)
    have hfactor : 2 ^ (j / 2) ≤ 2 ^ (j / 2) * (j + 1) ^ 2 :=
      Nat.le_mul_of_pos_right _ (by positivity)
    omega

/-- Charge the first length to its label and every further length to a
pair in that label. This counts distinct lengths even when they have
several possible witnesses. -/
theorem lengths_le_labels_and_pairs {κ : Type*} [DecidableEq κ]
    (D : Finset ℕ) (label : ℕ → κ) :
    D.card ≤ (D.image label).card +
      ∑ t ∈ D.image label, ((D.filter (fun x => label x = t)).card).choose 2 := by
  have one_and_pairs (n : ℕ) : n ≤ 1 + n.choose 2 := by
    induction n with
    | zero => simp
    | succ n ih =>
      cases n with
      | zero => decide
      | succ n =>
        rw [Nat.choose_succ_succ (n+1) 1, Nat.choose_one_right]
        omega
  calc
    D.card = ∑ t ∈ D.image label, (D.filter (fun x => label x = t)).card :=
      card_eq_sum_card_image label D
    _ ≤ ∑ t ∈ D.image label, (1 + ((D.filter (fun x => label x = t)).card).choose 2) :=
      sum_le_sum (fun _ _ => one_and_pairs _)
    _ = _ := by simp [sum_add_distrib]

/-- At a fixed upper stage, the union over all lower stages costs at most
one factor of j. The labels may be chosen separately at every pair of
stages, and the exceptional lists may overlap. -/
theorem union_of_labeled_lengths {κ : Type*} [DecidableEq κ] (j R : ℕ)
    (D : ℕ → Finset ℕ) (label : ℕ → ℕ → κ)
    (cost : ∀ i < j, ((D i).image (label i)).card +
      ∑ t ∈ (D i).image (label i), (((D i).filter (fun x => label i x = t)).card).choose 2 ≤ R) :
    ((range j).biUnion D).card ≤ j * R := by
  calc
    _ ≤ ∑ i ∈ range j, (D i).card := card_biUnion_le
    _ ≤ ∑ _i ∈ range j, R := sum_le_sum (fun i hi =>
      (lengths_le_labels_and_pairs (D i) (label i)).trans (cost i (mem_range.mp hi)))
    _ = _ := by simp

/-- A uniform pair-count estimate of square-root size, up to a fixed
power of the scale index, suffices for the exact finite-horizon
sparse-overlap hypothesis. The two coordinates of the label can be the
lower prime and its signed determinant carry. -/
theorem sparse_of_same_label_counts (d A J : ℕ)
    (blocks : ∀ N : ℕ, ∃ B : ℕ → Finset ℕ,
      (∀ j, B j ⊆ Ico (2^j) (2^(j+1))) ∧ (∀ j, IsSidon (B j : Set ℕ)) ∧
      ∀ j, J ≤ j → j ≤ N →
        2^j ≤ (B j).card^2 * (j+1)^(2*(d+1)) ∧
        ∃ (D : ℕ → Finset ℕ) (label : ℕ → ℕ → ℕ × ℤ),
          (∀ i < j, ((D i).image (label i)).card +
            ∑ t ∈ (D i).image (label i),
              (((D i).filter (fun x => label i x = t)).card).choose 2 ≤
              2^(j/2)*(j+1)^A) ∧
          ∀ i, i < j → ∀ a ∈ B i, ∀ b ∈ B i, ∀ u ∈ B j, ∀ v ∈ B j,
            b < a → v < u → a-b = u-v → 2^(j/2)*(j+1)^2 ≤ u-v → u-v ∈ D i) : H1 := by
  classical
  refine ⟨d, d+1+(A+1), J, fun N => ?_⟩
  obtain ⟨B, hpos, hsid, hstage⟩ := blocks N
  refine ⟨B, hpos, hsid, fun j hj hjN => ?_⟩
  obtain ⟨hd, D, label, hcost, hcovers⟩ := hstage j hj hjN
  refine ⟨hd, (range j).biUnion D, ?_, ?_⟩
  · have half := half_scale_le hd
    calc
      _ ≤ j * (2^(j/2)*(j+1)^A) := union_of_labeled_lengths j _ D label hcost
      _ ≤ (j+1) * (((B j).card*(j+1)^(d+1))*(j+1)^A) :=
        Nat.mul_le_mul (Nat.le_succ j) (Nat.mul_le_mul_right _ half)
      _ = _ := by rw [pow_add (j+1) (d+1), pow_succ (j+1) A]; ring
  · intro i hij a ha b hb u hu v hv hba hvu he hl
    exact mem_biUnion.mpr ⟨i, mem_range.mpr hij, hcovers i hij a ha b hb u hu v hv hba hvu he hl⟩

end OMA.R_Erdos1191_erdos_1191_parts_ii_R2_H1_R1
