import OMAStatements.S_arxiv_2001_06839
import Mathlib

namespace OMA.P_arxiv_2001_06839

open OMA.S_arxiv_2001_06839

/-- Rising-product basis `P_r(N, t) = ∏_{j=1}^N ((j + r * t) / j)`. -/
private noncomputable def risingP (r N : ℕ) (t : ℝ) : ℝ :=
  ∏ j ∈ Finset.Icc 1 N, (((j : ℝ) + (r : ℝ) * t) / (j : ℝ))

private lemma risingP_zero (r : ℕ) (t : ℝ) : risingP r 0 t = 1 := by
  simp [risingP]

private lemma risingP_succ (r N : ℕ) (t : ℝ) :
    risingP r (N + 1) t =
      (((N + 1 : ℕ) : ℝ) + (r : ℝ) * t) / ((N + 1 : ℕ) : ℝ) * risingP r N t := by
  unfold risingP
  rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ N + 1), mul_comm]

private lemma risingP_eq_div_factorial (r N : ℕ) (t : ℝ) :
    risingP r N t =
      (∏ j ∈ Finset.Icc 1 N, ((j : ℝ) + (r : ℝ) * t)) / (Nat.factorial N : ℝ) := by
  induction N with
  | zero => simp [risingP]
  | succ N ih =>
      rw [risingP_succ, ih, Finset.prod_Icc_succ_top (by omega : 1 ≤ N + 1),
        Nat.factorial_succ, Nat.cast_mul]
      field_simp

/-- Closed-form sum `S(N, m, t) = ∑_{r=0}^m (-1)^{m-r} C(m, r) P_r(N, t)`. -/
private noncomputable def sumS (N m : ℕ) (t : ℝ) : ℝ :=
  ∑ r ∈ Finset.range (m + 1),
    ((-1 : ℝ) ^ (m - r)) * (Nat.choose m r : ℝ) * risingP r N t

private lemma sumS_zero_zero (t : ℝ) : sumS 0 0 t = 1 := by
  simp [sumS, risingP_zero]

private lemma sumS_zero_succ (m : ℕ) (t : ℝ) : sumS 0 (m + 1) t = 0 := by
  unfold sumS
  simp only [risingP_zero, mul_one]
  have h := add_pow (1 : ℝ) (-1 : ℝ) (m + 1)
  have h0 : (1 + (-1 : ℝ)) ^ (m + 1) = 0 := by norm_num
  rw [h0] at h
  rw [h]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [one_pow, one_mul]

private lemma sumS_succ_zero (N : ℕ) (t : ℝ) : sumS N 0 t = 1 := by
  unfold sumS risingP
  simp only [Nat.zero_add, Finset.range_one, Finset.sum_singleton, Nat.sub_zero, pow_zero,
    Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.cast_zero, zero_mul, add_zero]
  refine Finset.prod_eq_one fun j hj => ?_
  have hjpos : (j : ℝ) ≠ 0 := by
    have := (Finset.mem_Icc.mp hj).1
    exact Nat.cast_ne_zero.mpr (by omega)
  exact div_self hjpos

/-- Key recurrence satisfied by `sumS`:
`sumS (N+1) m = ((N+1 + m*t)/(N+1)) * sumS N m + (m*t/(N+1)) * sumS N (m-1)`. -/
private lemma sumS_recurrence (N m : ℕ) (t : ℝ) :
    sumS (N + 1) (m + 1) t =
      (((N + 1 : ℕ) : ℝ) + ((m + 1 : ℕ) : ℝ) * t) / ((N + 1 : ℕ) : ℝ) * sumS N (m + 1) t +
      (((m + 1 : ℕ) : ℝ) * t) / ((N + 1 : ℕ) : ℝ) * sumS N m t := by
  unfold sumS
  rw [Finset.mul_sum, Finset.mul_sum]
  rw [Finset.sum_range_succ (fun r => _ * risingP r (N + 1) t) (m + 1)]
  rw [Finset.sum_range_succ (fun r => _ * (_ * risingP r N t)) (m + 1)]
  have hrearr : ∀ a b c : ℝ, a + (b + c) = (a + c) + b := fun a b c => by ring
  rw [add_assoc, hrearr, ← Finset.sum_add_distrib]
  congr 1
  · refine Finset.sum_congr rfl fun r hr => ?_
    rw [Finset.mem_range] at hr
    rw [risingP_succ]
    have hch : (m + 1) * Nat.choose m r = (m + 1 - r) * Nat.choose (m + 1) r := by
      have h3 : m + 1 - r = (m - r) + 1 := by omega
      have hf : Nat.choose (m + 1) r * Nat.factorial r * Nat.factorial (m + 1 - r) =
          Nat.factorial (m + 1) := Nat.choose_mul_factorial_mul_factorial (show r ≤ m + 1 by omega)
      have hf2 : Nat.choose m r * Nat.factorial r * Nat.factorial (m - r) =
          Nat.factorial m := Nat.choose_mul_factorial_mul_factorial (show r ≤ m by omega)
      have hf3 : Nat.factorial (m + 1 - r) = (m + 1 - r) * Nat.factorial (m - r) := by
        rw [h3, Nat.factorial_succ]
      have hf4 : Nat.factorial (m + 1) = (m + 1) * Nat.factorial m := Nat.factorial_succ m
      have hpos : 0 < Nat.factorial r * Nat.factorial (m - r) :=
        Nat.mul_pos (Nat.factorial_pos r) (Nat.factorial_pos (m - r))
      have hmul : (m + 1) * Nat.choose m r * (Nat.factorial r * Nat.factorial (m - r)) =
          (m + 1 - r) * Nat.choose (m + 1) r * (Nat.factorial r * Nat.factorial (m - r)) := by
        calc (m + 1) * Nat.choose m r * (Nat.factorial r * Nat.factorial (m - r))
            = (m + 1) * (Nat.choose m r * Nat.factorial r * Nat.factorial (m - r)) := by ring
          _ = (m + 1) * Nat.factorial m := by rw [hf2]
          _ = Nat.factorial (m + 1) := hf4.symm
          _ = Nat.choose (m + 1) r * Nat.factorial r * Nat.factorial (m + 1 - r) := hf.symm
          _ = Nat.choose (m + 1) r * Nat.factorial r * ((m + 1 - r) * Nat.factorial (m - r)) := by rw [hf3]
          _ = (m + 1 - r) * Nat.choose (m + 1) r * (Nat.factorial r * Nat.factorial (m - r)) := by ring
      exact Nat.eq_of_mul_eq_mul_right hpos hmul
    have hchR : ((m + 1 : ℕ) : ℝ) * (Nat.choose m r : ℝ) =
        (((m + 1 : ℕ) : ℝ) - (r : ℝ)) * (Nat.choose (m + 1) r : ℝ) := by
      have hsub : ((m + 1 - r : ℕ) : ℝ) = ((m + 1 : ℕ) : ℝ) - (r : ℝ) :=
        Nat.cast_sub (by omega)
      rw [← hsub]
      exact_mod_cast hch
    have hpow : (-1 : ℝ) ^ (m + 1 - r) = -((-1 : ℝ) ^ (m - r)) := by
      have h3 : m + 1 - r = (m - r) + 1 := by omega
      rw [h3, pow_succ]; ring
    have hNne : ((N + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [hpow]
    field_simp [hNne]
    linear_combination -(risingP r N t * t) * hchR
  · simp only [Nat.sub_self, pow_zero, one_mul, Nat.choose_self, Nat.cast_one]
    rw [risingP_succ]

/-- The tail seats `{s : Fin n | i ≤ s.val}` of `Fin n`. -/
private def tailSeats (n i : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun s : Fin n => i ≤ s.val)

/-- For `i ≥ k`, `ampStep n k t (n - i) occ` depends ONLY on `occ ∩ tailSeats n i` (provided
`occ.card = i`). -/
private lemma ampStep_depends_on_tail (n k : ℕ) (t : ℝ) :
    ∀ (rem : ℕ) (occ₁ occ₂ : Finset (Fin n)),
      rem ≤ n → k ≤ n - rem →
      occ₁.card = n - rem → occ₂.card = n - rem →
      occ₁ ∩ tailSeats n (n - rem) = occ₂ ∩ tailSeats n (n - rem) →
      ampStep n k t rem occ₁ = ampStep n k t rem occ₂ := by
  intro rem
  induction rem with
  | zero =>
      intro occ₁ occ₂ _ _ _ _ _
      rfl
  | succ r ih =>
      intro occ₁ occ₂ hrn hk hc1 hc2 htail
      set i := n - (r + 1) with hi_def
      have hi_lt : i < n := by omega
      have hi_not_lt_k : ¬ i < k := by omega
      have hfree1 : (Finset.univ \ occ₁).card = r + 1 := by
        rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, hc1]
        omega
      have hfree2 : (Finset.univ \ occ₂).card = r + 1 := by
        rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, hc2]
        omega
      have hi_tail : (⟨i, hi_lt⟩ : Fin n) ∈ tailSeats n i := by
        simp [tailSeats]
      have hmem_iff : (⟨i, hi_lt⟩ : Fin n) ∈ occ₁ ↔ (⟨i, hi_lt⟩ : Fin n) ∈ occ₂ := by
        have := Finset.ext_iff.mp htail ⟨i, hi_lt⟩
        simpa [hi_tail] using this
      have hnext_i : n - r = i + 1 := by omega
      have htail_sub : ∀ s : Fin n, s ∈ tailSeats n (i + 1) → s ∈ tailSeats n i := by
        intro s hs; simp only [tailSeats, Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢; omega
      have htail_eq_next : occ₁ ∩ tailSeats n (n - r) = occ₂ ∩ tailSeats n (n - r) := by
        ext s
        simp only [Finset.mem_inter, hnext_i]
        constructor
        · rintro ⟨h1, hs⟩
          have := (Finset.ext_iff.mp htail s).mp (Finset.mem_inter.mpr ⟨h1, htail_sub s hs⟩)
          exact ⟨(Finset.mem_inter.mp this).1, hs⟩
        · rintro ⟨h2, hs⟩
          have := (Finset.ext_iff.mp htail s).mpr (Finset.mem_inter.mpr ⟨h2, htail_sub s hs⟩)
          exact ⟨(Finset.mem_inter.mp this).1, hs⟩
      unfold ampStep
      simp only [← hi_def, hi_not_lt_k, ↓reduceIte, hi_lt, ↓reduceDIte]
      by_cases hi_occ : (⟨i, hi_lt⟩ : Fin n) ∈ occ₁
      · have hi_occ2 : (⟨i, hi_lt⟩ : Fin n) ∈ occ₂ := hmem_iff.mp hi_occ
        simp only [hi_occ, hi_occ2, not_true_eq_false, ↓reduceIte, hfree1, hfree2]
        congr 1
        -- Direct comparison between `occ₁` and `occ₂`:
        -- First show `((univ \ occ₁).filter (< i)).card = ((univ \ occ₂).filter (< i)).card`
        have hlt_card : ∀ (occ : Finset (Fin n)), occ.card = i →
            ((Finset.univ \ occ).filter (fun s : Fin n => s.val < i)).card =
              (occ ∩ tailSeats n i).card := by
          intro occ hc
          have hlow : (Finset.univ.filter (fun s : Fin n => s.val < i)).card = i := by
            have heq : Finset.univ.filter (fun s : Fin n => s.val < i) =
                (Finset.range i).attach.image (fun x => ⟨x.1, lt_trans (Finset.mem_range.mp x.2) hi_lt⟩) := by
              ext s
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
                Finset.mem_attach, Subtype.exists, Finset.mem_range]
              constructor
              · intro hs; exact ⟨s.val, hs, Fin.ext rfl⟩
              · rintro ⟨a, ha, rfl⟩; exact ha
            rw [heq, Finset.card_image_of_injective]
            · rw [Finset.card_attach, Finset.card_range]
            · intro a b hab; exact Subtype.ext (congrArg Fin.val hab)
          have hsplit_occ : occ.card = (occ.filter (fun s : Fin n => s.val < i)).card +
              (occ ∩ tailSeats n i).card := by
            have : occ ∩ tailSeats n i = occ.filter (fun s : Fin n => ¬ s.val < i) := by
              ext s; simp only [Finset.mem_inter, tailSeats, Finset.mem_filter, Finset.mem_univ,
                true_and, not_lt]
            rw [this, Finset.card_filter_add_card_filter_not]
          have hlow_split : (Finset.univ.filter (fun s : Fin n => s.val < i)).card =
              (occ.filter (fun s : Fin n => s.val < i)).card +
              ((Finset.univ \ occ).filter (fun s : Fin n => s.val < i)).card := by
            have hu : Finset.univ.filter (fun s : Fin n => s.val < i) =
                occ.filter (fun s : Fin n => s.val < i) ∪
                (Finset.univ \ occ).filter (fun s : Fin n => s.val < i) := by
              ext s; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
                Finset.mem_sdiff]; tauto
            have hd : Disjoint (occ.filter (fun s : Fin n => s.val < i))
                ((Finset.univ \ occ).filter (fun s : Fin n => s.val < i)) := by
              rw [Finset.disjoint_left]; intro s h1 h2
              simp only [Finset.mem_filter, Finset.mem_sdiff] at h1 h2
              exact h2.1.2 h1.1
            rw [hu, Finset.card_union_of_disjoint hd]
          omega
        -- Split both sums into `< i` and `≥ i + 1`
        have hpart_occ : ∀ (occ : Finset (Fin n)), (⟨i, hi_lt⟩ : Fin n) ∈ occ →
            Finset.univ \ occ =
              ((Finset.univ \ occ).filter (fun s : Fin n => s.val < i)) ∪
              (tailSeats n (i + 1) \ (occ ∩ tailSeats n (i + 1))) := by
          intro occ hio
          ext s
          simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union,
            Finset.mem_filter, Finset.mem_inter, tailSeats]
          constructor
          · intro hnot
            by_cases hlt : s.val < i
            · exact Or.inl ⟨hnot, hlt⟩
            · right
              have hne : s.val ≠ i := by
                intro heq; apply hnot; rw [show s = ⟨i, hi_lt⟩ from Fin.ext heq]; exact hio
              exact ⟨by omega, fun h => hnot h.1⟩
          · rintro (⟨hnot, _⟩ | ⟨hge, hnot⟩)
            · exact hnot
            · intro hs; exact hnot ⟨hs, hge⟩
        have hdisj_occ : ∀ (occ : Finset (Fin n)),
            Disjoint ((Finset.univ \ occ).filter (fun s : Fin n => s.val < i))
              (tailSeats n (i + 1) \ (occ ∩ tailSeats n (i + 1))) := by
          intro occ; rw [Finset.disjoint_left]; intro s h1 h2
          simp only [Finset.mem_filter, Finset.mem_sdiff, tailSeats, Finset.mem_univ, true_and] at h1 h2
          omega
        rw [hpart_occ occ₁ hi_occ, Finset.sum_union (hdisj_occ occ₁),
          hpart_occ occ₂ hi_occ2, Finset.sum_union (hdisj_occ occ₂)]
        have htail_sdiff : tailSeats n (i + 1) \ (occ₁ ∩ tailSeats n (i + 1)) =
            tailSeats n (i + 1) \ (occ₂ ∩ tailSeats n (i + 1)) := by
          rw [← hnext_i, htail_eq_next]
        congr 1
        · -- `< i` parts: both have the same cardinality `m = (occ₁ ∩ tailSeats n i).card`,
          -- and every term has the SAME value!
          have hcard_eq : ((Finset.univ \ occ₁).filter (fun s : Fin n => s.val < i)).card =
              ((Finset.univ \ occ₂).filter (fun s : Fin n => s.val < i)).card := by
            rw [hlt_card occ₁ hc1, hlt_card occ₂ hc2, htail]
          by_cases hne : ((Finset.univ \ occ₁).filter (fun s : Fin n => s.val < i)).Nonempty
          · obtain ⟨s0, hs0⟩ := hne
            have hconst1 : ∀ s ∈ (Finset.univ \ occ₁).filter (fun s : Fin n => s.val < i),
                t * ampStep n k t r (insert s occ₁) = t * ampStep n k t r (insert s0 occ₁) := by
              intro s hs
              congr 1
              have hs_not : s ∉ occ₁ := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hs).1).2
              have hs0_not : s0 ∉ occ₁ := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hs0).1).2
              have hs_lt : s.val < i := (Finset.mem_filter.mp hs).2
              have hs0_lt : s0.val < i := (Finset.mem_filter.mp hs0).2
              apply ih _ _ (by omega) (by omega)
                (by rw [Finset.card_insert_of_notMem hs_not, hc1]; omega)
                (by rw [Finset.card_insert_of_notMem hs0_not, hc1]; omega)
              ext x
              simp only [Finset.mem_inter, Finset.mem_insert, tailSeats, Finset.mem_filter,
                Finset.mem_univ, true_and, hnext_i]
              constructor
              · rintro ⟨rfl | hx, hge⟩
                · omega
                · exact ⟨Or.inr hx, hge⟩
              · rintro ⟨rfl | hx, hge⟩
                · omega
                · exact ⟨Or.inr hx, hge⟩
            have hconst2 : ∀ s ∈ (Finset.univ \ occ₂).filter (fun s : Fin n => s.val < i),
                t * ampStep n k t r (insert s occ₂) = t * ampStep n k t r (insert s0 occ₁) := by
              intro s hs
              congr 1
              have hs_not : s ∉ occ₂ := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hs).1).2
              have hs0_not : s0 ∉ occ₁ := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hs0).1).2
              have hs_lt : s.val < i := (Finset.mem_filter.mp hs).2
              have hs0_lt : s0.val < i := (Finset.mem_filter.mp hs0).2
              apply ih _ _ (by omega) (by omega)
                (by rw [Finset.card_insert_of_notMem hs_not, hc2]; omega)
                (by rw [Finset.card_insert_of_notMem hs0_not, hc1]; omega)
              ext x
              simp only [Finset.mem_inter, Finset.mem_insert, tailSeats, Finset.mem_filter,
                Finset.mem_univ, true_and, hnext_i]
              constructor
              · rintro ⟨rfl | hx, hge⟩
                · omega
                · have hx1 : x ∈ occ₁ ∩ tailSeats n (n - r) := by
                    rw [htail_eq_next]; exact Finset.mem_inter.mpr ⟨hx, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩⟩
                  exact ⟨Or.inr (Finset.mem_inter.mp hx1).1, hge⟩
              · rintro ⟨rfl | hx, hge⟩
                · omega
                · have hx2 : x ∈ occ₂ ∩ tailSeats n (n - r) := by
                    rw [← htail_eq_next]; exact Finset.mem_inter.mpr ⟨hx, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩⟩
                  exact ⟨Or.inr (Finset.mem_inter.mp hx2).1, hge⟩
            rw [Finset.sum_congr rfl hconst1, Finset.sum_congr rfl hconst2,
              Finset.sum_const, Finset.sum_const, hcard_eq]
          · have h1e : (Finset.univ \ occ₁).filter (fun s : Fin n => s.val < i) = ∅ :=
              Finset.not_nonempty_iff_eq_empty.mp hne
            have h2e : (Finset.univ \ occ₂).filter (fun s : Fin n => s.val < i) = ∅ :=
              Finset.card_eq_zero.mp (by rw [← hcard_eq, h1e, Finset.card_empty])
            rw [h1e, h2e, Finset.sum_empty, Finset.sum_empty]
        · rw [htail_sdiff]
          refine Finset.sum_congr rfl fun s hs => ?_
          congr 1
          have hs_t : s ∈ tailSeats n (i + 1) := (Finset.mem_sdiff.mp hs).1
          have hs_not2 : s ∉ occ₂ := fun h => (Finset.mem_sdiff.mp hs).2 (Finset.mem_inter.mpr ⟨h, hs_t⟩)
          have hs_not1 : s ∉ occ₁ := by
            intro h
            have : s ∈ occ₂ ∩ tailSeats n (n - r) := by
              rw [← htail_eq_next]; exact Finset.mem_inter.mpr ⟨h, by rwa [hnext_i]⟩
            exact hs_not2 (Finset.mem_inter.mp this).1
          apply ih _ _ (by omega) (by omega)
            (by rw [Finset.card_insert_of_notMem hs_not1, hc1]; omega)
            (by rw [Finset.card_insert_of_notMem hs_not2, hc2]; omega)
          ext x
          simp only [Finset.mem_inter, Finset.mem_insert]
          constructor
          · rintro ⟨rfl | hx, hxt⟩
            · exact ⟨Or.inl rfl, hxt⟩
            · have : x ∈ occ₂ ∩ tailSeats n (n - r) := by
                rw [← htail_eq_next]; exact Finset.mem_inter.mpr ⟨hx, hxt⟩
              exact ⟨Or.inr (Finset.mem_inter.mp this).1, hxt⟩
          · rintro ⟨rfl | hx, hxt⟩
            · exact ⟨Or.inl rfl, hxt⟩
            · have : x ∈ occ₁ ∩ tailSeats n (n - r) := by
                rw [htail_eq_next]; exact Finset.mem_inter.mpr ⟨hx, hxt⟩
              exact ⟨Or.inr (Finset.mem_inter.mp this).1, hxt⟩
      · have hi_occ2 : (⟨i, hi_lt⟩ : Fin n) ∉ occ₂ := fun h => hi_occ (hmem_iff.mpr h)
        simp only [hi_occ, hi_occ2, not_false_eq_true, ↓reduceIte]
        apply ih _ _ (by omega) (by omega)
          (by rw [Finset.card_insert_of_notMem hi_occ, hc1]; omega)
          (by rw [Finset.card_insert_of_notMem hi_occ2, hc2]; omega)
        ext x
        simp only [Finset.mem_inter, Finset.mem_insert, tailSeats, Finset.mem_filter,
          Finset.mem_univ, true_and, hnext_i]
        constructor
        · rintro ⟨rfl | hx, hge⟩
          · omega
          · have : x ∈ occ₂ ∩ tailSeats n (n - r) := by
              rw [← htail_eq_next]; exact Finset.mem_inter.mpr ⟨hx, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩⟩
            exact ⟨Or.inr (Finset.mem_inter.mp this).1, hge⟩
        · rintro ⟨rfl | hx, hge⟩
          · omega
          · have : x ∈ occ₁ ∩ tailSeats n (n - r) := by
              rw [htail_eq_next]; exact Finset.mem_inter.mpr ⟨hx, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩⟩
            exact ⟨Or.inr (Finset.mem_inter.mp this).1, hge⟩

/-- Canonical prefix-padding of a tail subset `B ⊆ tailSeats n (n - rem)` with `|B| ≤ n - rem`
to a full occupied set `occ` of size `n - rem` with `occ ∩ tailSeats n (n - rem) = B`. -/
private def padTail (n rem : ℕ) (B : Finset (Fin n)) : Finset (Fin n) :=
  B ∪ (Finset.univ.filter (fun s : Fin n => s.val < (n - rem) - B.card))

private lemma padTail_card {n rem : ℕ} {B : Finset (Fin n)}
    (hrn : rem ≤ n) (hBsub : B ⊆ tailSeats n (n - rem)) (hBcard : B.card ≤ n - rem) :
    (padTail n rem B).card = n - rem := by
  unfold padTail
  have hdisj : Disjoint B (Finset.univ.filter (fun s : Fin n => s.val < (n - rem) - B.card)) := by
    rw [Finset.disjoint_left]
    intro s hsB hsF
    have ht := hBsub hsB
    simp only [tailSeats, Finset.mem_filter, Finset.mem_univ, true_and] at ht hsF
    omega
  rw [Finset.card_union_of_disjoint hdisj]
  have hlow : (Finset.univ.filter (fun s : Fin n => s.val < (n - rem) - B.card)).card =
      (n - rem) - B.card := by
    have heq : Finset.univ.filter (fun s : Fin n => s.val < (n - rem) - B.card) =
        (Finset.range ((n - rem) - B.card)).attach.image
          (fun x => ⟨x.1, by have := Finset.mem_range.mp x.2; omega⟩) := by
      ext s
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
        Finset.mem_attach, Subtype.exists, Finset.mem_range]
      constructor
      · intro hs; exact ⟨s.val, hs, Fin.ext rfl⟩
      · rintro ⟨a, ha, rfl⟩; exact ha
    rw [heq, Finset.card_image_of_injective]
    · rw [Finset.card_attach, Finset.card_range]
    · intro a b hab; exact Subtype.ext (congrArg Fin.val hab)
  rw [hlow]
  omega

private lemma padTail_inter {n rem : ℕ} {B : Finset (Fin n)}
    (hBsub : B ⊆ tailSeats n (n - rem)) :
    padTail n rem B ∩ tailSeats n (n - rem) = B := by
  ext s
  simp only [padTail, Finset.mem_inter, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
    true_and, tailSeats]
  constructor
  · rintro ⟨hB | hlt, hge⟩
    · exact hB
    · omega
  · intro hB
    have ht := hBsub hB
    simp only [tailSeats, Finset.mem_filter, Finset.mem_univ, true_and] at ht
    exact ⟨Or.inl hB, ht⟩

/-- Value of `ampStep` on a tail subset `B ⊆ tailSeats n (n - rem)` (for `n - rem ≥ k`). -/
private noncomputable def ampTail (n k : ℕ) (t : ℝ) (rem : ℕ) (B : Finset (Fin n)) : ℝ :=
  ampStep n k t rem (padTail n rem B)

private lemma ampStep_eq_ampTail {n k rem : ℕ} {t : ℝ} {occ : Finset (Fin n)}
    (hrn : rem ≤ n) (hk : k ≤ n - rem) (hcard : occ.card = n - rem) :
    ampStep n k t rem occ = ampTail n k t rem (occ ∩ tailSeats n (n - rem)) := by
  unfold ampTail
  have hsub : occ ∩ tailSeats n (n - rem) ⊆ tailSeats n (n - rem) := Finset.inter_subset_right
  have hbc : (occ ∩ tailSeats n (n - rem)).card ≤ n - rem := by
    rw [← hcard]; exact Finset.card_le_card Finset.inter_subset_left
  apply ampStep_depends_on_tail n k t rem occ _ hrn hk hcard (padTail_card hrn hsub hbc)
  rw [padTail_inter hsub]

/-- Master tail-sum theorem: for any `rem ≤ n - k` and `m ≤ n - rem`,
the sum of `ampTail n k t rem B` over all `m`-element subsets `B ⊆ tailSeats n (n - rem)`
equals `sumS rem m t`! -/
private lemma sum_ampTail_eq_sumS (n k : ℕ) (t : ℝ) :
    ∀ (rem : ℕ), rem ≤ n → k ≤ n - rem →
      ∀ m : ℕ, m ≤ n - rem →
        (∑ B ∈ (tailSeats n (n - rem)).powersetCard m, ampTail n k t rem B) = sumS rem m t := by
  intro rem
  induction rem with
  | zero =>
      intro _ _ m _
      have hts : tailSeats n (n - 0) = ∅ := by
        ext s; simp only [tailSeats, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.notMem_empty, iff_false, Nat.sub_zero]; omega
      rw [hts]
      cases m with
      | zero =>
          simp only [Finset.powersetCard_zero, Finset.sum_singleton, sumS_zero_zero]
          rfl
      | succ m =>
          have he : (∅ : Finset (Fin n)).powersetCard (m + 1) = ∅ := by simp
          rw [he, Finset.sum_empty, sumS_zero_succ]
  | succ r ih =>
      intro hrn hk m hm
      set i := n - (r + 1) with hi_def
      have hi_lt : i < n := by omega
      have hnext_i : n - r = i + 1 := by omega
      cases m with
      | zero =>
          simp only [Finset.powersetCard_zero, Finset.sum_singleton, sumS_succ_zero]
          -- `ampTail n k t (r+1) ∅ = ampTail n k t r ∅ = ... = 1`
          have h0 : ampTail n k t (r + 1) ∅ = ampTail n k t r ∅ := by
            conv_lhs => unfold ampTail
            have hpad0 : padTail n (r + 1) ∅ = Finset.univ.filter (fun s : Fin n => s.val < i) := by
              unfold padTail
              rw [Finset.empty_union, Finset.card_empty, Nat.sub_zero, ← hi_def]
            have hnot : (⟨i, hi_lt⟩ : Fin n) ∉ padTail n (r + 1) ∅ := by
              rw [hpad0, Finset.mem_filter]
              rintro ⟨_, hlt⟩
              exact lt_irrefl i hlt
            unfold ampStep
            simp only [← hi_def, show ¬ i < k by omega, ↓reduceIte, hi_lt, ↓reduceDIte, hnot, not_false_eq_true]
            have hcard0 : (insert (⟨i, hi_lt⟩ : Fin n) (padTail n (r + 1) ∅)).card = n - r := by
              rw [Finset.card_insert_of_notMem hnot,
                padTail_card hrn (Finset.empty_subset _) (by simp)]
              omega
            rw [ampStep_eq_ampTail (by omega) (by omega) hcard0]
            congr 1
            ext s
            rw [hpad0]
            simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_filter, Finset.mem_univ,
              true_and, tailSeats, hnext_i, Finset.notMem_empty, iff_false]
            rintro ⟨rfl | hlt, hge⟩
            · exact absurd hge (by change ¬ (i + 1 ≤ i); omega)
            · omega
          rw [h0]
          have ih0 := ih (by omega) (by omega) 0 (by omega)
          simpa [Finset.powersetCard_zero, sumS_succ_zero] using ih0
      | succ m =>
          -- Split `B ∈ (tailSeats n i).powersetCard (m+1)` by `⟨i, hi_lt⟩ ∈ B` vs `∉ B`
          let ei : Fin n := ⟨i, hi_lt⟩
          have hei_ts : ei ∈ tailSeats n i := by simp [ei, tailSeats]
          have hts_eq : tailSeats n i = insert ei (tailSeats n (n - r)) := by
            ext s
            simp only [tailSeats, Finset.mem_filter, Finset.mem_univ, true_and,
              Finset.mem_insert, ei, hnext_i]
            constructor
            · intro hs
              by_cases heq : s.val = i
              · exact Or.inl (Fin.ext heq)
              · exact Or.inr (by omega)
            · rintro (rfl | hs)
              · exact le_rfl
              · omega
          have hei_not_next : ei ∉ tailSeats n (n - r) := by
            simp only [tailSeats, Finset.mem_filter, Finset.mem_univ, true_and, ei, hnext_i]; omega
          rw [hts_eq, Finset.powersetCard_succ_insert hei_not_next, Finset.sum_union]
          swap
          · rw [Finset.disjoint_left]
            intro B hB1 hB2
            have hsub := (Finset.mem_powersetCard.mp hB1).1
            obtain ⟨B0, _, rfl⟩ := Finset.mem_image.mp hB2
            exact hei_not_next (hsub (Finset.mem_insert_self ei B0))
          -- Part 1: `ei ∉ B`, so `B ⊆ tailSeats n (n - r)` of size `m + 1`:
          -- `ampTail n k t (r+1) B = ampTail n k t r B`!
          have hpart1 : (∑ B ∈ (tailSeats n (n - r)).powersetCard (m + 1), ampTail n k t (r + 1) B) =
              sumS r (m + 1) t := by
            rw [← ih (by omega) (by omega) (m + 1) (by omega)]
            refine Finset.sum_congr rfl fun B hB => ?_
            rcases Finset.mem_powersetCard.mp hB with ⟨hBsub, hBcard⟩
            have hBsub_i : B ⊆ tailSeats n i := hBsub.trans (by rw [hts_eq]; exact Finset.subset_insert _ _)
            have hnot_B : ei ∉ B := fun h => hei_not_next (hBsub h)
            have hnot_pad : ei ∉ padTail n (r + 1) B := by
              intro h
              have := (Finset.ext_iff.mp (padTail_inter hBsub_i) ei).mp (Finset.mem_inter.mpr ⟨h, hei_ts⟩)
              exact hnot_B this
            conv_lhs => unfold ampTail
            unfold ampStep
            simp only [← hi_def, show ¬ i < k by omega, ↓reduceIte, hi_lt, ↓reduceDIte]
            change (if ei ∉ padTail n (r + 1) B then _ else _) = _
            rw [if_pos hnot_pad]
            have hcard_ins : (insert ei (padTail n (r + 1) B)).card = n - r := by
              rw [Finset.card_insert_of_notMem hnot_pad,
                padTail_card hrn hBsub_i (by omega)]
              omega
            rw [ampStep_eq_ampTail (by omega) (by omega) hcard_ins]
            congr 1
            ext s
            simp only [Finset.mem_inter, Finset.mem_insert]
            constructor
            · rintro ⟨rfl | hs, hst⟩
              · exact absurd hst hei_not_next
              · have hs_i : s ∈ tailSeats n i := by
                  rw [hts_eq]; exact Finset.mem_insert_of_mem hst
                have := (Finset.ext_iff.mp (padTail_inter hBsub_i) s).mp (Finset.mem_inter.mpr ⟨hs, hs_i⟩)
                exact this
            · intro hsB
              exact ⟨Or.inr (Finset.mem_union_left _ hsB), hBsub hsB⟩
          -- Part 2: `B = insert ei B0` where `B0 ∈ (tailSeats n (n-r)).powersetCard m`
          rw [Finset.sum_image]
          swap
          · intro B1 hB1 B2 hB2 heq
            have h1 : ei ∉ B1 := fun h => hei_not_next ((Finset.mem_powersetCard.mp hB1).1 h)
            have h2 : ei ∉ B2 := fun h => hei_not_next ((Finset.mem_powersetCard.mp hB2).1 h)
            have := congrArg (fun S => S.erase ei) heq
            rwa [Finset.erase_insert h1, Finset.erase_insert h2] at this
          have hpart2 :
              (∑ B0 ∈ (tailSeats n (n - r)).powersetCard m,
                ampTail n k t (r + 1) (insert ei B0)) =
              (((m + 1 : ℕ) : ℝ) * t / ((r + 1 : ℕ) : ℝ)) * sumS r m t +
              (((m + 1 : ℕ) : ℝ) * t / ((r + 1 : ℕ) : ℝ)) * sumS r (m + 1) t := by
            -- Expand each `ampTail n k t (r+1) (insert ei B0)`
            have heach : ∀ B0 ∈ (tailSeats n (n - r)).powersetCard m,
                ampTail n k t (r + 1) (insert ei B0) =
                  (1 / ((r + 1 : ℕ) : ℝ)) * (
                    ((m + 1 : ℕ) : ℝ) * t * ampTail n k t r B0 +
                    ∑ s ∈ tailSeats n (n - r) \ B0, t * ampTail n k t r (insert s B0)) := by
              intro B0 hB0
              rcases Finset.mem_powersetCard.mp hB0 with ⟨hB0sub, hB0card⟩
              have hnot0 : ei ∉ B0 := fun h => hei_not_next (hB0sub h)
              have hBsub_i : insert ei B0 ⊆ tailSeats n i := by
                rw [hts_eq]; exact Finset.insert_subset_insert ei hB0sub
              have hBcard : (insert ei B0).card = m + 1 := by
                rw [Finset.card_insert_of_notMem hnot0, hB0card]
              set occ := padTail n (r + 1) (insert ei B0) with hocc_def
              have hocc_card : occ.card = i := padTail_card hrn hBsub_i (by omega)
              have hei_occ : ei ∈ occ := Finset.mem_union_left _ (Finset.mem_insert_self ei B0)
              have hfree_card : (Finset.univ \ occ).card = r + 1 := by
                rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin,
                  hocc_card]
                omega
              have hocc_inter_next : occ ∩ tailSeats n (n - r) = B0 := by
                ext s
                simp only [Finset.mem_inter]
                constructor
                · rintro ⟨hs_occ, hs_t⟩
                  have hs_i : s ∈ tailSeats n i := by rw [hts_eq]; exact Finset.mem_insert_of_mem hs_t
                  have h1 : s ∈ insert ei B0 := by
                    rw [← padTail_inter hBsub_i]; exact Finset.mem_inter.mpr ⟨hs_occ, hs_i⟩
                  rcases Finset.mem_insert.mp h1 with rfl | hB
                  · exact absurd hs_t hei_not_next
                  · exact hB
                · intro hsB0
                  exact ⟨Finset.mem_union_left _ (Finset.mem_insert_of_mem hsB0), hB0sub hsB0⟩
              conv_lhs => unfold ampTail
              rw [← hocc_def]
              unfold ampStep
              simp only [← hi_def, show ¬ i < k by omega, ↓reduceIte, hi_lt, ↓reduceDIte]
              change (if ei ∉ occ then _ else _) = _
              rw [if_neg (not_not.mpr hei_occ), hfree_card]
              congr 1
              -- Split `univ \ occ` into `< i` (cardinality `m + 1`) and `tailSeats n (n-r) \ B0`
              have hsplit_free : Finset.univ \ occ =
                  ((Finset.univ \ occ).filter (fun s : Fin n => s.val < i)) ∪
                  (tailSeats n (n - r) \ B0) := by
                ext s
                simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union,
                  Finset.mem_filter, tailSeats, hnext_i]
                constructor
                · intro hnot
                  by_cases hlt : s.val < i
                  · exact Or.inl ⟨hnot, hlt⟩
                  · right
                    have hne : s.val ≠ i := by
                      intro heq; apply hnot; rw [show s = ei from Fin.ext heq]; exact hei_occ
                    refine ⟨by omega, fun hsB0 => hnot (Finset.mem_union_left _ (Finset.mem_insert_of_mem hsB0))⟩
                · rintro (⟨hnot, _⟩ | ⟨hge, hnotB0⟩)
                  · exact hnot
                  · intro hs_occ
                    have hs_t : s ∈ tailSeats n (n - r) := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
                    exact hnotB0 (by rw [← hocc_inter_next]; exact Finset.mem_inter.mpr ⟨hs_occ, hs_t⟩)
              have hdisj_free : Disjoint
                  ((Finset.univ \ occ).filter (fun s : Fin n => s.val < i))
                  (tailSeats n (n - r) \ B0) := by
                rw [Finset.disjoint_left]; intro s h1 h2
                simp only [Finset.mem_filter, Finset.mem_sdiff, tailSeats, Finset.mem_univ, true_and,
                  hnext_i] at h1 h2
                omega
              rw [hsplit_free, Finset.sum_union hdisj_free]
              congr 1
              · -- `< i` part: each `s` gives `t * ampTail n k t r B0`, and count = `m + 1`
                have hlow_card : ((Finset.univ \ occ).filter (fun s : Fin n => s.val < i)).card = m + 1 := by
                  have hlt_all : (Finset.univ.filter (fun s : Fin n => s.val < i)).card = i := by
                    have heq : Finset.univ.filter (fun s : Fin n => s.val < i) =
                        (Finset.range i).attach.image
                          (fun x => ⟨x.1, lt_trans (Finset.mem_range.mp x.2) hi_lt⟩) := by
                      ext s
                      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
                        Finset.mem_attach, Subtype.exists, Finset.mem_range]
                      exact ⟨fun hs => ⟨s.val, hs, Fin.ext rfl⟩, by rintro ⟨a, ha, rfl⟩; exact ha⟩
                    rw [heq, Finset.card_image_of_injective]
                    · rw [Finset.card_attach, Finset.card_range]
                    · intro a b hab; exact Subtype.ext (congrArg Fin.val hab)
                  have hocc_split : occ.card =
                      (occ.filter (fun s : Fin n => s.val < i)).card + (occ ∩ tailSeats n i).card := by
                    have : occ ∩ tailSeats n i = occ.filter (fun s : Fin n => ¬ s.val < i) := by
                      ext s; simp only [Finset.mem_inter, tailSeats, Finset.mem_filter,
                        Finset.mem_univ, true_and, not_lt]
                    rw [this, Finset.card_filter_add_card_filter_not]
                  have hlow_split : (Finset.univ.filter (fun s : Fin n => s.val < i)).card =
                      (occ.filter (fun s : Fin n => s.val < i)).card +
                      ((Finset.univ \ occ).filter (fun s : Fin n => s.val < i)).card := by
                    have hu : Finset.univ.filter (fun s : Fin n => s.val < i) =
                        occ.filter (fun s : Fin n => s.val < i) ∪
                        (Finset.univ \ occ).filter (fun s : Fin n => s.val < i) := by
                      ext s; simp only [Finset.mem_filter, Finset.mem_univ, true_and,
                        Finset.mem_union, Finset.mem_sdiff]; tauto
                    have hd : Disjoint (occ.filter (fun s : Fin n => s.val < i))
                        ((Finset.univ \ occ).filter (fun s : Fin n => s.val < i)) := by
                      rw [Finset.disjoint_left]; intro s h1 h2
                      simp only [Finset.mem_filter, Finset.mem_sdiff] at h1 h2; exact h2.1.2 h1.1
                    rw [hu, Finset.card_union_of_disjoint hd]
                  have hinter_card : (occ ∩ tailSeats n i).card = m + 1 := by
                    rw [hocc_def, padTail_inter hBsub_i, hBcard]
                  omega
                have hconst : ∀ s ∈ (Finset.univ \ occ).filter (fun s : Fin n => s.val < i),
                    t * ampStep n k t r (insert s occ) = t * ampTail n k t r B0 := by
                  intro s hs
                  congr 1
                  have hs_not : s ∉ occ := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hs).1).2
                  have hs_lt : s.val < i := (Finset.mem_filter.mp hs).2
                  rw [ampStep_eq_ampTail (by omega) (by omega)
                    (by rw [Finset.card_insert_of_notMem hs_not, hocc_card]; omega)]
                  congr 1
                  ext x
                  simp only [Finset.mem_inter, Finset.mem_insert]
                  constructor
                  · rintro ⟨rfl | hx, hxt⟩
                    · simp only [tailSeats, Finset.mem_filter, Finset.mem_univ, true_and, hnext_i] at hxt
                      omega
                    · rw [← hocc_inter_next]; exact Finset.mem_inter.mpr ⟨hx, hxt⟩
                  · intro hxB0
                    have hx_inter : x ∈ occ ∩ tailSeats n (n - r) := by rw [hocc_inter_next]; exact hxB0
                    exact ⟨Or.inr (Finset.mem_inter.mp hx_inter).1, (Finset.mem_inter.mp hx_inter).2⟩
                rw [Finset.sum_congr rfl hconst, Finset.sum_const, hlow_card, nsmul_eq_mul]
                ring
              · -- `≥ i + 1` part
                refine Finset.sum_congr rfl fun s hs => ?_
                congr 1
                have hs_t : s ∈ tailSeats n (n - r) := (Finset.mem_sdiff.mp hs).1
                have hs_notB0 : s ∉ B0 := (Finset.mem_sdiff.mp hs).2
                have hs_not_occ : s ∉ occ := by
                  intro h; exact hs_notB0 (by rw [← hocc_inter_next]; exact Finset.mem_inter.mpr ⟨h, hs_t⟩)
                rw [ampStep_eq_ampTail (by omega) (by omega)
                  (by rw [Finset.card_insert_of_notMem hs_not_occ, hocc_card]; omega)]
                congr 1
                ext x
                simp only [Finset.mem_inter, Finset.mem_insert]
                constructor
                · rintro ⟨rfl | hx, hxt⟩
                  · exact Or.inl rfl
                  · exact Or.inr (by rw [← hocc_inter_next]; exact Finset.mem_inter.mpr ⟨hx, hxt⟩)
                · rintro (rfl | hxB0)
                  · exact ⟨Or.inl rfl, hs_t⟩
                  · have hx_inter : x ∈ occ ∩ tailSeats n (n - r) := by rw [hocc_inter_next]; exact hxB0
                    exact ⟨Or.inr (Finset.mem_inter.mp hx_inter).1, (Finset.mem_inter.mp hx_inter).2⟩
            rw [Finset.sum_congr rfl heach, ← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
            -- Double-count `∑ B0 (size m) ∑ s ∉ B0 f (insert s B0) = (m + 1) * ∑ B' (size m+1) f B'`!
            have hdc : (∑ B0 ∈ (tailSeats n (n - r)).powersetCard m,
                ∑ s ∈ tailSeats n (n - r) \ B0, t * ampTail n k t r (insert s B0)) =
                ((m + 1 : ℕ) : ℝ) * t *
                  ∑ B' ∈ (tailSeats n (n - r)).powersetCard (m + 1), ampTail n k t r B' := by
              -- Rewrite LHS as sum over pairs `(B0, s)` and biject with `(B', s)` where `s ∈ B'`!
              let LHS_pairs := (tailSeats n (n - r)).powersetCard m |>.biUnion
                (fun B0 => (tailSeats n (n - r) \ B0).image (fun s => (B0, s)))
              let RHS_pairs := (tailSeats n (n - r)).powersetCard (m + 1) |>.biUnion
                (fun B' => B'.image (fun s => (B', s)))
              have h1 : (∑ B0 ∈ (tailSeats n (n - r)).powersetCard m,
                  ∑ s ∈ tailSeats n (n - r) \ B0, ampTail n k t r (insert s B0)) =
                  ∑ p ∈ LHS_pairs, ampTail n k t r (insert p.2 p.1) := by
                rw [Finset.sum_biUnion]
                · refine Finset.sum_congr rfl fun B0 _ => ?_
                  rw [Finset.sum_image]
                  intro s1 _ s2 _ h; exact (Prod.mk.inj h).2
                · intro B1 _ B2 _ hne
                  dsimp only [Function.onFun]
                  rw [Finset.disjoint_left]
                  intro p hp1 hp2
                  obtain ⟨s1, _, rfl⟩ := Finset.mem_image.mp hp1
                  obtain ⟨s2, _, h2⟩ := Finset.mem_image.mp hp2
                  exact hne (Prod.mk.inj h2).1.symm
              have h2 : (∑ B' ∈ (tailSeats n (n - r)).powersetCard (m + 1),
                  ((m + 1 : ℕ) : ℝ) * ampTail n k t r B') =
                  ∑ p ∈ RHS_pairs, ampTail n k t r p.1 := by
                rw [Finset.sum_biUnion]
                · refine Finset.sum_congr rfl fun B' hB' => ?_
                  rw [Finset.sum_image]
                  · dsimp only
                    rw [Finset.sum_const, (Finset.mem_powersetCard.mp hB').2, nsmul_eq_mul]
                  · intro s1 _ s2 _ h; exact (Prod.mk.inj h).2
                · intro B1 _ B2 _ hne
                  dsimp only [Function.onFun]
                  rw [Finset.disjoint_left]
                  intro p hp1 hp2
                  obtain ⟨s1, _, rfl⟩ := Finset.mem_image.mp hp1
                  obtain ⟨s2, _, h2⟩ := Finset.mem_image.mp hp2
                  exact hne (Prod.mk.inj h2).1.symm
              have hbij : (∑ p ∈ LHS_pairs, ampTail n k t r (insert p.2 p.1)) =
                  ∑ p ∈ RHS_pairs, ampTail n k t r p.1 := by
                refine Finset.sum_bij (fun p _ => (insert p.2 p.1, p.2)) ?_ ?_ ?_ ?_
                · intro p hp
                  obtain ⟨B0, hB0, hp'⟩ := Finset.mem_biUnion.mp hp
                  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hp'
                  rcases Finset.mem_powersetCard.mp hB0 with ⟨hB0s, hB0c⟩
                  rcases Finset.mem_sdiff.mp hs with ⟨hsts, hsnot⟩
                  refine Finset.mem_biUnion.mpr ⟨insert s B0, ?_, ?_⟩
                  · exact Finset.mem_powersetCard.mpr ⟨Finset.insert_subset hsts hB0s,
                      by rw [Finset.card_insert_of_notMem hsnot, hB0c]⟩
                  · exact Finset.mem_image.mpr ⟨s, Finset.mem_insert_self s B0, rfl⟩
                · intro p1 hp1 p2 hp2 heq
                  obtain ⟨B1, _, hp1'⟩ := Finset.mem_biUnion.mp hp1
                  obtain ⟨s1, hs1, rfl⟩ := Finset.mem_image.mp hp1'
                  obtain ⟨B2, _, hp2'⟩ := Finset.mem_biUnion.mp hp2
                  obtain ⟨s2, hs2, rfl⟩ := Finset.mem_image.mp hp2'
                  rcases Prod.mk.inj heq with ⟨hins, hs⟩
                  subst hs
                  have h1 : s1 ∉ B1 := (Finset.mem_sdiff.mp hs1).2
                  have h2 : s1 ∉ B2 := (Finset.mem_sdiff.mp hs2).2
                  have hB : B1 = B2 := by
                    have := congrArg (fun S => S.erase s1) hins
                    rwa [Finset.erase_insert h1, Finset.erase_insert h2] at this
                  rw [hB]
                · intro q hq
                  obtain ⟨B', hB', hq'⟩ := Finset.mem_biUnion.mp hq
                  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hq'
                  rcases Finset.mem_powersetCard.mp hB' with ⟨hB's, hB'c⟩
                  refine ⟨(B'.erase s, s), ?_, ?_⟩
                  · refine Finset.mem_biUnion.mpr ⟨B'.erase s, ?_, ?_⟩
                    · exact Finset.mem_powersetCard.mpr
                        ⟨(Finset.erase_subset s B').trans hB's,
                         by rw [Finset.card_erase_of_mem hs, hB'c]; omega⟩
                    · exact Finset.mem_image.mpr ⟨s, Finset.mem_sdiff.mpr ⟨hB's hs, Finset.notMem_erase s B'⟩, rfl⟩
                  · simp [Finset.insert_erase hs]
                · intro _ _; rfl
              calc (∑ B0 ∈ (tailSeats n (n - r)).powersetCard m,
                    ∑ s ∈ tailSeats n (n - r) \ B0, t * ampTail n k t r (insert s B0))
                  = t * ∑ B0 ∈ (tailSeats n (n - r)).powersetCard m,
                      ∑ s ∈ tailSeats n (n - r) \ B0, ampTail n k t r (insert s B0) := by
                    simp_rw [← Finset.mul_sum]
                _ = t * ∑ p ∈ LHS_pairs, ampTail n k t r (insert p.2 p.1) := by rw [h1]
                _ = t * ∑ p ∈ RHS_pairs, ampTail n k t r p.1 := by rw [hbij]
                _ = t * ∑ B' ∈ (tailSeats n (n - r)).powersetCard (m + 1),
                      ((m + 1 : ℕ) : ℝ) * ampTail n k t r B' := by rw [← h2]
                _ = ((m + 1 : ℕ) : ℝ) * t *
                      ∑ B' ∈ (tailSeats n (n - r)).powersetCard (m + 1), ampTail n k t r B' := by
                    rw [← Finset.mul_sum]; ring
            rw [hdc, ih (by omega) (by omega) m (by omega), ih (by omega) (by omega) (m + 1) (by omega)]
            ring
          rw [hpart1, hpart2, sumS_recurrence]
          have hrne : ((r + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
          field_simp [hrne]
          ring

/-- Binomial inversion identity: `∑_{m=0}^{k'} C(k', m) * sumS N m t = risingP k' N t`. -/
private lemma binomial_inversion_sumS (k' N : ℕ) (t : ℝ) :
    (∑ m ∈ Finset.range (k' + 1), (Nat.choose k' m : ℝ) * sumS N m t) = risingP k' N t := by
  unfold sumS
  simp_rw [Finset.mul_sum]
  -- Rewrite inner sum over `r ∈ range (m + 1)` as `r ∈ range (k' + 1)` with `if r ≤ m`
  have hpad : ∀ m ∈ Finset.range (k' + 1),
      (∑ r ∈ Finset.range (m + 1),
        (Nat.choose k' m : ℝ) * ((-1 : ℝ) ^ (m - r) * (Nat.choose m r : ℝ) * risingP r N t)) =
      ∑ r ∈ Finset.range (k' + 1),
        if r ≤ m then
          (Nat.choose k' m : ℝ) * ((-1 : ℝ) ^ (m - r) * (Nat.choose m r : ℝ) * risingP r N t)
        else 0 := by
    intro m hm
    rw [Finset.mem_range] at hm
    symm
    rw [← Finset.sum_filter]
    congr 1
    ext r; simp only [Finset.mem_filter, Finset.mem_range]; omega
  rw [Finset.sum_congr rfl hpad, Finset.sum_comm]
  rw [Finset.sum_eq_single k']
  · rw [Finset.sum_eq_single k']
    · simp
    · intro m hm hne
      rw [Finset.mem_range] at hm
      simp [show ¬ k' ≤ m by omega]
    · intro h; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self k')) h
  · intro r hr hne
    rw [Finset.mem_range] at hr
    have hcoeff : (∑ m ∈ Finset.range (k' + 1),
        if r ≤ m then (Nat.choose k' m : ℝ) * ((-1 : ℝ) ^ (m - r) * (Nat.choose m r : ℝ) * risingP r N t)
        else 0) =
        ((Nat.choose k' r : ℝ) * risingP r N t) *
          ∑ j ∈ Finset.range (k' - r + 1), (-1 : ℝ) ^ j * (Nat.choose (k' - r) j : ℝ) := by
      rw [Finset.mul_sum, ← Finset.sum_filter]
      refine Finset.sum_bij (fun m _ => m - r) ?_ ?_ ?_ ?_
      · intro m hm; simp only [Finset.mem_filter, Finset.mem_range] at hm ⊢; omega
      · intro m1 h1 m2 h2 heq; simp only [Finset.mem_filter, Finset.mem_range] at h1 h2; omega
      · intro j hj; rw [Finset.mem_range] at hj
        exact ⟨r + j, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), by omega⟩, by omega⟩
      · intro m hm
        simp only [Finset.mem_filter, Finset.mem_range] at hm
        have hch : Nat.choose k' m * Nat.choose m r = Nat.choose k' r * Nat.choose (k' - r) (m - r) := by
          have h1 := Nat.choose_mul_factorial_mul_factorial (show m ≤ k' by omega)
          have h2 := Nat.choose_mul_factorial_mul_factorial (show r ≤ m by omega)
          have h3 := Nat.choose_mul_factorial_mul_factorial (show r ≤ k' by omega)
          have h4 := Nat.choose_mul_factorial_mul_factorial (show m - r ≤ k' - r by omega)
          rw [show k' - r - (m - r) = k' - m by omega] at h4
          have hpos : 0 < Nat.factorial r * Nat.factorial (m - r) * Nat.factorial (k' - m) := by
            positivity
          have hL : (Nat.choose k' m * Nat.choose m r) *
              (Nat.factorial r * Nat.factorial (m - r) * Nat.factorial (k' - m)) =
              Nat.factorial k' := by
            calc (Nat.choose k' m * Nat.choose m r) *
                  (Nat.factorial r * Nat.factorial (m - r) * Nat.factorial (k' - m))
                = Nat.choose k' m * (Nat.choose m r * Nat.factorial r * Nat.factorial (m - r)) *
                    Nat.factorial (k' - m) := by ring
              _ = Nat.choose k' m * Nat.factorial m * Nat.factorial (k' - m) := by rw [h2]
              _ = Nat.factorial k' := h1
          have hR : (Nat.choose k' r * Nat.choose (k' - r) (m - r)) *
              (Nat.factorial r * Nat.factorial (m - r) * Nat.factorial (k' - m)) =
              Nat.factorial k' := by
            calc (Nat.choose k' r * Nat.choose (k' - r) (m - r)) *
                  (Nat.factorial r * Nat.factorial (m - r) * Nat.factorial (k' - m))
                = Nat.choose k' r * Nat.factorial r *
                    (Nat.choose (k' - r) (m - r) * Nat.factorial (m - r) * Nat.factorial (k' - m)) := by ring
              _ = Nat.choose k' r * Nat.factorial r * Nat.factorial (k' - r) := by rw [h4]
              _ = Nat.factorial k' := h3
          exact Nat.eq_of_mul_eq_mul_right hpos (hL.trans hR.symm)
        have hchR : (Nat.choose k' m : ℝ) * (Nat.choose m r : ℝ) =
            (Nat.choose k' r : ℝ) * (Nat.choose (k' - r) (m - r) : ℝ) := by exact_mod_cast hch
        calc (Nat.choose k' m : ℝ) * ((-1 : ℝ) ^ (m - r) * (Nat.choose m r : ℝ) * risingP r N t)
            = ((Nat.choose k' m : ℝ) * (Nat.choose m r : ℝ)) * ((-1 : ℝ) ^ (m - r) * risingP r N t) := by ring
          _ = ((Nat.choose k' r : ℝ) * (Nat.choose (k' - r) (m - r) : ℝ)) * ((-1 : ℝ) ^ (m - r) * risingP r N t) := by rw [hchR]
          _ = (Nat.choose k' r : ℝ) * risingP r N t * ((-1 : ℝ) ^ (m - r) * (Nat.choose (k' - r) (m - r) : ℝ)) := by ring
    rw [hcoeff]
    have hzero : (∑ j ∈ Finset.range (k' - r + 1), (-1 : ℝ) ^ j * (Nat.choose (k' - r) j : ℝ)) = 0 := by
      have h := add_pow (-1 : ℝ) (1 : ℝ) (k' - r)
      have h0 : (-1 + 1 : ℝ) ^ (k' - r) = 0 := by
        rw [show (-1 + 1 : ℝ) = 0 by norm_num]; exact zero_pow (by omega)
      rw [h0] at h
      rw [h]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [one_pow, mul_one]
    rw [hzero, mul_zero]
  · intro h; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self k')) h

/-- Unrolling the first `j ≤ k` absent-minded steps of `ampStep` into a uniform average over
injections `f : Fin j → Fin n`. -/
private lemma ampStep_unroll_absent (n k : ℕ) (t : ℝ) :
    ∀ (j : ℕ), j ≤ k → j ≤ n →
      ampStep n k t n ∅ =
        ((Nat.factorial (n - j) : ℝ) / (Nat.factorial n : ℝ)) *
          ∑ f ∈ (Finset.univ : Finset (Fin j → Fin n)).filter Function.Injective,
            (∏ i : Fin j, if (f i).val = i.val then (1 : ℝ) else t) *
              ampStep n k t (n - j) (Finset.univ.image f) := by
  intro j
  induction j with
  | zero =>
      intro _ _
      simp only [Nat.sub_zero, div_self (Nat.cast_ne_zero (R := ℝ).mpr (Nat.factorial_ne_zero n)), one_mul]
      have huniq : (Finset.univ : Finset (Fin 0 → Fin n)).filter Function.Injective = {Fin.elim0} := by
        ext f
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        exact ⟨fun _ => funext fun x => Fin.elim0 x, fun _ x _ => Fin.elim0 x⟩
      rw [huniq, Finset.sum_singleton, Finset.univ_eq_empty, Finset.prod_empty, one_mul,
        Finset.image_empty]
  | succ j ih =>
      intro hjk hjn
      rw [ih (by omega) (by omega)]
      -- Expand `ampStep n k t (n - j) (univ.image f)` for each injective `f : Fin j → Fin n`
      have hnj : n - j = (n - (j + 1)) + 1 := by omega
      have hstep : ∀ f ∈ (Finset.univ : Finset (Fin j → Fin n)).filter Function.Injective,
          ampStep n k t (n - j) (Finset.univ.image f) =
            (1 / ((n - j : ℕ) : ℝ)) *
              ∑ s ∈ Finset.univ \ Finset.univ.image f,
                (if s.val = j then (1 : ℝ) else t) *
                  ampStep n k t (n - (j + 1)) (insert s (Finset.univ.image f)) := by
        intro f hf
        have hinj : Function.Injective f := (Finset.mem_filter.mp hf).2
        have hcard_im : (Finset.univ.image f).card = j := by
          rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
        have hcard_free : (Finset.univ \ Finset.univ.image f).card = n - j := by
          rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, hcard_im]
        conv_lhs => rw [hnj]; unfold ampStep
        have hi_eq : n - (n - (j + 1) + 1) = j := by omega
        simp only [hi_eq, show j < k by omega, ↓reduceIte, hcard_free]
      -- Combine factorial factor
      have hfac : ((Nat.factorial (n - j) : ℝ) / (Nat.factorial n : ℝ)) * (1 / ((n - j : ℕ) : ℝ)) =
          (Nat.factorial (n - (j + 1)) : ℝ) / (Nat.factorial n : ℝ) := by
        have h1 : Nat.factorial (n - j) = (n - j) * Nat.factorial (n - (j + 1)) := by
          rw [hnj, Nat.factorial_succ]
        have hne : ((n - j : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        rw [h1, Nat.cast_mul]
        field_simp [hne]
      rw [Finset.sum_congr rfl fun f hf => by rw [hstep f hf]]
      simp_rw [← mul_assoc, mul_comm _ (1 / ((n - j : ℕ) : ℝ)), mul_assoc]
      rw [← Finset.mul_sum, ← mul_assoc, hfac]
      congr 1
      -- Biject `(f, s)` with `f : Fin j ↪ Fin n`, `s ∉ range f` to `g : Fin (j+1) ↪ Fin n`!
      simp_rw [Finset.mul_sum]
      let pairs := ((Finset.univ : Finset (Fin j → Fin n)).filter Function.Injective).biUnion
        (fun f => (Finset.univ \ Finset.univ.image f).image (fun s => (f, s)))
      have hsum_pairs :
          (∑ f ∈ (Finset.univ : Finset (Fin j → Fin n)).filter Function.Injective,
            ∑ s ∈ Finset.univ \ Finset.univ.image f,
              (∏ i : Fin j, if (f i).val = i.val then (1 : ℝ) else t) *
                ((if s.val = j then (1 : ℝ) else t) *
                  ampStep n k t (n - (j + 1)) (insert s (Finset.univ.image f)))) =
          ∑ p ∈ pairs,
            (∏ i : Fin j, if (p.1 i).val = i.val then (1 : ℝ) else t) *
              ((if p.2.val = j then (1 : ℝ) else t) *
                ampStep n k t (n - (j + 1)) (insert p.2 (Finset.univ.image p.1))) := by
        rw [Finset.sum_biUnion]
        · refine Finset.sum_congr rfl fun f _ => ?_
          rw [Finset.sum_image]
          intro s1 _ s2 _ h; exact (Prod.mk.inj h).2
        · intro f1 _ f2 _ hne
          dsimp only [Function.onFun]
          rw [Finset.disjoint_left]; intro p hp1 hp2
          obtain ⟨s1, _, rfl⟩ := Finset.mem_image.mp hp1
          obtain ⟨s2, _, h2⟩ := Finset.mem_image.mp hp2
          exact hne (Prod.mk.inj h2).1.symm
      rw [hsum_pairs]
      refine Finset.sum_bij (fun p _ => Fin.snoc p.1 p.2) ?_ ?_ ?_ ?_
      · intro p hp
        obtain ⟨f, hf, hp'⟩ := Finset.mem_biUnion.mp hp
        obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hp'
        have hinj := (Finset.mem_filter.mp hf).2
        have hsnot : s ∉ Finset.univ.image f := (Finset.mem_sdiff.mp hs).2
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        intro a b
        refine Fin.lastCases ?_ (fun a' => ?_) a <;> refine Fin.lastCases ?_ (fun b' => ?_) b
        · intro _; rfl
        · intro hab'
          simp only [Fin.snoc_last, Fin.snoc_castSucc] at hab'
          exact absurd (Finset.mem_image.mpr ⟨b', Finset.mem_univ _, hab'.symm⟩) hsnot
        · intro hab'
          simp only [Fin.snoc_last, Fin.snoc_castSucc] at hab'
          exact absurd (Finset.mem_image.mpr ⟨a', Finset.mem_univ _, hab'⟩) hsnot
        · intro hab'
          simp only [Fin.snoc_castSucc] at hab'
          exact congrArg Fin.castSucc (hinj hab')
      · intro p1 _ p2 _ heq
        apply Prod.ext
        · funext i
          have := congrFun heq i.castSucc
          simpa [Fin.snoc_castSucc] using this
        · have := congrFun heq (Fin.last j)
          simpa [Fin.snoc_last] using this
      · intro g hg
        have hinj := (Finset.mem_filter.mp hg).2
        let f : Fin j → Fin n := fun i => g i.castSucc
        let s : Fin n := g (Fin.last j)
        refine ⟨(f, s), ?_, ?_⟩
        · refine Finset.mem_biUnion.mpr ⟨f, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            fun a b h => Fin.castSucc_injective j (hinj h)⟩, ?_⟩
          refine Finset.mem_image.mpr ⟨s, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
          intro him
          obtain ⟨a, _, ha⟩ := Finset.mem_image.mp him
          have := hinj ha
          exact Fin.castSucc_ne_last a this
        · ext i
          refine Fin.lastCases ?_ (fun i' => ?_) i
          · simp [Fin.snoc_last, s]
          · simp [Fin.snoc_castSucc, f]
      · intro p _
        have hprod : (∏ i : Fin (j + 1), if (Fin.snoc (α := fun _ => Fin n) p.1 p.2 i).val = i.val then (1 : ℝ) else t) =
            (∏ i : Fin j, if (p.1 i).val = i.val then (1 : ℝ) else t) *
              (if p.2.val = j then (1 : ℝ) else t) := by
          rw [Fin.prod_univ_castSucc]
          simp only [Fin.snoc_castSucc, Fin.val_castSucc, Fin.snoc_last, Fin.val_last]
        have him : Finset.univ.image (Fin.snoc (α := fun _ => Fin n) p.1 p.2) = insert p.2 (Finset.univ.image p.1) := by
          ext x
          simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert]
          constructor
          · rintro ⟨i, rfl⟩
            refine Fin.lastCases ?_ (fun i' => ?_) i
            · exact Or.inl (by simp [Fin.snoc_last])
            · exact Or.inr ⟨i', by simp [Fin.snoc_castSucc]⟩
          · rintro (rfl | ⟨i', rfl⟩)
            · exact ⟨Fin.last j, by simp [Fin.snoc_last]⟩
            · exact ⟨i'.castSucc, by simp [Fin.snoc_castSucc]⟩
        rw [hprod, him, mul_assoc]

/-- Number of injective functions `f : Fin k → Fin n` that fix a given subset `T ⊆ Fin k`
and satisfy `(image f) ∩ tailSeats n k = B` (where `B ⊆ tailSeats n k` has size `m ≤ k - |T|`):
equals `C(k - |T|, m) * (k - |T|)!`! -/
private lemma card_inj_fixing_with_tail (n k : ℕ) (hkn : k ≤ n) (T : Finset (Fin k))
    (B : Finset (Fin n)) (hBsub : B ⊆ tailSeats n k) (hm : B.card ≤ k - T.card) :
    ((Finset.univ : Finset (Fin k → Fin n)).filter (fun f =>
        Function.Injective f ∧
        (∀ i ∈ T, (f i).val = i.val) ∧
        Finset.univ.image f ∩ tailSeats n k = B)).card =
      Nat.choose (k - T.card) B.card * Nat.factorial (k - T.card) := by
  let S_dom : Finset (Fin k) := Finset.univ \ T
  let S_low : Finset (Fin n) :=
    (Finset.univ.filter (fun s : Fin n => s.val < k)) \
      (T.image (fun i : Fin k => (⟨i.val, lt_of_lt_of_le i.isLt hkn⟩ : Fin n)))
  have hSdom_card : S_dom.card = k - T.card := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
  have hSlow_card : S_low.card = k - T.card := by
    have hlow_all : (Finset.univ.filter (fun s : Fin n => s.val < k)).card = k := by
      have heq : Finset.univ.filter (fun s : Fin n => s.val < k) =
          Finset.univ.image (fun i : Fin k => (⟨i.val, lt_of_lt_of_le i.isLt hkn⟩ : Fin n)) := by
        ext s
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
        exact ⟨fun hs => ⟨⟨s.val, hs⟩, Fin.ext rfl⟩, by rintro ⟨i, rfl⟩; exact i.isLt⟩
      rw [heq, Finset.card_image_of_injective]
      · rw [Finset.card_univ, Fintype.card_fin]
      · intro a b hab; exact Fin.ext (congrArg (fun x : Fin n => x.val) hab)
    have hTsub : T.image (fun i : Fin k => (⟨i.val, lt_of_lt_of_le i.isLt hkn⟩ : Fin n)) ⊆
        Finset.univ.filter (fun s : Fin n => s.val < k) := by
      intro s hs
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hs
      simp [i.isLt]
    have hTcard : (T.image (fun i : Fin k => (⟨i.val, lt_of_lt_of_le i.isLt hkn⟩ : Fin n))).card = T.card := by
      rw [Finset.card_image_of_injective]
      intro a b hab; exact Fin.ext (congrArg (fun x : Fin n => x.val) hab)
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hTsub, hlow_all, hTcard]
  -- Partition the set of valid `f` by `A := (image f) ∩ S_low`, which ranges over
  -- `S_low.powersetCard (k - T.card - B.card)` (count = `C(k - |T|, k - |T| - |B|) = C(k - |T|, |B|)`),
  -- and for each such `A`, `f` corresponds bijectively to `Equiv S_dom (A ∪ B)` (count = `(k - |T|)!`)!
  let Fset := (Finset.univ : Finset (Fin k → Fin n)).filter (fun f =>
      Function.Injective f ∧
      (∀ i ∈ T, (f i).val = i.val) ∧
      Finset.univ.image f ∩ tailSeats n k = B)
  have hpart : Fset.card = ∑ A ∈ S_low.powersetCard (k - T.card - B.card),
      (Fset.filter (fun f => Finset.univ.image f ∩ S_low = A)).card := by
    rw [← Finset.card_biUnion]
    · congr 1
      ext f
      simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_powersetCard]
      constructor
      · intro hf
        refine ⟨Finset.univ.image f ∩ S_low, ⟨Finset.inter_subset_right, ?_⟩, hf, rfl⟩
        rcases (Finset.mem_filter.mp hf).2 with ⟨hinj, hfix, htail⟩
        have hdisj1 : Disjoint (Finset.univ.image f ∩ S_low) B := by
          rw [Finset.disjoint_left]; intro s h1 h2
          have hs1 := (Finset.mem_sdiff.mp (Finset.mem_inter.mp h1).2).1
          have hs2 := hBsub h2
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, tailSeats] at hs1 hs2
          omega
        have hTim : T.image f = T.image (fun i : Fin k => (⟨i.val, lt_of_lt_of_le i.isLt hkn⟩ : Fin n)) := by
          ext s; simp only [Finset.mem_image]
          constructor
          · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi, Fin.ext (hfix i hi).symm⟩
          · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi, Fin.ext (hfix i hi)⟩
        have him_split : Finset.univ.image f =
            (T.image f) ∪ (Finset.univ.image f ∩ S_low) ∪ B := by
          ext s
          simp only [Finset.mem_union, Finset.mem_inter]
          constructor
          · intro hs
            by_cases hge : k ≤ s.val
            · exact Or.inr (by rw [← htail]; exact Finset.mem_inter.mpr ⟨hs, by simp [tailSeats, hge]⟩)
            · by_cases hT : s ∈ T.image f
              · exact Or.inl (Or.inl hT)
              · refine Or.inl (Or.inr ⟨hs, Finset.mem_sdiff.mpr ⟨by simp; omega, ?_⟩⟩)
                rwa [← hTim]
          · rintro ((hT | ⟨hs, _⟩) | hB)
            · exact Finset.image_subset_image (Finset.subset_univ _) hT
            · exact hs
            · rw [← htail] at hB; exact (Finset.mem_inter.mp hB).1
        have hdisj_T_low : Disjoint (T.image f) (Finset.univ.image f ∩ S_low) := by
          rw [Finset.disjoint_left]; intro s h1 h2
          have h2' := (Finset.mem_sdiff.mp (Finset.mem_inter.mp h2).2).2
          rw [← hTim] at h2'; exact h2' h1
        have hdisj_TB : Disjoint (T.image f ∪ (Finset.univ.image f ∩ S_low)) B := by
          rw [Finset.disjoint_union_left]
          refine ⟨?_, hdisj1⟩
          rw [Finset.disjoint_left]; intro s h1 h2
          rw [hTim] at h1
          obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp h1
          have ht := hBsub h2
          simp only [tailSeats, Finset.mem_filter, Finset.mem_univ, true_and] at ht
          have := i.isLt; omega
        have hcard_tot : (Finset.univ.image f).card = k := by
          rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
        have hcard_T : (T.image f).card = T.card := Finset.card_image_of_injective _ hinj
        rw [him_split, Finset.card_union_of_disjoint hdisj_TB,
          Finset.card_union_of_disjoint hdisj_T_low, hcard_T] at hcard_tot
        omega
      · rintro ⟨_, _, hf, _⟩; exact hf
    · intro A1 _ A2 _ hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]; intro f h1 h2
      exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
  rw [hpart]
  have heachA : ∀ A ∈ S_low.powersetCard (k - T.card - B.card),
      (Fset.filter (fun f => Finset.univ.image f ∩ S_low = A)).card = Nat.factorial (k - T.card) := by
    intro A hA
    rcases Finset.mem_powersetCard.mp hA with ⟨hAsub, hAcard⟩
    have hdisjAB : Disjoint A B := by
      rw [Finset.disjoint_left]; intro s h1 h2
      have hs1 := (Finset.mem_sdiff.mp (hAsub h1)).1
      have hs2 := hBsub h2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, tailSeats] at hs1 hs2
      omega
    have hAB_card : (A ∪ B).card = k - T.card := by
      rw [Finset.card_union_of_disjoint hdisjAB, hAcard]; omega
    -- Biject `Fset.filter (... = A)` with `Equiv S_dom (A ∪ B)`!
    have hcard_equiv : Fintype.card (↥S_dom ≃ ↥(A ∪ B)) = Nat.factorial (k - T.card) := by
      rw [Fintype.card_congr (Equiv.equivCongr
        (Fintype.equivFinOfCardEq (n := k - T.card) (by rw [Fintype.card_coe, hSdom_card]))
        (Fintype.equivFinOfCardEq (n := k - T.card) (by rw [Fintype.card_coe, hAB_card])))]
      rw [Fintype.card_perm, Fintype.card_fin]
    rw [← hcard_equiv, ← Finset.card_univ]
    symm
    refine Finset.card_bij
      (fun (e : ↥S_dom ≃ ↥(A ∪ B)) _ =>
        fun i : Fin k =>
          if hi : i ∈ T then (⟨i.val, lt_of_lt_of_le i.isLt hkn⟩ : Fin n)
          else (e ⟨i, Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hi⟩⟩).1)
      ?_ ?_ ?_
    · intro e _
      set f : Fin k → Fin n := fun i =>
        if hi : i ∈ T then ⟨i.val, lt_of_lt_of_le i.isLt hkn⟩
        else (e ⟨i, Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hi⟩⟩).1
      have hT_disj_AB : ∀ i ∈ T, ∀ y ∈ A ∪ B, (⟨i.val, lt_of_lt_of_le i.isLt hkn⟩ : Fin n) ≠ y := by
        intro i hi y hy heq
        rcases Finset.mem_union.mp hy with hyA | hyB
        · have hnotT := (Finset.mem_sdiff.mp (hAsub hyA)).2
          exact hnotT (Finset.mem_image.mpr ⟨i, hi, heq⟩)
        · have ht := hBsub hyB
          simp only [tailSeats, Finset.mem_filter, Finset.mem_univ, true_and] at ht
          have hval : i.val = y.val := congrArg (fun z : Fin n => z.val) heq
          have := i.isLt; omega
      have hinj : Function.Injective f := by
        intro a b hab
        by_cases ha : a ∈ T <;> by_cases hb : b ∈ T
        · simp only [f, ha, hb, ↓reduceDIte] at hab
          exact Fin.ext (congrArg (fun x : Fin n => x.val) hab)
        · simp only [f, ha, hb, ↓reduceDIte] at hab
          exact absurd hab (hT_disj_AB a ha _ (e _).2)
        · simp only [f, ha, hb, ↓reduceDIte] at hab
          exact absurd hab.symm (hT_disj_AB b hb _ (e _).2)
        · simp only [f, ha, hb, ↓reduceDIte] at hab
          have := e.injective (Subtype.ext hab)
          exact congrArg Subtype.val this
      have hfix : ∀ i ∈ T, (f i).val = i.val := by
        intro i hi; simp [f, hi]
      have him_eq : Finset.univ.image f =
          (T.image (fun i : Fin k => (⟨i.val, lt_of_lt_of_le i.isLt hkn⟩ : Fin n))) ∪ (A ∪ B) := by
        ext s
        simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_union]
        constructor
        · rintro ⟨i, rfl⟩
          by_cases hi : i ∈ T
          · exact Or.inl ⟨i, hi, by simp [f, hi]⟩
          · right; simp only [f, hi, ↓reduceDIte]; exact Finset.mem_union.mp (e _).2
        · rintro (⟨i, hi, rfl⟩ | hsAB)
          · exact ⟨i, by simp [f, hi]⟩
          · let x := e.symm ⟨s, Finset.mem_union.mpr hsAB⟩
            have hxnot : x.1 ∉ T := (Finset.mem_sdiff.mp x.2).2
            refine ⟨x.1, ?_⟩
            simp only [f, hxnot, ↓reduceDIte]
            have := e.apply_symm_apply ⟨s, Finset.mem_union.mpr hsAB⟩
            exact congrArg Subtype.val this
      have htail_f : Finset.univ.image f ∩ tailSeats n k = B := by
        rw [him_eq]; ext s
        simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_image, tailSeats,
          Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨(⟨i, _, rfl⟩ | hsA | hsB), hge⟩
          · change k ≤ i.val at hge; have := i.isLt; omega
          · have := (Finset.mem_sdiff.mp (hAsub hsA)).1
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this; omega
          · exact hsB
        · intro hsB
          have ht := hBsub hsB
          simp only [tailSeats, Finset.mem_filter, Finset.mem_univ, true_and] at ht
          exact ⟨Or.inr (Or.inr hsB), ht⟩
      have hlow_f : Finset.univ.image f ∩ S_low = A := by
        rw [him_eq]; ext s
        simp only [Finset.mem_inter, Finset.mem_union]
        constructor
        · rintro ⟨hT | hsA | hsB, hsLow⟩
          · exact absurd hT (Finset.mem_sdiff.mp hsLow).2
          · exact hsA
          · have h1 := (Finset.mem_sdiff.mp hsLow).1
            have h2 := hBsub hsB
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, tailSeats] at h1 h2; omega
        · intro hsA; exact ⟨Or.inr (Or.inl hsA), hAsub hsA⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hinj, hfix, htail_f⟩, hlow_f⟩
    · intro e1 _ e2 _ heq
      apply Equiv.ext
      intro x
      apply Subtype.ext
      have hxnot : x.1 ∉ T := (Finset.mem_sdiff.mp x.2).2
      have := congrFun heq x.1
      simp only [hxnot, ↓reduceDIte] at this
      exact this
    · intro f hf
      rcases Finset.mem_filter.mp hf with ⟨hfF, hlow_f⟩
      rcases (Finset.mem_filter.mp hfF).2 with ⟨hinj, hfix, htail_f⟩
      have hmaps : ∀ x : ↥S_dom, f x.1 ∈ A ∪ B := by
        intro x
        have hxnot : x.1 ∉ T := (Finset.mem_sdiff.mp x.2).2
        by_cases hge : k ≤ (f x.1).val
        · apply Finset.mem_union_right A
          rw [← htail_f]
          exact Finset.mem_inter.mpr ⟨Finset.mem_image.mpr ⟨x.1, Finset.mem_univ _, rfl⟩,
            by simp [tailSeats, hge]⟩
        · apply Finset.mem_union_left B
          rw [← hlow_f]
          refine Finset.mem_inter.mpr ⟨Finset.mem_image.mpr ⟨x.1, Finset.mem_univ _, rfl⟩,
            Finset.mem_sdiff.mpr ⟨by simp; omega, ?_⟩⟩
          intro hT
          obtain ⟨i, hi, hfi⟩ := Finset.mem_image.mp hT
          have heq : f i = f x.1 := Fin.ext ((hfix i hi).trans (congrArg (fun z : Fin n => z.val) hfi))
          exact hxnot (hinj heq ▸ hi)
      let g : ↥S_dom → ↥(A ∪ B) := fun x => ⟨f x.1, hmaps x⟩
      have hg_inj : Function.Injective g := fun a b h =>
        Subtype.ext (hinj (congrArg Subtype.val h))
      have hcard_eq : Fintype.card ↥S_dom = Fintype.card ↥(A ∪ B) := by
        rw [Fintype.card_coe, Fintype.card_coe, hSdom_card, hAB_card]
      let e : ↥S_dom ≃ ↥(A ∪ B) := Equiv.ofBijective g ((Fintype.bijective_iff_injective_and_card g).mpr ⟨hg_inj, hcard_eq⟩)
      refine ⟨e, Finset.mem_univ _, ?_⟩
      funext i
      by_cases hi : i ∈ T
      · simp only [hi, ↓reduceDIte]
        exact Fin.ext (hfix i hi).symm
      · simp only [hi, ↓reduceDIte]; rfl
  rw [Finset.sum_congr rfl heachA, Finset.sum_const, Finset.card_powersetCard, hSlow_card,
    Nat.choose_symm hm, smul_eq_mul]

/-- Final main theorem proof. -/
theorem ampPGF_closed_form (n k : ℕ) (t : ℝ) (hkn : k ≤ n) :
    ampPGF n k t =
      ((Nat.factorial k : ℝ) / (Nat.factorial n : ℝ)) *
        ∑ s ∈ Finset.range (k + 1),
          ((1 - t) ^ s * t ^ (k - s) / (Nat.factorial s : ℝ)) *
            ∏ j ∈ Finset.Icc 1 (n - k), ((j : ℝ) + ((k - s : ℕ) : ℝ) * t) := by
  unfold ampPGF
  rw [ampStep_unroll_absent n k t k (le_rfl) hkn]
  -- Expand `∏ i, (if (f i).val = i.val then 1 else t)` via `Finset.prod_add`!
  have hprod_ie : ∀ f : Fin k → Fin n,
      (∏ i : Fin k, if (f i).val = i.val then (1 : ℝ) else t) =
        ∑ T ∈ (Finset.univ : Finset (Fin k)).powerset,
          if ∀ i ∈ T, (f i).val = i.val then (1 - t) ^ T.card * t ^ (k - T.card) else 0 := by
    intro f
    have hrewrite : (∏ i : Fin k, if (f i).val = i.val then (1 : ℝ) else t) =
        ∏ i : Fin k, ((if (f i).val = i.val then (1 - t) else 0) + t) := by
      refine Finset.prod_congr rfl fun i _ => ?_
      split_ifs <;> ring
    rw [hrewrite, Finset.prod_add]
    refine Finset.sum_congr rfl fun T hT => ?_
    have hTsub : T ⊆ Finset.univ := Finset.mem_powerset.mp hT
    have hc : (Finset.univ \ T).card = k - T.card := by
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
    rw [Finset.prod_const, hc]
    by_cases hall : ∀ i ∈ T, (f i).val = i.val
    · rw [if_pos hall]
      have : (∏ i ∈ T, if (f i).val = i.val then 1 - t else 0) = (1 - t) ^ T.card := by
        rw [Finset.prod_congr rfl fun i hi => by rw [if_pos (hall i hi)], Finset.prod_const]
      rw [this]
    · rw [if_neg hall]
      push Not at hall
      obtain ⟨i0, hi0, hne⟩ := hall
      have : (∏ i ∈ T, if (f i).val = i.val then 1 - t else 0) = 0 :=
        Finset.prod_eq_zero hi0 (if_neg hne)
      rw [this, zero_mul]
  -- Replace `ampStep` by `ampTail` and swap sums!
  have hterm : ∀ f ∈ (Finset.univ : Finset (Fin k → Fin n)).filter Function.Injective,
      (∏ i : Fin k, if (f i).val = i.val then (1 : ℝ) else t) *
        ampStep n k t (n - k) (Finset.univ.image f) =
      ∑ T ∈ (Finset.univ : Finset (Fin k)).powerset,
        if ∀ i ∈ T, (f i).val = i.val then
          ((1 - t) ^ T.card * t ^ (k - T.card)) *
            ampTail n k t (n - k) (Finset.univ.image f ∩ tailSeats n k)
        else 0 := by
    intro f hf
    have hinj := (Finset.mem_filter.mp hf).2
    have hcard_im : (Finset.univ.image f).card = n - (n - k) := by
      rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]; omega
    rw [ampStep_eq_ampTail (Nat.sub_le n k) (by omega) hcard_im, hprod_ie f, Finset.sum_mul]
    refine Finset.sum_congr rfl fun T _ => ?_
    split_ifs <;> simp [show n - (n - k) = k by omega]
  rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
  -- Evaluate the inner sum for each fixed `T ⊆ Fin k`!
  have hinner : ∀ T ∈ (Finset.univ : Finset (Fin k)).powerset,
      (∑ f ∈ (Finset.univ : Finset (Fin k → Fin n)).filter Function.Injective,
        if ∀ i ∈ T, (f i).val = i.val then
          ((1 - t) ^ T.card * t ^ (k - T.card)) *
            ampTail n k t (n - k) (Finset.univ.image f ∩ tailSeats n k)
        else 0) =
      ((1 - t) ^ T.card * t ^ (k - T.card)) *
        ((Nat.factorial (k - T.card) : ℝ) * risingP (k - T.card) (n - k) t) := by
    intro T _
    rw [← Finset.sum_filter, ← Finset.mul_sum]
    congr 1
    -- Group `f` by `B = Finset.univ.image f ∩ tailSeats n k` (which has size `m ≤ k - T.card`)
    have hgroup :
        (∑ f ∈ ((Finset.univ : Finset (Fin k → Fin n)).filter Function.Injective).filter
            (fun f => ∀ i ∈ T, (f i).val = i.val),
          ampTail n k t (n - k) (Finset.univ.image f ∩ tailSeats n k)) =
        ∑ m ∈ Finset.range (k - T.card + 1),
          ∑ B ∈ (tailSeats n k).powersetCard m,
            ((Nat.choose (k - T.card) m * Nat.factorial (k - T.card) : ℕ) : ℝ) *
              ampTail n k t (n - k) B := by
      let F_T := ((Finset.univ : Finset (Fin k → Fin n)).filter Function.Injective).filter
        (fun f => ∀ i ∈ T, (f i).val = i.val)
      have hcard_le : ∀ f ∈ F_T, (Finset.univ.image f ∩ tailSeats n k).card ≤ k - T.card := by
        intro f hf
        rcases Finset.mem_filter.mp hf with ⟨hf1, hfix⟩
        have hinj := (Finset.mem_filter.mp hf1).2
        have hsub : Finset.univ.image f ∩ tailSeats n k ⊆ (Finset.univ \ T).image f := by
          intro s hs
          rcases Finset.mem_inter.mp hs with ⟨him, ht⟩
          obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp him
          refine Finset.mem_image.mpr ⟨i, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
          intro hiT
          have h1 := hfix i hiT
          simp only [tailSeats, Finset.mem_filter, Finset.mem_univ, true_and] at ht
          have := i.isLt; omega
        calc (Finset.univ.image f ∩ tailSeats n k).card
            ≤ ((Finset.univ \ T).image f).card := Finset.card_le_card hsub
          _ = (Finset.univ \ T).card := Finset.card_image_of_injective _ hinj
          _ = k - T.card := by rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
      -- Fiber sum over `B ∈ (tailSeats n k).powerset` with `B.card ≤ k - T.card`
      have hfiber :
          (∑ f ∈ F_T, ampTail n k t (n - k) (Finset.univ.image f ∩ tailSeats n k)) =
          ∑ m ∈ Finset.range (k - T.card + 1),
            ∑ B ∈ (tailSeats n k).powersetCard m,
              ∑ f ∈ F_T.filter (fun f => Finset.univ.image f ∩ tailSeats n k = B),
                ampTail n k t (n - k) B := by
        have hunion : F_T = (Finset.range (k - T.card + 1)).biUnion fun m =>
            ((tailSeats n k).powersetCard m).biUnion fun B =>
              F_T.filter (fun f => Finset.univ.image f ∩ tailSeats n k = B) := by
          ext f
          simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_powersetCard, Finset.mem_filter]
          constructor
          · intro hf
            exact ⟨(Finset.univ.image f ∩ tailSeats n k).card,
              Nat.lt_succ_of_le (hcard_le f hf),
              Finset.univ.image f ∩ tailSeats n k,
              ⟨Finset.inter_subset_right, rfl⟩, hf, rfl⟩
          · rintro ⟨_, _, _, _, hf, _⟩; exact hf
        conv_lhs => rw [hunion]
        rw [Finset.sum_biUnion]
        · refine Finset.sum_congr rfl fun m _ => ?_
          rw [Finset.sum_biUnion]
          · refine Finset.sum_congr rfl fun B _ => ?_
            refine Finset.sum_congr rfl fun f hf => by rw [(Finset.mem_filter.mp hf).2]
          · intro B1 _ B2 _ hne
            dsimp only [Function.onFun]
            rw [Finset.disjoint_left]; intro f h1 h2
            exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
        · intro m1 _ m2 _ hne
          dsimp only [Function.onFun]
          rw [Finset.disjoint_left]; intro f h1 h2
          obtain ⟨B1, hB1, hf1⟩ := Finset.mem_biUnion.mp h1
          obtain ⟨B2, hB2, hf2⟩ := Finset.mem_biUnion.mp h2
          have hBeq : B1 = B2 := (Finset.mem_filter.mp hf1).2.symm.trans (Finset.mem_filter.mp hf2).2
          have := (Finset.mem_powersetCard.mp hB1).2
          have := (Finset.mem_powersetCard.mp hB2).2
          subst hBeq; exact hne (by omega)
      rw [hfiber]
      refine Finset.sum_congr rfl fun m hm => Finset.sum_congr rfl fun B hB => ?_
      rw [Finset.mem_range] at hm
      rcases Finset.mem_powersetCard.mp hB with ⟨hBsub, hBcard⟩
      rw [Finset.sum_const, nsmul_eq_mul]
      congr 1
      have hfeq : F_T.filter (fun f => Finset.univ.image f ∩ tailSeats n k = B) =
          (Finset.univ : Finset (Fin k → Fin n)).filter (fun f =>
            Function.Injective f ∧ (∀ i ∈ T, (f i).val = i.val) ∧
            Finset.univ.image f ∩ tailSeats n k = B) := by
        ext f; simp only [F_T, Finset.mem_filter, Finset.mem_univ, true_and]; tauto
      rw [hfeq, card_inj_fixing_with_tail n k hkn T B hBsub (by omega), hBcard]
    rw [hgroup]
    have hsum_m :
        (∑ m ∈ Finset.range (k - T.card + 1),
          ∑ B ∈ (tailSeats n k).powersetCard m,
            ((Nat.choose (k - T.card) m * Nat.factorial (k - T.card) : ℕ) : ℝ) *
              ampTail n k t (n - k) B) =
        (Nat.factorial (k - T.card) : ℝ) *
          ∑ m ∈ Finset.range (k - T.card + 1),
            (Nat.choose (k - T.card) m : ℝ) * sumS (n - k) m t := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun m hm => ?_
      rw [Finset.mem_range] at hm
      rw [← Finset.mul_sum, Nat.cast_mul]
      have hs := sum_ampTail_eq_sumS n k t (n - k) (Nat.sub_le n k) (by omega) m (by omega)
      rw [show n - (n - k) = k by omega] at hs
      rw [hs]; ring
    rw [hsum_m, binomial_inversion_sumS]
  rw [Finset.sum_congr rfl hinner]
  -- Group `T ∈ powerset univ` by `s = T.card ∈ range (k + 1)`!
  have hgroupT :
      (∑ T ∈ (Finset.univ : Finset (Fin k)).powerset,
        ((1 - t) ^ T.card * t ^ (k - T.card)) *
          ((Nat.factorial (k - T.card) : ℝ) * risingP (k - T.card) (n - k) t)) =
      ∑ s ∈ Finset.range (k + 1),
        (Nat.choose k s : ℝ) *
          (((1 - t) ^ s * t ^ (k - s)) *
            ((Nat.factorial (k - s) : ℝ) * risingP (k - s) (n - k) t)) := by
    have hpu : (Finset.univ : Finset (Fin k)).powerset =
        (Finset.range (k + 1)).biUnion (fun s => (Finset.univ : Finset (Fin k)).powersetCard s) := by
      ext T
      simp only [Finset.mem_powerset, Finset.subset_univ, true_iff, Finset.mem_biUnion,
        Finset.mem_range, Finset.mem_powersetCard, true_and]
      exact ⟨T.card, Nat.lt_succ_of_le (by simpa using Finset.card_le_univ T), rfl⟩
    rw [hpu, Finset.sum_biUnion]
    · refine Finset.sum_congr rfl fun s _ => ?_
      have hconst : ∀ T ∈ (Finset.univ : Finset (Fin k)).powersetCard s,
          ((1 - t) ^ T.card * t ^ (k - T.card)) *
            ((Nat.factorial (k - T.card) : ℝ) * risingP (k - T.card) (n - k) t) =
          ((1 - t) ^ s * t ^ (k - s)) *
            ((Nat.factorial (k - s) : ℝ) * risingP (k - s) (n - k) t) := by
        intro T hT; rw [(Finset.mem_powersetCard.mp hT).2]
      rw [Finset.sum_congr rfl hconst, Finset.sum_const, Finset.card_powersetCard,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    · intro s1 _ s2 _ hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]; intro T h1 h2
      exact hne ((Finset.mem_powersetCard.mp h1).2.symm.trans (Finset.mem_powersetCard.mp h2).2)
  rw [hgroupT, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [Finset.mem_range] at hs
  rw [risingP_eq_div_factorial]
  have hch : (Nat.choose k s : ℝ) * (Nat.factorial s : ℝ) * (Nat.factorial (k - s) : ℝ) =
      (Nat.factorial k : ℝ) := by
    have := Nat.choose_mul_factorial_mul_factorial (show s ≤ k by omega)
    exact_mod_cast this
  have hs_ne : (Nat.factorial s : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero s)
  have hnk_ne : (Nat.factorial (n - k) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hn_ne : (Nat.factorial n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  field_simp [hs_ne, hnk_ne, hn_ne]
  rw [← hch]; ring

end OMA.P_arxiv_2001_06839

theorem OMA.solution : type_of% @OMA.S_arxiv_2001_06839.main := by
  intro n k t hkn
  exact OMA.P_arxiv_2001_06839.ampPGF_closed_form n k t hkn
