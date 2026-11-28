import OMAStatements.S_mo_124716
import Mathlib

open scoped BigOperators
open Matrix Filter Topology

namespace OMA.Helpers

/-- Shifted matrix `z I - A` for the Metzler eigenvalue argument. -/
noncomputable def mo124716B {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (z : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  diagonal (fun _ => z) - A

/-- Unit vector at `i0`. -/
noncomputable def mo124716E {n : ℕ} (i0 : Fin n) : Fin n → ℝ :=
  fun j => if j = i0 then 1 else 0

/-- The solution of `(z I - A) x = e` via Cramer's rule. -/
noncomputable def mo124716X {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (i0 : Fin n) (z : ℝ) :
    Fin n → ℝ :=
  ((mo124716B A z).det)⁻¹ • cramer (mo124716B A z) (mo124716E i0)

lemma mo124716_row {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (i0 : Fin n) (z : ℝ)
    (hz : (mo124716B A z).det ≠ 0) (i : Fin n) :
    z * mo124716X A i0 z i - ∑ l, A i l * mo124716X A i0 z l = mo124716E i0 i := by
  have h1 : mo124716B A z *ᵥ mo124716X A i0 z = mo124716E i0 := by
    unfold mo124716X
    rw [mulVec_smul, mulVec_cramer, smul_smul, inv_mul_cancel₀ hz, one_smul]
  have h2 := congrFun h1 i
  rw [← h2]
  simp only [mo124716B, mulVec, dotProduct, Matrix.sub_apply, diagonal_apply, sub_mul,
    Finset.sum_sub_distrib, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

lemma mo124716_cont {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (i0 : Fin n) (z : ℝ)
    (hz : (mo124716B A z).det ≠ 0) (j : Fin n) :
    ContinuousAt (fun w => mo124716X A i0 w j) z := by
  have hB : Continuous (fun w => mo124716B A w) := by
    unfold mo124716B
    exact (Continuous.matrix_diagonal (continuous_pi fun _ => continuous_id)).sub
      continuous_const
  have hd : Continuous (fun w => (mo124716B A w).det) := hB.matrix_det
  have hc : Continuous (fun w => cramer (mo124716B A w) (mo124716E i0) j) :=
    (continuous_apply j).comp (hB.matrix_cramer continuous_const)
  unfold mo124716X
  simp only [Pi.smul_apply, smul_eq_mul]
  exact (hd.continuousAt.inv₀ hz).mul hc.continuousAt

theorem mo124716_core {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (i0 : Fin n)
    (hoff : ∀ i j, i ≠ j → 0 ≤ A i j) (hM : 0 < A i0 i0)
    (hirr : ∀ S : Set (Fin n), (∀ j l, j ∈ S → j ≠ l → 0 < A j l → l ∈ S) →
      ∀ j ∈ S, i0 ∈ S) :
    ∃ z : ℝ, 0 < z ∧ (mo124716B A z).det = 0 := by
  by_contra hcon
  push Not at hcon
  set M := A i0 i0 with hMdef
  set x := mo124716X A i0 with hxdef
  have hrow : ∀ z, 0 < z → ∀ i, z * x z i - ∑ l, A i l * x z l = mo124716E i0 i :=
    fun z hz i => mo124716_row A i0 z (hcon z hz) i
  have hcont : ∀ z, 0 < z → ∀ j, ContinuousAt (fun w => x w j) z :=
    fun z hz j => mo124716_cont A i0 z (hcon z hz) j
  have he0 : ∀ i, 0 ≤ mo124716E i0 i := by
    intro i; unfold mo124716E; split_ifs <;> norm_num
  -- off-diagonal sum is nonnegative when x is nonnegative off the diagonal
  set Z : ℝ := ∑ i, ∑ l, |A i l| + 1 with hZ
  have hbig : ∀ z, Z ≤ z → ∀ j, 0 ≤ x z j := by
    intro z hz
    have hzpos : 0 < z := by
      have : 0 ≤ ∑ i, ∑ l, |A i l| :=
        Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun l _ => abs_nonneg _
      linarith
    obtain ⟨i, -, hi⟩ := Finset.exists_min_image Finset.univ (x z) ⟨i0, Finset.mem_univ _⟩
    by_contra hneg
    push Not at hneg
    obtain ⟨j, hj⟩ := hneg
    have hxi : x z i < 0 := lt_of_le_of_lt (hi j (Finset.mem_univ _)) hj
    have hsum : (∑ l, A i l) * x z i ≤ ∑ l, A i l * x z l := by
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro l _
      by_cases hl : i = l
      · subst hl; exact le_refl _
      · exact mul_le_mul_of_nonneg_left (hi l (Finset.mem_univ _)) (hoff i l hl)
    have hrs : ∑ l, A i l < z := by
      have h1 : ∑ l, A i l ≤ ∑ l, |A i l| :=
        Finset.sum_le_sum fun l _ => le_abs_self _
      have h2 : ∑ l, |A i l| ≤ ∑ i', ∑ l, |A i' l| :=
        Finset.single_le_sum (f := fun i' => ∑ l, |A i' l|)
          (fun i' _ => Finset.sum_nonneg fun l _ => abs_nonneg _) (Finset.mem_univ i)
      linarith
    have hr := hrow z hzpos i
    have := he0 i
    nlinarith
  have hMneg : ∃ j, x M j < 0 := by
    by_contra hnn
    push Not at hnn
    have hr := hrow M hM i0
    have hsum : M * x M i0 ≤ ∑ l, A i0 l * x M l := by
      have : ∑ l, A i0 l * x M l = ∑ l, (if l = i0 then M * x M i0 else A i0 l * x M l) := by
        apply Finset.sum_congr rfl
        intro l _
        split_ifs with h
        · subst h; rfl
        · rfl
      rw [this, ← Finset.add_sum_erase _ _ (Finset.mem_univ i0), if_pos rfl]
      have : 0 ≤ ∑ l ∈ Finset.univ.erase i0,
          (if l = i0 then M * x M i0 else A i0 l * x M l) := by
        apply Finset.sum_nonneg
        intro l hl
        rw [if_neg (Finset.ne_of_mem_erase hl)]
        exact mul_nonneg (hoff i0 l (Ne.symm (Finset.ne_of_mem_erase hl))) (hnn l)
      linarith
    have : mo124716E i0 i0 = 1 := by simp [mo124716E]
    linarith
  set T : Set ℝ := {z | M ≤ z ∧ ∃ j, x z j < 0} with hT
  have hMT : M ∈ T := ⟨le_refl _, hMneg⟩
  have hTbdd : BddAbove T := by
    refine ⟨Z, fun z hz => ?_⟩
    by_contra hlt
    push Not at hlt
    obtain ⟨j, hj⟩ := hz.2
    have := hbig z hlt.le j
    linarith
  set s := sSup T with hs
  have hMs : M ≤ s := le_csSup hTbdd hMT
  have hspos : 0 < s := lt_of_lt_of_le hM hMs
  have hsnn : ∀ j, 0 ≤ x s j := by
    intro j
    by_contra hneg
    push Not at hneg
    have hev : ∀ᶠ w in 𝓝 s, x w j < 0 := (hcont s hspos j).eventually (gt_mem_nhds hneg)
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
    have hw : s + ε / 2 ∈ T := by
      refine ⟨by linarith, j, hball ?_⟩
      rw [Real.dist_eq]
      rw [abs_of_pos (by linarith)]
      linarith
    have := le_csSup hTbdd hw
    linarith
  have hzero : ∃ j, x s j = 0 := by
    by_contra hnz
    push Not at hnz
    have hpos : ∀ j, 0 < x s j := fun j => lt_of_le_of_ne (hsnn j) (Ne.symm (hnz j))
    have hev : ∀ᶠ w in 𝓝 s, ∀ j, 0 < x w j :=
      Filter.eventually_all.2 fun j => (hcont s hspos j).eventually (lt_mem_nhds (hpos j))
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
    obtain ⟨t, htT, hlt⟩ := exists_lt_of_lt_csSup ⟨M, hMT⟩ (by linarith : s - ε < s)
    have hts : t ≤ s := le_csSup hTbdd htT
    obtain ⟨j, hj⟩ := htT.2
    have hd : dist t s < ε := by
      rw [Real.dist_eq, abs_of_nonpos (by linarith)]
      linarith
    have := hball hd j
    linarith
  -- zero propagation
  have hnnsum : ∀ j, x s j = 0 → 0 ≤ ∑ l, A j l * x s l ∧
      ∀ l ∈ Finset.univ, 0 ≤ A j l * x s l := by
    intro j hj
    have hterm : ∀ l ∈ Finset.univ, 0 ≤ A j l * x s l := by
      intro l _
      by_cases hl : j = l
      · subst hl; rw [hj, mul_zero]
      · exact mul_nonneg (hoff j l hl) (hsnn l)
    exact ⟨Finset.sum_nonneg hterm, hterm⟩
  have hclosed : ∀ j l, j ∈ {l | x s l = 0} → j ≠ l → 0 < A j l → l ∈ {l | x s l = 0} := by
    intro j l hj hjl hA
    simp only [Set.mem_ofPred_eq] at hj ⊢
    obtain ⟨hs0, hterm⟩ := hnnsum j hj
    have hr := hrow s hspos j
    rw [hj, mul_zero, zero_sub] at hr
    have hsum0 : ∑ l, A j l * x s l = 0 := by
      have := he0 j
      linarith
    have := (Finset.sum_eq_zero_iff_of_nonneg hterm).1 hsum0 l (Finset.mem_univ _)
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · exact h
  obtain ⟨j0, hj0⟩ := hzero
  have hi0 : x s i0 = 0 := hirr {l | x s l = 0} hclosed j0 hj0
  obtain ⟨hs0, -⟩ := hnnsum i0 hi0
  have hr := hrow s hspos i0
  have : mo124716E i0 i0 = 1 := by simp [mo124716E]
  rw [hi0, mul_zero] at hr
  linarith

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_mo_124716.main := by
  intro n a P k _ ha hP _ hirr _ hk
  obtain ⟨i0, hi0⟩ := ha
  set A := Matrix.diagonal a + k • P with hA
  have hAoff : ∀ i j, i ≠ j → A i j = k * P i j := by
    intro i j hij
    simp [hA, Matrix.diagonal_apply_ne _ hij]
  have hoff : ∀ i j, i ≠ j → 0 ≤ A i j := by
    intro i j hij
    rw [hAoff i j hij]
    exact mul_nonneg hk.le (hP i j).1
  have hM : 0 < A i0 i0 := by
    simp only [hA, Matrix.add_apply, Matrix.diagonal_apply_eq, Matrix.smul_apply, smul_eq_mul]
    have := mul_nonneg hk.le (hP i0 i0).1
    linarith
  have hirrA : ∀ S : Set (Fin n), (∀ j l, j ∈ S → j ≠ l → 0 < A j l → l ∈ S) →
      ∀ j ∈ S, i0 ∈ S := by
    intro S hS j hj
    obtain ⟨m, hm⟩ := hirr j i0
    have key : ∀ m : ℕ, ∀ l, 0 < (P ^ m) j l → l ∈ S := by
      intro m
      induction m with
      | zero =>
        intro l hl
        rw [pow_zero, Matrix.one_apply] at hl
        split_ifs at hl with h
        · rw [← h]; exact hj
        · exact absurd hl (lt_irrefl _)
      | succ m ih =>
        intro l hl
        rw [pow_succ, Matrix.mul_apply] at hl
        obtain ⟨t, -, ht⟩ : ∃ t ∈ Finset.univ, 0 < (P ^ m) j t * P t l := by
          by_contra hno
          push Not at hno
          have := Finset.sum_nonpos hno
          linarith
        rcases pos_and_pos_or_neg_and_neg_of_mul_pos ht with ⟨h1, h2⟩ | ⟨_, h2⟩
        · have htS := ih t h1
          by_cases htl : t = l
          · rw [← htl]; exact htS
          · apply hS t l htS htl
            rw [hAoff t l htl]
            exact mul_pos hk h2
        · exact absurd (hP t l).1 (not_le.2 h2)
    exact key m i0 hm
  obtain ⟨z, hz, hdet⟩ := OMA.Helpers.mo124716_core A i0 hoff hM hirrA
  refine ⟨z, hz, ?_⟩
  rw [Matrix.eval_charpoly, Matrix.scalar_apply]
  exact hdet
