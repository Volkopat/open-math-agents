import OMAStatements.S_mo_171692

namespace OMA.S_mo_171692

lemma kl_nonneg {n : ℕ} (P Q : Fin n → ℝ) (hP : Dist P) (hQ : Dist Q) : 0 ≤ kl P Q := by
  have hterm (i : Fin n) : P i - Q i ≤ P i * Real.log (P i/Q i) := by
    have hp := hP.1 i
    have hq := hQ.1 i
    have hg := Real.log_le_sub_one_of_pos (div_pos hq hp)
    rw [Real.log_div hq.ne' hp.ne'] at hg
    rw [Real.log_div hp.ne' hq.ne']
    have hm := mul_le_mul_of_nonneg_right hg hp.le
    rw [sub_mul,sub_mul,div_mul_cancel₀ _ hp.ne',one_mul] at hm
    linarith
  have h := Finset.sum_le_sum (s := Finset.univ) fun i _ ↦ hterm i
  simpa [Finset.sum_sub_distrib,hP.2.1,hQ.2.1,kl] using h

lemma kl_chain {n : ℕ} (P Q R : Fin n → ℝ) (hP : Dist P) (hQ : Dist Q) (hR : Dist R) :
    kl P R - kl P Q - kl Q R = ∑ i, (P i-Q i)*Real.log (Q i/R i) := by
  simp only [kl,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [Real.log_div (hP.1 i).ne' (hR.1 i).ne',Real.log_div (hP.1 i).ne' (hQ.1 i).ne',
    Real.log_div (hQ.1 i).ne' (hR.1 i).ne']
  ring

end OMA.S_mo_171692

namespace OMA.S_mo_171692

open Finset

lemma weighted_mono {n : ℕ} (P Q w : Fin n → ℝ) (hm : Majorizes P Q) (hw : Antitone w) :
    (∑ i, Q i*w i) ≤ ∑ i,P i*w i := by
  let ext (f : Fin n → ℝ) (i : ℕ) := if h : i < n then f ⟨i,h⟩ else 0
  have bridge (f : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) :
      (∑ i : Fin n, if i.val < k then f i else 0) = ∑ i ∈ range k, ext f i := by
    rw [sum_fin_eq_sum_range]
    calc
      _ = ∑ i ∈ range n, if i ∈ range k then ext f i else 0 := by
        apply sum_congr rfl
        intro i hi
        simp [ext,mem_range.mp hi]
      _ = _ := by
        rw [← Finset.sum_filter]
        congr 1
        ext i
        simp only [mem_filter,mem_range]
        omega
  have pref (k : ℕ) (hk : k ≤ n) : (∑ i ∈ range k,ext Q i) ≤ ∑ i ∈ range k,ext P i := by
    rw [← bridge Q k hk,← bridge P k hk]
    exact hm.2 k
  have tot : (∑ i ∈ range n,ext P i) = ∑ i ∈ range n,ext Q i := by
    simpa only [sum_fin_eq_sum_range,ext] using hm.1
  have calcSum (f : Fin n → ℝ) : (∑ i, f i*w i) =
      ext w (n-1) * (∑ i ∈ range n,ext f i) -
      ∑ i ∈ range (n-1), (ext w (i+1)-ext w i)*(∑ j ∈ range (i+1),ext f j) := by
    have hb := Finset.sum_range_by_parts (ext w) (ext f) n
    simp only [smul_eq_mul] at hb
    rw [← hb]
    rw [sum_fin_eq_sum_range]
    apply sum_congr rfl
    intro i hi
    simp [ext,mem_range.mp hi,mul_comm]
  rw [calcSum Q,calcSum P,tot]
  apply sub_le_sub_left
  apply sum_le_sum
  intro i hi
  have hi' := mem_range.mp hi
  have hs : i+1 < n := by omega
  have hd : ext w (i+1)-ext w i ≤ 0 := by
    simpa [ext,hs,show i<n by omega] using (sub_nonpos.mpr (hw (show (⟨i,by omega⟩ : Fin n) ≤ ⟨i+1,hs⟩ by exact Nat.le_succ i)))
  exact mul_le_mul_of_nonpos_left (pref (i+1) hs.le) hd

end OMA.S_mo_171692

namespace OMA.S_mo_171692

lemma joint_failure : ∃ P Q R : Fin 3 → ℝ, Dist P ∧ Dist Q ∧ Dist R ∧
    Majorizes P Q ∧ Majorizes Q R ∧ kl P R < kl P Q ∧ kl R P < kl Q P := by
  let P : Fin 3 → ℝ := ![3/5,1/5,1/5]
  let Q : Fin 3 → ℝ := ![2/5,2/5,1/5]
  let R : Fin 3 → ℝ := ![2/5,3/10,3/10]
  refine ⟨P,Q,R,?_,?_,?_,?_,?_,?_,?_⟩
  · refine ⟨?_,by norm_num [P,Fin.sum_univ_succ],?_⟩
    · intro i;fin_cases i <;> norm_num [P]
    · intro i j h;fin_cases i <;> fin_cases j <;> norm_num [P] at *
  · refine ⟨?_,by norm_num [Q,Fin.sum_univ_succ],?_⟩
    · intro i;fin_cases i <;> norm_num [Q]
    · intro i j h;fin_cases i <;> fin_cases j <;> norm_num [Q] at *
      exact (by decide : ¬ (2 : Fin 3) ≤ 1) h
  · refine ⟨?_,by norm_num [R,Fin.sum_univ_succ],?_⟩
    · intro i;fin_cases i <;> norm_num [R]
    · intro i j h;fin_cases i <;> fin_cases j <;> norm_num [R] at *
  · refine ⟨by norm_num [P,Q,Fin.sum_univ_succ],fun k => ?_⟩
    by_cases h : k≤3
    · interval_cases k <;> norm_num [P,Q,Fin.sum_univ_succ]
    · have h' (i : Fin 3) : i.val<k := by omega
      simp only [if_pos (h' _)];norm_num [P,Q,Fin.sum_univ_succ]
  · refine ⟨by norm_num [R,Q,Fin.sum_univ_succ],fun k => ?_⟩
    by_cases h : k≤3
    · interval_cases k <;> norm_num [R,Q,Fin.sum_univ_succ]
    · have h' (i : Fin 3) : i.val<k := by omega
      simp only [if_pos (h' _)];norm_num [R,Q,Fin.sum_univ_succ]
  · have h := Real.log_lt_log (by norm_num) (by norm_num : (2/3:ℝ)^2 < 1/2)
    rw [Real.log_pow] at h
    norm_num [kl,P,Q,R,Fin.sum_univ_succ] at h ⊢
    linarith
  · have h := Real.log_lt_log (by norm_num) (by norm_num : (3/2:ℝ)^3 < (2:ℝ)^2)
    rw [Real.log_pow,Real.log_pow] at h
    norm_num [kl,P,Q,R,Fin.sum_univ_succ] at h ⊢
    linarith

end OMA.S_mo_171692

open OMA.S_mo_171692

namespace OMA.S_mo_171692

lemma comparisons {n} (P Q R : Fin n → ℝ) (hP : Dist P) (hQ : Dist Q) (hR : Dist R)
    (hpq : Majorizes P Q) (hqr : Majorizes Q R) :
    (Antitone (fun i => Q i/R i) → kl P Q ≤ kl P R) ∧
    (Antitone (fun i => P i/Q i) → kl Q P ≤ kl R P) := by
  constructor
  · intro h
    have ht : Antitone (fun i => Real.log (Q i/R i)) := fun i j hij =>
      Real.log_le_log (div_pos (hQ.1 j) (hR.1 j)) (h hij)
    have hw := weighted_mono P Q _ hpq ht
    have he := kl_chain P Q R hP hQ hR
    simp only [sub_mul,Finset.sum_sub_distrib] at he
    linarith [kl_nonneg Q R hQ hR]
  · intro h
    have ht : Antitone (fun i => Real.log (P i/Q i)) := fun i j hij =>
      Real.log_le_log (div_pos (hP.1 j) (hQ.1 j)) (h hij)
    have hw := weighted_mono Q R _ hqr ht
    have he := kl_chain R Q P hR hQ hP
    have hlog i : Real.log (Q i / P i) = -Real.log (P i/Q i) := by
      rw [Real.log_div (hQ.1 i).ne' (hP.1 i).ne',Real.log_div (hP.1 i).ne' (hQ.1 i).ne']
      ring
    simp only [hlog,sub_mul,mul_neg,Finset.sum_sub_distrib,Finset.sum_neg_distrib] at he
    linarith [kl_nonneg R Q hR hQ]

lemma binary_ratio (P Q : Fin 2 → ℝ) (_hP : Dist P) (hQ : Dist Q) (h : Majorizes P Q) :
    Antitone (fun i => P i / Q i) := by
  have h0 := h.2 1
  simp at h0
  have hsum := h.1
  rw [Fin.sum_univ_two,Fin.sum_univ_two] at hsum
  have h1 : P 1 ≤ Q 1 := by linarith
  intro i j hij
  rcases lt_or_eq_of_le hij with hij | rfl
  · have hi : i=0 := by omega
    have hj : j=1 := by omega
    subst i
    subst j
    exact ((div_le_one (hQ.1 1)).mpr h1).trans ((one_le_div (hQ.1 0)).mpr h0)
  · exact le_rfl

end OMA.S_mo_171692

theorem OMA.solution : type_of% @OMA.S_mo_171692.main := by
  refine ⟨joint_failure,?_,fun P Q R => comparisons P Q R⟩
  intro P Q R hP hQ hR hpq hqr
  obtain ⟨f,g⟩ := comparisons P Q R hP hQ hR hpq hqr
  exact ⟨f (binary_ratio Q R hQ hR hqr),g (binary_ratio P Q hP hQ hpq)⟩
