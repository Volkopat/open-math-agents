import OMAReductions.R_Mathoverflow339137_mathoverflow_339137_R1

-- Step Mathoverflow339137.mathoverflow_339137.R1.H1: hypothesis H1 of reduction Mathoverflow339137.mathoverflow_339137.R1
-- Credit: @qu1r0ra

open Polynomial Finset

namespace OMA.KrasnerRanulac

open OMA.R_Mathoverflow339137_mathoverflow_339137_R1 (isZeroOne_iff coeff_le_one sum_nat rev_facts)

lemma phi_coeff (N n : ℕ) :
    (∑ k ∈ range (N + 1), (X : ℝ[X]) ^ k).coeff n = 0 ∨
      (∑ k ∈ range (N + 1), (X : ℝ[X]) ^ k).coeff n = 1 := by
  rw [finsetSum_coeff]
  simp only [coeff_X_pow]
  rw [Finset.sum_ite_eq]
  split_ifs
  · right; rfl
  · left; rfl

lemma root_pow {N : ℕ} {P Q : ℝ[X]} (hPQ : P * Q = ∑ k ∈ range (N + 1), (X : ℝ[X]) ^ k)
    {z : ℂ} (hz : aeval z P = 0) : z ^ (N + 1) = 1 := by
  have hid : P * Q * (X - 1) = X ^ (N + 1) - 1 := by rw [hPQ, geom_sum_mul]
  have h := congrArg (aeval z) hid
  simp only [map_mul, map_sub, map_pow, aeval_X, map_one, hz, zero_mul] at h
  linear_combination -h

lemma sep_map {N : ℕ} {P Q : ℝ[X]} (hPQ : P * Q = ∑ k ∈ range (N + 1), (X : ℝ[X]) ^ k) :
    (P.map (algebraMap ℝ ℂ)).Separable := by
  have hid : P * Q * (X - 1) = X ^ (N + 1) - 1 := by rw [hPQ, geom_sum_mul]
  have hmap := congrArg (Polynomial.map (algebraMap ℝ ℂ)) hid
  simp only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_one] at hmap
  have hs : (X ^ (N + 1) - C (1 : ℂ)).Separable :=
    separable_X_pow_sub_C 1 (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero N)) one_ne_zero
  rw [C_1] at hs
  exact hs.of_dvd ⟨Q.map (algebraMap ℝ ℂ) * (X - 1), by rw [← mul_assoc, hmap]⟩

lemma rev_root {N : ℕ} {P Q : ℝ[X]} (hPQ : P * Q = ∑ k ∈ range (N + 1), (X : ℝ[X]) ^ k)
    {z : ℂ} (hz : aeval z P = 0) : aeval z P.reverse = 0 := by
  have h1 : z ^ (N + 1) = 1 := root_pow hPQ hz
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow (Nat.succ_ne_zero N)] at h1
    exact zero_ne_one h1
  have hn : ‖z‖ = 1 := Complex.norm_eq_one_of_pow_eq_one h1 (Nat.succ_ne_zero N)
  have hc : aeval z⁻¹ P = 0 := by
    rw [Complex.inv_eq_conj hn, aeval_conj, hz, map_zero]
  let _ : Invertible z⁻¹ := invertibleOfNonzero (inv_ne_zero hz0)
  have key := (eval₂_reverse_eq_zero_iff (algebraMap ℝ ℂ) z⁻¹ P).mpr
    (by rw [← aeval_def]; exact hc)
  rw [invOf_eq_inv, inv_inv, ← aeval_def] at key
  exact key

lemma dvd_of_roots {F G : ℂ[X]} (hF : F.Monic) (hG : G ≠ 0) (hsep : F.Separable)
    (h : ∀ z, F.eval z = 0 → G.eval z = 0) : F ∣ G := by
  have hsub : F.roots ⊆ G.roots := by
    intro z hz
    rw [mem_roots hF.ne_zero, IsRoot.def] at hz
    rw [mem_roots hG, IsRoot.def]
    exact h z hz
  have hle : F.roots ≤ G.roots := (Multiset.le_iff_subset (nodup_roots hsep)).mpr hsub
  rw [← prod_multiset_X_sub_C_of_monic_of_roots_card_eq hF IsAlgClosed.card_roots_eq_natDegree]
  exact (Multiset.prod_X_sub_C_dvd_iff_le_roots hG _).mpr hle

lemma palindrome {N : ℕ} {P Q : ℝ[X]} (hP : P.Monic) (hp0 : P.coeff 0 = 1)
    (hPQ : P * Q = ∑ k ∈ range (N + 1), (X : ℝ[X]) ^ k) : P.reverse = P := by
  obtain ⟨hRm, -, hRdeg, -⟩ := rev_facts hP hp0
  have hdvd : P.map (algebraMap ℝ ℂ) ∣ P.reverse.map (algebraMap ℝ ℂ) := by
    apply dvd_of_roots (hP.map _) (hRm.map _).ne_zero (sep_map hPQ)
    intro z hz
    rw [eval_map_algebraMap] at hz ⊢
    exact rev_root hPQ hz
  apply map_injective (algebraMap ℝ ℂ) (algebraMap ℝ ℂ).injective
  exact eq_of_monic_of_dvd_of_natDegree_le (hP.map _) (hRm.map _) hdvd
    (by rw [natDegree_map, natDegree_map, hRdeg])

lemma pq_zero {P Q : ℝ[X]} (hP : P.Monic) (hp : ∀ n, 0 ≤ P.coeff n) (hq : ∀ n, 0 ≤ Q.coeff n)
    (hR : ∀ n, (P * Q).coeff n = 0 ∨ (P * Q).coeff n = 1) (hp0 : P.coeff 0 = 1)
    (hq0 : Q.coeff 0 = 1) (hrev : P.reverse = P) :
    ∀ k, 1 ≤ k → P.coeff k * Q.coeff k = 0 := by
  intro k hk
  rcases Nat.lt_or_ge P.natDegree k with hlt | hkd
  · rw [coeff_eq_zero_of_natDegree_lt hlt, zero_mul]
  have hpal : P.coeff (P.natDegree - k) = P.coeff k := by
    have h := (rev_facts hP hp0).2.2.2 k hkd
    rw [hrev] at h
    exact h.symm
  have hsub : ({(P.natDegree, (0 : ℕ)), (P.natDegree - k, k)} : Finset (ℕ × ℕ)) ⊆
      antidiagonal P.natDegree := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;>
      simp [HasAntidiagonal.mem_antidiagonal, Nat.sub_add_cancel hkd]
  have hne : ((P.natDegree, (0 : ℕ)) : ℕ × ℕ) ≠ (P.natDegree - k, k) := by
    intro h
    have := congrArg Prod.snd h
    simp only at this
    omega
  have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (f := fun x : ℕ × ℕ => P.coeff x.1 * Q.coeff x.2) (fun x _ _ => mul_nonneg (hp _) (hq _))
  rw [Finset.sum_pair hne, ← coeff_mul] at hle
  simp only [hq0, hP.coeff_natDegree, hpal, one_mul] at hle
  have h0 := mul_nonneg (hp k) (hq k)
  rcases hR P.natDegree with h | h <;> linarith

lemma zo_both {P Q : ℝ[X]} (hp : ∀ n, 0 ≤ P.coeff n) (hq : ∀ n, 0 ≤ Q.coeff n)
    (hp0 : P.coeff 0 = 1) (hq0 : Q.coeff 0 = 1)
    (hR : ∀ n, (P * Q).coeff n = 0 ∨ (P * Q).coeff n = 1)
    (hpq : ∀ k, 1 ≤ k → P.coeff k * Q.coeff k = 0) :
    ∀ n, (P.coeff n = 0 ∨ P.coeff n = 1) ∧ (Q.coeff n = 0 ∨ Q.coeff n = 1) := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact ⟨Or.inr hp0, Or.inr hq0⟩
    have hmem0 : ((0 : ℕ), k) ∈ antidiagonal k := mem_antidiagonal.mpr (zero_add k)
    have hmem1 : (k, (0 : ℕ)) ∈ (antidiagonal k).erase (0, k) := by
      refine Finset.mem_erase.mpr ⟨?_, mem_antidiagonal.mpr (add_zero k)⟩
      intro h
      have := congrArg Prod.fst h
      simp only at this
      omega
    have hs1 := Finset.add_sum_erase (antidiagonal k)
      (fun x : ℕ × ℕ => P.coeff x.1 * Q.coeff x.2) hmem0
    have hs2 := Finset.add_sum_erase ((antidiagonal k).erase (0, k))
      (fun x : ℕ × ℕ => P.coeff x.1 * Q.coeff x.2) hmem1
    obtain ⟨s, hs⟩ : ∃ s : ℕ,
        ∑ x ∈ ((antidiagonal k).erase (0, k)).erase (k, 0), P.coeff x.1 * Q.coeff x.2 = s := by
      apply sum_nat
      intro x hx
      have hx1 := Finset.mem_erase.mp hx
      have hx2 := Finset.mem_erase.mp hx1.2
      have hx3 := mem_antidiagonal.mp hx2.2
      have ha : x.1 ≠ 0 := fun h0 => hx2.1 (Prod.ext h0 (by show x.2 = k; omega))
      have hb : x.2 ≠ 0 := fun h0 => hx1.1 (Prod.ext (by show x.1 = k; omega) h0)
      rcases (ih x.1 (by omega)).1 with h1 | h1 <;> rcases (ih x.2 (by omega)).2 with h2 | h2
      exacts [⟨0, by simp [h1, h2]⟩, ⟨0, by simp [h1, h2]⟩, ⟨0, by simp [h1, h2]⟩,
        ⟨1, by simp [h1, h2]⟩]
    have hrk := hR k
    rw [coeff_mul, ← hs1, ← hs2, hs] at hrk
    simp only [hp0, hq0, one_mul, mul_one] at hrk
    have hpk := hp k
    have hqk := hq k
    rcases Nat.eq_zero_or_pos s with h0 | hpos
    · subst h0
      simp only [Nat.cast_zero, add_zero] at hrk
      rcases mul_eq_zero.mp (hpq k hk) with h | h
      · rw [h, add_zero] at hrk
        exact ⟨Or.inl h, hrk⟩
      · rw [h, zero_add] at hrk
        exact ⟨hrk, Or.inl h⟩
    · have h1 : (1 : ℝ) ≤ s := by exact_mod_cast hpos
      have hle : Q.coeff k + (P.coeff k + s) ≤ 1 := by rcases hrk with h | h <;> linarith
      exact ⟨Or.inl (by linarith), Or.inl (by linarith)⟩

theorem kr {N : ℕ} {P Q : ℝ[X]} (hP : P.Monic) (hQ : Q.Monic) (hp : ∀ n, 0 ≤ P.coeff n)
    (hq : ∀ n, 0 ≤ Q.coeff n) (hPQ : P * Q = ∑ k ∈ range (N + 1), (X : ℝ[X]) ^ k) :
    ∀ n, P.coeff n = 0 ∨ P.coeff n = 1 := by
  have hR : ∀ n, (P * Q).coeff n = 0 ∨ (P * Q).coeff n = 1 := fun n => by
    rw [hPQ]; exact phi_coeff N n
  have hR' : ∀ n, (Q * P).coeff n = 0 ∨ (Q * P).coeff n = 1 := fun n => by
    rw [mul_comm Q P]; exact hR n
  have hc0 : P.coeff 0 * Q.coeff 0 = 1 := by
    rw [← mul_coeff_zero, hPQ, finsetSum_coeff]
    simp only [coeff_X_pow]
    rw [Finset.sum_ite_eq, if_pos (mem_range.mpr (Nat.succ_pos N))]
  have hp1 := coeff_le_one hQ hp hq hR 0
  have hq1 := coeff_le_one hP hq hp hR' 0
  have hp0 : P.coeff 0 = 1 := le_antisymm hp1 (by
    have := mul_le_mul_of_nonneg_left hq1 (hp 0); linarith)
  have hq0 : Q.coeff 0 = 1 := le_antisymm hq1 (by
    have := mul_le_mul_of_nonneg_right hp1 (hq 0); linarith)
  have hrev := palindrome hP hp0 hPQ
  have hpq := pq_zero hP hp hq hR hp0 hq0 hrev
  exact fun n => (zo_both hp hq hp0 hq0 hR hpq n).1

end OMA.KrasnerRanulac

theorem OMA.solution : OMA.R_Mathoverflow339137_mathoverflow_339137_R1.H1 := by
  intro N P Q hP hQ hp hq _ _ hPQ
  exact (OMA.R_Mathoverflow339137_mathoverflow_339137_R1.isZeroOne_iff P).mpr
    (OMA.KrasnerRanulac.kr hP hQ hp hq hPQ)
