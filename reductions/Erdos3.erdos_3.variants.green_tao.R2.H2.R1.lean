import OMAReductions.R_Erdos3_erdos_3_variants_green_tao_R2

-- Reduction Erdos3.erdos_3.variants.green_tao.R2.H2.R1 of step Erdos3.erdos_3.variants.green_tao.R2.H2
-- Credit: @mucoucah
--
-- First step of the inverse U^3 argument (proved here, from the R2.H2 proof attempt):
-- if the U^3 sum of the balanced function f = 1_S - alpha 1_[1,N] is at least
-- delta N^4 (delta = kappa alpha^K), then at least delta N / 6 shifts a in [-N, N] have
-- derivative U^2 energy  sum_b (sum_x f x f(x+a) f(x+b) f(x+a+b))^2  at least delta N^3 / 6.
-- So the structured case reduces to the bound for 4-AP-free sets with many derivatives of
-- large U^2 energy (the remaining inverse theorem plus density increment).
-- H1 / H2 are this statement for even N / odd N.

namespace OMA.R_Erdos3_erdos_3_variants_green_tao_R2_H2_R1

def H1 : Prop := ∀ K : ℕ, ∀ κ : ℝ, 0 < κ → ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ,
  ∀ N : ℕ, N₀ ≤ N → Even N → ∀ S : Finset ℕ, S ⊆ Finset.Icc 1 N →
    (∀ a d : ℕ, 0 < d → a ∈ S → a + d ∈ S → a + 2 * d ∈ S → a + 3 * d ∈ S → False) →
    (let f : ℤ → ℝ := fun x => (if 0 < x ∧ x.toNat ∈ S then (1 : ℝ) else 0) -
        (if 0 < x ∧ x ≤ (N : ℤ) then (S.card : ℝ) / N else 0)
     κ * ((S.card : ℝ) / N) ^ K * (N : ℝ) / 6 ≤
       (((Finset.Icc (-(N : ℤ)) N).filter (fun a => κ * ((S.card : ℝ) / N) ^ K * (N : ℝ) ^ 3 / 6 ≤
         ∑ b ∈ Finset.Icc (-(N : ℤ)) N, (∑ x ∈ Finset.Icc (1 : ℤ) N,
           f x * f (x + a) * f (x + b) * f (x + a + b)) ^ 2)).card : ℝ)) →
    (S.card : ℝ) ≤ C * ((N : ℝ) * Real.log N ^ (-c))

def H2 : Prop := ∀ K : ℕ, ∀ κ : ℝ, 0 < κ → ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ,
  ∀ N : ℕ, N₀ ≤ N → Odd N → ∀ S : Finset ℕ, S ⊆ Finset.Icc 1 N →
    (∀ a d : ℕ, 0 < d → a ∈ S → a + d ∈ S → a + 2 * d ∈ S → a + 3 * d ∈ S → False) →
    (let f : ℤ → ℝ := fun x => (if 0 < x ∧ x.toNat ∈ S then (1 : ℝ) else 0) -
        (if 0 < x ∧ x ≤ (N : ℤ) then (S.card : ℝ) / N else 0)
     κ * ((S.card : ℝ) / N) ^ K * (N : ℝ) / 6 ≤
       (((Finset.Icc (-(N : ℤ)) N).filter (fun a => κ * ((S.card : ℝ) / N) ^ K * (N : ℝ) ^ 3 / 6 ≤
         ∑ b ∈ Finset.Icc (-(N : ℤ)) N, (∑ x ∈ Finset.Icc (1 : ℤ) N,
           f x * f (x + a) * f (x + b) * f (x + a + b)) ^ 2)).card : ℝ)) →
    (S.card : ℝ) ≤ C * ((N : ℝ) * Real.log N ^ (-c))

lemma sum_translate_eq {N : ℕ} {g : ℤ → ℝ}
    (hg : ∀ y ∉ Finset.Icc (1 : ℤ) N, g y = 0) {x : ℤ} (hx : x ∈ Finset.Icc (1 : ℤ) N) :
    ∑ e ∈ Finset.Icc (-(N : ℤ)) N, g (x + e) = ∑ y ∈ Finset.Icc (1 : ℤ) N, g y := by
  simp only [Finset.mem_Icc] at hx
  refine Finset.sum_bij_ne_zero (fun e _ _ => x + e) ?_ ?_ ?_ ?_
  · intro e he h
    exact by_contra fun hy => h (hg _ hy)
  · intro e₁ _ _ e₂ _ _ h
    omega
  · intro y hy h
    have hy' : 1 ≤ y ∧ y ≤ (N : ℤ) := Finset.mem_Icc.mp hy
    refine ⟨y - x, ?_, ?_, by omega⟩
    · exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · simpa only [add_sub_cancel] using h
  · intros
    rfl

lemma cubeSum_eq_sq {N : ℕ} {f : ℤ → ℝ}
    (hf : ∀ x ∉ Finset.Icc (1 : ℤ) N, f x = 0) :
    ∑ x ∈ Finset.Icc (1 : ℤ) N, ∑ a ∈ Finset.Icc (-(N : ℤ)) N, ∑ b ∈ Finset.Icc (-(N : ℤ)) N,
       ∑ e ∈ Finset.Icc (-(N : ℤ)) N,
         f x * f (x + a) * f (x + b) * f (x + e) * f (x + a + b) * f (x + a + e) *
           f (x + b + e) * f (x + a + b + e) =
    ∑ a ∈ Finset.Icc (-(N : ℤ)) N, ∑ b ∈ Finset.Icc (-(N : ℤ)) N,
      (∑ x ∈ Finset.Icc (1 : ℤ) N, f x * f (x + a) * f (x + b) * f (x + a + b)) ^ 2 := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [sq, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hg : ∀ y ∉ Finset.Icc (1 : ℤ) N,
      f y * f (y + a) * f (y + b) * f (y + a + b) = 0 := by
    intro y hy
    simp [hf y hy]
  rw [← sum_translate_eq hg hx, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  simp only [add_right_comm (x + _) e, add_right_comm x e]
  ring

lemma card_filter_large_terms {ι : Type*} (D : Finset ι) (v : ι → ℝ)
    {u t : ℝ} (ht : 0 ≤ t) (hv : ∀ a ∈ D, v a ≤ u) :
    (∑ a ∈ D, v a) ≤
      ((D.filter (fun a => t ≤ v a)).card : ℝ) * u + (D.card : ℝ) * t := by
  classical
  calc
    _ ≤ ∑ a ∈ D, ((if t ≤ v a then u else 0) + t) := by
      apply Finset.sum_le_sum
      intro a ha
      split_ifs with h
      · linarith [hv a ha]
      · linarith
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_const, ← Finset.sum_filter, Finset.sum_const]
      simp only [nsmul_eq_mul]

lemma energy_le {N : ℕ} {f : ℤ → ℝ} (habs : ∀ x, |f x| ≤ 1) (a : ℤ) :
    ∑ b ∈ Finset.Icc (-(N : ℤ)) N, (∑ x ∈ Finset.Icc (1 : ℤ) N,
      f x * f (x + a) * f (x + b) * f (x + a + b)) ^ 2 ≤ 3 * (N : ℝ) ^ 3 := by
  have hface : ∀ b, |∑ x ∈ Finset.Icc (1 : ℤ) N, f x * f (x + a) * f (x + b) * f (x + a + b)|
      ≤ N := by
    intro b
    calc
      _ ≤ ∑ x ∈ Finset.Icc (1 : ℤ) N, |f x * f (x + a) * f (x + b) * f (x + a + b)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _x ∈ Finset.Icc (1 : ℤ) N, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro x _
        simp only [abs_mul]
        calc
          _ ≤ (1 : ℝ) * 1 * 1 * 1 := by gcongr <;> apply habs
          _ = 1 := by norm_num
      _ = _ := by simp [Int.card_Icc]
  calc
    _ ≤ ∑ _b ∈ Finset.Icc (-(N : ℤ)) N, (N : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro b _
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hface b) _
    _ = (2 * (N : ℝ) + 1) * (N : ℝ) ^ 2 := by
      simp only [Finset.sum_const, Int.card_Icc, nsmul_eq_mul]
      congr 1
      have : ((N : ℤ) + 1 - -(N : ℤ)).toNat = 2 * N + 1 := by omega
      rw [this]
      push_cast
      ring
    _ ≤ 3 * (N : ℝ) ^ 3 := by
      rcases Nat.eq_zero_or_pos N with h | h
      · subst h; simp
      · have hN : (1 : ℝ) ≤ N := by exact_mod_cast h
        nlinarith [sq_nonneg (N : ℝ)]

lemma many_large {N : ℕ} {f : ℤ → ℝ}
    (hf : ∀ x ∉ Finset.Icc (1 : ℤ) N, f x = 0) (habs : ∀ x, |f x| ≤ 1)
    (hN : 1 ≤ N) {δ : ℝ} (hδ : 0 ≤ δ)
    (hlarge : δ * (N : ℝ) ^ 4 ≤
      ∑ x ∈ Finset.Icc (1 : ℤ) N, ∑ a ∈ Finset.Icc (-(N : ℤ)) N, ∑ b ∈ Finset.Icc (-(N : ℤ)) N,
       ∑ e ∈ Finset.Icc (-(N : ℤ)) N,
         f x * f (x + a) * f (x + b) * f (x + e) * f (x + a + b) * f (x + a + e) *
           f (x + b + e) * f (x + a + b + e)) :
    δ * (N : ℝ) / 6 ≤
       (((Finset.Icc (-(N : ℤ)) N).filter (fun a => δ * (N : ℝ) ^ 3 / 6 ≤
         ∑ b ∈ Finset.Icc (-(N : ℤ)) N, (∑ x ∈ Finset.Icc (1 : ℤ) N,
           f x * f (x + a) * f (x + b) * f (x + a + b)) ^ 2)).card : ℝ) := by
  set D := (Finset.Icc (-(N : ℤ)) N).filter (fun a => δ * (N : ℝ) ^ 3 / 6 ≤
         ∑ b ∈ Finset.Icc (-(N : ℤ)) N, (∑ x ∈ Finset.Icc (1 : ℤ) N,
           f x * f (x + a) * f (x + b) * f (x + a + b)) ^ 2) with hD
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hcount : ((Finset.Icc (-(N : ℤ)) N).card : ℝ) ≤ 3 * (N : ℝ) := by
    have : (Finset.Icc (-(N : ℤ)) N).card = 2 * N + 1 := by
      simp only [Int.card_Icc]; omega
    rw [this]; push_cast; linarith
  have htotal := hlarge
  rw [cubeSum_eq_sq hf] at htotal
  have hsplit := card_filter_large_terms (Finset.Icc (-(N : ℤ)) N)
    (fun a => ∑ b ∈ Finset.Icc (-(N : ℤ)) N, (∑ x ∈ Finset.Icc (1 : ℤ) N,
           f x * f (x + a) * f (x + b) * f (x + a + b)) ^ 2)
    (u := 3 * (N : ℝ) ^ 3) (t := δ * (N : ℝ) ^ 3 / 6)
    (by positivity) (fun a _ => energy_le habs a)
  rw [← hD] at hsplit
  have hsmall := mul_le_mul_of_nonneg_right hcount
    (show 0 ≤ δ * (N : ℝ) ^ 3 / 6 by positivity)
  have hmul : (δ * (N : ℝ) / 6) * (3 * (N : ℝ) ^ 3) ≤
      (D.card : ℝ) * (3 * (N : ℝ) ^ 3) := by
    linarith only [htotal, hsplit, hsmall]
  exact le_of_mul_le_mul_right hmul (by positivity)

lemma balanced_props {N : ℕ} {S : Finset ℕ} (hS : S ⊆ Finset.Icc 1 N) :
    (∀ x ∉ Finset.Icc (1 : ℤ) N, ((if 0 < x ∧ x.toNat ∈ S then (1 : ℝ) else 0) -
        (if 0 < x ∧ x ≤ (N : ℤ) then (S.card : ℝ) / N else 0)) = 0) ∧
    (∀ x : ℤ, |(if 0 < x ∧ x.toNat ∈ S then (1 : ℝ) else 0) -
        (if 0 < x ∧ x ≤ (N : ℤ) then (S.card : ℝ) / N else 0)| ≤ 1) := by
  have hd0 : 0 ≤ (S.card : ℝ) / N := by positivity
  have hd1 : (S.card : ℝ) / N ≤ 1 := by
    have hc : S.card ≤ N := (Finset.card_le_card hS).trans_eq (by simp)
    rcases Nat.eq_zero_or_pos N with hN | hN
    · simp [hN]
    · exact (div_le_one (by exact_mod_cast hN)).mpr (by exact_mod_cast hc)
  refine ⟨fun x hx => ?_, fun x => ?_⟩
  · have hord : ¬ (0 < x ∧ x ≤ (N : ℤ)) := by
      simp only [Finset.mem_Icc] at hx
      omega
    have hmem : ¬ (0 < x ∧ x.toNat ∈ S) := by
      rintro ⟨hxpos, hxS⟩
      have hxN := (Finset.mem_Icc.mp (hS hxS)).2
      exact hord ⟨hxpos, by omega⟩
    simp [hord, hmem]
  · rw [abs_le]
    split_ifs <;> constructor <;> linarith

theorem main : H1 → H2 → OMA.R_Erdos3_erdos_3_variants_green_tao_R2.H2 := by
  intro h1 h2 K κ hκ
  obtain ⟨c₁, hc₁, C₁, hC₁, N₁, hu⟩ := h1 K κ hκ
  obtain ⟨c₂, hc₂, C₂, hC₂, N₂, hs⟩ := h2 K κ hκ
  refine ⟨min c₁ c₂, lt_min hc₁ hc₂, max C₁ C₂, lt_max_of_lt_left hC₁, max 3 (max N₁ N₂), ?_⟩
  intro N hN S hS hfree hlarge
  have hN3 : 3 ≤ N := le_trans (le_max_left _ _) hN
  have hN1 : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hN2 : N₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  obtain ⟨hsupp, habs⟩ := balanced_props hS
  have hδ : 0 ≤ κ * ((S.card : ℝ) / N) ^ K := by positivity
  have hder := many_large hsupp habs (by omega) hδ (le_of_not_gt hlarge)
  rcases Nat.even_or_odd N with he | ho
  · exact OMA.R_Erdos3_erdos_3_variants_green_tao_R2.bound_mono hN3 (min_le_left _ _)
      (le_max_left _ _) hC₁.le (hu N hN1 he S hS hfree hder)
  · exact OMA.R_Erdos3_erdos_3_variants_green_tao_R2.bound_mono hN3 (min_le_right _ _)
      (le_max_right _ _) hC₂.le (hs N hN2 ho S hS hfree hder)

end OMA.R_Erdos3_erdos_3_variants_green_tao_R2_H2_R1
