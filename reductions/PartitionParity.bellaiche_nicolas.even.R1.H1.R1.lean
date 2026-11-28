import OMAReductions.R_PartitionParity_bellaiche_nicolas_even_R1

/-!
For the explicit bound of Bellaïche and Nicolas, use their earlier estimate (1.13)
and inequality (6.12) of Theorem 5 at α = 0.335. The cutoff log log x = 16.2
lies in the overlap. The proof handles small x and certifies the constants.
Reference: Bellaïche and Nicolas, Parité des coefficients de formes modulaires,
Ramanujan Journal 40 (2016), section 6.
-/

namespace OMA.R_PartitionParity_bellaiche_nicolas_even_R1_H1_R1
open Real

/-- Nicolas's earlier estimate, restricted to the needed middle range. -/
def H1 : Prop := ∀ x : ℝ, 3 ≤ x → log (log x) ≤ 16.2 →
  0.28 * √x * √(log (log x)) ≤ ({n : ℕ | (n : ℝ) ≤ x ∧ Even (Nat.partitionNumber n)}.ncard : ℝ)

/-- The Hecke support and partition estimate (6.12) at a fixed α. -/
def H2 : Prop := ∀ x : ℝ, 3 ≤ x → 16.2 ≤ log (log x) →
  0.408 * 0.335 * √x * log (log x) *
    (1 - 39.5 / ((1 - 0.335) *
      (log (8*x)) ^ (1 - 0.335 + 0.335 * log 0.335))) ≤ ({n : ℕ | (n : ℝ) ≤ x ∧ Even (Nat.partitionNumber n)}.ncard : ℝ)

lemma denominator_bound (x : ℝ) (hx : 3 ≤ x) (hl : 16.2 ≤ log (log x)) :
    (120 : ℝ) ≤ (log (8*x)) ^ (1 - 0.335 + 0.335 * log 0.335) := by
  have hp : 0 < log x := log_pos (by linarith)
  have hp8 : 0 < log (8*x) := log_pos (by linarith)
  have hm := log_le_log hp (log_le_log (by linarith) (by linarith : x ≤ 8*x))
  have la : (-1.1 : ℝ) ≤ log 0.335 := by
    apply (le_log_iff_exp_le (by norm_num)).mpr
    rw [exp_neg, inv_le_comm₀ (exp_pos _) (by norm_num)]
    have h1 : (2.718:ℝ) ≤ exp 1 := by linarith [exp_one_gt_d9]
    have h2 : (1.1:ℝ) ≤ exp 0.1 := by linarith [add_one_le_exp (0.1:ℝ)]
    calc
      _ ≤ 2.718 * 1.1 := by norm_num
      _ ≤ exp 1 * exp 0.1 := mul_le_mul h1 h2 (by norm_num) (exp_pos _).le
      _ = exp 1.1 := by rw [← exp_add]; norm_num
  have hq : (0.2965:ℝ) ≤ 1-0.335 + 0.335*log 0.335 := by linarith
  have prod := mul_le_mul (hl.trans hm) hq (by norm_num) (by linarith : 0 ≤ log (log (8*x)))
  have ht : (4.8 : ℝ) ≤ log (log (8*x)) * (1-0.335 + 0.335*log 0.335) := by linarith
  have e : (1.105:ℝ) ≤ exp 0.1 := by linarith [quadratic_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 0.1)]
  rw [rpow_def_of_pos hp8]
  calc
    (120:ℝ) ≤ 1.105^48 := by norm_num
    _ ≤ (exp 0.1)^48 := pow_le_pow_left₀ (by norm_num) e _
    _ = exp 4.8 := by rw [← exp_nat_mul]; norm_num
    _ ≤ _ := exp_le_exp.mpr ht

lemma small_inputs (x : ℝ) (hx : 1 < x) (h3 : x ≤ 3) :
    0.069 * √x * log (log x) ≤ ({n : ℕ | (n : ℝ) ≤ x ∧ Even (Nat.partitionNumber n)}.ncard : ℝ) := by
  by_cases hn : x < 2
  · have hl : log x ≤ 1 := by
      apply (log_le_iff_le_exp (by linarith)).mpr
      linarith [exp_one_gt_d9]
    have hll := log_nonpos (log_pos hx).le hl
    exact (mul_nonpos_of_nonneg_of_nonpos (by positivity) hll).trans (Nat.cast_nonneg _)
  have h2 : (2:ℝ) ≤ x := le_of_not_gt hn
  have nonempty : {n : ℕ | (n:ℝ) ≤ x ∧ Even (Nat.partitionNumber n)}.Nonempty :=
    ⟨2,h2,by rw [Nat.partitionNumber_two]; decide⟩
  have finite : {n : ℕ | (n:ℝ) ≤ x ∧ Even (Nat.partitionNumber n)}.Finite :=
    (Set.finite_Iic ⌊x⌋₊).subset fun _ h => Nat.le_floor h.1
  have hc : 1 ≤ ({n : ℕ | (n : ℝ) ≤ x ∧ Even (Nat.partitionNumber n)}.ncard : ℝ) := by exact_mod_cast nonempty.ncard_pos finite
  have hs := (sqrt_le_left (by norm_num : (0:ℝ) ≤ 2)).mpr (by linarith : x ≤ 2^2)
  have hl := log_le_sub_one_of_pos (by linarith : 0 < x)
  have hll := log_le_sub_one_of_pos (log_pos hx)
  have hprod := mul_le_mul_of_nonneg_left (show log (log x) ≤ 1 by linarith) (sqrt_nonneg x)
  linarith

theorem main : H1 → H2 → OMA.R_PartitionParity_bellaiche_nicolas_even_R1.H1 := by
  intro middle large x hx
  change 0.069 * √x * log (log x) ≤ ({n : ℕ | (n : ℝ) ≤ x ∧ Even (Nat.partitionNumber n)}.ncard : ℝ)
  by_cases h3 : x ≤ 3
  · exact small_inputs x hx h3
  have hx3 := le_of_lt (lt_of_not_ge h3)
  have hl : 0 ≤ log (log x) := log_nonneg ((le_log_iff_exp_le (by linarith)).mpr
    (exp_one_lt_three.le.trans hx3))
  by_cases cut : log (log x) ≤ 16.2
  · apply le_trans _ (middle x hx3 cut)
    have hs := (sqrt_le_left (by norm_num : (0:ℝ) ≤ 4.03)).mpr (by linarith : log (log x) ≤ 4.03^2)
    have hsq := sq_sqrt hl
    have hh := mul_le_mul_of_nonneg_right (show 0.069*√(log (log x)) ≤ 0.28 by linarith)
      (sqrt_nonneg (log (log x)))
    have hcoef : 0.069*log (log x) ≤ 0.28 * √(log (log x)) := by nlinarith only [hsq,hh]
    linarith only [mul_le_mul_of_nonneg_left hcoef (sqrt_nonneg x)]
  · have ht := (lt_of_not_ge cut).le
    apply le_trans _ (large x hx3 ht)
    have hd := denominator_bound x hx3 ht
    have hden : (39.5:ℝ) / ((1-0.335) * (log (8*x)) ^ (1-0.335+0.335*log 0.335)) ≤
        39.5 / ((1-0.335)*120) := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      linarith
    have hc : 0.069 ≤ 0.408*0.335 * (1 - 39.5 / ((1-0.335) *
        (log (8*x)) ^ (1-0.335+0.335*log 0.335))) := by linarith
    linarith only [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (sqrt_nonneg x)) hl]

end OMA.R_PartitionParity_bellaiche_nicolas_even_R1_H1_R1
