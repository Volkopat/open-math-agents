import OMAStatements.S_oeis_a166872
import Mathlib

/-!
# OEIS A166872: the values occurring exactly three times have the conjectured generating function

Credit: @Squee451. The proof was found with Claude (claude-fable-5-2) and Codex; the Lean text was
written by Codex.

Outline. (1) For n >= 1 and k >= 0: a(n) >= k iff n >= L(k) := 2k + ceil(sqrt(16k+1)) (rewrite as n + 4 - 2k
>= sqrt(17 + 8n) and square; the negative branch is excluded). (2) So a(n) = k exactly for L(k) <= n
< L(k+1), and the multiplicity of k is 2 + (number of integers m >= 1 with 16k+1 <= m^2 < 16k+17).
(3) That number is 4, 1, 1, 2 for k = 0, 1, 2, 3 (m = 1..4; 5; 6; 7, 8), and for m >= 9 consecutive
squares differ by at least 19, so each k >= 4 gets at most one m. Hence the k with multiplicity 3
are 1, 2 and floor((m^2-1)/16) for m >= 9: b(0) = 1, b(1) = 2, b(j) = floor(((j+7)^2 - 1)/16) for j
>= 2, strictly increasing. (4) b(j+8) - b(j) = j + 11 for j >= 2, so with Q = (1-x)^2 (1-x^8) the
coefficient of x^j in Q*B vanishes for j >= 12, and the first twelve coefficients, from b = 1, 2, 5,
6, 7, 8, 10, 12, 14, 15, 18, 20, are 1, 0, 2, -2, 0, 0, 1, 0, -1, -1, 0, 1.
-/

open OMA.S_oeis_a166872

namespace OMA.A166872Proof

def s (k : ℕ) : ℕ := Nat.sqrt (16 * k)
def L (k : ℕ) : ℕ := 2 * k + s k + 1

lemma s_sq (k : ℕ) : s k ^ 2 ≤ 16 * k := Nat.sqrt_le' _
lemma s_sq_next (k : ℕ) : 16 * k < (s k + 1) ^ 2 := Nat.lt_succ_sqrt' _
lemma s_mono : Monotone s := fun _ _ h => Nat.sqrt_le_sqrt (by omega)

lemma floor_threshold (n k : ℕ) (hn : 1 ≤ n) :
    (k : ℤ) ≤ a n ↔ L k ≤ n := by
  rw [a, Int.le_floor]
  simp only [Int.cast_natCast]
  have hr := Real.sq_sqrt (show (0 : ℝ) ≤ 17 / 4 + 2 * n by positivity)
  have hp := Real.sqrt_nonneg (17 / 4 + 2 * (n : ℝ))
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hk' : (0 : ℝ) ≤ k := by positivity
  have hs : (s k : ℝ) ^ 2 ≤ 16 * k := by exact_mod_cast s_sq k
  have ht : 16 * (k : ℝ) < (s k + 1) ^ 2 := by exact_mod_cast s_sq_next k
  have hz : (0 : ℝ) ≤ s k := by positivity
  constructor
  · intro h
    have hbase : 2 * (k : ℝ) ≤ n := by
      by_contra hc
      have hnlt : (n : ℝ) < 2 * k := by linarith
      have hkpos : 1 ≤ k := by
        by_contra hk
        have : k = 0 := by omega
        subst k
        norm_num at hnlt
        linarith
      have hkpos' : (1 : ℝ) ≤ k := by exact_mod_cast hkpos
      have hsmall : Real.sqrt (17 / 4 + 2 * (n : ℝ)) < 2 := by linarith
      nlinarith
    have hsq : 16 * (k : ℝ) + 1 ≤ ((n : ℝ) - 2 * k) ^ 2 := by
      nlinarith [sq_nonneg ((n : ℝ) / 2 + 2 - k - Real.sqrt (17 / 4 + 2 * (n : ℝ))),
        mul_nonneg (show 0 ≤ (n : ℝ) / 2 + 2 - k - Real.sqrt (17 / 4 + 2 * (n : ℝ)) by linarith) hp]
    have : (s k : ℝ) < n - 2 * k := by nlinarith
    have : s k + 2 * k < n := by exact_mod_cast (show (s k : ℝ) + 2 * k < n by linarith)
    unfold L
    omega
  · intro h
    have hbound : (2 * k + s k + 1 : ℝ) ≤ n := by exact_mod_cast h
    have hsq : 16 * (k : ℝ) + 1 ≤ ((n : ℝ) - 2 * k) ^ 2 := by
      have ht' : 16 * k + 1 ≤ (s k + 1) ^ 2 := by have := s_sq_next k; omega
      have ht'' : 16 * (k : ℝ) + 1 ≤ (s k + 1) ^ 2 := by exact_mod_cast ht'
      nlinarith [sq_nonneg ((n : ℝ) - 2 * k - (s k + 1))]
    by_contra hc
    have : (n : ℝ) / 2 + 2 - k < Real.sqrt (17 / 4 + 2 * (n : ℝ)) := by linarith
    nlinarith [mul_pos (show 0 < Real.sqrt (17 / 4 + 2 * (n : ℝ)) - ((n : ℝ) / 2 + 2 - k) by linarith)
      (show 0 < Real.sqrt (17 / 4 + 2 * (n : ℝ)) + ((n : ℝ) / 2 + 2 - k) by linarith)]

lemma value_interval (n k : ℕ) :
    (1 ≤ n ∧ a n = (k : ℤ)) ↔ L k ≤ n ∧ n < L (k + 1) := by
  constructor
  · rintro ⟨hn, he⟩
    have hlo := (floor_threshold n k hn).mp (le_of_eq he.symm)
    have hhi : ¬ L (k + 1) ≤ n := by
      intro h
      have := (floor_threshold n (k + 1) hn).mpr h
      rw [he] at this
      omega
    exact ⟨hlo, by omega⟩
  · rintro ⟨hlo, hhi⟩
    have hn : 1 ≤ n := by unfold L at hlo; omega
    have h₁ := (floor_threshold n k hn).mpr hlo
    have h₂ : ¬ ((k + 1 : ℕ) : ℤ) ≤ a n := by
      intro h
      have := (floor_threshold n (k + 1) hn).mp h
      omega
    exact ⟨hn, by omega⟩

lemma multiplicity_eq (k : ℕ) : OMA.S_oeis_a166872.multiplicity k = L (k + 1) - L k := by
  have he : {n : ℕ | 1 ≤ n ∧ a n = (k : ℤ)} =
      (↑(Finset.Ico (L k) (L (k + 1))) : Set ℕ) := by
    ext n
    simpa only [Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_Ico] using value_interval n k
  unfold OMA.S_oeis_a166872.multiplicity
  rw [he, Set.ncard_coe_finset, Nat.card_Ico]

lemma multiplicity_three (k : ℕ) :
    OMA.S_oeis_a166872.multiplicity k = 3 ↔ s (k + 1) = s k + 1 := by
  rw [multiplicity_eq]
  unfold L
  have := s_mono (show k ≤ k + 1 by omega)
  omega

def b (j : ℕ) : ℕ :=
  if j = 0 then 1 else if j = 1 then 2 else ((j + 7) ^ 2 - 1) / 16

lemma b_formula (j : ℕ) (hj : 2 ≤ j) : b j = ((j + 7) ^ 2 - 1) / 16 := by
  simp [b, show j ≠ 0 by omega, show j ≠ 1 by omega]

lemma bucket (m k : ℕ) (hm : 1 ≤ m) :
    (m ^ 2 - 1) / 16 = k ↔ 16 * k < m ^ 2 ∧ m ^ 2 ≤ 16 * (k + 1) := by
  have : 1 ≤ m ^ 2 := by nlinarith
  omega

lemma large_three (k : ℕ) (hk : 4 ≤ k) :
    s (k + 1) = s k + 1 ↔ ∃ m : ℕ, 9 ≤ m ∧ (m ^ 2 - 1) / 16 = k := by
  constructor
  · intro h
    have hs8 : 8 ≤ s k := Nat.le_sqrt'.mpr (by omega)
    refine ⟨s (k + 1), by omega, (bucket _ _ (by omega)).mpr ?_⟩
    exact ⟨by rw [h]; exact s_sq_next k, s_sq (k + 1)⟩
  · rintro ⟨m, hm, he⟩
    obtain ⟨hlo, hhi⟩ := (bucket m k (by omega)).mp he
    have hm1 : m - 1 + 1 = m := by omega
    have h₁ : s k = m - 1 := by
      apply Eq.symm
      apply Nat.eq_sqrt'.mpr
      constructor
      · nlinarith
      · simpa only [hm1] using hlo
    have h₂ : s (k + 1) = m := by
      apply Eq.symm
      apply Nat.eq_sqrt'.mpr
      exact ⟨hhi, by nlinarith⟩
    omega

lemma three_characterization (k : ℕ) : OMA.S_oeis_a166872.multiplicity k = 3 ↔
    k = 1 ∨ k = 2 ∨ ∃ m : ℕ, 9 ≤ m ∧ (m ^ 2 - 1) / 16 = k := by
  rw [multiplicity_three]
  by_cases hk : 4 ≤ k
  · rw [large_three k hk]
    simp [show k ≠ 1 by omega, show k ≠ 2 by omega]
  · have hnone : ¬ ∃ m : ℕ, 9 ≤ m ∧ (m ^ 2 - 1) / 16 = k := by
      rintro ⟨m, hm, he⟩
      have hb := ((bucket m k (by omega)).mp he).2
      nlinarith
    simp only [hnone, or_false]
    interval_cases k <;> decide +kernel

lemma b_range (k : ℕ) : (∃ j, b j = k) ↔
    k = 1 ∨ k = 2 ∨ ∃ m : ℕ, 9 ≤ m ∧ (m ^ 2 - 1) / 16 = k := by
  constructor
  · rintro ⟨j, hj⟩
    by_cases h₀ : j = 0
    · subst j
      exact Or.inl (by simpa [b] using hj.symm)
    by_cases h₁ : j = 1
    · subst j
      exact Or.inr (Or.inl (by simpa [b] using hj.symm))
    exact Or.inr (Or.inr ⟨j + 7, by omega, by rwa [b_formula j (by omega)] at hj⟩)
  · rintro (rfl | rfl | ⟨m, hm, he⟩)
    · exact ⟨0, by norm_num [b]⟩
    · exact ⟨1, by norm_num [b]⟩
    refine ⟨m - 7, ?_⟩
    rw [b_formula _ (by omega), Nat.sub_add_cancel (by omega)]
    exact he

lemma b_strict : StrictMono b := by
  apply strictMono_nat_of_lt_succ
  intro j
  by_cases h₀ : j = 0
  · subst j; norm_num [b]
  by_cases h₁ : j = 1
  · subst j; norm_num [b]
  have hj : 2 ≤ j := by omega
  rw [b_formula j hj, b_formula (j + 1) (by omega)]
  have hsq : (j + 7) ^ 2 + 16 ≤ (j + 1 + 7) ^ 2 := by nlinarith
  have hpos : 1 ≤ (j + 7) ^ 2 := by nlinarith
  omega

lemma b_shift (j : ℕ) (hj : 2 ≤ j) : b (j + 8) = b j + j + 11 := by
  rw [b_formula (j + 8) (by omega), b_formula j hj]
  have hpos : 1 ≤ (j + 7) ^ 2 := by nlinarith
  have hpoly : (j + 8 + 7) ^ 2 - 1 = (j + 7) ^ 2 - 1 + (j + 11) * 16 := by
    have : 1 ≤ (j + 8 + 7) ^ 2 := by nlinarith
    have : (j + 8 + 7) ^ 2 = (j + 7) ^ 2 + (j + 11) * 16 := by ring
    omega
  omega

lemma b_recurrence (j : ℕ) (hj : 2 ≤ j) :
    (b (j + 10) : ℤ) - 2 * b (j + 9) + b (j + 8) - b (j + 2) +
      2 * b (j + 1) - b j = 0 := by
  have h₀ := congrArg (fun n : ℕ => (n : ℤ)) (b_shift j hj)
  have h₁ := congrArg (fun n : ℕ => (n : ℤ)) (b_shift (j + 1) (by omega))
  have h₂ := congrArg (fun n : ℕ => (n : ℤ)) (b_shift (j + 2) (by omega))
  push_cast at h₀ h₁ h₂
  norm_num [Nat.add_assoc] at h₀ h₁ h₂
  omega

lemma coeff_mul_X (p : PowerSeries ℤ) (n : ℕ) :
    PowerSeries.coeff n (p * PowerSeries.X) =
      if 1 ≤ n then PowerSeries.coeff (n - 1) p else 0 := by
  simpa only [pow_one] using PowerSeries.coeff_mul_X_pow' p 1 n

lemma generating_function :
    PowerSeries.mk (fun j => (b j : ℤ)) *
        (1 - 2 * PowerSeries.X + PowerSeries.X ^ 2 - PowerSeries.X ^ 8 +
          2 * PowerSeries.X ^ 9 - PowerSeries.X ^ 10) =
      (1 + 2 * PowerSeries.X ^ 2 - 2 * PowerSeries.X ^ 3 + PowerSeries.X ^ 6 -
        PowerSeries.X ^ 8 - PowerSeries.X ^ 9 + PowerSeries.X ^ 11 : PowerSeries ℤ) := by
  apply PowerSeries.ext
  intro n
  simp only [two_mul, mul_sub, mul_add, mul_one, map_add, map_sub,
    coeff_mul_X, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mk,
    PowerSeries.coeff_X_pow, PowerSeries.coeff_one]
  by_cases hn : n < 12
  · interval_cases n <;> norm_num [b]
  · have hrec := b_recurrence (n - 10) (by omega)
    have h₀ : n - 10 + 10 = n := by omega
    have h₁ : n - 10 + 9 = n - 1 := by omega
    have h₂ : n - 10 + 8 = n - 2 := by omega
    have h₃ : n - 10 + 2 = n - 8 := by omega
    have h₄ : n - 10 + 1 = n - 9 := by omega
    rw [h₀, h₁, h₂, h₃, h₄] at hrec
    simp (disch := omega) only [if_pos, if_neg]
    omega

end OMA.A166872Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a166872.main := by
  refine ⟨OMA.A166872Proof.b, OMA.A166872Proof.b_strict, ?_, OMA.A166872Proof.generating_function⟩
  intro k
  rw [OMA.A166872Proof.b_range, OMA.A166872Proof.three_characterization]
