import OMAStatements.S_oeis_a128939

/-!
# Proof of OEIS A128939: largest product of partition parts congruent to 1 mod 3

We establish both attainment (via explicit lists of `1`, `4`, and at most one `7`)
and optimality (via `p * prediction m ≤ prediction (p + m)` for every `p % 3 = 1`,
proved by direct case analysis for `p ∈ {1, 4, 7}` and `p ≤ 4 ^ (p / 4)` for `8 ≤ p`).
-/

namespace OMA.S_oeis_a128939.Proof

open OMA.S_oeis_a128939

private lemma prediction_in_products (n : ℕ) : prediction n ∈ products n := by
  unfold products prediction
  by_cases h4 : n < 4
  · simp only [if_pos h4]
    refine ⟨List.replicate n 1, ?_, ?_, ?_⟩
    · intro p hp
      rw [List.mem_replicate] at hp
      simp [hp.2]
    · simp
    · simp
  · by_cases hmod : n % 4 = 3
    · simp only [if_neg h4, if_pos hmod]
      refine ⟨7 :: List.replicate (n / 4 - 1) 4, ?_, ?_, ?_⟩
      · intro p hp
        simp only [List.mem_cons, List.mem_replicate] at hp
        rcases hp with rfl | ⟨_, rfl⟩ <;> decide
      · simp
        omega
      · simp
    · simp only [if_neg h4, if_neg hmod]
      refine ⟨List.replicate (n / 4) 4 ++ List.replicate (n % 4) 1, ?_, ?_, ?_⟩
      · intro p hp
        simp only [List.mem_append, List.mem_replicate] at hp
        rcases hp with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide
      · simp
        omega
      · simp

private lemma prediction_succ_le (n : ℕ) : prediction n ≤ prediction (n + 1) := by
  by_cases hlt : n + 1 < 4
  · have hn4 : n < 4 := by omega
    simp [prediction, hlt, hn4]
  · by_cases hn3 : n = 3
    · subst hn3
      decide
    · have hn4 : ¬ (n < 4) := by omega
      have hn4' : ¬ (n + 1 < 4) := hlt
      by_cases hmod3 : n % 4 = 3
      · have hmod' : (n + 1) % 4 ≠ 3 := by omega
        have hq : (n + 1) / 4 = (n / 4 - 1) + 2 := by omega
        simp only [prediction, if_neg hn4, if_neg hn4', if_pos hmod3, if_neg hmod', hq]
        rw [Nat.pow_succ, Nat.pow_succ]
        calc
          7 * 4 ^ (n / 4 - 1) ≤ 16 * 4 ^ (n / 4 - 1) :=
            Nat.mul_le_mul_right _ (by decide)
          _ = 4 ^ (n / 4 - 1) * 4 * 4 := by
            rw [Nat.mul_comm 16, Nat.mul_assoc]
      · by_cases hmod2 : n % 4 = 2
        · have hmod' : (n + 1) % 4 = 3 := by omega
          have hq1 : n / 4 = (n / 4 - 1) + 1 := by omega
          have hq2 : (n + 1) / 4 - 1 = n / 4 - 1 := by omega
          simp only [prediction, if_neg hn4, if_neg hn4', if_neg hmod3, if_pos hmod', hq2]
          rw [hq1, Nat.pow_succ, Nat.mul_comm (4 ^ (n / 4 - 1)) 4]
          exact Nat.mul_le_mul_right _ (by decide)
        · have hmod' : (n + 1) % 4 ≠ 3 := by omega
          have hq : (n + 1) / 4 = n / 4 := by omega
          simp [prediction, hn4, hn4', hmod3, hmod', hq]

private lemma prediction_mono {a b : ℕ} (h : a ≤ b) : prediction a ≤ prediction b := by
  induction b with
  | zero =>
    have ha : a = 0 := by omega
    subst ha
    exact Nat.le_refl _
  | succ b ih =>
    rcases Nat.eq_or_lt_of_le h with rfl | hlt
    · exact Nat.le_refl _
    · exact Nat.le_trans (ih (by omega)) (prediction_succ_le b)

private lemma four_mul_prediction_le (m : ℕ) : 4 * prediction m ≤ prediction (m + 4) := by
  by_cases hm4 : m < 4
  · rcases (by omega : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3) with rfl | rfl | rfl | rfl <;> decide
  · have hm4' : ¬ (m + 4 < 4) := by omega
    by_cases hmod : m % 4 = 3
    · have hmod' : (m + 4) % 4 = 3 := by omega
      have hq : (m + 4) / 4 - 1 = (m / 4 - 1) + 1 := by omega
      simp only [prediction, if_neg hm4, if_neg hm4', if_pos hmod, if_pos hmod', hq]
      rw [Nat.pow_succ, Nat.mul_left_comm, Nat.mul_comm 4 (4 ^ (m / 4 - 1))]
      exact Nat.le_refl _
    · have hmod' : (m + 4) % 4 ≠ 3 := by omega
      have hq : (m + 4) / 4 = m / 4 + 1 := by omega
      simp only [prediction, if_neg hm4, if_neg hm4', if_neg hmod, if_neg hmod', hq]
      rw [Nat.pow_succ, Nat.mul_comm]
      exact Nat.le_refl _

private lemma pow_four_mul_prediction_le (q m : ℕ) :
    4 ^ q * prediction m ≤ prediction (4 * q + m) := by
  induction q generalizing m with
  | zero => simp
  | succ q ih =>
    calc
      4 ^ (q + 1) * prediction m = 4 ^ q * (4 * prediction m) := by
        rw [Nat.pow_succ, Nat.mul_assoc]
      _ ≤ 4 ^ q * prediction (m + 4) :=
        Nat.mul_le_mul_left _ (four_mul_prediction_le m)
      _ ≤ prediction (4 * q + (m + 4)) := ih (m + 4)
      _ = prediction (4 * (q + 1) + m) := by
        have : 4 * q + (m + 4) = 4 * (q + 1) + m := by omega
        rw [this]

private lemma seven_mul_prediction_le (m : ℕ) : 7 * prediction m ≤ prediction (m + 7) := by
  by_cases hm4 : m < 4
  · rcases (by omega : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3) with rfl | rfl | rfl | rfl <;> decide
  · have hm4' : ¬ (m + 7 < 4) := by omega
    by_cases h0 : m % 4 = 0
    · have hmod : m % 4 ≠ 3 := by omega
      have hmod' : (m + 7) % 4 = 3 := by omega
      have hq : (m + 7) / 4 - 1 = m / 4 := by omega
      simp only [prediction, if_neg hm4, if_neg hm4', if_neg hmod, if_pos hmod', hq]
      exact Nat.le_refl _
    · by_cases h3 : m % 4 = 3
      · have hmod' : (m + 7) % 4 ≠ 3 := by omega
        have hq : (m + 7) / 4 = (m / 4 - 1) + 3 := by omega
        simp only [prediction, if_neg hm4, if_neg hm4', if_pos h3, if_neg hmod', hq]
        rw [Nat.pow_succ, Nat.pow_succ, Nat.pow_succ]
        calc
          7 * (7 * 4 ^ (m / 4 - 1)) = 49 * 4 ^ (m / 4 - 1) := by
            rw [← Nat.mul_assoc]
          _ ≤ 64 * 4 ^ (m / 4 - 1) := Nat.mul_le_mul_right _ (by decide)
          _ = 4 ^ (m / 4 - 1) * 4 * 4 * 4 := by
            rw [Nat.mul_comm 64, Nat.mul_assoc, Nat.mul_assoc]
      · have hmod' : (m + 7) % 4 ≠ 3 := by omega
        have hq : (m + 7) / 4 = m / 4 + 2 := by omega
        simp only [prediction, if_neg hm4, if_neg hm4', if_neg h3, if_neg hmod', hq]
        rw [Nat.pow_succ, Nat.pow_succ]
        calc
          7 * 4 ^ (m / 4) ≤ 16 * 4 ^ (m / 4) := Nat.mul_le_mul_right _ (by decide)
          _ = 4 ^ (m / 4) * 4 * 4 := by
            rw [Nat.mul_comm 16, Nat.mul_assoc]

private lemma four_mul_add_three_le_pow (q : ℕ) (hq : 2 ≤ q) : 4 * q + 3 ≤ 4 ^ q := by
  induction q with
  | zero => omega
  | succ q ih =>
    rcases Nat.eq_or_lt_of_le hq with h2 | hgt
    · have : q = 1 := by omega
      subst this
      decide
    · have hih := ih (by omega)
      have hpow : 1 ≤ 4 ^ q := Nat.one_le_pow _ _ (by decide)
      rw [Nat.pow_succ]
      omega

private lemma le_four_pow_div_four {p : ℕ} (hp : 8 ≤ p) : p ≤ 4 ^ (p / 4) := by
  have hq : 2 ≤ p / 4 := by omega
  have hbound := four_mul_add_three_le_pow (p / 4) hq
  omega

private lemma step_mul_prediction_le {p : ℕ} (hp : p % 3 = 1) (m : ℕ) :
    p * prediction m ≤ prediction (p + m) := by
  by_cases hp8 : 8 ≤ p
  · calc
      p * prediction m ≤ 4 ^ (p / 4) * prediction m :=
        Nat.mul_le_mul_right _ (le_four_pow_div_four hp8)
      _ ≤ prediction (4 * (p / 4) + m) := pow_four_mul_prediction_le (p / 4) m
      _ ≤ prediction (p + m) := prediction_mono (by omega)
  · have hcases : p = 1 ∨ p = 4 ∨ p = 7 := by omega
    rcases hcases with rfl | rfl | rfl
    · simpa using prediction_mono (Nat.le_add_left m 1)
    · simpa [Nat.add_comm] using four_mul_prediction_le m
    · simpa [Nat.add_comm] using seven_mul_prediction_le m

private lemma prod_le_prediction_sum (parts : List ℕ) (hparts : ∀ p ∈ parts, p % 3 = 1) :
    parts.prod ≤ prediction parts.sum := by
  induction parts with
  | nil =>
    simp [prediction]
  | cons p ps ih =>
    have hp : p % 3 = 1 := hparts p (by simp)
    have hps : ∀ q ∈ ps, q % 3 = 1 := fun q hq => hparts q (by simp [hq])
    calc
      (p :: ps).prod = p * ps.prod := by simp
      _ ≤ p * prediction ps.sum := Nat.mul_le_mul_left _ (ih hps)
      _ ≤ prediction (p + ps.sum) := step_mul_prediction_le hp ps.sum
      _ = prediction (p :: ps).sum := by simp

theorem main_proof : ∀ n : ℕ, 1 ≤ n → IsGreatest (products n) (prediction n) := by
  intro n _
  refine ⟨prediction_in_products n, ?_⟩
  rintro v ⟨parts, hparts, rfl, rfl⟩
  exact prod_le_prediction_sum parts hparts

end OMA.S_oeis_a128939.Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a128939.main :=
  OMA.S_oeis_a128939.Proof.main_proof
