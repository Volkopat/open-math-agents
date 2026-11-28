import OMAStatements.S_oeis_a126156
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

namespace OeisA126156Proof

open OMA.S_oeis_a126156

/-- Pure-integer recurrence for OEIS A126156 (equivalent to Tani Akinari's formula
`a(n) = ∑_{k=1}^n a(n-k) * C(2n, 2k) * (k/(2n) - 1) * (-2)^k`). -/
def aSeq : ℕ → ℤ
  | 0 => 1
  | n + 1 =>
    ∑ k : Fin (n + 1),
      (-1 : ℤ) ^ k.1 * (2 : ℤ) ^ k.1 *
        (2 * (Nat.choose (2 * n + 1) (2 * k.1 + 2) : ℤ) +
          (Nat.choose (2 * n + 1) (2 * k.1 + 1) : ℤ)) *
        aSeq (n - k.1)
termination_by n => n

private lemma aSeq_zero : aSeq 0 = 1 := by
  rw [aSeq]

private lemma aSeq_one : aSeq 1 = 1 := by
  rw [aSeq, Fin.sum_univ_one]
  simp [aSeq_zero]

private lemma choose_two_mul_two (m : ℕ) : 2 * Nat.choose (m + 1) 2 = (m + 1) * m := by
  have h := Nat.choose_two_right (m + 1)
  have h2 : 2 ∣ (m + 1) * m := by
    rcases Nat.even_or_odd m with ⟨r, hr⟩ | ⟨r, hr⟩
    · refine ⟨(m + 1) * r, ?_⟩; rw [hr]; ring
    · refine ⟨(r + 1) * m, ?_⟩; rw [hr]; ring
  rw [h]
  exact Nat.mul_div_cancel' h2

private lemma choose_three_mul_six (m : ℕ) :
    6 * Nat.choose (m + 2) 3 = (m + 2) * (m + 1) * m := by
  have h := Nat.descFactorial_eq_factorial_mul_choose (m + 2) 3
  have h3 : (3 : ℕ).factorial = 6 := by decide
  rw [h3] at h
  rw [← h]
  simp only [Nat.descFactorial_succ, Nat.descFactorial_zero, mul_one, Nat.sub_zero,
    show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega]
  ring

private lemma choose_odd_three_mod_two (n : ℕ) :
    Nat.choose (2 * n + 3) 3 % 2 = (n + 1) % 2 := by
  have h6 := choose_three_mul_six (2 * n + 1)
  have h23 : 2 * n + 1 + 2 = 2 * n + 3 := by omega
  have h22 : 2 * n + 1 + 1 = 2 * (n + 1) := by omega
  rw [h23, h22] at h6
  have h3 : 3 * Nat.choose (2 * n + 3) 3 = (2 * n + 3) * (n + 1) * (2 * n + 1) := by
    linarith
  have hmod : (3 * Nat.choose (2 * n + 3) 3) % 2 = ((2 * n + 3) * (n + 1) * (2 * n + 1)) % 2 := by
    rw [h3]
  have hlhs : (3 * Nat.choose (2 * n + 3) 3) % 2 = Nat.choose (2 * n + 3) 3 % 2 := by
    rw [Nat.mul_mod]; simp
  have hrhs : ((2 * n + 3) * (n + 1) * (2 * n + 1)) % 2 = (n + 1) % 2 := by
    rw [Nat.mul_mod, Nat.mul_mod (2 * n + 3)]
    have h1 : (2 * n + 3) % 2 = 1 := by omega
    have h2 : (2 * n + 1) % 2 = 1 := by omega
    rw [h1, h2]
    simp
  omega

private lemma aSeq_rec_mod_four (n : ℕ) :
    aSeq (n + 2) ≡ aSeq (n + 1) + 2 * ((n + 1 : ℕ) : ℤ) * aSeq n [ZMOD 4] := by
  rw [aSeq, Fin.sum_univ_succ, Fin.sum_univ_succ]
  -- Term k = 0
  have ht0 :
      (-1 : ℤ) ^ (0 : Fin (n + 2)).1 * (2 : ℤ) ^ (0 : Fin (n + 2)).1 *
          (2 * (Nat.choose (2 * (n + 1) + 1) (2 * (0 : Fin (n + 2)).1 + 2) : ℤ) +
            (Nat.choose (2 * (n + 1) + 1) (2 * (0 : Fin (n + 2)).1 + 1) : ℤ)) *
          aSeq (n + 1 - (0 : Fin (n + 2)).1) ≡
        aSeq (n + 1) [ZMOD 4] := by
    simp only [Fin.val_zero, pow_zero, one_mul, mul_zero, zero_add, Nat.sub_zero,
      Nat.choose_one_right]
    have hc2 : 2 * (Nat.choose (2 * n + 3) 2 : ℤ) = ((2 * n + 3 : ℕ) : ℤ) * ((2 * n + 2 : ℕ) : ℤ) := by
      exact_mod_cast choose_two_mul_two (2 * n + 2)
    have hrew : 2 * (Nat.choose (2 * (n + 1) + 1) 2 : ℤ) + ((2 * (n + 1) + 1 : ℕ) : ℤ) =
        4 * (((n : ℤ) + 1) * ((n : ℤ) + 2)) + 1 := by
      have h23 : 2 * (n + 1) + 1 = 2 * n + 3 := by omega
      rw [h23, hc2]
      push_cast
      ring
    rw [hrew]
    rw [Int.modEq_iff_dvd]
    refine ⟨-(((n : ℤ) + 1) * ((n : ℤ) + 2) * aSeq (n + 1)), ?_⟩
    ring
  -- Term k = 1
  have ht1 :
      (-1 : ℤ) ^ (0 : Fin (n + 1)).succ.1 * (2 : ℤ) ^ (0 : Fin (n + 1)).succ.1 *
          (2 * (Nat.choose (2 * (n + 1) + 1) (2 * (0 : Fin (n + 1)).succ.1 + 2) : ℤ) +
            (Nat.choose (2 * (n + 1) + 1) (2 * (0 : Fin (n + 1)).succ.1 + 1) : ℤ)) *
          aSeq (n + 1 - (0 : Fin (n + 1)).succ.1) ≡
        2 * ((n + 1 : ℕ) : ℤ) * aSeq n [ZMOD 4] := by
    simp only [Fin.val_succ, Fin.val_zero]
    have hsub : n + 1 - 1 = n := by omega
    have h23 : 2 * (n + 1) + 1 = 2 * n + 3 := by omega
    rw [hsub, h23]
    have hpar := choose_odd_three_mod_two n
    have hdvd : (2 : ℤ) ∣ ((Nat.choose (2 * n + 3) 3 : ℤ) + ((n + 1 : ℕ) : ℤ)) := by
      omega
    obtain ⟨q, hq⟩ := hdvd
    rw [Int.modEq_iff_dvd]
    refine ⟨q * aSeq n + (Nat.choose (2 * n + 3) 4 : ℤ) * aSeq n, ?_⟩
    have hq' : (Nat.choose (2 * n + 3) 3 : ℤ) = 2 * q - ((n + 1 : ℕ) : ℤ) := by linarith
    rw [hq']
    ring
  -- Terms k ≥ 2
  have htail :
      (∑ x : Fin n,
        (-1 : ℤ) ^ x.succ.succ.1 * (2 : ℤ) ^ x.succ.succ.1 *
          (2 * (Nat.choose (2 * (n + 1) + 1) (2 * x.succ.succ.1 + 2) : ℤ) +
            (Nat.choose (2 * (n + 1) + 1) (2 * x.succ.succ.1 + 1) : ℤ)) *
          aSeq (n + 1 - x.succ.succ.1)) ≡ 0 [ZMOD 4] := by
    rw [Int.modEq_zero_iff_dvd]
    apply Finset.dvd_sum
    intro x _
    have h4 : (4 : ℤ) ∣ (2 : ℤ) ^ x.succ.succ.1 := by
      simp only [Fin.val_succ]
      rw [pow_succ, pow_succ]
      refine ⟨(2 : ℤ) ^ x.1, ?_⟩
      ring
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right h4 _) _) _
  have hsum := (ht0.add (ht1.add htail))
  simpa [add_zero, add_assoc] using hsum

lemma aSeq_mod_four : ∀ n : ℕ, aSeq n ≡ (if n % 4 < 2 then 1 else 3) [ZMOD 4] := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 => simp [aSeq_zero, Int.ModEq]
    | 1 => simp [aSeq_one, Int.ModEq]
    | m + 2 =>
      have hrec := aSeq_rec_mod_four m
      have ih1 := ih (m + 1) (by omega)
      have ih0 := ih m (by omega)
      have hstep : aSeq (m + 2) ≡
          (if (m + 1) % 4 < 2 then (1 : ℤ) else 3) +
            2 * ((m + 1 : ℕ) : ℤ) * (if m % 4 < 2 then (1 : ℤ) else 3) [ZMOD 4] := by
        exact hrec.trans (ih1.add (ih0.mul_left _))
      have hm4 : m % 4 = 0 ∨ m % 4 = 1 ∨ m % 4 = 2 ∨ m % 4 = 3 := by omega
      rcases hm4 with h0 | h1 | h2 | h3
      · have h0a : (m + 2) % 4 = 2 := by omega
        have h0b : (m + 1) % 4 = 1 := by omega
        rw [h0a]
        rw [h0, h0b] at hstep
        simp only [show (0 : ℕ) < 2 by decide, show (1 : ℕ) < 2 by decide,
          show ¬((2 : ℕ) < 2) by decide, ↓reduceIte] at hstep ⊢
        have h2m : (2 * ((m + 1 : ℕ) : ℤ) : ℤ) ≡ 2 [ZMOD 4] := by
          rw [Int.modEq_iff_dvd]; omega
        exact hstep.trans (by
          have := (Int.ModEq.refl 1).add (h2m.mul_right 1)
          simpa using this)
      · have h1a : (m + 2) % 4 = 3 := by omega
        have h1b : (m + 1) % 4 = 2 := by omega
        rw [h1a]
        rw [h1, h1b] at hstep
        simp only [show (1 : ℕ) < 2 by decide, show ¬((2 : ℕ) < 2) by decide,
          show ¬((3 : ℕ) < 2) by decide, ↓reduceIte] at hstep ⊢
        have h2m : (2 * ((m + 1 : ℕ) : ℤ) : ℤ) ≡ 0 [ZMOD 4] := by
          rw [Int.modEq_iff_dvd]; omega
        exact hstep.trans (by
          have := (Int.ModEq.refl 3).add (h2m.mul_right 1)
          simpa using this)
      · have h2a : (m + 2) % 4 = 0 := by omega
        have h2b : (m + 1) % 4 = 3 := by omega
        rw [h2a]
        rw [h2, h2b] at hstep
        simp only [show ¬((2 : ℕ) < 2) by decide, show ¬((3 : ℕ) < 2) by decide,
          show (0 : ℕ) < 2 by decide, ↓reduceIte] at hstep ⊢
        have h2m : (2 * ((m + 1 : ℕ) : ℤ) : ℤ) ≡ 2 [ZMOD 4] := by
          rw [Int.modEq_iff_dvd]; omega
        exact hstep.trans (by
          have htmp : 3 + 2 * ((m + 1 : ℕ) : ℤ) * 3 ≡ 3 + 2 * 3 [ZMOD 4] :=
            (Int.ModEq.refl 3).add (h2m.mul_right 3)
          exact htmp.trans (by decide : (3 + 2 * 3 : ℤ) ≡ 1 [ZMOD 4]))
      · have h3a : (m + 2) % 4 = 1 := by omega
        have h3b : (m + 1) % 4 = 0 := by omega
        rw [h3a]
        rw [h3, h3b] at hstep
        simp only [show ¬((3 : ℕ) < 2) by decide, show (0 : ℕ) < 2 by decide,
          show (1 : ℕ) < 2 by decide, ↓reduceIte] at hstep ⊢
        have h2m : (2 * ((m + 1 : ℕ) : ℤ) : ℤ) ≡ 0 [ZMOD 4] := by
          rw [Int.modEq_iff_dvd]; omega
        exact hstep.trans (by
          have := (Int.ModEq.refl 1).add (h2m.mul_right 3)
          simpa using this)

/-! ### Formal power series verification that `aSeq` satisfies `A(x)^2 * cos(sqrt(2)*x) = 1` -/

private noncomputable def psDeriv (F : PowerSeries ℚ) : PowerSeries ℚ :=
  PowerSeries.mk fun n => ((n + 1 : ℕ) : ℚ) * PowerSeries.coeff (n + 1) F

private lemma coeff_psDeriv (F : PowerSeries ℚ) (n : ℕ) :
    PowerSeries.coeff n (psDeriv F) = ((n + 1 : ℕ) : ℚ) * PowerSeries.coeff (n + 1) F := by
  simp [psDeriv]

private lemma coeff_mul_range (F G : PowerSeries ℚ) (n : ℕ) :
    PowerSeries.coeff n (F * G) =
      ∑ i ∈ Finset.range (n + 1), PowerSeries.coeff i F * PowerSeries.coeff (n - i) G := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => PowerSeries.coeff i F * PowerSeries.coeff j G)]

private lemma psDeriv_mul (F G : PowerSeries ℚ) :
    psDeriv (F * G) = psDeriv F * G + F * psDeriv G := by
  ext n
  rw [coeff_psDeriv, map_add, coeff_mul_range, coeff_mul_range, coeff_mul_range]
  have h1 :
      ((n + 1 : ℕ) : ℚ) *
          ∑ i ∈ Finset.range (n + 2), PowerSeries.coeff i F * PowerSeries.coeff (n + 1 - i) G =
        (∑ i ∈ Finset.range (n + 2),
          ((i : ℚ) * PowerSeries.coeff i F * PowerSeries.coeff (n + 1 - i) G)) +
        (∑ i ∈ Finset.range (n + 2),
          (PowerSeries.coeff i F * (((n + 1 - i : ℕ) : ℚ) * PowerSeries.coeff (n + 1 - i) G))) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    have hadd : (i : ℚ) + ((n + 1 - i : ℕ) : ℚ) = ((n + 1 : ℕ) : ℚ) := by
      have : i + (n + 1 - i) = n + 1 := by omega
      exact_mod_cast this
    calc ((n + 1 : ℕ) : ℚ) * (PowerSeries.coeff i F * PowerSeries.coeff (n + 1 - i) G)
        = ((i : ℚ) + ((n + 1 - i : ℕ) : ℚ)) *
            (PowerSeries.coeff i F * PowerSeries.coeff (n + 1 - i) G) := by rw [hadd]
      _ = (i : ℚ) * PowerSeries.coeff i F * PowerSeries.coeff (n + 1 - i) G +
          PowerSeries.coeff i F * (((n + 1 - i : ℕ) : ℚ) * PowerSeries.coeff (n + 1 - i) G) := by
          ring
  rw [h1]
  congr 1
  · rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero, zero_mul, add_zero]
    apply Finset.sum_congr rfl
    intro i _
    rw [coeff_psDeriv]
    have hsub : n + 1 - (i + 1) = n - i := by omega
    rw [hsub]
  · rw [Finset.sum_range_succ]
    simp only [Nat.sub_self, Nat.cast_zero, zero_mul, mul_zero, add_zero]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    rw [coeff_psDeriv]
    have hsub : n + 1 - i = (n - i) + 1 := by omega
    rw [hsub]

private noncomputable def psA : PowerSeries ℚ :=
  PowerSeries.mk fun m => if m % 2 = 0 then (aSeq (m / 2) : ℚ) / (m.factorial : ℚ) else 0

private noncomputable def psC : PowerSeries ℚ :=
  PowerSeries.mk fun m => if m % 2 = 0 then (-2 : ℚ) ^ (m / 2) / (m.factorial : ℚ) else 0

private noncomputable def psS : PowerSeries ℚ :=
  PowerSeries.mk fun m =>
    if m % 2 = 1 then (-1 : ℚ) ^ (m / 2) * (2 : ℚ) ^ (m / 2 + 1) / (m.factorial : ℚ) else 0

private lemma psDeriv_C : psDeriv psC = -psS := by
  ext m
  rw [coeff_psDeriv, map_neg]
  simp only [psC, psS, PowerSeries.coeff_mk]
  by_cases hm : m % 2 = 1
  · have hm1 : (m + 1) % 2 = 0 := by omega
    have hdiv : (m + 1) / 2 = m / 2 + 1 := by omega
    simp only [hm, hm1, ↓reduceIte, hdiv]
    rw [Nat.factorial_succ]
    have hmne : ((m + 1 : ℕ) : ℚ) ≠ 0 := by positivity
    have hfac : (m.factorial : ℚ) ≠ 0 := by positivity
    push_cast
    field_simp
    rw [show (-2 : ℚ) = (-1 : ℚ) * 2 by ring, mul_pow]
    ring
  · have hm1 : (m + 1) % 2 ≠ 0 := by omega
    simp [hm, hm1]

private lemma choose_mul_fact_rat (n k : ℕ) (hk : k ≤ n) :
    (Nat.choose n k : ℚ) * (k.factorial : ℚ) * ((n - k).factorial : ℚ) = (n.factorial : ℚ) := by
  have h := Nat.choose_mul_factorial_mul_factorial hk
  exact_mod_cast h

private lemma two_derivA_mul_C : 2 * psDeriv psA * psC = psA * psS := by
  ext m
  rw [mul_assoc, show PowerSeries.coeff m (2 * (psDeriv psA * psC)) =
      2 * PowerSeries.coeff m (psDeriv psA * psC) by
      rw [show (2 : PowerSeries ℚ) = PowerSeries.C 2 from rfl, PowerSeries.coeff_C_mul]]
  rw [coeff_mul_range, coeff_mul_range]
  rcases Nat.even_or_odd m with ⟨n, rfl⟩ | ⟨n, rfl⟩
  · -- m = n + n (even): both sides are 0
    have hlhs : ∑ i ∈ Finset.range (n + n + 1),
        PowerSeries.coeff i (psDeriv psA) * PowerSeries.coeff (n + n - i) psC = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [Finset.mem_range] at hi
      rw [coeff_psDeriv]
      simp only [psA, psC, PowerSeries.coeff_mk]
      by_cases hip : i % 2 = 0
      · have hi1 : (i + 1) % 2 ≠ 0 := by omega
        simp [hi1]
      · have hni : (n + n - i) % 2 ≠ 0 := by omega
        simp [hni]
    have hrhs : ∑ i ∈ Finset.range (n + n + 1),
        PowerSeries.coeff i psA * PowerSeries.coeff (n + n - i) psS = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [Finset.mem_range] at hi
      simp only [psA, psS, PowerSeries.coeff_mk]
      by_cases hip : i % 2 = 0
      · have hni : (n + n - i) % 2 ≠ 1 := by omega
        simp [hni]
      · simp [hip]
    rw [hlhs, hrhs, mul_zero]
  · -- m = 2 * n + 1 (odd): multiply both sides by (2n + 1)!
    have hfac_ne : (((2 * n + 1).factorial : ℕ) : ℚ) ≠ 0 := by positivity
    apply mul_left_cancel₀ hfac_ne
    -- LHS scaled by (2n + 1)!
    have hL :
        (((2 * n + 1).factorial : ℕ) : ℚ) *
          (2 * ∑ i ∈ Finset.range (2 * n + 1 + 1),
            PowerSeries.coeff i (psDeriv psA) * PowerSeries.coeff (2 * n + 1 - i) psC) =
        2 * ∑ k ∈ Finset.range (n + 1),
          (Nat.choose (2 * n + 1) (2 * k) : ℚ) * (-2 : ℚ) ^ k * (aSeq (n + 1 - k) : ℚ) := by
      rw [← mul_assoc, mul_comm (((2 * n + 1).factorial : ℕ) : ℚ) 2, mul_assoc]
      congr 1
      rw [Finset.mul_sum]
      -- Use sum_filter so non-contributing even terms drop cleanly!
      have hfilt :
          ∑ i ∈ Finset.range (2 * n + 1 + 1),
            (((2 * n + 1).factorial : ℕ) : ℚ) *
              (PowerSeries.coeff i (psDeriv psA) * PowerSeries.coeff (2 * n + 1 - i) psC) =
          ∑ i ∈ (Finset.range (2 * n + 2)).filter (fun i => i % 2 = 1),
            (((2 * n + 1).factorial : ℕ) : ℚ) *
              (PowerSeries.coeff i (psDeriv psA) * PowerSeries.coeff (2 * n + 1 - i) psC) := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mem_range] at hi
        by_cases hip : i % 2 = 1
        · simp [hip]
        · have hi1 : (i + 1) % 2 ≠ 0 := by omega
          simp [hip, coeff_psDeriv, psA, hi1]
      rw [hfilt]
      symm
      apply Finset.sum_bij (fun k _ => 2 * (n - k) + 1)
      · intro k hk
        rw [Finset.mem_filter, Finset.mem_range]
        rw [Finset.mem_range] at hk
        exact ⟨by omega, by omega⟩
      · intro k1 hk1 k2 hk2 heq
        rw [Finset.mem_range] at hk1 hk2
        omega
      · intro i hi
        rw [Finset.mem_filter, Finset.mem_range] at hi
        refine ⟨(2 * n + 1 - i) / 2, Finset.mem_range.mpr (by omega), by omega⟩
      · intro k hk
        rw [Finset.mem_range] at hk
        have hsub1 : 2 * n + 1 - (2 * (n - k) + 1) = 2 * k := by omega
        have hadd1 : 2 * (n - k) + 1 + 1 = 2 * (n + 1 - k) := by omega
        rw [hsub1, coeff_psDeriv, hadd1]
        simp only [psA, psC, PowerSeries.coeff_mk, Nat.mul_mod_right, ↓reduceIte]
        have hd1 : 2 * (n + 1 - k) / 2 = n + 1 - k := by omega
        have hd2 : 2 * k / 2 = k := by omega
        rw [hd1, hd2]
        have hch := choose_mul_fact_rat (2 * n + 1) (2 * k) (by omega)
        have hsub2 : 2 * n + 1 - 2 * k = 2 * (n - k) + 1 := by omega
        rw [hsub2] at hch
        have hfac_succ : ((2 * (n + 1 - k)).factorial : ℚ) =
            ((2 * (n + 1 - k) : ℕ) : ℚ) * (((2 * (n - k) + 1).factorial : ℕ) : ℚ) := by
          have : 2 * (n + 1 - k) = (2 * (n - k) + 1) + 1 := by omega
          rw [this, Nat.factorial_succ]
          push_cast
          ring
        rw [hfac_succ, ← hch]
        have h1 : ((2 * (n + 1 - k) : ℕ) : ℚ) ≠ 0 := by
          have : 0 < 2 * (n + 1 - k) := by omega
          positivity
        have h2 : (((2 * (n - k) + 1).factorial : ℕ) : ℚ) ≠ 0 := by positivity
        have h3 : (((2 * k).factorial : ℕ) : ℚ) ≠ 0 := by positivity
        field_simp
    -- RHS scaled by (2n + 1)!
    have hR :
        (((2 * n + 1).factorial : ℕ) : ℚ) *
          ∑ i ∈ Finset.range (2 * n + 1 + 1),
            PowerSeries.coeff i psA * PowerSeries.coeff (2 * n + 1 - i) psS =
        ∑ k ∈ Finset.range (n + 1),
          (Nat.choose (2 * n + 1) (2 * k + 1) : ℚ) *
            ((-1 : ℚ) ^ k * (2 : ℚ) ^ (k + 1)) * (aSeq (n - k) : ℚ) := by
      rw [Finset.mul_sum]
      have hfilt :
          ∑ i ∈ Finset.range (2 * n + 1 + 1),
            (((2 * n + 1).factorial : ℕ) : ℚ) *
              (PowerSeries.coeff i psA * PowerSeries.coeff (2 * n + 1 - i) psS) =
          ∑ i ∈ (Finset.range (2 * n + 2)).filter (fun i => i % 2 = 0),
            (((2 * n + 1).factorial : ℕ) : ℚ) *
              (PowerSeries.coeff i psA * PowerSeries.coeff (2 * n + 1 - i) psS) := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mem_range] at hi
        by_cases hip : i % 2 = 0
        · simp [hip]
        · simp [hip, psA]
      rw [hfilt]
      symm
      apply Finset.sum_bij (fun k _ => 2 * (n - k))
      · intro k hk
        rw [Finset.mem_filter, Finset.mem_range]
        rw [Finset.mem_range] at hk
        exact ⟨by omega, by omega⟩
      · intro k1 hk1 k2 hk2 heq
        rw [Finset.mem_range] at hk1 hk2
        omega
      · intro i hi
        rw [Finset.mem_filter, Finset.mem_range] at hi
        refine ⟨(2 * n - i) / 2, Finset.mem_range.mpr (by omega), by omega⟩
      · intro k hk
        rw [Finset.mem_range] at hk
        have hsub1 : 2 * n + 1 - 2 * (n - k) = 2 * k + 1 := by omega
        rw [hsub1]
        simp only [psA, psS, PowerSeries.coeff_mk, Nat.mul_mod_right, ↓reduceIte,
          show (2 * k + 1) % 2 = 1 by omega]
        have hd1 : 2 * (n - k) / 2 = n - k := by omega
        have hd2 : (2 * k + 1) / 2 = k := by omega
        rw [hd1, hd2]
        have hch := choose_mul_fact_rat (2 * n + 1) (2 * k + 1) (by omega)
        have hsub2 : 2 * n + 1 - (2 * k + 1) = 2 * (n - k) := by omega
        rw [hsub2] at hch
        rw [← hch]
        have h2 : (((2 * (n - k)).factorial : ℕ) : ℚ) ≠ 0 := by positivity
        have h3 : (((2 * k + 1).factorial : ℕ) : ℚ) ≠ 0 := by positivity
        field_simp
    rw [hL, hR]
    -- Now split k = 0 from LHS and match with aSeq (n + 1) definition!
    rw [Finset.sum_range_succ']
    simp only [mul_zero, Nat.choose_zero_right, Nat.cast_one, pow_zero, mul_one,
      Nat.sub_zero, one_mul]
    have ha : (aSeq (n + 1) : ℚ) =
        ∑ k ∈ Finset.range (n + 1),
          (-1 : ℚ) ^ k * (2 : ℚ) ^ k *
            (2 * (Nat.choose (2 * n + 1) (2 * k + 2) : ℚ) +
              (Nat.choose (2 * n + 1) (2 * k + 1) : ℚ)) *
            (aSeq (n - k) : ℚ) := by
      conv_lhs => rw [aSeq]
      rw [Fin.sum_univ_eq_sum_range (fun k =>
        (-1 : ℤ) ^ k * (2 : ℤ) ^ k *
          (2 * (Nat.choose (2 * n + 1) (2 * k + 2) : ℤ) +
            (Nat.choose (2 * n + 1) (2 * k + 1) : ℤ)) *
          aSeq (n - k))]
      push_cast
      rfl
    rw [ha]
    have hlast :
        ∑ k ∈ Finset.range n,
          (Nat.choose (2 * n + 1) (2 * (k + 1)) : ℚ) * (-2 : ℚ) ^ (k + 1) *
            (aSeq (n + 1 - (k + 1)) : ℚ) =
        ∑ k ∈ Finset.range (n + 1),
          (Nat.choose (2 * n + 1) (2 * k + 2) : ℚ) * (-2 : ℚ) ^ (k + 1) *
            (aSeq (n - k) : ℚ) := by
      rw [Finset.sum_range_succ]
      have hzero : Nat.choose (2 * n + 1) (2 * n + 2) = 0 :=
        Nat.choose_eq_zero_of_lt (by omega)
      simp only [hzero, Nat.cast_zero, zero_mul, add_zero]
      apply Finset.sum_congr rfl
      intro k _
      have h1 : 2 * (k + 1) = 2 * k + 2 := by omega
      have h2 : n + 1 - (k + 1) = n - k := by omega
      rw [h1, h2]
    rw [hlast, mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    have hpow : (-2 : ℚ) ^ (k + 1) = -((-1 : ℚ) ^ k * (2 : ℚ) ^ (k + 1)) := by
      rw [show (-2 : ℚ) = (-1 : ℚ) * 2 by ring, mul_pow, pow_succ (-1 : ℚ)]
      ring
    rw [hpow, pow_succ (2 : ℚ) k]
    ring

private lemma psDeriv_AAC : psDeriv (psA * psA * psC) = 0 := by
  rw [psDeriv_mul, psDeriv_mul, psDeriv_C]
  calc (psDeriv psA * psA + psA * psDeriv psA) * psC + psA * psA * -psS
      = psA * (2 * psDeriv psA * psC - psA * psS) := by ring
    _ = psA * (psA * psS - psA * psS) := by rw [two_derivA_mul_C]
    _ = 0 := by ring

private lemma coeff_AAC_eq_zero (m : ℕ) (hm : 1 ≤ m) :
    PowerSeries.coeff m (psA * psA * psC) = 0 := by
  have h := congrArg (PowerSeries.coeff (m - 1)) psDeriv_AAC
  rw [coeff_psDeriv, map_zero] at h
  have hsub : m - 1 + 1 = m := by omega
  rw [hsub] at h
  have hmne : ((m : ℕ) : ℚ) ≠ 0 := by positivity
  exact (mul_eq_zero.mp h).resolve_left hmne

private lemma coeff_AA_even (r : ℕ) :
    PowerSeries.coeff (2 * r) (psA * psA) =
      (∑ j ∈ Finset.range (r + 1),
        (Nat.choose (2 * r) (2 * j) : ℚ) * (aSeq j : ℚ) * (aSeq (r - j) : ℚ)) /
        (((2 * r).factorial : ℕ) : ℚ) := by
  have hfac_ne : (((2 * r).factorial : ℕ) : ℚ) ≠ 0 := by positivity
  rw [eq_div_iff hfac_ne, mul_comm]
  rw [coeff_mul_range, Finset.mul_sum]
  have hfilt :
      ∑ i ∈ Finset.range (2 * r + 1),
        (((2 * r).factorial : ℕ) : ℚ) *
          (PowerSeries.coeff i psA * PowerSeries.coeff (2 * r - i) psA) =
      ∑ i ∈ (Finset.range (2 * r + 1)).filter (fun i => i % 2 = 0),
        (((2 * r).factorial : ℕ) : ℚ) *
          (PowerSeries.coeff i psA * PowerSeries.coeff (2 * r - i) psA) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hip : i % 2 = 0
    · simp [hip]
    · simp [hip, psA]
  rw [hfilt]
  symm
  apply Finset.sum_bij (fun j _ => 2 * j)
  · intro j hj
    rw [Finset.mem_filter, Finset.mem_range]
    rw [Finset.mem_range] at hj
    exact ⟨by omega, by omega⟩
  · intro j1 _ j2 _ heq; omega
  · intro i hi
    rw [Finset.mem_filter, Finset.mem_range] at hi
    refine ⟨i / 2, Finset.mem_range.mpr (by omega), by omega⟩
  · intro j hj
    rw [Finset.mem_range] at hj
    have hsub : 2 * r - 2 * j = 2 * (r - j) := by omega
    rw [hsub]
    simp only [psA, PowerSeries.coeff_mk, Nat.mul_mod_right, ↓reduceIte]
    have hd1 : 2 * j / 2 = j := by omega
    have hd2 : 2 * (r - j) / 2 = r - j := by omega
    rw [hd1, hd2]
    have hch := choose_mul_fact_rat (2 * r) (2 * j) (by omega)
    rw [hsub] at hch
    rw [← hch]
    have h1 : (((2 * j).factorial : ℕ) : ℚ) ≠ 0 := by positivity
    have h2 : (((2 * (r - j)).factorial : ℕ) : ℚ) ≠ 0 := by positivity
    field_simp

theorem aSeq_isA126156 : IsA126156 aSeq := by
  refine ⟨aSeq_zero, ?_⟩
  intro n hn
  have hzero : PowerSeries.coeff (2 * n) (psA * psA * psC) = 0 :=
    coeff_AAC_eq_zero (2 * n) (by omega)
  have hrat :
      (∑ k ∈ Finset.range (n + 1),
        (Nat.choose (2 * n) (2 * k) : ℚ) * (-2 : ℚ) ^ k *
          (∑ j ∈ Finset.range (n - k + 1),
            (Nat.choose (2 * (n - k)) (2 * j) : ℚ) * (aSeq j : ℚ) * (aSeq (n - k - j) : ℚ))) = 0 := by
    have hscaled : (((2 * n).factorial : ℕ) : ℚ) *
        PowerSeries.coeff (2 * n) (psA * psA * psC) = 0 := by
      rw [hzero, mul_zero]
    rw [← hscaled, coeff_mul_range, Finset.mul_sum]
    have hfilt :
        ∑ i ∈ Finset.range (2 * n + 1),
          (((2 * n).factorial : ℕ) : ℚ) *
            (PowerSeries.coeff i (psA * psA) * PowerSeries.coeff (2 * n - i) psC) =
        ∑ i ∈ (Finset.range (2 * n + 1)).filter (fun i => i % 2 = 0),
          (((2 * n).factorial : ℕ) : ℚ) *
            (PowerSeries.coeff i (psA * psA) * PowerSeries.coeff (2 * n - i) psC) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mem_range] at hi
      by_cases hip : i % 2 = 0
      · simp [hip]
      · have hni : (2 * n - i) % 2 ≠ 0 := by omega
        simp [hip, psC, hni]
    rw [hfilt]
    apply Finset.sum_bij (fun k _ => 2 * (n - k))
    · intro k hk
      rw [Finset.mem_filter, Finset.mem_range]
      rw [Finset.mem_range] at hk
      exact ⟨by omega, by omega⟩
    · intro k1 hk1 k2 hk2 heq
      rw [Finset.mem_range] at hk1 hk2
      omega
    · intro i hi
      rw [Finset.mem_filter, Finset.mem_range] at hi
      refine ⟨(2 * n - i) / 2, Finset.mem_range.mpr (by omega), by omega⟩
    · intro k hk
      rw [Finset.mem_range] at hk
      have hsub : 2 * n - 2 * (n - k) = 2 * k := by omega
      rw [hsub, coeff_AA_even (n - k)]
      simp only [psC, PowerSeries.coeff_mk, Nat.mul_mod_right, ↓reduceIte]
      have hd : 2 * k / 2 = k := by omega
      rw [hd]
      have hch := choose_mul_fact_rat (2 * n) (2 * k) (by omega)
      have hsub2 : 2 * n - 2 * k = 2 * (n - k) := by omega
      rw [hsub2] at hch
      rw [← hch]
      have h1 : (((2 * k).factorial : ℕ) : ℚ) ≠ 0 := by positivity
      have h2 : (((2 * (n - k)).factorial : ℕ) : ℚ) ≠ 0 := by positivity
      field_simp
  exact_mod_cast hrat

end OeisA126156Proof

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a126156.main) := by
  intro h
  obtain ⟨N, hN⟩ := h OeisA126156Proof.aSeq OeisA126156Proof.aSeq_isA126156 4 (by omega)
  have htot : Nat.totient 4 = 2 := by decide
  have hmod := hN N (le_refl N)
  rw [htot] at hmod
  have h1 := OeisA126156Proof.aSeq_mod_four (N + 2)
  have h2 := OeisA126156Proof.aSeq_mod_four N
  have hcontra :
      (if (N + 2) % 4 < 2 then (1 : ℤ) else 3) ≡
        (if N % 4 < 2 then (1 : ℤ) else 3) [ZMOD 4] :=
    h1.symm.trans (hmod.trans h2)
  by_cases hlt : N % 4 < 2
  · have hlt2 : ¬((N + 2) % 4 < 2) := by omega
    simp only [hlt, hlt2, ↓reduceIte] at hcontra
    exact absurd hcontra (by decide)
  · have hlt2 : (N + 2) % 4 < 2 := by omega
    simp only [hlt, hlt2, ↓reduceIte] at hcontra
    exact absurd hcontra (by decide)
