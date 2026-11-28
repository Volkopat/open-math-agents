import OMAStatements.S_oeis_a236326
import Mathlib

namespace OMA.A236326Proof

open OMA.S_oeis_a236326 PowerSeries

lemma sp_step (c : ℕ → ℤ) (x₀ : ℤ) (k j : ℕ) :
    startPt c x₀ (k + (j + 1)) = 2 * c (k + j) - startPt c x₀ (k + j) := rfl

lemma sp_period (c : ℕ → ℤ) (hc : ∀ k, c (k + 5) = c k) (x₀ : ℤ) (k : ℕ) :
    startPt c x₀ (k + 10) = startPt c x₀ k := by
  have s0 := sp_step c x₀ k 0
  have s1 := sp_step c x₀ k 1
  have s2 := sp_step c x₀ k 2
  have s3 := sp_step c x₀ k 3
  have s4 := sp_step c x₀ k 4
  have s5 := sp_step c x₀ k 5
  have s6 := sp_step c x₀ k 6
  have s7 := sp_step c x₀ k 7
  have s8 := sp_step c x₀ k 8
  have s9 := sp_step c x₀ k 9
  have c0 := hc k
  have c1 := hc (k + 1)
  have c2 := hc (k + 2)
  have c3 := hc (k + 3)
  have c4 := hc (k + 4)
  simp only [Nat.reduceAdd, add_zero, Nat.add_assoc] at *
  linarith

lemma center_per (k : ℕ) : center (k + 5) = center k := by
  unfold center
  have : (k + 5) % 5 = k % 5 := by omega
  rw [this]

lemma pos_per (k : ℕ) : pos (k + 10) = pos k := sp_period center center_per 2 k

lemma radius_per (k : ℕ) : radius (k + 10) = radius k := by
  unfold radius
  have : center (k + 10) = center k := by
    have := center_per (k + 5)
    rw [show k + 5 + 5 = k + 10 from rfl] at this
    rw [this, center_per]
  rw [pos_per, this]

lemma win (j : ℕ) : ∑ i ∈ Finset.range 10, radius (j + i) = 24 := by
  induction j with
  | zero => decide +kernel
  | succ j ih =>
    rw [← ih]
    have e1 : ∑ i ∈ Finset.range 10, radius (j + i) =
        ∑ i ∈ Finset.range 9, radius (j + (i + 1)) + radius (j + 0) :=
      Finset.sum_range_succ' (fun i => radius (j + i)) 9
    have e2 : ∑ i ∈ Finset.range 10, radius (j + 1 + i) =
        ∑ i ∈ Finset.range 9, radius (j + 1 + i) + radius (j + 1 + 9) :=
      Finset.sum_range_succ (fun i => radius (j + 1 + i)) 9
    have e3 : ∑ i ∈ Finset.range 9, radius (j + 1 + i) = ∑ i ∈ Finset.range 9, radius (j + (i + 1)) :=
      Finset.sum_congr rfl (fun i _ => by rw [show j + 1 + i = j + (i + 1) by omega])
    have e4 : radius (j + 1 + 9) = radius (j + 0) := by
      rw [show j + 1 + 9 = j + 10 by omega, radius_per]; rfl
    rw [e2, e3, e4, e1]

lemma a_step (n : ℕ) : a (n + 5) = a n + 24 := by
  unfold a
  rw [show 2 * (n + 5) = 2 * n + 10 by ring, Finset.sum_range_add, win]

lemma a_form (n : ℕ) : a n = 3 * (n : ℤ) + 4 * ((n / 5 : ℕ) : ℤ) + 4 * (((n + 1) / 5 : ℕ) : ℤ) + (((n + 2) / 5 : ℕ) : ℤ) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h : n < 5
    · interval_cases n <;> decide +kernel
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
      rw [a_step, ih m (by omega)]
      push_cast
      omega


lemma perm_per (σ : Equiv.Perm (Fin 5)) (k : ℕ) : permCenter σ (k + 5) = permCenter σ k := by
  have h : (⟨(k + 5) % 5, Nat.mod_lt _ (by norm_num)⟩ : Fin 5) = ⟨k % 5, Nat.mod_lt _ (by norm_num)⟩ :=
    Fin.ext (by simp)
  unfold permCenter
  rw [h]

lemma part1 : ∀ σ : Equiv.Perm (Fin 5), ∀ x₀ : ℤ, ∃ p : ℕ, 0 < p ∧ ∀ k : ℕ,
      startPt (permCenter σ) x₀ (k + p) = startPt (permCenter σ) x₀ k ∧
        permCenter σ (k + p) = permCenter σ k ∧ (k + p) % 2 = k % 2 := by
  intro σ x₀
  refine ⟨10, by norm_num, fun k => ⟨sp_period _ (perm_per σ) x₀ k, ?_, by omega⟩⟩
  have := perm_per σ (k + 5)
  rw [show k + 5 + 5 = k + 10 from rfl] at this
  rw [this, perm_per]

lemma part2 : ∀ n : ℕ, 7 ≤ n → a n = a (n - 1) + a (n - 5) - a (n - 6) := by
  intro n hn
  rw [a_form n, a_form (n - 1), a_form (n - 5), a_form (n - 6)]
  push_cast
  omega

lemma hb (k : ℕ) (hk : 1 ≤ k) : (if k = 0 then (0 : ℚ) else (a k : ℚ)) = a k := if_neg (by omega)

lemma part3 :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
        ((X - 1) ^ 2 * (X ^ 4 + X ^ 3 + X ^ 2 + X + 1)) =
      X * (7 * X ^ 4 + 7 * X ^ 3 + 4 * X ^ 2 + 3 * X + 3) := by
  have hD : ((X - 1) ^ 2 * (X ^ 4 + X ^ 3 + X ^ 2 + X + 1) : PowerSeries ℚ) = X ^ 6 - X ^ 5 - X ^ 1 + 1 := by ring
  have hN : (X * (7 * X ^ 4 + 7 * X ^ 3 + 4 * X ^ 2 + 3 * X + 3) : PowerSeries ℚ) =
      C (3:ℚ) * X ^ 1 + C (3:ℚ) * X ^ 2 + C (4:ℚ) * X ^ 3 + C (7:ℚ) * X ^ 4 + C (7:ℚ) * X ^ 5 := by
    simp only [map_ofNat]; ring
  rw [hD, hN]
  ext n
  simp only [mul_sub, mul_add, mul_one, map_sub, map_add, coeff_mul_X_pow', coeff_C_mul, coeff_X_pow, coeff_mk]
  by_cases hn : n ≤ 6
  · interval_cases n <;> simp [a_form] <;> norm_num
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
    have h6 := hb (m + 7 - 6) (by omega)
    have h5 := hb (m + 7 - 5) (by omega)
    have h1 := hb (m + 7 - 1) (by omega)
    have h0 := hb (m + 7) (by omega)
    have := part2 (m + 7) (by omega)
    have hq : ((a (m + 7) : ℤ) : ℚ) = a (m + 7 - 1) + a (m + 7 - 5) - a (m + 7 - 6) := by exact_mod_cast this
    simp [if_pos (show 6 ≤ m + 7 by omega), if_pos (show 5 ≤ m + 7 by omega), if_pos (show 1 ≤ m + 7 by omega)]
    have hq' : ((a (m + 7) : ℤ) : ℚ) = a (m + 6) + a (m + 2) - a (m + 1) := by simpa using hq
    linarith

end OMA.A236326Proof

open OMA.A236326Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a236326.main :=
  ⟨part1, part2, part3, fun n _ => a_form n⟩

