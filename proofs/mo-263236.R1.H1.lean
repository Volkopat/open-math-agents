import OMAReductions.R_mo_263236_R1
import Mathlib

/-! Step mo-263236.R1.H1: the rows k = 1, k = n - 1 and k = n contain 2-adic integers only for
n at most 3 (harmonic numbers via Mathlib's padicValRat_two_harmonic; H n n = 1/n!;
H n (n-1) = (1 + ... + n)/n! and 2^v2(n+1) divides (n-1)!). -/

namespace OMA.P263

open Finset

theorem prod_inv_Icc (n : ℕ) : ∏ i ∈ Icc 1 n, (1 / (i : ℚ)) = 1 / (n.factorial : ℚ) := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Finset.prod_Icc_succ_top (by omega), ih, Nat.factorial_succ]
    push_cast
    field_simp

theorem two_mul_sum_Icc (n : ℕ) : 2 * ∑ i ∈ Icc 1 n, i = n * (n + 1) := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega), mul_add, ih]
    ring

theorem H_one (n : ℕ) : OMA.S_mo_263236.H n 1 = harmonic n := by
  unfold OMA.S_mo_263236.H
  rw [Finset.powersetCard_one, Finset.sum_map, harmonic_eq_sum_Icc]
  simp

theorem H_self (n : ℕ) : OMA.S_mo_263236.H n n = 1 / (n.factorial : ℚ) := by
  unfold OMA.S_mo_263236.H
  have h : (Icc 1 n).card = n := by simp
  have hs := Finset.powersetCard_self (Icc 1 n)
  rw [h] at hs
  rw [hs, Finset.sum_singleton, prod_inv_Icc]

theorem H_pred (n : ℕ) (hn : 1 ≤ n) :
    OMA.S_mo_263236.H n (n - 1) = ((∑ i ∈ Icc 1 n, i : ℕ) : ℚ) / (n.factorial : ℚ) := by
  unfold OMA.S_mo_263236.H
  have hc : (Icc 1 n).card = n := by simp
  rw [show ((∑ i ∈ Icc 1 n, i : ℕ) : ℚ) / (n.factorial : ℚ)
      = ∑ i ∈ Icc 1 n, (i : ℚ) * ∏ j ∈ Icc 1 n, (1 / (j : ℚ)) by
    rw [prod_inv_Icc, ← Finset.sum_mul]; push_cast; ring]
  symm
  refine Finset.sum_bij (fun i _ => (Icc 1 n).erase i) ?_ ?_ ?_ ?_
  · intro i hi
    rw [Finset.mem_powersetCard]
    exact ⟨Finset.erase_subset _ _, by rw [Finset.card_erase_of_mem hi, hc]⟩
  · intro i hi j hj hij
    by_contra hne
    have : j ∈ (Icc 1 n).erase i := Finset.mem_erase.mpr ⟨Ne.symm hne, hj⟩
    rw [hij] at this
    simp at this
  · intro T hT
    rw [Finset.mem_powersetCard] at hT
    have hcard : ((Icc 1 n) \ T).card = 1 := by
      rw [Finset.card_sdiff_of_subset hT.1, hT.2, hc]; omega
    obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hcard
    have hiS : i ∈ (Icc 1 n) \ T := by rw [hi]; exact Finset.mem_singleton_self i
    refine ⟨i, (Finset.mem_sdiff.mp hiS).1, ?_⟩
    ext j
    constructor
    · intro hj
      rcases Finset.mem_erase.mp hj with ⟨hji, hjs⟩
      by_contra hjT
      have : j ∈ (Icc 1 n) \ T := Finset.mem_sdiff.mpr ⟨hjs, hjT⟩
      rw [hi, Finset.mem_singleton] at this
      exact hji this
    · intro hj
      have hjs := hT.1 hj
      refine Finset.mem_erase.mpr ⟨?_, hjs⟩
      rintro rfl
      exact (Finset.mem_sdiff.mp hiS).2 hj
  · intro i hi
    have hi0 : (i : ℚ) ≠ 0 := by
      have := (Finset.mem_Icc.mp hi).1
      exact_mod_cast (show i ≠ 0 by omega)
    rw [← Finset.mul_prod_erase (Icc 1 n) (fun j => 1 / (j : ℚ)) hi]
    field_simp

/-- `2 ^ v₂(n + 1)` divides `(n - 1)!` for `n ≥ 4`. -/
theorem key_dvd (n : ℕ) (hn : 4 ≤ n) : 2 ^ padicValNat 2 (n + 1) ∣ (n - 1).factorial := by
  set d := 2 ^ padicValNat 2 (n + 1) with hd
  have hdvd : d ∣ n + 1 := pow_padicValNat_dvd
  have hpos : 0 < d := by positivity
  by_cases hle : d ≤ n - 1
  · exact Nat.dvd_factorial hpos hle
  · have hdle : d ≤ n + 1 := Nat.le_of_dvd (by omega) hdvd
    have hcase : d = n ∨ d = n + 1 := by omega
    rcases hcase with h | h
    · exfalso
      rw [h] at hdvd
      have : n ∣ 1 := (Nat.dvd_add_right (dvd_refl n)).mp hdvd
      have := Nat.le_of_dvd one_pos this
      omega
    · -- `n + 1 = 2 ^ a` with `a ≥ 3`
      set a := padicValNat 2 (n + 1) with ha
      have ha3 : 3 ≤ a := by
        by_contra hlt
        have : 2 ^ a ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      obtain ⟨b, hb'⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
      have hb4 : 4 ≤ 2 ^ b := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hdeq : d = 2 * 2 ^ b := by rw [hd, hb', pow_succ]; ring
      rw [hdeq]
      have h1 : (2 ^ b).factorial ∣ (n - 1).factorial :=
        Nat.factorial_dvd_factorial (by omega)
      have h2 : 2 * 2 ^ b ∣ (2 ^ b).factorial := by
        have e : (2 ^ b).factorial = 2 ^ b * (2 ^ b - 1).factorial :=
          (Nat.mul_factorial_pred (by omega)).symm
        rw [e, mul_comm 2 (2 ^ b)]
        exact Nat.mul_dvd_mul_left _ (Nat.dvd_factorial (by norm_num) (by omega))
      exact h2.trans h1

theorem val_factorial_pos (n : ℕ) (hn : 2 ≤ n) : 1 ≤ padicValNat 2 n.factorial := by
  have : 2 ∣ n.factorial := Nat.dvd_factorial (by norm_num) hn
  exact one_le_padicValNat_of_dvd (Nat.factorial_pos n).ne' this

theorem solution_aux : ∀ n k : ℕ, 1 ≤ k → k ≤ n → (k = 1 ∨ k + 1 = n ∨ k = n) →
    0 ≤ padicValRat 2 (OMA.S_mo_263236.H n k) → n ≤ 3 := by
  intro n k hk1 hkn hcase hv
  by_contra hn3
  rw [not_le] at hn3
  rcases hcase with rfl | h | rfl
  · rw [H_one, padicValRat_two_harmonic] at hv
    have : 1 ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num) (by omega)
    omega
  · obtain rfl : k = n - 1 := by omega
    rw [H_pred n (by omega)] at hv
    set T := ∑ i ∈ Icc 1 n, i with hT
    have hT2 := two_mul_sum_Icc n
    rw [← hT] at hT2
    have hT0 : T ≠ 0 := by
      intro h0; rw [h0] at hT2; simp at hT2; omega
    have hf0 : n.factorial ≠ 0 := (Nat.factorial_pos n).ne'
    rw [padicValRat.div (by exact_mod_cast hT0) (by exact_mod_cast hf0),
      ← padicValRat_of_nat, ← padicValRat_of_nat] at hv
    -- valuations of `2 T = n (n + 1)` and `n! = n (n - 1)!`
    have e1 : padicValNat 2 (2 * T) = 1 + padicValNat 2 T := by
      rw [padicValNat.mul (by norm_num) hT0, padicValNat.self (by norm_num)]
    have e2 : padicValNat 2 (n * (n + 1)) = padicValNat 2 n + padicValNat 2 (n + 1) :=
      padicValNat.mul (by omega) (by omega)
    have e3 : n.factorial = n * (n - 1).factorial := (Nat.mul_factorial_pred (by omega)).symm
    have e4 : padicValNat 2 n.factorial = padicValNat 2 n + padicValNat 2 (n - 1).factorial := by
      rw [e3, padicValNat.mul (by omega) (Nat.factorial_pos _).ne']
    have hkey : padicValNat 2 (n + 1) ≤ padicValNat 2 (n - 1).factorial :=
      (padicValNat_dvd_iff_le (Nat.factorial_pos _).ne').mp (key_dvd n (by omega))
    rw [hT2] at e1
    omega
  · rw [H_self, one_div, padicValRat.inv, ← padicValRat_of_nat] at hv
    have := val_factorial_pos k (by omega)
    omega

end OMA.P263

theorem OMA.solution : OMA.R_mo_263236_R1.H1 := OMA.P263.solution_aux
