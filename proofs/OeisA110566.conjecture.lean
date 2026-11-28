import FormalConjectures.OEIS.«110566»
import Mathlib.NumberTheory.Harmonic.Int
import Mathlib.Data.Nat.Factorization.Basic

/-! The odd number 81 never occurs in OEIS A110566 via 3-adic valuations of harmonic numbers. -/

private lemma rem (n : ℕ) : 0 ≤ padicValRat 3 (harmonic n - harmonic (n / 3) / 3) := by
  induction n with
  | zero => simp
  | succ n ih =>
    by_cases hd : 3 ∣ n + 1
    · have hn : (n + 1 : ℚ) = 3 * ((n / 3 : ℕ) + 1 : ℚ) := by
        exact_mod_cast (by omega : n + 1 = 3 * (n / 3 + 1))
      rw [show (n + 1) / 3 = n / 3 + 1 by omega, harmonic_succ, harmonic_succ]
      convert ih using 1; congr 1; push_cast; rw [hn, mul_inv_rev]; ring
    · rw [show (n + 1) / 3 = n / 3 by omega, harmonic_succ,
        show harmonic n + ((n + 1 : ℕ) : ℚ)⁻¹ - harmonic (n / 3) / 3 =
          (harmonic n - harmonic (n / 3) / 3) + ((n + 1 : ℕ) : ℚ)⁻¹ by ring]
      by_cases hz : (harmonic n - harmonic (n / 3) / 3) + ((n + 1 : ℕ) : ℚ)⁻¹ = 0
      · rw [hz]; simp
      · refine le_trans (le_min ih ?_) (padicValRat.min_le_padicValRat_add hz)
        rw [padicValRat.inv, padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hd]; simp

private lemma bnd (n : ℕ) (hn : 27 ≤ n) : padicValRat 3 (harmonic n) + Nat.log 3 n ≤ 3 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h81 : n < 81
    · interval_cases n <;> decide +kernel
    have prev := ih (n / 3) (by omega) (by omega)
    have lg : 3 ≤ Nat.log 3 (n / 3) := Nat.le_log_of_pow_le (by decide) (by omega)
    have qpos := (harmonic_pos (by omega : n / 3 ≠ 0)).ne'
    have hv : padicValRat 3 (harmonic (n / 3) / 3) = padicValRat 3 (harmonic (n / 3)) - 1 := by
      rw [padicValRat.div qpos (by norm_num), show padicValRat 3 3 = 1 by decide +kernel]
    let R := harmonic n - harmonic (n / 3) / 3
    have he : harmonic n = harmonic (n / 3) / 3 + R := by dsimp [R]; ring
    have vr : 0 ≤ padicValRat 3 R := rem n
    have step : padicValRat 3 (harmonic n) = padicValRat 3 (harmonic (n / 3)) - 1 := by
      rw [he]; by_cases hz : R = 0
      · simpa [hz] using hv
      · rw [padicValRat.add_eq_of_lt (he ▸ (harmonic_pos (by omega : n ≠ 0)).ne')
          (div_ne_zero qpos (by norm_num)) hz (by omega), hv]
    have := Nat.log_div_base 3 n
    omega

private lemma lcm_d (n : ℕ) :
    let L := (Finset.Icc 1 n).lcm id
    (harmonic n).den ∣ L ∧ L ≠ 0 ∧ padicValNat 3 L = Nat.log 3 n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rcases ih with ⟨hd, hz, hv⟩
    rw [← Finset.insert_Icc_right_eq_Icc_add_one (by omega), Finset.lcm_insert]
    refine ⟨?_, Nat.lcm_ne_zero (Nat.succ_ne_zero n) hz, ?_⟩
    · rw [harmonic_succ]
      refine (Rat.add_den_dvd_lcm _ _).trans (Nat.lcm_dvd (hd.trans (Nat.dvd_lcm_right _ _)) ?_)
      rw [Rat.den_inv_of_ne_zero (by positivity : ((n + 1 : ℕ) : ℚ) ≠ 0)]
      exact Nat.dvd_lcm_left _ _
    · have hp : Nat.Prime 3 := by decide
      change padicValNat 3 (Nat.lcm (n + 1) _) = _
      rw [← Nat.factorization_def _ hp, Nat.factorization_lcm (by omega) hz, Finsupp.sup_apply,
        Nat.factorization_def _ hp, Nat.factorization_def _ hp, hv, max_comm]
      exact Nat.max_log_padicValNat_succ_eq_log_succ n

theorem OMA.disproof : ¬ (type_of% @OeisA110566.conjecture) := by
  intro all
  obtain ⟨n, _, eq⟩ := all 81 (by decide)
  obtain ⟨dvd, _, vL⟩ := lcm_d n
  have val := congrArg (padicValNat 3) eq
  rw [OeisA110566.a, padicValNat.div_of_dvd dvd, vL, show padicValNat 3 81 = 4 by decide +kernel] at val
  by_cases sm : n < 27
  · have := Nat.log_mono_right (b := 3) (by omega : n ≤ 26)
    have : Nat.log 3 26 = 2 := by decide
    omega
  · have h := bnd n (by omega); rw [padicValRat_def] at h; omega
