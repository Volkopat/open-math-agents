import OMAStatements.S_oeis_a131662
import Mathlib

-- Problem: A131662, Colin Barker's generating function and recurrence.
-- Upstream: formal-conjectures statements/oeis-a131662.lean (declaration OMA.S_oeis_a131662.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Proof: the condition is periodic modulo 27720 = lcm(1, ..., 12), with exactly the residues
-- 0, 2519, 11879, 13320, 14399, 15840, 25200, 27719 (a kernel check over the residues that are
-- 0 or -1 modulo 8 and 9), so term (8q + r + 1) = 27720 q + B r and term (k + 8) = term k + 27720.

namespace OMA.P_oeis_a131662

open OMA.S_oeis_a131662

/-- The bounded form of the divisibility condition. -/
def Qf (n : ℕ) : Prop := ∀ d, d < 13 → 1 ≤ d → d ∣ n ∨ d ∣ n + 1

instance : DecidablePred Qf := fun n => by unfold Qf; infer_instance

/-- The residues modulo 27720 = lcm(1, ..., 12) that satisfy the condition. -/
def good (s : ℕ) : Prop := s = 0 ∨ s = 2519 ∨ s = 11879 ∨ s = 13320 ∨ s = 14399 ∨ s = 15840 ∨ s = 25200 ∨ s = 27719

instance : DecidablePred good := fun s => by unfold good; infer_instance

theorem qual_iff (n : ℕ) : qualifies n ↔ 0 < n ∧ Qf n := by
  unfold qualifies Qf
  constructor
  · rintro ⟨h0, h⟩
    exact ⟨h0, fun d hd h1 => h d h1 (by omega)⟩
  · rintro ⟨h0, h⟩
    exact ⟨h0, fun d h1 h2 => h d (by omega) h1⟩

theorem Qf_periodic (q s : ℕ) : Qf (27720 * q + s) ↔ Qf s := by
  unfold Qf
  apply forall_congr'
  intro d
  apply imp_congr_right
  intro hd
  apply imp_congr_right
  intro h1
  have hdvd : d ∣ 27720 * q := by
    have : d ∣ 27720 := by
      interval_cases d <;> norm_num
    exact Dvd.dvd.mul_right this q
  rw [Nat.dvd_add_right hdvd, add_assoc, Nat.dvd_add_right hdvd]

theorem cls0 : ∀ t, t < 385 → Qf (72 * t + 0) → good (72 * t + 0) := by
  decide +kernel

theorem cls8 : ∀ t, t < 385 → Qf (72 * t + 8) → good (72 * t + 8) := by
  decide +kernel

theorem cls63 : ∀ t, t < 385 → Qf (72 * t + 63) → good (72 * t + 63) := by
  decide +kernel

theorem cls71 : ∀ t, t < 385 → Qf (72 * t + 71) → good (72 * t + 71) := by
  decide +kernel

theorem classify (s : ℕ) (hs : s < 27720) (h : Qf s) : good s := by
  have h8 := h 8 (by norm_num) (by norm_num)
  have h9 := h 9 (by norm_num) (by norm_num)
  have ht : s / 72 < 385 := by omega
  have hr : s % 72 = 0 ∨ s % 72 = 8 ∨ s % 72 = 63 ∨ s % 72 = 71 := by omega
  have e : s = 72 * (s / 72) + s % 72 := (Nat.div_add_mod s 72).symm
  rcases hr with hr | hr | hr | hr <;> rw [hr] at e <;> rw [e] at h ⊢
  · exact cls0 _ ht h
  · exact cls8 _ ht h
  · exact cls63 _ ht h
  · exact cls71 _ ht h

/-- The residues in increasing order, with 27720 in place of 0. -/
def B : ℕ → ℕ
  | 0 => 2519
  | 1 => 11879
  | 2 => 13320
  | 3 => 14399
  | 4 => 15840
  | 5 => 25200
  | 6 => 27719
  | _ => 27720

/-- The claimed enumeration of the sequence. -/
def f (n : ℕ) : ℕ := 27720 * (n / 8) + B (n % 8)

theorem f_eq (q r : ℕ) (hr : r < 8) : f (8 * q + r) = 27720 * q + B r := by
  unfold f
  rw [show (8 * q + r) / 8 = q by omega, show (8 * q + r) % 8 = r by omega]

theorem f_add8 (n : ℕ) : f (n + 8) = f n + 27720 := by
  unfold f
  rw [show (n + 8) / 8 = n / 8 + 1 by omega, show (n + 8) % 8 = n % 8 by omega]
  ring

theorem f_mono : StrictMono f := by
  apply strictMono_nat_of_lt_succ
  intro n
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 8 ∧ n = 8 * q + r :=
    ⟨n / 8, n % 8, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod n 8).symm⟩
  rw [f_eq q r hr]
  interval_cases r
  · rw [show 8 * q + 0 + 1 = 8 * q + 1 by ring, f_eq q 1 (by norm_num)]; simp [B]
  · rw [show 8 * q + 1 + 1 = 8 * q + 2 by ring, f_eq q 2 (by norm_num)]; simp [B]
  · rw [show 8 * q + 2 + 1 = 8 * q + 3 by ring, f_eq q 3 (by norm_num)]; simp [B]
  · rw [show 8 * q + 3 + 1 = 8 * q + 4 by ring, f_eq q 4 (by norm_num)]; simp [B]
  · rw [show 8 * q + 4 + 1 = 8 * q + 5 by ring, f_eq q 5 (by norm_num)]; simp [B]
  · rw [show 8 * q + 5 + 1 = 8 * q + 6 by ring, f_eq q 6 (by norm_num)]; simp [B]
  · rw [show 8 * q + 6 + 1 = 8 * q + 7 by ring, f_eq q 7 (by norm_num)]; simp [B]
  · rw [show 8 * q + 7 + 1 = 8 * (q + 1) + 0 by ring, f_eq (q + 1) 0 (by norm_num)]
    simp only [B]
    omega

theorem f_maps (n : ℕ) : qualifies (f n) := by
  rw [qual_iff]
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 8 ∧ n = 8 * q + r :=
    ⟨n / 8, n % 8, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod n 8).symm⟩
  rw [f_eq q r hr, Qf_periodic]
  interval_cases r <;> exact ⟨by simp [B], by decide⟩

theorem f_surj (m : ℕ) (hm : qualifies m) : ∃ n, f n = m := by
  rw [qual_iff] at hm
  obtain ⟨h0, hq⟩ := hm
  obtain ⟨q, s, hs, rfl⟩ : ∃ q s, s < 27720 ∧ m = 27720 * q + s :=
    ⟨m / 27720, m % 27720, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod m 27720).symm⟩
  rw [Qf_periodic] at hq
  rcases classify s hs hq with h | h | h | h | h | h | h | h <;> subst h
  · obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    exact ⟨8 * q' + 7, by rw [f_eq q' 7 (by norm_num)]; simp only [B]; ring⟩
  · exact ⟨8 * q + 0, by rw [f_eq q 0 (by norm_num)]; rfl⟩
  · exact ⟨8 * q + 1, by rw [f_eq q 1 (by norm_num)]; rfl⟩
  · exact ⟨8 * q + 2, by rw [f_eq q 2 (by norm_num)]; rfl⟩
  · exact ⟨8 * q + 3, by rw [f_eq q 3 (by norm_num)]; rfl⟩
  · exact ⟨8 * q + 4, by rw [f_eq q 4 (by norm_num)]; rfl⟩
  · exact ⟨8 * q + 5, by rw [f_eq q 5 (by norm_num)]; rfl⟩
  · exact ⟨8 * q + 6, by rw [f_eq q 6 (by norm_num)]; rfl⟩

theorem term_succ (n : ℕ) : term (n + 1) = f n := by
  show Nat.nth qualifies n = f n
  have hinf : (Set.ofPred qualifies).Infinite :=
    Set.infinite_of_injective_forall_mem f_mono.injective f_maps
  have hU : ∀ k, k ∈ {k : ℕ | ∀ hf : (Set.ofPred qualifies).Finite, k < hf.toFinset.card} :=
    fun k hf => absurd hf hinf
  refine (Nat.eq_nth_of_strictMonoOn_of_mapsTo_of_surjOn f ?_ ?_ ?_ (hU n)).symm
  · intro m hm
    obtain ⟨k, hk⟩ := f_surj m hm
    exact ⟨k, hU k, hk⟩
  · intro k _
    exact f_maps k
  · exact f_mono.strictMonoOn _

theorem term_shift (k : ℕ) (hk : 1 ≤ k) : term (k + 8) = term k + 27720 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [show j + 1 + 8 = (j + 8) + 1 by ring, term_succ, term_succ, f_add8]

theorem part2 : ∀ n : ℕ, 9 < n → term n + term (n - 9) = term (n - 1) + term (n - 8) := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 10 := ⟨n - 10, by omega⟩
  rw [show k + 10 - 9 = k + 1 by omega, show k + 10 - 1 = (k + 1) + 8 by omega,
    show k + 10 - 8 = k + 2 by omega, show k + 10 = (k + 2) + 8 by omega,
    term_shift (k + 2) (by omega), term_shift (k + 1) (by omega)]
  ring

theorem t_vals : term 0 = 0 ∧ term 1 = 2519 ∧ term 2 = 11879 ∧ term 3 = 13320 ∧
    term 4 = 14399 ∧ term 5 = 15840 ∧ term 6 = 25200 ∧ term 7 = 27719 ∧ term 8 = 27720 ∧
    term 9 = 30239 := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (rw [term_succ]; rfl)

open PowerSeries in
theorem part1 : denominator * series = numerator := by
  have hden : denominator = 1 - X ^ 1 - X ^ 8 + X ^ 9 := by
    unfold denominator
    ring
  have hnum : numerator = C (2519 : ℤ) * X ^ 1 + C (9360 : ℤ) * X ^ 2 + C (1441 : ℤ) * X ^ 3 +
      C (1079 : ℤ) * X ^ 4 + C (1441 : ℤ) * X ^ 5 + C (9360 : ℤ) * X ^ 6 +
      C (2519 : ℤ) * X ^ 7 + C (1 : ℤ) * X ^ 8 := by
    unfold numerator
    simp only [map_ofNat, map_one]
    ring
  rw [hden, hnum]
  ext n
  rw [add_mul, sub_mul, sub_mul, one_mul, mul_comm (X ^ 1), mul_comm (X ^ 8), mul_comm (X ^ 9),
    map_add, map_sub, map_sub, coeff_mul_X_pow', coeff_mul_X_pow', coeff_mul_X_pow']
  simp only [map_add, coeff_C_mul_X_pow, series, coeff_mk]
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := t_vals
  rcases Nat.lt_or_ge n 10 with h | h
  · interval_cases n <;> simp [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 10 := ⟨n - 10, by omega⟩
    simp only [show 1 ≤ k + 10 by omega, show 8 ≤ k + 10 by omega, show 9 ≤ k + 10 by omega, show k + 10 ≠ 1 by omega,
      show k + 10 ≠ 2 by omega, show k + 10 ≠ 3 by omega, show k + 10 ≠ 4 by omega,
      show k + 10 ≠ 5 by omega, show k + 10 ≠ 6 by omega, show k + 10 ≠ 7 by omega,
      show k + 10 ≠ 8 by omega, ↓reduceIte]
    rw [show k + 10 - 8 = k + 2 by omega, show k + 10 - 9 = k + 1 by omega,
      show k + 10 = (k + 2) + 8 by omega, term_shift (k + 2) (by omega),
      show k + 2 + 8 - 1 = (k + 1) + 8 by omega, term_shift (k + 1) (by omega)]
    push_cast
    ring

end OMA.P_oeis_a131662

theorem OMA.solution : type_of% @OMA.S_oeis_a131662.main :=
  ⟨OMA.P_oeis_a131662.part1, OMA.P_oeis_a131662.part2⟩
