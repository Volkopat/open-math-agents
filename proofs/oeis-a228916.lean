import OMAStatements.S_oeis_a228916
import Mathlib

namespace A228916H

open OMA.S_oeis_a228916

theorem u_rec (n : ℕ) : u (n + 2) = 3 * u (n + 1) + u n := rfl

theorem u_period (m : ℕ) :
    u (m + 12) % 10 = u m % 10 ∧ u (m + 13) % 10 = u (m + 1) % 10 := by
  induction m with
  | zero => decide
  | succ k ih =>
    have h1 : u (k + 14) = 3 * u (k + 13) + u (k + 12) := u_rec (k + 12)
    have h2 : u (k + 2) = 3 * u (k + 1) + u k := u_rec k
    show u (k + 13) % 10 = u (k + 1) % 10 ∧ u (k + 14) % 10 = u (k + 2) % 10
    exact ⟨ih.2, by omega⟩

theorem u_mod12 (q r : ℕ) : u (r + 12 * q) % 10 = u r % 10 := by
  induction q with
  | zero => simp
  | succ q ih =>
    have e : r + 12 * (q + 1) = (r + 12 * q) + 12 := by ring
    rw [e, (u_period _).1, ih]

theorem u_mod (m : ℕ) : u m % 10 = u (m % 12) % 10 := by
  have h := u_mod12 (m / 12) (m % 12)
  rwa [Nat.mod_add_div] at h

theorem u_small : ∀ r, r < 12 →
    (r % 3 = 2 → u r % 10 % 2 = 0) ∧ (r % 3 = 1 → u r % 10 % 5 = 0) := by
  decide

theorem u_le_succ (n : ℕ) : u n ≤ u (n + 1) := by
  cases n with
  | zero => decide
  | succ k =>
    have h := u_rec k
    show u (k + 1) ≤ u (k + 2)
    omega

theorem u_mono : Monotone u := monotone_nat_of_le_succ u_le_succ

theorem key (m : ℕ) (hp : (u m).Prime) : m = 1 ∨ 3 ∣ m := by
  have hm := u_mod m
  have hr := u_small (m % 12) (Nat.mod_lt _ (by norm_num))
  rcases (by omega : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2) with h | h | h
  · right
    exact Nat.dvd_of_mod_eq_zero h
  · by_cases hm1 : m = 1
    · left
      exact hm1
    · exfalso
      have h4 : 4 ≤ m := by omega
      have hge : u 4 ≤ u m := u_mono h4
      have hu4 : u 4 = 175 := by decide
      have h5' := hr.2 (by omega)
      have h5 : 5 ∣ u m := by omega
      rcases hp.eq_one_or_self_of_dvd 5 h5 with h' | h' <;> omega
  · exfalso
    have h2 : 2 ≤ m := by omega
    have hge : u 2 ≤ u m := u_mono h2
    have hu2 : u 2 = 16 := by decide
    have h2' := hr.1 (by omega)
    have h2d : 2 ∣ u m := by omega
    rcases hp.eq_one_or_self_of_dvd 2 h2d with h' | h' <;> omega

end A228916H

theorem OMA.solution : type_of% @OMA.S_oeis_a228916.main := by
  intro n hn
  show 3 ∣ Nat.nth (fun m => (OMA.S_oeis_a228916.u m).Prime) (n - 1)
  have h0 : ¬ (fun m => (OMA.S_oeis_a228916.u m).Prime) 0 := by
    show ¬ (OMA.S_oeis_a228916.u 0).Prime
    exact Nat.not_prime_one
  by_cases hk : Nat.nth (fun m => (OMA.S_oeis_a228916.u m).Prime) (n - 1) = 0
  · rw [hk]
    exact dvd_zero 3
  · have hf := Nat.lt_card_toFinset_of_nth_ne_zero hk
    have hlt := Nat.nth_lt_nth' (p := fun m => (OMA.S_oeis_a228916.u m).Prime)
      (show 0 < n - 1 by omega) hf
    have hmem := Nat.nth_mem_of_ne_zero hk
    rcases A228916H.key _ hmem with h1 | h3
    · exfalso
      have hz : Nat.nth (fun m => (OMA.S_oeis_a228916.u m).Prime) 0 = 0 := by omega
      exact hk (Nat.nth_eq_zero_mono h0 (Nat.zero_le _) hz)
    · exact h3
