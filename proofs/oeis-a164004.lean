import OMAStatements.S_oeis_a164004
import Mathlib

-- Proof of Colin Barker's conjectures in OEIS A164004 (statement by @ivillar).
-- Idea: for n ≥ 2 the numbers j < n(n+3) with A033676(j) = n are exactly n^2, n^2+n, n^2+2n
-- (a divisor e > n of such j would have e^2 > j), and A033676(n(n+3)) = n since n+1 cannot divide
-- n(n+3) = (n+1)(n+2) - 2; so the 4th term of column n is n(n+3). Column 1 starts 1, 2, 3, 5.

namespace OMAA164004Helpers

open OMA.S_oeis_a164004

theorem d_eq_iff (j n : ℕ) (hj : 1 ≤ j) :
    d j = n ↔ (n ∣ j ∧ n * n ≤ j ∧ ∀ e, e ∣ j → e * e ≤ j → e ≤ n) := by
  have hne : (j.divisors.filter (fun e => e * e ≤ j)).Nonempty :=
    ⟨1, by simp [Finset.mem_filter, Nat.mem_divisors]; omega⟩
  constructor
  · intro h
    obtain ⟨e, he, hsup⟩ := Finset.exists_mem_eq_sup _ hne id
    have hen : e = n := by rw [← h]; exact hsup.symm
    subst hen
    simp only [Finset.mem_filter, Nat.mem_divisors] at he
    refine ⟨he.1.1, he.2, fun e' h1 h2 => ?_⟩
    rw [← h]
    exact Finset.le_sup (f := id) (by simp [Finset.mem_filter, Nat.mem_divisors, h1, h2]; omega)
  · rintro ⟨h1, h2, h3⟩
    apply le_antisymm
    · apply Finset.sup_le
      intro e he
      simp only [Finset.mem_filter, Nat.mem_divisors] at he
      exact h3 e he.1.1 he.2
    · exact Finset.le_sup (f := id) (by simp [Finset.mem_filter, Nat.mem_divisors, h1, h2]; omega)

theorem d_top (n : ℕ) (hn : 2 ≤ n) : d (n * (n + 3)) = n := by
  rw [d_eq_iff _ _ (by nlinarith)]
  refine ⟨dvd_mul_right _ _, by nlinarith, fun e h1 h2 => ?_⟩
  by_contra hlt
  push Not at hlt
  have he : e ≤ n + 1 := by nlinarith
  have heq : e = n + 1 := by omega
  subst heq
  have h3 : (n + 1) ∣ (n + 1) * (n + 2) := dvd_mul_right _ _
  have h4 : (n + 1) * (n + 2) = n * (n + 3) + 2 := by ring
  rw [h4] at h3
  have h5 : (n + 1) ∣ 2 := (Nat.dvd_add_right h1).mp h3
  have := Nat.le_of_dvd (by norm_num) h5
  omega

theorem filt (n : ℕ) (hn : 2 ≤ n) :
    (Finset.range (n * (n + 3))).filter (fun j => d j = n) = {n * n, n * n + n, n * n + 2 * n} := by
  ext j
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hj, hd⟩
    have hj1 : 1 ≤ j := by
      rcases Nat.eq_zero_or_pos j with h | h
      · subst h; simp [d] at hd; omega
      · exact h
    rw [d_eq_iff _ _ hj1] at hd
    obtain ⟨⟨t, rfl⟩, h2, -⟩ := hd
    have ht1 : n ≤ t := by nlinarith
    have ht2 : t < n + 3 := by nlinarith
    rcases (show t = n ∨ t = n + 1 ∨ t = n + 2 by omega) with h | h | h <;> subst h
    · left; ring
    · right; left; ring
    · right; right; ring
  · intro h
    have key : ∀ t, n ≤ t → t ≤ n + 2 → d (n * t) = n := by
      intro t h1 h2
      rw [d_eq_iff _ _ (by nlinarith)]
      refine ⟨dvd_mul_right _ _, by nlinarith, fun e _ he => ?_⟩
      by_contra hlt
      push Not at hlt
      nlinarith
    rcases h with rfl | rfl | rfl
    · exact ⟨by nlinarith, key n le_rfl (by omega)⟩
    · refine ⟨by nlinarith, ?_⟩
      rw [show n * n + n = n * (n + 1) by ring]; exact key (n + 1) (by omega) (by omega)
    · refine ⟨by nlinarith, ?_⟩
      rw [show n * n + 2 * n = n * (n + 2) by ring]; exact key (n + 2) (by omega) (by omega)

theorem a_big (n : ℕ) (hn : 2 ≤ n) : a n = n * (n + 3) := by
  unfold a
  rw [if_neg (by omega)]
  have hc : Nat.count (fun j => d j = n) (n * (n + 3)) = 3 := by
    rw [Nat.count_eq_card_filter_range, filt n hn]
    rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        constructor <;> intro h <;> nlinarith),
      Finset.card_insert_of_notMem (by
        simp only [Finset.mem_singleton]
        intro h; nlinarith), Finset.card_singleton]
  have := Nat.nth_count (p := fun j => d j = n) (d_top n hn)
  rw [hc] at this
  exact this

theorem a_one : a 1 = 5 := by
  unfold a
  rw [if_neg (by omega)]
  have h5 : d 5 = 1 := by decide
  have hc : Nat.count (fun j => d j = 1) 5 = 3 := by decide
  have := Nat.nth_count (p := fun j => d j = 1) h5
  rw [hc] at this
  exact this

theorem a0 : a 0 = 0 := by simp [a]

theorem key : PowerSeries.mk (fun n => (a n : ℚ)) * ((PowerSeries.X - 1) ^ 3) =
    PowerSeries.X * (PowerSeries.X ^ 3 - 3 * PowerSeries.X ^ 2 + 5 * PowerSeries.X - 5) := by
  set F := PowerSeries.mk (fun n => (a n : ℚ))
  have e1 : F * ((PowerSeries.X - 1) ^ 3) =
      PowerSeries.X ^ 3 * F - PowerSeries.C (3 : ℚ) * (PowerSeries.X ^ 2 * F) +
        PowerSeries.C (3 : ℚ) * (PowerSeries.X ^ 1 * F) - F := by
    simp only [map_ofNat]
    ring
  have e2 : (PowerSeries.X * (PowerSeries.X ^ 3 - 3 * PowerSeries.X ^ 2 + 5 * PowerSeries.X - 5) :
      PowerSeries ℚ) = PowerSeries.X ^ 4 - PowerSeries.C (3 : ℚ) * PowerSeries.X ^ 3 +
        PowerSeries.C (5 : ℚ) * PowerSeries.X ^ 2 - PowerSeries.C (5 : ℚ) * PowerSeries.X ^ 1 := by
    simp only [map_ofNat]
    ring
  rw [e1, e2]
  have v2 := a_big 2 (by norm_num)
  have v3 := a_big 3 (by norm_num)
  have v4 := a_big 4 (by norm_num)
  ext n
  simp only [F, map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk,
    PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow]
  by_cases hn : n ≤ 4
  · interval_cases n <;> simp [a0, a_one, v2, v3, v4] <;> norm_num
  · obtain ⟨j, rfl⟩ : ∃ j, n = j + 5 := ⟨n - 5, by omega⟩
    have h5 := a_big (j + 5) (by omega)
    have h4 := a_big (j + 4) (by omega)
    have h3 := a_big (j + 3) (by omega)
    have h2 := a_big (j + 2) (by omega)
    simp [show j + 5 - 3 = j + 2 by omega, show j + 5 - 2 = j + 3 by omega,
      show j + 5 - 1 = j + 4 by omega, h5, h4, h3, h2]
    ring

end OMAA164004Helpers

open OMA.S_oeis_a164004 OMAA164004Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a164004.main := by
  refine ⟨fun n hn => ?_, fun n hn => ?_, ?_⟩
  · rw [a_big n hn]; ring
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
    rw [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega, show m + 5 - 3 = m + 2 by omega,
      a_big (m + 5) (by omega), a_big (m + 4) (by omega), a_big (m + 3) (by omega),
      a_big (m + 2) (by omega)]
    push_cast
    ring
  · rw [G, PowerSeries.eq_mul_inv_iff_mul_eq (by simp), key]
