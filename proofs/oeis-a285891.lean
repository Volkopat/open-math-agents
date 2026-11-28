import OMAStatements.S_oeis_a285891

namespace OMA.P_oeis_a285891

open OMA.S_oeis_a285891

lemma sum_two (m k : ℕ) : (consecParts m k).sum * 2 = k * (2 * m + k + 1) := by
  induction k with
  | zero => simp [consecParts]
  | succ k ih =>
    have : consecParts m (k + 1) = consecParts m k ++ [m + 1 + k] := by
      simp [consecParts, List.range_succ]
    rw [this, List.sum_append, List.sum_singleton, add_mul, ih]
    ring

lemma tri_two (k : ℕ) : k * (k + 1) / 2 * 2 = k * (k + 1) := by
  have : 2 ∣ k * (k + 1) := (Nat.even_mul_succ_self k).two_dvd
  exact Nat.div_mul_cancel this

lemma sum_eq (m k : ℕ) : (consecParts m k).sum = k * m + k * (k + 1) / 2 := by
  have h1 := sum_two m k
  have h2 := tri_two k
  have : (consecParts m k).sum * 2 = (k * m + k * (k + 1) / 2) * 2 := by
    rw [h1, add_mul, h2]; ring
  omega

end OMA.P_oeis_a285891

open OMA.P_oeis_a285891 in
theorem OMA.solution : type_of% @OMA.S_oeis_a285891.main := by
  intro n k hn hk ht
  simp only [OMA.S_oeis_a285891.T, OMA.S_oeis_a285891.A237048, sum_eq]
  set t := k * (k + 1) / 2 with htdef
  have hfilter : ∀ m, (k * m + t = n) ↔ ((n - t) % k = 0 ∧ m = (n - t) / k) := by
    intro m
    constructor
    · intro h
      have : n - t = k * m := by omega
      rw [this]
      refine ⟨Nat.mul_mod_right k m, ?_⟩
      rw [Nat.mul_div_cancel_left m (by omega)]
    · rintro ⟨h1, rfl⟩
      have := Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h1)
      omega
  have hsum : (∑ m ∈ Finset.range (n + 1), if k * m + t = n then k * m + t else 0) =
      ∑ m ∈ Finset.range (n + 1), if (n - t) % k = 0 ∧ m = (n - t) / k then n else 0 := by
    apply Finset.sum_congr rfl
    intro m _
    by_cases h : k * m + t = n
    · rw [if_pos h, if_pos ((hfilter m).mp h), h]
    · rw [if_neg h, if_neg (fun h' => h ((hfilter m).mpr h'))]
  rw [hsum]
  by_cases hd : (n - t) % k = 0
  · simp only [hd, true_and]
    rw [Finset.sum_ite_eq' (Finset.range (n + 1)) ((n - t) / k) (fun _ => n)]
    have hmem : (n - t) / k ∈ Finset.range (n + 1) := by
      rw [Finset.mem_range]
      have : (n - t) / k ≤ n - t := Nat.div_le_self _ _
      omega
    rw [if_pos hmem, if_pos ⟨ht, trivial⟩, mul_one]
  · simp [hd]
