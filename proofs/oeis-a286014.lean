import OMAStatements.S_oeis_a286014

namespace OMA.P_oeis_a286014

open OMA.S_oeis_a286014

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

/-- For fixed `k >= 1`, the inner sum over `m` is the entry of A211343. -/
lemma inner (n k : ℕ) (hk : 1 ≤ k) :
    (∑ m ∈ Finset.range (n + 1), if (consecParts m k).sum = n then m + 1 else 0) =
      A211343 n k := by
  simp only [sum_eq, A211343]
  set t := k * (k + 1) / 2 with htdef
  have hfilter : ∀ m, (k * m + t = n) ↔ ((t ≤ n ∧ (n - t) % k = 0) ∧ m = (n - t) / k) := by
    intro m
    constructor
    · intro h
      have h' : n - t = k * m := by omega
      refine ⟨⟨by omega, ?_⟩, ?_⟩
      · rw [h']; exact Nat.mul_mod_right k m
      · rw [h', Nat.mul_div_cancel_left m (by omega)]
    · rintro ⟨⟨h0, h1⟩, rfl⟩
      have := Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h1)
      omega
  have hsum : (∑ m ∈ Finset.range (n + 1), if k * m + t = n then m + 1 else 0) =
      ∑ m ∈ Finset.range (n + 1),
        if (t ≤ n ∧ (n - t) % k = 0) ∧ m = (n - t) / k then (n - t) / k + 1 else 0 := by
    apply Finset.sum_congr rfl
    intro m _
    by_cases h : k * m + t = n
    · rw [if_pos h, if_pos ((hfilter m).mp h), ((hfilter m).mp h).2]
    · rw [if_neg h, if_neg (fun h' => h ((hfilter m).mpr h'))]
  rw [hsum]
  by_cases hd : t ≤ n ∧ (n - t) % k = 0
  · simp only [hd, true_and, and_self]
    rw [Finset.sum_ite_eq' (Finset.range (n + 1)) ((n - t) / k) (fun _ => (n - t) / k + 1)]
    have hmem : (n - t) / k ∈ Finset.range (n + 1) := by
      rw [Finset.mem_range]
      have : (n - t) / k ≤ n - t := Nat.div_le_self _ _
      omega
    rw [if_pos hmem, if_pos trivial]
  · rw [if_neg hd]
    apply Finset.sum_eq_zero
    intro m _
    rw [if_neg]
    rintro ⟨h, -⟩
    exact hd h

end OMA.P_oeis_a286014

open OMA.P_oeis_a286014 in
theorem OMA.solution : type_of% @OMA.S_oeis_a286014.main := by
  intro n hn
  unfold OMA.S_oeis_a286014.a OMA.S_oeis_a286014.rowSum
  rw [Finset.sum_filter, Finset.sum_product_right, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_Icc] at hk
  rw [inner n k hk.1]
  by_cases ht : k * (k + 1) / 2 ≤ n
  · rw [if_pos ht]
  · rw [if_neg ht, OMA.S_oeis_a286014.A211343, if_neg (fun h => ht h.1)]
