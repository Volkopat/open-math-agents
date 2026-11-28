import OMAStatements.S_oeis_a156834

namespace BC4E

open OMA.S_oeis_a156834

theorem choose_ge_two {m k : ℕ} (hk : 1 ≤ k) (hkm : k < m) : 2 ≤ m.choose k := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  first
  | rw [Nat.choose_succ_succ']
  | rw [Nat.choose_succ_succ]
  have h1 : 0 < m'.choose k' := Nat.choose_pos (by omega)
  have h2 : 0 < m'.choose (k' + 1) := Nat.choose_pos (by omega)
  have h3 : 0 < m'.choose k'.succ := Nat.choose_pos (by omega)
  omega

theorem a_prime {p : ℕ} (hp : p.Prime) : a p = p := by
  have h2 := hp.two_le
  unfold a
  rw [hp.divisors, Finset.sum_pair (by omega : (1 : ℕ) ≠ p)]
  rw [Nat.div_one, Nat.div_self hp.pos, Nat.totient_one, Nat.totient_prime hp]
  rw [show 1 + p - 2 = p - 1 by omega, show p + 1 - 2 = p - 1 by omega, Nat.sub_self,
    Nat.choose_zero_right, Nat.choose_self]
  omega

theorem a_gt {n : ℕ} (hn : 1 < n) (hnp : ¬ n.Prime) : n < a n := by
  obtain ⟨d, hdn, hd2, hdlt⟩ := Nat.exists_dvd_of_not_prime2 (by omega) hnp
  have hsum : ∑ m ∈ n.divisors, m.totient = n := Nat.sum_totient n
  unfold a
  calc n = ∑ m ∈ n.divisors, m.totient := hsum.symm
    _ < ∑ m ∈ n.divisors, m.totient * (m + n / m - 2).choose (m - 1) := by
      apply Finset.sum_lt_sum
      · intro m hm
        have hm' := Nat.mem_divisors.mp hm
        have hmpos : 0 < m := Nat.pos_of_mem_divisors hm
        have hq : 0 < n / m := Nat.div_pos (Nat.le_of_dvd (by omega) hm'.1) hmpos
        have hc : 0 < (m + n / m - 2).choose (m - 1) := Nat.choose_pos (by omega)
        exact Nat.le_mul_of_pos_right _ hc
      · refine ⟨d, Nat.mem_divisors.mpr ⟨hdn, by omega⟩, ?_⟩
        have he : 2 ≤ n / d := by
          obtain ⟨e, he⟩ := hdn
          rw [he, Nat.mul_div_cancel_left e (by omega)]
          by_contra h
          have h' : e < 2 := by omega
          interval_cases e <;> omega
        have hc : 2 ≤ (d + n / d - 2).choose (d - 1) := choose_ge_two (by omega) (by omega)
        have ht : 0 < d.totient := by
          first
          | exact Nat.totient_pos.mpr (by omega)
          | exact Nat.totient_pos (by omega)
        calc d.totient < d.totient * 2 := by omega
          _ ≤ d.totient * (d + n / d - 2).choose (d - 1) := Nat.mul_le_mul_left _ hc

end BC4E

theorem OMA.solution : type_of% @OMA.S_oeis_a156834.main := by
  intro n hn
  constructor
  · intro h
    by_contra hnp
    have h' := BC4E.a_gt hn hnp
    omega
  · intro hp
    exact BC4E.a_prime hp
