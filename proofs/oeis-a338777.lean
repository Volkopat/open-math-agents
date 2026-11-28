import OMAStatements.S_oeis_a338777

namespace OMA.P_oeis_a338777

open OMA.S_oeis_a338777

/-- Every element `p` of `GB (2 * n)` (with `n ≥ 3`) gives a Goldbach partition
`2 * n = (2 * n - p) + p`: the complement `2 * n - p ≥ n` has no prime factor
`≤ sqrt(2 * n)`, so it is prime. -/
theorem gb_partition {n p : ℕ} (hn : 3 ≤ n) (hp : p ∈ GB (2 * n)) :
    p.Prime ∧ (2 * n - p).Prime ∧ p ≤ n := by
  unfold GB at hp
  rw [Finset.mem_filter, Finset.mem_Icc] at hp
  obtain ⟨⟨_, hhi⟩, hpr, hq⟩ := hp
  have hpn : p ≤ n := by omega
  refine ⟨hpr, ?_, hpn⟩
  by_contra hr
  have hr0 : 0 < 2 * n - p := by omega
  have hr1 : 2 * n - p ≠ 1 := by omega
  have hqp : (Nat.minFac (2 * n - p)).Prime := Nat.minFac_prime hr1
  have hsq : (Nat.minFac (2 * n - p)) ^ 2 ≤ 2 * n - p := Nat.minFac_sq_le_self hr0 hr
  have hle : Nat.minFac (2 * n - p) ≤ Nat.sqrt (2 * n) := by
    rw [Nat.le_sqrt']
    exact le_trans hsq (by omega)
  apply hq (Nat.minFac (2 * n - p)) (Finset.mem_range.mpr (by omega)) hqp
  have hd : (Nat.minFac (2 * n - p) : ℤ) ∣ ((2 * n - p : ℕ) : ℤ) :=
    Int.natCast_dvd_natCast.mpr (Nat.minFac_dvd _)
  have heq : (p : ℤ) - ((2 * n : ℕ) : ℤ) = -((2 * n - p : ℕ) : ℤ) := by omega
  rw [heq]
  exact Dvd.dvd.mul_left (dvd_neg.mpr hd) _

end OMA.P_oeis_a338777

open OMA.S_oeis_a338777 OMA.P_oeis_a338777 in
theorem OMA.solution : type_of% @OMA.S_oeis_a338777.main := by
  have part1 : ∀ n : ℕ, 3 ≤ n → a n ≠ 1 →
      ∃ m ∈ GB (2 * n), (∀ p ∈ GB (2 * n), p ≤ m) ∧
        (2 * n - m).Prime ∧ m.Prime ∧ (2 * n - m) + m = 2 * n := by
    intro n hn ha
    have hne : (GB (2 * n)).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro h
      apply ha
      unfold a
      rw [h, Finset.prod_empty]
    refine ⟨(GB (2 * n)).max' hne, Finset.max'_mem _ hne,
      fun p hp => Finset.le_max' _ p hp, ?_⟩
    obtain ⟨h1, h2, h3⟩ := gb_partition hn (Finset.max'_mem _ hne)
    exact ⟨h2, h1, by omega⟩
  refine ⟨part1, ?_⟩
  intro hall m hm hev
  obtain ⟨k, hk⟩ := hev
  by_cases h4 : m = 4
  · exact ⟨2, 2, Nat.prime_two, Nat.prime_two, by omega⟩
  · obtain ⟨x, _, _, hx, hy, hs⟩ := part1 k (by omega) (hall k (by omega))
    exact ⟨2 * k - x, x, hx, hy, by omega⟩
