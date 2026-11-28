import OMAStatements.S_oeis_a309291

lemma fact_big (k : ℕ) (hk : 5 ≤ k) : k ^ 2 + k < Nat.factorial k := by
  induction k, hk using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    rw [Nat.factorial_succ]
    nlinarith

theorem OMA.solution : type_of% @OMA.S_oeis_a309291.main := by
  intro k hk q hq hlo hhi
  have hbig := fact_big k hk
  have hqk : k < q := by omega
  by_contra hnp
  set p := Nat.factorial k - q with hp
  have hp1 : k ≤ p := by omega
  have hp2 : p ≤ k ^ 2 := by omega
  have hpos : 0 < p := by omega
  have hp_ne1 : p ≠ 1 := by omega
  have hl := Nat.minFac_prime hp_ne1
  have hsq := Nat.minFac_sq_le_self hpos hnp
  -- the least prime factor of p is at most k, so it divides k! and hence q
  have hlk : p.minFac ≤ k := by
    by_contra h
    push Not at h
    have : k ^ 2 < p.minFac ^ 2 := Nat.pow_lt_pow_left h (by norm_num)
    omega
  have hdk : p.minFac ∣ Nat.factorial k := Nat.dvd_factorial hl.pos hlk
  have hdq : p.minFac ∣ q := by
    have : q = Nat.factorial k - p := by omega
    rw [this]
    exact Nat.dvd_sub hdk (Nat.minFac_dvd p)
  rcases (Nat.dvd_prime hq).1 hdq with h | h
  · exact hl.ne_one h
  · omega
