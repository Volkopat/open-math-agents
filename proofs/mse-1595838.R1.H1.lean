import OMAReductions.R_mse_1595838_R1

-- Step mse-1595838.R1.H1 of reduction mse-1595838.R1
-- Credit: @grp06
-- Source for the problem and divisibility argument:
-- https://math.stackexchange.com/questions/1595838

theorem OMA.solution : OMA.R_mse_1595838_R1.H1 := by
  intro n m hn hnm hdiv
  obtain ⟨k, hfib⟩ := Nat.fib_dvd n m hdiv
  obtain ⟨q, hmul⟩ := hdiv
  have hq : 2 ≤ q := by
    by_contra! h
    have hbound : n * q ≤ n * 1 :=
      Nat.mul_le_mul_left n (by omega)
    rw [Nat.mul_one, ← hmul] at hbound
    omega
  have hindex : n + 2 ≤ m := by
    have hbound := Nat.mul_le_mul_left n hq
    rw [← hmul, Nat.mul_two] at hbound
    omega
  have hprev : 0 < Nat.fib (n - 1) := Nat.fib_pos.mpr (by omega)
  have hgrowth : Nat.fib n * 2 < Nat.fib m := by
    apply lt_of_lt_of_le _ (Nat.fib_mono hindex)
    rw [Nat.fib_add_two, Nat.fib_add_one (n := n) (by omega), Nat.mul_two]
    omega
  have hk : 2 < k := by
    by_contra! h
    have hbound := Nat.mul_le_mul_left (Nat.fib n) h
    rw [← hfib] at hbound
    omega
  have hktot : 2 ≤ k.totient := by
    have hpos : 0 < k.totient := Nat.totient_pos.mpr (by omega)
    by_contra! h
    have heq : k.totient = 1 := by omega
    rcases Nat.totient_eq_one_iff.mp heq with h | h <;> omega
  have hpos : 0 < (Nat.fib n).totient :=
    Nat.totient_pos.mpr (Nat.fib_pos.mpr (by omega))
  apply ne_of_lt
  calc
    (Nat.fib n).totient < (Nat.fib n).totient * 2 := by
      rw [Nat.mul_two]
      omega
    _ ≤ (Nat.fib n).totient * k.totient :=
      Nat.mul_le_mul_left _ hktot
    _ ≤ (Nat.fib m).totient := by
      rw [hfib]
      exact Nat.totient_super_multiplicative (Nat.fib n) k
