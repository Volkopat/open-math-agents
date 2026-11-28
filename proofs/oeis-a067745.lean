import OMAStatements.S_oeis_a067745

-- Problem: A067745, the numerator of (3n-2)/(n^(2n-1)(2n-1)4^(n-1)) is the odd part of 3n-2.
-- Credit: @ShoQo
-- Proof (after Robert Israel's sketch in the entry): write 3n-2 = 2^v * o with o odd.
-- o is coprime to n (a common factor divides 3n - (3n-2) = 2), to 2n-1 (since
-- 3(2n-1) - 2(3n-2) = 1) and to 4, and 2^v <= 3n-2 <= 4^(n-1), so 2^v cancels into the
-- denominator and o / (D / 2^v) is already in lowest terms.

open OMA.S_oeis_a067745 in
theorem OMA.solution : type_of% @OMA.S_oeis_a067745.main := by
  intro n hn
  show ((3 * (n : ℚ) - 2) / ((n : ℚ) ^ (2 * n - 1) * (2 * (n : ℚ) - 1) * 4 ^ (n - 1))).num
    = (oddPart (3 * n - 2) : ℤ)
  set N := 3 * n - 2 with hNdef
  set v := N.factorization 2
  set o := N / 2 ^ v
  have hN0 : N ≠ 0 := by omega
  have hNo : 2 ^ v * o = N := Nat.ordProj_mul_ordCompl_eq_self N 2
  have ho2 : Nat.Coprime 2 o := Nat.coprime_ordCompl Nat.prime_two hN0
  have hodvd : o ∣ N := ⟨2 ^ v, by rw [mul_comm]; exact hNo.symm⟩
  -- the odd part is coprime to each factor of the denominator
  have hcop_n : Nat.Coprime o n := by
    rw [Nat.Coprime]
    set g := Nat.gcd o n
    have hgN : g ∣ N := (Nat.gcd_dvd_left o n).trans hodvd
    have hgn : g ∣ n := Nat.gcd_dvd_right o n
    have hg2 : g ∣ 2 := by
      have : 2 = 3 * n - N := by omega
      rw [this]; exact Nat.dvd_sub (Dvd.dvd.mul_left hgn 3) hgN
    have hgo : Nat.Coprime 2 g := Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_left o n) ho2
    rcases (Nat.dvd_prime Nat.prime_two).mp hg2 with h | h
    · exact h
    · rw [h] at hgo; norm_num at hgo
  have hcop_m : Nat.Coprime o (2 * n - 1) := by
    refine Nat.Coprime.coprime_dvd_left hodvd ?_
    rw [Nat.Coprime]
    set g := Nat.gcd N (2 * n - 1)
    have h1 : g ∣ 3 * (2 * n - 1) - 2 * N :=
      Nat.dvd_sub (Dvd.dvd.mul_left (Nat.gcd_dvd_right _ _) 3)
        (Dvd.dvd.mul_left (Nat.gcd_dvd_left _ _) 2)
    rwa [show 3 * (2 * n - 1) - 2 * N = 1 by omega, Nat.dvd_one] at h1
  have hcop_4 : Nat.Coprime o 4 := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num]; exact Nat.Coprime.pow_right 2 ho2.symm
  set D := n ^ (2 * n - 1) * (2 * n - 1) * 4 ^ (n - 1)
  have hcopD : Nat.Coprime o D :=
    Nat.Coprime.mul_right (Nat.Coprime.mul_right (Nat.Coprime.pow_right _ hcop_n) hcop_m)
      (Nat.Coprime.pow_right _ hcop_4)
  -- 2^v ≤ N ≤ 4^(n-1), so 2^v divides 4^(n-1)
  have hgrow : ∀ m : ℕ, 3 * m + 1 ≤ 4 ^ m := by
    intro m; induction m with
    | zero => simp
    | succ m ih => rw [pow_succ]; omega
  have hvle : 2 ^ v ≤ 2 ^ (2 * (n - 1)) := by
    calc 2 ^ v ≤ N := Nat.le_of_dvd (by omega) ⟨o, hNo.symm⟩
      _ ≤ 4 ^ (n - 1) := by have := hgrow (n - 1); omega
      _ = 2 ^ (2 * (n - 1)) := by rw [pow_mul]; norm_num
  have hvdvd : 2 ^ v ∣ D := by
    refine Dvd.dvd.mul_left ?_ _
    rw [show (4 : ℕ) ^ (n - 1) = 2 ^ (2 * (n - 1)) by rw [pow_mul]; norm_num]
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mpr
      ((Nat.pow_le_pow_iff_right (by norm_num)).mp hvle)
  obtain ⟨D', hD'⟩ := hvdvd
  have hD'pos : 0 < D' := by
    rcases Nat.eq_zero_or_pos D' with h | h
    · exfalso; rw [h, mul_zero] at hD'
      have : 0 < D :=
        Nat.mul_pos (Nat.mul_pos (pow_pos (by omega) _) (by omega)) (pow_pos (by norm_num) _)
      omega
    · exact h
  have hcopD' : Nat.Coprime o D' := Nat.Coprime.coprime_dvd_right ⟨2 ^ v, by rw [hD']; ring⟩ hcopD
  -- rewrite the rational as o / D'
  have hq : (3 * (n : ℚ) - 2) / ((n : ℚ) ^ (2 * n - 1) * (2 * (n : ℚ) - 1) * 4 ^ (n - 1))
      = ((o : ℤ) : ℚ) / ((D' : ℤ) : ℚ) := by
    have hNq : (3 * (n : ℚ) - 2) = ((2 ^ v * o : ℕ) : ℚ) := by
      rw [hNo, hNdef]; push_cast [show 2 ≤ 3 * n by omega]; ring
    have hDq : (n : ℚ) ^ (2 * n - 1) * (2 * (n : ℚ) - 1) * 4 ^ (n - 1) = ((2 ^ v * D' : ℕ) : ℚ) := by
      rw [← hD']
      show _ = ((n ^ (2 * n - 1) * (2 * n - 1) * 4 ^ (n - 1) : ℕ) : ℚ)
      push_cast [show 1 ≤ 2 * n by omega]; ring
    rw [hNq, hDq]; push_cast
    have : (2 : ℚ) ^ v ≠ 0 := by positivity
    field_simp
  rw [hq, Rat.num_div_eq_of_coprime (by exact_mod_cast hD'pos) (by simpa using hcopD')]
  rfl

