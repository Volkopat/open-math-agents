import OMAStatements.S_oeis_a140869

-- Problem oeis-a140869: with T(m, n) = floor((2mn + m + n - 2)/2), if h is not of the form T(m, n) with
-- m >= n >= 1, then 4h + 5 is prime.
-- Upstream: statements/oeis-a140869.lean (declaration OMA.S_oeis_a140869.main)
-- Credit: @cclyles (the owner of the agent is credited as the solver)
--
-- Contrapositive. If 4h + 5 is not prime, write it as a * b with a its least prime factor, so a <= b.
-- Both factors are odd, say a = 2n + 1 and b = 2m + 1 with 1 <= n <= m. Expanding the product gives
-- 2mn + m + n = 2h + 2, hence T(m, n) = h.

theorem OMA.solution : type_of% @OMA.S_oeis_a140869.main := by
  intro h hns
  by_contra hnp
  apply hns
  have hpr : (4 * h + 5).minFac.Prime := Nat.minFac_prime (by omega)
  have hdiv := Nat.minFac_dvd (4 * h + 5)
  have hle0 := Nat.minFac_le_div (by omega : 0 < 4 * h + 5) hnp
  generalize (4 * h + 5).minFac = a at hpr hdiv hle0
  obtain ⟨b, hb⟩ := hdiv
  have hle : a ≤ b := by
    rw [Nat.div_eq_of_eq_mul_right hpr.pos hb] at hle0
    exact hle0
  have hodd : Odd (a * b) := by
    rw [← hb]
    exact ⟨2 * h + 2, by ring⟩
  obtain ⟨⟨n, hn⟩, ⟨m, hm⟩⟩ := Nat.odd_mul.mp hodd
  have hn1 : 1 ≤ n := by
    have := hpr.two_le
    omega
  refine ⟨m, n, hn1, by omega, ?_⟩
  unfold OMA.S_oeis_a140869.T
  have key : 2 * m * n + m + n = 2 * h + 2 := by
    rw [hn, hm] at hb
    nlinarith [hb]
  rw [key]
  omega
