import OMAStatements.S_oeis_a398563
import Mathlib

/-!
# A bound for semiprime differences of prime cubes

Source: https://oeis.org/A398563
Credit: @cheniverse

If the smaller primes in twin pairs are bounded by B, then a semiprime
difference p³ − q³ is at most (B + 3)³. For p > 3, the prime gap and the
cofactor both exceed one, so semiprimality forces the gap to be prime.
-/

open ArithmeticFunction

theorem OMA.solution : type_of% @OMA.S_oeis_a398563.main := by
  intro twins
  obtain ⟨B, hB⟩ := twins.bddAbove
  have bound (r : ℕ) (hr : r.Prime) (hr' : (r + 2).Prime) : r ≤ B := hB ⟨hr, hr'⟩
  apply (Set.finite_Iic ((B + 3) ^ 3)).subset
  rintro _ ⟨⟨_, count⟩, p, q, hp, hq, hqp, rfl⟩
  apply (Nat.sub_le _ _).trans
  apply Nat.pow_le_pow_left
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hqp.le
  by_cases small : q + d ≤ 3
  · omega
  have oddp := hp.eq_two_or_odd.resolve_left (by omega)
  have gap : 1 < d := by
    rcases hq.eq_two_or_odd with h | h <;> omega
  let cofactor := d ^ 2 + 3 * q * (q + d)
  have large : 1 < cofactor := by
    dsimp [cofactor]
    nlinarith
  have factor : (q + d) ^ 3 - q ^ 3 = d * cofactor := by
    apply Nat.sub_eq_of_eq_add
    dsimp [cofactor]
    ring
  rw [factor, cardFactors_mul (by omega) (by omega)] at count
  have primeGap : d.Prime := cardFactors_eq_one_iff_prime.mp (by
    have := cardFactors_pos_iff_one_lt.mpr gap
    have := cardFactors_pos_iff_one_lt.mpr large
    omega)
  rcases hq.eq_two_or_odd with rfl | oddq
  · have := bound d primeGap (by simpa only [Nat.add_comm] using hp)
    omega
  · have : d = 2 := by rcases primeGap.eq_two_or_odd with h | h <;> omega
    subst d
    have := bound q hq hp
    omega
