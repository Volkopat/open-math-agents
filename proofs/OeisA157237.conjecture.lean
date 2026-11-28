import FormalConjectures.OEIS.«157237»

/-!
A counterexample to the conjecture of Z.-W. Sun recorded in OEIS A157237.

The odd number `667623212539751 = 2 * 333811606269876 - 1` cannot be written as
`p + 2 ^ x + 11 * 2 ^ y` with `p` a prime congruent to `1` modulo `6` and `x, y ≥ 1`:
for every pair `(x, y)` with `2 ^ x + 11 * 2 ^ y < 667623212539751` the difference is either
not congruent to `1` modulo `6` or has the explicit proper divisor listed in the table `W`.
Hence `a 333811606269876 = 0`, although `333811606269876` is not one of the listed exceptions.
-/

namespace SunEleven

/-- Boolean certificate check for one pair of exponents, given a claimed proper divisor `d`. -/
def chk (N x y d : ℕ) : Bool :=
  decide (N ≤ 2 ^ x + 11 * 2 ^ y) || decide ((N - (2 ^ x + 11 * 2 ^ y)) % 6 ≠ 1) ||
    (decide (1 < d) && decide (d < N - (2 ^ x + 11 * 2 ^ y)) &&
      decide ((N - (2 ^ x + 11 * 2 ^ y)) % d = 0))

theorem chk_sound {N x y d : ℕ} (h : chk N x y d = true) :
    ¬ (2 ^ x + 11 * 2 ^ y < N ∧ (N - (2 ^ x + 11 * 2 ^ y)).Prime ∧
      (N - (2 ^ x + 11 * 2 ^ y)) % 6 = 1) := by
  rintro ⟨h1, h2, h3⟩
  simp only [chk, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at h
  rcases h with (h | h) | ⟨⟨ht1, ht2⟩, ht3⟩
  · omega
  · exact h h3
  · exact Nat.not_prime_of_dvd_of_lt (Nat.dvd_of_mod_eq_zero ht3) ht1 ht2 h2

/-- Row `x`, column `y` of a table of divisors. -/
def look (W : List (List ℕ)) (x y : ℕ) : ℕ := (W.getD x []).getD y 0

theorem a_eq_zero (n X Y : ℕ) (W : List (List ℕ)) (hn : n ≠ 0)
    (hX : 2 * n - 1 ≤ 2 ^ X) (hY : 2 * n - 1 ≤ 11 * 2 ^ Y)
    (hall : ∀ x < X, ∀ y < Y, 1 ≤ x → 1 ≤ y → chk (2 * n - 1) x y (look W x y) = true) :
    OeisA157237.a n = 0 := by
  unfold OeisA157237.a
  rw [if_neg hn]
  apply Finset.sum_eq_zero
  intro x hx
  apply Finset.sum_eq_zero
  intro y hy
  rw [Finset.mem_Icc] at hx hy
  rw [if_neg]
  intro hc
  have h1 : 2 ^ x + 11 * 2 ^ y < 2 * n - 1 := hc.1
  have hxX : x < X := by
    by_contra hcon
    have h2 : 2 ^ X ≤ 2 ^ x :=
      Nat.pow_le_pow_right (show 0 < 2 by norm_num) (Nat.le_of_not_lt hcon)
    exact Nat.lt_irrefl _ (lt_of_le_of_lt (Nat.le_add_right _ _)
      (lt_of_lt_of_le h1 (le_trans hX h2)))
  have hyY : y < Y := by
    by_contra hcon
    have h2 : 2 ^ Y ≤ 2 ^ y :=
      Nat.pow_le_pow_right (show 0 < 2 by norm_num) (Nat.le_of_not_lt hcon)
    exact Nat.lt_irrefl _ (lt_of_le_of_lt (Nat.le_add_left _ _)
      (lt_of_lt_of_le h1 (le_trans hY (Nat.mul_le_mul_left 11 h2))))
  exact chk_sound (hall x hxX y hyY hx.1 hy.1) hc

/-- Proper divisors of `667623212539751 - (2 ^ x + 11 * 2 ^ y)` (row `x`, column `y`; `0` where none is needed). -/
def z : List ℕ := List.replicate 46 0

def r (l : List ℕ) : List ℕ := 0::0::l.flatMap (fun d => [d,0])

/-- Proper divisors of `667623212539751 - (2 ^ x + 11 * 2 ^ y)` (row `x`, column `y`; `0` where none is needed). -/
def W : List (List ℕ) :=
  [z,r [5,89,5,1597,5,7,5,53593,5,61,5,7,5,24203,5,6511469,5,7,5,787,5,67],z,r [13,53,17,19,31,4452533,13,163,467,31,17,383,13,89,17,4657,67,43,13,31,61,19],z,r [5,13,5,7,5,71,5,13,5,7,5,139,5,13,5,7,5,22220267,5,13,5,7],z,r [23,17,7,461,89,7,8297,19,7,17,541,7,59,17,7,89,19,7,71,599,7,17],z,r [5,11,5,11,5,11,5,11,5,11,5,11,5,11,5,11,5,11,5,11,5,11],z,r [7,991579,17,7,13,151,7,111497,47,7,13,1583,7,19,17,7,13,89,7,15130439,151,7],z,r [5,15134681,5,71,5,7,5,23,5,31,5,7,5,79,5,19,5,7,5,31,5,25931],z,r [13,17,229,5227,5209,17,13,8253541,89,17,59,353,13,17,8641541,6871,3469,17,13,89,83,17],z,r [5,13,5,7,5,149,5,13,5,7,5,37,5,13,5,7,5,43,5,13,5,7],z,r [11,11,7,11,11,7,11,11,7,11,11,7,11,11,7,11,11,7,11,11,7,11],z,r [5,281,5,13,5,23,5,37,5,13,5,89,5,967,5,13,5,1846153,5,79,5,13],z,r [7,17,29,7,13,17,7,127,5233,7,13,2657,7,17,31,7,13,17,7,31,173,7],z,r [5,151,5,1481,5,7,5,19,5,53,5,7,5,89,5,1061,5,7,5,5717,5,157],z,r [13,41,17,29,67,8539,13,887,191,421699,17,41,13,41539,17,30493,49333,29,13,2153,547,41],z,r [5,11,5,7,5,11,5,11,5,7,5,11,5,11,5,7,5,11,5,11,5,7],z,r [2393,17,7,43,193,7,19,4519,7,17,43,7,29,17,7,19,89,7,107,23,7,17],z,r [5,101173,5,13,5,47,5,97,5,13,5,179,5,124717,5,13,5,89,5,31,5,13],z,r [7,109,17,7,13,157,7,23,103,7,13,3119,7,463,17,7,13,47,7,109,2161,7],z,r [5,179,5,67,5,7,5,127,5,79,5,7,5,101,5,47,5,7,5,89,5,127],z,r [11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11],z,r [5,13,5,7,5,73,5,13,5,7,5,101,5,13,5,7,5,1487,5,13,5,7],z,r [89,311,7,2393,31,7,17,19,7,31,17,7,167,107,7,101,19,7,17,31,7,397],z,r [5,89,5,13,5,727,5,2952689,5,13,5,53,5,419,5,13,5,43,5,1291,5,13],z,r [7,17,89,7,13,17,7,79,17732999,7,13,41,7,17,83,7,13,17,7,3253,137,7],z,r [5,11,5,11,5,7,5,11,5,11,5,7,5,11,5,11,5,7,5,11,5,0]]

theorem a_zero : OeisA157237.a 333811606269876 = 0 := by
  apply a_eq_zero 333811606269876 50 46 W (by norm_num) (by norm_num) (by norm_num)
  decide +kernel

end SunEleven

theorem OMA.disproof : ¬ (type_of% @OeisA157237.conjecture) := by
  intro h
  have h1 := (h 333811606269876 (by norm_num)).mp SunEleven.a_zero
  omega
