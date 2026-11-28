import OMAStatements.S_oeis_a087403

/-!
# Infinitely many zeros of OEIS A087403

The block 104040 already occurs in the disproof of OeisA86766.conjecture2.
Its factorization extends to blocks of every length divisible by six. For each
such length the block below has one digit 1, two digits 4, and zeros elsewhere.
-/

namespace DecimalBlocks

open OMA.S_oeis_a087403 Finset

/-- If both factors of a multiple of p exceed its multiplier, then p is composite. -/
private lemma composite {p m a b : ℕ} (ha : m < a) (hb : m < b) (h : m * p = a * b) :
    ¬ p.Prime := by
  intro hp
  have excludes {x y : ℕ} (hx : 0 < x) (hy : m < y) (eq : m * p = x * y) : ¬ p ∣ x := by
    intro hd
    have := Nat.mul_le_mul_left m (Nat.le_of_dvd hx hd)
    nlinarith [Nat.mul_lt_mul_of_pos_left hy hx]
  exact (hp.dvd_mul.mp (h ▸ Nat.dvd_mul_left p m)).elim
    (excludes (by omega) hb h) (excludes (by omega) ha (h.trans (mul_comm ..)))

/-- If the decimal base and the initial block give a difference of two squares,
every repetition has a nontrivial factorization. -/
lemma zero_of_squares {n b u v : ℕ}
    (base : 10 ^ (Nat.digits 10 n).length = b ^ 2)
    (block : 10 * n = u ^ 2) (balance : u ^ 2 + 1 = b ^ 2 + v ^ 2)
    (large : b ^ 2 + v ≤ u * b) (hb : 1 < b) : a n = 0 := by
  apply Nat.sInf_eq_zero.mpr
  right
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro p ⟨hp, r, hr, rfl⟩
  let S := ∑ i ∈ range r, (b ^ 2) ^ i
  let t := b ^ r
  have ht : b ≤ t := Nat.le_self_pow hr.ne' b
  have hz : 1 ≤ b ^ 2 := Nat.one_le_pow 2 b (by omega)
  have hprod := Nat.mul_le_mul_left u ht
  have hg : S * (b ^ 2 - 1) + 1 = t ^ 2 := by
    dsimp only [S, t]
    rw [geom_sum_mul_of_one_le hz, Nat.sub_add_cancel (Nat.one_le_pow r _ hz), pow_right_comm]
  rw [repeatDecimal, base, ← mul_sum, ← mul_assoc, block] at hp
  -- Multiplying the candidate by the radix minus one gives a difference of squares.
  apply composite (m := b ^ 2 - 1) (a := u * t - v) (b := u * t + v) (by omega) (by omega) _ hp
  change (b ^ 2 - 1) * (u ^ 2 * S + 1) = (u * t - v) * (u * t + v)
  zify [show v ≤ u * t by omega, hz] at hg balance ⊢
  linear_combination (u : ℤ) ^ 2 * hg - balance

/-- Decimal expansion with a single 1 and two 4s. The gaps grow with s. -/
def block (s : ℕ) := 10 ^ (s * 6 + 5) + 4 * 10 ^ (s * 4 + 3) + 4 * 10 ^ (s * 2 + 1)

/-- Every positive number of repetitions of this block gives a composite candidate. -/
theorem block_zero (s : ℕ) : a (block s) = 0 := by
  let t := 10 ^ (s + 1)
  have hlen : (Nat.digits 10 (block s)).length = s * 6 + 6 := by
    apply le_antisymm
    · apply (Nat.digits_length_le_iff (by decide) _).2
      have hi : (10 : ℕ) ^ (s * 4 + 3) ≤ 10 ^ (s * 6 + 5) := by gcongr <;> omega
      have hj : (10 : ℕ) ^ (s * 2 + 1) ≤ 10 ^ (s * 6 + 5) := by gcongr <;> omega
      have pos : 0 < (10 : ℕ) ^ (s * 6 + 5) := by positivity
      unfold block
      rw [pow_succ 10 (s * 6 + 5)]
      omega
    · exact (Nat.lt_digits_length_iff (by decide) _).2 (by unfold block; omega)
  have ht : 10 ≤ t := Nat.le_self_pow (by omega) 10
  apply zero_of_squares (b := t ^ 3) (u := t ^ 3 + 2 * t) (v := 2 * t ^ 2 + 1)
  · simp only [hlen, t, ← pow_mul]
    congr 1
    omega
  · simp only [block, t, pow_add, pow_mul, pow_one]
    ring
  · ring
  · have hs := Nat.pow_le_pow_left ht 2
    nlinarith [Nat.mul_le_mul_left (t ^ 2) hs]
  · nlinarith [Nat.pow_le_pow_left ht 3]

end DecimalBlocks

open DecimalBlocks

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a087403.main) := by
  intro h
  exact h _ (by decide : 0 < block 0) (block_zero 0)
