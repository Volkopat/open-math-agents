import FormalConjectures.OEIS.«109671»

/-!
# A109671: the block starting at three times a power of two

At every `k > 0`, suppose the term just before `3 * 2 ^ k` is one. The odd-index
update then starts the block with the value three. Induction on the block and the
index shows that all positive offsets below `2 ^ k` are exactly triple the original
sequence. In particular, every attained positive value can be multiplied by three.
It therefore suffices to find the positive values not divisible by three.
-/

namespace OMA.R_OeisA109671_conjecture_R1

open OeisA109671

/-- The term immediately before each block is one. -/
def H1 : Prop := ∀ k : ℕ, 0 < k → a (3 * 2 ^ k - 1) = 1

/-- All positive integers not divisible by three occur in the sequence. -/
def H2 : Prop := ∀ m : ℕ, 0 < m → ¬ 3 ∣ m → ∃ n : ℕ, 0 < n ∧ a n = m

lemma a_even (n : ℕ) : a (2 * n) = a n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rfl
  rw [a.eq_def, if_neg (by omega), if_neg (by omega), if_pos (by omega),
    show 2 * n / 2 = n by omega]

lemma a_odd (n : ℕ) (hn : 0 < n) :
    a (2 * n + 1) =
      if a (2 * n - 1) > a n then a (2 * n - 1) - a n else a (2 * n - 1) + a n := by
  rw [a.eq_def, if_neg (by omega), if_neg (by omega), if_neg (by omega),
    show (2 * n + 1 - 1) / 2 = n by omega, show 2 * n + 1 - 2 = 2 * n - 1 by omega]

lemma a_dyadic (n k : ℕ) : a (2 ^ k * n) = a n := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', mul_assoc, a_even, ih]

lemma a_block_scale (seed : ∀ k : ℕ, 0 < k → a (3 * 2 ^ k - 1) = 1) :
    ∀ k j : ℕ, 0 < j → j < 2 ^ k → a (3 * 2 ^ k + j) = 3 * a j := by
  have one : a 1 = 1 := by rw [a.eq_def]; decide
  have three : a 3 = 2 := by
    change a (2 * 1 + 1) = 2
    rw [a_odd 1 (by decide), show 2 * 1 - 1 = 1 by decide, one]
    decide
  intro k
  induction k with
  | zero =>
    intro j hj hlt
    simp at hlt
    omega
  | succ k ih =>
    have hb : 3 * 2 ^ (k + 1) = 2 * (3 * 2 ^ k) := by rw [pow_succ']; ring
    have hp : 2 ^ (k + 1) = 2 * 2 ^ k := pow_succ' 2 k
    intro j
    induction j using Nat.strong_induction_on with
    | _ j smaller =>
      intro hj hjk
      obtain ⟨q, rfl | rfl⟩ := Nat.even_or_odd' j
      · calc
          a (3 * 2 ^ (k + 1) + 2 * q) = a (3 * 2 ^ k + q) := by
            rw [show 3 * 2 ^ (k + 1) + 2 * q = 2 * (3 * 2 ^ k + q) by omega, a_even]
          _ = 3 * a q := ih q (by omega) (by omega)
          _ = 3 * a (2 * q) := by rw [a_even]
      · rcases Nat.eq_zero_or_pos q with rfl | hq
        · rw [show 2 * 0 + 1 = 1 by decide, hb, a_odd _ (by positivity), ← hb,
            seed (k + 1) (by omega), mul_comm 3 (2 ^ k), a_dyadic, three, one]
          decide
        · rw [show 3 * 2 ^ (k + 1) + (2 * q + 1) = 2 * (3 * 2 ^ k + q) + 1 by omega,
            a_odd _ (by positivity), a_odd q hq,
            show 2 * (3 * 2 ^ k + q) - 1 = 3 * 2 ^ (k + 1) + (2 * q - 1) by omega,
            smaller (2 * q - 1) (by omega) (by omega) (by omega), ih q hq (by omega)]
          split <;> split <;> omega

theorem main : H1 → H2 → type_of% @OeisA109671.conjecture := by
  intro seed roots m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm
    by_cases hd : 3 ∣ m
    · obtain ⟨q, rfl⟩ := hd
      have hq : 0 < q := by omega
      obtain ⟨n, hn, hvalue⟩ := ih q (by omega) hq
      refine ⟨3 * 2 ^ n + n, by omega, ?_⟩
      rw [a_block_scale seed n n hn Nat.lt_two_pow_self, hvalue]
    · exact roots m hm hd

end OMA.R_OeisA109671_conjecture_R1
