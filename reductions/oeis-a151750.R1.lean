import OMAStatements.S_oeis_a151750
import Mathlib

/-! A151750 restated through Kummer's criterion for central binomial coefficients.

For a prime `p`, `p` does not divide `C(2n, n)` exactly when every base-`p` digit `d` of `n`
satisfies `2 d < p`, that is, when doubling `n` in base `p` produces no carry (Kummer; it also
follows from Lucas' theorem by peeling off the lowest digit). That is `H1`, a classical theorem
about all primes and all `n`, not progress on the conjecture.

With `H1`, `gcd(C(2n, n), 3 * 5 * 7 * 11) = 1` says that the digits of `n` are at most 1 in
base 3, at most 2 in base 5, at most 3 in base 7 and at most 5 in base 11. `H2` is the open rest,
a digit problem of Erdős-Graham-Ruzsa-Straus type: only `0`, `1` and `3160` satisfy all four.
-/

namespace OMA.R_oeis_a151750_R1

open OMA.S_oeis_a151750

/-- Kummer's criterion: `p ∤ C(2n, n)` iff doubling `n` in base `p` has no carry. -/
def H1 : Prop := ∀ p n : ℕ, p.Prime →
  (¬ p ∣ Nat.choose (2 * n) n ↔ ∀ d ∈ Nat.digits p n, 2 * d < p)

/-- The open rest: the simultaneous small-digit condition in bases 3, 5, 7 and 11. -/
def H2 : Prop := ∀ n : ℕ,
  (∀ d ∈ Nat.digits 3 n, 2 * d < 3) → (∀ d ∈ Nat.digits 5 n, 2 * d < 5) →
  (∀ d ∈ Nat.digits 7 n, 2 * d < 7) → (∀ d ∈ Nat.digits 11 n, 2 * d < 11) →
  n = 0 ∨ n = 1 ∨ n = 3160

lemma isTerm_iff (n : ℕ) : IsTerm n ↔
    (¬ 3 ∣ Nat.choose (2 * n) n ∧ ¬ 5 ∣ Nat.choose (2 * n) n) ∧
      ¬ 7 ∣ Nat.choose (2 * n) n ∧ ¬ 11 ∣ Nat.choose (2 * n) n := by
  have hc : ∀ p : ℕ, p.Prime → (Nat.Coprime (Nat.choose (2 * n) n) p ↔ ¬ p ∣ Nat.choose (2 * n) n) :=
    fun p hp => Nat.coprime_comm.trans (Nat.Prime.coprime_iff_not_dvd hp)
  show Nat.Coprime _ _ ↔ _
  rw [Nat.coprime_mul_iff_right, Nat.coprime_mul_iff_right, Nat.coprime_mul_iff_right,
    hc 3 (by norm_num), hc 5 (by norm_num), hc 7 (by norm_num), hc 11 (by norm_num), and_assoc]

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a151750.main := by
  intro h1 h2 n
  rw [isTerm_iff, h1 3 n (by norm_num), h1 5 n (by norm_num), h1 7 n (by norm_num),
    h1 11 n (by norm_num)]
  constructor
  · rintro ⟨⟨a, b⟩, c, d⟩
    exact h2 n a b c d
  · rintro (rfl | rfl | rfl) <;> norm_num

end OMA.R_oeis_a151750_R1
