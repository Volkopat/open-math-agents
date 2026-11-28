import OMAReductions.R_oeis_a079390_R1
import Mathlib

/-! Step oeis-a079390.R1.H1, the classical parts. For twin primes `(n, n + 2)` with `n > 2` we get
`a n = 2n(n + 2)`. An earlier `a m` is at most `4(m + 1)` for even `m` and at most `2m(m + 2)` for
odd `m`, which is smaller in both cases. For even `n > 2`, `a (n - 1) ≥ 4 · lpf(n + 1) = a n`, so a
record value sits at odd `n`. -/

namespace OMA.A079390H1

open OMA.S_oeis_a079390

lemma minFac_even {m : ℕ} (h : m % 2 = 0) : m.minFac = 2 := by
  rw [Nat.minFac_eq_two_iff]; omega

theorem main (n : ℕ) (hn : 2 < n) :
    ((n.Prime ∧ (n + 2).Prime) → ∀ m, 1 ≤ m → m < n → a m < a n) ∧
    ((∀ m, 1 ≤ m → m < n → a m < a n) → n % 2 = 1) := by
  constructor
  · rintro ⟨hp, hp2⟩ m hm1 hmn
    have hodd : n % 2 = 1 := by
      rcases hp.eq_two_or_odd with h | h
      · omega
      · exact h
    have han : a n = n * 2 * (n + 2) := by
      unfold a
      rw [hp.minFac_eq, hp2.minFac_eq, minFac_even (by omega)]
    rw [han]
    unfold a
    rcases Nat.even_or_odd m with ⟨k, hk⟩ | ⟨k, hk⟩
    · rw [minFac_even (by omega), minFac_even (show (m + 2) % 2 = 0 by omega)]
      have h1 : (m + 1).minFac ≤ m + 1 := Nat.minFac_le (by omega)
      have h2 : 2 * (m + 1).minFac * 2 ≤ 2 * (m + 1) * 2 := by
        apply Nat.mul_le_mul_right; apply Nat.mul_le_mul_left; exact h1
      have h3 : 2 * (m + 1) * 2 < n * 2 * (n + 2) := by nlinarith
      omega
    · rw [minFac_even (show (m + 1) % 2 = 0 by omega)]
      have h1 : m.minFac ≤ m := Nat.minFac_le (by omega)
      have h2 : (m + 2).minFac ≤ m + 2 := Nat.minFac_le (by omega)
      have h3 : m.minFac * 2 * (m + 2).minFac ≤ m * 2 * (m + 2) :=
        Nat.mul_le_mul (Nat.mul_le_mul_right 2 h1) h2
      have h4 : m * 2 * (m + 2) < n * 2 * (n + 2) := by nlinarith
      omega
  · intro hrec
    by_contra heven
    have he : n % 2 = 0 := by omega
    have := hrec (n - 1) (by omega) (by omega)
    unfold a at this
    rw [show n - 1 + 1 = n by omega, show n - 1 + 2 = n + 1 by omega, minFac_even he,
      minFac_even (show (n + 2) % 2 = 0 by omega)] at this
    have h2 : 2 ≤ (n - 1).minFac := (Nat.minFac_prime (by omega)).two_le
    have : 2 * 2 * (n + 1).minFac ≤ (n - 1).minFac * 2 * (n + 1).minFac := by
      apply Nat.mul_le_mul_right; exact Nat.mul_le_mul_right 2 h2
    omega

end OMA.A079390H1

theorem OMA.solution : OMA.R_oeis_a079390_R1.H1 :=
  OMA.A079390H1.main
