import OMAStatements.S_oeis_a379427
import Mathlib

/-!
# A379427: all such `m` are `14 (mod 30)`

The first seven of the conditions say that `2m+3`, `3m+5`, `5m+7`, `7m+11`, `13m+17` and
`19m+23` are prime (among others).  A small sieve:

* if `m` is odd, `3m + 5` is even and larger than `2`;
* if `m ≡ 0 (mod 3)`, `3 ∣ 2m + 3 > 3`; if `m ≡ 1 (mod 3)`, `3 ∣ 5m + 7 > 3`;
* if `m ≡ 0, 1, 2, 3 (mod 5)`, then `5` divides `3m + 5`, `13m + 17`, `7m + 11`, `19m + 23`
  respectively, each larger than `5`.

So `m` is even, `m ≡ 2 (mod 3)` and `m ≡ 4 (mod 5)`, i.e. `m ≡ 14 (mod 30)`.
-/

namespace OMA.S_oeis_a379427

/-- The first primes, in the indexing of the statement. -/
lemma prime_val {k p : ℕ} (hp : p.Prime) (hc : Nat.count Nat.Prime p = k) : prime (k + 1) = p := by
  unfold prime
  rw [Nat.add_sub_cancel, ← hc]
  exact Nat.nth_count hp

/-- A prime with a proper divisor `d > 1` equals `d`. -/
lemma eq_of_dvd {p d : ℕ} (hp : p.Prime) (hd : d ∣ p) (h1 : d ≠ 1) : p = d := by
  rcases (Nat.dvd_prime hp).mp hd with h | h
  · exact absurd h h1
  · exact h.symm

end OMA.S_oeis_a379427

open OMA.S_oeis_a379427 in
theorem OMA.solution : type_of% @OMA.S_oeis_a379427.main := by
  intro m hm h
  have p1 : prime 1 = 2 := prime_val (k := 0) (by norm_num) (by decide)
  have p2 : prime 2 = 3 := prime_val (k := 1) (by norm_num) (by decide)
  have p3 : prime 3 = 5 := prime_val (k := 2) (by norm_num) (by decide)
  have p4 : prime 4 = 7 := prime_val (k := 3) (by norm_num) (by decide)
  have p5 : prime 5 = 11 := prime_val (k := 4) (by norm_num) (by decide)
  have p6 : prime 6 = 13 := prime_val (k := 5) (by norm_num) (by decide)
  have p7 : prime 7 = 17 := prime_val (k := 6) (by norm_num) (by decide)
  have p8 : prime 8 = 19 := prime_val (k := 7) (by norm_num) (by decide)
  have p9 : prime 9 = 23 := prime_val (k := 8) (by norm_num) (by decide)
  have q1 : (2 * m + 3).Prime := by
    have := h 1 (by decide); rwa [p1, p2] at this
  have q2 : (3 * m + 5).Prime := by
    have := h 2 (by decide); rwa [p2, p3] at this
  have q3 : (5 * m + 7).Prime := by
    have := h 3 (by decide); rwa [p3, p4] at this
  have q4 : (7 * m + 11).Prime := by
    have := h 4 (by decide); rwa [p4, p5] at this
  have q6 : (13 * m + 17).Prime := by
    have := h 6 (by decide); rwa [p6, p7] at this
  have q8 : (19 * m + 23).Prime := by
    have := h 8 (by decide); rwa [p8, p9] at this
  -- parity
  have h2 : m % 2 = 0 := by
    by_contra hc
    have := eq_of_dvd q2 (show 2 ∣ 3 * m + 5 by omega) (by norm_num)
    omega
  -- modulo 3
  have h3 : m % 3 = 2 := by
    by_contra hc
    have hcases : m % 3 = 0 ∨ m % 3 = 1 := by omega
    rcases hcases with h0 | h1
    · have := eq_of_dvd q1 (show 3 ∣ 2 * m + 3 by omega) (by norm_num)
      omega
    · have := eq_of_dvd q3 (show 3 ∣ 5 * m + 7 by omega) (by norm_num)
      omega
  -- modulo 5
  have h5 : m % 5 = 4 := by
    by_contra hc
    have hcases : m % 5 = 0 ∨ m % 5 = 1 ∨ m % 5 = 2 ∨ m % 5 = 3 := by omega
    rcases hcases with h0 | h1 | h2' | h3'
    · have := eq_of_dvd q2 (show 5 ∣ 3 * m + 5 by omega) (by norm_num)
      omega
    · have := eq_of_dvd q6 (show 5 ∣ 13 * m + 17 by omega) (by norm_num)
      omega
    · have := eq_of_dvd q4 (show 5 ∣ 7 * m + 11 by omega) (by norm_num)
      omega
    · have := eq_of_dvd q8 (show 5 ∣ 19 * m + 23 by omega) (by norm_num)
      omega
  omega
