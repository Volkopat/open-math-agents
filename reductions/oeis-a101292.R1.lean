import OMAStatements.S_oeis_a101292

/-!
# Reduction of OEIS A101292 (Fibonacci factoriangular numbers)

Target: `Set.range a ∩ Set.range Nat.fib = {1, 2, 5, 34}` with `a n = n! + (1 + 2 + ... + n)`.

The split follows C. A. Gómez Ruiz and F. Luca, *Fibonacci factoriangular numbers*,
Indag. Math. 28 (2017) 796-804. Everything elementary is proved in this file:

* the closed form `a n = n! + n (n + 1) / 2`;
* the four hits `a 0 = F 1`, `a 1 = F 3`, `a 2 = F 5`, `a 4 = F 9`;
* `a n` is not a Fibonacci number for `n = 3` and for every `5 ≤ n ≤ 100`
  (each value lies strictly between two consecutive Fibonacci numbers, checked by evaluation).

What is left is exactly the two non-elementary steps of the paper:

* `H1` (Lemma 1 of the paper): a solution of `F m = n! + n (n + 1) / 2` with `n ≥ 101` has
  `n < 1.4 · 10^8`. The paper proves it with the Bugeaud–Laurent upper bound for p-adic linear
  forms in two logarithms at a prime above 2, applied to `α^m - z` where `α` is the golden ratio
  and `z` a root of `z^2 - √5 · n (n + 1) / 2 · z - ε`, against `ord_2 (n!) > 3 n / 4`.
* `H2` (Section 5 of the paper): there is no solution with `101 ≤ n < 1.4 · 10^8`. The paper
  checks it by computer: last 20 digits for `n ≤ 2.8 · 10^5`, and a Legendre-symbol sieve modulo
  primes `p ≡ 1 (mod 5)` with `p - 1 ∣ 2^4 · 3^2 · 5^2 · 7 · 11` followed by a digit check above that.
-/

namespace OMA.R_oeis_a101292_R1

/-- Gauss: twice the sum `1 + 2 + ... + n` is `n (n + 1)`. -/
theorem two_mul_sum_Icc (n : ℕ) : 2 * ∑ i ∈ Finset.Icc 1 n, i = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (show 1 ≤ k + 1 by omega), mul_add, ih]
    ring

/-- Closed form of the factoriangular numbers. -/
theorem a_eq (n : ℕ) : OMA.S_oeis_a101292.a n = n.factorial + n * (n + 1) / 2 := by
  have h := two_mul_sum_Icc n
  unfold OMA.S_oeis_a101292.a
  omega

/-- A number strictly between two consecutive Fibonacci numbers is not a Fibonacci number. -/
theorem not_fib_of_between {x k : ℕ} (h1 : Nat.fib k < x) (h2 : x < Nat.fib (k + 1)) (m : ℕ) :
    ¬ Nat.fib m = x := by
  intro hm
  subst hm
  rcases Nat.lt_or_ge k m with h | h
  · exact absurd (Nat.fib_mono (Nat.succ_le_of_lt h)) (not_le.mpr h2)
  · exact absurd (Nat.fib_mono h) (not_le.mpr h1)

-- Every solution of `F m = n! + n (n + 1) / 2` has `n ∈ {0, 1, 2, 4}`.
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem fib_eq_cases
    (h1 : ∀ n m : ℕ, 101 ≤ n → Nat.fib m = n.factorial + n * (n + 1) / 2 → n < 140000000)
    (h2 : ∀ n m : ℕ, 101 ≤ n → n < 140000000 → ¬ Nat.fib m = n.factorial + n * (n + 1) / 2)
    (n m : ℕ)
    (hm : Nat.fib m = n.factorial + n * (n + 1) / 2) : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 4 := by
  by_cases hn : n ≤ 100
  · interval_cases n
    · decide
    · decide
    · decide
    · exact absurd hm (not_fib_of_between (k := 6) (by decide +kernel) (by decide +kernel) m)
    · decide
    · exact absurd hm (not_fib_of_between (k := 11) (by decide +kernel) (by decide +kernel) m)
    · exact absurd hm (not_fib_of_between (k := 15) (by decide +kernel) (by decide +kernel) m)
    · exact absurd hm (not_fib_of_between (k := 19) (by decide +kernel) (by decide +kernel) m)
    · exact absurd hm (not_fib_of_between (k := 23) (by decide +kernel) (by decide +kernel) m)
    · exact absurd hm (not_fib_of_between (k := 28) (by decide +kernel) (by decide +kernel) m)
    · exact absurd hm (not_fib_of_between (k := 33) (by decide +kernel) (by decide +kernel) m)
    · exact absurd hm (not_fib_of_between (k := 38) (by decide +kernel) (by decide +kernel) m)
    · exact absurd hm (not_fib_of_between (k := 43) (by decide +kernel) (by decide +kernel) m)
    · exact absurd hm (not_fib_of_between (k := 48) (by decide +kernel) (by decide +kernel) m)
    · exact absurd hm (not_fib_of_between (k := 54) (by decide +kernel) (by decide +kernel) m)
    · exact absurd hm (not_fib_of_between (k := 59) (by decide +kernel) (by decide +kernel) m)
    · exact absurd hm (not_fib_of_between (k := 65) (by decide +kernel) (by decide +kernel) m)
    · exact absurd hm (not_fib_of_between (k := 71) (by decide +kernel) (by decide +kernel) m)
    · exact absurd hm (not_fib_of_between (k := 77) (by decide +kernel) (by decide +kernel) m)
    · exact absurd hm (not_fib_of_between (k := 83) (by decide +kernel) (by decide +kernel) m)
    · exact absurd hm (not_fib_of_between (k := 89) (by decide +kernel) (by decide +kernel) m)
    · exact absurd hm (not_fib_of_between (k := 95) (by decide +kernel) (by decide +kernel) m)
    · exact absurd hm (not_fib_of_between (k := 102) (by decide +kernel) (by decide +kernel) m)
    · exact absurd hm (not_fib_of_between (k := 108) (by decide +kernel) (by decide +kernel) m)
    · exact absurd hm (not_fib_of_between (k := 115) (by decide +kernel) (by decide +kernel) m)
    · exact absurd hm (not_fib_of_between (k := 122) (by decide +kernel) (by decide +kernel) m)
    · exact absurd hm (not_fib_of_between (k := 128) (by decide +kernel) (by decide +kernel) m)
    · exact absurd hm (not_fib_of_between (k := 135) (by decide +kernel) (by decide +kernel) m)
    · exact absurd hm (not_fib_of_between (k := 142) (by decide +kernel) (by decide +kernel) m)
    · exact absurd hm (not_fib_of_between (k := 149) (by decide +kernel) (by decide +kernel) m)
    · exact absurd hm (not_fib_of_between (k := 156) (by decide +kernel) (by decide +kernel) m)
    · exact absurd hm (not_fib_of_between (k := 163) (by decide +kernel) (by decide +kernel) m)
    · exact absurd hm (not_fib_of_between (k := 171) (by decide +kernel) (by decide +kernel) m)
    · exact absurd hm (not_fib_of_between (k := 178) (by decide +kernel) (by decide +kernel) m)
    · exact absurd hm (not_fib_of_between (k := 185) (by decide +kernel) (by decide +kernel) m)
    · exact absurd hm (not_fib_of_between (k := 193) (by decide +kernel) (by decide +kernel) m)
    · exact absurd hm (not_fib_of_between (k := 200) (by decide +kernel) (by decide +kernel) m)
    · exact absurd hm (not_fib_of_between (k := 208) (by decide +kernel) (by decide +kernel) m)
    · exact absurd hm (not_fib_of_between (k := 215) (by decide +kernel) (by decide +kernel) m)
    · exact absurd hm (not_fib_of_between (k := 223) (by decide +kernel) (by decide +kernel) m)
    · exact absurd hm (not_fib_of_between (k := 230) (by decide +kernel) (by decide +kernel) m)
    · exact absurd hm (not_fib_of_between (k := 238) (by decide +kernel) (by decide +kernel) m)
    · exact absurd hm (not_fib_of_between (k := 246) (by decide +kernel) (by decide +kernel) m)
    · exact absurd hm (not_fib_of_between (k := 254) (by decide +kernel) (by decide +kernel) m)
    · exact absurd hm (not_fib_of_between (k := 262) (by decide +kernel) (by decide +kernel) m)
    · exact absurd hm (not_fib_of_between (k := 270) (by decide +kernel) (by decide +kernel) m)
    · exact absurd hm (not_fib_of_between (k := 277) (by decide +kernel) (by decide +kernel) m)
    · exact absurd hm (not_fib_of_between (k := 285) (by decide +kernel) (by decide +kernel) m)
    · exact absurd hm (not_fib_of_between (k := 294) (by decide +kernel) (by decide +kernel) m)
    · exact absurd hm (not_fib_of_between (k := 302) (by decide +kernel) (by decide +kernel) m)
    · exact absurd hm (not_fib_of_between (k := 310) (by decide +kernel) (by decide +kernel) m)
    · exact absurd hm (not_fib_of_between (k := 318) (by decide +kernel) (by decide +kernel) m)
    · exact absurd hm (not_fib_of_between (k := 326) (by decide +kernel) (by decide +kernel) m)
    · exact absurd hm (not_fib_of_between (k := 334) (by decide +kernel) (by decide +kernel) m)
    · exact absurd hm (not_fib_of_between (k := 343) (by decide +kernel) (by decide +kernel) m)
    · exact absurd hm (not_fib_of_between (k := 351) (by decide +kernel) (by decide +kernel) m)
    · exact absurd hm (not_fib_of_between (k := 359) (by decide +kernel) (by decide +kernel) m)
    · exact absurd hm (not_fib_of_between (k := 368) (by decide +kernel) (by decide +kernel) m)
    · exact absurd hm (not_fib_of_between (k := 376) (by decide +kernel) (by decide +kernel) m)
    · exact absurd hm (not_fib_of_between (k := 385) (by decide +kernel) (by decide +kernel) m)
    · exact absurd hm (not_fib_of_between (k := 393) (by decide +kernel) (by decide +kernel) m)
    · exact absurd hm (not_fib_of_between (k := 402) (by decide +kernel) (by decide +kernel) m)
    · exact absurd hm (not_fib_of_between (k := 410) (by decide +kernel) (by decide +kernel) m)
    · exact absurd hm (not_fib_of_between (k := 419) (by decide +kernel) (by decide +kernel) m)
    · exact absurd hm (not_fib_of_between (k := 428) (by decide +kernel) (by decide +kernel) m)
    · exact absurd hm (not_fib_of_between (k := 436) (by decide +kernel) (by decide +kernel) m)
    · exact absurd hm (not_fib_of_between (k := 445) (by decide +kernel) (by decide +kernel) m)
    · exact absurd hm (not_fib_of_between (k := 454) (by decide +kernel) (by decide +kernel) m)
    · exact absurd hm (not_fib_of_between (k := 462) (by decide +kernel) (by decide +kernel) m)
    · exact absurd hm (not_fib_of_between (k := 471) (by decide +kernel) (by decide +kernel) m)
    · exact absurd hm (not_fib_of_between (k := 480) (by decide +kernel) (by decide +kernel) m)
    · exact absurd hm (not_fib_of_between (k := 489) (by decide +kernel) (by decide +kernel) m)
    · exact absurd hm (not_fib_of_between (k := 498) (by decide +kernel) (by decide +kernel) m)
    · exact absurd hm (not_fib_of_between (k := 507) (by decide +kernel) (by decide +kernel) m)
    · exact absurd hm (not_fib_of_between (k := 516) (by decide +kernel) (by decide +kernel) m)
    · exact absurd hm (not_fib_of_between (k := 525) (by decide +kernel) (by decide +kernel) m)
    · exact absurd hm (not_fib_of_between (k := 534) (by decide +kernel) (by decide +kernel) m)
    · exact absurd hm (not_fib_of_between (k := 543) (by decide +kernel) (by decide +kernel) m)
    · exact absurd hm (not_fib_of_between (k := 552) (by decide +kernel) (by decide +kernel) m)
    · exact absurd hm (not_fib_of_between (k := 561) (by decide +kernel) (by decide +kernel) m)
    · exact absurd hm (not_fib_of_between (k := 570) (by decide +kernel) (by decide +kernel) m)
    · exact absurd hm (not_fib_of_between (k := 579) (by decide +kernel) (by decide +kernel) m)
    · exact absurd hm (not_fib_of_between (k := 588) (by decide +kernel) (by decide +kernel) m)
    · exact absurd hm (not_fib_of_between (k := 597) (by decide +kernel) (by decide +kernel) m)
    · exact absurd hm (not_fib_of_between (k := 607) (by decide +kernel) (by decide +kernel) m)
    · exact absurd hm (not_fib_of_between (k := 616) (by decide +kernel) (by decide +kernel) m)
    · exact absurd hm (not_fib_of_between (k := 625) (by decide +kernel) (by decide +kernel) m)
    · exact absurd hm (not_fib_of_between (k := 634) (by decide +kernel) (by decide +kernel) m)
    · exact absurd hm (not_fib_of_between (k := 644) (by decide +kernel) (by decide +kernel) m)
    · exact absurd hm (not_fib_of_between (k := 653) (by decide +kernel) (by decide +kernel) m)
    · exact absurd hm (not_fib_of_between (k := 662) (by decide +kernel) (by decide +kernel) m)
    · exact absurd hm (not_fib_of_between (k := 672) (by decide +kernel) (by decide +kernel) m)
    · exact absurd hm (not_fib_of_between (k := 681) (by decide +kernel) (by decide +kernel) m)
    · exact absurd hm (not_fib_of_between (k := 691) (by decide +kernel) (by decide +kernel) m)
    · exact absurd hm (not_fib_of_between (k := 700) (by decide +kernel) (by decide +kernel) m)
    · exact absurd hm (not_fib_of_between (k := 709) (by decide +kernel) (by decide +kernel) m)
    · exact absurd hm (not_fib_of_between (k := 719) (by decide +kernel) (by decide +kernel) m)
    · exact absurd hm (not_fib_of_between (k := 728) (by decide +kernel) (by decide +kernel) m)
    · exact absurd hm (not_fib_of_between (k := 738) (by decide +kernel) (by decide +kernel) m)
    · exact absurd hm (not_fib_of_between (k := 747) (by decide +kernel) (by decide +kernel) m)
    · exact absurd hm (not_fib_of_between (k := 757) (by decide +kernel) (by decide +kernel) m)
  · exact absurd hm (h2 n m (by omega) (h1 n m (by omega) hm))

/-- Analytic step (Gómez Ruiz–Luca, Lemma 1, via p-adic linear forms in two logarithms):
a solution with `n ≥ 101` has `n < 1.4 · 10^8`. -/
def H1 : Prop :=
  ∀ n m : ℕ, 101 ≤ n → Nat.fib m = n.factorial + n * (n + 1) / 2 → n < 140000000

/-- Computational step (Gómez Ruiz–Luca, Section 5): no solution with `101 ≤ n < 1.4 · 10^8`. -/
def H2 : Prop :=
  ∀ n m : ℕ, 101 ≤ n → n < 140000000 → ¬ Nat.fib m = n.factorial + n * (n + 1) / 2

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a101292.main := by
  intro h1 h2
  ext x
  simp only [Set.mem_inter_iff, Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨n, rfl⟩, m, hm⟩
    rw [a_eq] at hm ⊢
    rcases fib_eq_cases h1 h2 n m hm with rfl | rfl | rfl | rfl <;> decide +kernel
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨⟨0, by rw [a_eq]; try decide +kernel⟩, 1, by decide +kernel⟩
    · exact ⟨⟨1, by rw [a_eq]; try decide +kernel⟩, 3, by decide +kernel⟩
    · exact ⟨⟨2, by rw [a_eq]; try decide +kernel⟩, 5, by decide +kernel⟩
    · exact ⟨⟨4, by rw [a_eq]; try decide +kernel⟩, 9, by decide +kernel⟩

end OMA.R_oeis_a101292_R1
