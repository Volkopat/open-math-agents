import OMAReductions.R_mo_503999_R1

/-!
Step `mo-503999.R1.H1`: a palindromic product of three consecutive primes that is divisible
by 11 is `1001`.

11 is prime, so it equals one of the three primes, and `11 = nth Prime 4`, so the index `i`
is 2, 3 or 4. The three products are `5 * 7 * 11 = 385`, `7 * 11 * 13 = 1001` and
`11 * 13 * 17 = 2431`; only `1001` is a palindrome.
-/

open OMA.S_mo_503999

namespace OMA.Step_mo_503999_R1_H1

lemma nth_of_count {p k : ℕ} (hp : p.Prime) (hc : Nat.count Nat.Prime p = k) :
    Nat.nth Nat.Prime k = p := by
  rw [← hc]; exact Nat.nth_count hp

lemma p2 : Nat.nth Nat.Prime 2 = 5 := nth_of_count (by norm_num) (by decide)
lemma p3 : Nat.nth Nat.Prime 3 = 7 := nth_of_count (by norm_num) (by decide)
lemma p4 : Nat.nth Nat.Prime 4 = 11 := nth_of_count (by norm_num) (by decide)
lemma p5 : Nat.nth Nat.Prime 5 = 13 := nth_of_count (by norm_num) (by decide)
lemma p6 : Nat.nth Nat.Prime 6 = 17 := nth_of_count (by norm_num) (by decide)

/-- If `11 = nth Prime j` then `j = 4`. -/
lemma idx_eq {j : ℕ} (h : Nat.nth Nat.Prime j = 11) : j = 4 :=
  Nat.nth_injective Nat.infinite_setOfPred_prime (h.trans p4.symm)

lemma prime_nth (j : ℕ) : (Nat.nth Nat.Prime j).Prime :=
  Nat.prime_nth_prime j

/-- 11 dividing a prime forces equality. -/
lemma eq_of_dvd {j : ℕ} (h : 11 ∣ Nat.nth Nat.Prime j) : Nat.nth Nat.Prime j = 11 :=
  ((Nat.prime_dvd_prime_iff_eq (by norm_num) (prime_nth j)).1 h).symm

end OMA.Step_mo_503999_R1_H1

open OMA.Step_mo_503999_R1_H1 in
theorem OMA.solution : OMA.R_mo_503999_R1.H1 := by
  intro i hpal h11
  have h11p : Nat.Prime 11 := by norm_num
  have hi : i = 2 ∨ i = 3 ∨ i = 4 := by
    rcases (Nat.Prime.dvd_mul h11p).1 h11 with h | h
    · rcases (Nat.Prime.dvd_mul h11p).1 h with h | h
      · have := idx_eq (eq_of_dvd h); omega
      · have := idx_eq (eq_of_dvd h); omega
    · have := idx_eq (eq_of_dvd h); omega
  rcases hi with rfl | rfl | rfl
  · exfalso
    rw [p2, p3, p4] at hpal
    revert hpal
    norm_num [IsPalindrome]
  · rw [p3, p4, p5]
  · exfalso
    rw [p4, p5, p6] at hpal
    revert hpal
    norm_num [IsPalindrome]
