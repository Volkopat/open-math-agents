import OMAStatements.S_oeis_a330724
import Mathlib

/-!
# A330724: every admissible `m` is a sum of prime factors of a composite number coprime to `6`

Take `k = 5^a · 7^b · 11^c`.  Its prime factors, with multiplicity, are `a` fives, `b` sevens and
`c` elevens, so their sum is `5a + 7b + 11c` and their number is `a + b + c`.  Such a `k` is
coprime to `6`, and it is composite as soon as `a + b + c ≥ 2`.

Every `m ≥ 28` is `5a + 7b` with `b = 3m mod 5`; the remaining admissible values
`12, 14, 16, …, 27` (all `m ≥ 12` except `13` and `15`) are handled by explicit exponents.
-/

namespace OMA.S_oeis_a330724

/-- The prime factors of `5^a · 7^b · 11^c`. -/
lemma perm_factors (a b c : ℕ) : (5 ^ a * 7 ^ b * 11 ^ c).primeFactorsList.Perm
    (List.replicate a 5 ++ List.replicate b 7 ++ List.replicate c 11) := by
  have h5 : (5 ^ a).primeFactorsList = List.replicate a 5 :=
    Nat.Prime.primeFactorsList_pow (by norm_num) a
  have h7 : (7 ^ b).primeFactorsList = List.replicate b 7 :=
    Nat.Prime.primeFactorsList_pow (by norm_num) b
  have h11 : (11 ^ c).primeFactorsList = List.replicate c 11 :=
    Nat.Prime.primeFactorsList_pow (by norm_num) c
  have p1 := Nat.perm_primeFactorsList_mul (a := 5 ^ a * 7 ^ b) (b := 11 ^ c)
    (by positivity) (by positivity)
  have p2 := Nat.perm_primeFactorsList_mul (a := 5 ^ a) (b := 7 ^ b) (by positivity) (by positivity)
  rw [h11] at p1
  rw [h5, h7] at p2
  exact p1.trans (p2.append_right _)

/-- The witness for exponents with `a + b + c ≥ 2`. -/
lemma witness (a b c : ℕ) (h : 2 ≤ a + b + c) :
    ∃ k : ℕ, 1 < k ∧ ¬ k.Prime ∧ Nat.Coprime k 6 ∧
      k.primeFactorsList.sum = 5 * a + 7 * b + 11 * c := by
  have hp := perm_factors a b c
  have hsum : (5 ^ a * 7 ^ b * 11 ^ c).primeFactorsList.sum = 5 * a + 7 * b + 11 * c := by
    rw [hp.sum_eq]
    simp
    ring
  have hlen : (5 ^ a * 7 ^ b * 11 ^ c).primeFactorsList.length = a + b + c := by
    rw [hp.length_eq]
    simp
    omega
  have hpos : 0 < 5 ^ a * 7 ^ b * 11 ^ c := by positivity
  have hnp : ¬ (5 ^ a * 7 ^ b * 11 ^ c).Prime := by
    intro hprime
    rw [Nat.primeFactorsList_prime hprime] at hlen
    simp at hlen
    omega
  refine ⟨5 ^ a * 7 ^ b * 11 ^ c, ?_, hnp, ?_, hsum⟩
  · by_contra hk
    have h1 : 5 ^ a * 7 ^ b * 11 ^ c = 1 := by omega
    rw [h1] at hlen
    simp at hlen
    omega
  · exact Nat.Coprime.mul_left (Nat.Coprime.mul_left (Nat.Coprime.pow_left a (by decide))
      (Nat.Coprime.pow_left b (by decide))) (Nat.Coprime.pow_left c (by decide))

/-- Exponents for every admissible `m`. -/
lemma exponents (m : ℕ) (hm : (m % 2 = 0 ∧ 10 < m) ∨ (m % 2 = 1 ∧ 15 < m)) :
    ∃ a b c : ℕ, 2 ≤ a + b + c ∧ 5 * a + 7 * b + 11 * c = m := by
  rcases Nat.lt_or_ge m 28 with hlt | hge
  · have h12 : 12 ≤ m := by omega
    interval_cases m
    · exact ⟨1, 1, 0, by norm_num, by norm_num⟩
    · omega
    · exact ⟨0, 2, 0, by norm_num, by norm_num⟩
    · omega
    · exact ⟨1, 0, 1, by norm_num, by norm_num⟩
    · exact ⟨2, 1, 0, by norm_num, by norm_num⟩
    · exact ⟨0, 1, 1, by norm_num, by norm_num⟩
    · exact ⟨1, 2, 0, by norm_num, by norm_num⟩
    · exact ⟨4, 0, 0, by norm_num, by norm_num⟩
    · exact ⟨0, 3, 0, by norm_num, by norm_num⟩
    · exact ⟨0, 0, 2, by norm_num, by norm_num⟩
    · exact ⟨1, 1, 1, by norm_num, by norm_num⟩
    · exact ⟨2, 2, 0, by norm_num, by norm_num⟩
    · exact ⟨5, 0, 0, by norm_num, by norm_num⟩
    · exact ⟨1, 3, 0, by norm_num, by norm_num⟩
    · exact ⟨4, 1, 0, by norm_num, by norm_num⟩
  · exact ⟨(m - 7 * (3 * m % 5)) / 5, 3 * m % 5, 0, by omega, by omega⟩

end OMA.S_oeis_a330724

open OMA.S_oeis_a330724 in
theorem OMA.solution : type_of% @OMA.S_oeis_a330724.main := by
  intro m hm
  have hm' : (m % 2 = 0 ∧ 10 < m) ∨ (m % 2 = 1 ∧ 15 < m) := by
    rcases hm with ⟨he, h⟩ | ⟨ho, h⟩
    · exact Or.inl ⟨Nat.even_iff.mp he, h⟩
    · exact Or.inr ⟨Nat.odd_iff.mp ho, h⟩
  obtain ⟨a, b, c, habc, hsum⟩ := exponents m hm'
  obtain ⟨k, h1, h2, h3, h4⟩ := witness a b c habc
  exact ⟨k, h1, h2, h3, by rw [h4, hsum]⟩
