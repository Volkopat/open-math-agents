import OMAStatements.S_oeis_a401759

-- Problem: A401759: a(n) = number of primes p <= n, taken in decreasing order starting from the largest, that must be tried before reaching the first one for which 2*n - p is also prime.
-- Credit: original proof by @agchua (#20391).
-- Simplify the optional-value existence equivalence directly by its two definition branches.
-- Proof idea: a n is some value iff good n is nonempty; a prime p <= n with 2n - p prime gives
-- 2n = p + (2n - p), and from 2n = p + q the smaller of p, q is at most n. The Goldbach
-- conjecture is the same statement for the even numbers 2n > 2.

open OMA.S_oeis_a401759 in
theorem OMA.solution : type_of% @OMA.S_oeis_a401759.main := by
  have hdef : ∀ n : ℕ, (∃ v, a n = some v) ↔ (good n).Nonempty := by
    intro n
    unfold a
    split_ifs <;> simp_all
  have hgood : ∀ n : ℕ, (good n).Nonempty ↔ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = 2 * n := by
    intro n
    constructor
    · rintro ⟨p, hp⟩
      simp only [good, Finset.mem_filter, Finset.mem_range] at hp
      obtain ⟨hp1, hp2, hp3⟩ := hp
      exact ⟨p, 2 * n - p, hp2, hp3, by omega⟩
    · rintro ⟨p, q, hp, hq, hpq⟩
      by_cases hpn : p ≤ n
      · refine ⟨p, ?_⟩
        simp only [good, Finset.mem_filter, Finset.mem_range]
        have e : 2 * n - p = q := by omega
        rw [e]
        exact ⟨by omega, hp, hq⟩
      · refine ⟨q, ?_⟩
        simp only [good, Finset.mem_filter, Finset.mem_range]
        have e : 2 * n - q = p := by omega
        rw [e]
        exact ⟨by omega, hq, hp⟩
  have h1 : ∀ n : ℕ, (∃ v, a n = some v) ↔ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = 2 * n :=
    fun n => (hdef n).trans (hgood n)
  refine ⟨h1, ?_⟩
  constructor
  · intro hall m hm he
    obtain ⟨r, hr⟩ := he
    obtain ⟨p, q, hp, hq, hpq⟩ := (h1 r).mp (hall r (by omega))
    exact ⟨p, q, hp, hq, by omega⟩
  · intro hG n hn
    obtain ⟨p, q, hp, hq, hpq⟩ := hG (2 * n) (by omega) (even_two_mul n)
    exact (h1 n).mpr ⟨p, q, hp, hq, hpq⟩
