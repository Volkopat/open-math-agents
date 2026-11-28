import OMAReductions.R_oeis_a070542_R1

-- Reduction oeis-a070542.R1.H2.R1 of step oeis-a070542.R1.H2
-- Credit: @John-A-McMahon

namespace OMA.R_oeis_a070542_R1_H2_R1

/-- The finite part: all positive n at most 49 with no witness are among the ten known terms.
The search is over p, q at most 2n, which is enough because p + q = 2n. -/
def H1 : Prop :=
  ∀ n : ℕ, 1 ≤ n → n ≤ 49 →
    (∀ p ∈ Finset.range (2 * n + 1), ∀ q ∈ Finset.range (2 * n + 1),
      ¬ (p.Prime ∧ q.Prime ∧ p ≠ q ∧ p ∣ Nat.choose (2 * n) n ∧
        q ∣ Nat.choose (2 * n) n ∧ p + q = 2 * n)) →
    n ∈ ({1, 2, 3, 4, 6, 10, 15, 26, 28, 64} : Set ℕ)

/-- The Goldbach-strengthening part for n at least 50: a Goldbach pair whose smaller prime
p lies in (n/2, 2n/3]. Both primes then occur in the central binomial coefficient. -/
def H2 : Prop :=
  ∀ n : ℕ, 50 ≤ n →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n < 2 * p ∧ 3 * p ≤ 2 * n ∧ q = 2 * n - p

/-- A prime p whose first base-p carry contributes to (2n choose n) divides that coefficient. -/
lemma centralBinom_dvd_of_carry (n p : ℕ) (hp : p.Prime) (hlog : Nat.log p (2 * n) < 2)
    (hcarry : p ≤ n % p + n % p) : p ∣ Nat.choose (2 * n) n := by
  rw [← Nat.centralBinom_eq_two_mul_choose n]
  apply Nat.dvd_of_factorization_pos
  have hf : (Nat.centralBinom n).factorization p = 1 := by
    rw [Nat.centralBinom_eq_two_mul_choose]
    rw [Nat.factorization_choose (p := p) (n := 2 * n) (k := n) (b := 2) hp (by omega) hlog]
    have hsub : 2 * n - n = n := by omega
    have hset : {x ∈ Finset.Ico 1 2 | p ^ x ≤ n % p ^ x + (2 * n - n) % p ^ x} = {1} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_singleton]
      constructor
      · intro h
        omega
      · intro hx
        subst x
        rw [hsub]
        simpa using hcarry
    rw [hset]
    simp
  rw [hf]
  norm_num

theorem main : H1 → H2 → OMA.R_oeis_a070542_R1.H2 := by
  intro hsmall hgold
  intro n hn
  rcases hn with ⟨hnpos, hno⟩
  by_cases hn49 : n ≤ 49
  · apply hsmall n hnpos hn49
    intro p hp_mem q hq_mem hpair
    exact hno ⟨p, q, hpair⟩
  · have hn50 : 50 ≤ n := by omega
    rcases hgold n hn50 with ⟨p, q, hp, hq, hnp, hp_le, hqeq⟩
    have hp_lt_n : p < n := by nlinarith
    have hq_gt_n : n < q := by omega
    have hp_sq : 2 * n < p ^ 2 := by nlinarith [hp.two_le]
    have hq_sq : 2 * n < q ^ 2 := by nlinarith [hq.two_le]
    have hp_dvd : p ∣ Nat.choose (2 * n) n := by
      apply centralBinom_dvd_of_carry n p hp (Nat.log_lt_of_lt_pow (by omega) hp_sq)
      rw [Nat.mod_eq_sub_mod (show p ≤ n by omega)]
      rw [Nat.mod_eq_of_lt (show n - p < p by omega)]
      omega
    have hq_dvd : q ∣ Nat.choose (2 * n) n := by
      apply centralBinom_dvd_of_carry n q hq (Nat.log_lt_of_lt_pow (by omega) hq_sq)
      rw [Nat.mod_eq_of_lt hq_gt_n]
      omega
    have hpq_ne : p ≠ q := by omega
    have hsum : p + q = 2 * n := by omega
    exfalso
    exact hno ⟨p, q, hp, hq, hpq_ne, hp_dvd, hq_dvd, hsum⟩

end OMA.R_oeis_a070542_R1_H2_R1
