import OMAReductions.R_oeis_a067126_R1

/-!
For an odd prime square, every earlier composite has totient at most the totient of
the square. Thus the square case of the A067126 record question is exactly a question
about a prime in the interval immediately below the square. Higher prime powers
can be treated by a wider prime interval.
-/

open OMA.S_oeis_a067126

namespace OMA.R_oeis_a067126_R1_H1_R1

private theorem totient_mul_prime_le {p : ℕ} (hp : p.Prime) (v : ℕ) :
    (p * v).totient ≤ (p - 1) * v := by
  induction v using Nat.strong_induction_on with
  | h v ih =>
    by_cases hd : p ∣ v
    · obtain ⟨w, rfl⟩ := hd
      by_cases hw : w = 0
      · simp [hw]
      have hlt : w < p * w := by
        simpa using Nat.mul_lt_mul_of_pos_right hp.one_lt (Nat.pos_of_ne_zero hw)
      rw [Nat.totient_mul_of_prime_of_dvd hp (dvd_mul_right p w)]
      exact (Nat.mul_le_mul_left p (ih w hlt)).trans_eq (by ac_rfl)
    · rw [Nat.totient_mul_of_prime_of_not_dvd hp hd]
      exact Nat.mul_le_mul_left _ (Nat.totient_le v)

private theorem totient_square {p : ℕ} (hp : p.Prime) :
    (p ^ 2).totient = p * (p - 1) := by
  simpa only [pow_one] using Nat.totient_prime_pow_succ hp 1

private theorem composite_le_totient_square {p m : ℕ} (hp : p.Prime)
    (hm : 1 ≤ m) (hm' : m < p ^ 2) (hnp : ¬m.Prime) :
    m.totient ≤ p * (p - 1) := by
  by_cases hsmall : m ≤ p * (p - 1)
  · exact (Nat.totient_le _).trans hsmall
  have hmOne : m ≠ 1 := by
    have hlarge : 1 ≤ p * (p - 1) := Nat.mul_pos hp.pos (by have := hp.two_le; omega)
    omega
  let q := m.minFac
  have hq : q.Prime := Nat.minFac_prime hmOne
  have hdvd : q ∣ m := Nat.minFac_dvd m
  obtain ⟨u, hu⟩ := hdvd
  have hqu : q ≤ u := by
    have hh := Nat.minFac_le_div (by omega : 0 < m) hnp
    change q ≤ m / q at hh
    rwa [hu, Nat.mul_div_cancel_left _ hq.pos] at hh
  have hqp : q < p := by
    by_contra! hpq
    have hle : p * p ≤ q * u := Nat.mul_le_mul hpq (hpq.trans hqu)
    rw [pow_two, hu] at hm'
    omega
  have hpu : p ≤ u := by
    by_contra! hup
    have hle : q * u ≤ p * (p - 1) := Nat.mul_le_mul (by omega) (by omega)
    omega
  calc
    m.totient = (q * u).totient := by rw [← hu]
    _ ≤ (q - 1) * u := totient_mul_prime_le hq u
    _ ≤ p * (p - 1) := by
      have hsplit : (q - 1) * u + u = m := by
        calc
          (q - 1) * u + u = (q - 1) * u + 1 * u := by simp
          _ = q * u := by rw [← Nat.add_mul, Nat.sub_add_cancel hq.one_lt.le]
          _ = m := hu.symm
      rw [pow_two] at hm'
      have hpSplit : p * (p - 1) + p = p * p := by
        calc
          p * (p - 1) + p = p * (p - 1) + p * 1 := by simp
          _ = p * p := by rw [← Nat.mul_add, Nat.sub_add_cancel hp.one_lt.le]
      omega

/-- An exact prime interval criterion for a prime square to be a record. -/
private theorem square_record_iff {p : ℕ} (hp : p.Prime) :
    IsTerm (p ^ 2) ↔ ¬∃ q : ℕ, q.Prime ∧ p * (p - 1) + 1 < q ∧ q < p ^ 2 := by
  constructor
  · intro h ⟨q, hq, hlow, hhigh⟩
    have hbound := h q hq.one_lt.le hhigh
    rw [Nat.totient_prime hq, totient_square hp] at hbound
    omega
  · intro h m hm hlt
    rw [totient_square hp]
    by_cases hmp : m.Prime
    · rw [Nat.totient_prime hmp]
      by_contra! hno
      exact h ⟨m, hmp, by omega, hlt⟩
    · exact composite_le_totient_square hp hm hlt hmp

/-- The exact missing prime interval for squares of odd primes greater than 3. -/
def H1 : Prop := ∀ p : ℕ, p.Prime → 3 < p →
  ∃ q : ℕ, q.Prime ∧ p * (p - 1) + 1 < q ∧ q < p ^ 2

/-- Prime intervals beneath prime powers of exponent at least three. -/
def H2 : Prop := ∀ p k : ℕ, p.Prime → Odd p → 2 ≤ k →
  ∃ q : ℕ, q.Prime ∧ p ^ k * (p - 1) + 1 < q ∧ q < p ^ (k + 1)

theorem main : H1 → H2 → OMA.R_oeis_a067126_R1.H1 := by
  intro hs hh n _ hnodd hpp hnprime hrecord
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).mp hpp
  have hpodd : Odd p := by
    rcases hp.eq_two_or_odd' with he | ho
    · subst p
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
      exact (hnodd.not_two_dvd_nat (by rw [pow_succ]; exact dvd_mul_left 2 _)).elim
    · exact ho
  have hk2 : 2 ≤ k := by
    by_contra! h1
    have heq : k = 1 := by omega
    exact hnprime (by simpa [heq] using hp)
  by_cases hsq : k = 2
  · subst k
    by_cases hthree : p = 3
    · simp [hthree]
    have hthreeLe : 3 ≤ p := hp.odd_iff.mp hpodd
    obtain ⟨q, hq, hlo, hhi⟩ := hs p hp (by omega)
    exact ((square_record_iff hp).mp hrecord ⟨q, hq, hlo, hhi⟩).elim
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
    obtain ⟨q, hq, hlo, hhi⟩ := hh p j hp hpodd (by omega)
    have hbound := hrecord q hq.one_lt.le hhi
    rw [Nat.totient_prime hq, Nat.totient_prime_pow_succ hp] at hbound
    omega

end OMA.R_oeis_a067126_R1_H1_R1
