import OMAStatements.S_oeis_a069548

open Finset ArithmeticFunction
open OMA.S_oeis_a069548
open scoped ArithmeticFunction.zeta

namespace OMA.A069548

private theorem twoZero : (2 : ZMod 2) = 0 := by decide

-- Only odd nonsquarefree divisors contribute to parity.
private theorem termCast (d : ℕ) :
    (summand d : ZMod 2) = (d : ZMod 2) * (1 + (moebius d : ZMod 2)) := by
  rcases moebius_eq_or d with h | h | h <;> rw [summand, h]
  · have hdiv : 6 * (d : ℤ) / (2 + 0) = 3 * d := by omega
    rw [hdiv]
    push_cast
    have hthree : (3 : ZMod 2) = 1 := by decide
    simp [hthree]
  · have hdiv : 6 * (d : ℤ) / (2 + 1) = 2 * d := by omega
    rw [hdiv]
    push_cast
    simp [twoZero, show (1 : ZMod 2) + 1 = 0 by decide]
  · have hdiv : 6 * (d : ℤ) / (2 + -1) = 6 * d := by omega
    rw [hdiv]
    push_cast
    simp [show (6 : ZMod 2) = 0 by decide, show (1 : ZMod 2) + 1 = 0 by decide]

private theorem oddDivisors (e m : ℕ) (hm : Odd m) :
    ((2 ^ e * m).divisors.filter Odd) = m.divisors := by
  ext d
  simp only [mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hd, _⟩, ho⟩
    exact ⟨(ho.coprime_two_right.pow_right _).dvd_of_dvd_mul_left hd, hm.pos.ne'⟩
  · rintro ⟨hd, hm0⟩
    exact ⟨⟨dvd_mul_of_dvd_right hd _, mul_ne_zero (by positivity) hm0⟩, hm.of_dvd_nat hd⟩

private theorem sumMu (m : ℕ) :
    (∑ d ∈ m.divisors, moebius d) = if m = 1 then 1 else 0 := by
  rw [← coe_mul_zeta_apply, moebius_mul_coe_zeta, one_apply]

private theorem divisorCast (e m : ℕ) (hm : Odd m) :
    (divisorSum (2 ^ e * m) : ZMod 2) =
      (m.divisors.card : ZMod 2) + (if m = 1 then 1 else 0) := by
  unfold divisorSum
  rw [Int.cast_sum]
  simp only [termCast]
  have hfilter :
      (∑ d ∈ (2 ^ e * m).divisors, (d : ZMod 2) * (1 + (moebius d : ZMod 2))) =
        ∑ d ∈ (2 ^ e * m).divisors.filter Odd, (1 + (moebius d : ZMod 2)) := by
    rw [sum_filter]
    apply sum_congr rfl
    intro d _
    by_cases ho : Odd d
    · have hc : (d : ZMod 2) = 1 :=
        (ZMod.natCast_eq_natCast_iff d 1 2).mpr (Nat.odd_iff.mp ho)
      simp [ho, hc]
    · have hc : (d : ZMod 2) = 0 :=
        (CharP.cast_eq_zero_iff (ZMod 2) 2 d).mpr (Nat.not_odd_iff_even.mp ho).two_dvd
      simp [ho, hc]
  rw [hfilter, oddDivisors e m hm, sum_add_distrib, ← Int.cast_sum, sumMu]
  by_cases hm1 : m = 1 <;> simp [hm1]

private theorem squareOfOddCard {m : ℕ} (hm : m ≠ 0) (h : Odd m.divisors.card) :
    IsSquare m := by
  rw [Nat.card_divisors hm] at h
  let u := ∏ p ∈ m.primeFactors, p ^ (m.factorization p / 2)
  refine ⟨u, ?_⟩
  calc
    m = ∏ p ∈ m.primeFactors, p ^ m.factorization p := by
      simpa only [Finsupp.prod, Nat.support_factorization] using
        (Nat.prod_factorization_pow_eq_self hm).symm
    _ = ∏ p ∈ m.primeFactors, (p ^ (m.factorization p / 2)) ^ 2 := by
      apply prod_congr rfl
      intro p hp
      have hnum := Nat.odd_iff.mp (h.of_dvd_nat (dvd_prod_of_mem _ hp))
      rw [← pow_mul, show m.factorization p / 2 * 2 = m.factorization p by omega]
    _ = u ^ 2 := by rw [prod_pow]
    _ = u * u := pow_two u

theorem solution : type_of% @OMA.S_oeis_a069548.main := by
  intro n hn ho
  obtain ⟨e, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd (by omega : n ≠ 0)
  have hs : (divisorSum (2 ^ e * m) : ZMod 2) = 1 := by
    obtain ⟨j, hj⟩ := odd_iff_exists_bit1.mp ho
    rw [hj]
    push_cast
    simp [twoZero]
  have hcast := divisorCast e m hm
  rw [hs] at hcast
  have h1 : m ≠ 1 := by
    intro he
    simp [he, show (1 : ZMod 2) + 1 = 0 by decide] at hcast
  have hc : (m.divisors.card : ZMod 2) = 1 := by simpa [h1] using hcast.symm
  have hOdd : Odd m.divisors.card :=
    Nat.odd_iff.mpr ((ZMod.natCast_eq_natCast_iff _ 1 2).mp hc)
  obtain ⟨u, he⟩ := squareOfOddCard hm.pos.ne' hOdd
  rcases Nat.even_or_odd e with h | h
  · obtain ⟨v, hv⟩ := h
    exact Or.inl ⟨2 ^ v * u, by rw [hv, pow_add, he]; ring⟩
  · obtain ⟨v, hv⟩ := h
    exact Or.inr ⟨2 ^ v * u, by rw [hv, pow_succ, mul_comm 2 v, pow_mul, he]; ring⟩

end OMA.A069548

theorem OMA.solution : type_of% @OMA.S_oeis_a069548.main := OMA.A069548.solution
