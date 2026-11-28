import OMAStatements.S_oeis_a327943

/-!
# A327943: local tests and prime divisors of solutions

Credit: @jiyongparkphysics. The source statement was formalized by @luciusacarr.
Source: https://oeis.org/A327943 . The same conjecture occurs in A327468.

At a maximal prime-power divisor of a proposed modulus m, one test concerns
the cofactor modulo p and the other bounds the exponent of p. H2 asks for
candidates using arbitrarily large prime divisors. At k >= 3 every fixed
finite set of primes supports only finitely many solutions, since p^e must
divide the nonzero integer (1-k)^p-(1-k). At k = 2, powers of three suffice.
-/

namespace OMA.R_oeis_a327943_R1

/-- Each positive power of three yields a solution for base two. -/
private theorem base_two (r : ℕ) : (2 : ℤ)^(3^r) ≡ -1 [ZMOD (3 : ℤ)^(r+1)] := by
  induction r with
  | zero => decide
  | succ r ih =>
    set z := (2 : ℤ)^(3^r)
    have h3 := ih.of_dvd (dvd_pow_self (3 : ℤ) (by omega : r+1 ≠ 0))
    change z ≡ -1 [ZMOD 3] at h3
    have hfac : (3 : ℤ) ∣ z^2-z+1 := by
      have hz := ((h3.pow 2).sub h3).add_right 1
      have hr : z^2-z+1 ≡ 0 [ZMOD 3] := hz.trans (by decide)
      exact Int.modEq_zero_iff_dvd.mp hr
    have hz : (3:ℤ)^(r+1) ∣ z+1 := by simpa [sub_neg_eq_add] using ih.symm.dvd
    rw [pow_succ 3 r, pow_mul]
    change z^3 ≡ -1 [ZMOD (3:ℤ)^((r+1)+1)]
    apply Int.modEq_iff_dvd.mpr
    have heq : -1-z^3 = -((z+1)*(z^2-z+1)) := by ring
    rw [heq, dvd_neg, pow_succ]
    exact mul_dvd_mul hz hfac

/-- Exact local criterion, with one pair of tests per distinct prime factor. -/
def H1 : Prop := ∀ (a b : ℤ) (m : ℕ), 0 < m →
  (a^m ≡ b [ZMOD (m : ℤ)] ↔ ∀ p ∈ m.primeFactors,
    a^(m / p^(m.factorization p)) ≡ b [ZMOD (p : ℤ)] ∧
    b^p ≡ b [ZMOD (p : ℤ)^(m.factorization p)])

/-- Construct locally compatible moduli containing arbitrarily large primes. -/
def H2 : Prop := ∀ k : ℕ, 3 ≤ k → ∀ B : ℕ, ∃ m q : ℕ,
  0 < m ∧ q ∈ m.primeFactors ∧ B < q ∧
  ∀ p ∈ m.primeFactors,
    (k : ℤ)^(m / p^(m.factorization p)) ≡ 1-k [ZMOD (p : ℤ)] ∧
    (1-(k : ℤ))^p ≡ 1-k [ZMOD (p : ℤ)^(m.factorization p)]

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a327943.main := by
  intro localCriterion candidates k hk
  apply Set.infinite_of_not_bddAbove
  apply not_bddAbove_iff.mpr
  intro B
  by_cases htwo : k = 2
  · subst k
    refine ⟨3^(B+1), ⟨by positivity, ?_⟩, ?_⟩
    · have hm := (base_two (B+1)).of_dvd (pow_dvd_pow (3:ℤ) (by omega : B+1 ≤ (B+1)+1))
      simpa using hm
    · exact lt_trans (Nat.lt_succ_self _) (Nat.lt_pow_self (by decide : 1 < 3))
  · obtain ⟨m,q,hm,hq,hB,tests⟩ := candidates k (by omega) B
    exact ⟨m, ⟨hm, (localCriterion k (1-k) m hm).mpr tests⟩,
      lt_of_lt_of_le hB (Nat.le_of_dvd hm (Nat.mem_primeFactors.mp hq).2.1)⟩

end OMA.R_oeis_a327943_R1
