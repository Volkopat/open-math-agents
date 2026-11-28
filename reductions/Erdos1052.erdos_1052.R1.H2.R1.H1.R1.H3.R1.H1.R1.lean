import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H3_R1

-- Reduction Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H3.R1.H1.R1
-- Credit: @adammcarter
-- Splits step H1 of Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H3.R1 (3 is a repeated prime, at least two
-- repeated odd primes, S not admissible) by the exponent of 3, with multi-prime forms of the
-- round-4 kill lemmas for 3, 5 and 7 built in.  Proving H1 and H2 proves the step.
--
-- Notation: n unitary perfect, a = padicValNat 2 n, e(z) = n.factorization z, S = the repeated odd
-- primes.  e is an ODD MULTIPLE of d when e mod 2d = d; then 1 + z^d divides 1 + z^e.
--
-- PROVED BELOW (any S, any exponents; table3, table5, table7): for z = 3, 5, 7 and each d in
-- the tables written out in H1 and H2 there is an explicit finite list L(z, d) of primes, such that
-- if z is repeated and e(z) is an odd multiple of d, then S contains a prime of L(z, d).
-- L(z, d) is the forced chain of the round-4 kill lemma kill<z>_e<d> plus its collision prime.
-- Reason: those lemmas use the balance equation only through the kernel-generic lemma facts. With
-- kernel S the same chain still gives a contradiction unless one of its primes is repeated.
-- Examples: e(3) = 10 mod 20 forces 5 into S (25 divides 1 + 3^10); e(3) = 21 mod 42 forces 7;
-- e(5) = 26 mod 52 forces 13; e(7) = 2 mod 4 forces 5.  For z = 5, 7 only the d whose list avoids 3
-- are written (3 is in S here, so the others say nothing).  For 2 <= e(3) <= 40, the values not
-- covered by the table for 3 are 2, 3, 4, 5, 7, 11, 13, 19.
--
-- H1 (OPEN): e(3) is an odd multiple of some d in the table for 3, S meets L(3, d) for every
--    such d, and the clauses for 5 and 7 hold.
-- H2 (OPEN): e(3) is an odd multiple of no d in the table for 3, and the clauses for 5 and 7 hold.

namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H3_R1_H1_R1

open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1 (facts S_sq two_dvd_of_isUnitaryPerfect
  one_add_pow_dvd_of_odd_mul prime_74480363 prime_266442959 prime_4795973261 prime_23535794707
  prime_374857981681 prime_926510094425921 prime_234750601 prime_59509429687890001
  prime_29754714843945001)
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1 (kernel_balance)
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H3_R1 (fact_pos)

-- H1: e(3) is an odd multiple of some d in D3; S meets L(3, d) for every such d; clauses for 5, 7.
def H1 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    ∀ S : Finset ℕ, (∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n) → 2 ≤ S.card →
    ¬ ((∀ z ∈ S, 128 ≤ z ∧ S.card + 3 ≤ z) ∧
      ∏ z ∈ S, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (S.card : ℚ))) ≤ 2101 / 2097) →
    3 ∈ S →
    ¬ (∀ d ∈ ({6, 8, 9, 10, 12, 14, 15, 16, 17, 20, 21, 22, 23, 25, 26, 28, 29, 31, 32, 33, 34, 35, 37, 38, 39} : Finset ℕ), n.factorization 3 % (2 * d) ≠ d) →
    (∀ dL ∈ ([(6, [73, 37, 19, 5]), (8, [193, 97, 7]), (9, [37, 19]), (10, [5]),
      (12, [41, 6481, 7]), (14, [29, 5]), (15, [61, 31]), (16, [21523361, 61, 31]),
      (17, [103, 13, 307, 7]), (20, [41, 42521761, 21260881, 10630441, 139, 7]),
      (21, [7]), (22, [5501, 570461, 3067, 13, 7]),
      (23, [23535794707, 79, 74480363, 98519, 5]), (25, [151, 19, 22996651, 29, 5]),
      (26, [4795973261, 266442959, 5]), (28, [41, 430697, 3121, 7]),
      (29, [5385997, 2692999, 5]), (31, [6883, 1721, 41, 7]),
      (32, [926510094425921, 6883, 1721, 41, 7]), (33, [661, 331, 83, 7]),
      (34, [956353, 68311, 8539, 5]), (35, [547, 137, 374857981681, 2851, 23]),
      (37, [18427, 271, 17]), (38, [5301533, 126227, 157, 79, 5]), (39, [157, 79])] : List (ℕ × List ℕ)),
      n.factorization 3 % (2 * dL.1) = dL.1 → ∃ c ∈ dL.2, c ∈ S) →
    (5 ∈ S → ∀ dL ∈ ([(6, [13, 601, 7]), (10, [13, 41, 7]), (14, [234750601, 5953, 13]),
      (20, [241, 11]), (26, [13]),
      (28, [59509429687890001, 29754714843945001, 83, 7679233, 769, 7]),
      (34, [13, 1973, 7])] : List (ℕ × List ℕ)),
      n.factorization 5 % (2 * dL.1) = dL.1 → ∃ c ∈ dL.2, c ∈ S) →
    (7 ∈ S → ∀ dL ∈ ([(2, [5]), (19, [351121, 419]), (32, [7699649, 5]), (37, [149, 5])] : List (ℕ × List ℕ)),
      n.factorization 7 % (2 * dL.1) = dL.1 → ∃ c ∈ dL.2, c ∈ S) →
    padicValNat 2 n ≤ A

-- H2: e(3) is an odd multiple of no d in D3; clauses for 5, 7.
def H2 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    ∀ S : Finset ℕ, (∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n) → 2 ≤ S.card →
    ¬ ((∀ z ∈ S, 128 ≤ z ∧ S.card + 3 ≤ z) ∧
      ∏ z ∈ S, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (S.card : ℚ))) ≤ 2101 / 2097) →
    3 ∈ S →
    (∀ d ∈ ({6, 8, 9, 10, 12, 14, 15, 16, 17, 20, 21, 22, 23, 25, 26, 28, 29, 31, 32, 33, 34, 35, 37, 38, 39} : Finset ℕ), n.factorization 3 % (2 * d) ≠ d) →
    (5 ∈ S → ∀ dL ∈ ([(6, [13, 601, 7]), (10, [13, 41, 7]), (14, [234750601, 5953, 13]),
      (20, [241, 11]), (26, [13]),
      (28, [59509429687890001, 29754714843945001, 83, 7679233, 769, 7]),
      (34, [13, 1973, 7])] : List (ℕ × List ℕ)),
      n.factorization 5 % (2 * dL.1) = dL.1 → ∃ c ∈ dL.2, c ∈ S) →
    (7 ∈ S → ∀ dL ∈ ([(2, [5]), (19, [351121, 419]), (32, [7699649, 5]), (37, [149, 5])] : List (ℕ × List ℕ)),
      n.factorization 7 % (2 * dL.1) = dL.1 → ∃ c ∈ dL.2, c ∈ S) →
    padicValNat 2 n ≤ A

-- Section 1. The round-4 kill lemmas with an arbitrary kernel N (each prime of the list must lie
-- outside N).

theorem mkill3_e6 {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 6 ∣ K') (hL : ∀ c ∈ ([73, 37, 19, 5] : List ℕ), c ∉ N) : False := by
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g73 : 73 ∈ P := S7 73 (by norm_num) (by norm_num) (hL _ (by simp))
    ((by norm_num : 73 ∣ 1 + 3 ^ 6).trans hd)
  have g37 : 37 ∈ P := S1 37 (by norm_num) (by norm_num) (hL _ (by simp)) 73 g73 (by norm_num)
  have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hL _ (by simp)) 37 g37 (by norm_num)
  exact S8 5 (by norm_num) (by norm_num) (hL _ (by simp)) ((by norm_num : 5 ∣ 1 + 3 ^ 6).trans hd) 19 g19 (by norm_num)

theorem mkill3_e8 {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 8 ∣ K') (hL : ∀ c ∈ ([193, 97, 7] : List ℕ), c ∉ N) : False := by
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g193 : 193 ∈ P := S7 193 (by norm_num) (by norm_num) (hL _ (by simp))
    ((by norm_num : 193 ∣ 1 + 3 ^ 8).trans hd)
  have g97 : 97 ∈ P := S1 97 (by norm_num) (by norm_num) (hL _ (by simp)) 193 g193 (by norm_num)
  exact S6 7 (by norm_num) (by norm_num) (hL _ (by simp)) 97 g97 (by norm_num)

theorem mkill3_e9 {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 9 ∣ K') (hL : ∀ c ∈ ([37, 19] : List ℕ), c ∉ N) : False := by
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g37 : 37 ∈ P := S7 37 (by norm_num) (by norm_num) (hL _ (by simp))
    ((by norm_num : 37 ∣ 1 + 3 ^ 9).trans hd)
  exact S8 19 (by norm_num) (by norm_num) (hL _ (by simp)) ((by norm_num : 19 ∣ 1 + 3 ^ 9).trans hd) 37 g37 (by norm_num)

theorem mkill3_e10 {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 10 ∣ K') (hL : ∀ c ∈ ([5] : List ℕ), c ∉ N) : False := by
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  exact S_sq hP hK E (c := 5) (by norm_num) (by norm_num) (hL _ (by simp))
    ((((by norm_num : 5 * 5 ∣ 1 + 3 ^ 10).trans hd).mul_left _).mul_right _)

theorem mkill3_e12 {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 12 ∣ K') (hL : ∀ c ∈ ([41, 6481, 7] : List ℕ), c ∉ N) : False := by
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g41 : 41 ∈ P := S7 41 (by norm_num) (by norm_num) (hL _ (by simp))
    ((by norm_num : 41 ∣ 1 + 3 ^ 12).trans hd)
  have g6481 : 6481 ∈ P := S7 6481 (by norm_num) (by norm_num) (hL _ (by simp))
    ((by norm_num : 6481 ∣ 1 + 3 ^ 12).trans hd)
  have := S3 7 (by norm_num) (by norm_num) (hL _ (by simp)) 41 g41 6481 g6481 (by norm_num) (by norm_num)
  omega

theorem mkill3_e14 {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 14 ∣ K') (hL : ∀ c ∈ ([29, 5] : List ℕ), c ∉ N) : False := by
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g29 : 29 ∈ P := S7 29 (by norm_num) (by norm_num) (hL _ (by simp))
    ((by norm_num : 29 ∣ 1 + 3 ^ 14).trans hd)
  exact S8 5 (by norm_num) (by norm_num) (hL _ (by simp)) ((by norm_num : 5 ∣ 1 + 3 ^ 14).trans hd) 29 g29 (by norm_num)

theorem mkill3_e15 {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 15 ∣ K') (hL : ∀ c ∈ ([61, 31] : List ℕ), c ∉ N) : False := by
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g61 : 61 ∈ P := S7 61 (by norm_num) (by norm_num) (hL _ (by simp))
    ((by norm_num : 61 ∣ 1 + 3 ^ 15).trans hd)
  exact S8 31 (by norm_num) (by norm_num) (hL _ (by simp)) ((by norm_num : 31 ∣ 1 + 3 ^ 15).trans hd) 61 g61 (by norm_num)

theorem mkill3_e16 {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 16 ∣ K') (hL : ∀ c ∈ ([21523361, 61, 31] : List ℕ), c ∉ N) : False := by
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g21523361 : 21523361 ∈ P := S7 21523361 (by norm_num) (by norm_num) (hL _ (by simp))
    ((by norm_num : 21523361 ∣ 1 + 3 ^ 16).trans hd)
  have g61 : 61 ∈ P := S1 61 (by norm_num) (by norm_num) (hL _ (by simp)) 21523361 g21523361 (by norm_num)
  have := S3 31 (by norm_num) (by norm_num) (hL _ (by simp)) 21523361 g21523361 61 g61 (by norm_num) (by norm_num)
  omega

theorem mkill3_e17 {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 17 ∣ K') (hL : ∀ c ∈ ([103, 13, 307, 7] : List ℕ), c ∉ N) : False := by
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g103 : 103 ∈ P := S7 103 (by norm_num) (by norm_num) (hL _ (by simp))
    ((by norm_num : 103 ∣ 1 + 3 ^ 17).trans hd)
  have g13 : 13 ∈ P := S1 13 (by norm_num) (by norm_num) (hL _ (by simp)) 103 g103 (by norm_num)
  have g307 : 307 ∈ P := S7 307 (by norm_num) (by norm_num) (hL _ (by simp))
    ((by norm_num : 307 ∣ 1 + 3 ^ 17).trans hd)
  have := S3 7 (by norm_num) (by norm_num) (hL _ (by simp)) 13 g13 307 g307 (by norm_num) (by norm_num)
  omega

theorem mkill3_e20 {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 20 ∣ K') (hL : ∀ c ∈ ([41, 42521761, 21260881, 10630441, 139, 7] : List ℕ), c ∉ N) : False := by
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g41 : 41 ∈ P := S7 41 (by norm_num) (by norm_num) (hL _ (by simp))
    ((by norm_num : 41 ∣ 1 + 3 ^ 20).trans hd)
  have g42521761 : 42521761 ∈ P := S7 42521761 (by norm_num) (by norm_num) (hL _ (by simp))
    ((by norm_num : 42521761 ∣ 1 + 3 ^ 20).trans hd)
  have g21260881 : 21260881 ∈ P := S1 21260881 (by norm_num) (by norm_num) (hL _ (by simp)) 42521761 g42521761 (by norm_num)
  have g10630441 : 10630441 ∈ P := S1 10630441 (by norm_num) (by norm_num) (hL _ (by simp)) 21260881 g21260881 (by norm_num)
  have g139 : 139 ∈ P := S1 139 (by norm_num) (by norm_num) (hL _ (by simp)) 10630441 g10630441 (by norm_num)
  have := S3 7 (by norm_num) (by norm_num) (hL _ (by simp)) 41 g41 139 g139 (by norm_num) (by norm_num)
  omega

theorem mkill3_e21 {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 21 ∣ K') (hL : ∀ c ∈ ([7] : List ℕ), c ∉ N) : False := by
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  exact S_sq hP hK E (c := 7) (by norm_num) (by norm_num) (hL _ (by simp))
    ((((by norm_num : 7 * 7 ∣ 1 + 3 ^ 21).trans hd).mul_left _).mul_right _)

theorem mkill3_e22 {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 22 ∣ K') (hL : ∀ c ∈ ([5501, 570461, 3067, 13, 7] : List ℕ), c ∉ N) : False := by
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g5501 : 5501 ∈ P := S7 5501 (by norm_num) (by norm_num) (hL _ (by simp))
    ((by norm_num : 5501 ∣ 1 + 3 ^ 22).trans hd)
  have g570461 : 570461 ∈ P := S7 570461 (by norm_num) (by norm_num) (hL _ (by simp))
    ((by norm_num : 570461 ∣ 1 + 3 ^ 22).trans hd)
  have g3067 : 3067 ∈ P := S1 3067 (by norm_num) (by norm_num) (hL _ (by simp)) 570461 g570461 (by norm_num)
  have g13 : 13 ∈ P := S1 13 (by norm_num) (by norm_num) (hL _ (by simp)) 3067 g3067 (by norm_num)
  have := S3 7 (by norm_num) (by norm_num) (hL _ (by simp)) 5501 g5501 13 g13 (by norm_num) (by norm_num)
  omega

theorem mkill3_e25 {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 25 ∣ K') (hL : ∀ c ∈ ([151, 19, 22996651, 29, 5] : List ℕ), c ∉ N) : False := by
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g151 : 151 ∈ P := S7 151 (by norm_num) (by norm_num) (hL _ (by simp))
    ((by norm_num : 151 ∣ 1 + 3 ^ 25).trans hd)
  have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hL _ (by simp)) 151 g151 (by norm_num)
  have g22996651 : 22996651 ∈ P := S7 22996651 (by norm_num) (by norm_num) (hL _ (by simp))
    ((by norm_num : 22996651 ∣ 1 + 3 ^ 25).trans hd)
  have g29 : 29 ∈ P := S1 29 (by norm_num) (by norm_num) (hL _ (by simp)) 22996651 g22996651 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hL _ (by simp)) 19 g19 29 g29 (by norm_num) (by norm_num)
  omega

theorem mkill3_e28 {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 28 ∣ K') (hL : ∀ c ∈ ([41, 430697, 3121, 7] : List ℕ), c ∉ N) : False := by
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g41 : 41 ∈ P := S7 41 (by norm_num) (by norm_num) (hL _ (by simp))
    ((by norm_num : 41 ∣ 1 + 3 ^ 28).trans hd)
  have g430697 : 430697 ∈ P := S7 430697 (by norm_num) (by norm_num) (hL _ (by simp))
    ((by norm_num : 430697 ∣ 1 + 3 ^ 28).trans hd)
  have g3121 : 3121 ∈ P := S1 3121 (by norm_num) (by norm_num) (hL _ (by simp)) 430697 g430697 (by norm_num)
  have := S3 7 (by norm_num) (by norm_num) (hL _ (by simp)) 41 g41 3121 g3121 (by norm_num) (by norm_num)
  omega

theorem mkill3_e29 {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 29 ∣ K') (hL : ∀ c ∈ ([5385997, 2692999, 5] : List ℕ), c ∉ N) : False := by
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g5385997 : 5385997 ∈ P := S7 5385997 (by norm_num) (by norm_num) (hL _ (by simp))
    ((by norm_num : 5385997 ∣ 1 + 3 ^ 29).trans hd)
  have g2692999 : 2692999 ∈ P := S1 2692999 (by norm_num) (by norm_num) (hL _ (by simp)) 5385997 g5385997 (by norm_num)
  exact S6 5 (by norm_num) (by norm_num) (hL _ (by simp)) 2692999 g2692999 (by norm_num)

theorem mkill3_e31 {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 31 ∣ K') (hL : ∀ c ∈ ([6883, 1721, 41, 7] : List ℕ), c ∉ N) : False := by
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g6883 : 6883 ∈ P := S7 6883 (by norm_num) (by norm_num) (hL _ (by simp))
    ((by norm_num : 6883 ∣ 1 + 3 ^ 31).trans hd)
  have g1721 : 1721 ∈ P := S1 1721 (by norm_num) (by norm_num) (hL _ (by simp)) 6883 g6883 (by norm_num)
  have g41 : 41 ∈ P := S1 41 (by norm_num) (by norm_num) (hL _ (by simp)) 1721 g1721 (by norm_num)
  have := S3 7 (by norm_num) (by norm_num) (hL _ (by simp)) 1721 g1721 41 g41 (by norm_num) (by norm_num)
  omega

theorem mkill3_e33 {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 33 ∣ K') (hL : ∀ c ∈ ([661, 331, 83, 7] : List ℕ), c ∉ N) : False := by
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g661 : 661 ∈ P := S7 661 (by norm_num) (by norm_num) (hL _ (by simp))
    ((by norm_num : 661 ∣ 1 + 3 ^ 33).trans hd)
  have g331 : 331 ∈ P := S1 331 (by norm_num) (by norm_num) (hL _ (by simp)) 661 g661 (by norm_num)
  have g83 : 83 ∈ P := S1 83 (by norm_num) (by norm_num) (hL _ (by simp)) 331 g331 (by norm_num)
  exact S8 7 (by norm_num) (by norm_num) (hL _ (by simp)) ((by norm_num : 7 ∣ 1 + 3 ^ 33).trans hd) 83 g83 (by norm_num)

theorem mkill3_e34 {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 34 ∣ K') (hL : ∀ c ∈ ([956353, 68311, 8539, 5] : List ℕ), c ∉ N) : False := by
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g956353 : 956353 ∈ P := S7 956353 (by norm_num) (by norm_num) (hL _ (by simp))
    ((by norm_num : 956353 ∣ 1 + 3 ^ 34).trans hd)
  have g68311 : 68311 ∈ P := S1 68311 (by norm_num) (by norm_num) (hL _ (by simp)) 956353 g956353 (by norm_num)
  have g8539 : 8539 ∈ P := S1 8539 (by norm_num) (by norm_num) (hL _ (by simp)) 68311 g68311 (by norm_num)
  exact S8 5 (by norm_num) (by norm_num) (hL _ (by simp)) ((by norm_num : 5 ∣ 1 + 3 ^ 34).trans hd) 8539 g8539 (by norm_num)

theorem mkill3_e37 {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 37 ∣ K') (hL : ∀ c ∈ ([18427, 271, 17] : List ℕ), c ∉ N) : False := by
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g18427 : 18427 ∈ P := S7 18427 (by norm_num) (by norm_num) (hL _ (by simp))
    ((by norm_num : 18427 ∣ 1 + 3 ^ 37).trans hd)
  have g271 : 271 ∈ P := S1 271 (by norm_num) (by norm_num) (hL _ (by simp)) 18427 g18427 (by norm_num)
  have := S3 17 (by norm_num) (by norm_num) (hL _ (by simp)) 18427 g18427 271 g271 (by norm_num) (by norm_num)
  omega

theorem mkill3_e38 {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 38 ∣ K') (hL : ∀ c ∈ ([5301533, 126227, 157, 79, 5] : List ℕ), c ∉ N) : False := by
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g5301533 : 5301533 ∈ P := S7 5301533 (by norm_num) (by norm_num) (hL _ (by simp))
    ((by norm_num : 5301533 ∣ 1 + 3 ^ 38).trans hd)
  have g126227 : 126227 ∈ P := S1 126227 (by norm_num) (by norm_num) (hL _ (by simp)) 5301533 g5301533 (by norm_num)
  have g157 : 157 ∈ P := S1 157 (by norm_num) (by norm_num) (hL _ (by simp)) 126227 g126227 (by norm_num)
  have g79 : 79 ∈ P := S1 79 (by norm_num) (by norm_num) (hL _ (by simp)) 157 g157 (by norm_num)
  exact S8 5 (by norm_num) (by norm_num) (hL _ (by simp)) ((by norm_num : 5 ∣ 1 + 3 ^ 38).trans hd) 79 g79 (by norm_num)

theorem mkill3_e39 {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 39 ∣ K') (hL : ∀ c ∈ ([157, 79] : List ℕ), c ∉ N) : False := by
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g157 : 157 ∈ P := S7 157 (by norm_num) (by norm_num) (hL _ (by simp))
    ((by norm_num : 157 ∣ 1 + 3 ^ 39).trans hd)
  exact S8 79 (by norm_num) (by norm_num) (hL _ (by simp)) ((by norm_num : 79 ∣ 1 + 3 ^ 39).trans hd) 157 g157 (by norm_num)

theorem mkill3_e23 {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 23 ∣ K') (hL : ∀ c ∈ ([23535794707, 79, 74480363, 98519, 5] : List ℕ), c ∉ N) : False := by
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g23535794707 : 23535794707 ∈ P := S7 23535794707 prime_23535794707 (by norm_num) (hL _ (by simp))
    ((by norm_num : 23535794707 ∣ 1 + 3 ^ 23).trans hd)
  have g79 : 79 ∈ P := S1 79 (by norm_num) (by norm_num) (hL _ (by simp)) 23535794707 g23535794707 (by norm_num)
  have g74480363 : 74480363 ∈ P := S1 74480363 prime_74480363 (by norm_num) (hL _ (by simp)) 23535794707 g23535794707 (by norm_num)
  have g98519 : 98519 ∈ P := S1 98519 (by norm_num) (by norm_num) (hL _ (by simp)) 74480363 g74480363 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hL _ (by simp)) 79 g79 98519 g98519 (by norm_num) (by norm_num)
  omega

theorem mkill3_e26 {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 26 ∣ K') (hL : ∀ c ∈ ([4795973261, 266442959, 5] : List ℕ), c ∉ N) : False := by
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g4795973261 : 4795973261 ∈ P := S7 4795973261 prime_4795973261 (by norm_num) (hL _ (by simp))
    ((by norm_num : 4795973261 ∣ 1 + 3 ^ 26).trans hd)
  have g266442959 : 266442959 ∈ P := S1 266442959 prime_266442959 (by norm_num) (hL _ (by simp)) 4795973261 g4795973261 (by norm_num)
  exact S8 5 (by norm_num) (by norm_num) (hL _ (by simp)) ((by norm_num : 5 ∣ 1 + 3 ^ 26).trans hd) 266442959 g266442959 (by norm_num)

theorem mkill3_e32 {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 32 ∣ K') (hL : ∀ c ∈ ([926510094425921, 6883, 1721, 41, 7] : List ℕ), c ∉ N) : False := by
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g926510094425921 : 926510094425921 ∈ P := S7 926510094425921 prime_926510094425921 (by norm_num) (hL _ (by simp))
    ((by norm_num : 926510094425921 ∣ 1 + 3 ^ 32).trans hd)
  have g6883 : 6883 ∈ P := S1 6883 (by norm_num) (by norm_num) (hL _ (by simp)) 926510094425921 g926510094425921 (by norm_num)
  have g1721 : 1721 ∈ P := S1 1721 (by norm_num) (by norm_num) (hL _ (by simp)) 6883 g6883 (by norm_num)
  have g41 : 41 ∈ P := S1 41 (by norm_num) (by norm_num) (hL _ (by simp)) 1721 g1721 (by norm_num)
  have := S3 7 (by norm_num) (by norm_num) (hL _ (by simp)) 1721 g1721 41 g41 (by norm_num) (by norm_num)
  omega

theorem mkill3_e35 {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 35 ∣ K') (hL : ∀ c ∈ ([547, 137, 374857981681, 2851, 23] : List ℕ), c ∉ N) : False := by
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g547 : 547 ∈ P := S7 547 (by norm_num) (by norm_num) (hL _ (by simp))
    ((by norm_num : 547 ∣ 1 + 3 ^ 35).trans hd)
  have g137 : 137 ∈ P := S1 137 (by norm_num) (by norm_num) (hL _ (by simp)) 547 g547 (by norm_num)
  have g374857981681 : 374857981681 ∈ P := S7 374857981681 prime_374857981681 (by norm_num) (hL _ (by simp))
    ((by norm_num : 374857981681 ∣ 1 + 3 ^ 35).trans hd)
  have g2851 : 2851 ∈ P := S1 2851 (by norm_num) (by norm_num) (hL _ (by simp)) 374857981681 g374857981681 (by norm_num)
  have := S3 23 (by norm_num) (by norm_num) (hL _ (by simp)) 137 g137 2851 g2851 (by norm_num) (by norm_num)
  omega

theorem mkill5_e6 {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    (hd : 1 + 5 ^ 6 ∣ K') (hL : ∀ c ∈ ([13, 601, 7] : List ℕ), c ∉ N) : False := by
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g13 : 13 ∈ P := S7 13 (by norm_num) (by norm_num) (hL _ (by simp))
    ((by norm_num : 13 ∣ 1 + 5 ^ 6).trans hd)
  have g601 : 601 ∈ P := S7 601 (by norm_num) (by norm_num) (hL _ (by simp))
    ((by norm_num : 601 ∣ 1 + 5 ^ 6).trans hd)
  have := S3 7 (by norm_num) (by norm_num) (hL _ (by simp)) 13 g13 601 g601 (by norm_num) (by norm_num)
  omega

theorem mkill5_e10 {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    (hd : 1 + 5 ^ 10 ∣ K') (hL : ∀ c ∈ ([13, 41, 7] : List ℕ), c ∉ N) : False := by
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g13 : 13 ∈ P := S7 13 (by norm_num) (by norm_num) (hL _ (by simp))
    ((by norm_num : 13 ∣ 1 + 5 ^ 10).trans hd)
  have g41 : 41 ∈ P := S7 41 (by norm_num) (by norm_num) (hL _ (by simp))
    ((by norm_num : 41 ∣ 1 + 5 ^ 10).trans hd)
  have := S3 7 (by norm_num) (by norm_num) (hL _ (by simp)) 13 g13 41 g41 (by norm_num) (by norm_num)
  omega

theorem mkill5_e14 {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    (hd : 1 + 5 ^ 14 ∣ K') (hL : ∀ c ∈ ([234750601, 5953, 13] : List ℕ), c ∉ N) : False := by
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g234750601 : 234750601 ∈ P := S7 234750601 prime_234750601 (by norm_num) (hL _ (by simp))
    ((by norm_num : 234750601 ∣ 1 + 5 ^ 14).trans hd)
  have g5953 : 5953 ∈ P := S1 5953 (by norm_num) (by norm_num) (hL _ (by simp)) 234750601 g234750601 (by norm_num)
  exact S8 13 (by norm_num) (by norm_num) (hL _ (by simp)) ((by norm_num : 13 ∣ 1 + 5 ^ 14).trans hd) 5953 g5953 (by norm_num)

theorem mkill5_e20 {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    (hd : 1 + 5 ^ 20 ∣ K') (hL : ∀ c ∈ ([241, 11] : List ℕ), c ∉ N) : False := by
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g241 : 241 ∈ P := S7 241 (by norm_num) (by norm_num) (hL _ (by simp))
    ((by norm_num : 241 ∣ 1 + 5 ^ 20).trans hd)
  exact S6 11 (by norm_num) (by norm_num) (hL _ (by simp)) 241 g241 (by norm_num)

theorem mkill5_e26 {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    (hd : 1 + 5 ^ 26 ∣ K') (hL : ∀ c ∈ ([13] : List ℕ), c ∉ N) : False := by
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  exact S_sq hP hK E (c := 13) (by norm_num) (by norm_num) (hL _ (by simp))
    ((((by norm_num : 13 * 13 ∣ 1 + 5 ^ 26).trans hd).mul_left _).mul_right _)

theorem mkill5_e34 {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    (hd : 1 + 5 ^ 34 ∣ K') (hL : ∀ c ∈ ([13, 1973, 7] : List ℕ), c ∉ N) : False := by
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g13 : 13 ∈ P := S7 13 (by norm_num) (by norm_num) (hL _ (by simp))
    ((by norm_num : 13 ∣ 1 + 5 ^ 34).trans hd)
  have g1973 : 1973 ∈ P := S7 1973 (by norm_num) (by norm_num) (hL _ (by simp))
    ((by norm_num : 1973 ∣ 1 + 5 ^ 34).trans hd)
  have := S3 7 (by norm_num) (by norm_num) (hL _ (by simp)) 13 g13 1973 g1973 (by norm_num) (by norm_num)
  omega

theorem mkill5_e28 {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    (hd : 1 + 5 ^ 28 ∣ K') (hL : ∀ c ∈ ([59509429687890001, 29754714843945001, 83, 7679233, 769, 7] : List ℕ), c ∉ N) : False := by
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g59509429687890001 : 59509429687890001 ∈ P := S7 59509429687890001 prime_59509429687890001 (by norm_num) (hL _ (by simp))
    ((by norm_num : 59509429687890001 ∣ 1 + 5 ^ 28).trans hd)
  have g29754714843945001 : 29754714843945001 ∈ P := S1 29754714843945001 prime_29754714843945001 (by norm_num) (hL _ (by simp)) 59509429687890001 g59509429687890001 (by norm_num)
  have g83 : 83 ∈ P := S1 83 (by norm_num) (by norm_num) (hL _ (by simp)) 29754714843945001 g29754714843945001 (by norm_num)
  have g7679233 : 7679233 ∈ P := S1 7679233 (by norm_num) (by norm_num) (hL _ (by simp)) 29754714843945001 g29754714843945001 (by norm_num)
  have g769 : 769 ∈ P := S1 769 (by norm_num) (by norm_num) (hL _ (by simp)) 7679233 g7679233 (by norm_num)
  have := S3 7 (by norm_num) (by norm_num) (hL _ (by simp)) 83 g83 769 g769 (by norm_num) (by norm_num)
  omega

theorem mkill7_e2 {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    (hd : 1 + 7 ^ 2 ∣ K') (hL : ∀ c ∈ ([5] : List ℕ), c ∉ N) : False := by
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  exact S_sq hP hK E (c := 5) (by norm_num) (by norm_num) (hL _ (by simp))
    ((((by norm_num : 5 * 5 ∣ 1 + 7 ^ 2).trans hd).mul_left _).mul_right _)

theorem mkill7_e19 {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    (hd : 1 + 7 ^ 19 ∣ K') (hL : ∀ c ∈ ([351121, 419] : List ℕ), c ∉ N) : False := by
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g351121 : 351121 ∈ P := S7 351121 (by norm_num) (by norm_num) (hL _ (by simp))
    ((by norm_num : 351121 ∣ 1 + 7 ^ 19).trans hd)
  exact S6 419 (by norm_num) (by norm_num) (hL _ (by simp)) 351121 g351121 (by norm_num)

theorem mkill7_e32 {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    (hd : 1 + 7 ^ 32 ∣ K') (hL : ∀ c ∈ ([7699649, 5] : List ℕ), c ∉ N) : False := by
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g7699649 : 7699649 ∈ P := S7 7699649 (by norm_num) (by norm_num) (hL _ (by simp))
    ((by norm_num : 7699649 ∣ 1 + 7 ^ 32).trans hd)
  exact S6 5 (by norm_num) (by norm_num) (hL _ (by simp)) 7699649 g7699649 (by norm_num)

theorem mkill7_e37 {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    (hd : 1 + 7 ^ 37 ∣ K') (hL : ∀ c ∈ ([149, 5] : List ℕ), c ∉ N) : False := by
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g149 : 149 ∈ P := S7 149 (by norm_num) (by norm_num) (hL _ (by simp))
    ((by norm_num : 149 ∣ 1 + 7 ^ 37).trans hd)
  exact S6 5 (by norm_num) (by norm_num) (hL _ (by simp)) 149 g149 (by norm_num)

-- Section 2. The balance equation with kernel S.

theorem setup {n : ℕ} {S : Finset ℕ} (h : Erdos1052.IsUnitaryPerfect n)
    (hS : ∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n) {z : ℕ} (hzS : z ∈ S) :
    ∃ (m K K' : ℕ) (P : Finset ℕ), (∀ p ∈ P, p.Prime ∧ p ≠ 2) ∧
      (∀ c : ℕ, c.Prime → c ∣ K → c ∈ S) ∧
      (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p ∧
      1 + z ^ n.factorization z ∣ K' := by
  have hn : n ≠ 0 := h.2.ne'
  have h2 := two_dvd_of_isUnitaryPerfect h
  have hs : ∀ r ∈ n.primeFactors, r ≠ 2 → r ∉ S → n.factorization r = 1 := by
    intro r hr hr2 hrS
    have hrp := Nat.prime_of_mem_primeFactors hr
    have h1 := fact_pos hr
    by_contra hne
    exact hrS ((hS r).mpr ⟨hrp, hr2, (hrp.pow_dvd_iff_le_factorization hn).mpr (by omega)⟩)
  have E := kernel_balance (N := S) h h2 hs
  refine ⟨n.factorization 2,
    ∏ z ∈ (n.primeFactors.erase 2).filter (fun r => r ∈ S), z ^ n.factorization z,
    ∏ z ∈ (n.primeFactors.erase 2).filter (fun r => r ∈ S), (1 + z ^ n.factorization z),
    (n.primeFactors.erase 2).filter (fun r => ¬ r ∈ S), ?_, ?_, E, ?_⟩
  · intro p hp
    obtain ⟨hp1, _⟩ := Finset.mem_filter.mp hp
    exact ⟨Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hp1), Finset.ne_of_mem_erase hp1⟩
  · intro c hc hcd
    obtain ⟨y, hy, hcy⟩ := (Prime.dvd_finsetProd_iff hc.prime _).mp hcd
    obtain ⟨hy1, hyS⟩ := Finset.mem_filter.mp hy
    have hyp := Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hy1)
    rw [(Nat.prime_dvd_prime_iff_eq hc hyp).mp (hc.dvd_of_dvd_pow hcy)]
    exact hyS
  · have hz := (hS z).mp hzS
    have hzpf : z ∈ n.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hz.1, (dvd_pow_self z (by norm_num)).trans hz.2.2, hn⟩
    exact Finset.dvd_prod_of_mem (fun y => 1 + y ^ n.factorization y)
      (Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hz.2.1, hzpf⟩, hzS⟩)

-- Section 3. The tables.

theorem table3 {n : ℕ} {S : Finset ℕ} (h : Erdos1052.IsUnitaryPerfect n)
    (hS : ∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n) (hzS : 3 ∈ S) :
    ∀ dL ∈ ([(6, [73, 37, 19, 5]), (8, [193, 97, 7]), (9, [37, 19]), (10, [5]),
      (12, [41, 6481, 7]), (14, [29, 5]), (15, [61, 31]), (16, [21523361, 61, 31]),
      (17, [103, 13, 307, 7]), (20, [41, 42521761, 21260881, 10630441, 139, 7]),
      (21, [7]), (22, [5501, 570461, 3067, 13, 7]),
      (23, [23535794707, 79, 74480363, 98519, 5]), (25, [151, 19, 22996651, 29, 5]),
      (26, [4795973261, 266442959, 5]), (28, [41, 430697, 3121, 7]),
      (29, [5385997, 2692999, 5]), (31, [6883, 1721, 41, 7]),
      (32, [926510094425921, 6883, 1721, 41, 7]), (33, [661, 331, 83, 7]),
      (34, [956353, 68311, 8539, 5]), (35, [547, 137, 374857981681, 2851, 23]),
      (37, [18427, 271, 17]), (38, [5301533, 126227, 157, 79, 5]), (39, [157, 79])] : List (ℕ × List ℕ)),
      n.factorization 3 % (2 * dL.1) = dL.1 → ∃ c ∈ dL.2, c ∈ S := by
  obtain ⟨m, K, K', P, hP, hK, E, hKz⟩ := setup h hS hzS
  intro dL hdL hmod
  by_contra hne
  have hne' : ∀ c ∈ dL.2, c ∉ S := fun c hc hcS => hne ⟨c, hc, hcS⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hdL
  rcases hdL with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact mkill3_e6 hP hK E ((one_add_pow_dvd_of_odd_mul hmod).trans hKz) hne'
  · exact mkill3_e8 hP hK E ((one_add_pow_dvd_of_odd_mul hmod).trans hKz) hne'
  · exact mkill3_e9 hP hK E ((one_add_pow_dvd_of_odd_mul hmod).trans hKz) hne'
  · exact mkill3_e10 hP hK E ((one_add_pow_dvd_of_odd_mul hmod).trans hKz) hne'
  · exact mkill3_e12 hP hK E ((one_add_pow_dvd_of_odd_mul hmod).trans hKz) hne'
  · exact mkill3_e14 hP hK E ((one_add_pow_dvd_of_odd_mul hmod).trans hKz) hne'
  · exact mkill3_e15 hP hK E ((one_add_pow_dvd_of_odd_mul hmod).trans hKz) hne'
  · exact mkill3_e16 hP hK E ((one_add_pow_dvd_of_odd_mul hmod).trans hKz) hne'
  · exact mkill3_e17 hP hK E ((one_add_pow_dvd_of_odd_mul hmod).trans hKz) hne'
  · exact mkill3_e20 hP hK E ((one_add_pow_dvd_of_odd_mul hmod).trans hKz) hne'
  · exact mkill3_e21 hP hK E ((one_add_pow_dvd_of_odd_mul hmod).trans hKz) hne'
  · exact mkill3_e22 hP hK E ((one_add_pow_dvd_of_odd_mul hmod).trans hKz) hne'
  · exact mkill3_e23 hP hK E ((one_add_pow_dvd_of_odd_mul hmod).trans hKz) hne'
  · exact mkill3_e25 hP hK E ((one_add_pow_dvd_of_odd_mul hmod).trans hKz) hne'
  · exact mkill3_e26 hP hK E ((one_add_pow_dvd_of_odd_mul hmod).trans hKz) hne'
  · exact mkill3_e28 hP hK E ((one_add_pow_dvd_of_odd_mul hmod).trans hKz) hne'
  · exact mkill3_e29 hP hK E ((one_add_pow_dvd_of_odd_mul hmod).trans hKz) hne'
  · exact mkill3_e31 hP hK E ((one_add_pow_dvd_of_odd_mul hmod).trans hKz) hne'
  · exact mkill3_e32 hP hK E ((one_add_pow_dvd_of_odd_mul hmod).trans hKz) hne'
  · exact mkill3_e33 hP hK E ((one_add_pow_dvd_of_odd_mul hmod).trans hKz) hne'
  · exact mkill3_e34 hP hK E ((one_add_pow_dvd_of_odd_mul hmod).trans hKz) hne'
  · exact mkill3_e35 hP hK E ((one_add_pow_dvd_of_odd_mul hmod).trans hKz) hne'
  · exact mkill3_e37 hP hK E ((one_add_pow_dvd_of_odd_mul hmod).trans hKz) hne'
  · exact mkill3_e38 hP hK E ((one_add_pow_dvd_of_odd_mul hmod).trans hKz) hne'
  · exact mkill3_e39 hP hK E ((one_add_pow_dvd_of_odd_mul hmod).trans hKz) hne'

theorem table5 {n : ℕ} {S : Finset ℕ} (h : Erdos1052.IsUnitaryPerfect n)
    (hS : ∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n) (hzS : 5 ∈ S) :
    ∀ dL ∈ ([(6, [13, 601, 7]), (10, [13, 41, 7]), (14, [234750601, 5953, 13]),
      (20, [241, 11]), (26, [13]),
      (28, [59509429687890001, 29754714843945001, 83, 7679233, 769, 7]),
      (34, [13, 1973, 7])] : List (ℕ × List ℕ)),
      n.factorization 5 % (2 * dL.1) = dL.1 → ∃ c ∈ dL.2, c ∈ S := by
  obtain ⟨m, K, K', P, hP, hK, E, hKz⟩ := setup h hS hzS
  intro dL hdL hmod
  by_contra hne
  have hne' : ∀ c ∈ dL.2, c ∉ S := fun c hc hcS => hne ⟨c, hc, hcS⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hdL
  rcases hdL with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact mkill5_e6 hP hK E ((one_add_pow_dvd_of_odd_mul hmod).trans hKz) hne'
  · exact mkill5_e10 hP hK E ((one_add_pow_dvd_of_odd_mul hmod).trans hKz) hne'
  · exact mkill5_e14 hP hK E ((one_add_pow_dvd_of_odd_mul hmod).trans hKz) hne'
  · exact mkill5_e20 hP hK E ((one_add_pow_dvd_of_odd_mul hmod).trans hKz) hne'
  · exact mkill5_e26 hP hK E ((one_add_pow_dvd_of_odd_mul hmod).trans hKz) hne'
  · exact mkill5_e28 hP hK E ((one_add_pow_dvd_of_odd_mul hmod).trans hKz) hne'
  · exact mkill5_e34 hP hK E ((one_add_pow_dvd_of_odd_mul hmod).trans hKz) hne'

theorem table7 {n : ℕ} {S : Finset ℕ} (h : Erdos1052.IsUnitaryPerfect n)
    (hS : ∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n) (hzS : 7 ∈ S) :
    ∀ dL ∈ ([(2, [5]), (19, [351121, 419]), (32, [7699649, 5]), (37, [149, 5])] : List (ℕ × List ℕ)),
      n.factorization 7 % (2 * dL.1) = dL.1 → ∃ c ∈ dL.2, c ∈ S := by
  obtain ⟨m, K, K', P, hP, hK, E, hKz⟩ := setup h hS hzS
  intro dL hdL hmod
  by_contra hne
  have hne' : ∀ c ∈ dL.2, c ∉ S := fun c hc hcS => hne ⟨c, hc, hcS⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hdL
  rcases hdL with rfl | rfl | rfl | rfl
  · exact mkill7_e2 hP hK E ((one_add_pow_dvd_of_odd_mul hmod).trans hKz) hne'
  · exact mkill7_e19 hP hK E ((one_add_pow_dvd_of_odd_mul hmod).trans hKz) hne'
  · exact mkill7_e32 hP hK E ((one_add_pow_dvd_of_odd_mul hmod).trans hKz) hne'
  · exact mkill7_e37 hP hK E ((one_add_pow_dvd_of_odd_mul hmod).trans hKz) hne'

-- Section 4. The step.

theorem main : H1 → H2 → OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H3_R1.H1 := by
  rintro ⟨A1, h1⟩ ⟨A2, h2⟩
  refine ⟨A1 + A2, fun n h S hS hc hna h3S => ?_⟩
  have c5 := fun h5 => table5 h hS h5
  have c7 := fun h7 => table7 h hS h7
  by_cases hcl : ∀ d ∈ ({6, 8, 9, 10, 12, 14, 15, 16, 17, 20, 21, 22, 23, 25, 26, 28, 29, 31, 32, 33, 34, 35, 37, 38, 39} : Finset ℕ), n.factorization 3 % (2 * d) ≠ d
  · have := h2 n h S hS hc hna h3S hcl c5 c7
    omega
  · have := h1 n h S hS hc hna h3S hcl (table3 h hS h3S) c5 c7
    omega

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H3_R1_H1_R1
