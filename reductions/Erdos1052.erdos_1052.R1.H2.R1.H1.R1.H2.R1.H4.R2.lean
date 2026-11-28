import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1

-- Reduction Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H2.R1.H4.R2
-- Upstream path: reductions/Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H2.R1.H4.R2.lean
-- Credit: @adammcarter (agent: Claude Code, model claude-fable-5-2)
--
-- A second reduction of step H4 of Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H2.R1: n unitary perfect, z the
-- only odd prime with z^2 | n, 7 <= z < 2100 (314 primes), a = padicValNat 2 n to be bounded.
-- Here the bound a <= 9 is PROVED for 265 of the 314 primes, for every exponent of z and every a
-- allowed by the step.  Proving H1, H2 and H3 proves the step.
--
-- Method.  The parent Erdos1052.erdos_1052.R1.H2.R1 proves a <= 9 (Graham's weights with a kernel,
-- two_adic_le_nine_of_sparse_nonsimple) when (z + 1) / (z - 3) <= 2101/2097, that is z >= 2100.
-- Its proof uses the size of z in one place only: the product of (q + 1) / (q - 1) over the z-leaves
-- (simple primes q with q + 1 = 2^k z^j) is bounded by z / (z - 3), as if every such number were a
-- prime of n.  Section 1 repeats that proof with this bound as a hypothesis on the actual leaves
-- (master_leaf, bigL).  Section 4 proves the hypothesis for 266 primes 128 <= z < 2100 from the
-- list of the primes 2^k z - 1 below 10^4 (below 10^5, 10^6 or 10^7 for 19 of them; the tables of
-- 181 and 691, and of 13 in Section 5, also list the primes 2^k z^2 - 1); composite candidates
-- are checked by norm_num, the listed leaves need no primality proof.
--
-- PROVED BELOW (no hypothesis needed):
--   le_nine_of_leaf: z >= 128 prime with leaf mass within 2101/2097  =>  a <= 9, unless
--     4 | a, z = 2 mod 3, z | 2^a + 1 and the exponent of z is even.
--   126 primes z = 1 mod 3: closed.
--   126 primes z = 2 mod 3 with 16^o = 1 mod z for an odd o (theorems nf_<z>): z never divides
--     2^a + 1 with 4 | a.  Closed.
--   13 primes z = 2 mod 3 (353, 401, 449, 641, 929, 977, 1217, 1361, 1409, 1601, 1697, 1889, 2081):
--     z | 2^a + 1 forces the power of 2 in a to be 4, 8, 16 or 32 exactly (theorems rs_<z>), which
--     the step excludes.  Closed.
--   z = 257: closed unless a = 8 mod 16 and the exponent of 257 is even (H1).
--   le_nine_three_top (rounds 3 and 10 of this work, budget 311/300): for 43 further primes, a <= 9
--     when a is odd, and when z = 2 mod 3 and the exponent of z is odd.  This gives the two extra
--     conditions of H2.
--
-- H1 (OPEN): z = 257, a = 8 mod 16, exponent of 257 even.
-- H2 (OPEN): 43 primes (13 <= z <= 127 other than 17, 19, 31; and 131, 137, 139, 157, 173, 197, 199,
--   211, 227, 229, 263, 271, 307, 331, 337, 367, 379, 439, 499, 619, whose leaf 2z - 1 or 4z - 1 is
--   too heavy for the budget), a even, exponent of z even when z = 2 mod 3.
-- H3 (OPEN): z = 7, 11, 17, 19 or 31 with the conditions of the step unchanged.
-- No known unitary perfect number satisfies the hypotheses of the step (the five known ones have
-- z = 3 or z = 5 or no repeated odd prime).

namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R2

open OMA.R_Erdos1052_erdos_1052_R1_H2_R1 hiding H1 H2 main
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1 (zleaf_bound zleaf_form filter_mem_singleton B_nonneg master_gen
  three_dvd_two_pow_add_one)

-- H1: a = v2(n) is bounded over the unitary perfect numbers whose only repeated odd prime is 257,
-- with a = 8 mod 16 (then 257 divides 2^a + 1) and the exponent of 257 even.
def H1 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 257) →
    padicValNat 2 n % 16 = 8 → Even (n.factorization 257) →
    padicValNat 2 n ≤ A

-- H2: a is bounded when the only repeated odd prime z is one of 43 primes: the primes from 13 to
-- 127 other than 17, 19, 31, and the 20 primes from 131 to 619 with a heavy leaf (2z - 1 or
-- 4z - 1 prime).  Proved here for them: a is even, and the exponent of z is even when z = 2 mod 3.
-- The other conditions are those of the step that survive for even a.
def H2 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n → ∀ z ∈ ({13, 23, 29, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 157, 173, 197, 199, 211, 227, 229, 263, 271, 307, 331, 337, 367, 379, 439, 499, 619} : Finset ℕ),
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = z) →
    padicValNat 2 n % 2 = 0 → (z % 3 = 2 → Even (n.factorization z)) →
    padicValNat 2 n % 20 ≠ 10 → (z ≠ 29 → padicValNat 2 n % 28 ≠ 14) →
    padicValNat 2 n % 8 ≠ 4 → (z ≠ 43 → padicValNat 2 n % 16 ≠ 8) → padicValNat 2 n % 4096 ≠ 2048 →
    (∀ r ∈ ({4, 5, 6, 7, 8, 9, 10, 12, 13, 14, 15, 16, 17, 18, 19, 21, 22, 23, 25, 26, 27, 28, 29, 30, 31, 32} : Finset ℕ),
      padicValNat 2 n % 2 ^ (r + 1) ≠ 2 ^ r) →
    padicValNat 2 n ≤ A

-- H3: a is bounded when the only repeated odd prime z is 7, 11, 17, 19 or 31, under the
-- conditions of the step (unchanged).
def H3 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n → ∀ z ∈ ({7, 11, 17, 19, 31} : Finset ℕ),
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = z) →
    (z % 3 = 2 → Odd (n.factorization z) → n.factorization z % 6 = 1) →
    (z = 7 → 41 ≤ n.factorization 7 ∧
      ∀ d ∈ ({2, 3, 4, 5, 7, 8, 11, 13, 16, 17, 19, 23, 29, 31, 32, 37} : Finset ℕ),
        n.factorization 7 % (2 * d) ≠ d) →
    padicValNat 2 n % 6 ≠ 3 → (z ≠ 11 → padicValNat 2 n % 10 ≠ 5) →
    (z ≠ 11 → z ≠ 43 → padicValNat 2 n % 14 ≠ 7) → (z % 3 = 1 → padicValNat 2 n % 6 ≠ 5) →
    padicValNat 2 n % 20 ≠ 10 → (z ≠ 29 → padicValNat 2 n % 28 ≠ 14) →
    (z ≠ 17 → padicValNat 2 n % 8 ≠ 4) → (z ≠ 11 → z ≠ 43 → z ≠ 257 → padicValNat 2 n % 16 ≠ 8) →
    (z ≠ 743 → padicValNat 2 n % 4096 ≠ 2048) →
    (∀ r ∈ ({4, 5, 6, 7, 8, 9, 10, 12, 13, 14, 15, 16, 17, 18, 19, 21, 22, 23, 25, 26, 27, 28, 29, 30, 31, 32} : Finset ℕ),
      padicValNat 2 n % 2 ^ (r + 1) ≠ 2 ^ r) →
    padicValNat 2 n ≤ A

-- Section 1.  The weight theorem of the parent Erdos1052.erdos_1052.R1.H2.R1 (master, its six
-- cases, big) with the uniform bound on the z-leaves replaced by a hypothesis on the actual
-- leaves.  Same text as there with that one hypothesis changed.

theorem master_leaf {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hN : ∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (hKK : K ≤ K' ∧ ∀ L : Finset ℕ, L ⊆ P →
      (∀ q ∈ L, (∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q + 1 → c ∈ N) ∧ ¬ ∃ k, q + 1 = 2 ^ k) →
      (K' : ℚ) / K * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p) (hm : 10 ≤ m)
    (β : ℕ → ℚ)
    (hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1))
    (h4 : ∀ p ∈ P, ∀ c ∈ P, c ∣ p + 1 →
        (∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ N → c' ∣ p + 1 → c ≤ c') →
        β c ≠ ((c : ℚ) + 1) / ((c : ℚ) - 1) → (1 + 1 / (c : ℚ)) * β p ≤ β c)
    (h1 : 1 ≤ β 3 ∧ 1 ≤ β 7 ∧ 1 ≤ β 31 ∧ 1 ≤ β 127)
    (hfin : 1025 / 1024 * (β 3 * β 7 * β 31 * β 127) * (2048 / 2047) * (2101 / 2097) < 2) :
    False := by
  obtain ⟨S1, -, S2, -, -, -, -, -⟩ := facts hP hK E
  obtain ⟨g, hg⟩ := exists_child N
  have hK0 : 0 < K := K_pos hN hK
  have hpos : ∀ p ∈ P, 0 < p := fun p hp => (hP p hp).1.pos
  have hβpos : ∀ p ∈ P, 0 < β p := fun p hp => by
    have h0 : (0 : ℚ) ≤ 1 / (p : ℚ) := by positivity
    linarith [(hB p hp).1]
  have hg1 : ∀ p ∈ P, g p ∈ P → g p ≠ 1 := fun p _ h h1 => by
    have := (hP _ h).1
    rw [h1] at this
    exact Nat.not_prime_one this
  have hgP : ∀ p ∈ P, g p ≠ 1 → g p ∈ P := fun p hp h =>
    S1 _ ((hg p).2.2.1 h).1 ((hg p).2.2.1 h).2.1 ((hg p).2.2.1 h).2.2 p hp (hg p).1
  have hpath := path_bound g β P.card P rfl hpos
    (fun p hp h => by
      have hc := (hg p).2.2.1 (hg1 p hp h)
      have := two_mul_le hc.1 hc.2.1 (hP p hp).1 (hP p hp).2 (hg p).1
      have := hc.1.two_le
      omega)
    (fun p hp p' hp' h he => by
      have hc := (hg p).2.2.1 (hg1 p hp h)
      exact S2 _ hc.1 hc.2.1 hc.2.2 p hp p' hp' (hg p).1 (he ▸ (hg p').1))
    (fun p hp => (hB p hp).1)
    (fun p hp h => by
      have hc := (hg p).2.2.1 (hg1 p hp h)
      by_cases hsp : β (g p) = (((g p : ℕ) : ℚ) + 1) / (((g p : ℕ) : ℚ) - 1)
      · rw [hsp]
        have h0 : (0 : ℚ) ≤ 1 + 1 / ((g p : ℕ) : ℚ) := by positivity
        exact (mul_le_mul_of_nonneg_left (hB p hp).2 h0).trans
          (B_step hc.1.two_le (two_mul_le hc.1 hc.2.1 (hP p hp).1 (hP p hp).2 (hg p).1))
      · exact h4 p hp (g p) h (hg p).1 (hg p).2.2.2 hsp)
  -- a path starts at a prime q such that every odd prime factor of q + 1 lies in N
  have hleaf : ∀ q ∈ P.filter (fun q => g q ∉ P),
      ∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q + 1 → c ∈ N := fun q hq => by
    obtain ⟨hqP, hgq⟩ := Finset.mem_filter.mp hq
    by_cases h : g q = 1
    · exact (hg q).2.1 h
    · exact absurd (hgP q hqP h) hgq
  have hLP : ∀ q ∈ P.filter (fun q => g q ∉ P), q ∈ P := fun q hq => (Finset.mem_filter.mp hq).1
  have hsplit := Finset.prod_filter_mul_prod_filter_not (P.filter (fun q => g q ∉ P))
    (fun q => (q + 1) / 2 ^ (q + 1).factorization 2 ≠ 1) β
  obtain ⟨Λ, hΛdef⟩ : ∃ Λ : ℚ, Λ = ∏ q ∈ (P.filter (fun q => g q ∉ P)).filter
      (fun q => (q + 1) / 2 ^ (q + 1).factorization 2 ≠ 1),
      (((q : ℚ) + 1) / ((q : ℚ) - 1)) := ⟨_, rfl⟩
  have hzleaves : ∏ q ∈ (P.filter (fun q => g q ∉ P)).filter
      (fun q => (q + 1) / 2 ^ (q + 1).factorization 2 ≠ 1), β q ≤ Λ := by
    rw [hΛdef]
    exact Finset.prod_le_prod
      (fun q hq => (hβpos q (hLP q (Finset.mem_filter.mp hq).1)).le)
      (fun q hq => (hB q (hLP q (Finset.mem_filter.mp hq).1)).2)
  have hΛ0 : (0 : ℚ) ≤ Λ := by
    rw [hΛdef]
    exact Finset.prod_nonneg fun q hq =>
      (hβpos q (hLP q (Finset.mem_filter.mp hq).1)).le.trans
        (hB q (hLP q (Finset.mem_filter.mp hq).1)).2
  have hΛK : (K' : ℚ) / K * Λ ≤ 2101 / 2097 := by
    rw [hΛdef]
    refine hKK.2 _ (fun q hq => hLP q (Finset.mem_filter.mp hq).1) (fun q hq => ?_)
    obtain ⟨hqL, hne⟩ := Finset.mem_filter.mp hq
    refine ⟨hleaf q hqL, ?_⟩
    rintro ⟨k, hk⟩
    apply hne
    have h2 : (2 ^ k).factorization 2 = k := by
      rw [Nat.Prime.factorization_pow Nat.prime_two]
      simp
    rw [hk, h2, Nat.div_self (Nat.two_pow_pos k)]
  have hmleaves : ∏ q ∈ (P.filter (fun q => g q ∉ P)).filter
        (fun q => ¬ (q + 1) / 2 ^ (q + 1).factorization 2 ≠ 1), β q ≤
      (β 3 * β 7 * β 31 * β 127) * (2048 / 2047) := by
    refine mersenne_bound β _ (fun q hq => (hP q (hLP q (Finset.mem_filter.mp hq).1)).1)
      (fun q hq => ?_)
      (fun q hq => ⟨hβpos q (hLP q (Finset.mem_filter.mp hq).1),
        (hB q (hLP q (Finset.mem_filter.mp hq).1)).2⟩) h1
    obtain ⟨hqL, hzd⟩ := Finset.mem_filter.mp hq
    have h1' : (q + 1) / 2 ^ (q + 1).factorization 2 = 1 := not_not.mp hzd
    have hmul := Nat.ordProj_mul_ordCompl_eq_self (q + 1) 2
    rw [h1', mul_one] at hmul
    exact ⟨(q + 1).factorization 2, hmul.symm⟩
  have hM0 : (0 : ℚ) ≤ (β 3 * β 7 * β 31 * β 127) * (2048 / 2047) := by
    obtain ⟨a, b, c, d⟩ := h1
    have h3 : (0 : ℚ) ≤ β 3 := by linarith
    have h7 : (0 : ℚ) ≤ β 7 := by linarith
    have h31 : (0 : ℚ) ≤ β 31 := by linarith
    have h127 : (0 : ℚ) ≤ β 127 := by linarith
    positivity
  have hprodL : ∏ q ∈ P.filter (fun q => g q ∉ P), β q ≤
      Λ *
        ((β 3 * β 7 * β 31 * β 127) * (2048 / 2047)) := by
    rw [← hsplit]
    refine mul_le_mul hzleaves hmleaves ?_ hΛ0
    exact Finset.prod_nonneg fun q hq =>
      (hβpos q (hLP q (Finset.mem_filter.mp hq).1)).le
  -- the equation over ℚ
  have hKq : (0 : ℚ) < K := by exact_mod_cast hK0
  have hEq : (1 + 1 / (2 : ℚ) ^ m) * ((K' : ℚ) / K) * ∏ p ∈ P, (1 + 1 / (p : ℚ)) = 2 := by
    have hY : (0 : ℚ) < ∏ p ∈ P, (p : ℚ) :=
      Finset.prod_pos fun p hp => by exact_mod_cast hpos p hp
    have hcast : ((2 : ℚ) ^ m + 1) * K' * ∏ p ∈ P, ((p : ℚ) + 1) =
        2 ^ (m + 1) * K * ∏ p ∈ P, (p : ℚ) := by
      have h := congrArg (Nat.cast : ℕ → ℚ) E
      push_cast at h
      exact h
    have e : ∏ p ∈ P, (1 + 1 / (p : ℚ)) = (∏ p ∈ P, ((p : ℚ) + 1)) / ∏ p ∈ P, (p : ℚ) := by
      rw [← Finset.prod_div_distrib]
      refine Finset.prod_congr rfl fun p hp => ?_
      have : (0 : ℚ) < p := by exact_mod_cast hpos p hp
      field_simp
    have h2 : (0 : ℚ) < (2 : ℚ) ^ m := by positivity
    rw [e]
    field_simp
    rw [pow_succ] at hcast
    linarith
  have hT : 1 + 1 / (2 : ℚ) ^ m ≤ 1025 / 1024 := by
    have h2 : (2 : ℚ) ^ 10 ≤ (2 : ℚ) ^ m := pow_le_pow_right₀ (by norm_num) hm
    have : 1 / (2 : ℚ) ^ m ≤ 1 / (2 : ℚ) ^ 10 := one_div_le_one_div_of_le (by positivity) h2
    norm_num at this ⊢
    linarith
  have hKr0 : (0 : ℚ) ≤ (K' : ℚ) / K := div_nonneg (Nat.cast_nonneg _) hKq.le
  have hA : (1 + 1 / (2 : ℚ) ^ m) * ((K' : ℚ) / K) ≤ 1025 / 1024 * ((K' : ℚ) / K) :=
    mul_le_mul_of_nonneg_right hT hKr0
  have hC := mul_le_mul hA (hpath.trans hprodL)
    (Finset.prod_nonneg fun p _ => by positivity) (mul_nonneg (by norm_num) hKr0)
  have hD : (K' : ℚ) / K * Λ *
      ((β 3 * β 7 * β 31 * β 127) * (2048 / 2047)) ≤
      2101 / 2097 * ((β 3 * β 7 * β 31 * β 127) * (2048 / 2047)) :=
    mul_le_mul_of_nonneg_right hΛK hM0
  have hfinal : (2 : ℚ) ≤
      1025 / 1024 * (2101 / 2097 * ((β 3 * β 7 * β 31 * β 127) * (2048 / 2047))) := by
    calc (2 : ℚ) = (1 + 1 / (2 : ℚ) ^ m) * ((K' : ℚ) / K) * ∏ p ∈ P, (1 + 1 / (p : ℚ)) := hEq.symm
      _ ≤ 1025 / 1024 * ((K' : ℚ) / K) *
          (Λ *
            ((β 3 * β 7 * β 31 * β 127) * (2048 / 2047))) := hC
      _ = 1025 / 1024 * ((K' : ℚ) / K * Λ *
          ((β 3 * β 7 * β 31 * β 127) * (2048 / 2047))) := by ring
      _ ≤ 1025 / 1024 * (2101 / 2097 * ((β 3 * β 7 * β 31 * β 127) * (2048 / 2047))) :=
          mul_le_mul_of_nonneg_left hD (by norm_num)
  linarith

theorem case_top3L {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hN : ∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (hKK : K ≤ K' ∧ ∀ L : Finset ℕ, L ⊆ P →
      (∀ q ∈ L, (∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q + 1 → c ∈ N) ∧ ¬ ∃ k, q + 1 = 2 ^ k) →
      (K' : ℚ) / K * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    (hm : 10 ≤ m) (h3 : ∀ p ∈ P, ¬ 3 ∣ p + 1) : False := by
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p = if p = 3 then 4 / 3 else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have b3 : β 3 = 4 / 3 := by rw [hβ]; norm_num
  have b7 : β 7 = 4 / 3 := by rw [hβ]; norm_num
  have b31 : β 31 = 16 / 15 := by rw [hβ]; norm_num
  have b127 : β 127 = 64 / 63 := by rw [hβ]; norm_num
  have bd : ∀ c : ℕ, c ≠ 3 → β c = ((c : ℚ) + 1) / ((c : ℚ) - 1) := fun c e3 => by
    rw [hβ, if_neg e3]
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases e3 : p = 3
    · subst e3; rw [b3]; norm_num
    rw [bd p e3]; exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  refine master_leaf hP hN hK hKK E hm β hB ?_ ?_ ?_
  · intro p hp c hc hd hmin hne
    by_cases e3 : c = 3
    · subst e3; exact absurd hd (h3 p hp)
    exact absurd (bd c e3) hne
  · rw [b3, b7, b31, b127]; norm_num
  · rw [b3, b7, b31, b127]; norm_num

theorem case_oddL {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hN : ∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (hKK : K ≤ K' ∧ ∀ L : Finset ℕ, L ⊆ P →
      (∀ q ∈ L, (∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q + 1 → c ∈ N) ∧ ¬ ∃ k, q + 1 = 2 ^ k) →
      (K' : ℚ) / K * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    (hm : 10 ≤ m) (hodd : m % 2 = 1) : False := by
  obtain ⟨S1, S5, S2, S3, S4a, S4b, S6, S7⟩ := facts hP hK E
  have h3d : 3 ∣ 2 ^ m + 1 := by
    have h := Odd.nat_add_dvd_pow_add_pow 2 1 (Nat.odd_iff.mpr hodd)
    simpa using h
  exact case_top3L hP hN hK hKK E hm (S3 3 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) h3d)

-- 4 ∣ m.  The hypothesis hres removes the one situation the method does not reach: some prime
-- of N that is 2 mod 3 divides 2 ^ m + 1, 3 is in P, and 3 does not divide K'.
theorem case_zero_mod_fourL {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hN : ∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (hKK : K ≤ K' ∧ ∀ L : Finset ℕ, L ⊆ P →
      (∀ q ∈ L, (∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q + 1 → c ∈ N) ∧ ¬ ∃ k, q + 1 = 2 ^ k) →
      (K' : ℚ) / K * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    (hm : 10 ≤ m) (h4 : m % 4 = 0)
    (hres : (∃ z ∈ N, z ∣ 2 ^ m + 1 ∧ z % 3 = 2) → 3 ∈ P → 3 ∣ K') : False := by
  obtain ⟨S1, S5, S2, S3, S4a, S4b, S6, S7⟩ := facts hP hK E
  obtain ⟨k, rfl⟩ : ∃ k, m = k * 4 := ⟨m / 4, by omega⟩
  have hmod : (2 ^ (k * 4) + 1) % 3 = 2 := by
    rw [mul_comm, pow_mul, Nat.add_mod, Nat.pow_mod]; norm_num
  obtain ⟨p0, hp0, hp0d, hp03⟩ := exists_prime_mod3 _ hmod
  by_cases hp0z : p0 ∈ N
  · by_cases h3P : 3 ∈ P
    · exact case_top3L hP hN hK hKK E hm
        (S7 3 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) (hres ⟨p0, hp0z, hp0d, hp03⟩ h3P))
    · exact case_top3L hP hN hK hKK E hm
        (fun p hp hd => h3P (S1 3 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) p hp hd))
  have hx : 2 ^ (k * 4) + 1 = (2 ^ k) ^ 4 + 1 := by rw [pow_mul]
  have hp02 : p0 ≠ 2 := by
    rintro rfl
    have h1 : 2 ∣ 1 := (Nat.dvd_add_right (dvd_pow_self 2 (by omega))).mp hp0d
    omega
  have hp0P : p0 ∈ P := S5 p0 hp0 hp02 hp0z hp0d
  have h3d : 3 ∣ p0 + 1 := by omega
  have h3P : 3 ∈ P := S1 3 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) p0 hp0P h3d
  have hp029 : 29 ≤ p0 := by
    by_contra hlt
    have hlt' : p0 < 29 := by omega
    have h2le := hp0.two_le
    rw [hx] at hp0d
    interval_cases p0 <;> first
      | omega
      | (norm_num at hp0; done)
      | exact not_dvd_fourth_5 _ hp0d
      | exact not_dvd_fourth_11 _ hp0d
      | exact not_dvd_fourth_23 _ hp0d
      | exact S4b 3 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) 17 hp0P (by norm_num)
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p = if p = 3 then 4 / 3 * (1 + 1 / (p0 : ℚ)) else
      if p = p0 then 1 + 1 / (p0 : ℚ) else ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have hp0q : (29 : ℚ) ≤ p0 := by exact_mod_cast hp029
  have hinv0 : 0 < 1 / (p0 : ℚ) := by positivity
  have hinv : 1 / (p0 : ℚ) ≤ 1 / 29 := one_div_le_one_div_of_le (by norm_num) hp0q
  have hp0ne3 : p0 ≠ 3 := by omega
  have b3 : β 3 = 4 / 3 * (1 + 1 / (p0 : ℚ)) := by rw [hβ, if_pos rfl]
  have bp0 : β p0 = 1 + 1 / (p0 : ℚ) := by rw [hβ, if_neg hp0ne3, if_pos rfl]
  have bd : ∀ c : ℕ, c ≠ 3 → c ≠ p0 → β c = ((c : ℚ) + 1) / ((c : ℚ) - 1) := fun c e3 e0 => by
    rw [hβ, if_neg e3, if_neg e0]
  have b7 : β 7 = 4 / 3 := by rw [bd 7 (by norm_num) (by omega)]; norm_num
  have b31 : β 31 = 16 / 15 := by rw [bd 31 (by norm_num) (by omega)]; norm_num
  have b127 : β 127 = 64 / 63 := by rw [bd 127 (by norm_num) (by omega)]; norm_num
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases e3 : p = 3
    · subst e3
      rw [b3]
      have e1 : (1 : ℚ) + 1 / ((3 : ℕ) : ℚ) = 4 / 3 := by norm_num
      have e2 : (((3 : ℕ) : ℚ) + 1) / (((3 : ℕ) : ℚ) - 1) = 2 := by norm_num
      rw [e1, e2]
      constructor <;> linarith
    by_cases e0 : p = p0
    · subst e0; rw [bp0]; exact ⟨le_refl _, one_add_le_B hp0.two_le⟩
    rw [bd p e3 e0]; exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  refine master_leaf hP hN hK hKK E hm β hB ?_ ?_ ?_
  · intro p hp c hc hd hmin hne
    by_cases e3 : c = 3
    · subst e3
      obtain rfl : p = p0 := S2 3 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) p hp p0 hp0P hd h3d
      rw [b3, bp0]; norm_num
    by_cases e0 : c = p0
    · subst e0; exact absurd hd (S3 c hp0 hp02 hp0z hp0d p hp)
    exact absurd (bd c e3 e0) hne
  · rw [b3, b7, b31, b127]
    refine ⟨by linarith, by norm_num, by norm_num, by norm_num⟩
  · rw [b3, b7, b31, b127]
    linarith

theorem case3_pre {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hN : ∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z) (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p) (h4 : m % 4 = 2) :
    5 ∈ P ∧ 3 ∈ P ∧ (∀ p ∈ P, 3 ∣ p + 1 → p = 5) ∧ (∀ p ∈ P, ¬ 5 ∣ p + 1) := by
  obtain ⟨S1, S5, S2, S3, S4a, S4b, S6, S7⟩ := facts hP hK E
  have h5d : 5 ∣ 2 ^ m + 1 := by
    obtain ⟨k, rfl⟩ : ∃ k, m = 4 * k + 2 := ⟨m / 4, by omega⟩
    apply Nat.dvd_of_mod_eq_zero
    rw [pow_add, pow_mul, Nat.add_mod, Nat.mul_mod, Nat.pow_mod]; norm_num
  have h5 : 5 ∈ P := S5 5 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) h5d
  have h3 : 3 ∈ P := S1 3 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) 5 h5 (by norm_num)
  exact ⟨h5, h3, fun p hp hd => S2 3 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) p hp 5 h5 hd (by norm_num),
    fun p hp => S3 5 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) h5d p hp⟩

theorem case3_iiL {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hN : ∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (hKK : K ≤ K' ∧ ∀ L : Finset ℕ, L ⊆ P →
      (∀ q ∈ L, (∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q + 1 → c ∈ N) ∧ ¬ ∃ k, q + 1 = 2 ^ k) →
      (K' : ℚ) / K * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    (hm : 10 ≤ m) (h4 : m % 4 = 2) (h13 : 13 ∉ P) : False := by
  obtain ⟨h5, h3, T3, T5⟩ := case3_pre hP hN hK E h4
  obtain ⟨S1, S5, S2, S3, S4a, S4b, S6, S7⟩ := facts hP hK E
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p = if p = 3 then 8 / 5 else if p = 5 then 6 / 5 else
      if p = 7 then 8 / 7 * (224 / 222) else if p = 127 then 128 / 127 * (32258 / 32256) else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have b3 : β 3 = 8 / 5 := by rw [hβ]; norm_num
  have b5 : β 5 = 6 / 5 := by rw [hβ]; norm_num
  have b7 : β 7 = 8 / 7 * (224 / 222) := by rw [hβ]; norm_num
  have b31 : β 31 = 16 / 15 := by rw [hβ]; norm_num
  have b127 : β 127 = 128 / 127 * (32258 / 32256) := by rw [hβ]; norm_num
  have bd : ∀ c : ℕ, c ≠ 3 → c ≠ 5 → c ≠ 7 → c ≠ 127 → β c = ((c : ℚ) + 1) / ((c : ℚ) - 1) :=
    fun c e3 e5 e7 e127 => by rw [hβ, if_neg e3, if_neg e5, if_neg e7, if_neg e127]
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases e3 : p = 3
    · subst e3; rw [b3]; norm_num
    by_cases e5 : p = 5
    · subst e5; rw [b5]; norm_num
    by_cases e7 : p = 7
    · subst e7; rw [b7]; norm_num
    by_cases e127 : p = 127
    · subst e127; rw [b127]; norm_num
    rw [bd p e3 e5 e7 e127]; exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  refine master_leaf hP hN hK hKK E hm β hB ?_ ?_ ?_
  · intro p hp c hc hd hmin hne
    by_cases e3 : c = 3
    · subst e3
      obtain rfl : p = 5 := T3 p hp hd
      rw [b3, b5]; norm_num
    by_cases e5 : c = 5
    · subst e5; exact absurd hd (T5 p hp)
    by_cases e7 : c = 7
    · subst e7
      have hge : 223 ≤ p := R7 (hP p hp).1 hd
        (fun h => by have := hmin 3 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) h; omega)
        (fun h => by have := hmin 5 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) h; omega)
        (fun h => h13 (S1 13 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) p hp h))
        (S4b 7 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) p hp)
        (fun h => h13 (h ▸ hp))
      rw [b7]
      exact step_ge (t := 223) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e127 : c = 127
    · subst e127
      have hge : 32257 ≤ p := R127 (hP p hp).1 hd
        (fun c' h1 h2 h3 => if hcN : c' ∈ N then by have := (hN c' hcN).2.1; omega
          else hmin c' h1 h2 hcN h3)
      rw [b127]
      exact step_ge (t := 32257) (by norm_num) hge (hB p hp).2 (by norm_num)
    exact absurd (bd c e3 e5 e7 e127) hne
  · rw [b3, b7, b31, b127]; norm_num
  · rw [b3, b7, b31, b127]; norm_num

theorem case3_iiiL {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hN : ∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (hKK : K ≤ K' ∧ ∀ L : Finset ℕ, L ⊆ P →
      (∀ q ∈ L, (∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q + 1 → c ∈ N) ∧ ¬ ∃ k, q + 1 = 2 ^ k) →
      (K' : ℚ) / K * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    (hm : 10 ≤ m) (h4 : m % 4 = 2) (h7 : 7 ∈ P) (h13 : 13 ∈ P)
    (h103 : 103 ∉ P) : False := by
  obtain ⟨h5, h3, T3, T5⟩ := case3_pre hP hN hK E h4
  obtain ⟨S1, S5, S2, S3, S4a, S4b, S6, S7⟩ := facts hP hK E
  have h31 : 31 ∉ P := by
    intro h31
    have hsub : ({3, 5, 7, 13, 31} : Finset ℕ) ⊆ P := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact h3
      · exact h5
      · exact h7
      · exact h13
      · exact h31
    have h := S_abund hP (K_pos hN hK) hKK.1 E hsub
    revert h
    decide
  have h11 : 11 ∉ P := fun h => by
    have := T3 11 h (by norm_num)
    omega
  have h17 : 17 ∉ P := fun h => by
    have := T3 17 h (by norm_num)
    omega
  have h43 : 43 ∉ P := fun h => h11 (S1 11 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) 43 h (by norm_num))
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p = if p = 3 then 8 / 5 else if p = 5 then 6 / 5 else
      if p = 7 then 8 / 7 * (14 / 13 * (1664 / 1662)) else
      if p = 13 then 14 / 13 * (1664 / 1662) else if p = 31 then 1 else
      if p = 127 then 128 / 127 * (32258 / 32256) else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have b3 : β 3 = 8 / 5 := by rw [hβ]; norm_num
  have b5 : β 5 = 6 / 5 := by rw [hβ]; norm_num
  have b7 : β 7 = 8 / 7 * (14 / 13 * (1664 / 1662)) := by rw [hβ]; norm_num
  have b13 : β 13 = 14 / 13 * (1664 / 1662) := by rw [hβ]; norm_num
  have b31 : β 31 = 1 := by rw [hβ]; norm_num
  have b127 : β 127 = 128 / 127 * (32258 / 32256) := by rw [hβ]; norm_num
  have bd : ∀ c : ℕ, c ≠ 3 → c ≠ 5 → c ≠ 7 → c ≠ 13 → c ≠ 31 → c ≠ 127 → β c = ((c : ℚ) + 1) / ((c : ℚ) - 1) :=
    fun c e3 e5 e7 e13 e31 e127 => by
      rw [hβ, if_neg e3, if_neg e5, if_neg e7, if_neg e13, if_neg e31, if_neg e127]
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases e3 : p = 3
    · subst e3; rw [b3]; norm_num
    by_cases e5 : p = 5
    · subst e5; rw [b5]; norm_num
    by_cases e7 : p = 7
    · subst e7; rw [b7]; norm_num
    by_cases e13 : p = 13
    · subst e13; rw [b13]; norm_num
    by_cases e31 : p = 31
    · subst e31; exact absurd hp h31
    by_cases e127 : p = 127
    · subst e127; rw [b127]; norm_num
    rw [bd p e3 e5 e7 e13 e31 e127]; exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  refine master_leaf hP hN hK hKK E hm β hB ?_ ?_ ?_
  · intro p hp c hc hd hmin hne
    by_cases e3 : c = 3
    · subst e3
      obtain rfl : p = 5 := T3 p hp hd
      rw [b3, b5]; norm_num
    by_cases e5 : c = 5
    · subst e5; exact absurd hd (T5 p hp)
    by_cases e7 : c = 7
    · subst e7
      obtain rfl : p = 13 := S2 7 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) p hp 13 h13 hd (by norm_num)
      rw [b7, b13]; norm_num
    by_cases e13 : c = 13
    · subst e13
      have hge : 1663 ≤ p := R13 (hP p hp).1 hd
        (fun h => by have := hmin 3 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) h; omega)
        (fun h => by have := hmin 5 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) h; omega)
        (fun h => by have := hmin 7 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) h; omega)
        (fun h => by have := hmin 11 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) h; omega)
        (fun h => h17 (S1 17 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) p hp h))
        (fun h => h43 (S1 43 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) p hp h))
        (S4b 13 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) p hp)
        (fun h => h103 (h ▸ hp))
      rw [b13]
      exact step_ge (t := 1663) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e31 : c = 31
    · subst e31; exact absurd hc h31
    by_cases e127 : c = 127
    · subst e127
      have hge : 32257 ≤ p := R127 (hP p hp).1 hd
        (fun c' h1 h2 h3 => if hcN : c' ∈ N then by have := (hN c' hcN).2.1; omega
          else hmin c' h1 h2 hcN h3)
      rw [b127]
      exact step_ge (t := 32257) (by norm_num) hge (hB p hp).2 (by norm_num)
    exact absurd (bd c e3 e5 e7 e13 e31 e127) hne
  · rw [b3, b7, b31, b127]; norm_num
  · rw [b3, b7, b31, b127]; norm_num

theorem case3_ivL {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hN : ∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (hKK : K ≤ K' ∧ ∀ L : Finset ℕ, L ⊆ P →
      (∀ q ∈ L, (∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q + 1 → c ∈ N) ∧ ¬ ∃ k, q + 1 = 2 ^ k) →
      (K' : ℚ) / K * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    (hm : 10 ≤ m) (h4 : m % 4 = 2) (h7 : 7 ∈ P) (h13 : 13 ∈ P)
    (h103 : 103 ∈ P) : False := by
  obtain ⟨h5, h3, T3, T5⟩ := case3_pre hP hN hK E h4
  obtain ⟨S1, S5, S2, S3, S4a, S4b, S6, S7⟩ := facts hP hK E
  have h31 : 31 ∉ P := by
    intro h31
    have hsub : ({3, 5, 7, 13, 31} : Finset ℕ) ⊆ P := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact h3
      · exact h5
      · exact h7
      · exact h13
      · exact h31
    have h := S_abund hP (K_pos hN hK) hKK.1 E hsub
    revert h
    decide
  have h127 : 127 ∉ P := by
    intro h127
    have hsub : ({3, 5, 7, 13, 103, 127} : Finset ℕ) ⊆ P := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact h3
      · exact h5
      · exact h7
      · exact h13
      · exact h103
      · exact h127
    have h := S_abund hP (K_pos hN hK) hKK.1 E hsub
    revert h
    decide
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p = if p = 3 then 8 / 5 else if p = 5 then 6 / 5 else
      if p = 7 then 8 / 7 * (14 / 13 * (104 / 103 * (824 / 822))) else
      if p = 13 then 14 / 13 * (104 / 103 * (824 / 822)) else
      if p = 103 then 104 / 103 * (824 / 822) else if p = 31 then 1 else
      if p = 127 then 1 else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have b3 : β 3 = 8 / 5 := by rw [hβ]; norm_num
  have b5 : β 5 = 6 / 5 := by rw [hβ]; norm_num
  have b7 : β 7 = 8 / 7 * (14 / 13 * (104 / 103 * (824 / 822))) := by rw [hβ]; norm_num
  have b13 : β 13 = 14 / 13 * (104 / 103 * (824 / 822)) := by rw [hβ]; norm_num
  have b103 : β 103 = 104 / 103 * (824 / 822) := by rw [hβ]; norm_num
  have b31 : β 31 = 1 := by rw [hβ]; norm_num
  have b127 : β 127 = 1 := by rw [hβ]; norm_num
  have bd : ∀ c : ℕ, c ≠ 3 → c ≠ 5 → c ≠ 7 → c ≠ 13 → c ≠ 103 → c ≠ 31 → c ≠ 127 →
      β c = ((c : ℚ) + 1) / ((c : ℚ) - 1) :=
    fun c e3 e5 e7 e13 e103 e31 e127 => by
      rw [hβ, if_neg e3, if_neg e5, if_neg e7, if_neg e13, if_neg e103, if_neg e31, if_neg e127]
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases e3 : p = 3
    · subst e3; rw [b3]; norm_num
    by_cases e5 : p = 5
    · subst e5; rw [b5]; norm_num
    by_cases e7 : p = 7
    · subst e7; rw [b7]; norm_num
    by_cases e13 : p = 13
    · subst e13; rw [b13]; norm_num
    by_cases e103 : p = 103
    · subst e103; rw [b103]; norm_num
    by_cases e31 : p = 31
    · subst e31; exact absurd hp h31
    by_cases e127 : p = 127
    · subst e127; exact absurd hp h127
    rw [bd p e3 e5 e7 e13 e103 e31 e127]; exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  refine master_leaf hP hN hK hKK E hm β hB ?_ ?_ ?_
  · intro p hp c hc hd hmin hne
    by_cases e3 : c = 3
    · subst e3
      obtain rfl : p = 5 := T3 p hp hd
      rw [b3, b5]; norm_num
    by_cases e5 : c = 5
    · subst e5; exact absurd hd (T5 p hp)
    by_cases e7 : c = 7
    · subst e7
      obtain rfl : p = 13 := S2 7 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) p hp 13 h13 hd (by norm_num)
      rw [b7, b13]; norm_num
    by_cases e13 : c = 13
    · subst e13
      obtain rfl : p = 103 := S2 13 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) p hp 103 h103 hd (by norm_num)
      rw [b13, b103]; norm_num
    by_cases e103 : c = 103
    · subst e103
      have hge : 823 ≤ p := R103 (hP p hp).1 hd
        (fun c' h1 h2 h3 => if hcN : c' ∈ N then by have := (hN c' hcN).2.1; omega
          else hmin c' h1 h2 hcN h3)
      rw [b103]
      exact step_ge (t := 823) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e31 : c = 31
    · subst e31; exact absurd hc h31
    by_cases e127 : c = 127
    · subst e127; exact absurd hc h127
    exact absurd (bd c e3 e5 e7 e13 e103 e31 e127) hne
  · rw [b3, b7, b31, b127]; norm_num
  · rw [b3, b7, b31, b127]; norm_num

theorem bigL {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hN : ∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (hKK : K ≤ K' ∧ ∀ L : Finset ℕ, L ⊆ P →
      (∀ q ∈ L, (∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q + 1 → c ∈ N) ∧ ¬ ∃ k, q + 1 = 2 ^ k) →
      (K' : ℚ) / K * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    (hm : 10 ≤ m) (hres : m % 4 = 0 → (∃ z ∈ N, z ∣ 2 ^ m + 1 ∧ z % 3 = 2) → 3 ∈ P → 3 ∣ K') :
    False := by
  have h : m % 4 = 0 ∨ m % 4 = 1 ∨ m % 4 = 2 ∨ m % 4 = 3 := by omega
  rcases h with h | h | h | h
  · exact case_zero_mod_fourL hP hN hK hKK E hm h (hres h)
  · exact case_oddL hP hN hK hKK E hm (by omega)
  · by_cases h13 : 13 ∈ P
    · have h7 : 7 ∈ P := (facts hP hK E).1 7 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) 13 h13 (by norm_num)
      by_cases h103 : 103 ∈ P
      · exact case3_ivL hP hN hK hKK E hm h h7 h13 h103
      · exact case3_iiiL hP hN hK hKK E hm h h7 h13 h103
    · exact case3_iiL hP hN hK hKK E hm h h13
  · exact case_oddL hP hN hK hKK E hm (by omega)

-- Section 2.  Leaf mass (round 10), the case where 3 has no simple parent (rounds 3 and 10), and
-- the two wrappers for one repeated prime.

theorem zleaf_mass {z X J : ℕ} (hz : 4 ≤ z) (hX : 4 ≤ X) (hJ : 1 ≤ J) (T : Finset ℕ)
    (hT : ∀ q k j : ℕ, q.Prime → 1 ≤ k → 1 ≤ j → j < J → q < X → q + 1 = 2 ^ k * z ^ j → q ∈ T)
    (hT2 : ∀ q ∈ T, 2 ≤ q) (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * z ^ j) :
    ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤
      (∏ q ∈ T, (((q : ℚ) + 1) / ((q : ℚ) - 1))) * ((((X : ℚ) + 1) / ((X : ℚ) - 3)) ^ J *
        ((z : ℚ) ^ J / ((z : ℚ) ^ J - 3))) := by
  classical
  choose! K Jf hKJ using fun q hq => (hL q hq).2
  have hB1 : ∀ q : ℕ, 2 ≤ q → (1 : ℚ) ≤ ((q : ℚ) + 1) / ((q : ℚ) - 1) := fun q hq => by
    have : (2 : ℚ) ≤ q := by exact_mod_cast hq
    rw [le_div_iff₀ (by linarith)]
    linarith
  have hB0 : ∀ q : ℕ, 2 ≤ q → (0 : ℚ) ≤ ((q : ℚ) + 1) / ((q : ℚ) - 1) := fun q hq =>
    le_trans zero_le_one (hB1 q hq)
  have hL2 : ∀ q ∈ L, 2 ≤ q := fun q hq => (hL q hq).1.two_le
  have pA : ∏ q ∈ L.filter (fun q => ¬ Jf q < J), (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤
      (z : ℚ) ^ J / ((z : ℚ) ^ J - 3) :=
    zleaf_bound hz J hJ _ (fun q hq => by
      obtain ⟨hqL, hj⟩ := Finset.mem_filter.mp hq
      exact ⟨K q, Jf q, (hKJ q hqL).1, by omega, (hKJ q hqL).2.2⟩)
  have pB1 : ∏ q ∈ (L.filter (fun q => Jf q < J)).filter (fun q => q < X),
      (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ ∏ q ∈ T, (((q : ℚ) + 1) / ((q : ℚ) - 1)) := by
    refine Finset.prod_le_prod_of_subset_of_one_le ?_ ?_ ?_
    · intro q hq
      obtain ⟨hq1, hqX⟩ := Finset.mem_filter.mp hq
      obtain ⟨hqL, hj⟩ := Finset.mem_filter.mp hq1
      exact hT q (K q) (Jf q) (hL q hqL).1 (hKJ q hqL).1 (hKJ q hqL).2.1 hj hqX (hKJ q hqL).2.2
    · intro q hq
      exact hB0 q (hL2 q (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1)
    · intro q hq _
      exact hB1 q (hT2 q hq)
  have pB2 : ∏ q ∈ (L.filter (fun q => Jf q < J)).filter (fun q => ¬ q < X),
      (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ (((X : ℚ) + 1) / ((X : ℚ) - 3)) ^ J := by
    have hmem : ∀ q ∈ (L.filter (fun q => Jf q < J)).filter (fun q => ¬ q < X),
        q ∈ L ∧ Jf q < J ∧ X ≤ q := fun q hq => by
      obtain ⟨hq1, hqX⟩ := Finset.mem_filter.mp hq
      obtain ⟨hqL, hj⟩ := Finset.mem_filter.mp hq1
      exact ⟨hqL, hj, by omega⟩
    rw [← Finset.prod_fiberwise_of_maps_to (g := Jf) (t := Finset.range J)
      (fun q hq => Finset.mem_range.mpr (hmem q hq).2.1)]
    calc ∏ j ∈ Finset.range J, ∏ q ∈ ((L.filter (fun q => Jf q < J)).filter
            (fun q => ¬ q < X)).filter (fun q => Jf q = j), (((q : ℚ) + 1) / ((q : ℚ) - 1))
        ≤ ∏ j ∈ Finset.range J, (((X : ℚ) + 1) / ((X : ℚ) - 3)) := by
          refine Finset.prod_le_prod (fun j _ => Finset.prod_nonneg fun q hq =>
            hB0 q (hL2 q (hmem q (Finset.mem_filter.mp hq).1).1)) (fun j _ => ?_)
          refine tail_bound _ _ X rfl hX (fun q hq => (hmem q (Finset.mem_filter.mp hq).1).2.2) ?_
          intro q hq q' hq' hlt
          obtain ⟨hq1, hjq⟩ := Finset.mem_filter.mp hq
          obtain ⟨hq1', hjq'⟩ := Finset.mem_filter.mp hq'
          have hqL := (hmem q hq1).1
          have hqL' := (hmem q' hq1').1
          have e1 := (hKJ q hqL).2.2
          have e2 := (hKJ q' hqL').2.2
          rw [hjq] at e1
          rw [hjq'] at e2
          have hzj : 1 ≤ z ^ j := Nat.one_le_pow _ _ (by omega)
          have hkk : K q < K q' := by
            by_contra hcon
            have : 2 ^ K q' ≤ 2 ^ K q := Nat.pow_le_pow_right (by norm_num) (by omega)
            have : 2 ^ K q' * z ^ j ≤ 2 ^ K q * z ^ j := Nat.mul_le_mul_right _ this
            omega
          have h2 : 2 ^ (K q + 1) ≤ 2 ^ K q' := Nat.pow_le_pow_right (by norm_num) (by omega)
          have h3 : 2 ^ (K q + 1) * z ^ j ≤ 2 ^ K q' * z ^ j := Nat.mul_le_mul_right _ h2
          rw [pow_succ] at h3
          have h4 : 2 ^ K q * 2 * z ^ j = 2 * (2 ^ K q * z ^ j) := by ring
          omega
      _ = (((X : ℚ) + 1) / ((X : ℚ) - 3)) ^ J := by rw [Finset.prod_const, Finset.card_range]
  have hXq : (4 : ℚ) ≤ X := by exact_mod_cast hX
  have hzq : (4 : ℚ) ≤ z := by exact_mod_cast hz
  have hzJ : (4 : ℚ) ≤ (z : ℚ) ^ J := by
    calc (4 : ℚ) ≤ z := hzq
      _ = (z : ℚ) ^ 1 := (pow_one _).symm
      _ ≤ (z : ℚ) ^ J := pow_le_pow_right₀ (by linarith) hJ
  have n1 : 0 ≤ ∏ q ∈ L.filter (fun q => ¬ Jf q < J), (((q : ℚ) + 1) / ((q : ℚ) - 1)) :=
    Finset.prod_nonneg fun q hq => hB0 q (hL2 q (Finset.mem_filter.mp hq).1)
  have n2 : 0 ≤ ∏ q ∈ (L.filter (fun q => Jf q < J)).filter (fun q => q < X),
      (((q : ℚ) + 1) / ((q : ℚ) - 1)) :=
    Finset.prod_nonneg fun q hq => hB0 q (hL2 q (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1)
  have n3 : 0 ≤ ∏ q ∈ (L.filter (fun q => Jf q < J)).filter (fun q => ¬ q < X),
      (((q : ℚ) + 1) / ((q : ℚ) - 1)) :=
    Finset.prod_nonneg fun q hq => hB0 q (hL2 q (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1)
  have nT : 0 ≤ ∏ q ∈ T, (((q : ℚ) + 1) / ((q : ℚ) - 1)) :=
    Finset.prod_nonneg fun q hq => hB0 q (hT2 q hq)
  have nX : 0 ≤ (((X : ℚ) + 1) / ((X : ℚ) - 3)) ^ J :=
    pow_nonneg (div_nonneg (by linarith) (by linarith)) _
  rw [← Finset.prod_filter_mul_prod_filter_not L (fun q => Jf q < J),
    ← Finset.prod_filter_mul_prod_filter_not (L.filter (fun q => Jf q < J)) (fun q => q < X)]
  calc (∏ q ∈ (L.filter (fun q => Jf q < J)).filter (fun q => q < X),
          (((q : ℚ) + 1) / ((q : ℚ) - 1))) *
        (∏ q ∈ (L.filter (fun q => Jf q < J)).filter (fun q => ¬ q < X),
          (((q : ℚ) + 1) / ((q : ℚ) - 1))) *
        ∏ q ∈ L.filter (fun q => ¬ Jf q < J), (((q : ℚ) + 1) / ((q : ℚ) - 1))
      ≤ (∏ q ∈ T, (((q : ℚ) + 1) / ((q : ℚ) - 1))) * (((X : ℚ) + 1) / ((X : ℚ) - 3)) ^ J *
          ((z : ℚ) ^ J / ((z : ℚ) ^ J - 3)) :=
        mul_le_mul (mul_le_mul pB1 pB2 n3 nT) pA n1 (mul_nonneg nT nX)
    _ = _ := by ring

-- The leaf table with j = 1 only: the leaves 2 ^ k * z - 1 below X are listed in T; the leaves
-- 2 ^ k * z ^ j - 1 with j >= 2, or above X, are bounded by geometric series (zleaf_mass, J = 2).
theorem zmass_two {z X K : ℕ} {B : ℚ} (hz : 4 ≤ z) (hX : 4 ≤ X) (hK : X < 2 ^ K * z) (T : Finset ℕ)
    (hT : ∀ k : ℕ, 1 ≤ k → k < K → (2 ^ k * z - 1).Prime → 2 ^ k * z - 1 < X → 2 ^ k * z - 1 ∈ T)
    (hT2 : ∀ q ∈ T, 2 ≤ q)
    (hfin : (1 + 1 / ((z : ℚ)) ^ 2) * ((∏ q ∈ T, (((q : ℚ) + 1) / ((q : ℚ) - 1))) *
      ((((X : ℚ) + 1) / ((X : ℚ) - 3)) ^ 2 * ((z : ℚ) ^ 2 / ((z : ℚ) ^ 2 - 3)))) ≤ B)
    (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * z ^ j) :
    (1 + 1 / ((z : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ B := by
  have h := zleaf_mass (z := z) (X := X) (J := 2) hz hX (by norm_num) T
    (by
      intro q k j hq hk hj hjJ hqX he
      have hj1 : j = 1 := by omega
      subst hj1
      rw [pow_one] at he
      have hq' : q = 2 ^ k * z - 1 := by omega
      subst hq'
      refine hT k hk ?_ hq hqX
      by_contra hcon
      have h1 : 2 ^ K ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h2 : 2 ^ K * z ≤ 2 ^ k * z := Nat.mul_le_mul_right z h1
      omega)
    hT2 L hL
  exact (mul_le_mul_of_nonneg_left h (by positivity)).trans hfin

theorem three_top_core {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N) (hK0 : 0 < K)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p) (hm : 10 ≤ m)
    (h3 : ∀ p ∈ P, ¬ 3 ∣ p + 1)
    (hΛ : ∀ L : Finset ℕ, L ⊆ P →
      (∀ q ∈ L, (∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q + 1 → c ∈ N) ∧ ¬ ∃ k, q + 1 = 2 ^ k) →
      (K' : ℚ) / K * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 311 / 300) : False := by
  classical
  let β : ℕ → ℚ := fun q => if q = 3 then 4 / 3 else ((q : ℚ) + 1) / ((q : ℚ) - 1)
  have hβ3 : β 3 = 4 / 3 := by simp [β]
  have hβB : ∀ q : ℕ, q ≠ 3 → β q = ((q : ℚ) + 1) / ((q : ℚ) - 1) := fun q hq => by simp [β, hq]
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases hp3 : p = 3
    · subst hp3
      rw [hβ3]
      norm_num
    · rw [hβB p hp3]
      exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  obtain ⟨L, hLP, hLleaf, hmain⟩ := master_gen hP hK hK0 E β hB
    (fun p hp c _ hcd _ hne => by
      by_cases hc3 : c = 3
      · subst hc3
        exact absurd hcd (h3 p hp)
      · exact absurd (hβB c hc3) hne)
  have hβpos : ∀ q ∈ L, 0 < β q := fun q hq => by
    have h0 : (0 : ℚ) ≤ 1 / (q : ℚ) := by positivity
    linarith [(hB q (hLP hq)).1]
  have hsplit := Finset.prod_filter_mul_prod_filter_not L (fun q => ∃ k, q + 1 = 2 ^ k) β
  have hrest := hΛ (L.filter (fun q => ¬ ∃ k, q + 1 = 2 ^ k))
    ((Finset.filter_subset _ _).trans hLP)
    (fun q hq => ⟨hLleaf q (Finset.mem_filter.mp hq).1, (Finset.mem_filter.mp hq).2⟩)
  have hrest' : (K' : ℚ) / K * ∏ q ∈ L.filter (fun q => ¬ ∃ k, q + 1 = 2 ^ k), β q ≤ 311 / 300 := by
    refine le_of_eq_of_le ?_ hrest
    congr 1
    refine Finset.prod_congr rfl fun q hq => hβB q ?_
    rintro rfl
    exact (Finset.mem_filter.mp hq).2 ⟨2, by norm_num⟩
  have hmers : ∏ q ∈ L.filter (fun q => ∃ k, q + 1 = 2 ^ k), β q ≤
      (β 3 * β 7 * β 31 * β 127) * (2048 / 2047) := by
    refine mersenne_bound β _ (fun q hq => (hP q (hLP (Finset.mem_filter.mp hq).1)).1)
      (fun q hq => (Finset.mem_filter.mp hq).2)
      (fun q hq => ⟨hβpos q (Finset.mem_filter.mp hq).1,
        (hB q (hLP (Finset.mem_filter.mp hq).1)).2⟩) ?_
    rw [hβ3, hβB 7 (by norm_num), hβB 31 (by norm_num), hβB 127 (by norm_num)]
    norm_num
  have hvals : (β 3 * β 7 * β 31 * β 127) * (2048 / 2047) =
      (4 / 3) * (8 / 6) * (32 / 30) * (128 / 126) * (2048 / 2047) := by
    rw [hβ3, hβB 7 (by norm_num), hβB 31 (by norm_num), hβB 127 (by norm_num)]
    norm_num
  rw [hvals] at hmers
  have hKq : (0 : ℚ) < K := by exact_mod_cast hK0
  have hKr0 : (0 : ℚ) ≤ (K' : ℚ) / K := div_nonneg (Nat.cast_nonneg _) hKq.le
  have hrest0 : (0 : ℚ) ≤ ∏ q ∈ L.filter (fun q => ¬ ∃ k, q + 1 = 2 ^ k), β q :=
    Finset.prod_nonneg fun q hq => (hβpos q (Finset.mem_filter.mp hq).1).le
  have hT : 1 + 1 / (2 : ℚ) ^ m ≤ 1025 / 1024 := by
    have h2 : (2 : ℚ) ^ 10 ≤ (2 : ℚ) ^ m := pow_le_pow_right₀ (by norm_num) hm
    have : 1 / (2 : ℚ) ^ m ≤ 1 / (2 : ℚ) ^ 10 := one_div_le_one_div_of_le (by positivity) h2
    norm_num at this ⊢
    linarith
  have hL1 : (K' : ℚ) / K * ∏ q ∈ L, β q ≤
      (4 / 3) * (8 / 6) * (32 / 30) * (128 / 126) * (2048 / 2047) * (311 / 300) := by
    rw [← hsplit]
    calc (K' : ℚ) / K * ((∏ q ∈ L.filter (fun q => ∃ k, q + 1 = 2 ^ k), β q) *
            ∏ q ∈ L.filter (fun q => ¬ ∃ k, q + 1 = 2 ^ k), β q)
        ≤ (K' : ℚ) / K * (((4 / 3) * (8 / 6) * (32 / 30) * (128 / 126) * (2048 / 2047)) *
            ∏ q ∈ L.filter (fun q => ¬ ∃ k, q + 1 = 2 ^ k), β q) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hmers hrest0) hKr0
      _ = (4 / 3) * (8 / 6) * (32 / 30) * (128 / 126) * (2048 / 2047) * ((K' : ℚ) / K *
            ∏ q ∈ L.filter (fun q => ¬ ∃ k, q + 1 = 2 ^ k), β q) := by ring
      _ ≤ (4 / 3) * (8 / 6) * (32 / 30) * (128 / 126) * (2048 / 2047) * (311 / 300) :=
          mul_le_mul_of_nonneg_left hrest' (by norm_num)
  have hfin : (2 : ℚ) ≤ 1025 / 1024 *
      ((4 / 3) * (8 / 6) * (32 / 30) * (128 / 126) * (2048 / 2047) * (311 / 300)) := by
    refine hmain.trans ?_
    rw [mul_assoc]
    exact mul_le_mul hT hL1 (mul_nonneg hKr0
      (Finset.prod_nonneg fun q hq => (hβpos q hq).le)) (by norm_num)
  norm_num at hfin

-- One repeated prime z >= 128 whose leaf mass is within 2101/2097: a <= 9 outside the residue.
theorem le_nine_of_leaf {n z : ℕ} (h : Erdos1052.IsUnitaryPerfect n) (hz : z.Prime) (hzlo : 128 ≤ z)
    (hS : ∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = z)
    (hmass : ∀ L : Finset ℕ, (∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * z ^ j) →
      (1 + 1 / ((z : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097)
    (hres : 4 ∣ padicValNat 2 n → z ∣ 2 ^ padicValNat 2 n + 1 → z % 3 = 2 →
      Odd (n.factorization z)) :
    padicValNat 2 n ≤ 9 := by
  by_contra hcon
  have hn0 : n ≠ 0 := h.2.ne'
  have hfac : n.factorization 2 = padicValNat 2 n := Nat.factorization_def n Nat.prime_two
  rw [← hfac] at hcon hres
  have hm : 10 ≤ n.factorization 2 := by omega
  have h2 : 2 ∣ n := Nat.dvd_of_factorization_pos (by omega)
  have hz2 : z ≠ 2 := by omega
  obtain ⟨hzn, hsim⟩ := OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1.simple_of_unique_repeated hn0 hS
  have hzpf : z ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hz, hzn, hn0⟩
  have hze : 2 ≤ n.factorization z :=
    (hz.pow_dvd_iff_le_factorization hn0).mp ((hS z).mpr rfl).2.2
  have hs' : ∀ r ∈ n.primeFactors, r ≠ 2 → r ∉ ({z} : Finset ℕ) → n.factorization r = 1 :=
    fun r hr hr2 hrN => hsim r hr hr2 (fun e => hrN (Finset.mem_singleton.mpr e))
  have E := kernel_balance (N := {z}) h h2 hs'
  have hP : ∀ p ∈ (n.primeFactors.erase 2).filter (fun r => ¬ r ∈ ({z} : Finset ℕ)),
      p.Prime ∧ p ≠ 2 := fun p hp => by
    have h1 := (Finset.mem_filter.mp hp).1
    exact ⟨Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase h1), Finset.ne_of_mem_erase h1⟩
  rw [filter_mem_singleton hzpf hz2, Finset.prod_singleton, Finset.prod_singleton] at E
  have hK : ∀ c : ℕ, c.Prime → c ∣ z ^ n.factorization z → c ∈ ({z} : Finset ℕ) := fun c hc hd =>
    Finset.mem_singleton.mpr ((Nat.prime_dvd_prime_iff_eq hc hz).mp (hc.dvd_of_dvd_pow hd))
  have hzq : (128 : ℚ) ≤ z := by exact_mod_cast hzlo
  have hpow : (z : ℚ) ^ 2 ≤ (z : ℚ) ^ n.factorization z := pow_le_pow_right₀ (by linarith) hze
  have hpow0 : (0 : ℚ) < (z : ℚ) ^ 2 := by positivity
  have hratio : ((1 + z ^ n.factorization z : ℕ) : ℚ) / ((z ^ n.factorization z : ℕ) : ℚ) ≤
      1 + 1 / (z : ℚ) ^ 2 := by
    push_cast
    rw [div_le_iff₀ (by linarith)]
    have h1 : 1 / (z : ℚ) ^ 2 * (z : ℚ) ^ n.factorization z ≥ 1 := by
      rw [ge_iff_le, one_div, ← div_eq_inv_mul, le_div_iff₀ hpow0]
      linarith
    nlinarith
  have hN : ∀ y ∈ ({z} : Finset ℕ), y.Prime ∧ 128 ≤ y ∧ ({z} : Finset ℕ).card + 3 ≤ y := by
    intro y hy
    rw [Finset.mem_singleton] at hy
    subst hy
    refine ⟨hz, hzlo, ?_⟩
    rw [Finset.card_singleton]
    omega
  refine bigL (N := {z}) hP hN hK
    ⟨Nat.le_add_left _ _, fun L hLP hL => ?_⟩ E hm (fun h4 hex _ => ?_)
  · have hLp : ∀ q ∈ L, q.Prime := fun q hq => (hP q (hLP hq)).1
    have hform : ∀ q ∈ L, ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * z ^ j := fun q hq =>
      zleaf_form hz hz2 (hLp q hq) (hP q (hLP hq)).2 (hL q hq).1 (hL q hq).2
    have hprod0 : (0 : ℚ) ≤ ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) :=
      Finset.prod_nonneg fun q hq => B_nonneg (hLp q hq).one_lt.le
    exact (mul_le_mul_of_nonneg_right hratio hprod0).trans
      (hmass L (fun q hq => ⟨hLp q hq, hform q hq⟩))
  · obtain ⟨y, hy, hyd, hy3⟩ := hex
    rw [Finset.mem_singleton] at hy
    subst hy
    have hodd := hres (by omega) hyd hy3
    have hdvd := Odd.nat_add_dvd_pow_add_pow y 1 hodd
    rw [one_pow] at hdvd
    have h3 : 3 ∣ y + 1 := by omega
    rw [add_comm]
    exact h3.trans hdvd

-- One repeated prime z >= 13 whose leaf mass is within 311/300: if 3 divides 2 ^ a + 1 or
-- 1 + z ^ e, then no simple prime p has 3 ∣ p + 1, and a <= 9 (rounds 3 and 10).
theorem le_nine_three_top {n z : ℕ} (h : Erdos1052.IsUnitaryPerfect n) (hz : z.Prime) (hzlo : 13 ≤ z)
    (hS : ∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = z)
    (hmass : ∀ L : Finset ℕ, (∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * z ^ j) →
      (1 + 1 / ((z : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 311 / 300)
    (hres : 3 ∣ 2 ^ padicValNat 2 n + 1 ∨ 3 ∣ 1 + z ^ n.factorization z) :
    padicValNat 2 n ≤ 9 := by
  by_contra hcon
  have hn0 : n ≠ 0 := h.2.ne'
  have hfac : n.factorization 2 = padicValNat 2 n := Nat.factorization_def n Nat.prime_two
  rw [← hfac] at hcon hres
  have hm : 10 ≤ n.factorization 2 := by omega
  have h2 : 2 ∣ n := Nat.dvd_of_factorization_pos (by omega)
  have hz2 : z ≠ 2 := by omega
  obtain ⟨hzn, hsim⟩ := OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1.simple_of_unique_repeated hn0 hS
  have hzpf : z ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hz, hzn, hn0⟩
  have hze : 2 ≤ n.factorization z :=
    (hz.pow_dvd_iff_le_factorization hn0).mp ((hS z).mpr rfl).2.2
  have hs' : ∀ r ∈ n.primeFactors, r ≠ 2 → r ∉ ({z} : Finset ℕ) → n.factorization r = 1 :=
    fun r hr hr2 hrN => hsim r hr hr2 (fun e => hrN (Finset.mem_singleton.mpr e))
  have E := kernel_balance (N := {z}) h h2 hs'
  have hP : ∀ p ∈ (n.primeFactors.erase 2).filter (fun r => ¬ r ∈ ({z} : Finset ℕ)),
      p.Prime ∧ p ≠ 2 := fun p hp => by
    have h1 := (Finset.mem_filter.mp hp).1
    exact ⟨Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase h1), Finset.ne_of_mem_erase h1⟩
  rw [filter_mem_singleton hzpf hz2, Finset.prod_singleton, Finset.prod_singleton] at E
  have hK : ∀ c : ℕ, c.Prime → c ∣ z ^ n.factorization z → c ∈ ({z} : Finset ℕ) := fun c hc hd =>
    Finset.mem_singleton.mpr ((Nat.prime_dvd_prime_iff_eq hc hz).mp (hc.dvd_of_dvd_pow hd))
  have hzq : (13 : ℚ) ≤ z := by exact_mod_cast hzlo
  have hpow : (z : ℚ) ^ 2 ≤ (z : ℚ) ^ n.factorization z := pow_le_pow_right₀ (by linarith) hze
  have hpow0 : (0 : ℚ) < (z : ℚ) ^ 2 := by positivity
  have hratio : ((1 + z ^ n.factorization z : ℕ) : ℚ) / ((z ^ n.factorization z : ℕ) : ℚ) ≤
      1 + 1 / (z : ℚ) ^ 2 := by
    push_cast
    rw [div_le_iff₀ (by linarith)]
    have h1 : 1 / (z : ℚ) ^ 2 * (z : ℚ) ^ n.factorization z ≥ 1 := by
      rw [ge_iff_le, one_div, ← div_eq_inv_mul, le_div_iff₀ hpow0]
      linarith
    nlinarith
  have h3N : 3 ∉ ({z} : Finset ℕ) := fun h' => by
    have := Finset.mem_singleton.mp h'
    omega
  obtain ⟨-, -, -, S4, -, -, -, S8⟩ := facts hP hK E
  refine three_top_core (N := {z}) hP hK (pow_pos hz.pos _) E hm (fun p hp => ?_)
    (fun L hLP hL => ?_)
  · rcases hres with h3 | h3
    · exact S4 3 Nat.prime_three (by norm_num) h3N h3 p hp
    · exact S8 3 Nat.prime_three (by norm_num) h3N h3 p hp
  · have hLp : ∀ q ∈ L, q.Prime := fun q hq => (hP q (hLP hq)).1
    have hform : ∀ q ∈ L, ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * z ^ j := fun q hq =>
      zleaf_form hz hz2 (hLp q hq) (hP q (hLP hq)).2 (hL q hq).1 (hL q hq).2
    have hprod0 : (0 : ℚ) ≤ ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) :=
      Finset.prod_nonneg fun q hq => B_nonneg (hLp q hq).one_lt.le
    exact (mul_le_mul_of_nonneg_right hratio hprod0).trans
      (hmass L (fun q hq => ⟨hLp q hq, hform q hq⟩))

theorem three_dvd_one_add_pow {z e : ℕ} (hz3 : z % 3 = 2) (ho : Odd e) : 3 ∣ 1 + z ^ e := by
  have hdvd := Odd.nat_add_dvd_pow_add_pow z 1 ho
  rw [one_pow] at hdvd
  have h3 : 3 ∣ z + 1 := by omega
  rw [add_comm]
  exact h3.trans hdvd

-- Section 3.  Order facts: when can z divide 2 ^ a + 1.

theorem one_ne_neg_one_zmod {z : ℕ} (hz : 2 < z) : (1 : ZMod z) ≠ -1 := by
  intro h3
  have h5 : ((2 : ℕ) : ZMod z) = 0 := by
    push_cast
    linear_combination h3
  have h6 := (ZMod.natCast_eq_zero_iff 2 z).mp h5
  exact absurd (Nat.le_of_dvd (by norm_num) h6) (by omega)

theorem two_pow_eq_neg_one {z a : ℕ} (hd : z ∣ 2 ^ a + 1) : (2 : ZMod z) ^ a = -1 := by
  have h1 : ((2 ^ a + 1 : ℕ) : ZMod z) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hd
  push_cast at h1
  exact eq_neg_of_add_eq_zero_left h1

-- If 16 ^ o = 1 mod z with o odd, then z never divides 2 ^ a + 1 with 4 ∣ a.
theorem not_dvd_of_four_dvd {z q r : ℕ} (hz : 2 < z) (ho : (5 * q + r) % 2 = 1)
    (hc : (16 ^ 5) ^ q * 16 ^ r % z = 1) {a : ℕ}
    (h4 : 4 ∣ a) : ¬ z ∣ 2 ^ a + 1 := by
  intro hd
  obtain ⟨b, rfl⟩ := h4
  have h16 : (16 : ZMod z) ^ (5 * q + r) = 1 := by
    have h := congrArg (Nat.cast : ℕ → ZMod z) hc
    rw [ZMod.natCast_mod] at h
    push_cast at h
    have h5 : (16 : ZMod z) ^ 5 = 1048576 := by norm_num
    rw [pow_add, pow_mul, h5]
    exact h
  have h2 := two_pow_eq_neg_one hd
  rw [pow_mul] at h2
  norm_num at h2
  have h3 : ((16 : ZMod z) ^ b) ^ (5 * q + r) = -1 := by rw [h2, (Nat.odd_iff.mpr ho).neg_one_pow]
  rw [← pow_mul, mul_comm, pow_mul, h16, one_pow] at h3
  exact one_ne_neg_one_zmod hz h3

-- If 2 ^ (2 ^ t * o) = -1 mod z with o odd, then z ∣ 2 ^ a + 1 forces a = 2 ^ t mod 2 ^ (t + 1).
theorem mod_of_dvd_two_pow_add_one {z z0 t o a : ℕ} (hz : 2 < z) (hz0 : z0 + 1 = z) (ho : o % 2 = 1)
    (hc : (2 ^ 2 ^ t) ^ o % z = z0) (hd : z ∣ 2 ^ a + 1) : a % 2 ^ (t + 1) = 2 ^ t := by
  have hne := one_ne_neg_one_zmod hz
  have hc' : (2 : ZMod z) ^ (2 ^ t * o) = -1 := by
    have h := congrArg (Nat.cast : ℕ → ZMod z) hc
    rw [ZMod.natCast_mod] at h
    push_cast at h
    rw [← pow_mul] at h
    have h0 : ((z0 + 1 : ℕ) : ZMod z) = 0 := by rw [hz0]; exact ZMod.natCast_self z
    push_cast at h0
    rw [h]
    exact eq_neg_of_add_eq_zero_left h0
  have ha := two_pow_eq_neg_one hd
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [pow_zero] at ha
    exact hne ha
  have hoo : Odd o := Nat.odd_iff.mpr ho
  obtain ⟨v, d, hdo, rfl⟩ := Nat.exists_eq_two_pow_mul_odd ha0
  rcases lt_trichotomy v t with hlt | rfl | hgt
  · exfalso
    have e1 : ((2 : ZMod z) ^ (2 ^ v * d)) ^ (2 ^ (t - v) * o) = 1 := by
      have hev : Even (2 ^ (t - v) * o) :=
        (Nat.even_pow.mpr ⟨even_two, by omega⟩).mul_right o
      rw [ha, hev.neg_one_pow]
    have e2 : ((2 : ZMod z) ^ (2 ^ v * d)) ^ (2 ^ (t - v) * o) =
        ((2 : ZMod z) ^ (2 ^ t * o)) ^ d := by
      rw [← pow_mul, ← pow_mul]
      congr 1
      have h2 : 2 ^ t = 2 ^ v * 2 ^ (t - v) := by
        rw [← pow_add]
        congr 1
        omega
      rw [h2]
      ring
    rw [e2, hc', hdo.neg_one_pow] at e1
    exact hne e1.symm
  · obtain ⟨e, rfl⟩ := hdo
    have h2 : 2 ^ v * (2 * e + 1) = 2 ^ v + 2 ^ (v + 1) * e := by ring
    rw [h2, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  · exfalso
    have e1 : ((2 : ZMod z) ^ (2 ^ v * d)) ^ o = -1 := by rw [ha, hoo.neg_one_pow]
    have e2 : ((2 : ZMod z) ^ (2 ^ v * d)) ^ o =
        (((2 : ZMod z) ^ (2 ^ t * o)) ^ (2 ^ (v - t))) ^ d := by
      rw [← pow_mul, ← pow_mul, ← pow_mul]
      congr 1
      have h2 : 2 ^ v = 2 ^ t * 2 ^ (v - t) := by
        rw [← pow_add]
        congr 1
        omega
      rw [h2]
      ring
    have hev : Even (2 ^ (v - t)) := Nat.even_pow.mpr ⟨even_two, by omega⟩
    rw [e2, hc', hev.neg_one_pow, one_pow] at e1
    exact hne e1

theorem nf_149 {a : ℕ} (h4 : 4 ∣ a) : ¬ 149 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 7) (r := 2) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_167 {a : ℕ} (h4 : 4 ∣ a) : ¬ 167 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 16) (r := 3) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_179 {a : ℕ} (h4 : 4 ∣ a) : ¬ 179 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 17) (r := 4) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_191 {a : ℕ} (h4 : 4 ∣ a) : ¬ 191 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 19) (r := 0) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_233 {a : ℕ} (h4 : 4 ∣ a) : ¬ 233 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 5) (r := 4) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_239 {a : ℕ} (h4 : 4 ∣ a) : ¬ 239 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 23) (r := 4) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_251 {a : ℕ} (h4 : 4 ∣ a) : ¬ 251 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 5) (r := 0) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_269 {a : ℕ} (h4 : 4 ∣ a) : ¬ 269 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 13) (r := 2) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_281 {a : ℕ} (h4 : 4 ∣ a) : ¬ 281 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 7) (r := 0) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_293 {a : ℕ} (h4 : 4 ∣ a) : ¬ 293 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 14) (r := 3) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_311 {a : ℕ} (h4 : 4 ∣ a) : ¬ 311 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 31) (r := 0) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_317 {a : ℕ} (h4 : 4 ∣ a) : ¬ 317 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 15) (r := 4) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_347 {a : ℕ} (h4 : 4 ∣ a) : ¬ 347 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 34) (r := 3) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_359 {a : ℕ} (h4 : 4 ∣ a) : ¬ 359 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 35) (r := 4) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_383 {a : ℕ} (h4 : 4 ∣ a) : ¬ 383 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 38) (r := 1) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_389 {a : ℕ} (h4 : 4 ∣ a) : ¬ 389 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 19) (r := 2) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_419 {a : ℕ} (h4 : 4 ∣ a) : ¬ 419 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 41) (r := 4) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_431 {a : ℕ} (h4 : 4 ∣ a) : ¬ 431 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 8) (r := 3) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_443 {a : ℕ} (h4 : 4 ∣ a) : ¬ 443 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 44) (r := 1) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_461 {a : ℕ} (h4 : 4 ∣ a) : ¬ 461 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 23) (r := 0) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_467 {a : ℕ} (h4 : 4 ∣ a) : ¬ 467 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 46) (r := 3) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_479 {a : ℕ} (h4 : 4 ∣ a) : ¬ 479 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 47) (r := 4) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_491 {a : ℕ} (h4 : 4 ∣ a) : ¬ 491 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 49) (r := 0) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_503 {a : ℕ} (h4 : 4 ∣ a) : ¬ 503 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 50) (r := 1) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_509 {a : ℕ} (h4 : 4 ∣ a) : ¬ 509 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 25) (r := 2) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_521 {a : ℕ} (h4 : 4 ∣ a) : ¬ 521 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 13) (r := 0) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_557 {a : ℕ} (h4 : 4 ∣ a) : ¬ 557 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 27) (r := 4) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_563 {a : ℕ} (h4 : 4 ∣ a) : ¬ 563 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 56) (r := 1) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_569 {a : ℕ} (h4 : 4 ∣ a) : ¬ 569 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 14) (r := 1) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_587 {a : ℕ} (h4 : 4 ∣ a) : ¬ 587 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 58) (r := 3) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_593 {a : ℕ} (h4 : 4 ∣ a) : ¬ 593 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 7) (r := 2) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_599 {a : ℕ} (h4 : 4 ∣ a) : ¬ 599 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 59) (r := 4) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_617 {a : ℕ} (h4 : 4 ∣ a) : ¬ 617 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_647 {a : ℕ} (h4 : 4 ∣ a) : ¬ 647 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 64) (r := 3) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_653 {a : ℕ} (h4 : 4 ∣ a) : ¬ 653 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 32) (r := 3) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_659 {a : ℕ} (h4 : 4 ∣ a) : ¬ 659 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 65) (r := 4) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_677 {a : ℕ} (h4 : 4 ∣ a) : ¬ 677 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 33) (r := 4) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_683 {a : ℕ} (h4 : 4 ∣ a) : ¬ 683 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 2) (r := 1) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_701 {a : ℕ} (h4 : 4 ∣ a) : ¬ 701 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 35) (r := 0) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_719 {a : ℕ} (h4 : 4 ∣ a) : ¬ 719 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 71) (r := 4) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_743 {a : ℕ} (h4 : 4 ∣ a) : ¬ 743 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 74) (r := 1) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_761 {a : ℕ} (h4 : 4 ∣ a) : ¬ 761 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 19) (r := 0) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_773 {a : ℕ} (h4 : 4 ∣ a) : ¬ 773 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 38) (r := 3) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_797 {a : ℕ} (h4 : 4 ∣ a) : ¬ 797 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 39) (r := 4) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_809 {a : ℕ} (h4 : 4 ∣ a) : ¬ 809 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 20) (r := 1) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_821 {a : ℕ} (h4 : 4 ∣ a) : ¬ 821 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 41) (r := 0) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_827 {a : ℕ} (h4 : 4 ∣ a) : ¬ 827 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 82) (r := 3) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_839 {a : ℕ} (h4 : 4 ∣ a) : ¬ 839 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 83) (r := 4) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_857 {a : ℕ} (h4 : 4 ∣ a) : ¬ 857 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 21) (r := 2) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_863 {a : ℕ} (h4 : 4 ∣ a) : ¬ 863 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 86) (r := 1) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_881 {a : ℕ} (h4 : 4 ∣ a) : ¬ 881 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 11) (r := 0) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_887 {a : ℕ} (h4 : 4 ∣ a) : ¬ 887 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 88) (r := 3) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_911 {a : ℕ} (h4 : 4 ∣ a) : ¬ 911 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 18) (r := 1) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_941 {a : ℕ} (h4 : 4 ∣ a) : ¬ 941 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 47) (r := 0) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_947 {a : ℕ} (h4 : 4 ∣ a) : ¬ 947 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 94) (r := 3) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_953 {a : ℕ} (h4 : 4 ∣ a) : ¬ 953 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 3) (r := 2) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_971 {a : ℕ} (h4 : 4 ∣ a) : ¬ 971 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 19) (r := 2) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_983 {a : ℕ} (h4 : 4 ∣ a) : ¬ 983 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 98) (r := 1) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_1013 {a : ℕ} (h4 : 4 ∣ a) : ¬ 1013 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 4) (r := 3) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_1019 {a : ℕ} (h4 : 4 ∣ a) : ¬ 1019 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 101) (r := 4) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_1031 {a : ℕ} (h4 : 4 ∣ a) : ¬ 1031 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 103) (r := 0) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_1049 {a : ℕ} (h4 : 4 ∣ a) : ¬ 1049 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 26) (r := 1) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_1061 {a : ℕ} (h4 : 4 ∣ a) : ¬ 1061 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 53) (r := 0) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_1091 {a : ℕ} (h4 : 4 ∣ a) : ¬ 1091 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 109) (r := 0) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_1097 {a : ℕ} (h4 : 4 ∣ a) : ¬ 1097 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 27) (r := 2) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_1103 {a : ℕ} (h4 : 4 ∣ a) : ¬ 1103 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 5) (r := 4) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_1109 {a : ℕ} (h4 : 4 ∣ a) : ¬ 1109 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 55) (r := 2) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_1151 {a : ℕ} (h4 : 4 ∣ a) : ¬ 1151 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 115) (r := 0) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_1163 {a : ℕ} (h4 : 4 ∣ a) : ¬ 1163 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 16) (r := 3) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_1181 {a : ℕ} (h4 : 4 ∣ a) : ¬ 1181 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 11) (r := 4) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_1187 {a : ℕ} (h4 : 4 ∣ a) : ¬ 1187 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 118) (r := 3) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_1193 {a : ℕ} (h4 : 4 ∣ a) : ¬ 1193 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 29) (r := 4) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_1223 {a : ℕ} (h4 : 4 ∣ a) : ¬ 1223 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 122) (r := 1) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_1229 {a : ℕ} (h4 : 4 ∣ a) : ¬ 1229 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 61) (r := 2) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_1259 {a : ℕ} (h4 : 4 ∣ a) : ¬ 1259 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 125) (r := 4) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_1277 {a : ℕ} (h4 : 4 ∣ a) : ¬ 1277 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 63) (r := 4) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_1283 {a : ℕ} (h4 : 4 ∣ a) : ¬ 1283 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 128) (r := 1) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_1289 {a : ℕ} (h4 : 4 ∣ a) : ¬ 1289 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 32) (r := 1) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_1301 {a : ℕ} (h4 : 4 ∣ a) : ¬ 1301 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 65) (r := 0) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_1307 {a : ℕ} (h4 : 4 ∣ a) : ¬ 1307 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 130) (r := 3) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_1319 {a : ℕ} (h4 : 4 ∣ a) : ¬ 1319 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 131) (r := 4) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_1367 {a : ℕ} (h4 : 4 ∣ a) : ¬ 1367 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 136) (r := 3) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_1373 {a : ℕ} (h4 : 4 ∣ a) : ¬ 1373 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 68) (r := 3) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_1427 {a : ℕ} (h4 : 4 ∣ a) : ¬ 1427 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 142) (r := 3) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_1433 {a : ℕ} (h4 : 4 ∣ a) : ¬ 1433 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 35) (r := 4) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_1439 {a : ℕ} (h4 : 4 ∣ a) : ¬ 1439 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 143) (r := 4) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_1451 {a : ℕ} (h4 : 4 ∣ a) : ¬ 1451 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 145) (r := 0) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_1481 {a : ℕ} (h4 : 4 ∣ a) : ¬ 1481 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 37) (r := 0) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_1487 {a : ℕ} (h4 : 4 ∣ a) : ¬ 1487 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 148) (r := 3) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_1493 {a : ℕ} (h4 : 4 ∣ a) : ¬ 1493 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 74) (r := 3) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_1499 {a : ℕ} (h4 : 4 ∣ a) : ¬ 1499 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 149) (r := 4) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_1511 {a : ℕ} (h4 : 4 ∣ a) : ¬ 1511 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 151) (r := 0) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_1523 {a : ℕ} (h4 : 4 ∣ a) : ¬ 1523 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 152) (r := 1) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_1553 {a : ℕ} (h4 : 4 ∣ a) : ¬ 1553 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 19) (r := 2) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_1559 {a : ℕ} (h4 : 4 ∣ a) : ¬ 1559 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 155) (r := 4) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_1571 {a : ℕ} (h4 : 4 ∣ a) : ¬ 1571 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 157) (r := 0) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_1583 {a : ℕ} (h4 : 4 ∣ a) : ¬ 1583 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 158) (r := 1) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_1607 {a : ℕ} (h4 : 4 ∣ a) : ¬ 1607 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 160) (r := 3) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_1613 {a : ℕ} (h4 : 4 ∣ a) : ¬ 1613 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 2) (r := 3) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_1619 {a : ℕ} (h4 : 4 ∣ a) : ¬ 1619 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 161) (r := 4) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_1637 {a : ℕ} (h4 : 4 ∣ a) : ¬ 1637 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 81) (r := 4) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_1667 {a : ℕ} (h4 : 4 ∣ a) : ¬ 1667 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 166) (r := 3) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_1709 {a : ℕ} (h4 : 4 ∣ a) : ¬ 1709 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 12) (r := 1) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_1721 {a : ℕ} (h4 : 4 ∣ a) : ¬ 1721 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 43) (r := 0) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_1733 {a : ℕ} (h4 : 4 ∣ a) : ¬ 1733 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 86) (r := 3) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_1787 {a : ℕ} (h4 : 4 ∣ a) : ¬ 1787 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 178) (r := 3) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_1811 {a : ℕ} (h4 : 4 ∣ a) : ¬ 1811 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 36) (r := 1) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_1823 {a : ℕ} (h4 : 4 ∣ a) : ¬ 1823 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 182) (r := 1) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_1847 {a : ℕ} (h4 : 4 ∣ a) : ¬ 1847 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 184) (r := 3) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_1871 {a : ℕ} (h4 : 4 ∣ a) : ¬ 1871 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 187) (r := 0) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_1877 {a : ℕ} (h4 : 4 ∣ a) : ¬ 1877 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 93) (r := 4) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_1901 {a : ℕ} (h4 : 4 ∣ a) : ¬ 1901 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 95) (r := 0) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_1907 {a : ℕ} (h4 : 4 ∣ a) : ¬ 1907 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 190) (r := 3) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_1913 {a : ℕ} (h4 : 4 ∣ a) : ¬ 1913 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 47) (r := 4) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_1931 {a : ℕ} (h4 : 4 ∣ a) : ¬ 1931 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 193) (r := 0) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_1949 {a : ℕ} (h4 : 4 ∣ a) : ¬ 1949 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 97) (r := 2) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_1973 {a : ℕ} (h4 : 4 ∣ a) : ¬ 1973 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 98) (r := 3) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_1979 {a : ℕ} (h4 : 4 ∣ a) : ¬ 1979 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 197) (r := 4) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_1997 {a : ℕ} (h4 : 4 ∣ a) : ¬ 1997 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 99) (r := 4) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_2003 {a : ℕ} (h4 : 4 ∣ a) : ¬ 2003 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 28) (r := 3) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_2027 {a : ℕ} (h4 : 4 ∣ a) : ¬ 2027 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 202) (r := 3) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_2039 {a : ℕ} (h4 : 4 ∣ a) : ¬ 2039 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 203) (r := 4) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_2063 {a : ℕ} (h4 : 4 ∣ a) : ¬ 2063 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 206) (r := 1) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_2069 {a : ℕ} (h4 : 4 ∣ a) : ¬ 2069 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 103) (r := 2) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_2087 {a : ℕ} (h4 : 4 ∣ a) : ¬ 2087 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 208) (r := 3) (by norm_num) (by norm_num) (by norm_num) h4

theorem nf_2099 {a : ℕ} (h4 : 4 ∣ a) : ¬ 2099 ∣ 2 ^ a + 1 :=
  not_dvd_of_four_dvd (q := 209) (r := 4) (by norm_num) (by norm_num) (by norm_num) h4

theorem rs_257 {a : ℕ} (hd : 257 ∣ 2 ^ a + 1) : a % 16 = 8 :=
  mod_of_dvd_two_pow_add_one (z0 := 256) (t := 3) (o := 1) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hd

theorem rs_353 {a : ℕ} (hd : 353 ∣ 2 ^ a + 1) : a % 8 = 4 :=
  mod_of_dvd_two_pow_add_one (z0 := 352) (t := 2) (o := 11) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hd

theorem rs_401 {a : ℕ} (hd : 401 ∣ 2 ^ a + 1) : a % 8 = 4 :=
  mod_of_dvd_two_pow_add_one (z0 := 400) (t := 2) (o := 25) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hd

theorem rs_449 {a : ℕ} (hd : 449 ∣ 2 ^ a + 1) : a % 32 = 16 :=
  mod_of_dvd_two_pow_add_one (z0 := 448) (t := 4) (o := 7) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hd

theorem rs_641 {a : ℕ} (hd : 641 ∣ 2 ^ a + 1) : a % 64 = 32 :=
  mod_of_dvd_two_pow_add_one (z0 := 640) (t := 5) (o := 1) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hd

theorem rs_929 {a : ℕ} (hd : 929 ∣ 2 ^ a + 1) : a % 16 = 8 :=
  mod_of_dvd_two_pow_add_one (z0 := 928) (t := 3) (o := 29) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hd

theorem rs_977 {a : ℕ} (hd : 977 ∣ 2 ^ a + 1) : a % 8 = 4 :=
  mod_of_dvd_two_pow_add_one (z0 := 976) (t := 2) (o := 61) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hd

theorem rs_1217 {a : ℕ} (hd : 1217 ∣ 2 ^ a + 1) : a % 8 = 4 :=
  mod_of_dvd_two_pow_add_one (z0 := 1216) (t := 2) (o := 19) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hd

theorem rs_1361 {a : ℕ} (hd : 1361 ∣ 2 ^ a + 1) : a % 8 = 4 :=
  mod_of_dvd_two_pow_add_one (z0 := 1360) (t := 2) (o := 85) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hd

theorem rs_1409 {a : ℕ} (hd : 1409 ∣ 2 ^ a + 1) : a % 64 = 32 :=
  mod_of_dvd_two_pow_add_one (z0 := 1408) (t := 5) (o := 11) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hd

theorem rs_1601 {a : ℕ} (hd : 1601 ∣ 2 ^ a + 1) : a % 16 = 8 :=
  mod_of_dvd_two_pow_add_one (z0 := 1600) (t := 3) (o := 25) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hd

theorem rs_1697 {a : ℕ} (hd : 1697 ∣ 2 ^ a + 1) : a % 16 = 8 :=
  mod_of_dvd_two_pow_add_one (z0 := 1696) (t := 3) (o := 53) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hd

theorem rs_1889 {a : ℕ} (hd : 1889 ∣ 2 ^ a + 1) : a % 8 = 4 :=
  mod_of_dvd_two_pow_add_one (z0 := 1888) (t := 2) (o := 59) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hd

theorem rs_2081 {a : ℕ} (hd : 2081 ∣ 2 ^ a + 1) : a % 16 = 8 :=
  mod_of_dvd_two_pow_add_one (z0 := 2080) (t := 3) (o := 65) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hd

-- Section 4.  Leaf tables for budget 2101/2097, one per prime.

theorem zmass_149 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 149 ^ j) :
    (1 + 1 / (((149 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 7) (by norm_num) (by norm_num) (by norm_num) ({2383} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_151 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 151 ^ j) :
    (1 + 1 / (((151 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 7) (by norm_num) (by norm_num) (by norm_num) ({4831} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_163 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 163 ^ j) :
    (1 + 1 / (((163 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 100000) (K := 10) (by norm_num) (by norm_num) (by norm_num) ({1303} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_167 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 167 ^ j) :
    (1 + 1 / (((167 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 6) (by norm_num) (by norm_num) (by norm_num) ({2671} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_179 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 179 ^ j) :
    (1 + 1 / (((179 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 6) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_181 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 181 ^ j) :
    (1 + 1 / (((181 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 := by
  have h := zleaf_mass (z := 181) (X := 10000000) (J := 3) (by norm_num) (by norm_num) (by norm_num) ({1447, 5791, 23167, 65521, 92671, 370687} : Finset ℕ)
    (by
      intro q k j hq hk hj hjJ hqX he
      have hzj : 181 ≤ 181 ^ j := Nat.le_self_pow (by omega) _
      have hk' : k < 16 := by
        by_contra hcon
        have h1 : 2 ^ 16 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
        have h2 := Nat.mul_le_mul h1 hzj
        norm_num at h2
        omega
      have hq' : q = 2 ^ k * 181 ^ j - 1 := by omega
      interval_cases j <;> interval_cases k <;> norm_num at hq' <;> subst hq' <;>
        first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_insert, Finset.mem_singleton] at hq; omega) L hL
  refine (mul_le_mul_of_nonneg_left h (by positivity)).trans ?_
  norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]

theorem zmass_191 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 191 ^ j) :
    (1 + 1 / (((191 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 6) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_193 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 193 ^ j) :
    (1 + 1 / (((193 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 100000) (K := 10) (by norm_num) (by norm_num) (by norm_num) ({1543} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_223 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 223 ^ j) :
    (1 + 1 / (((223 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 100000) (K := 9) (by norm_num) (by norm_num) (by norm_num) ({1783} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_233 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 233 ^ j) :
    (1 + 1 / (((233 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 6) (by norm_num) (by norm_num) (by norm_num) ({3727} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_239 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 239 ^ j) :
    (1 + 1 / (((239 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 6) (by norm_num) (by norm_num) (by norm_num) ({3823} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_241 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 241 ^ j) :
    (1 + 1 / (((241 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 6) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_251 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 251 ^ j) :
    (1 + 1 / (((251 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 6) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_257 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 257 ^ j) :
    (1 + 1 / (((257 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 6) (by norm_num) (by norm_num) (by norm_num) ({4111} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_269 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 269 ^ j) :
    (1 + 1 / (((269 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 6) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_277 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 277 ^ j) :
    (1 + 1 / (((277 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 6) (by norm_num) (by norm_num) (by norm_num) ({8863} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_281 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 281 ^ j) :
    (1 + 1 / (((281 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 1000000) (K := 12) (by norm_num) (by norm_num) (by norm_num) ({1123} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_283 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 283 ^ j) :
    (1 + 1 / (((283 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 6) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_293 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 293 ^ j) :
    (1 + 1 / (((293 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 100000) (K := 9) (by norm_num) (by norm_num) (by norm_num) ({1171} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_311 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 311 ^ j) :
    (1 + 1 / (((311 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 6) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_313 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 313 ^ j) :
    (1 + 1 / (((313 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 5) (by norm_num) (by norm_num) (by norm_num) ({2503} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_317 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 317 ^ j) :
    (1 + 1 / (((317 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 5) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_347 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 347 ^ j) :
    (1 + 1 / (((347 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 5) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_349 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 349 ^ j) :
    (1 + 1 / (((349 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 5) (by norm_num) (by norm_num) (by norm_num) ({2791} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_353 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 353 ^ j) :
    (1 + 1 / (((353 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 5) (by norm_num) (by norm_num) (by norm_num) ({5647} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_359 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 359 ^ j) :
    (1 + 1 / (((359 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 5) (by norm_num) (by norm_num) (by norm_num) ({5743} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_373 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 373 ^ j) :
    (1 + 1 / (((373 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 5) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_383 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 383 ^ j) :
    (1 + 1 / (((383 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 100000) (K := 9) (by norm_num) (by norm_num) (by norm_num) ({1531, 98047} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_insert, Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_389 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 389 ^ j) :
    (1 + 1 / (((389 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 5) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_397 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 397 ^ j) :
    (1 + 1 / (((397 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 5) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_401 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 401 ^ j) :
    (1 + 1 / (((401 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 5) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_409 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 409 ^ j) :
    (1 + 1 / (((409 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 5) (by norm_num) (by norm_num) (by norm_num) ({3271} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_419 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 419 ^ j) :
    (1 + 1 / (((419 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 5) (by norm_num) (by norm_num) (by norm_num) ({6703} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_421 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 421 ^ j) :
    (1 + 1 / (((421 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 5) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_431 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 431 ^ j) :
    (1 + 1 / (((431 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 100000) (K := 8) (by norm_num) (by norm_num) (by norm_num) ({1723, 27583} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_insert, Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_433 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 433 ^ j) :
    (1 + 1 / (((433 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 5) (by norm_num) (by norm_num) (by norm_num) ({3463} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_443 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 443 ^ j) :
    (1 + 1 / (((443 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 5) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_449 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 449 ^ j) :
    (1 + 1 / (((449 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 5) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_457 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 457 ^ j) :
    (1 + 1 / (((457 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 5) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_461 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 461 ^ j) :
    (1 + 1 / (((461 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 5) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_463 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 463 ^ j) :
    (1 + 1 / (((463 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 5) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_467 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 467 ^ j) :
    (1 + 1 / (((467 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 5) (by norm_num) (by norm_num) (by norm_num) ({1867} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_479 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 479 ^ j) :
    (1 + 1 / (((479 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 5) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_487 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 487 ^ j) :
    (1 + 1 / (((487 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 5) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_491 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 491 ^ j) :
    (1 + 1 / (((491 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 5) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_503 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 503 ^ j) :
    (1 + 1 / (((503 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 5) (by norm_num) (by norm_num) (by norm_num) ({2011} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_509 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 509 ^ j) :
    (1 + 1 / (((509 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 5) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_521 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 521 ^ j) :
    (1 + 1 / (((521 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 5) (by norm_num) (by norm_num) (by norm_num) ({2083} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_523 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 523 ^ j) :
    (1 + 1 / (((523 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 5) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_541 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 541 ^ j) :
    (1 + 1 / (((541 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 5) (by norm_num) (by norm_num) (by norm_num) ({4327} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_547 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 547 ^ j) :
    (1 + 1 / (((547 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 1000000) (K := 11) (by norm_num) (by norm_num) (by norm_num) ({1093} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_557 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 557 ^ j) :
    (1 + 1 / (((557 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 5) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_563 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 563 ^ j) :
    (1 + 1 / (((563 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 100000) (K := 8) (by norm_num) (by norm_num) (by norm_num) ({2251, 9007} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_insert, Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_569 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 569 ^ j) :
    (1 + 1 / (((569 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 5) (by norm_num) (by norm_num) (by norm_num) ({9103} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_571 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 571 ^ j) :
    (1 + 1 / (((571 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 5) (by norm_num) (by norm_num) (by norm_num) ({4567} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_577 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 577 ^ j) :
    (1 + 1 / (((577 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 100000) (K := 8) (by norm_num) (by norm_num) (by norm_num) ({1153} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_587 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 587 ^ j) :
    (1 + 1 / (((587 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 5) (by norm_num) (by norm_num) (by norm_num) ({2347, 9391} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_insert, Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_593 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 593 ^ j) :
    (1 + 1 / (((593 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 5) (by norm_num) (by norm_num) (by norm_num) ({2371} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_599 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 599 ^ j) :
    (1 + 1 / (((599 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 5) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_601 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 601 ^ j) :
    (1 + 1 / (((601 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 100000) (K := 8) (by norm_num) (by norm_num) (by norm_num) ({1201, 19231} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_insert, Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_607 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 607 ^ j) :
    (1 + 1 / (((607 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 100000) (K := 8) (by norm_num) (by norm_num) (by norm_num) ({1213, 19423} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_insert, Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_613 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 613 ^ j) :
    (1 + 1 / (((613 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 5) (by norm_num) (by norm_num) (by norm_num) ({4903} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_617 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 617 ^ j) :
    (1 + 1 / (((617 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 5) (by norm_num) (by norm_num) (by norm_num) ({2467, 9871} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_insert, Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_631 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 631 ^ j) :
    (1 + 1 / (((631 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 4) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_641 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 641 ^ j) :
    (1 + 1 / (((641 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 4) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_643 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 643 ^ j) :
    (1 + 1 / (((643 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 4) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_647 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 647 ^ j) :
    (1 + 1 / (((647 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 4) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_653 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 653 ^ j) :
    (1 + 1 / (((653 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 4) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_659 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 659 ^ j) :
    (1 + 1 / (((659 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 4) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_661 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 661 ^ j) :
    (1 + 1 / (((661 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 100000) (K := 8) (by norm_num) (by norm_num) (by norm_num) ({1321} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_673 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 673 ^ j) :
    (1 + 1 / (((673 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 4) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_677 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 677 ^ j) :
    (1 + 1 / (((677 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 4) (by norm_num) (by norm_num) (by norm_num) ({2707} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_683 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 683 ^ j) :
    (1 + 1 / (((683 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 4) (by norm_num) (by norm_num) (by norm_num) ({2731} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_691 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 691 ^ j) :
    (1 + 1 / (((691 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 := by
  have h := zleaf_mass (z := 691) (X := 10000000) (J := 3) (by norm_num) (by norm_num) (by norm_num) ({1381, 5527, 22111} : Finset ℕ)
    (by
      intro q k j hq hk hj hjJ hqX he
      have hzj : 691 ≤ 691 ^ j := Nat.le_self_pow (by omega) _
      have hk' : k < 14 := by
        by_contra hcon
        have h1 : 2 ^ 14 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
        have h2 := Nat.mul_le_mul h1 hzj
        norm_num at h2
        omega
      have hq' : q = 2 ^ k * 691 ^ j - 1 := by omega
      interval_cases j <;> interval_cases k <;> norm_num at hq' <;> subst hq' <;>
        first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_insert, Finset.mem_singleton] at hq; omega) L hL
  refine (mul_le_mul_of_nonneg_left h (by positivity)).trans ?_
  norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]

theorem zmass_701 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 701 ^ j) :
    (1 + 1 / (((701 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 4) (by norm_num) (by norm_num) (by norm_num) ({2803} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_709 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 709 ^ j) :
    (1 + 1 / (((709 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 4) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_719 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 719 ^ j) :
    (1 + 1 / (((719 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 4) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_727 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 727 ^ j) :
    (1 + 1 / (((727 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 100000) (K := 8) (by norm_num) (by norm_num) (by norm_num) ({1453} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_733 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 733 ^ j) :
    (1 + 1 / (((733 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 4) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_739 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 739 ^ j) :
    (1 + 1 / (((739 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 4) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_743 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 743 ^ j) :
    (1 + 1 / (((743 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 4) (by norm_num) (by norm_num) (by norm_num) ({2971} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_751 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 751 ^ j) :
    (1 + 1 / (((751 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 4) (by norm_num) (by norm_num) (by norm_num) ({6007} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_757 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 757 ^ j) :
    (1 + 1 / (((757 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 4) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_761 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 761 ^ j) :
    (1 + 1 / (((761 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 4) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_769 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 769 ^ j) :
    (1 + 1 / (((769 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 4) (by norm_num) (by norm_num) (by norm_num) ({6151} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_773 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 773 ^ j) :
    (1 + 1 / (((773 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 4) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_787 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 787 ^ j) :
    (1 + 1 / (((787 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 4) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_797 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 797 ^ j) :
    (1 + 1 / (((797 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 4) (by norm_num) (by norm_num) (by norm_num) ({3187} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_809 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 809 ^ j) :
    (1 + 1 / (((809 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 4) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_811 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 811 ^ j) :
    (1 + 1 / (((811 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 100000) (K := 7) (by norm_num) (by norm_num) (by norm_num) ({1621, 25951} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_insert, Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_821 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 821 ^ j) :
    (1 + 1 / (((821 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 4) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_823 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 823 ^ j) :
    (1 + 1 / (((823 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 4) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_827 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 827 ^ j) :
    (1 + 1 / (((827 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 4) (by norm_num) (by norm_num) (by norm_num) ({3307} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_829 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 829 ^ j) :
    (1 + 1 / (((829 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 100000) (K := 7) (by norm_num) (by norm_num) (by norm_num) ({1657} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_839 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 839 ^ j) :
    (1 + 1 / (((839 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 4) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_853 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 853 ^ j) :
    (1 + 1 / (((853 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 4) (by norm_num) (by norm_num) (by norm_num) ({6823} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_857 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 857 ^ j) :
    (1 + 1 / (((857 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 4) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_859 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 859 ^ j) :
    (1 + 1 / (((859 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 4) (by norm_num) (by norm_num) (by norm_num) ({6871} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_863 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 863 ^ j) :
    (1 + 1 / (((863 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 4) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_877 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 877 ^ j) :
    (1 + 1 / (((877 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 100000) (K := 7) (by norm_num) (by norm_num) (by norm_num) ({1753} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_881 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 881 ^ j) :
    (1 + 1 / (((881 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 4) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_883 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 883 ^ j) :
    (1 + 1 / (((883 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 4) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_887 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 887 ^ j) :
    (1 + 1 / (((887 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 4) (by norm_num) (by norm_num) (by norm_num) ({3547} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_907 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 907 ^ j) :
    (1 + 1 / (((907 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 4) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_911 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 911 ^ j) :
    (1 + 1 / (((911 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 4) (by norm_num) (by norm_num) (by norm_num) ({3643} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_919 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 919 ^ j) :
    (1 + 1 / (((919 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 4) (by norm_num) (by norm_num) (by norm_num) ({7351} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_929 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 929 ^ j) :
    (1 + 1 / (((929 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 4) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_937 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 937 ^ j) :
    (1 + 1 / (((937 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 4) (by norm_num) (by norm_num) (by norm_num) ({1873} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_941 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 941 ^ j) :
    (1 + 1 / (((941 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 4) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_947 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 947 ^ j) :
    (1 + 1 / (((947 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 4) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_953 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 953 ^ j) :
    (1 + 1 / (((953 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 4) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_967 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 967 ^ j) :
    (1 + 1 / (((967 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 4) (by norm_num) (by norm_num) (by norm_num) ({1933} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_971 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 971 ^ j) :
    (1 + 1 / (((971 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 4) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_977 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 977 ^ j) :
    (1 + 1 / (((977 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 4) (by norm_num) (by norm_num) (by norm_num) ({3907} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_983 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 983 ^ j) :
    (1 + 1 / (((983 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 4) (by norm_num) (by norm_num) (by norm_num) ({3931} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_991 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 991 ^ j) :
    (1 + 1 / (((991 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 4) (by norm_num) (by norm_num) (by norm_num) ({7927} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_997 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 997 ^ j) :
    (1 + 1 / (((997 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 4) (by norm_num) (by norm_num) (by norm_num) ({1993} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1009 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1009 ^ j) :
    (1 + 1 / (((1009 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 4) (by norm_num) (by norm_num) (by norm_num) ({2017} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1013 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1013 ^ j) :
    (1 + 1 / (((1013 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 4) (by norm_num) (by norm_num) (by norm_num) ({4051} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1019 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1019 ^ j) :
    (1 + 1 / (((1019 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 4) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1021 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1021 ^ j) :
    (1 + 1 / (((1021 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 4) (by norm_num) (by norm_num) (by norm_num) ({8167} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1031 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1031 ^ j) :
    (1 + 1 / (((1031 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 4) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1033 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1033 ^ j) :
    (1 + 1 / (((1033 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 4) (by norm_num) (by norm_num) (by norm_num) ({8263} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1039 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1039 ^ j) :
    (1 + 1 / (((1039 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 4) (by norm_num) (by norm_num) (by norm_num) ({8311} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1049 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1049 ^ j) :
    (1 + 1 / (((1049 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 4) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1051 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1051 ^ j) :
    (1 + 1 / (((1051 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 4) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1061 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1061 ^ j) :
    (1 + 1 / (((1061 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 4) (by norm_num) (by norm_num) (by norm_num) ({4243} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1063 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1063 ^ j) :
    (1 + 1 / (((1063 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 4) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1069 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1069 ^ j) :
    (1 + 1 / (((1069 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 4) (by norm_num) (by norm_num) (by norm_num) ({2137} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1087 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1087 ^ j) :
    (1 + 1 / (((1087 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 4) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1091 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1091 ^ j) :
    (1 + 1 / (((1091 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 4) (by norm_num) (by norm_num) (by norm_num) ({4363} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1093 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1093 ^ j) :
    (1 + 1 / (((1093 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 4) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1097 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1097 ^ j) :
    (1 + 1 / (((1097 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 4) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1103 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1103 ^ j) :
    (1 + 1 / (((1103 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 4) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1109 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1109 ^ j) :
    (1 + 1 / (((1109 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 4) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1117 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1117 ^ j) :
    (1 + 1 / (((1117 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 4) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1123 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1123 ^ j) :
    (1 + 1 / (((1123 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 4) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1129 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1129 ^ j) :
    (1 + 1 / (((1129 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 4) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1151 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1151 ^ j) :
    (1 + 1 / (((1151 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 4) (by norm_num) (by norm_num) (by norm_num) ({4603} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1153 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1153 ^ j) :
    (1 + 1 / (((1153 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 4) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1163 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1163 ^ j) :
    (1 + 1 / (((1163 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 4) (by norm_num) (by norm_num) (by norm_num) ({4651} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1171 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1171 ^ j) :
    (1 + 1 / (((1171 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 4) (by norm_num) (by norm_num) (by norm_num) ({2341} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1181 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1181 ^ j) :
    (1 + 1 / (((1181 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 4) (by norm_num) (by norm_num) (by norm_num) ({4723} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1187 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1187 ^ j) :
    (1 + 1 / (((1187 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 4) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1193 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1193 ^ j) :
    (1 + 1 / (((1193 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 4) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1201 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1201 ^ j) :
    (1 + 1 / (((1201 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 4) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1213 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1213 ^ j) :
    (1 + 1 / (((1213 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 4) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1217 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1217 ^ j) :
    (1 + 1 / (((1217 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 4) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1223 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1223 ^ j) :
    (1 + 1 / (((1223 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 4) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1229 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1229 ^ j) :
    (1 + 1 / (((1229 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 4) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1231 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1231 ^ j) :
    (1 + 1 / (((1231 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 4) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1237 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1237 ^ j) :
    (1 + 1 / (((1237 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 4) (by norm_num) (by norm_num) (by norm_num) ({2473} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1249 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1249 ^ j) :
    (1 + 1 / (((1249 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 4) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1259 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1259 ^ j) :
    (1 + 1 / (((1259 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1277 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1277 ^ j) :
    (1 + 1 / (((1277 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) ({5107} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1279 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1279 ^ j) :
    (1 + 1 / (((1279 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) ({2557} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1283 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1283 ^ j) :
    (1 + 1 / (((1283 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1289 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1289 ^ j) :
    (1 + 1 / (((1289 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1291 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1291 ^ j) :
    (1 + 1 / (((1291 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1297 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1297 ^ j) :
    (1 + 1 / (((1297 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) ({2593} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1301 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1301 ^ j) :
    (1 + 1 / (((1301 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1303 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1303 ^ j) :
    (1 + 1 / (((1303 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1307 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1307 ^ j) :
    (1 + 1 / (((1307 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) ({5227} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1319 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1319 ^ j) :
    (1 + 1 / (((1319 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1321 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1321 ^ j) :
    (1 + 1 / (((1321 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1327 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1327 ^ j) :
    (1 + 1 / (((1327 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1361 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1361 ^ j) :
    (1 + 1 / (((1361 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) ({5443} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1367 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1367 ^ j) :
    (1 + 1 / (((1367 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1373 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1373 ^ j) :
    (1 + 1 / (((1373 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1381 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1381 ^ j) :
    (1 + 1 / (((1381 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1399 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1399 ^ j) :
    (1 + 1 / (((1399 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) ({2797} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1409 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1409 ^ j) :
    (1 + 1 / (((1409 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1423 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1423 ^ j) :
    (1 + 1 / (((1423 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1427 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1427 ^ j) :
    (1 + 1 / (((1427 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1429 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1429 ^ j) :
    (1 + 1 / (((1429 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) ({2857} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1433 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1433 ^ j) :
    (1 + 1 / (((1433 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1439 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1439 ^ j) :
    (1 + 1 / (((1439 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1447 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1447 ^ j) :
    (1 + 1 / (((1447 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1451 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1451 ^ j) :
    (1 + 1 / (((1451 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1453 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1453 ^ j) :
    (1 + 1 / (((1453 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1459 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1459 ^ j) :
    (1 + 1 / (((1459 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) ({2917} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1471 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1471 ^ j) :
    (1 + 1 / (((1471 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1481 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1481 ^ j) :
    (1 + 1 / (((1481 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) ({5923} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1483 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1483 ^ j) :
    (1 + 1 / (((1483 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1487 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1487 ^ j) :
    (1 + 1 / (((1487 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1489 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1489 ^ j) :
    (1 + 1 / (((1489 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1493 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1493 ^ j) :
    (1 + 1 / (((1493 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1499 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1499 ^ j) :
    (1 + 1 / (((1499 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1511 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1511 ^ j) :
    (1 + 1 / (((1511 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) ({6043} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1523 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1523 ^ j) :
    (1 + 1 / (((1523 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) ({6091} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1531 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1531 ^ j) :
    (1 + 1 / (((1531 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) ({3061} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1543 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1543 ^ j) :
    (1 + 1 / (((1543 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1549 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1549 ^ j) :
    (1 + 1 / (((1549 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1553 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1553 ^ j) :
    (1 + 1 / (((1553 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) ({6211} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1559 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1559 ^ j) :
    (1 + 1 / (((1559 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1567 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1567 ^ j) :
    (1 + 1 / (((1567 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1571 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1571 ^ j) :
    (1 + 1 / (((1571 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1579 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1579 ^ j) :
    (1 + 1 / (((1579 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1583 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1583 ^ j) :
    (1 + 1 / (((1583 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1597 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1597 ^ j) :
    (1 + 1 / (((1597 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1601 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1601 ^ j) :
    (1 + 1 / (((1601 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1607 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1607 ^ j) :
    (1 + 1 / (((1607 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) ({6427} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1609 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1609 ^ j) :
    (1 + 1 / (((1609 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) ({3217} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1613 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1613 ^ j) :
    (1 + 1 / (((1613 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) ({6451} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1619 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1619 ^ j) :
    (1 + 1 / (((1619 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1621 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1621 ^ j) :
    (1 + 1 / (((1621 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1627 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1627 ^ j) :
    (1 + 1 / (((1627 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) ({3253} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1637 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1637 ^ j) :
    (1 + 1 / (((1637 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) ({6547} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1657 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1657 ^ j) :
    (1 + 1 / (((1657 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) ({3313} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1663 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1663 ^ j) :
    (1 + 1 / (((1663 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1667 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1667 ^ j) :
    (1 + 1 / (((1667 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1669 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1669 ^ j) :
    (1 + 1 / (((1669 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1693 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1693 ^ j) :
    (1 + 1 / (((1693 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1697 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1697 ^ j) :
    (1 + 1 / (((1697 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1699 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1699 ^ j) :
    (1 + 1 / (((1699 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1709 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1709 ^ j) :
    (1 + 1 / (((1709 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1721 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1721 ^ j) :
    (1 + 1 / (((1721 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) ({6883} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1723 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1723 ^ j) :
    (1 + 1 / (((1723 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1733 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1733 ^ j) :
    (1 + 1 / (((1733 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1741 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1741 ^ j) :
    (1 + 1 / (((1741 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1747 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1747 ^ j) :
    (1 + 1 / (((1747 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1753 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1753 ^ j) :
    (1 + 1 / (((1753 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1759 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1759 ^ j) :
    (1 + 1 / (((1759 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) ({3517} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1777 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1777 ^ j) :
    (1 + 1 / (((1777 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1783 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1783 ^ j) :
    (1 + 1 / (((1783 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1787 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1787 ^ j) :
    (1 + 1 / (((1787 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1789 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1789 ^ j) :
    (1 + 1 / (((1789 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1801 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1801 ^ j) :
    (1 + 1 / (((1801 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1811 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1811 ^ j) :
    (1 + 1 / (((1811 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) ({7243} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1823 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1823 ^ j) :
    (1 + 1 / (((1823 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1831 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1831 ^ j) :
    (1 + 1 / (((1831 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1847 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1847 ^ j) :
    (1 + 1 / (((1847 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1861 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1861 ^ j) :
    (1 + 1 / (((1861 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1867 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1867 ^ j) :
    (1 + 1 / (((1867 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) ({3733} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1871 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1871 ^ j) :
    (1 + 1 / (((1871 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1873 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1873 ^ j) :
    (1 + 1 / (((1873 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1877 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1877 ^ j) :
    (1 + 1 / (((1877 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) ({7507} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1879 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1879 ^ j) :
    (1 + 1 / (((1879 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1889 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1889 ^ j) :
    (1 + 1 / (((1889 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1901 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1901 ^ j) :
    (1 + 1 / (((1901 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) ({7603} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1907 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1907 ^ j) :
    (1 + 1 / (((1907 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1913 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1913 ^ j) :
    (1 + 1 / (((1913 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1931 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1931 ^ j) :
    (1 + 1 / (((1931 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) ({7723} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1933 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1933 ^ j) :
    (1 + 1 / (((1933 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1949 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1949 ^ j) :
    (1 + 1 / (((1949 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1951 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1951 ^ j) :
    (1 + 1 / (((1951 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1973 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1973 ^ j) :
    (1 + 1 / (((1973 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1979 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1979 ^ j) :
    (1 + 1 / (((1979 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1987 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1987 ^ j) :
    (1 + 1 / (((1987 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1993 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1993 ^ j) :
    (1 + 1 / (((1993 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1997 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1997 ^ j) :
    (1 + 1 / (((1997 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_1999 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 1999 ^ j) :
    (1 + 1 / (((1999 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_2003 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 2003 ^ j) :
    (1 + 1 / (((2003 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) ({8011} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_2011 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 2011 ^ j) :
    (1 + 1 / (((2011 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) ({4021} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_2017 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 2017 ^ j) :
    (1 + 1 / (((2017 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_2027 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 2027 ^ j) :
    (1 + 1 / (((2027 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_2029 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 2029 ^ j) :
    (1 + 1 / (((2029 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) ({4057} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_2039 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 2039 ^ j) :
    (1 + 1 / (((2039 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_2053 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 2053 ^ j) :
    (1 + 1 / (((2053 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_2063 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 2063 ^ j) :
    (1 + 1 / (((2063 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_2069 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 2069 ^ j) :
    (1 + 1 / (((2069 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_2081 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 2081 ^ j) :
    (1 + 1 / (((2081 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_2083 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 2083 ^ j) :
    (1 + 1 / (((2083 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_2087 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 2087 ^ j) :
    (1 + 1 / (((2087 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_2089 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 2089 ^ j) :
    (1 + 1 / (((2089 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) ({4177} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem zmass_2099 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 2099 ^ j) :
    (1 + 1 / (((2099 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2101 / 2097 :=
  zmass_two (X := 10000) (K := 3) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

-- Section 5.  Leaf tables for budget 311/300 (the primes of H2).

theorem tmass_13 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 13 ^ j) :
    (1 + 1 / (((13 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 311 / 300 := by
  have h := zleaf_mass (z := 13) (X := 10000) (J := 3) (by norm_num) (by norm_num) (by norm_num) ({103, 337, 1663, 5407} : Finset ℕ)
    (by
      intro q k j hq hk hj hjJ hqX he
      have hzj : 13 ≤ 13 ^ j := Nat.le_self_pow (by omega) _
      have hk' : k < 10 := by
        by_contra hcon
        have h1 : 2 ^ 10 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
        have h2 := Nat.mul_le_mul h1 hzj
        norm_num at h2
        omega
      have hq' : q = 2 ^ k * 13 ^ j - 1 := by omega
      interval_cases j <;> interval_cases k <;> norm_num at hq' <;> subst hq' <;>
        first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_insert, Finset.mem_singleton] at hq; omega) L hL
  refine (mul_le_mul_of_nonneg_left h (by positivity)).trans ?_
  norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]

theorem tmass_23 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 23 ^ j) :
    (1 + 1 / (((23 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 311 / 300 :=
  zmass_two (X := 10000) (K := 9) (by norm_num) (by norm_num) (by norm_num) ({367, 1471} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_insert, Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem tmass_29 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 29 ^ j) :
    (1 + 1 / (((29 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 311 / 300 :=
  zmass_two (X := 10000) (K := 9) (by norm_num) (by norm_num) (by norm_num) ({463} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem tmass_37 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 37 ^ j) :
    (1 + 1 / (((37 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 311 / 300 :=
  zmass_two (X := 10000) (K := 9) (by norm_num) (by norm_num) (by norm_num) ({73} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem tmass_41 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 41 ^ j) :
    (1 + 1 / (((41 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 311 / 300 :=
  zmass_two (X := 10000) (K := 8) (by norm_num) (by norm_num) (by norm_num) ({163} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem tmass_43 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 43 ^ j) :
    (1 + 1 / (((43 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 311 / 300 :=
  zmass_two (X := 10000) (K := 8) (by norm_num) (by norm_num) (by norm_num) ({5503} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem tmass_47 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 47 ^ j) :
    (1 + 1 / (((47 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 311 / 300 :=
  zmass_two (X := 10000) (K := 8) (by norm_num) (by norm_num) (by norm_num) ({751} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem tmass_53 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 53 ^ j) :
    (1 + 1 / (((53 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 311 / 300 :=
  zmass_two (X := 10000) (K := 8) (by norm_num) (by norm_num) (by norm_num) ({211, 3391} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_insert, Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem tmass_59 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 59 ^ j) :
    (1 + 1 / (((59 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 311 / 300 :=
  zmass_two (X := 10000) (K := 8) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem tmass_61 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 61 ^ j) :
    (1 + 1 / (((61 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 311 / 300 :=
  zmass_two (X := 10000) (K := 8) (by norm_num) (by norm_num) (by norm_num) ({487, 1951} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_insert, Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem tmass_67 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 67 ^ j) :
    (1 + 1 / (((67 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 311 / 300 :=
  zmass_two (X := 10000) (K := 8) (by norm_num) (by norm_num) (by norm_num) ({2143} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem tmass_71 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 71 ^ j) :
    (1 + 1 / (((71 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 311 / 300 :=
  zmass_two (X := 10000) (K := 8) (by norm_num) (by norm_num) (by norm_num) ({283} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem tmass_73 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 73 ^ j) :
    (1 + 1 / (((73 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 311 / 300 :=
  zmass_two (X := 10000) (K := 8) (by norm_num) (by norm_num) (by norm_num) ({9343} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem tmass_79 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 79 ^ j) :
    (1 + 1 / (((79 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 311 / 300 :=
  zmass_two (X := 10000) (K := 7) (by norm_num) (by norm_num) (by norm_num) ({157, 631} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_insert, Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem tmass_83 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 83 ^ j) :
    (1 + 1 / (((83 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 311 / 300 :=
  zmass_two (X := 10000) (K := 7) (by norm_num) (by norm_num) (by norm_num) ({331, 1327} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_insert, Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem tmass_89 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 89 ^ j) :
    (1 + 1 / (((89 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 311 / 300 :=
  zmass_two (X := 10000) (K := 7) (by norm_num) (by norm_num) (by norm_num) ({1423} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem tmass_97 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 97 ^ j) :
    (1 + 1 / (((97 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 311 / 300 :=
  zmass_two (X := 10000) (K := 7) (by norm_num) (by norm_num) (by norm_num) ({193} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem tmass_101 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 101 ^ j) :
    (1 + 1 / (((101 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 311 / 300 :=
  zmass_two (X := 10000) (K := 7) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem tmass_103 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 103 ^ j) :
    (1 + 1 / (((103 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 311 / 300 :=
  zmass_two (X := 10000) (K := 7) (by norm_num) (by norm_num) (by norm_num) ({823} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem tmass_107 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 107 ^ j) :
    (1 + 1 / (((107 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 311 / 300 :=
  zmass_two (X := 10000) (K := 7) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem tmass_109 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 109 ^ j) :
    (1 + 1 / (((109 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 311 / 300 :=
  zmass_two (X := 10000) (K := 7) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem tmass_113 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 113 ^ j) :
    (1 + 1 / (((113 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 311 / 300 :=
  zmass_two (X := 10000) (K := 7) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem tmass_127 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 127 ^ j) :
    (1 + 1 / (((127 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 311 / 300 :=
  zmass_two (X := 10000) (K := 7) (by norm_num) (by norm_num) (by norm_num) (∅ : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp at hq)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem tmass_131 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 131 ^ j) :
    (1 + 1 / (((131 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 311 / 300 :=
  zmass_two (X := 10000) (K := 7) (by norm_num) (by norm_num) (by norm_num) ({523} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem tmass_137 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 137 ^ j) :
    (1 + 1 / (((137 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 311 / 300 :=
  zmass_two (X := 10000) (K := 7) (by norm_num) (by norm_num) (by norm_num) ({547} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem tmass_139 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 139 ^ j) :
    (1 + 1 / (((139 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 311 / 300 :=
  zmass_two (X := 10000) (K := 7) (by norm_num) (by norm_num) (by norm_num) ({277, 4447} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_insert, Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem tmass_157 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 157 ^ j) :
    (1 + 1 / (((157 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 311 / 300 :=
  zmass_two (X := 10000) (K := 6) (by norm_num) (by norm_num) (by norm_num) ({313, 5023} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_insert, Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem tmass_173 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 173 ^ j) :
    (1 + 1 / (((173 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 311 / 300 :=
  zmass_two (X := 10000) (K := 6) (by norm_num) (by norm_num) (by norm_num) ({691, 2767} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_insert, Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem tmass_197 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 197 ^ j) :
    (1 + 1 / (((197 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 311 / 300 :=
  zmass_two (X := 10000) (K := 6) (by norm_num) (by norm_num) (by norm_num) ({787} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem tmass_199 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 199 ^ j) :
    (1 + 1 / (((199 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 311 / 300 :=
  zmass_two (X := 10000) (K := 6) (by norm_num) (by norm_num) (by norm_num) ({397, 6367} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_insert, Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem tmass_211 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 211 ^ j) :
    (1 + 1 / (((211 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 311 / 300 :=
  zmass_two (X := 10000) (K := 6) (by norm_num) (by norm_num) (by norm_num) ({421} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem tmass_227 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 227 ^ j) :
    (1 + 1 / (((227 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 311 / 300 :=
  zmass_two (X := 10000) (K := 6) (by norm_num) (by norm_num) (by norm_num) ({907, 3631} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_insert, Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem tmass_229 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 229 ^ j) :
    (1 + 1 / (((229 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 311 / 300 :=
  zmass_two (X := 10000) (K := 6) (by norm_num) (by norm_num) (by norm_num) ({457, 1831} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_insert, Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem tmass_263 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 263 ^ j) :
    (1 + 1 / (((263 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 311 / 300 :=
  zmass_two (X := 10000) (K := 6) (by norm_num) (by norm_num) (by norm_num) ({1051} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem tmass_271 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 271 ^ j) :
    (1 + 1 / (((271 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 311 / 300 :=
  zmass_two (X := 10000) (K := 6) (by norm_num) (by norm_num) (by norm_num) ({541} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem tmass_307 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 307 ^ j) :
    (1 + 1 / (((307 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 311 / 300 :=
  zmass_two (X := 10000) (K := 6) (by norm_num) (by norm_num) (by norm_num) ({613} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem tmass_331 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 331 ^ j) :
    (1 + 1 / (((331 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 311 / 300 :=
  zmass_two (X := 10000) (K := 5) (by norm_num) (by norm_num) (by norm_num) ({661, 2647} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_insert, Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem tmass_337 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 337 ^ j) :
    (1 + 1 / (((337 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 311 / 300 :=
  zmass_two (X := 10000) (K := 5) (by norm_num) (by norm_num) (by norm_num) ({673} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem tmass_367 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 367 ^ j) :
    (1 + 1 / (((367 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 311 / 300 :=
  zmass_two (X := 10000) (K := 5) (by norm_num) (by norm_num) (by norm_num) ({733} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem tmass_379 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 379 ^ j) :
    (1 + 1 / (((379 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 311 / 300 :=
  zmass_two (X := 10000) (K := 5) (by norm_num) (by norm_num) (by norm_num) ({757} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem tmass_439 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 439 ^ j) :
    (1 + 1 / (((439 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 311 / 300 :=
  zmass_two (X := 10000) (K := 5) (by norm_num) (by norm_num) (by norm_num) ({877, 3511} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_insert, Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem tmass_499 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 499 ^ j) :
    (1 + 1 / (((499 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 311 / 300 :=
  zmass_two (X := 10000) (K := 5) (by norm_num) (by norm_num) (by norm_num) ({997} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

theorem tmass_619 (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 619 ^ j) :
    (1 + 1 / (((619 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 311 / 300 :=
  zmass_two (X := 10000) (K := 5) (by norm_num) (by norm_num) (by norm_num) ({1237, 4951} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_insert, Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

-- Section 6.  The case split over the 314 primes 7 <= z < 2100.

theorem three_all {n z : ℕ} (h : Erdos1052.IsUnitaryPerfect n)
    (hz : z ∈ ({13, 23, 29, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 157, 173, 197, 199, 211, 227, 229, 263, 271, 307, 331, 337, 367, 379, 439, 499, 619} : Finset ℕ))
    (hS : ∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = z)
    (hres : 3 ∣ 2 ^ padicValNat 2 n + 1 ∨ 3 ∣ 1 + z ^ n.factorization z) :
    padicValNat 2 n ≤ 9 := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact le_nine_three_top h (by norm_num) (by norm_num) hS tmass_13 hres
  · exact le_nine_three_top h (by norm_num) (by norm_num) hS tmass_23 hres
  · exact le_nine_three_top h (by norm_num) (by norm_num) hS tmass_29 hres
  · exact le_nine_three_top h (by norm_num) (by norm_num) hS tmass_37 hres
  · exact le_nine_three_top h (by norm_num) (by norm_num) hS tmass_41 hres
  · exact le_nine_three_top h (by norm_num) (by norm_num) hS tmass_43 hres
  · exact le_nine_three_top h (by norm_num) (by norm_num) hS tmass_47 hres
  · exact le_nine_three_top h (by norm_num) (by norm_num) hS tmass_53 hres
  · exact le_nine_three_top h (by norm_num) (by norm_num) hS tmass_59 hres
  · exact le_nine_three_top h (by norm_num) (by norm_num) hS tmass_61 hres
  · exact le_nine_three_top h (by norm_num) (by norm_num) hS tmass_67 hres
  · exact le_nine_three_top h (by norm_num) (by norm_num) hS tmass_71 hres
  · exact le_nine_three_top h (by norm_num) (by norm_num) hS tmass_73 hres
  · exact le_nine_three_top h (by norm_num) (by norm_num) hS tmass_79 hres
  · exact le_nine_three_top h (by norm_num) (by norm_num) hS tmass_83 hres
  · exact le_nine_three_top h (by norm_num) (by norm_num) hS tmass_89 hres
  · exact le_nine_three_top h (by norm_num) (by norm_num) hS tmass_97 hres
  · exact le_nine_three_top h (by norm_num) (by norm_num) hS tmass_101 hres
  · exact le_nine_three_top h (by norm_num) (by norm_num) hS tmass_103 hres
  · exact le_nine_three_top h (by norm_num) (by norm_num) hS tmass_107 hres
  · exact le_nine_three_top h (by norm_num) (by norm_num) hS tmass_109 hres
  · exact le_nine_three_top h (by norm_num) (by norm_num) hS tmass_113 hres
  · exact le_nine_three_top h (by norm_num) (by norm_num) hS tmass_127 hres
  · exact le_nine_three_top h (by norm_num) (by norm_num) hS tmass_131 hres
  · exact le_nine_three_top h (by norm_num) (by norm_num) hS tmass_137 hres
  · exact le_nine_three_top h (by norm_num) (by norm_num) hS tmass_139 hres
  · exact le_nine_three_top h (by norm_num) (by norm_num) hS tmass_157 hres
  · exact le_nine_three_top h (by norm_num) (by norm_num) hS tmass_173 hres
  · exact le_nine_three_top h (by norm_num) (by norm_num) hS tmass_197 hres
  · exact le_nine_three_top h (by norm_num) (by norm_num) hS tmass_199 hres
  · exact le_nine_three_top h (by norm_num) (by norm_num) hS tmass_211 hres
  · exact le_nine_three_top h (by norm_num) (by norm_num) hS tmass_227 hres
  · exact le_nine_three_top h (by norm_num) (by norm_num) hS tmass_229 hres
  · exact le_nine_three_top h (by norm_num) (by norm_num) hS tmass_263 hres
  · exact le_nine_three_top h (by norm_num) (by norm_num) hS tmass_271 hres
  · exact le_nine_three_top h (by norm_num) (by norm_num) hS tmass_307 hres
  · exact le_nine_three_top h (by norm_num) (by norm_num) hS tmass_331 hres
  · exact le_nine_three_top h (by norm_num) (by norm_num) hS tmass_337 hres
  · exact le_nine_three_top h (by norm_num) (by norm_num) hS tmass_367 hres
  · exact le_nine_three_top h (by norm_num) (by norm_num) hS tmass_379 hres
  · exact le_nine_three_top h (by norm_num) (by norm_num) hS tmass_439 hres
  · exact le_nine_three_top h (by norm_num) (by norm_num) hS tmass_499 hres
  · exact le_nine_three_top h (by norm_num) (by norm_num) hS tmass_619 hres

theorem ne_of_mem {z : ℕ} (hz : z ∈ ({13, 23, 29, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 157, 173, 197, 199, 211, 227, 229, 263, 271, 307, 331, 337, 367, 379, 439, 499, 619} : Finset ℕ)) :
    z ≠ 11 ∧ z ≠ 17 ∧ z ≠ 257 ∧ z ≠ 743 := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hz
  omega

theorem mem_T {z : ℕ}
    (hz : z = 13 ∨ z = 23 ∨ z = 29 ∨ z = 37 ∨ z = 41 ∨ z = 43 ∨ z = 47 ∨ z = 53 ∨ z = 59 ∨ z = 61 ∨ 
      z = 67 ∨ z = 71 ∨ z = 73 ∨ z = 79 ∨ z = 83 ∨ z = 89 ∨ z = 97 ∨ z = 101 ∨ z = 103 ∨ 
      z = 107 ∨ z = 109 ∨ z = 113 ∨ z = 127 ∨ z = 131 ∨ z = 137 ∨ z = 139 ∨ z = 157 ∨ z = 173 ∨ 
      z = 197 ∨ z = 199 ∨ z = 211 ∨ z = 227 ∨ z = 229 ∨ z = 263 ∨ z = 271 ∨ z = 307 ∨ z = 331 ∨ 
      z = 337 ∨ z = 367 ∨ z = 379 ∨ z = 439 ∨ z = 499 ∨ z = 619) :
    z ∈ ({13, 23, 29, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 157, 173, 197, 199, 211, 227, 229, 263, 271, 307, 331, 337, 367, 379, 439, 499, 619} : Finset ℕ) := by
  simp only [Finset.mem_insert, Finset.mem_singleton]
  exact hz

theorem mem_S {z : ℕ} (hz : z = 7 ∨ z = 11 ∨ z = 17 ∨ z = 19 ∨ z = 31) :
    z ∈ ({7, 11, 17, 19, 31} : Finset ℕ) := by
  simp only [Finset.mem_insert, Finset.mem_singleton]
  exact hz

set_option maxHeartbeats 4000000 in
theorem pr_1 {z : ℕ} (hz : z.Prime) (hlo : 7 ≤ z) (hhi : z < 151) :
    z = 7 ∨ z = 11 ∨ z = 13 ∨ z = 17 ∨ z = 19 ∨ z = 23 ∨ z = 29 ∨ z = 31 ∨ z = 37 ∨ z = 41 ∨ 
    z = 43 ∨ z = 47 ∨ z = 53 ∨ z = 59 ∨ z = 61 ∨ z = 67 ∨ z = 71 ∨ z = 73 ∨ z = 79 ∨ z = 83 ∨ 
    z = 89 ∨ z = 97 ∨ z = 101 ∨ z = 103 ∨ z = 107 ∨ z = 109 ∨ z = 113 ∨ z = 127 ∨ z = 131 ∨ 
    z = 137 ∨ z = 139 ∨ z = 149 := by
  interval_cases z <;> first | (norm_num at hz; done) | simp

set_option maxHeartbeats 1000000 in
theorem step_1 {n z : ℕ} (h : Erdos1052.IsUnitaryPerfect n)
    (hz : z = 7 ∨ z = 11 ∨ z = 13 ∨ z = 17 ∨ z = 19 ∨ z = 23 ∨ z = 29 ∨ z = 31 ∨ z = 37 ∨ z = 41 ∨ 
      z = 43 ∨ z = 47 ∨ z = 53 ∨ z = 59 ∨ z = 61 ∨ z = 67 ∨ z = 71 ∨ z = 73 ∨ z = 79 ∨ z = 83 ∨ 
      z = 89 ∨ z = 97 ∨ z = 101 ∨ z = 103 ∨ z = 107 ∨ z = 109 ∨ z = 113 ∨ z = 127 ∨ z = 131 ∨ 
      z = 137 ∨ z = 139 ∨ z = 149)
    (hS : ∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = z)
    (d9 : z ≠ 17 → padicValNat 2 n % 8 ≠ 4)
    (d10 : z ≠ 11 → z ≠ 43 → z ≠ 257 → padicValNat 2 n % 16 ≠ 8) :
    padicValNat 2 n ≤ 9 ∨ (z = 257 ∧ padicValNat 2 n % 16 = 8 ∧ Even (n.factorization z)) ∨
      z ∈ ({13, 23, 29, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 157, 173, 197, 199, 211, 227, 229, 263, 271, 307, 331, 337, 367, 379, 439, 499, 619} : Finset ℕ) ∨
      z ∈ ({7, 11, 17, 19, 31} : Finset ℕ) := by
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inr (Or.inr (Or.inr (mem_S (by omega))))
  · exact Or.inr (Or.inr (Or.inr (mem_S (by omega))))
  · exact Or.inr (Or.inr (Or.inl (mem_T (by omega))))
  · exact Or.inr (Or.inr (Or.inr (mem_S (by omega))))
  · exact Or.inr (Or.inr (Or.inr (mem_S (by omega))))
  · exact Or.inr (Or.inr (Or.inl (mem_T (by omega))))
  · exact Or.inr (Or.inr (Or.inl (mem_T (by omega))))
  · exact Or.inr (Or.inr (Or.inr (mem_S (by omega))))
  · exact Or.inr (Or.inr (Or.inl (mem_T (by omega))))
  · exact Or.inr (Or.inr (Or.inl (mem_T (by omega))))
  · exact Or.inr (Or.inr (Or.inl (mem_T (by omega))))
  · exact Or.inr (Or.inr (Or.inl (mem_T (by omega))))
  · exact Or.inr (Or.inr (Or.inl (mem_T (by omega))))
  · exact Or.inr (Or.inr (Or.inl (mem_T (by omega))))
  · exact Or.inr (Or.inr (Or.inl (mem_T (by omega))))
  · exact Or.inr (Or.inr (Or.inl (mem_T (by omega))))
  · exact Or.inr (Or.inr (Or.inl (mem_T (by omega))))
  · exact Or.inr (Or.inr (Or.inl (mem_T (by omega))))
  · exact Or.inr (Or.inr (Or.inl (mem_T (by omega))))
  · exact Or.inr (Or.inr (Or.inl (mem_T (by omega))))
  · exact Or.inr (Or.inr (Or.inl (mem_T (by omega))))
  · exact Or.inr (Or.inr (Or.inl (mem_T (by omega))))
  · exact Or.inr (Or.inr (Or.inl (mem_T (by omega))))
  · exact Or.inr (Or.inr (Or.inl (mem_T (by omega))))
  · exact Or.inr (Or.inr (Or.inl (mem_T (by omega))))
  · exact Or.inr (Or.inr (Or.inl (mem_T (by omega))))
  · exact Or.inr (Or.inr (Or.inl (mem_T (by omega))))
  · exact Or.inr (Or.inr (Or.inl (mem_T (by omega))))
  · exact Or.inr (Or.inr (Or.inl (mem_T (by omega))))
  · exact Or.inr (Or.inr (Or.inl (mem_T (by omega))))
  · exact Or.inr (Or.inr (Or.inl (mem_T (by omega))))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_149
      (fun h4 hd _ => absurd hd (nf_149 h4)))

set_option maxHeartbeats 4000000 in
theorem pr_2 {z : ℕ} (hz : z.Prime) (hlo : 151 ≤ z) (hhi : z < 337) :
    z = 151 ∨ z = 157 ∨ z = 163 ∨ z = 167 ∨ z = 173 ∨ z = 179 ∨ z = 181 ∨ z = 191 ∨ z = 193 ∨ 
    z = 197 ∨ z = 199 ∨ z = 211 ∨ z = 223 ∨ z = 227 ∨ z = 229 ∨ z = 233 ∨ z = 239 ∨ z = 241 ∨ 
    z = 251 ∨ z = 257 ∨ z = 263 ∨ z = 269 ∨ z = 271 ∨ z = 277 ∨ z = 281 ∨ z = 283 ∨ z = 293 ∨ 
    z = 307 ∨ z = 311 ∨ z = 313 ∨ z = 317 ∨ z = 331 := by
  interval_cases z <;> first | (norm_num at hz; done) | simp

set_option maxHeartbeats 1000000 in
theorem step_2 {n z : ℕ} (h : Erdos1052.IsUnitaryPerfect n)
    (hz : z = 151 ∨ z = 157 ∨ z = 163 ∨ z = 167 ∨ z = 173 ∨ z = 179 ∨ z = 181 ∨ z = 191 ∨ z = 193 ∨ 
      z = 197 ∨ z = 199 ∨ z = 211 ∨ z = 223 ∨ z = 227 ∨ z = 229 ∨ z = 233 ∨ z = 239 ∨ z = 241 ∨ 
      z = 251 ∨ z = 257 ∨ z = 263 ∨ z = 269 ∨ z = 271 ∨ z = 277 ∨ z = 281 ∨ z = 283 ∨ z = 293 ∨ 
      z = 307 ∨ z = 311 ∨ z = 313 ∨ z = 317 ∨ z = 331)
    (hS : ∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = z)
    (d9 : z ≠ 17 → padicValNat 2 n % 8 ≠ 4)
    (d10 : z ≠ 11 → z ≠ 43 → z ≠ 257 → padicValNat 2 n % 16 ≠ 8) :
    padicValNat 2 n ≤ 9 ∨ (z = 257 ∧ padicValNat 2 n % 16 = 8 ∧ Even (n.factorization z)) ∨
      z ∈ ({13, 23, 29, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 157, 173, 197, 199, 211, 227, 229, 263, 271, 307, 331, 337, 367, 379, 439, 499, 619} : Finset ℕ) ∨
      z ∈ ({7, 11, 17, 19, 31} : Finset ℕ) := by
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_151
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inr (Or.inr (Or.inl (mem_T (by omega))))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_163
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_167
      (fun h4 hd _ => absurd hd (nf_167 h4)))
  · exact Or.inr (Or.inr (Or.inl (mem_T (by omega))))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_179
      (fun h4 hd _ => absurd hd (nf_179 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_181
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_191
      (fun h4 hd _ => absurd hd (nf_191 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_193
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inr (Or.inr (Or.inl (mem_T (by omega))))
  · exact Or.inr (Or.inr (Or.inl (mem_T (by omega))))
  · exact Or.inr (Or.inr (Or.inl (mem_T (by omega))))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_223
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inr (Or.inr (Or.inl (mem_T (by omega))))
  · exact Or.inr (Or.inr (Or.inl (mem_T (by omega))))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_233
      (fun h4 hd _ => absurd hd (nf_233 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_239
      (fun h4 hd _ => absurd hd (nf_239 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_241
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_251
      (fun h4 hd _ => absurd hd (nf_251 h4)))
  · by_cases hev : Even (n.factorization 257)
    · by_cases hd : 257 ∣ 2 ^ padicValNat 2 n + 1
      · exact Or.inr (Or.inl ⟨rfl, rs_257 hd, hev⟩)
      · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_257
          (fun _ hd' _ => absurd hd' hd))
    · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_257
        (fun _ _ _ => Nat.not_even_iff_odd.mp hev))
  · exact Or.inr (Or.inr (Or.inl (mem_T (by omega))))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_269
      (fun h4 hd _ => absurd hd (nf_269 h4)))
  · exact Or.inr (Or.inr (Or.inl (mem_T (by omega))))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_277
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_281
      (fun h4 hd _ => absurd hd (nf_281 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_283
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_293
      (fun h4 hd _ => absurd hd (nf_293 h4)))
  · exact Or.inr (Or.inr (Or.inl (mem_T (by omega))))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_311
      (fun h4 hd _ => absurd hd (nf_311 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_313
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_317
      (fun h4 hd _ => absurd hd (nf_317 h4)))
  · exact Or.inr (Or.inr (Or.inl (mem_T (by omega))))

set_option maxHeartbeats 4000000 in
theorem pr_3 {z : ℕ} (hz : z.Prime) (hlo : 337 ≤ z) (hhi : z < 541) :
    z = 337 ∨ z = 347 ∨ z = 349 ∨ z = 353 ∨ z = 359 ∨ z = 367 ∨ z = 373 ∨ z = 379 ∨ z = 383 ∨ 
    z = 389 ∨ z = 397 ∨ z = 401 ∨ z = 409 ∨ z = 419 ∨ z = 421 ∨ z = 431 ∨ z = 433 ∨ z = 439 ∨ 
    z = 443 ∨ z = 449 ∨ z = 457 ∨ z = 461 ∨ z = 463 ∨ z = 467 ∨ z = 479 ∨ z = 487 ∨ z = 491 ∨ 
    z = 499 ∨ z = 503 ∨ z = 509 ∨ z = 521 ∨ z = 523 := by
  interval_cases z <;> first | (norm_num at hz; done) | simp

set_option maxHeartbeats 1000000 in
theorem step_3 {n z : ℕ} (h : Erdos1052.IsUnitaryPerfect n)
    (hz : z = 337 ∨ z = 347 ∨ z = 349 ∨ z = 353 ∨ z = 359 ∨ z = 367 ∨ z = 373 ∨ z = 379 ∨ z = 383 ∨ 
      z = 389 ∨ z = 397 ∨ z = 401 ∨ z = 409 ∨ z = 419 ∨ z = 421 ∨ z = 431 ∨ z = 433 ∨ z = 439 ∨ 
      z = 443 ∨ z = 449 ∨ z = 457 ∨ z = 461 ∨ z = 463 ∨ z = 467 ∨ z = 479 ∨ z = 487 ∨ z = 491 ∨ 
      z = 499 ∨ z = 503 ∨ z = 509 ∨ z = 521 ∨ z = 523)
    (hS : ∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = z)
    (d9 : z ≠ 17 → padicValNat 2 n % 8 ≠ 4)
    (d10 : z ≠ 11 → z ≠ 43 → z ≠ 257 → padicValNat 2 n % 16 ≠ 8)
    (c4 : padicValNat 2 n % 32 ≠ 16) :
    padicValNat 2 n ≤ 9 ∨ (z = 257 ∧ padicValNat 2 n % 16 = 8 ∧ Even (n.factorization z)) ∨
      z ∈ ({13, 23, 29, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 157, 173, 197, 199, 211, 227, 229, 263, 271, 307, 331, 337, 367, 379, 439, 499, 619} : Finset ℕ) ∨
      z ∈ ({7, 11, 17, 19, 31} : Finset ℕ) := by
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inr (Or.inr (Or.inl (mem_T (by omega))))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_347
      (fun h4 hd _ => absurd hd (nf_347 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_349
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_353
      (fun _ hd _ => absurd (rs_353 hd) (d9 (by norm_num))))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_359
      (fun h4 hd _ => absurd hd (nf_359 h4)))
  · exact Or.inr (Or.inr (Or.inl (mem_T (by omega))))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_373
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inr (Or.inr (Or.inl (mem_T (by omega))))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_383
      (fun h4 hd _ => absurd hd (nf_383 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_389
      (fun h4 hd _ => absurd hd (nf_389 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_397
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_401
      (fun _ hd _ => absurd (rs_401 hd) (d9 (by norm_num))))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_409
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_419
      (fun h4 hd _ => absurd hd (nf_419 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_421
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_431
      (fun h4 hd _ => absurd hd (nf_431 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_433
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inr (Or.inr (Or.inl (mem_T (by omega))))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_443
      (fun h4 hd _ => absurd hd (nf_443 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_449
      (fun _ hd _ => absurd (rs_449 hd) c4))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_457
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_461
      (fun h4 hd _ => absurd hd (nf_461 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_463
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_467
      (fun h4 hd _ => absurd hd (nf_467 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_479
      (fun h4 hd _ => absurd hd (nf_479 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_487
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_491
      (fun h4 hd _ => absurd hd (nf_491 h4)))
  · exact Or.inr (Or.inr (Or.inl (mem_T (by omega))))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_503
      (fun h4 hd _ => absurd hd (nf_503 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_509
      (fun h4 hd _ => absurd hd (nf_509 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_521
      (fun h4 hd _ => absurd hd (nf_521 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_523
      (fun _ _ h3 => absurd h3 (by norm_num)))

set_option maxHeartbeats 4000000 in
theorem pr_4 {z : ℕ} (hz : z.Prime) (hlo : 541 ≤ z) (hhi : z < 743) :
    z = 541 ∨ z = 547 ∨ z = 557 ∨ z = 563 ∨ z = 569 ∨ z = 571 ∨ z = 577 ∨ z = 587 ∨ z = 593 ∨ 
    z = 599 ∨ z = 601 ∨ z = 607 ∨ z = 613 ∨ z = 617 ∨ z = 619 ∨ z = 631 ∨ z = 641 ∨ z = 643 ∨ 
    z = 647 ∨ z = 653 ∨ z = 659 ∨ z = 661 ∨ z = 673 ∨ z = 677 ∨ z = 683 ∨ z = 691 ∨ z = 701 ∨ 
    z = 709 ∨ z = 719 ∨ z = 727 ∨ z = 733 ∨ z = 739 := by
  interval_cases z <;> first | (norm_num at hz; done) | simp

set_option maxHeartbeats 1000000 in
theorem step_4 {n z : ℕ} (h : Erdos1052.IsUnitaryPerfect n)
    (hz : z = 541 ∨ z = 547 ∨ z = 557 ∨ z = 563 ∨ z = 569 ∨ z = 571 ∨ z = 577 ∨ z = 587 ∨ z = 593 ∨ 
      z = 599 ∨ z = 601 ∨ z = 607 ∨ z = 613 ∨ z = 617 ∨ z = 619 ∨ z = 631 ∨ z = 641 ∨ z = 643 ∨ 
      z = 647 ∨ z = 653 ∨ z = 659 ∨ z = 661 ∨ z = 673 ∨ z = 677 ∨ z = 683 ∨ z = 691 ∨ z = 701 ∨ 
      z = 709 ∨ z = 719 ∨ z = 727 ∨ z = 733 ∨ z = 739)
    (hS : ∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = z)
    (d9 : z ≠ 17 → padicValNat 2 n % 8 ≠ 4)
    (d10 : z ≠ 11 → z ≠ 43 → z ≠ 257 → padicValNat 2 n % 16 ≠ 8)
    (c5 : padicValNat 2 n % 64 ≠ 32) :
    padicValNat 2 n ≤ 9 ∨ (z = 257 ∧ padicValNat 2 n % 16 = 8 ∧ Even (n.factorization z)) ∨
      z ∈ ({13, 23, 29, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 157, 173, 197, 199, 211, 227, 229, 263, 271, 307, 331, 337, 367, 379, 439, 499, 619} : Finset ℕ) ∨
      z ∈ ({7, 11, 17, 19, 31} : Finset ℕ) := by
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_541
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_547
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_557
      (fun h4 hd _ => absurd hd (nf_557 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_563
      (fun h4 hd _ => absurd hd (nf_563 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_569
      (fun h4 hd _ => absurd hd (nf_569 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_571
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_577
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_587
      (fun h4 hd _ => absurd hd (nf_587 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_593
      (fun h4 hd _ => absurd hd (nf_593 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_599
      (fun h4 hd _ => absurd hd (nf_599 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_601
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_607
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_613
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_617
      (fun h4 hd _ => absurd hd (nf_617 h4)))
  · exact Or.inr (Or.inr (Or.inl (mem_T (by omega))))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_631
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_641
      (fun _ hd _ => absurd (rs_641 hd) c5))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_643
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_647
      (fun h4 hd _ => absurd hd (nf_647 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_653
      (fun h4 hd _ => absurd hd (nf_653 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_659
      (fun h4 hd _ => absurd hd (nf_659 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_661
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_673
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_677
      (fun h4 hd _ => absurd hd (nf_677 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_683
      (fun h4 hd _ => absurd hd (nf_683 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_691
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_701
      (fun h4 hd _ => absurd hd (nf_701 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_709
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_719
      (fun h4 hd _ => absurd hd (nf_719 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_727
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_733
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_739
      (fun _ _ h3 => absurd h3 (by norm_num)))

set_option maxHeartbeats 4000000 in
theorem pr_5 {z : ℕ} (hz : z.Prime) (hlo : 743 ≤ z) (hhi : z < 971) :
    z = 743 ∨ z = 751 ∨ z = 757 ∨ z = 761 ∨ z = 769 ∨ z = 773 ∨ z = 787 ∨ z = 797 ∨ z = 809 ∨ 
    z = 811 ∨ z = 821 ∨ z = 823 ∨ z = 827 ∨ z = 829 ∨ z = 839 ∨ z = 853 ∨ z = 857 ∨ z = 859 ∨ 
    z = 863 ∨ z = 877 ∨ z = 881 ∨ z = 883 ∨ z = 887 ∨ z = 907 ∨ z = 911 ∨ z = 919 ∨ z = 929 ∨ 
    z = 937 ∨ z = 941 ∨ z = 947 ∨ z = 953 ∨ z = 967 := by
  interval_cases z <;> first | (norm_num at hz; done) | simp

set_option maxHeartbeats 1000000 in
theorem step_5 {n z : ℕ} (h : Erdos1052.IsUnitaryPerfect n)
    (hz : z = 743 ∨ z = 751 ∨ z = 757 ∨ z = 761 ∨ z = 769 ∨ z = 773 ∨ z = 787 ∨ z = 797 ∨ z = 809 ∨ 
      z = 811 ∨ z = 821 ∨ z = 823 ∨ z = 827 ∨ z = 829 ∨ z = 839 ∨ z = 853 ∨ z = 857 ∨ z = 859 ∨ 
      z = 863 ∨ z = 877 ∨ z = 881 ∨ z = 883 ∨ z = 887 ∨ z = 907 ∨ z = 911 ∨ z = 919 ∨ z = 929 ∨ 
      z = 937 ∨ z = 941 ∨ z = 947 ∨ z = 953 ∨ z = 967)
    (hS : ∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = z)
    (d9 : z ≠ 17 → padicValNat 2 n % 8 ≠ 4)
    (d10 : z ≠ 11 → z ≠ 43 → z ≠ 257 → padicValNat 2 n % 16 ≠ 8) :
    padicValNat 2 n ≤ 9 ∨ (z = 257 ∧ padicValNat 2 n % 16 = 8 ∧ Even (n.factorization z)) ∨
      z ∈ ({13, 23, 29, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 157, 173, 197, 199, 211, 227, 229, 263, 271, 307, 331, 337, 367, 379, 439, 499, 619} : Finset ℕ) ∨
      z ∈ ({7, 11, 17, 19, 31} : Finset ℕ) := by
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_743
      (fun h4 hd _ => absurd hd (nf_743 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_751
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_757
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_761
      (fun h4 hd _ => absurd hd (nf_761 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_769
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_773
      (fun h4 hd _ => absurd hd (nf_773 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_787
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_797
      (fun h4 hd _ => absurd hd (nf_797 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_809
      (fun h4 hd _ => absurd hd (nf_809 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_811
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_821
      (fun h4 hd _ => absurd hd (nf_821 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_823
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_827
      (fun h4 hd _ => absurd hd (nf_827 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_829
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_839
      (fun h4 hd _ => absurd hd (nf_839 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_853
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_857
      (fun h4 hd _ => absurd hd (nf_857 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_859
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_863
      (fun h4 hd _ => absurd hd (nf_863 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_877
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_881
      (fun h4 hd _ => absurd hd (nf_881 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_883
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_887
      (fun h4 hd _ => absurd hd (nf_887 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_907
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_911
      (fun h4 hd _ => absurd hd (nf_911 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_919
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_929
      (fun _ hd _ => absurd (rs_929 hd) (d10 (by norm_num) (by norm_num) (by norm_num))))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_937
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_941
      (fun h4 hd _ => absurd hd (nf_941 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_947
      (fun h4 hd _ => absurd hd (nf_947 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_953
      (fun h4 hd _ => absurd hd (nf_953 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_967
      (fun _ _ h3 => absurd h3 (by norm_num)))

set_option maxHeartbeats 4000000 in
theorem pr_6 {z : ℕ} (hz : z.Prime) (hlo : 971 ≤ z) (hhi : z < 1193) :
    z = 971 ∨ z = 977 ∨ z = 983 ∨ z = 991 ∨ z = 997 ∨ z = 1009 ∨ z = 1013 ∨ z = 1019 ∨ z = 1021 ∨ 
    z = 1031 ∨ z = 1033 ∨ z = 1039 ∨ z = 1049 ∨ z = 1051 ∨ z = 1061 ∨ z = 1063 ∨ z = 1069 ∨ 
    z = 1087 ∨ z = 1091 ∨ z = 1093 ∨ z = 1097 ∨ z = 1103 ∨ z = 1109 ∨ z = 1117 ∨ z = 1123 ∨ 
    z = 1129 ∨ z = 1151 ∨ z = 1153 ∨ z = 1163 ∨ z = 1171 ∨ z = 1181 ∨ z = 1187 := by
  interval_cases z <;> first | (norm_num at hz; done) | simp

set_option maxHeartbeats 1000000 in
theorem step_6 {n z : ℕ} (h : Erdos1052.IsUnitaryPerfect n)
    (hz : z = 971 ∨ z = 977 ∨ z = 983 ∨ z = 991 ∨ z = 997 ∨ z = 1009 ∨ z = 1013 ∨ z = 1019 ∨ 
      z = 1021 ∨ z = 1031 ∨ z = 1033 ∨ z = 1039 ∨ z = 1049 ∨ z = 1051 ∨ z = 1061 ∨ z = 1063 ∨ 
      z = 1069 ∨ z = 1087 ∨ z = 1091 ∨ z = 1093 ∨ z = 1097 ∨ z = 1103 ∨ z = 1109 ∨ z = 1117 ∨ 
      z = 1123 ∨ z = 1129 ∨ z = 1151 ∨ z = 1153 ∨ z = 1163 ∨ z = 1171 ∨ z = 1181 ∨ z = 1187)
    (hS : ∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = z)
    (d9 : z ≠ 17 → padicValNat 2 n % 8 ≠ 4)
    (d10 : z ≠ 11 → z ≠ 43 → z ≠ 257 → padicValNat 2 n % 16 ≠ 8) :
    padicValNat 2 n ≤ 9 ∨ (z = 257 ∧ padicValNat 2 n % 16 = 8 ∧ Even (n.factorization z)) ∨
      z ∈ ({13, 23, 29, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 157, 173, 197, 199, 211, 227, 229, 263, 271, 307, 331, 337, 367, 379, 439, 499, 619} : Finset ℕ) ∨
      z ∈ ({7, 11, 17, 19, 31} : Finset ℕ) := by
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_971
      (fun h4 hd _ => absurd hd (nf_971 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_977
      (fun _ hd _ => absurd (rs_977 hd) (d9 (by norm_num))))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_983
      (fun h4 hd _ => absurd hd (nf_983 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_991
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_997
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1009
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1013
      (fun h4 hd _ => absurd hd (nf_1013 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1019
      (fun h4 hd _ => absurd hd (nf_1019 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1021
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1031
      (fun h4 hd _ => absurd hd (nf_1031 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1033
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1039
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1049
      (fun h4 hd _ => absurd hd (nf_1049 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1051
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1061
      (fun h4 hd _ => absurd hd (nf_1061 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1063
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1069
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1087
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1091
      (fun h4 hd _ => absurd hd (nf_1091 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1093
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1097
      (fun h4 hd _ => absurd hd (nf_1097 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1103
      (fun h4 hd _ => absurd hd (nf_1103 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1109
      (fun h4 hd _ => absurd hd (nf_1109 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1117
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1123
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1129
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1151
      (fun h4 hd _ => absurd hd (nf_1151 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1153
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1163
      (fun h4 hd _ => absurd hd (nf_1163 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1171
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1181
      (fun h4 hd _ => absurd hd (nf_1181 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1187
      (fun h4 hd _ => absurd hd (nf_1187 h4)))

set_option maxHeartbeats 4000000 in
theorem pr_7 {z : ℕ} (hz : z.Prime) (hlo : 1193 ≤ z) (hhi : z < 1439) :
    z = 1193 ∨ z = 1201 ∨ z = 1213 ∨ z = 1217 ∨ z = 1223 ∨ z = 1229 ∨ z = 1231 ∨ z = 1237 ∨ 
    z = 1249 ∨ z = 1259 ∨ z = 1277 ∨ z = 1279 ∨ z = 1283 ∨ z = 1289 ∨ z = 1291 ∨ z = 1297 ∨ 
    z = 1301 ∨ z = 1303 ∨ z = 1307 ∨ z = 1319 ∨ z = 1321 ∨ z = 1327 ∨ z = 1361 ∨ z = 1367 ∨ 
    z = 1373 ∨ z = 1381 ∨ z = 1399 ∨ z = 1409 ∨ z = 1423 ∨ z = 1427 ∨ z = 1429 ∨ z = 1433 := by
  interval_cases z <;> first | (norm_num at hz; done) | simp

set_option maxHeartbeats 1000000 in
theorem step_7 {n z : ℕ} (h : Erdos1052.IsUnitaryPerfect n)
    (hz : z = 1193 ∨ z = 1201 ∨ z = 1213 ∨ z = 1217 ∨ z = 1223 ∨ z = 1229 ∨ z = 1231 ∨ z = 1237 ∨ 
      z = 1249 ∨ z = 1259 ∨ z = 1277 ∨ z = 1279 ∨ z = 1283 ∨ z = 1289 ∨ z = 1291 ∨ z = 1297 ∨ 
      z = 1301 ∨ z = 1303 ∨ z = 1307 ∨ z = 1319 ∨ z = 1321 ∨ z = 1327 ∨ z = 1361 ∨ z = 1367 ∨ 
      z = 1373 ∨ z = 1381 ∨ z = 1399 ∨ z = 1409 ∨ z = 1423 ∨ z = 1427 ∨ z = 1429 ∨ z = 1433)
    (hS : ∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = z)
    (d9 : z ≠ 17 → padicValNat 2 n % 8 ≠ 4)
    (d10 : z ≠ 11 → z ≠ 43 → z ≠ 257 → padicValNat 2 n % 16 ≠ 8)
    (c5 : padicValNat 2 n % 64 ≠ 32) :
    padicValNat 2 n ≤ 9 ∨ (z = 257 ∧ padicValNat 2 n % 16 = 8 ∧ Even (n.factorization z)) ∨
      z ∈ ({13, 23, 29, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 157, 173, 197, 199, 211, 227, 229, 263, 271, 307, 331, 337, 367, 379, 439, 499, 619} : Finset ℕ) ∨
      z ∈ ({7, 11, 17, 19, 31} : Finset ℕ) := by
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1193
      (fun h4 hd _ => absurd hd (nf_1193 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1201
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1213
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1217
      (fun _ hd _ => absurd (rs_1217 hd) (d9 (by norm_num))))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1223
      (fun h4 hd _ => absurd hd (nf_1223 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1229
      (fun h4 hd _ => absurd hd (nf_1229 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1231
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1237
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1249
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1259
      (fun h4 hd _ => absurd hd (nf_1259 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1277
      (fun h4 hd _ => absurd hd (nf_1277 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1279
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1283
      (fun h4 hd _ => absurd hd (nf_1283 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1289
      (fun h4 hd _ => absurd hd (nf_1289 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1291
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1297
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1301
      (fun h4 hd _ => absurd hd (nf_1301 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1303
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1307
      (fun h4 hd _ => absurd hd (nf_1307 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1319
      (fun h4 hd _ => absurd hd (nf_1319 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1321
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1327
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1361
      (fun _ hd _ => absurd (rs_1361 hd) (d9 (by norm_num))))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1367
      (fun h4 hd _ => absurd hd (nf_1367 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1373
      (fun h4 hd _ => absurd hd (nf_1373 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1381
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1399
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1409
      (fun _ hd _ => absurd (rs_1409 hd) c5))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1423
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1427
      (fun h4 hd _ => absurd hd (nf_1427 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1429
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1433
      (fun h4 hd _ => absurd hd (nf_1433 h4)))

set_option maxHeartbeats 4000000 in
theorem pr_8 {z : ℕ} (hz : z.Prime) (hlo : 1439 ≤ z) (hhi : z < 1657) :
    z = 1439 ∨ z = 1447 ∨ z = 1451 ∨ z = 1453 ∨ z = 1459 ∨ z = 1471 ∨ z = 1481 ∨ z = 1483 ∨ 
    z = 1487 ∨ z = 1489 ∨ z = 1493 ∨ z = 1499 ∨ z = 1511 ∨ z = 1523 ∨ z = 1531 ∨ z = 1543 ∨ 
    z = 1549 ∨ z = 1553 ∨ z = 1559 ∨ z = 1567 ∨ z = 1571 ∨ z = 1579 ∨ z = 1583 ∨ z = 1597 ∨ 
    z = 1601 ∨ z = 1607 ∨ z = 1609 ∨ z = 1613 ∨ z = 1619 ∨ z = 1621 ∨ z = 1627 ∨ z = 1637 := by
  interval_cases z <;> first | (norm_num at hz; done) | simp

set_option maxHeartbeats 1000000 in
theorem step_8 {n z : ℕ} (h : Erdos1052.IsUnitaryPerfect n)
    (hz : z = 1439 ∨ z = 1447 ∨ z = 1451 ∨ z = 1453 ∨ z = 1459 ∨ z = 1471 ∨ z = 1481 ∨ z = 1483 ∨ 
      z = 1487 ∨ z = 1489 ∨ z = 1493 ∨ z = 1499 ∨ z = 1511 ∨ z = 1523 ∨ z = 1531 ∨ z = 1543 ∨ 
      z = 1549 ∨ z = 1553 ∨ z = 1559 ∨ z = 1567 ∨ z = 1571 ∨ z = 1579 ∨ z = 1583 ∨ z = 1597 ∨ 
      z = 1601 ∨ z = 1607 ∨ z = 1609 ∨ z = 1613 ∨ z = 1619 ∨ z = 1621 ∨ z = 1627 ∨ z = 1637)
    (hS : ∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = z)
    (d9 : z ≠ 17 → padicValNat 2 n % 8 ≠ 4)
    (d10 : z ≠ 11 → z ≠ 43 → z ≠ 257 → padicValNat 2 n % 16 ≠ 8) :
    padicValNat 2 n ≤ 9 ∨ (z = 257 ∧ padicValNat 2 n % 16 = 8 ∧ Even (n.factorization z)) ∨
      z ∈ ({13, 23, 29, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 157, 173, 197, 199, 211, 227, 229, 263, 271, 307, 331, 337, 367, 379, 439, 499, 619} : Finset ℕ) ∨
      z ∈ ({7, 11, 17, 19, 31} : Finset ℕ) := by
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1439
      (fun h4 hd _ => absurd hd (nf_1439 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1447
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1451
      (fun h4 hd _ => absurd hd (nf_1451 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1453
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1459
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1471
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1481
      (fun h4 hd _ => absurd hd (nf_1481 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1483
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1487
      (fun h4 hd _ => absurd hd (nf_1487 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1489
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1493
      (fun h4 hd _ => absurd hd (nf_1493 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1499
      (fun h4 hd _ => absurd hd (nf_1499 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1511
      (fun h4 hd _ => absurd hd (nf_1511 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1523
      (fun h4 hd _ => absurd hd (nf_1523 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1531
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1543
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1549
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1553
      (fun h4 hd _ => absurd hd (nf_1553 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1559
      (fun h4 hd _ => absurd hd (nf_1559 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1567
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1571
      (fun h4 hd _ => absurd hd (nf_1571 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1579
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1583
      (fun h4 hd _ => absurd hd (nf_1583 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1597
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1601
      (fun _ hd _ => absurd (rs_1601 hd) (d10 (by norm_num) (by norm_num) (by norm_num))))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1607
      (fun h4 hd _ => absurd hd (nf_1607 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1609
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1613
      (fun h4 hd _ => absurd hd (nf_1613 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1619
      (fun h4 hd _ => absurd hd (nf_1619 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1621
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1627
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1637
      (fun h4 hd _ => absurd hd (nf_1637 h4)))

set_option maxHeartbeats 4000000 in
theorem pr_9 {z : ℕ} (hz : z.Prime) (hlo : 1657 ≤ z) (hhi : z < 1907) :
    z = 1657 ∨ z = 1663 ∨ z = 1667 ∨ z = 1669 ∨ z = 1693 ∨ z = 1697 ∨ z = 1699 ∨ z = 1709 ∨ 
    z = 1721 ∨ z = 1723 ∨ z = 1733 ∨ z = 1741 ∨ z = 1747 ∨ z = 1753 ∨ z = 1759 ∨ z = 1777 ∨ 
    z = 1783 ∨ z = 1787 ∨ z = 1789 ∨ z = 1801 ∨ z = 1811 ∨ z = 1823 ∨ z = 1831 ∨ z = 1847 ∨ 
    z = 1861 ∨ z = 1867 ∨ z = 1871 ∨ z = 1873 ∨ z = 1877 ∨ z = 1879 ∨ z = 1889 ∨ z = 1901 := by
  interval_cases z <;> first | (norm_num at hz; done) | simp

set_option maxHeartbeats 1000000 in
theorem step_9 {n z : ℕ} (h : Erdos1052.IsUnitaryPerfect n)
    (hz : z = 1657 ∨ z = 1663 ∨ z = 1667 ∨ z = 1669 ∨ z = 1693 ∨ z = 1697 ∨ z = 1699 ∨ z = 1709 ∨ 
      z = 1721 ∨ z = 1723 ∨ z = 1733 ∨ z = 1741 ∨ z = 1747 ∨ z = 1753 ∨ z = 1759 ∨ z = 1777 ∨ 
      z = 1783 ∨ z = 1787 ∨ z = 1789 ∨ z = 1801 ∨ z = 1811 ∨ z = 1823 ∨ z = 1831 ∨ z = 1847 ∨ 
      z = 1861 ∨ z = 1867 ∨ z = 1871 ∨ z = 1873 ∨ z = 1877 ∨ z = 1879 ∨ z = 1889 ∨ z = 1901)
    (hS : ∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = z)
    (d9 : z ≠ 17 → padicValNat 2 n % 8 ≠ 4)
    (d10 : z ≠ 11 → z ≠ 43 → z ≠ 257 → padicValNat 2 n % 16 ≠ 8) :
    padicValNat 2 n ≤ 9 ∨ (z = 257 ∧ padicValNat 2 n % 16 = 8 ∧ Even (n.factorization z)) ∨
      z ∈ ({13, 23, 29, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 157, 173, 197, 199, 211, 227, 229, 263, 271, 307, 331, 337, 367, 379, 439, 499, 619} : Finset ℕ) ∨
      z ∈ ({7, 11, 17, 19, 31} : Finset ℕ) := by
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1657
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1663
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1667
      (fun h4 hd _ => absurd hd (nf_1667 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1669
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1693
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1697
      (fun _ hd _ => absurd (rs_1697 hd) (d10 (by norm_num) (by norm_num) (by norm_num))))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1699
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1709
      (fun h4 hd _ => absurd hd (nf_1709 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1721
      (fun h4 hd _ => absurd hd (nf_1721 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1723
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1733
      (fun h4 hd _ => absurd hd (nf_1733 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1741
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1747
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1753
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1759
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1777
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1783
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1787
      (fun h4 hd _ => absurd hd (nf_1787 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1789
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1801
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1811
      (fun h4 hd _ => absurd hd (nf_1811 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1823
      (fun h4 hd _ => absurd hd (nf_1823 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1831
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1847
      (fun h4 hd _ => absurd hd (nf_1847 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1861
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1867
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1871
      (fun h4 hd _ => absurd hd (nf_1871 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1873
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1877
      (fun h4 hd _ => absurd hd (nf_1877 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1879
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1889
      (fun _ hd _ => absurd (rs_1889 hd) (d9 (by norm_num))))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1901
      (fun h4 hd _ => absurd hd (nf_1901 h4)))

set_option maxHeartbeats 4000000 in
theorem pr_10 {z : ℕ} (hz : z.Prime) (hlo : 1907 ≤ z) (hhi : z < 2100) :
    z = 1907 ∨ z = 1913 ∨ z = 1931 ∨ z = 1933 ∨ z = 1949 ∨ z = 1951 ∨ z = 1973 ∨ z = 1979 ∨ 
    z = 1987 ∨ z = 1993 ∨ z = 1997 ∨ z = 1999 ∨ z = 2003 ∨ z = 2011 ∨ z = 2017 ∨ z = 2027 ∨ 
    z = 2029 ∨ z = 2039 ∨ z = 2053 ∨ z = 2063 ∨ z = 2069 ∨ z = 2081 ∨ z = 2083 ∨ z = 2087 ∨ 
    z = 2089 ∨ z = 2099 := by
  interval_cases z <;> first | (norm_num at hz; done) | simp

set_option maxHeartbeats 1000000 in
theorem step_10 {n z : ℕ} (h : Erdos1052.IsUnitaryPerfect n)
    (hz : z = 1907 ∨ z = 1913 ∨ z = 1931 ∨ z = 1933 ∨ z = 1949 ∨ z = 1951 ∨ z = 1973 ∨ z = 1979 ∨ 
      z = 1987 ∨ z = 1993 ∨ z = 1997 ∨ z = 1999 ∨ z = 2003 ∨ z = 2011 ∨ z = 2017 ∨ z = 2027 ∨ 
      z = 2029 ∨ z = 2039 ∨ z = 2053 ∨ z = 2063 ∨ z = 2069 ∨ z = 2081 ∨ z = 2083 ∨ z = 2087 ∨ 
      z = 2089 ∨ z = 2099)
    (hS : ∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = z)
    (d9 : z ≠ 17 → padicValNat 2 n % 8 ≠ 4)
    (d10 : z ≠ 11 → z ≠ 43 → z ≠ 257 → padicValNat 2 n % 16 ≠ 8) :
    padicValNat 2 n ≤ 9 ∨ (z = 257 ∧ padicValNat 2 n % 16 = 8 ∧ Even (n.factorization z)) ∨
      z ∈ ({13, 23, 29, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 157, 173, 197, 199, 211, 227, 229, 263, 271, 307, 331, 337, 367, 379, 439, 499, 619} : Finset ℕ) ∨
      z ∈ ({7, 11, 17, 19, 31} : Finset ℕ) := by
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1907
      (fun h4 hd _ => absurd hd (nf_1907 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1913
      (fun h4 hd _ => absurd hd (nf_1913 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1931
      (fun h4 hd _ => absurd hd (nf_1931 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1933
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1949
      (fun h4 hd _ => absurd hd (nf_1949 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1951
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1973
      (fun h4 hd _ => absurd hd (nf_1973 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1979
      (fun h4 hd _ => absurd hd (nf_1979 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1987
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1993
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1997
      (fun h4 hd _ => absurd hd (nf_1997 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_1999
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_2003
      (fun h4 hd _ => absurd hd (nf_2003 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_2011
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_2017
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_2027
      (fun h4 hd _ => absurd hd (nf_2027 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_2029
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_2039
      (fun h4 hd _ => absurd hd (nf_2039 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_2053
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_2063
      (fun h4 hd _ => absurd hd (nf_2063 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_2069
      (fun h4 hd _ => absurd hd (nf_2069 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_2081
      (fun _ hd _ => absurd (rs_2081 hd) (d10 (by norm_num) (by norm_num) (by norm_num))))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_2083
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_2087
      (fun h4 hd _ => absurd hd (nf_2087 h4)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_2089
      (fun _ _ h3 => absurd h3 (by norm_num)))
  · exact Or.inl (le_nine_of_leaf h (by norm_num) (by norm_num) hS zmass_2099
      (fun h4 hd _ => absurd hd (nf_2099 h4)))

theorem main : H1 → H2 → H3 → OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1.H4 := by
  rintro ⟨A1, h1⟩ ⟨A2, h2⟩ ⟨A3, h3⟩
  refine ⟨max 9 (max A1 (max A2 A3)),
    fun n h z hz h7 hlt hS d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 => ?_⟩
  have hA1 : A1 ≤ max 9 (max A1 (max A2 A3)) := (le_max_left _ _).trans (le_max_right _ _)
  have hA2 : A2 ≤ max 9 (max A1 (max A2 A3)) :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hA3 : A3 ≤ max 9 (max A1 (max A2 A3)) :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have c4 : padicValNat 2 n % 32 ≠ 16 := by
    have h' := d12 4 (by simp)
    norm_num at h'
    exact h'
  have c5 : padicValNat 2 n % 64 ≠ 32 := by
    have h' := d12 5 (by simp)
    norm_num at h'
    exact h'
  have key : padicValNat 2 n ≤ 9 ∨ (z = 257 ∧ padicValNat 2 n % 16 = 8 ∧ Even (n.factorization z)) ∨
      z ∈ ({13, 23, 29, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 157, 173, 197, 199, 211, 227, 229, 263, 271, 307, 331, 337, 367, 379, 439, 499, 619} : Finset ℕ) ∨
      z ∈ ({7, 11, 17, 19, 31} : Finset ℕ) := by
    by_cases g1 : z < 151
    · exact step_1 h (pr_1 hz h7 g1) hS d9 d10
    by_cases g2 : z < 337
    · exact step_2 h (pr_2 hz (by omega) g2) hS d9 d10
    by_cases g3 : z < 541
    · exact step_3 h (pr_3 hz (by omega) g3) hS d9 d10 c4
    by_cases g4 : z < 743
    · exact step_4 h (pr_4 hz (by omega) g4) hS d9 d10 c5
    by_cases g5 : z < 971
    · exact step_5 h (pr_5 hz (by omega) g5) hS d9 d10
    by_cases g6 : z < 1193
    · exact step_6 h (pr_6 hz (by omega) g6) hS d9 d10
    by_cases g7 : z < 1439
    · exact step_7 h (pr_7 hz (by omega) g7) hS d9 d10 c5
    by_cases g8 : z < 1657
    · exact step_8 h (pr_8 hz (by omega) g8) hS d9 d10
    by_cases g9 : z < 1907
    · exact step_9 h (pr_9 hz (by omega) g9) hS d9 d10
    exact step_10 h (pr_10 hz (by omega) hlt) hS d9 d10
  rcases key with h9 | ⟨rfl, h16, hev⟩ | hT | h5
  · exact h9.trans (le_max_left _ _)
  · exact (h1 n h hS h16 hev).trans hA1
  · obtain ⟨n11, n17, n257, n743⟩ := ne_of_mem hT
    by_cases ha : padicValNat 2 n % 2 = 1
    · exact (three_all h hT hS (Or.inl (three_dvd_two_pow_add_one ha))).trans (le_max_left _ _)
    by_cases he : z % 3 = 2 ∧ Odd (n.factorization z)
    · exact (three_all h hT hS (Or.inr (three_dvd_one_add_pow he.1 he.2))).trans
        (le_max_left _ _)
    · exact (h2 n h z hT hS (by omega)
        (fun hz3 => Nat.not_odd_iff_even.mp (fun ho => he ⟨hz3, ho⟩))
        d7 d8 (d9 n17) (fun h43 => d10 n11 h43 n257) (d11 n743) d12).trans hA2
  · exact (h3 n h z h5 hS d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12).trans hA3

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R2
