import OMAStatements.S_oeis_a328959

-- Problem oeis-a328959: a(n) = tau(n) - 2 - (Omega(n) - 1) * omega(n) satisfies a(1) = -1 and a(n) >= 0 for n >= 2,
-- where tau counts divisors, Omega counts prime factors with multiplicity and omega counts distinct prime factors.
-- Upstream: statements/oeis-a328959.lean (declaration OMA.S_oeis_a328959.main)
-- Credit: @cclyles (the owner of the agent is credited as the solver)
--
-- Proof: write r = omega(n), S = Omega(n). The stronger bound
--   2^r * (S - r + 2) <= 2 * tau(n)        (*)
-- holds with equality for prime powers (r = 1, S = k, tau = k + 1) and is preserved by products of coprime
-- numbers, because tau is multiplicative, S and r are additive, and (s + 2)(t + 2) >= 2 (s + t + 2).
-- So (*) holds for every n >= 2 by induction over the prime factorization. Then (*) gives the claim, using
-- 2^r >= 2r and 2^r >= r^2 - r + 2 for r >= 1.

open ArithmeticFunction

private lemma two_pow_bounds_a328959 :
    ∀ k : ℕ, 2 * (k + 1) ≤ 2 ^ (k + 1) ∧ (k + 1) * (k + 1) + 2 ≤ 2 ^ (k + 1) + (k + 1) := by
  intro k
  induction k with
  | zero => norm_num
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih
    have hk : k ≤ k * k := Nat.le_mul_self k
    have hp : 2 ^ (k + 1 + 1) = 2 * 2 ^ (k + 1) := by ring
    rw [hp]
    constructor
    · nlinarith [h1]
    · nlinarith [h2, hk]

private lemma key_a328959 : ∀ n : ℕ, 1 < n →
    1 ≤ cardDistinctFactors n ∧ cardDistinctFactors n ≤ cardFactors n ∧
      2 ^ cardDistinctFactors n * (cardFactors n + 2)
        ≤ 2 * n.divisors.card + 2 ^ cardDistinctFactors n * cardDistinctFactors n := by
  intro n
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
    intro _
    rw [cardDistinctFactors_apply_prime_pow hp hk.ne', cardFactors_apply_prime_pow hp,
      Nat.divisors_prime_pow hp, Finset.card_map, Finset.card_range]
    refine ⟨le_refl 1, hk, ?_⟩
    simp only [pow_one]
    omega
  | zero =>
    intro h
    omega
  | one =>
    intro h
    omega
  | coprime a b ha hb hab iha ihb =>
    intro _
    obtain ⟨a1, a2, a3⟩ := iha ha
    obtain ⟨b1, b2, b3⟩ := ihb hb
    have ha0 : a ≠ 0 := by omega
    have hb0 : b ≠ 0 := by omega
    rw [cardDistinctFactors_mul hab, cardFactors_mul ha0 hb0, Nat.Coprime.card_divisors_mul hab]
    obtain ⟨ta, hta⟩ := Nat.exists_eq_add_of_le a2
    obtain ⟨tb, htb⟩ := Nat.exists_eq_add_of_le b2
    rw [hta] at a3
    rw [htb] at b3
    have a4 : 2 ^ cardDistinctFactors a * (ta + 2) ≤ 2 * a.divisors.card := by nlinarith [a3]
    have b4 : 2 ^ cardDistinctFactors b * (tb + 2) ≤ 2 * b.divisors.card := by nlinarith [b3]
    have hprod := Nat.mul_le_mul a4 b4
    have hz : 0 ≤ 2 ^ cardDistinctFactors a * 2 ^ cardDistinctFactors b * ta * tb := Nat.zero_le _
    refine ⟨by omega, by omega, ?_⟩
    rw [hta, htb, pow_add]
    nlinarith [hprod, hz]

private lemma final_arith_a328959 (τ S r : ℕ) (h1 : 1 ≤ r) (h2 : r ≤ S)
    (h3 : 2 ^ r * (S + 2) ≤ 2 * τ + 2 ^ r * r) :
    (0 : ℤ) ≤ (τ : ℤ) - 2 - ((S : ℤ) - 1) * (r : ℤ) := by
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
  obtain ⟨t, rfl⟩ : ∃ t, S = k + 1 + t := ⟨S - (k + 1), by omega⟩
  obtain ⟨hb1, hb2⟩ := two_pow_bounds_a328959 k
  have hp : 2 * (k + 1) * t ≤ 2 ^ (k + 1) * t := Nat.mul_le_mul_right t hb1
  have h3' : ((2 : ℤ) ^ (k + 1)) * ((k : ℤ) + 1 + t + 2) ≤ 2 * τ + (2 : ℤ) ^ (k + 1) * ((k : ℤ) + 1) := by
    exact_mod_cast h3
  have hb2' : ((k : ℤ) + 1) * ((k : ℤ) + 1) + 2 ≤ (2 : ℤ) ^ (k + 1) + ((k : ℤ) + 1) := by
    exact_mod_cast hb2
  have hp' : 2 * ((k : ℤ) + 1) * (t : ℤ) ≤ (2 : ℤ) ^ (k + 1) * (t : ℤ) := by
    exact_mod_cast hp
  push_cast
  nlinarith [h3', hb2', hp']

theorem OMA.solution : type_of% @OMA.S_oeis_a328959.main := by
  refine ⟨?_, ?_⟩
  · simp [OMA.S_oeis_a328959.a]
  · intro n hn
    obtain ⟨h1, h2, h3⟩ := key_a328959 n (by omega)
    unfold OMA.S_oeis_a328959.a
    exact final_arith_a328959 _ _ _ h1 h2 h3
