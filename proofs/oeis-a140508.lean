import OMAStatements.S_oeis_a140508

-- Problem: A140508: Mobius transform applied twice to A001414.
-- Upstream: formal-conjectures statements/oeis-a140508.lean:0 (declaration OMA.S_oeis_a140508.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: let c(d) = p if d is a power of the prime p and c(d) = 0 otherwise. Then
-- Sum_{i | n} c(i) = sopfr(n) (induction over prime powers and coprime products), so by Mobius
-- inversion the Mobius transform of sopfr is c. Then a(n) = Sum_{d | n} mu(n/d) c(d) =
-- -mu(n) * W(n) with W(n) = Sum_{p | n} p, by the same induction. For n > 1, W(n) > 0.

namespace L03A140508

open OMA.S_oeis_a140508

def c (d : ℕ) : ℤ := if IsPrimePow d then (d.minFac : ℤ) else 0

def G (n : ℕ) : ℤ := ∑ d ∈ n.divisors, ArithmeticFunction.moebius (n / d) * c d

def W (n : ℕ) : ℤ := ∑ p ∈ n.primeFactors, (p : ℤ)

theorem c_one : c 1 = 0 := by
  unfold c
  rw [if_neg (show ¬IsPrimePow (1 : ℕ) from not_isPrimePow_one)]

theorem c_pow (p i : ℕ) (hp : p.Prime) (hi : i ≠ 0) : c (p ^ i) = (p : ℤ) := by
  unfold c
  rw [if_pos (hp.prime.isPrimePow.pow hi), Nat.pow_minFac hi, hp.minFac_eq]

theorem c_prime (p : ℕ) (hp : p.Prime) : c p = (p : ℤ) := by
  have h := c_pow p 1 hp one_ne_zero
  rwa [pow_one] at h

theorem c_filter (n : ℕ) : ∑ i ∈ n.divisors, c i =
    ∑ i ∈ Finset.filter (fun d => IsPrimePow d) n.divisors, (i.minFac : ℤ) := by
  unfold c
  rw [Finset.sum_filter]

theorem sum_c (n : ℕ) : 0 < n → ∑ i ∈ n.divisors, c i = (A001414 n : ℤ) := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp _ =>
    intro _
    rw [Nat.sum_divisors_prime_pow hp, Finset.sum_range_succ', pow_zero, c_one, add_zero]
    have hc : ∀ i ∈ Finset.range k, c (p ^ (i + 1)) = (p : ℤ) :=
      fun i _ => c_pow p (i + 1) hp (Nat.succ_ne_zero i)
    rw [Finset.sum_congr rfl hc, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    unfold A001414
    rw [hp.primeFactorsList_pow, List.sum_replicate, smul_eq_mul, Nat.cast_mul]
  | zero =>
    intro h
    exact absurd h (lt_irrefl 0)
  | one =>
    intro _
    rw [Nat.divisors_one, Finset.sum_singleton, c_one]
    unfold A001414
    rw [Nat.primeFactorsList_one, List.sum_nil, Nat.cast_zero]
  | coprime x y hx hy hxy ihx ihy =>
    intro _
    have hx0 := ihx (Nat.zero_lt_of_lt hx)
    have hy0 := ihy (Nat.zero_lt_of_lt hy)
    rw [c_filter] at hx0 hy0 ⊢
    rw [Nat.mul_divisors_filter_prime_pow hxy, Finset.filter_union,
      Finset.sum_union (Nat.disjoint_divisors_filter_isPrimePow hxy), hx0, hy0]
    unfold A001414
    rw [(Nat.perm_primeFactorsList_mul (show x ≠ 0 by omega) (show y ≠ 0 by omega)).sum_eq,
      List.sum_append, Nat.cast_add]

theorem T_sopfr (d : ℕ) (hd : 0 < d) :
    moebiusTransform (fun k => (A001414 k : ℤ)) d = c d := by
  have h := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq (R := ℤ) (f := c)
    (g := fun k => (A001414 k : ℤ))).mp sum_c d hd
  rw [← h]
  unfold moebiusTransform
  rw [← Nat.sum_divisorsAntidiagonal'
    (fun x y => ArithmeticFunction.moebius x * (A001414 y : ℤ))]
  simp only [Int.cast_id]

theorem a_eq (n : ℕ) : a n = G n := by
  unfold a
  show ∑ d ∈ n.divisors, ArithmeticFunction.moebius (n / d) *
      moebiusTransform (fun k => (A001414 k : ℤ)) d = G n
  unfold G
  refine Finset.sum_congr rfl (fun d hd => ?_)
  rw [T_sopfr d (Nat.pos_of_mem_divisors hd)]

theorem G_filter (n : ℕ) : G n = ∑ d ∈ Finset.filter (fun d => IsPrimePow d) n.divisors,
    ArithmeticFunction.moebius (n / d) * (d.minFac : ℤ) := by
  rw [Finset.sum_filter]
  unfold G c
  refine Finset.sum_congr rfl (fun d _ => ?_)
  by_cases h : IsPrimePow d
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, mul_zero]

theorem G_one : G 1 = -ArithmeticFunction.moebius 1 * W 1 := by
  unfold G W
  rw [Nat.divisors_one, Finset.sum_singleton, c_one, mul_zero, Nat.primeFactors_one,
    Finset.sum_empty, mul_zero]

theorem G_pp (p k : ℕ) (hp : p.Prime) (hk : 0 < k) :
    G (p ^ k) = -ArithmeticFunction.moebius (p ^ k) * W (p ^ k) := by
  have hW : W (p ^ k) = (p : ℤ) := by
    unfold W
    rw [Nat.primeFactors_prime_pow hk.ne' hp, Finset.sum_singleton]
  rw [hW]
  rcases (show k = 1 ∨ 2 ≤ k by omega) with h1 | h2
  · subst h1
    rw [pow_one]
    unfold G
    rw [hp.divisors, Finset.sum_pair hp.one_lt.ne, Nat.div_one, Nat.div_self hp.pos, c_one,
      c_prime p hp, ArithmeticFunction.moebius_apply_one,
      ArithmeticFunction.moebius_apply_prime hp]
    ring
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 + 1 := ⟨k - 2, by omega⟩
    have hs : ∑ d ∈ (p ^ (m + 1 + 1)).divisors,
        ArithmeticFunction.moebius (p ^ (m + 1 + 1) / d) * c d =
        ∑ i ∈ Finset.range (m + 1 + 1 + 1),
        ArithmeticFunction.moebius (p ^ (m + 1 + 1) / p ^ i) * c (p ^ i) :=
      Nat.sum_divisors_prime_pow hp
    have hz : ∑ i ∈ Finset.range (m + 1),
        ArithmeticFunction.moebius (p ^ (m + 1 + 1) / p ^ i) * c (p ^ i) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hi' : i < m + 1 := Finset.mem_range.mp hi
      rw [Nat.pow_div (show i ≤ m + 1 + 1 by omega) hp.pos,
        ArithmeticFunction.moebius_apply_prime_pow hp (show m + 1 + 1 - i ≠ 0 by omega),
        if_neg (show ¬(m + 1 + 1 - i = 1) by omega), zero_mul]
    unfold G
    rw [hs, Finset.sum_range_succ, Finset.sum_range_succ, hz,
      Nat.pow_div (show m + 1 ≤ m + 1 + 1 by omega) hp.pos,
      show m + 1 + 1 - (m + 1) = 1 by omega, pow_one,
      Nat.div_self (pow_pos hp.pos (m + 1 + 1)),
      c_pow p (m + 1) hp (by omega), c_pow p (m + 1 + 1) hp (by omega),
      ArithmeticFunction.moebius_apply_prime hp, ArithmeticFunction.moebius_apply_one,
      ArithmeticFunction.moebius_apply_prime_pow hp (show m + 1 + 1 ≠ 0 by omega),
      if_neg (show ¬(m + 1 + 1 = 1) by omega)]
    ring

theorem G_mul (x y : ℕ) (hxy : Nat.Coprime x y)
    (ihx : G x = -ArithmeticFunction.moebius x * W x)
    (ihy : G y = -ArithmeticFunction.moebius y * W y) :
    G (x * y) = -ArithmeticFunction.moebius (x * y) * W (x * y) := by
  rw [G_filter] at ihx ihy ⊢
  rw [Nat.mul_divisors_filter_prime_pow hxy, Finset.filter_union,
    Finset.sum_union (Nat.disjoint_divisors_filter_isPrimePow hxy)]
  have e1 : ∑ d ∈ Finset.filter (fun d => IsPrimePow d) x.divisors,
      ArithmeticFunction.moebius (x * y / d) * (d.minFac : ℤ) =
      ArithmeticFunction.moebius y * ∑ d ∈ Finset.filter (fun d => IsPrimePow d) x.divisors,
      ArithmeticFunction.moebius (x / d) * (d.minFac : ℤ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun d hd => ?_)
    have hdx : d ∣ x := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1
    rw [Nat.mul_div_right_comm hdx y,
      ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
        (Nat.Coprime.coprime_div_left hxy hdx)]
    ring
  have e2 : ∑ d ∈ Finset.filter (fun d => IsPrimePow d) y.divisors,
      ArithmeticFunction.moebius (x * y / d) * (d.minFac : ℤ) =
      ArithmeticFunction.moebius x * ∑ d ∈ Finset.filter (fun d => IsPrimePow d) y.divisors,
      ArithmeticFunction.moebius (y / d) * (d.minFac : ℤ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun d hd => ?_)
    have hdy : d ∣ y := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1
    rw [Nat.mul_div_assoc x hdy,
      ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
        (Nat.Coprime.coprime_div_right hxy hdy)]
    ring
  have hW : W (x * y) = W x + W y := by
    unfold W
    rw [Nat.Coprime.primeFactors_mul hxy, Finset.sum_union hxy.disjoint_primeFactors]
  rw [e1, e2, ihx, ihy, hW, ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hxy]
  ring

theorem key (n : ℕ) : 0 < n → G n = -ArithmeticFunction.moebius n * W n := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
    intro _
    exact G_pp p k hp hk
  | zero =>
    intro h
    exact absurd h (lt_irrefl 0)
  | one =>
    intro _
    exact G_one
  | coprime x y hx hy hxy ihx ihy =>
    intro _
    exact G_mul x y hxy (ihx (Nat.zero_lt_of_lt hx)) (ihy (Nat.zero_lt_of_lt hy))

theorem W_pos (n : ℕ) (hn : 1 < n) : 0 < W n := by
  unfold W
  apply Finset.sum_pos
  · intro p hp
    have h2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
    have h3 : (2 : ℤ) ≤ (p : ℤ) := by exact_mod_cast h2
    linarith
  · exact Nat.nonempty_primeFactors.mpr hn

theorem formula (n : ℕ) (hn : 0 < n) : a n = -ArithmeticFunction.moebius n * W n := by
  rw [a_eq]
  exact key n hn

end L03A140508

open OMA.S_oeis_a140508 L03A140508 in
theorem OMA.solution : type_of% @OMA.S_oeis_a140508.main := by
  intro n hn
  have hf := formula n (by omega)
  have hW := W_pos n (by omega)
  constructor
  · rw [hf]
    constructor
    · intro h
      rcases mul_eq_zero.mp h with h0 | h0
      · exact neg_eq_zero.mp h0
      · exact absurd h0 hW.ne'
    · intro h
      rw [h, neg_zero, zero_mul]
  · intro hne
    have hb := ArithmeticFunction.abs_moebius_le_one (n := n)
    rw [abs_le] at hb
    rcases (show ArithmeticFunction.moebius n = -1 ∨ ArithmeticFunction.moebius n = 0 ∨
        ArithmeticFunction.moebius n = 1 by omega) with h | h | h
    · have ha : a n = W n := by
        rw [hf, h]
        ring
      rw [h, ha, abs_of_pos hW, show -W n = -1 * W n by ring, Int.mul_ediv_cancel _ hW.ne']
    · exact absurd (show a n = 0 by rw [hf, h, neg_zero, zero_mul]) hne
    · have ha : a n = -W n := by
        rw [hf, h]
        ring
      rw [h, ha, abs_neg, abs_of_pos hW, neg_neg, Int.ediv_self hW.ne']
