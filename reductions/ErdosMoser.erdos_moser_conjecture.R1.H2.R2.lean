import OMAReductions.R_ErdosMoser_erdos_moser_conjecture_R1
import Mathlib

/-!
# Reduction of the even-exponent Erdős-Moser conjecture (Moser 1953, Krzysztofek 1966, MTU 1994, Moree 2011, GMZ 2010)

Reduction `ErdosMoser.erdos_moser_conjecture.R1.H2.R2` of `ErdosMoser.erdos_moser_conjecture.R1.H2`.

We prove unconditionally (using no hypotheses):
1. Krzysztofek (1966) sharp algebraic bounds: `k + 2 < m` and `2 * m < 3 * (k + 1)` (and `6 ≤ k`).
2. Universal non-divisibility: for every prime `p` with `p - 1 ∣ k`, `¬ p ∣ m` (in particular `Odd m` and `¬ 3 ∣ m`).
3. Unified prime-power base-`p` congruence: for every odd prime `p` with `p - 1 ∣ k`,
   `((p - 1) * m + m % p) ≡ 2 * p [MOD p ^ (padicValNat p k + 2)]`.
   In particular, `m % 3 = 1 → 3 ^ (padicValNat 3 k + 2) ∣ 2 * m - 5` (so `m % 9 = 7`) and
   `m % 3 = 2 → 3 ^ (padicValNat 3 k + 2) ∣ m - 2` (so `m % 9 = 2`).
4. `√m`-smoothness for `D_k`: every odd prime `p` with `p - 1 ∣ k` satisfies `p ^ 2 ≤ m ∨ m = p ^ 2 - p + 1`.
5. Moree-te Riele-Urbanowicz (1994) exact 2-adic valuation: `padicValNat 2 (m - 3) = padicValNat 2 k + 3`
   (hence `m % 16 = 3`).
6. Moser (1953) and Moree (2011) Theorem 2: all four prime divisibility/congruence/squarefreeness
   relations on `m - 1`, `(m + 1) / 2`, `2 * m - 1`, `2 * m + 1`, squarefreeness of
   `M1 = (m ^ 2 - 1) * (4 * m ^ 2 - 1) / 12`, and the combined master inequality
   `19 / 6 ≤ ∑_{p ∣ M1} 1 / p + 1 / (m - 1) + 2 / (m + 1) + 2 / (2 * m - 1) + 4 / (2 * m + 1)`.
7. Leo Moser (1953) headline lower bound: `10 ^ 1000000 < m`, proved from scratch via Chebyshev 30-identity,
   elementary Stirling bounds, discrete summation by parts, and a verified prime reciprocal sieve up to 5000.
8. Voronoi (1889) / Kellner (2011) Bernoulli numerator divisibility: `m ∣ (bernoulli k).num.natAbs`, proved via
   Faulhaber's formula (`sum_range_pow`), `Bernoulli.vonStaudt_clausen`, and `p`-adic valuation estimates for `p ≥ 5`.

This splits `ErdosMoser.erdos_moser_conjecture.R1.H2` into three steps:
- `H1` (known, Gallot-Moree-Zudilin 2010 Theorem 1 + Corollary 1): any even-exponent solution with `10 ^ 9 < m`
  and `k + 2 < m < 3 * (k + 1) / 2` satisfies `0 < Real.log 2 - 2k / (2m - 3) < 1 / (90 * (2m - 3)^2)`
  and `2k / (2m - 3)` is a continued fraction convergent of `Real.log 2`.
- `H2` (open core, `m % 3 = 1` regime): equipped with all structural, Moser, Voronoi Bernoulli divisibility,
  2-adic, 3-adic, `√m`-smoothness, `10 ^ 1000000 < m`, and GMZ continued-fraction hypotheses.
- `H3` (open core, `m % 3 = 2` regime): equipped with all structural, Moser, Voronoi Bernoulli divisibility,
  2-adic, 3-adic (`3 ^ (padicValNat 3 k + 2) ∣ m - 2`), `√m`-smoothness, `10 ^ 1000000 < m`, and GMZ hypotheses.
-/

namespace OMA.R_ErdosMoser_erdos_moser_conjecture_R1_H2_R2

-- Step H1 (Gallot-Moree-Zudilin 2010): analytic approximation and continued fraction convergent of log 2.
def H1 : Prop :=
  ∀ k m : ℕ, 0 < k → 10 ^ 9 < m → Even k →
    k + 2 < m → 2 * m < 3 * (k + 1) →
    ErdosMoser.powerSum k m = m ^ k →
    0 < Real.log 2 - (2 * k : ℝ) / (2 * m - 3 : ℝ) ∧
      Real.log 2 - (2 * k : ℝ) / (2 * m - 3 : ℝ) < 1 / (90 * (2 * m - 3 : ℝ) ^ 2) ∧
      ∃ n : ℕ, ((2 * k : ℚ) / (2 * m - 3 : ℚ)) = (Real.log 2).convergent n

-- Step H2 (open core, m ≡ 1 mod 3): no even-exponent solution satisfies all Moser/Krzysztofek/Voronoi/MTU/GMZ constraints.
def H2 : Prop :=
  ∀ k m : ℕ, 0 < k → Even k → 10 ^ 1000000 < m →
    k + 2 < m → 2 * m < 3 * (k + 1) →
    m % 3 = 1 → 3 ^ (padicValNat 3 k + 2) ∣ 2 * m - 5 →
    padicValNat 2 (m - 3) = padicValNat 2 k + 3 →
    m ∣ (bernoulli k).num.natAbs →
    ErdosMoser.powerSum k m = m ^ k →
    Squarefree (m - 1) ∧ Squarefree ((m + 1) / 2) ∧
      Squarefree (2 * m - 1) ∧ Squarefree (2 * m + 1) ∧
      Squarefree ((m ^ 2 - 1) * (4 * m ^ 2 - 1) / 12) →
    (∀ p : ℕ, p.Prime →
      (p ∣ m - 1 ∨ p ∣ m + 1 ∨ p ∣ 2 * m - 1 ∨ p ∣ 2 * m + 1) → p - 1 ∣ k) →
    (∀ p : ℕ, p.Prime → p - 1 ∣ k →
      ¬ p ∣ m ∧ (p = 2 ∨ p ^ 2 ≤ m ∨ m = p ^ 2 - p + 1) ∧
      (p ≠ 2 → ((p - 1) * m + m % p) ≡ 2 * p [MOD p ^ (padicValNat p k + 2)])) →
    (19 / 6 : ℚ) ≤
      (∑ p ∈ Nat.primeFactors ((m ^ 2 - 1) * (4 * m ^ 2 - 1) / 12), (1 : ℚ) / ((p : ℕ) : ℚ)) +
        1 / (m - 1 : ℚ) + 2 / (m + 1 : ℚ) + 2 / (2 * m - 1 : ℚ) + 4 / (2 * m + 1 : ℚ) →
    0 < Real.log 2 - (2 * k : ℝ) / (2 * m - 3 : ℝ) →
    Real.log 2 - (2 * k : ℝ) / (2 * m - 3 : ℝ) < 1 / (90 * (2 * m - 3 : ℝ) ^ 2) →
    (∃ n : ℕ, ((2 * k : ℚ) / (2 * m - 3 : ℚ)) = (Real.log 2).convergent n) →
    False

-- Step H3 (open core, m ≡ 2 mod 3): no even-exponent solution satisfies all Moser/Krzysztofek/Voronoi/MTU/GMZ constraints.
def H3 : Prop :=
  ∀ k m : ℕ, 0 < k → Even k → 10 ^ 1000000 < m →
    k + 2 < m → 2 * m < 3 * (k + 1) →
    m % 3 = 2 → 3 ^ (padicValNat 3 k + 2) ∣ m - 2 →
    padicValNat 2 (m - 3) = padicValNat 2 k + 3 →
    m ∣ (bernoulli k).num.natAbs →
    ErdosMoser.powerSum k m = m ^ k →
    Squarefree (m - 1) ∧ Squarefree ((m + 1) / 2) ∧
      Squarefree (2 * m - 1) ∧ Squarefree (2 * m + 1) ∧
      Squarefree ((m ^ 2 - 1) * (4 * m ^ 2 - 1) / 12) →
    (∀ p : ℕ, p.Prime →
      (p ∣ m - 1 ∨ p ∣ m + 1 ∨ p ∣ 2 * m - 1 ∨ p ∣ 2 * m + 1) → p - 1 ∣ k) →
    (∀ p : ℕ, p.Prime → p - 1 ∣ k →
      ¬ p ∣ m ∧ (p = 2 ∨ p ^ 2 ≤ m ∨ m = p ^ 2 - p + 1) ∧
      (p ≠ 2 → ((p - 1) * m + m % p) ≡ 2 * p [MOD p ^ (padicValNat p k + 2)])) →
    (19 / 6 : ℚ) ≤
      (∑ p ∈ Nat.primeFactors ((m ^ 2 - 1) * (4 * m ^ 2 - 1) / 12), (1 : ℚ) / ((p : ℕ) : ℚ)) +
        1 / (m - 1 : ℚ) + 2 / (m + 1 : ℚ) + 2 / (2 * m - 1 : ℚ) + 4 / (2 * m + 1 : ℚ) →
    0 < Real.log 2 - (2 * k : ℝ) / (2 * m - 3 : ℝ) →
    Real.log 2 - (2 * k : ℝ) / (2 * m - 3 : ℝ) < 1 / (90 * (2 * m - 3 : ℝ) ^ 2) →
    (∃ n : ℕ, ((2 * k : ℚ) / (2 * m - 3 : ℚ)) = (Real.log 2).convergent n) →
    False

open Finset

/- ### Section 1: Basic power sum rewrite and Krzysztofek's algebraic bounds (1966) -/

lemma powerSum_eq_range {k m : ℕ} (hk : 0 < k) :
    ErdosMoser.powerSum k m = ∑ i ∈ range m, i ^ k := by
  unfold ErdosMoser.powerSum
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot hm]
    simp [Nat.zero_pow hk]

lemma pascal_powerSum (r m : ℕ) :
    m ^ (r + 1) = ∑ j ∈ range (r + 1), (r + 1).choose j * ∑ i ∈ range m, i ^ j := by
  have htele : ∑ i ∈ range m, ((i + 1) ^ (r + 1) - i ^ (r + 1)) = m ^ (r + 1) := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [sum_range_succ, ih]
      have hle : m ^ (r + 1) ≤ (m + 1) ^ (r + 1) := Nat.pow_le_pow_left (Nat.le_succ m) _
      omega
  rw [← htele]
  have hbinom : ∀ i : ℕ, (i + 1) ^ (r + 1) - i ^ (r + 1) =
      ∑ j ∈ range (r + 1), (r + 1).choose j * i ^ j := by
    intro i
    have h1 : (i + 1) ^ (r + 1) = ∑ j ∈ range (r + 2), i ^ j * 1 ^ (r + 1 - j) * (r + 1).choose j :=
      add_pow i 1 (r + 1)
    rw [sum_range_succ] at h1
    simp only [one_pow, mul_one, Nat.choose_self] at h1
    have h2 : ∑ j ∈ range (r + 1), i ^ j * (r + 1).choose j =
        ∑ j ∈ range (r + 1), (r + 1).choose j * i ^ j :=
      sum_congr rfl fun j _ => mul_comm _ _
    omega
  simp_rw [hbinom]
  rw [sum_comm]
  refine sum_congr rfl fun j _ => ?_
  rw [← mul_sum]

lemma choose_mul_sub_eq (k j : ℕ) (hj : j ≤ k) :
    (k + 1) * k.choose j = (k + 1 - j) * (k + 1).choose j := by
  have h1 : (k + 1).choose (k + 1 - j) * (k + 1 - j) = (k + 1) * k.choose (k - j) := by
    have h := Nat.add_one_mul_choose_eq k (k - j)
    have hsub : k - j + 1 = k + 1 - j := by omega
    rw [hsub] at h
    linarith
  rw [Nat.choose_symm hj, Nat.choose_symm (by omega : j ≤ k + 1)] at h1
  linarith

lemma krzysztofek_lower {k m : ℕ} (hk : 0 < k) (hm : 0 < m) (heven : Even k)
    (heq : ErdosMoser.powerSum k m = m ^ k) : k + 2 < m := by
  have hk2 : 2 ≤ k := by
    obtain ⟨t, rfl⟩ := heven
    omega
  rw [powerSum_eq_range hk] at heq
  have hp1 := pascal_powerSum k m
  rw [sum_range_succ, Nat.choose_succ_self_right, heq] at hp1
  have hsum_pos : 0 < ∑ j ∈ range k, (k + 1).choose j * ∑ i ∈ range m, i ^ j := by
    have h0 : 0 ∈ range k := mem_range.mpr hk
    have hterm : 0 < (k + 1).choose 0 * ∑ i ∈ range m, i ^ 0 := by
      simp [hm]
    exact lt_of_lt_of_le hterm
      (single_le_sum (f := fun j => (k + 1).choose j * ∑ i ∈ range m, i ^ j)
        (fun _ _ => Nat.zero_le _) h0)
  have hmk_pos : 0 < m ^ k := pow_pos hm k
  have hk1_lt : k + 1 < m := by
    by_contra hle
    push Not at hle
    have h1 : m ^ (k + 1) ≤ (k + 1) * m ^ k := by
      rw [pow_succ, mul_comm]
      exact Nat.mul_le_mul_right _ hle
    omega
  have hne : m ≠ k + 2 := by
    intro hmeq
    have hp0 := pascal_powerSum (k - 1) m
    have hk_sub : k - 1 + 1 = k := by omega
    rw [hk_sub] at hp0
    have hsub : m ^ (k + 1) = (k + 1) * m ^ k + m ^ k := by
      calc m ^ (k + 1) = m * m ^ k := by rw [pow_succ, mul_comm]
        _ = (k + 2) * m ^ k := by rw [hmeq]
        _ = (k + 1) * m ^ k + m ^ k := by ring
    have heq_sums : ∑ j ∈ range k, k.choose j * ∑ i ∈ range m, i ^ j =
        ∑ j ∈ range k, (k + 1).choose j * ∑ i ∈ range m, i ^ j := by
      omega
    have hlt_sums : ∑ j ∈ range k, k.choose j * ∑ i ∈ range m, i ^ j <
        ∑ j ∈ range k, (k + 1).choose j * ∑ i ∈ range m, i ^ j := by
      refine sum_lt_sum (fun j _ => ?_) ⟨1, mem_range.mpr (by omega), ?_⟩
      · exact Nat.mul_le_mul_right _ (Nat.choose_le_succ k j)
      · have hch : k.choose 1 < (k + 1).choose 1 := by simp
        have hs1 : 0 < ∑ i ∈ range m, i ^ 1 := by
          have h1m : 1 ∈ range m := mem_range.mpr (by omega)
          exact lt_of_lt_of_le (by norm_num : 0 < 1 ^ 1)
            (single_le_sum (f := fun i => i ^ 1) (fun _ _ => Nat.zero_le _) h1m)
        exact Nat.mul_lt_mul_of_pos_right hch hs1
    omega
  omega

lemma krzysztofek_upper {k m : ℕ} (hk : 0 < k) (hm : 0 < m) (heven : Even k)
    (heq : ErdosMoser.powerSum k m = m ^ k) : 2 * m < 3 * (k + 1) := by
  have hk2 : 2 ≤ k := by
    obtain ⟨t, rfl⟩ := heven
    omega
  have hkl : k + 2 < m := krzysztofek_lower hk hm heven heq
  rw [powerSum_eq_range hk] at heq
  have hp1 := pascal_powerSum k m
  rw [sum_range_succ, Nat.choose_succ_self_right, heq] at hp1
  have hp0 := pascal_powerSum (k - 1) m
  have hk_sub : k - 1 + 1 = k := by omega
  rw [hk_sub] at hp0
  have h2lt : 2 * ∑ j ∈ range k, (k + 1).choose j * ∑ i ∈ range m, i ^ j <
      (k + 1) * ∑ j ∈ range k, k.choose j * ∑ i ∈ range m, i ^ j := by
    rw [mul_sum, mul_sum]
    refine sum_lt_sum (fun j hj => ?_) ⟨0, mem_range.mpr hk, ?_⟩
    · rw [← mul_assoc, ← mul_assoc]
      refine Nat.mul_le_mul_right _ ?_
      have hjlt : j < k := mem_range.mp hj
      rw [choose_mul_sub_eq k j (le_of_lt hjlt)]
      exact Nat.mul_le_mul_right _ (by omega)
    · simp only [Nat.choose_zero_right, mul_one, pow_zero, sum_const, card_range, smul_eq_mul]
      nlinarith
  rw [← hp0] at h2lt
  have hmk : m ^ (k + 1) = m * m ^ k := by rw [pow_succ, mul_comm]
  have hmul : 2 * (m ^ (k + 1) - (k + 1) * m ^ k) < (k + 1) * m ^ k := by omega
  have hmk_pos : 0 < m ^ k := pow_pos hm k
  have h3 : 2 * m * m ^ k < 3 * (k + 1) * m ^ k := by
    have hle : (k + 1) * m ^ k ≤ m ^ (k + 1) := by omega
    nlinarith
  exact Nat.lt_of_mul_lt_mul_right h3

lemma k_ge_six {k m : ℕ} (hk : 0 < k) (hm : 0 < m) (heven : Even k)
    (heq : ErdosMoser.powerSum k m = m ^ k) : 6 ≤ k := by
  have hlo := krzysztofek_lower hk hm heven heq
  have hhi := krzysztofek_upper hk hm heven heq
  obtain ⟨t, rfl⟩ := heven
  have ht : t ≠ 0 := by omega
  have ht1 : t ≠ 1 := by omega
  have ht2 : t ≠ 2 := by
    intro h2
    subst h2
    have hm7 : m = 7 := by omega
    subst hm7
    have hval : ErdosMoser.powerSum (2 + 2) 7 ≠ 7 ^ (2 + 2) := by decide
    exact hval heq
  omega

/- ### Section 2: Power sums modulo p and p^λ (Moree Lemmas 1 and 2) -/

lemma sum_pow_zmod_eq_zero_of_not_dvd {p k : ℕ} [Fact p.Prime] (hk : ¬ (p - 1 ∣ k)) :
    ∑ x : ZMod p, x ^ k = 0 := by
  have hp : p.Prime := Fact.out
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have hord : orderOf g = p - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card,
      ZMod.card_units_eq_totient, Nat.totient_prime hp]
  have hgk_ne : (g : ZMod p) ^ k ≠ 1 := by
    intro h
    have h1 : g ^ k = 1 := by
      ext
      simpa [Units.val_pow_eq_pow_val] using h
    rw [← orderOf_dvd_iff_pow_eq_one, hord] at h1
    exact hk h1
  have hmul : (g : ZMod p) ^ k * ∑ x : ZMod p, x ^ k = ∑ x : ZMod p, x ^ k := by
    rw [mul_sum]
    have hbij : ∑ x : ZMod p, ((g : ZMod p) * x) ^ k = ∑ x : ZMod p, x ^ k := by
      refine Fintype.sum_bijective (fun x : ZMod p => (g : ZMod p) * x) ?_ _ _ (fun _ => rfl)
      exact (Units.mulLeft g).bijective
    simpa [mul_pow] using hbij
  have hsub : ((g : ZMod p) ^ k - 1) * ∑ x : ZMod p, x ^ k = 0 := by
    rw [sub_mul, one_mul, hmul, sub_self]
  exact (mul_eq_zero.mp hsub).resolve_left (sub_ne_zero.mpr hgk_ne)

lemma sum_pow_zmod_eq_neg_one_of_dvd {p k : ℕ} [Fact p.Prime] (hk0 : 0 < k) (hk : p - 1 ∣ k) :
    ∑ x : ZMod p, x ^ k = -1 := by
  have hp : p.Prime := Fact.out
  obtain ⟨m, rfl⟩ := hk
  have hterm : ∀ x : ZMod p, x ^ ((p - 1) * m) = if x = 0 then 0 else 1 := by
    intro x
    split_ifs with hx
    · subst hx
      exact zero_pow (Nat.ne_of_gt hk0)
    · rw [pow_mul, ZMod.pow_card_sub_one_eq_one hx, one_pow]
  simp_rw [hterm, sum_ite, sum_const_zero, zero_add, sum_const, nsmul_eq_mul, mul_one]
  have hcard : (univ.filter (fun x : ZMod p => ¬ x = 0)).card = p - 1 := by
    have h1 : univ.filter (fun x : ZMod p => ¬ x = 0) = univ.erase (0 : ZMod p) := by
      ext x
      simp
    rw [h1, card_erase_of_mem (mem_univ _), card_univ, ZMod.card]
  rw [hcard, Nat.cast_sub hp.one_le, ZMod.natCast_self, Nat.cast_one, zero_sub]

lemma sum_range_eq_sum_univ_zmod {p k : ℕ} [Fact p.Prime] :
    ((∑ r ∈ range p, r ^ k : ℕ) : ZMod p) = ∑ x : ZMod p, x ^ k := by
  rw [Nat.cast_sum]
  refine sum_bij (fun r _ => (r : ZMod p)) (fun _ _ => mem_univ _) ?_ ?_ ?_
  · intro a ha b hb hab
    have h1 : a % p = b % p := (ZMod.natCast_eq_natCast_iff' a b p).mp hab
    rw [Nat.mod_eq_of_lt (mem_range.mp ha), Nat.mod_eq_of_lt (mem_range.mp hb)] at h1
    exact h1
  · intro x _
    refine ⟨x.val, mem_range.mpr (ZMod.val_lt x), ZMod.natCast_zmod_val x⟩
  · intro r _
    simp

lemma sum_range_pow_mul_mod (q d k : ℕ) :
    ∑ i ∈ range (q * d), i ^ k ≡ q * ∑ r ∈ range d, r ^ k [MOD d] := by
  induction q with
  | zero => simp [Nat.ModEq]
  | succ q ih =>
    rw [add_mul, one_mul, sum_range_add]
    have hblock : ∑ r ∈ range d, (q * d + r) ^ k ≡ ∑ r ∈ range d, r ^ k [MOD d] := by
      rw [← ZMod.natCast_eq_natCast_iff]
      push_cast
      refine sum_congr rfl fun r _ => ?_
      rw [ZMod.natCast_self, mul_zero, zero_add]
    have h := ih.add hblock
    simpa [add_mul, one_mul] using h

lemma sum_range_pow_prime_pow_step {p k lam : ℕ} (hp : p.Prime) (hk : 0 < k) (hlam : 1 ≤ lam)
    (hpar : p ≠ 2 ∨ Even k) :
    ∑ i ∈ range (p ^ (lam + 1)), i ^ k ≡
      p * ∑ i ∈ range (p ^ lam), i ^ k [MOD p ^ (lam + 1)] := by
  rw [← ZMod.natCast_eq_natCast_iff]
  have hmul : p ^ (lam + 1) = p * p ^ lam := by rw [pow_succ, mul_comm]
  have hsplit : ∑ i ∈ range (p ^ (lam + 1)), i ^ k =
      ∑ a ∈ range p, ∑ b ∈ range (p ^ lam), (a * p ^ lam + b) ^ k := by
    rw [hmul]
    generalize p ^ lam = M
    clear hpar hlam hk hp hmul
    induction p with
    | zero => simp
    | succ n ih =>
      rw [add_mul, one_mul, sum_range_add, sum_range_succ, ih]
  rw [hsplit]
  have hmod_term : ∀ a b : ℕ,
      (((a * p ^ lam + b) ^ k : ℕ) : ZMod (p ^ (lam + 1))) =
        (b : ZMod (p ^ (lam + 1))) ^ k +
          (k : ZMod (p ^ (lam + 1))) * (a : ZMod (p ^ (lam + 1))) *
            (p ^ lam : ZMod (p ^ (lam + 1))) * (b : ZMod (p ^ (lam + 1))) ^ (k - 1) := by
    intro a b
    have hbin : (b + a * p ^ lam) ^ k =
        ∑ j ∈ range (k + 1), (a * p ^ lam) ^ j * b ^ (k - j) * k.choose j := by
      simpa [add_comm] using add_pow (a * p ^ lam) b k
    rw [add_comm (a * p ^ lam) b, hbin, Nat.cast_sum]
    have hsplit2 : ∑ j ∈ range (k + 1),
          (((a * p ^ lam) ^ j * b ^ (k - j) * k.choose j : ℕ) : ZMod (p ^ (lam + 1))) =
        ((b ^ k : ℕ) : ZMod (p ^ (lam + 1))) +
          (((a * p ^ lam) * b ^ (k - 1) * k : ℕ) : ZMod (p ^ (lam + 1))) := by
      rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot (Nat.zero_lt_succ k)]
      rw [sum_eq_sum_Ico_succ_bot (by omega : 1 < k + 1)]
      have htail : ∑ j ∈ Ico 2 (k + 1),
            (((a * p ^ lam) ^ j * b ^ (k - j) * k.choose j : ℕ) : ZMod (p ^ (lam + 1))) = 0 := by
        refine sum_eq_zero fun j hj => ?_
        have hj2 : 2 ≤ j := (mem_Ico.mp hj).1
        rw [ZMod.natCast_eq_zero_iff]
        have hd1 : p ^ (lam + 1) ∣ (p ^ lam) ^ j := by
          rw [← pow_mul]
          exact Nat.pow_dvd_pow p (by nlinarith)
        have hd2 : (p ^ lam) ^ j ∣ (a * p ^ lam) ^ j := by
          rw [mul_pow]
          exact dvd_mul_left _ _
        exact dvd_trans (dvd_trans hd1 hd2) (dvd_mul_of_dvd_left (dvd_mul_right _ _) _)
      rw [htail, add_zero]
      simp [Nat.choose_zero_right, Nat.choose_one_right]
    rw [hsplit2]
    push_cast
    ring
  rw [Nat.cast_sum]
  simp_rw [Nat.cast_sum, hmod_term]
  simp_rw [sum_add_distrib]
  have hfirst : ∑ _a ∈ range p, ∑ b ∈ range (p ^ lam), (b : ZMod (p ^ (lam + 1))) ^ k =
      ((p * ∑ i ∈ range (p ^ lam), i ^ k : ℕ) : ZMod (p ^ (lam + 1))) := by
    rw [sum_const, card_range, nsmul_eq_mul]
    push_cast
    rfl
  rw [hfirst]
  suffices hzero : ∑ a ∈ range p, ∑ b ∈ range (p ^ lam),
      (k : ZMod (p ^ (lam + 1))) * (a : ZMod (p ^ (lam + 1))) *
        (p ^ lam : ZMod (p ^ (lam + 1))) * (b : ZMod (p ^ (lam + 1))) ^ (k - 1) = 0 by
    rw [hzero, add_zero]
  have hfact : ∑ a ∈ range p, ∑ b ∈ range (p ^ lam),
      (k : ZMod (p ^ (lam + 1))) * (a : ZMod (p ^ (lam + 1))) *
        (p ^ lam : ZMod (p ^ (lam + 1))) * (b : ZMod (p ^ (lam + 1))) ^ (k - 1) =
      ((k * (∑ a ∈ range p, a) * p ^ lam : ℕ) : ZMod (p ^ (lam + 1))) *
        ∑ b ∈ range (p ^ lam), (b : ZMod (p ^ (lam + 1))) ^ (k - 1) := by
    push_cast
    rw [mul_sum, sum_comm]
    refine sum_congr rfl fun b _ => ?_
    rw [mul_sum, sum_mul, sum_mul]
  rw [hfact]
  suffices hdvd : p ^ (lam + 1) ∣ k * (∑ a ∈ range p, a) * p ^ lam by
    rw [(ZMod.natCast_eq_zero_iff _ _).mpr hdvd, zero_mul]
  rw [pow_succ, mul_comm (p ^ lam) p]
  have hsum_a : 2 * ∑ a ∈ range p, a = p * (p - 1) := by
    have := Finset.sum_range_id_mul_two p
    linarith
  have hd : p ∣ k * ∑ a ∈ range p, a := by
    rcases hpar with hp2 | heven
    · have hodd : Odd p := hp.odd_of_ne_two hp2
      obtain ⟨r, hr⟩ := hodd
      have hdiv : ∑ a ∈ range p, a = p * r := by
        have hpm1 : p - 1 = 2 * r := by omega
        rw [hpm1] at hsum_a
        linarith
      rw [hdiv]
      exact dvd_mul_of_dvd_right (dvd_mul_right p r) k
    · obtain ⟨t, rfl⟩ := heven
      have hdiv : (t + t) * ∑ a ∈ range p, a = t * (p * (p - 1)) := by
        calc (t + t) * ∑ a ∈ range p, a = t * (2 * ∑ a ∈ range p, a) := by ring
          _ = t * (p * (p - 1)) := by rw [hsum_a]
      rw [hdiv]
      exact dvd_mul_of_dvd_right (dvd_mul_right p _) t
  exact Nat.mul_dvd_mul_right hd (p ^ lam)

lemma sum_range_pow_prime_pow_dvd {p k lam : ℕ} (hp : p.Prime) (hk : 0 < k) (hlam : 1 ≤ lam)
    (hdvd : p - 1 ∣ k) (hpar : p ≠ 2 ∨ Even k) :
    p ^ lam ∣ (∑ i ∈ range (p ^ lam), i ^ k) + p ^ (lam - 1) := by
  induction lam with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [zero_add, pow_one, Nat.sub_self, pow_zero]
      have : Fact p.Prime := ⟨hp⟩
      rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_one,
        sum_range_eq_sum_univ_zmod, sum_pow_zmod_eq_neg_one_of_dvd hk hdvd]
      ring
    · have ih' := ih hn
      have hstep := sum_range_pow_prime_pow_step hp hk hn hpar
      have hmul : p ^ (n + 1) ∣ p * (∑ i ∈ range (p ^ n), i ^ k) + p ^ n := by
        have h1 : p * ((∑ i ∈ range (p ^ n), i ^ k) + p ^ (n - 1)) =
            p * (∑ i ∈ range (p ^ n), i ^ k) + p ^ n := by
          rw [mul_add, ← pow_succ', Nat.sub_add_cancel hn]
        rw [← h1, pow_succ']
        exact Nat.mul_dvd_mul_left p ih'
      rw [Nat.add_sub_cancel]
      have hmod : (∑ i ∈ range (p ^ (n + 1)), i ^ k) + p ^ n ≡
          p * (∑ i ∈ range (p ^ n), i ^ k) + p ^ n [MOD p ^ (n + 1)] :=
        hstep.add_right _
      exact (Nat.ModEq.dvd_iff hmod (dvd_refl _)).mpr hmul

lemma not_dvd_m_of_sub_one_dvd_k {k m p : ℕ} (hk : 0 < k) (hm : 0 < m) (heven : Even k)
    (heq : ErdosMoser.powerSum k m = m ^ k) (hp : p.Prime) (hpk : p - 1 ∣ k) :
    ¬ p ∣ m := by
  intro hpm
  have : Fact p.Prime := ⟨hp⟩
  have hpar : p ≠ 2 ∨ Even k := Or.inr heven
  let lam := padicValNat p m
  have hlam_pos : 1 ≤ lam := one_le_padicValNat_of_dvd hm.ne' hpm
  have hpow_dvd : p ^ lam ∣ m := pow_padicValNat_dvd
  have hnot_succ : ¬ p ^ (lam + 1) ∣ m := pow_succ_padicValNat_not_dvd hm.ne'
  obtain ⟨q, hq⟩ := hpow_dvd
  have hpq : ¬ p ∣ q := by
    intro hd
    obtain ⟨r, rfl⟩ := hd
    apply hnot_succ
    exact ⟨r, by rw [hq, pow_succ]; ring⟩
  rw [powerSum_eq_range hk] at heq
  have hmul_mod : ∑ i ∈ range m, i ^ k ≡ q * ∑ i ∈ range (p ^ lam), i ^ k [MOD p ^ lam] := by
    rw [hq, mul_comm]
    exact sum_range_pow_mul_mod q (p ^ lam) k
  have hmk_dvd : p ^ lam ∣ m ^ k := by
    have h1 : (p ^ lam) ^ k ∣ m ^ k := pow_dvd_pow_of_dvd ⟨q, hq⟩ k
    exact dvd_trans (dvd_pow_self _ hk.ne') h1
  have hsum_dvd : p ^ lam ∣ q * ∑ i ∈ range (p ^ lam), i ^ k := by
    rw [← heq] at hmk_dvd
    exact (Nat.ModEq.dvd_iff hmul_mod (dvd_refl _)).mp hmk_dvd
  have hstep := sum_range_pow_prime_pow_dvd hp hk hlam_pos hpk hpar
  have hqstep : p ^ lam ∣ q * (∑ i ∈ range (p ^ lam), i ^ k) + q * p ^ (lam - 1) := by
    rw [← mul_add]
    exact dvd_mul_of_dvd_right hstep q
  have hqp : p ^ lam ∣ q * p ^ (lam - 1) := (Nat.dvd_add_right hsum_dvd).mp hqstep
  have hpow_eq : p ^ lam = p * p ^ (lam - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hlam_pos]
  rw [hpow_eq] at hqp
  have hdvd_q : p ∣ q := by
    have hpos : 0 < p ^ (lam - 1) := pow_pos hp.pos _
    exact (Nat.mul_dvd_mul_iff_right hpos).mp hqp
  exact hpq hdvd_q

lemma odd_m {k m : ℕ} (hk : 0 < k) (hm : 0 < m) (heven : Even k)
    (heq : ErdosMoser.powerSum k m = m ^ k) : Odd m := by
  have h2 : ¬ 2 ∣ m := not_dvd_m_of_sub_one_dvd_k hk hm heven heq Nat.prime_two (by simp)
  exact Nat.odd_iff.mpr (by omega)

lemma three_not_dvd_m {k m : ℕ} (hk : 0 < k) (hm : 0 < m) (heven : Even k)
    (heq : ErdosMoser.powerSum k m = m ^ k) : ¬ 3 ∣ m := by
  have h2k : 2 ∣ k := even_iff_two_dvd.mp heven
  exact not_dvd_m_of_sub_one_dvd_k hk hm heven heq Nat.prime_three h2k

/- ### Section 3: Unified prime-power congruence, √m-smoothness, and exact 2-adic valuation -/

lemma card_range_not_dvd {m p : ℕ} (hp : 0 < p) (hpm : ¬ p ∣ m) :
    (range m |>.filter (fun i => ¬ p ∣ i)).card = m - 1 - m / p := by
  have hdiv_card : (range m |>.filter (fun i => p ∣ i)).card = m / p + 1 := by
    have hbij : (range m |>.filter (fun i => p ∣ i)) = (range (m / p + 1)).image (fun j => j * p) := by
      ext x
      simp only [mem_filter, mem_range, mem_image]
      constructor
      · rintro ⟨hxm, ⟨j, rfl⟩⟩
        refine ⟨j, ?_, mul_comm j p⟩
        have h1 : p * j < p * (m / p + 1) := by
          have := Nat.lt_mul_div_succ m hp
          omega
        exact Nat.lt_of_mul_lt_mul_left h1
      · rintro ⟨j, hj, rfl⟩
        refine ⟨?_, ⟨j, mul_comm j p⟩⟩
        have hmod : 0 < m % p := Nat.pos_of_ne_zero (fun h => hpm (Nat.dvd_of_mod_eq_zero h))
        have hdm := Nat.div_add_mod m p
        have hjle : j ≤ m / p := Nat.lt_succ_iff.mp hj
        have hmul : j * p ≤ (m / p) * p := Nat.mul_le_mul_right p hjle
        nlinarith
    rw [hbij, card_image_of_injective _ (fun a b h => Nat.eq_of_mul_eq_mul_right hp h), card_range]
  have hsum := card_filter_add_card_filter_not (s := range m) (p := fun i => p ∣ i)
  rw [card_range, hdiv_card] at hsum
  omega

lemma add_one_le_pow_of_three_le {p n : ℕ} (hp : 3 ≤ p) (hn : 1 ≤ n) : n + 1 ≤ p ^ n := by
  induction n with
  | zero => omega
  | succ r ih =>
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · simp; omega
    · have ih' := ih hr
      have h1 : 1 ≤ p ^ r := Nat.one_le_pow r p (by omega)
      calc r + 1 + 1 ≤ p ^ r + 1 := by omega
        _ ≤ p ^ r * 3 := by omega
        _ ≤ p ^ r * p := Nat.mul_le_mul_left _ hp
        _ = p ^ (r + 1) := (pow_succ p r).symm

lemma unified_prime_pow_congr {k m p : ℕ} (hk : 0 < k) (hm : 0 < m) (heven : Even k)
    (heq : ErdosMoser.powerSum k m = m ^ k) (hp : p.Prime) (hp2 : p ≠ 2) (hpk : p - 1 ∣ k) :
    ((p - 1) * m + m % p) ≡ 2 * p [MOD p ^ (padicValNat p k + 2)] := by
  have hkl : 2 ≤ m := by
    have := krzysztofek_lower hk hm heven heq
    omega
  set a := padicValNat p k
  have hpm : ¬ p ∣ m := not_dvd_m_of_sub_one_dvd_k hk hm heven heq hp hpk
  have hpa_dvd : p ^ a ∣ k := pow_padicValNat_dvd
  have hcop : Nat.Coprime (p ^ a) (p - 1) := by
    refine Nat.Coprime.pow_left a ?_
    have hp1 : p = (p - 1) + 1 := (Nat.sub_add_cancel hp.one_le).symm
    rw [hp1]
    exact Nat.coprime_self_add_left.mpr (Nat.coprime_one_left _)
  have htot_dvd : Nat.totient (p ^ (a + 1)) ∣ k := by
    rw [Nat.totient_prime_pow hp (Nat.succ_pos a), Nat.succ_sub_one]
    exact hcop.mul_dvd_of_dvd_of_dvd hpa_dvd hpk
  have ha_le : a + 1 ≤ k := by
    rcases Nat.eq_zero_or_pos a with ha0 | hapos
    · omega
    · have hp3 : 3 ≤ p := by have := hp.two_le; omega
      exact le_trans (add_one_le_pow_of_three_le hp3 hapos) (Nat.le_of_dvd hk hpa_dvd)
  have hpow_one : ∀ i : ℕ, ¬ p ∣ i → i ^ k ≡ 1 [MOD p ^ (a + 1)] := by
    intro i hpi
    have hci : Nat.Coprime i (p ^ (a + 1)) :=
      ((hp.coprime_iff_not_dvd.mpr hpi).symm).pow_right (a + 1)
    obtain ⟨u, hu⟩ := htot_dvd
    rw [hu, pow_mul]
    have h1 := Nat.ModEq.pow_totient hci
    simpa [one_pow] using h1.pow u
  have hpow_zero : ∀ i : ℕ, p ∣ i → i ^ k ≡ 0 [MOD p ^ (a + 1)] := by
    intro i hpi
    rw [Nat.modEq_zero_iff_dvd]
    exact dvd_trans (Nat.pow_dvd_pow p ha_le) (pow_dvd_pow_of_dvd hpi k)
  rw [powerSum_eq_range hk] at heq
  have hsum_mod : ∑ i ∈ range m, i ^ k ≡
      (range m |>.filter (fun i => ¬ p ∣ i)).card [MOD p ^ (a + 1)] := by
    rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_sum]
    have h1 : ∀ i ∈ range m, ((i ^ k : ℕ) : ZMod (p ^ (a + 1))) =
        if ¬ p ∣ i then 1 else 0 := by
      intro i _
      by_cases hi : p ∣ i
      · rw [if_neg (not_not.mpr hi)]
        exact_mod_cast (ZMod.natCast_eq_natCast_iff _ _ _).mpr (hpow_zero i hi)
      · rw [if_pos hi]
        exact_mod_cast (ZMod.natCast_eq_natCast_iff _ _ _).mpr (hpow_one i hi)
    rw [sum_congr rfl h1, sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul, mul_one]
  rw [card_range_not_dvd hp.pos hpm] at hsum_mod
  have hm_mod : m ^ k ≡ 1 [MOD p ^ (a + 1)] := hpow_one m hpm
  have hcount_mod : m - 1 - m / p ≡ 1 [MOD p ^ (a + 1)] := by
    rw [← heq] at hm_mod
    exact hsum_mod.symm.trans hm_mod
  have hsub_ge : m / p + 1 ≤ m := by
    have hp2' : 2 ≤ p := hp.two_le
    have hdm := Nat.div_add_mod m p
    have hmod_pos : 1 ≤ m % p := Nat.pos_of_ne_zero (fun h => hpm (Nat.dvd_of_mod_eq_zero h))
    nlinarith
  have hmul_mod : p * (m - 1 - m / p) ≡ p * 1 [MOD p ^ (a + 2)] := by
    have hp_pow : p ^ (a + 2) = p * p ^ (a + 1) := by rw [pow_succ, mul_comm]
    rw [hp_pow]
    exact Nat.ModEq.mul_left' p hcount_mod
  have hrewrite : p * (m - 1 - m / p) + p = (p - 1) * m + m % p := by
    have hdm : p * (m / p) + m % p = m := Nat.div_add_mod m p
    have hp1 : 1 ≤ p := hp.one_le
    have hsub1 : (m - 1 - m / p) + 1 = m - m / p := by omega
    calc p * (m - 1 - m / p) + p = p * ((m - 1 - m / p) + 1) := by ring
      _ = p * (m - m / p) := by rw [hsub1]
      _ = p * m - p * (m / p) := Nat.mul_sub p m (m / p)
      _ = p * m - (m - m % p) := by congr 1; omega
      _ = (p - 1) * m + m % p := by
        have hle1 : m % p ≤ m := Nat.mod_le m p
        have hpm_eq : p * m = (p - 1) * m + m := by
          conv_lhs => rw [← Nat.sub_add_cancel hp1]
          ring
        omega
  have hfinal := hmul_mod.add_right p
  rw [hrewrite, mul_one, ← two_mul] at hfinal
  simpa [mul_comm] using hfinal

lemma sqrt_m_smooth {k m p : ℕ} (hk : 0 < k) (hm : 0 < m) (heven : Even k)
    (heq : ErdosMoser.powerSum k m = m ^ k) (hp : p.Prime) (hp2 : p ≠ 2) (hpk : p - 1 ∣ k) :
    p ^ 2 ≤ m ∨ m = p ^ 2 - p + 1 := by
  by_contra h
  push Not at h
  rcases h with ⟨hlt, hne⟩
  have hcong := unified_prime_pow_congr hk hm heven heq hp hp2 hpk
  have hpm : ¬ p ∣ m := not_dvd_m_of_sub_one_dvd_k hk hm heven heq hp hpk
  have hodd : Odd m := odd_m hk hm heven heq
  have hp_odd : Odd p := hp.odd_of_ne_two hp2
  have hmod2 : ((p - 1) * m + m % p) ≡ 2 * p [MOD p ^ 2] :=
    hcong.of_dvd (Nat.pow_dvd_pow p (by omega))
  set q := m / p
  set t := m % p
  have ht_pos : 1 ≤ t := Nat.pos_of_ne_zero (fun hz => hpm (Nat.dvd_of_mod_eq_zero hz))
  have ht_lt : t < p := Nat.mod_lt m hp.pos
  have hdm : p * q + t = m := Nat.div_add_mod m p
  have hq_lt : q < p := by
    by_contra hge
    push Not at hge
    have : p * p ≤ p * q := Nat.mul_le_mul_left p hge
    nlinarith
  have h1 : (p - 1) * m + t + p * (q + 2) = p * (p * q + t) + 2 * p := by
    have hp1 : 1 ≤ p := hp.one_le
    have hpm_eq : (p - 1) * m + m = p * m := by
      conv_rhs => rw [← Nat.sub_add_cancel hp1]
      ring
    calc (p - 1) * m + t + p * (q + 2)
        = (p - 1) * m + (p * q + t) + 2 * p := by ring
      _ = (p - 1) * m + m + 2 * p := by rw [hdm]
      _ = p * m + 2 * p := by rw [hpm_eq]
      _ = p * (p * q + t) + 2 * p := by rw [hdm]
  have h2 : p * (q + 2) + 2 * p ≡ p * (p * q + t) + 2 * p [MOD p ^ 2] := by
    have h2' : 2 * p + p * (q + 2) ≡ (p - 1) * m + t + p * (q + 2) [MOD p ^ 2] :=
      hmod2.symm.add_right _
    rw [h1, add_comm (2 * p)] at h2'
    exact h2'
  have h3 : p * (q + 2) ≡ p * (p * q + t) [MOD p ^ 2] :=
    Nat.ModEq.add_right_cancel' (2 * p) h2
  have h4 : q + 2 ≡ p * q + t [MOD p] := by
    rw [sq] at h3
    exact Nat.ModEq.mul_left_cancel' hp.ne_zero h3
  have h5 : q + 2 ≡ t [MOD p] := by
    have hpq0 : p * q + t ≡ t [MOD p] := by
      simp [Nat.ModEq]
    exact h4.trans hpq0
  rcases Nat.eq_or_lt_of_le ht_pos with ht1 | ht2
  · rw [← ht1] at h5
    have hqp : q = p - 1 := by
      have h6 : (q + 2) % p = 1 % p := h5
      rw [Nat.mod_eq_of_lt hp.one_lt] at h6
      have hp3 : 3 ≤ p := by have := hp.two_le; omega
      rcases lt_or_ge (q + 2) p with hltp | hgep
      · rw [Nat.mod_eq_of_lt hltp] at h6; linarith
      · have hsub : q + 2 - p < p := by omega
        rw [Nat.mod_eq_sub_mod hgep, Nat.mod_eq_of_lt hsub] at h6
        omega
    apply hne
    have hsq : p * (p - 1) = p ^ 2 - p := by
      rw [Nat.mul_sub, sq, mul_one]
    rw [← hdm, hqp, ← ht1, hsq]
  · have hqt : q + 2 = t := by
      have h6 : (q + 2) % p = t % p := h5
      rw [Nat.mod_eq_of_lt ht_lt] at h6
      rcases lt_or_ge (q + 2) p with hltp | hgep
      · rw [Nat.mod_eq_of_lt hltp] at h6; exact h6
      · have hsub : q + 2 - p < p := by omega
        rw [Nat.mod_eq_sub_mod hgep, Nat.mod_eq_of_lt hsub] at h6
        omega
    have heven_m : Even m := by
      obtain ⟨r, hr⟩ := hp_odd
      refine ⟨q * (r + 1) + 1, ?_⟩
      calc m = p * q + t := hdm.symm
        _ = (2 * r + 1) * q + (q + 2) := by rw [hr, ← hqt]
        _ = q * (r + 1) + 1 + (q * (r + 1) + 1) := by ring
    exact Nat.not_even_iff_odd.mpr hodd heven_m

-- Exact 2-adic LTE helpers
lemma pow_two_pow_mod_one {x a : ℕ} (ha : 1 ≤ a) (hx : x % 8 = 1 ∨ x % 8 = 7) :
    x ^ (2 ^ a) ≡ 1 [MOD 2 ^ (a + 3)] := by
  induction a with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · change x ^ 2 ≡ 1 [MOD 16]
      have h16 : x % 16 = 1 ∨ x % 16 = 7 ∨ x % 16 = 9 ∨ x % 16 = 15 := by omega
      rw [Nat.ModEq, Nat.pow_mod]
      rcases h16 with h | h | h | h <;> rw [h]
    · have ih' := ih hn
      rw [pow_succ 2 n, pow_mul]
      obtain ⟨c, hc⟩ : ∃ c, x ^ (2 ^ n) = 1 + c * 2 ^ (n + 3) := by
        have hpos : 1 ≤ x ^ (2 ^ n) := Nat.one_le_pow _ _ (by omega)
        have hd : 2 ^ (n + 3) ∣ x ^ (2 ^ n) - 1 :=
          (Nat.modEq_iff_dvd' hpos).mp ih'.symm
        obtain ⟨c, hc⟩ := hd
        rw [Nat.sub_eq_iff_eq_add hpos] at hc
        exact ⟨c, by linarith⟩
      rw [hc]
      have hsq : (1 + c * 2 ^ (n + 3)) ^ 2 =
          1 + (c * 2 ^ (n + 4) + c ^ 2 * 2 ^ (2 * n + 6)) := by
        have h1 : 2 ^ (n + 4) = 2 * 2 ^ (n + 3) := by rw [pow_succ, mul_comm]
        have h2 : 2 ^ (2 * n + 6) = (2 ^ (n + 3)) ^ 2 := by rw [← pow_mul]; congr 1; omega
        rw [h1, h2]
        ring
      rw [hsq]
      have hd1 : 2 ^ (n + 4) ∣ c * 2 ^ (n + 4) := dvd_mul_left _ _
      have hd2 : 2 ^ (n + 4) ∣ c ^ 2 * 2 ^ (2 * n + 6) :=
        dvd_mul_of_dvd_right (Nat.pow_dvd_pow 2 (by omega)) _
      have hd : 2 ^ (n + 4) ∣ c * 2 ^ (n + 4) + c ^ 2 * 2 ^ (2 * n + 6) := dvd_add hd1 hd2
      simpa using (Nat.modEq_zero_iff_dvd.mpr hd).add_left 1

lemma pow_two_pow_mod_half {x a : ℕ} (ha : 1 ≤ a) (hx : x % 8 = 3 ∨ x % 8 = 5) :
    x ^ (2 ^ a) ≡ 1 + 2 ^ (a + 2) [MOD 2 ^ (a + 3)] := by
  induction a with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · change x ^ 2 ≡ 9 [MOD 16]
      have h16 : x % 16 = 3 ∨ x % 16 = 5 ∨ x % 16 = 11 ∨ x % 16 = 13 := by omega
      rw [Nat.ModEq, Nat.pow_mod]
      rcases h16 with h | h | h | h <;> rw [h]
    · have ih' := ih hn
      rw [pow_succ 2 n, pow_mul]
      obtain ⟨c, hc⟩ : ∃ c, x ^ (2 ^ n) = 1 + 2 ^ (n + 2) + c * 2 ^ (n + 3) := by
        have hrem : x ^ (2 ^ n) % 2 ^ (n + 3) = 1 + 2 ^ (n + 2) := by
          have hlt : 1 + 2 ^ (n + 2) < 2 ^ (n + 3) := by
            have : 2 ^ (n + 3) = 2 * 2 ^ (n + 2) := by rw [pow_succ, mul_comm]
            have : 2 ≤ 2 ^ (n + 2) := by
              calc 2 = 2 ^ 1 := by norm_num
                _ ≤ 2 ^ (n + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
            omega
          rw [Nat.ModEq, Nat.mod_eq_of_lt hlt] at ih'
          exact ih'
        refine ⟨x ^ (2 ^ n) / 2 ^ (n + 3), ?_⟩
        have hdm := Nat.div_add_mod (x ^ (2 ^ n)) (2 ^ (n + 3))
        rw [hrem] at hdm
        linarith
      rw [hc]
      have hexp : (1 + 2 ^ (n + 2) + c * 2 ^ (n + 3)) ^ 2 =
          (1 + 2 ^ (n + 3)) +
          (2 ^ (2 * n + 4) + c * 2 ^ (n + 4) + c * 2 ^ (2 * n + 6) + c ^ 2 * 2 ^ (2 * n + 6)) := by
        have h2a : 2 ^ (n + 3) = 2 * 2 ^ (n + 2) := by rw [pow_succ, mul_comm]
        have h2b : 2 ^ (n + 4) = 2 * 2 ^ (n + 3) := by rw [pow_succ, mul_comm]
        have h2c : 2 ^ (2 * n + 4) = (2 ^ (n + 2)) ^ 2 := by rw [← pow_mul]; congr 1; omega
        have h2d : 2 ^ (2 * n + 6) = (2 ^ (n + 3)) ^ 2 := by rw [← pow_mul]; congr 1; omega
        rw [h2c, h2d, h2b, h2a]
        ring
      rw [hexp]
      have hdvd : 2 ^ (n + 4) ∣
          2 ^ (2 * n + 4) + c * 2 ^ (n + 4) + c * 2 ^ (2 * n + 6) + c ^ 2 * 2 ^ (2 * n + 6) := by
        refine dvd_add (dvd_add (dvd_add ?_ ?_) ?_) ?_
        · exact Nat.pow_dvd_pow 2 (by omega)
        · exact dvd_mul_left _ _
        · exact dvd_mul_of_dvd_right (Nat.pow_dvd_pow 2 (by omega)) _
        · exact dvd_mul_of_dvd_right (Nat.pow_dvd_pow 2 (by omega)) _
      simpa using (Nat.modEq_zero_iff_dvd.mpr hdvd).add_left (1 + 2 ^ (n + 3))

lemma one_add_half_pow_odd {a u : ℕ} (ha : 1 ≤ a) (hu : Odd u) :
    (1 + 2 ^ (a + 2)) ^ u ≡ 1 + 2 ^ (a + 2) [MOD 2 ^ (a + 3)] := by
  obtain ⟨r, rfl⟩ := hu
  induction r with
  | zero => simp [Nat.ModEq]
  | succ r ih =>
    have hpow : (1 + 2 ^ (a + 2)) ^ (2 * (r + 1) + 1) =
        (1 + 2 ^ (a + 2)) ^ (2 * r + 1) * (1 + 2 ^ (a + 2)) ^ 2 := by
      rw [← pow_add]
      congr 1
    rw [hpow]
    have hsq : (1 + 2 ^ (a + 2)) ^ 2 ≡ 1 [MOD 2 ^ (a + 3)] := by
      have h1 : (1 + 2 ^ (a + 2)) ^ 2 = 1 + (2 ^ (a + 3) + 2 ^ (2 * a + 4)) := by
        have ha1 : 2 ^ (a + 3) = 2 * 2 ^ (a + 2) := by rw [pow_succ, mul_comm]
        have ha2 : 2 ^ (2 * a + 4) = (2 ^ (a + 2)) ^ 2 := by rw [← pow_mul]; congr 1; omega
        rw [ha1, ha2]; ring
      rw [h1]
      have hd : 2 ^ (a + 3) ∣ 2 ^ (a + 3) + 2 ^ (2 * a + 4) :=
        dvd_add (dvd_refl _) (Nat.pow_dvd_pow 2 (by omega))
      simpa using (Nat.modEq_zero_iff_dvd.mpr hd).add_left 1
    simpa [mul_one] using ih.mul hsq

lemma add_three_le_two_pow {n : ℕ} (hn : 4 ≤ n) : n + 3 ≤ 2 ^ n := by
  induction n with
  | zero => omega
  | succ r ih =>
    rcases lt_or_ge r 4 with hr | hr
    · have hr3 : r = 3 := by omega
      subst hr3; norm_num
    · have ih' := ih hr
      rw [pow_succ]
      omega

lemma padicValNat_two_m_sub_three {k m : ℕ} (hk : 0 < k) (hm : 0 < m) (heven : Even k)
    (heq : ErdosMoser.powerSum k m = m ^ k) :
    padicValNat 2 (m - 3) = padicValNat 2 k + 3 := by
  have hk6 : 6 ≤ k := k_ge_six hk hm heven heq
  have hodd : Odd m := odd_m hk hm heven heq
  have hm_ge : 8 < m := by
    have := krzysztofek_lower hk hm heven heq
    omega
  set a := padicValNat 2 k
  have ha_pos : 1 ≤ a := one_le_padicValNat_of_dvd hk.ne' (even_iff_two_dvd.mp heven)
  have hpow_dvd : 2 ^ a ∣ k := pow_padicValNat_dvd
  obtain ⟨u, hu⟩ := hpow_dvd
  have hu_odd : Odd u := by
    rw [Nat.odd_iff]
    by_contra h2u
    have h2du : 2 ∣ u := by omega
    obtain ⟨v, rfl⟩ := h2du
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hdiv : 2 ^ (a + 1) ∣ k := ⟨v, by rw [hu, pow_succ]; ring⟩
    exact pow_succ_padicValNat_not_dvd (p := 2) hk.ne' hdiv
  have ha3_le : a + 3 ≤ k := by
    have h2a_le : 2 ^ a ≤ k := Nat.le_of_dvd hk ⟨u, hu⟩
    rcases lt_or_ge a 4 with hlt | hge
    · omega
    · exact le_trans (add_three_le_two_pow hge) h2a_le
  have hi_even : ∀ i : ℕ, 2 ∣ i → i ^ k ≡ 0 [MOD 2 ^ (a + 3)] := by
    intro i hi
    rw [Nat.modEq_zero_iff_dvd]
    exact dvd_trans (Nat.pow_dvd_pow 2 ha3_le) (pow_dvd_pow_of_dvd hi k)
  have hi_17 : ∀ i : ℕ, (i % 8 = 1 ∨ i % 8 = 7) → i ^ k ≡ 1 [MOD 2 ^ (a + 3)] := by
    intro i hi
    rw [hu, pow_mul]
    simpa [one_pow] using (pow_two_pow_mod_one ha_pos hi).pow u
  have hi_35 : ∀ i : ℕ, (i % 8 = 3 ∨ i % 8 = 5) → i ^ k ≡ 1 + 2 ^ (a + 2) [MOD 2 ^ (a + 3)] := by
    intro i hi
    rw [hu, pow_mul]
    exact ((pow_two_pow_mod_half ha_pos hi).pow u).trans (one_add_half_pow_odd ha_pos hu_odd)
  have hi_odd_mod2 : ∀ i : ℕ, ¬ 2 ∣ i → i ^ k ≡ 1 [MOD 2 ^ (a + 2)] := by
    intro i hi
    have hd : 2 ^ (a + 2) ∣ 2 ^ (a + 3) := Nat.pow_dvd_pow 2 (by omega)
    have h8 : i % 8 = 1 ∨ i % 8 = 3 ∨ i % 8 = 5 ∨ i % 8 = 7 := by omega
    rcases h8 with h | h | h | h
    · exact (hi_17 i (Or.inl h)).of_dvd hd
    · exact ((hi_35 i (Or.inl h)).of_dvd hd).trans (by
        simp [Nat.ModEq])
    · exact ((hi_35 i (Or.inr h)).of_dvd hd).trans (by
        simp [Nat.ModEq])
    · exact (hi_17 i (Or.inr h)).of_dvd hd
  rw [powerSum_eq_range hk] at heq
  have h2nm : ¬ 2 ∣ m := by
    obtain ⟨r, rfl⟩ := hodd
    omega
  have hsum_mod2 : ∑ i ∈ range m, i ^ k ≡ (m - 1) / 2 [MOD 2 ^ (a + 2)] := by
    have hcard : (range m |>.filter (fun i => ¬ 2 ∣ i)).card = (m - 1) / 2 := by
      have hc := card_range_not_dvd (by norm_num : 0 < 2) h2nm
      omega
    rw [← hcard, ← ZMod.natCast_eq_natCast_iff, Nat.cast_sum]
    have h1 : ∀ i ∈ range m, ((i ^ k : ℕ) : ZMod (2 ^ (a + 2))) =
        if ¬ 2 ∣ i then 1 else 0 := by
      intro i _
      by_cases hi : 2 ∣ i
      · rw [if_neg (not_not.mpr hi)]
        exact_mod_cast (ZMod.natCast_eq_natCast_iff _ _ _).mpr
          ((hi_even i hi).of_dvd (Nat.pow_dvd_pow 2 (by omega)))
      · rw [if_pos hi]
        exact_mod_cast (ZMod.natCast_eq_natCast_iff _ _ _).mpr (hi_odd_mod2 i hi)
    rw [sum_congr rfl h1, sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul, mul_one]
  have hm_mod2 : m ^ k ≡ 1 [MOD 2 ^ (a + 2)] := hi_odd_mod2 m h2nm
  have hhalf_mod : (m - 1) / 2 ≡ 1 [MOD 2 ^ (a + 2)] := by
    rw [← heq] at hm_mod2
    exact hsum_mod2.symm.trans hm_mod2
  have hm_mod8 : m % 8 = 3 := by
    have h4 : 4 ∣ 2 ^ (a + 2) := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ∣ 2 ^ (a + 2) := Nat.pow_dvd_pow 2 (by omega)
    have h4m := hhalf_mod.of_dvd h4
    have hrem : ((m - 1) / 2) % 4 = 1 := by simpa [Nat.ModEq] using h4m
    obtain ⟨r, rfl⟩ := hodd
    omega
  set q := m / 8
  have hmq : m = 8 * q + 3 := by omega
  have hblock : ∀ r : ℕ,
      ∑ j ∈ range 8, (8 * r + j) ^ k ≡ 4 [MOD 2 ^ (a + 3)] := by
    intro r
    rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_sum]
    simp only [sum_range_succ, sum_range_zero, zero_add]
    have h0 : (((8 * r + 0) ^ k : ℕ) : ZMod (2 ^ (a + 3))) = 0 := by
      simpa using (ZMod.natCast_eq_natCast_iff _ _ _).mpr (hi_even (8 * r + 0) ⟨4 * r, by ring⟩)
    have h1 : (((8 * r + 1) ^ k : ℕ) : ZMod (2 ^ (a + 3))) = 1 := by
      simpa using (ZMod.natCast_eq_natCast_iff _ _ _).mpr (hi_17 (8 * r + 1) (Or.inl (by omega)))
    have h2 : (((8 * r + 2) ^ k : ℕ) : ZMod (2 ^ (a + 3))) = 0 := by
      simpa using (ZMod.natCast_eq_natCast_iff _ _ _).mpr (hi_even (8 * r + 2) ⟨4 * r + 1, by ring⟩)
    have h3 : (((8 * r + 3) ^ k : ℕ) : ZMod (2 ^ (a + 3))) =
        ((1 + 2 ^ (a + 2) : ℕ) : ZMod (2 ^ (a + 3))) :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mpr (hi_35 (8 * r + 3) (Or.inl (by omega)))
    have h4 : (((8 * r + 4) ^ k : ℕ) : ZMod (2 ^ (a + 3))) = 0 := by
      simpa using (ZMod.natCast_eq_natCast_iff _ _ _).mpr (hi_even (8 * r + 4) ⟨4 * r + 2, by ring⟩)
    have h5 : (((8 * r + 5) ^ k : ℕ) : ZMod (2 ^ (a + 3))) =
        ((1 + 2 ^ (a + 2) : ℕ) : ZMod (2 ^ (a + 3))) :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mpr (hi_35 (8 * r + 5) (Or.inr (by omega)))
    have h6 : (((8 * r + 6) ^ k : ℕ) : ZMod (2 ^ (a + 3))) = 0 := by
      simpa using (ZMod.natCast_eq_natCast_iff _ _ _).mpr (hi_even (8 * r + 6) ⟨4 * r + 3, by ring⟩)
    have h7 : (((8 * r + 7) ^ k : ℕ) : ZMod (2 ^ (a + 3))) = 1 := by
      simpa using (ZMod.natCast_eq_natCast_iff _ _ _).mpr (hi_17 (8 * r + 7) (Or.inr (by omega)))
    rw [h0, h1, h2, h3, h4, h5, h6, h7]
    push_cast
    have h2p : (2 : ZMod (2 ^ (a + 3))) * (2 ^ (a + 2) : ZMod (2 ^ (a + 3))) = 0 := by
      have : ((2 * 2 ^ (a + 2) : ℕ) : ZMod (2 ^ (a + 3))) = 0 := by
        rw [mul_comm, ← pow_succ, ZMod.natCast_self]
      simpa using this
    linear_combination h2p
  have hblocks : ∑ i ∈ range (8 * q), i ^ k ≡ 4 * q [MOD 2 ^ (a + 3)] := by
    clear hmq hm_mod8 hhalf_mod hm_mod2 hsum_mod2 heq hm_ge hodd h2nm
    induction q with
    | zero => simp [Nat.ModEq]
    | succ q ih =>
      rw [show 8 * (q + 1) = 8 * q + 8 by ring, sum_range_add]
      have := ih.add (hblock q)
      simpa [mul_add] using this
  have hsum_mod3 : ∑ i ∈ range m, i ^ k ≡ 4 * q + 1 [MOD 2 ^ (a + 3)] := by
    rw [hmq, sum_range_add]
    have hrem : ∑ j ∈ range 3, (8 * q + j) ^ k ≡ 1 [MOD 2 ^ (a + 3)] := by
      rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_sum]
      simp only [sum_range_succ, sum_range_zero, zero_add]
      have h0 : (((8 * q + 0) ^ k : ℕ) : ZMod (2 ^ (a + 3))) = 0 := by
        simpa using (ZMod.natCast_eq_natCast_iff _ _ _).mpr (hi_even (8 * q + 0) ⟨4 * q, by ring⟩)
      have h1 : (((8 * q + 1) ^ k : ℕ) : ZMod (2 ^ (a + 3))) = 1 := by
        simpa using (ZMod.natCast_eq_natCast_iff _ _ _).mpr (hi_17 (8 * q + 1) (Or.inl (by omega)))
      have h2 : (((8 * q + 2) ^ k : ℕ) : ZMod (2 ^ (a + 3))) = 0 := by
        simpa using (ZMod.natCast_eq_natCast_iff _ _ _).mpr (hi_even (8 * q + 2) ⟨4 * q + 1, by ring⟩)
      rw [h0, h1, h2]
      norm_num
    exact hblocks.add hrem
  have hm_mod3 : m ^ k ≡ 1 + 2 ^ (a + 2) [MOD 2 ^ (a + 3)] := hi_35 m (Or.inl hm_mod8)
  have h4q : 4 * q ≡ 2 ^ (a + 2) [MOD 2 ^ (a + 3)] := by
    rw [← heq] at hm_mod3
    have h1 : 4 * q + 1 ≡ 2 ^ (a + 2) + 1 [MOD 2 ^ (a + 3)] := by
      simpa [add_comm] using hsum_mod3.symm.trans hm_mod3
    exact Nat.ModEq.add_right_cancel' 1 h1
  have h8q : m - 3 ≡ 2 ^ (a + 3) [MOD 2 ^ (a + 4)] := by
    have h2 : 2 * (4 * q) ≡ 2 * 2 ^ (a + 2) [MOD 2 * 2 ^ (a + 3)] :=
      Nat.ModEq.mul_left' 2 h4q
    have hm3 : m - 3 = 2 * (4 * q) := by omega
    have hp1 : 2 * 2 ^ (a + 2) = 2 ^ (a + 3) := by rw [mul_comm, ← pow_succ]
    have hp2 : 2 * 2 ^ (a + 3) = 2 ^ (a + 4) := by rw [mul_comm, ← pow_succ]
    rwa [← hm3, hp1, hp2] at h2
  have hdvd_a3 : 2 ^ (a + 3) ∣ m - 3 := by
    have hd1 : 2 ^ (a + 3) ∣ 2 ^ (a + 4) := Nat.pow_dvd_pow 2 (by omega)
    exact (Nat.ModEq.dvd_iff (h8q.of_dvd hd1) (dvd_refl _)).mpr (dvd_refl _)
  have hndvd_a4 : ¬ 2 ^ (a + 4) ∣ m - 3 := by
    intro hd
    have h0 : 2 ^ (a + 3) ≡ 0 [MOD 2 ^ (a + 4)] :=
      h8q.symm.trans (Nat.modEq_zero_iff_dvd.mpr hd)
    have hd2 : 2 ^ (a + 4) ∣ 2 ^ (a + 3) := Nat.modEq_zero_iff_dvd.mp h0
    have hle : 2 ^ (a + 4) ≤ 2 ^ (a + 3) := Nat.le_of_dvd (pow_pos (by norm_num) _) hd2
    have hlt : 2 ^ (a + 3) < 2 ^ (a + 4) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hm3_ne : m - 3 ≠ 0 := by omega
  have hge : a + 3 ≤ padicValNat 2 (m - 3) :=
    (padicValNat_dvd_iff_le hm3_ne).mp hdvd_a3
  have hlt : padicValNat 2 (m - 3) < a + 4 := by
    by_contra hge4
    push Not at hge4
    exact hndvd_a4 ((padicValNat_dvd_iff_le hm3_ne).mpr hge4)
  omega

lemma m_mod_sixteen {k m : ℕ} (hk : 0 < k) (hm : 0 < m) (heven : Even k)
    (heq : ErdosMoser.powerSum k m = m ^ k) : m % 16 = 3 := by
  have hv := padicValNat_two_m_sub_three hk hm heven heq
  have ha : 1 ≤ padicValNat 2 k := one_le_padicValNat_of_dvd hk.ne' (even_iff_two_dvd.mp heven)
  have hm_ge : 8 < m := by
    have := krzysztofek_lower hk hm heven heq
    have := k_ge_six hk hm heven heq
    omega
  have hdvd : 2 ^ 4 ∣ m - 3 :=
    dvd_trans (Nat.pow_dvd_pow 2 (by omega)) (pow_padicValNat_dvd (p := 2) (n := m - 3))
  omega

/- ### Section 4: Moser's four congruences, squarefreeness, and master inequality (19/6) -/

lemma sum_range_two_mul_add_one_zmod {n k : ℕ} (hk : 0 < k) (heven : Even k) :
    ((∑ i ∈ range (2 * n + 1), i ^ k : ℕ) : ZMod (2 * n + 1)) =
      2 * ((∑ i ∈ range (n + 1), i ^ k : ℕ) : ZMod (2 * n + 1)) := by
  have hsplit : ∑ i ∈ range (2 * n + 1), i ^ k =
      (∑ i ∈ range (n + 1), i ^ k) + ∑ i ∈ Ico (n + 1) (2 * n + 1), i ^ k := by
    rw [range_eq_Ico, ← sum_Ico_consecutive _ (Nat.zero_le (n + 1)) (by omega), ← range_eq_Ico]
  rw [hsplit, Nat.cast_add, two_mul ((∑ i ∈ range (n + 1), i ^ k : ℕ) : ZMod (2 * n + 1))]
  congr 1
  rw [Nat.cast_sum, Nat.cast_sum]
  have hzero : ∑ i ∈ range (n + 1), ((i ^ k : ℕ) : ZMod (2 * n + 1)) =
      ∑ i ∈ Ico 1 (n + 1), ((i ^ k : ℕ) : ZMod (2 * n + 1)) := by
    rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot (Nat.succ_pos n)]
    simp [Nat.zero_pow hk]
  rw [hzero]
  refine sum_bij (fun i _ => (2 * n + 1) - i) ?_ ?_ ?_ ?_
  · intro i hi
    simp only [mem_Ico] at hi ⊢
    omega
  · intro a ha b hb hab
    simp only [mem_Ico] at ha hb
    omega
  · intro j hj
    simp only [mem_Ico] at hj
    refine ⟨(2 * n + 1) - j, mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
  · intro i hi
    simp only [mem_Ico] at hi
    rw [Nat.cast_pow, Nat.cast_pow]
    have hneg : (((2 * n + 1 - i : ℕ) : ZMod (2 * n + 1))) = -(i : ZMod (2 * n + 1)) := by
      have h1 : ((2 * n + 1 - i : ℕ) : ZMod (2 * n + 1)) + (i : ZMod (2 * n + 1)) = 0 := by
        rw [← Nat.cast_add, Nat.sub_add_cancel (by omega : i ≤ 2 * n + 1), ZMod.natCast_self]
      exact eq_neg_of_add_eq_zero_left h1
    rw [hneg, heven.neg_pow]

lemma moser_m_sub_one {k m p : ℕ} (hk : 0 < k) (hm : 0 < m) (heven : Even k)
    (heq : ErdosMoser.powerSum k m = m ^ k) (hp : p.Prime) (hpdvd : p ∣ m - 1) :
    (p - 1 ∣ k) ∧ p ∣ (m - 1) / p + 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hm2 : 2 ≤ m := by
    have := krzysztofek_lower hk hm heven heq
    omega
  set q := (m - 1) / p
  have hmq : m - 1 = q * p := (Nat.div_mul_cancel hpdvd).symm
  rw [powerSum_eq_range hk] at heq
  have hsum : ((∑ i ∈ range m, i ^ k : ℕ) : ZMod p) = (q : ZMod p) * ∑ x : ZMod p, x ^ k := by
    have hm1 : m = q * p + 1 := by omega
    rw [hm1, sum_range_succ, Nat.cast_add]
    have hlast : (((q * p) ^ k : ℕ) : ZMod p) = 0 := by
      rw [Nat.cast_pow, Nat.cast_mul, ZMod.natCast_self, mul_zero, zero_pow hk.ne']
    rw [hlast, add_zero]
    have hmul := (ZMod.natCast_eq_natCast_iff _ _ p).mpr (sum_range_pow_mul_mod q p k)
    rw [hmul, Nat.cast_mul, sum_range_eq_sum_univ_zmod]
  have hmk : ((m ^ k : ℕ) : ZMod p) = 1 := by
    have hm1 : (m : ZMod p) = 1 := by
      have h1 : m = q * p + 1 := by omega
      rw [h1, Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, mul_zero, zero_add, Nat.cast_one]
    rw [Nat.cast_pow, hm1, one_pow]
  have hz : (q : ZMod p) * ∑ x : ZMod p, x ^ k = 1 := by
    rw [← hsum, heq, hmk]
  have hpk : p - 1 ∣ k := by
    by_contra hndvd
    rw [sum_pow_zmod_eq_zero_of_not_dvd hndvd, mul_zero] at hz
    exact zero_ne_one hz
  refine ⟨hpk, ?_⟩
  rw [sum_pow_zmod_eq_neg_one_of_dvd hk hpk] at hz
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_one]
  linear_combination -hz

lemma moser_m_add_one {k m p : ℕ} (hk : 0 < k) (_hm : 0 < m) (heven : Even k)
    (heq : ErdosMoser.powerSum k m = m ^ k) (hp : p.Prime) (hpdvd : p ∣ m + 1) :
    (p - 1 ∣ k) ∧ (p ≠ 2 → p ∣ (m + 1) / p + 2) := by
  have : Fact p.Prime := ⟨hp⟩
  rcases eq_or_ne p 2 with rfl | hp2
  · exact ⟨by simp, fun h => absurd rfl h⟩
  set q := (m + 1) / p
  have hmq : m + 1 = q * p := (Nat.div_mul_cancel hpdvd).symm
  rw [powerSum_eq_range hk] at heq
  have hsum : ((∑ i ∈ range (m + 1), i ^ k : ℕ) : ZMod p) = (q : ZMod p) * ∑ x : ZMod p, x ^ k := by
    rw [hmq]
    have hmul := (ZMod.natCast_eq_natCast_iff _ _ p).mpr (sum_range_pow_mul_mod q p k)
    rw [hmul, Nat.cast_mul, sum_range_eq_sum_univ_zmod]
  have hmk : ((∑ i ∈ range (m + 1), i ^ k : ℕ) : ZMod p) = 2 := by
    rw [sum_range_succ, heq, ← two_mul, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
    have hm_neg : (m : ZMod p) = -1 := by
      have h1 : (m : ZMod p) + 1 = 0 := by
        rw [← Nat.cast_one, ← Nat.cast_add, hmq, Nat.cast_mul, ZMod.natCast_self, mul_zero]
      exact eq_neg_of_add_eq_zero_left h1
    rw [hm_neg, heven.neg_pow, one_pow, mul_one]
  have hz : (q : ZMod p) * ∑ x : ZMod p, x ^ k = 2 := by
    rw [← hsum, hmk]
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro h2z
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h2z
    have := Nat.le_of_dvd (by norm_num) hd
    have := hp.two_le
    omega
  have hpk : p - 1 ∣ k := by
    by_contra hndvd
    rw [sum_pow_zmod_eq_zero_of_not_dvd hndvd, mul_zero] at hz
    exact h2ne hz.symm
  refine ⟨hpk, fun _ => ?_⟩
  rw [sum_pow_zmod_eq_neg_one_of_dvd hk hpk] at hz
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_ofNat]
  linear_combination -hz

lemma moser_two_m_sub_one {k m p : ℕ} (hk : 0 < k) (hm : 0 < m) (heven : Even k)
    (heq : ErdosMoser.powerSum k m = m ^ k) (hp : p.Prime) (hpdvd : p ∣ 2 * m - 1) :
    (p - 1 ∣ k) ∧ p ∣ (2 * m - 1) / p + 2 := by
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by
    intro h2
    subst h2
    omega
  set q := (2 * m - 1) / p
  have hmq : 2 * m - 1 = q * p := (Nat.div_mul_cancel hpdvd).symm
  have hrefl : ∑ i ∈ range (2 * m - 1), i ^ k ≡ 2 * m ^ k [MOD 2 * m - 1] := by
    have h1 : 2 * m - 1 = 2 * (m - 1) + 1 := by omega
    have h2 : m - 1 + 1 = m := by omega
    rw [← ZMod.natCast_eq_natCast_iff]
    rw [h1]
    have h3 := sum_range_two_mul_add_one_zmod (n := m - 1) hk heven
    rw [h2] at h3
    conv_rhs at h3 => rw [← powerSum_eq_range hk, heq]
    simpa [Nat.cast_mul] using h3
  have hmodp : ((∑ i ∈ range (2 * m - 1), i ^ k : ℕ) : ZMod p) = ((2 * m ^ k : ℕ) : ZMod p) :=
    (ZMod.natCast_eq_natCast_iff _ _ p).mpr (hrefl.of_dvd hpdvd)
  have hsum : ((∑ i ∈ range (2 * m - 1), i ^ k : ℕ) : ZMod p) =
      (q : ZMod p) * ∑ x : ZMod p, x ^ k := by
    rw [hmq]
    have hmul := (ZMod.natCast_eq_natCast_iff _ _ p).mpr (sum_range_pow_mul_mod q p k)
    rw [hmul, Nat.cast_mul, sum_range_eq_sum_univ_zmod]
  have hz : (q : ZMod p) * ∑ x : ZMod p, x ^ k = 2 * (m : ZMod p) ^ k := by
    rw [← hsum, hmodp]
    push_cast
    rfl
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro h2z
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h2z
    have := Nat.le_of_dvd (by norm_num) hd
    have := hp.two_le
    omega
  have hmne : (m : ZMod p) ≠ 0 := by
    intro hmz
    have hpm : p ∣ m := (ZMod.natCast_eq_zero_iff m p).mp hmz
    have h1 : p ∣ 1 := by
      have h2m : p ∣ 2 * m := dvd_mul_of_dvd_right hpm 2
      have hsub : 2 * m - (2 * m - 1) = 1 := by omega
      rw [← hsub]
      exact Nat.dvd_sub h2m hpdvd
    exact hp.not_dvd_one h1
  have hpk : p - 1 ∣ k := by
    by_contra hndvd
    rw [sum_pow_zmod_eq_zero_of_not_dvd hndvd, mul_zero] at hz
    have hprod_ne : (2 : ZMod p) * (m : ZMod p) ^ k ≠ 0 :=
      mul_ne_zero h2ne (pow_ne_zero k hmne)
    exact hprod_ne hz.symm
  refine ⟨hpk, ?_⟩
  rw [sum_pow_zmod_eq_neg_one_of_dvd hk hpk] at hz
  have hmk1 : (m : ZMod p) ^ k = 1 := by
    obtain ⟨u, hu⟩ := hpk
    rw [hu, pow_mul, ZMod.pow_card_sub_one_eq_one hmne, one_pow]
  rw [hmk1, mul_one] at hz
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_ofNat]
  linear_combination -hz

lemma moser_two_m_add_one {k m p : ℕ} (hk : 0 < k) (_hm : 0 < m) (heven : Even k)
    (heq : ErdosMoser.powerSum k m = m ^ k) (hp : p.Prime) (hpdvd : p ∣ 2 * m + 1) :
    (p - 1 ∣ k) ∧ p ∣ (2 * m + 1) / p + 4 := by
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by
    intro h2
    subst h2
    omega
  set q := (2 * m + 1) / p
  have hmq : 2 * m + 1 = q * p := (Nat.div_mul_cancel hpdvd).symm
  have hrefl : ∑ i ∈ range (2 * m + 1), i ^ k ≡ 4 * m ^ k [MOD 2 * m + 1] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    have h3 := sum_range_two_mul_add_one_zmod (n := m) hk heven
    conv_rhs at h3 => rw [sum_range_succ, ← powerSum_eq_range hk, heq]
    rw [h3]
    push_cast
    ring
  have hmodp : ((∑ i ∈ range (2 * m + 1), i ^ k : ℕ) : ZMod p) = ((4 * m ^ k : ℕ) : ZMod p) :=
    (ZMod.natCast_eq_natCast_iff _ _ p).mpr (hrefl.of_dvd hpdvd)
  have hsum : ((∑ i ∈ range (2 * m + 1), i ^ k : ℕ) : ZMod p) =
      (q : ZMod p) * ∑ x : ZMod p, x ^ k := by
    rw [hmq]
    have hmul := (ZMod.natCast_eq_natCast_iff _ _ p).mpr (sum_range_pow_mul_mod q p k)
    rw [hmul, Nat.cast_mul, sum_range_eq_sum_univ_zmod]
  have hz : (q : ZMod p) * ∑ x : ZMod p, x ^ k = 4 * (m : ZMod p) ^ k := by
    rw [← hsum, hmodp]
    push_cast
    rfl
  have h4ne : (4 : ZMod p) ≠ 0 := by
    intro h4z
    have hd : p ∣ 4 := (ZMod.natCast_eq_zero_iff 4 p).mp h4z
    have hd2 : p ∣ 2 := hp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 by simpa using hd)
    have := Nat.le_of_dvd (by norm_num) hd2
    have := hp.two_le
    omega
  have hmne : (m : ZMod p) ≠ 0 := by
    intro hmz
    have hpm : p ∣ m := (ZMod.natCast_eq_zero_iff m p).mp hmz
    have h1 : p ∣ 1 := by
      have h2m : p ∣ 2 * m := dvd_mul_of_dvd_right hpm 2
      exact (Nat.dvd_add_right h2m).mp hpdvd
    exact hp.not_dvd_one h1
  have hpk : p - 1 ∣ k := by
    by_contra hndvd
    rw [sum_pow_zmod_eq_zero_of_not_dvd hndvd, mul_zero] at hz
    have hprod_ne : (4 : ZMod p) * (m : ZMod p) ^ k ≠ 0 :=
      mul_ne_zero h4ne (pow_ne_zero k hmne)
    exact hprod_ne hz.symm
  refine ⟨hpk, ?_⟩
  rw [sum_pow_zmod_eq_neg_one_of_dvd hk hpk] at hz
  have hmk1 : (m : ZMod p) ^ k = 1 := by
    obtain ⟨u, hu⟩ := hpk
    rw [hu, pow_mul, ZMod.pow_card_sub_one_eq_one hmne, one_pow]
  rw [hmk1, mul_one] at hz
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_ofNat]
  linear_combination -hz

lemma squarefree_of_not_sq_dvd {n : ℕ} (_hn : n ≠ 0)
    (h : ∀ p : ℕ, p.Prime → ¬ p * p ∣ n) : Squarefree n := by
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hp hsq
  exact h p hp hsq

lemma squarefree_m_sub_one {k m : ℕ} (hk : 0 < k) (hm : 0 < m) (heven : Even k)
    (heq : ErdosMoser.powerSum k m = m ^ k) : Squarefree (m - 1) := by
  have hm2 : 2 ≤ m := by have := krzysztofek_lower hk hm heven heq; omega
  refine squarefree_of_not_sq_dvd (by omega) fun p hp hsq => ?_
  have hpdvd : p ∣ m - 1 := dvd_trans (dvd_mul_left p p) hsq
  have hmod := (moser_m_sub_one hk hm heven heq hp hpdvd).2
  have hpq : p ∣ (m - 1) / p := by
    obtain ⟨r, hr⟩ := hsq
    refine ⟨r, ?_⟩
    have h1 : (m - 1) / p = p * r := by
      rw [hr, mul_assoc, Nat.mul_div_cancel_left _ hp.pos]
    exact h1
  have h1 : p ∣ 1 := (Nat.dvd_add_right hpq).mp hmod
  exact hp.not_dvd_one h1

lemma squarefree_m_add_one_div_two {k m : ℕ} (hk : 0 < k) (hm : 0 < m) (heven : Even k)
    (heq : ErdosMoser.powerSum k m = m ^ k) : Squarefree ((m + 1) / 2) := by
  have hm16 := m_mod_sixteen hk hm heven heq
  refine squarefree_of_not_sq_dvd (by omega) fun p hp hsq => ?_
  rcases eq_or_ne p 2 with rfl | hp2
  · omega
  · have hpdvd2 : p * p ∣ m + 1 := by
      have h2 : 2 * ((m + 1) / 2) = m + 1 := by omega
      rw [← h2]
      exact dvd_mul_of_dvd_right hsq 2
    have hpdvd : p ∣ m + 1 := dvd_trans (dvd_mul_left p p) hpdvd2
    have hmod := (moser_m_add_one hk hm heven heq hp hpdvd).2 hp2
    have hpq : p ∣ (m + 1) / p := by
      obtain ⟨r, hr⟩ := hpdvd2
      exact ⟨r, by rw [hr, mul_assoc, Nat.mul_div_cancel_left _ hp.pos]⟩
    have h2 : p ∣ 2 := (Nat.dvd_add_right hpq).mp hmod
    have := Nat.le_of_dvd (by norm_num) h2
    have := hp.two_le
    omega

lemma moser_m_add_one_div_two_congr {k m p : ℕ} (hk : 0 < k) (hm : 0 < m) (heven : Even k)
    (heq : ErdosMoser.powerSum k m = m ^ k) (hp : p.Prime) (hpdvd : p ∣ (m + 1) / 2) :
    p ∣ ((m + 1) / 2) / p + 1 := by
  have hm16 := m_mod_sixteen hk hm heven heq
  rcases eq_or_ne p 2 with rfl | hp2
  · omega
  · have h2eq : 2 * ((m + 1) / 2) = m + 1 := by omega
    have hpdvd' : p ∣ m + 1 := by rw [← h2eq]; exact dvd_mul_of_dvd_right hpdvd 2
    have hmod := (moser_m_add_one hk hm heven heq hp hpdvd').2 hp2
    have hdiv : (m + 1) / p = 2 * (((m + 1) / 2) / p) := by
      obtain ⟨r, hr⟩ := hpdvd
      have h1 : m + 1 = p * (2 * r) := by linarith
      calc (m + 1) / p = p * (2 * r) / p := by rw [h1]
        _ = 2 * r := Nat.mul_div_cancel_left _ hp.pos
        _ = 2 * (p * r / p) := by rw [Nat.mul_div_cancel_left _ hp.pos]
        _ = 2 * (((m + 1) / 2) / p) := by rw [← hr]
    rw [hdiv, ← mul_add_one] at hmod
    have hcop : Nat.Coprime p 2 := hp.coprime_iff_not_dvd.mpr (fun hd => by
      have := Nat.le_of_dvd (by norm_num) hd; have := hp.two_le; omega)
    exact hcop.dvd_of_dvd_mul_left hmod

lemma squarefree_two_m_sub_one {k m : ℕ} (hk : 0 < k) (hm : 0 < m) (heven : Even k)
    (heq : ErdosMoser.powerSum k m = m ^ k) : Squarefree (2 * m - 1) := by
  refine squarefree_of_not_sq_dvd (by omega) fun p hp hsq => ?_
  have hpdvd : p ∣ 2 * m - 1 := dvd_trans (dvd_mul_left p p) hsq
  have hp2 : p ≠ 2 := by intro h; subst h; omega
  have hmod := (moser_two_m_sub_one hk hm heven heq hp hpdvd).2
  have hpq : p ∣ (2 * m - 1) / p := by
    obtain ⟨r, hr⟩ := hsq
    exact ⟨r, by rw [hr, mul_assoc, Nat.mul_div_cancel_left _ hp.pos]⟩
  have h2 : p ∣ 2 := (Nat.dvd_add_right hpq).mp hmod
  have := Nat.le_of_dvd (by norm_num) h2
  have := hp.two_le
  omega

lemma squarefree_two_m_add_one {k m : ℕ} (hk : 0 < k) (hm : 0 < m) (heven : Even k)
    (heq : ErdosMoser.powerSum k m = m ^ k) : Squarefree (2 * m + 1) := by
  refine squarefree_of_not_sq_dvd (by omega) fun p hp hsq => ?_
  have hpdvd : p ∣ 2 * m + 1 := dvd_trans (dvd_mul_left p p) hsq
  have hp2 : p ≠ 2 := by intro h; subst h; omega
  have hmod := (moser_two_m_add_one hk hm heven heq hp hpdvd).2
  have hpq : p ∣ (2 * m + 1) / p := by
    obtain ⟨r, hr⟩ := hsq
    exact ⟨r, by rw [hr, mul_assoc, Nat.mul_div_cancel_left _ hp.pos]⟩
  have h4 : p ∣ 4 := (Nat.dvd_add_right hpq).mp hmod
  have h2 : p ∣ 2 := hp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 by simpa using h4)
  have := Nat.le_of_dvd (by norm_num) h2
  have := hp.two_le
  omega

lemma egyptian_ge_one {N c : ℕ} (hN : 0 < N) (hc : 0 < c)
    (hsq : Squarefree N) (hmod : ∀ p ∈ N.primeFactors, p ∣ N / p + c) :
    ∃ I : ℕ, 1 ≤ I ∧ (∑ p ∈ N.primeFactors, (1 : ℚ) / p) + (c : ℚ) / N = I := by
  set T : ℕ := (∑ p ∈ N.primeFactors, N / p) + c
  have hprod : ∏ p ∈ N.primeFactors, p = N := Nat.prod_primeFactors_of_squarefree hsq
  have hdvd_each : ∀ p ∈ N.primeFactors, p ∣ T := by
    intro p hp
    have hsplit : ∑ q ∈ N.primeFactors, N / q = N / p + ∑ q ∈ N.primeFactors.erase p, N / q := by
      rw [add_comm, sum_erase_add _ _ hp]
    have hTeq : T = (N / p + c) + ∑ q ∈ N.primeFactors.erase p, N / q := by
      dsimp only [T]
      rw [hsplit]
      ring
    rw [hTeq]
    refine dvd_add (hmod p hp) (dvd_sum fun q hq => ?_)
    have hne : q ≠ p := ne_of_mem_erase hq
    have hqmem : q ∈ N.primeFactors := mem_of_mem_erase hq
    have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hqmem
    have hpdvd : p ∣ N := Nat.dvd_of_mem_primeFactors hp
    have hqdvd : q ∣ N := Nat.dvd_of_mem_primeFactors hqmem
    have hcop : Nat.Coprime p q := (Nat.coprime_primes hp_prime hq_prime).mpr hne.symm
    have hpq : p * q ∣ N := hcop.mul_dvd_of_dvd_of_dvd hpdvd hqdvd
    obtain ⟨r, hr⟩ := hpq
    exact ⟨r, by rw [hr, mul_comm p q, mul_assoc, Nat.mul_div_cancel_left _ hq_prime.pos]⟩
  have hNdvd : N ∣ T := by
    rw [← hprod]
    have haux : ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime ∧ p ∣ T) → (∏ p ∈ S, p) ∣ T := by
      intro S
      induction S using Finset.induction_on with
      | empty => intro _; simp
      | @insert a s has ih =>
        intro h
        rw [prod_insert has]
        have ha := h a (mem_insert_self a s)
        have hs := ih (fun p hp => h p (mem_insert_of_mem hp))
        have hcop : Nat.Coprime a (∏ p ∈ s, p) := by
          refine Nat.Coprime.prod_right fun p hp => ?_
          have hne : a ≠ p := fun heq => has (heq ▸ hp)
          exact (Nat.coprime_primes ha.1 (h p (mem_insert_of_mem hp)).1).mpr hne
        exact hcop.mul_dvd_of_dvd_of_dvd ha.2 hs
    exact haux N.primeFactors (fun p hp => ⟨Nat.prime_of_mem_primeFactors hp, hdvd_each p hp⟩)
  obtain ⟨I, hIT⟩ := hNdvd
  have hIpos : 1 ≤ I := by
    by_contra h0
    have hI0 : I = 0 := by omega
    rw [hI0, mul_zero] at hIT
    have : 0 < T := by dsimp only [T]; omega
    omega
  refine ⟨I, hIpos, ?_⟩
  have hNne : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  have hsumQ : (∑ p ∈ N.primeFactors, (1 : ℚ) / p) + (c : ℚ) / N = (T : ℚ) / N := by
    have h1 : (∑ p ∈ N.primeFactors, (1 : ℚ) / p) = (∑ p ∈ N.primeFactors, ((N / p : ℕ) : ℚ)) / N := by
      rw [sum_div]
      refine sum_congr rfl fun p hp => ?_
      have hpdvd : p ∣ N := Nat.dvd_of_mem_primeFactors hp
      have hpne : (p : ℚ) ≠ 0 := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
      rw [Nat.cast_div hpdvd hpne]
      field_simp
    rw [h1, ← add_div]
    congr 1
    dsimp only [T]
    push_cast
    rfl
  rw [hsumQ, hIT, Nat.cast_mul, mul_div_cancel_left₀ _ hNne]

lemma moser_M1_structure {k m : ℕ} (hk : 0 < k) (hm : 0 < m) (heven : Even k)
    (heq : ErdosMoser.powerSum k m = m ^ k) :
    12 ∣ (m ^ 2 - 1) * (4 * m ^ 2 - 1) ∧
    Squarefree ((m ^ 2 - 1) * (4 * m ^ 2 - 1) / 12) ∧
    (∀ p ∈ ((m ^ 2 - 1) * (4 * m ^ 2 - 1) / 12).primeFactors, p - 1 ∣ k) ∧
    (19 / 6 : ℚ) ≤
      (∑ p ∈ Nat.primeFactors ((m ^ 2 - 1) * (4 * m ^ 2 - 1) / 12), (1 : ℚ) / ((p : ℕ) : ℚ)) +
        1 / (m - 1 : ℚ) + 2 / (m + 1 : ℚ) + 2 / (2 * m - 1 : ℚ) + 4 / (2 * m + 1 : ℚ) := by
  have hm16 := m_mod_sixteen hk hm heven heq
  have h3nm := three_not_dvd_m hk hm heven heq
  have hm_ge : 8 < m := by
    have := krzysztofek_lower hk hm heven heq
    have := k_ge_six hk hm heven heq
    omega
  set A := m - 1
  set B := (m + 1) / 2
  set C := 2 * m - 1
  set D := 2 * m + 1
  have hA_pos : 0 < A := by omega
  have hB_pos : 0 < B := by omega
  have hC_pos : 0 < C := by omega
  have hD_pos : 0 < D := by omega
  have hsqA : Squarefree A := squarefree_m_sub_one hk hm heven heq
  have hsqB : Squarefree B := squarefree_m_add_one_div_two hk hm heven heq
  have hsqC : Squarefree C := squarefree_two_m_sub_one hk hm heven heq
  have hsqD : Squarefree D := squarefree_two_m_add_one hk hm heven heq
  have hprod_eq : (m ^ 2 - 1) * (4 * m ^ 2 - 1) = 2 * (A * B * C * D) := by
    have h2B : 2 * B = m + 1 := by omega
    have h1 : m ^ 2 - 1 = A * (m + 1) := by
      dsimp only [A]
      zify [show 1 ≤ m by omega, show 1 ≤ m ^ 2 by nlinarith]
      ring
    have h2 : 4 * m ^ 2 - 1 = C * D := by
      dsimp only [C, D]
      zify [show 1 ≤ 2 * m by omega, show 1 ≤ 4 * m ^ 2 by nlinarith]
      ring
    rw [h1, h2, ← h2B]
    ring
  have h6dvd : 6 ∣ A * B * C * D := by
    have h2A : 2 ∣ A := by omega
    have h3dvd : 3 ∣ A * B * C * D := by
      have hm3 : m % 3 = 1 ∨ m % 3 = 2 := by omega
      rcases hm3 with h3 | h3
      · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (by omega) _) _) _
      · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (by omega) _) _) _
    have hcop : Nat.Coprime 2 3 := by decide
    exact hcop.mul_dvd_of_dvd_of_dvd (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h2A _) _) _) h3dvd
  have h12dvd : 12 ∣ (m ^ 2 - 1) * (4 * m ^ 2 - 1) := by
    rw [hprod_eq]
    obtain ⟨r, hr⟩ := h6dvd
    exact ⟨r, by linarith⟩
  set M1 := (m ^ 2 - 1) * (4 * m ^ 2 - 1) / 12
  have hM1_eq : 6 * M1 = A * B * C * D := by
    obtain ⟨r, hr⟩ := h6dvd
    have h1 : M1 = r := by
      dsimp only [M1]
      rw [hprod_eq, hr]
      have : 2 * (6 * r) = 12 * r := by ring
      rw [this, Nat.mul_div_cancel_left _ (by norm_num)]
    linarith
  have hM1_pos : 0 < M1 := by
    have hpos : 0 < A * B * C * D := by positivity
    omega
  -- Check exact prime multiplicity in A * B * C * D for every prime p
  have hno_common_ge5 : ∀ p : ℕ, p.Prime → 5 ≤ p →
      ¬ (p ∣ A ∧ p ∣ B) ∧ ¬ (p ∣ A ∧ p ∣ C) ∧ ¬ (p ∣ A ∧ p ∣ D) ∧
      ¬ (p ∣ B ∧ p ∣ C) ∧ ¬ (p ∣ B ∧ p ∣ D) ∧ ¬ (p ∣ C ∧ p ∣ D) := by
    intro p hp hp5
    have h2B : 2 * B = m + 1 := by omega
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rintro ⟨hA, hB⟩
      have h1 : p ∣ 2 := by
        have h2 : p ∣ m + 1 := by rw [← h2B]; exact dvd_mul_of_dvd_right hB 2
        have hsub : (m + 1) - (m - 1) = 2 := by omega
        rw [← hsub]; exact Nat.dvd_sub h2 hA
      have := Nat.le_of_dvd (by norm_num) h1; omega
    · rintro ⟨hA, hC⟩
      have h1 : p ∣ 1 := by
        have h2 : p ∣ 2 * A := dvd_mul_of_dvd_right hA 2
        have hsub : C - 2 * A = 1 := by omega
        rw [← hsub]; exact Nat.dvd_sub hC h2
      exact hp.not_dvd_one h1
    · rintro ⟨hA, hD⟩
      have h1 : p ∣ 3 := by
        have h2 : p ∣ 2 * A := dvd_mul_of_dvd_right hA 2
        have hsub : D - 2 * A = 3 := by omega
        rw [← hsub]; exact Nat.dvd_sub hD h2
      have := Nat.le_of_dvd (by norm_num) h1; omega
    · rintro ⟨hB, hC⟩
      have h1 : p ∣ 3 := by
        have h2 : p ∣ 2 * (m + 1) := by rw [← h2B]; exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right hB 2) 2
        have hsub : 2 * (m + 1) - C = 3 := by omega
        rw [← hsub]; exact Nat.dvd_sub h2 hC
      have := Nat.le_of_dvd (by norm_num) h1; omega
    · rintro ⟨hB, hD⟩
      have h1 : p ∣ 1 := by
        have h2 : p ∣ 2 * (m + 1) := by rw [← h2B]; exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right hB 2) 2
        have hsub : 2 * (m + 1) - D = 1 := by omega
        rw [← hsub]; exact Nat.dvd_sub h2 hD
      exact hp.not_dvd_one h1
    · rintro ⟨hC, hD⟩
      have h1 : p ∣ 2 := by
        have hsub : D - C = 2 := by omega
        rw [← hsub]; exact Nat.dvd_sub hD hC
      have := Nat.le_of_dvd (by norm_num) h1; omega
  have hsqM1 : Squarefree M1 := by
    refine squarefree_of_not_sq_dvd hM1_pos.ne' fun p hp hsq => ?_
    have hp_or : p = 2 ∨ p = 3 ∨ 5 ≤ p := by
      have := hp.two_le
      by_contra h
      push Not at h
      have hp4 : p = 4 := by omega
      subst hp4
      exact absurd hp (by decide)
    rcases hp_or with rfl | rfl | hp5
    · -- p = 2: 2 ∣ A, 2 ∣ B, ¬ 4 ∣ A, ¬ 4 ∣ B, ¬ 2 ∣ C, ¬ 2 ∣ D, so 4 ∥ A*B*C*D, hence ¬ 4 ∣ M1
      have h8 : 8 ∣ A * B * C * D := by
        obtain ⟨r, hr⟩ := hsq
        exact ⟨3 * r, by linarith⟩
      have hv : ¬ 8 ∣ A * B * C * D := by
        have hA2 : A % 4 = 2 := by omega
        have hB2 : B % 4 = 2 := by omega
        have hC2 : C % 2 = 1 := by omega
        have hD2 : D % 2 = 1 := by omega
        obtain ⟨a', ha'⟩ : ∃ a', A = 2 * (2 * a' + 1) := ⟨A / 4, by omega⟩
        obtain ⟨b', hb'⟩ : ∃ b', B = 2 * (2 * b' + 1) := ⟨B / 4, by omega⟩
        obtain ⟨c', hc'⟩ : ∃ c', C = 2 * c' + 1 := ⟨C / 2, by omega⟩
        obtain ⟨d', hd'⟩ : ∃ d', D = 2 * d' + 1 := ⟨D / 2, by omega⟩
        rw [ha', hb', hc', hd']
        intro ⟨t, ht⟩
        have hodd : (2 * a' + 1) * (2 * b' + 1) * (2 * c' + 1) * (2 * d' + 1) = 2 * t := by
          linarith
        have hmod := congrArg (· % 2) hodd
        simp [Nat.mul_mod] at hmod
      exact hv h8
    · -- p = 3: 3 divides exactly two of A,B,C,D (each to power 1 since squarefree), so ¬ 27 ∣ A*B*C*D
      have h27 : 27 ∣ A * B * C * D := by
        obtain ⟨r, hr⟩ := hsq
        exact ⟨2 * r, by linarith⟩
      have hnot9A : ¬ 9 ∣ A := fun hd => (Nat.squarefree_iff_prime_squarefree.mp hsqA 3 Nat.prime_three hd)
      have hnot9B : ¬ 9 ∣ B := fun hd => (Nat.squarefree_iff_prime_squarefree.mp hsqB 3 Nat.prime_three hd)
      have hnot9C : ¬ 9 ∣ C := fun hd => (Nat.squarefree_iff_prime_squarefree.mp hsqC 3 Nat.prime_three hd)
      have hnot9D : ¬ 9 ∣ D := fun hd => (Nat.squarefree_iff_prime_squarefree.mp hsqD 3 Nat.prime_three hd)
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have hv_ge : 3 ≤ padicValNat 3 (A * B * C * D) :=
        (padicValNat_dvd_iff_le (by positivity)).mp (show 3 ^ 3 ∣ A * B * C * D by simpa using h27)
      have hv_sum : padicValNat 3 (A * B * C * D) =
          padicValNat 3 A + padicValNat 3 B + padicValNat 3 C + padicValNat 3 D := by
        rw [padicValNat.mul (by positivity) hD_pos.ne',
            padicValNat.mul (by positivity) hC_pos.ne',
            padicValNat.mul hA_pos.ne' hB_pos.ne']
      have hvle : ∀ X : ℕ, X ≠ 0 → ¬ 9 ∣ X → padicValNat 3 X ≤ 1 := by
        intro X hX h9
        by_contra h2
        push Not at h2
        exact h9 (show 3 ^ 2 ∣ X from (padicValNat_dvd_iff_le hX).mpr h2)
      have hm3 : m % 3 = 1 ∨ m % 3 = 2 := by omega
      rcases hm3 with h3 | h3
      · have hvB : padicValNat 3 B = 0 := padicValNat.eq_zero_of_not_dvd (by omega)
        have hvC : padicValNat 3 C = 0 := padicValNat.eq_zero_of_not_dvd (by omega)
        have hvA := hvle A hA_pos.ne' hnot9A
        have hvD := hvle D hD_pos.ne' hnot9D
        omega
      · have hvA : padicValNat 3 A = 0 := padicValNat.eq_zero_of_not_dvd (by omega)
        have hvD : padicValNat 3 D = 0 := padicValNat.eq_zero_of_not_dvd (by omega)
        have hvB := hvle B hB_pos.ne' hnot9B
        have hvC := hvle C hC_pos.ne' hnot9C
        omega
    · -- p ≥ 5: p^2 ∣ 6 * M1 = A*B*C*D, p divides at most one of A,B,C,D, contradicting squarefreeness!
      have hsqP : p * p ∣ A * B * C * D := by
        rw [← hM1_eq]
        exact dvd_mul_of_dvd_right hsq 6
      have hnc := hno_common_ge5 p hp hp5
      have : Fact p.Prime := ⟨hp⟩
      have hv_ge : 2 ≤ padicValNat p (A * B * C * D) :=
        (padicValNat_dvd_iff_le (by positivity)).mp (by simpa [sq] using hsqP)
      have hv_sum : padicValNat p (A * B * C * D) =
          padicValNat p A + padicValNat p B + padicValNat p C + padicValNat p D := by
        rw [padicValNat.mul (by positivity) hD_pos.ne',
            padicValNat.mul (by positivity) hC_pos.ne',
            padicValNat.mul hA_pos.ne' hB_pos.ne']
      have hvle : ∀ X : ℕ, X ≠ 0 → Squarefree X → padicValNat p X ≤ 1 := by
        intro X hX hsqX
        by_contra h2
        push Not at h2
        have hpsq : p * p ∣ X := by
          simpa [sq] using (padicValNat_dvd_iff_le hX).mpr h2
        exact Nat.squarefree_iff_prime_squarefree.mp hsqX p hp hpsq
      have hvA := hvle A hA_pos.ne' hsqA
      have hvB := hvle B hB_pos.ne' hsqB
      have hvC := hvle C hC_pos.ne' hsqC
      have hvD := hvle D hD_pos.ne' hsqD
      have hnz : ∀ X : ℕ, 0 < padicValNat p X → p ∣ X := fun X hX =>
        dvd_trans (dvd_pow_self p hX.ne') pow_padicValNat_dvd
      by_cases hA0 : padicValNat p A = 0 <;>
      by_cases hB0 : padicValNat p B = 0 <;>
      by_cases hC0 : padicValNat p C = 0 <;>
      by_cases hD0 : padicValNat p D = 0
      · omega
      · omega
      · omega
      · exact hnc.2.2.2.2.2 ⟨hnz C (by omega), hnz D (by omega)⟩
      · omega
      · exact hnc.2.2.2.2.1 ⟨hnz B (by omega), hnz D (by omega)⟩
      · exact hnc.2.2.2.1 ⟨hnz B (by omega), hnz C (by omega)⟩
      · exact hnc.2.2.2.1 ⟨hnz B (by omega), hnz C (by omega)⟩
      · omega
      · exact hnc.2.2.1 ⟨hnz A (by omega), hnz D (by omega)⟩
      · exact hnc.2.1 ⟨hnz A (by omega), hnz C (by omega)⟩
      · exact hnc.2.1 ⟨hnz A (by omega), hnz C (by omega)⟩
      · exact hnc.1 ⟨hnz A (by omega), hnz B (by omega)⟩
      · exact hnc.1 ⟨hnz A (by omega), hnz B (by omega)⟩
      · exact hnc.1 ⟨hnz A (by omega), hnz B (by omega)⟩
      · exact hnc.1 ⟨hnz A (by omega), hnz B (by omega)⟩
  -- Every prime factor of M1 divides A, B, C, or D (and conversely!)
  have hpf_eq : M1.primeFactors =
      ((A.primeFactors ∪ B.primeFactors) ∪ C.primeFactors) ∪ D.primeFactors := by
    ext p
    simp only [Nat.mem_primeFactors, mem_union]
    constructor
    · rintro ⟨hp, hpdvd, _⟩
      have h6 : p ∣ A * B * C * D := by
        rw [← hM1_eq]; exact dvd_mul_of_dvd_right hpdvd 6
      rcases hp.dvd_mul.mp h6 with hABC | hD
      · rcases hp.dvd_mul.mp hABC with hAB | hC
        · rcases hp.dvd_mul.mp hAB with hA | hB
          · exact Or.inl (Or.inl (Or.inl ⟨hp, hA, hA_pos.ne'⟩))
          · exact Or.inl (Or.inl (Or.inr ⟨hp, hB, hB_pos.ne'⟩))
        · exact Or.inl (Or.inr ⟨hp, hC, hC_pos.ne'⟩)
      · exact Or.inr ⟨hp, hD, hD_pos.ne'⟩
    · intro hmem
      have hp : p.Prime := by rcases hmem with ((⟨h, _⟩ | ⟨h, _⟩) | ⟨h, _⟩) | ⟨h, _⟩ <;> exact h
      refine ⟨hp, ?_, hM1_pos.ne'⟩
      have hp_or : p = 2 ∨ p = 3 ∨ 5 ≤ p := by
        have := hp.two_le
        by_contra h
        push Not at h
        have : p = 4 := by omega
        subst this
        exact absurd hp (by decide)
      rcases hp_or with rfl | rfl | hp5
      · -- 2 ∣ M1 since 4 ∣ A * B and 6 * M1 = A * B * C * D
        have h4 : 4 ∣ A * B := by
          have h2A : 2 ∣ A := by omega
          have h2B : 2 ∣ B := by omega
          exact mul_dvd_mul h2A h2B
        have h4M : 4 ∣ 6 * M1 := by
          rw [hM1_eq]
          exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h4 C) D
        omega
      · -- 3 ∣ M1 since 9 ∣ A * B * C * D
        have h9 : 9 ∣ A * B * C * D := by
          have hm3 : m % 3 = 1 ∨ m % 3 = 2 := by omega
          rcases hm3 with h3 | h3
          · have h3A : 3 ∣ A := by omega
            have h3D : 3 ∣ D := by omega
            obtain ⟨a, ha⟩ := h3A; obtain ⟨d, hd⟩ := h3D
            exact ⟨a * B * C * d, by rw [ha, hd]; ring⟩
          · have h3B : 3 ∣ B := by omega
            have h3C : 3 ∣ C := by omega
            obtain ⟨b, hb⟩ := h3B; obtain ⟨c, hc⟩ := h3C
            exact ⟨A * b * c * D, by rw [hb, hc]; ring⟩
        have h9M : 9 ∣ 6 * M1 := by rwa [hM1_eq]
        omega
      · have hcop : Nat.Coprime p 6 := hp.coprime_iff_not_dvd.mpr (fun hd => by
          have hle := Nat.le_of_dvd (by norm_num) hd
          have hp56 : p = 5 ∨ p = 6 := by omega
          rcases hp56 with rfl | rfl
          · norm_num at hd
          · exact absurd hp (by decide))
        have h6M : p ∣ 6 * M1 := by
          rw [hM1_eq]
          rcases hmem with ((⟨_, hA, _⟩ | ⟨_, hB, _⟩) | ⟨_, hC, _⟩) | ⟨_, hD, _⟩
          · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hA _) _) _
          · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hB _) _) _
          · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hC _) _
          · exact dvd_mul_of_dvd_right hD _
        exact hcop.dvd_of_dvd_mul_left h6M
  have hM1_dvd_k : ∀ p ∈ M1.primeFactors, p - 1 ∣ k := by
    intro p hp
    rw [hpf_eq] at hp
    simp only [mem_union, Nat.mem_primeFactors] at hp
    rcases hp with ((⟨hp', hA, _⟩ | ⟨hp', hB, _⟩) | ⟨hp', hC, _⟩) | ⟨hp', hD, _⟩
    · exact (moser_m_sub_one hk hm heven heq hp' hA).1
    · have hB' : p ∣ m + 1 := by
        have h2B : 2 * B = m + 1 := by omega
        rw [← h2B]; exact dvd_mul_of_dvd_right hB 2
      exact (moser_m_add_one hk hm heven heq hp' hB').1
    · exact (moser_two_m_sub_one hk hm heven heq hp' hC).1
    · exact (moser_two_m_add_one hk hm heven heq hp' hD).1
  -- Apply egyptian_ge_one to A, B, C, D
  obtain ⟨IA, hIA, hsumA⟩ := egyptian_ge_one hA_pos (by norm_num : 0 < 1) hsqA
    (fun p hp => (moser_m_sub_one hk hm heven heq (Nat.prime_of_mem_primeFactors hp)
      (Nat.dvd_of_mem_primeFactors hp)).2)
  obtain ⟨IB, hIB, hsumB⟩ := egyptian_ge_one hB_pos (by norm_num : 0 < 1) hsqB
    (fun p hp => moser_m_add_one_div_two_congr hk hm heven heq (Nat.prime_of_mem_primeFactors hp)
      (Nat.dvd_of_mem_primeFactors hp))
  obtain ⟨IC, hIC, hsumC⟩ := egyptian_ge_one hC_pos (by norm_num : 0 < 2) hsqC
    (fun p hp => (moser_two_m_sub_one hk hm heven heq (Nat.prime_of_mem_primeFactors hp)
      (Nat.dvd_of_mem_primeFactors hp)).2)
  obtain ⟨ID, hID, hsumD⟩ := egyptian_ge_one hD_pos (by norm_num : 0 < 4) hsqD
    (fun p hp => (moser_two_m_add_one hk hm heven heq (Nat.prime_of_mem_primeFactors hp)
      (Nat.dvd_of_mem_primeFactors hp)).2)
  -- Relate sum of the 4 prime reciprocal sums to ∑_{p ∈ M1.primeFactors} 1/p + 1/2 + 1/3
  have hsum_combine :
      (∑ p ∈ A.primeFactors, (1 : ℚ) / p) + (∑ p ∈ B.primeFactors, (1 : ℚ) / p) +
      (∑ p ∈ C.primeFactors, (1 : ℚ) / p) + (∑ p ∈ D.primeFactors, (1 : ℚ) / p) =
      (∑ p ∈ M1.primeFactors, (1 : ℚ) / p) + 1 / 2 + 1 / 3 := by
    have h2M : 2 ∈ M1.primeFactors := by
      rw [hpf_eq]
      refine mem_union_left _ (mem_union_left _ (mem_union_left _ ?_))
      exact Nat.mem_primeFactors.mpr ⟨Nat.prime_two, by omega, hA_pos.ne'⟩
    have h3M : 3 ∈ M1.primeFactors := by
      rw [hpf_eq]
      have hm3 : m % 3 = 1 ∨ m % 3 = 2 := by omega
      rcases hm3 with h3 | h3
      · refine mem_union_left _ (mem_union_left _ (mem_union_left _ ?_))
        exact Nat.mem_primeFactors.mpr ⟨Nat.prime_three, by omega, hA_pos.ne'⟩
      · refine mem_union_left _ (mem_union_left _ (mem_union_right _ ?_))
        exact Nat.mem_primeFactors.mpr ⟨Nat.prime_three, by omega, hB_pos.ne'⟩
    -- Rewrite each sum over X.primeFactors as ∑ p ∈ M1.primeFactors, if p ∈ X.primeFactors then 1/p else 0
    have hsubA : A.primeFactors ⊆ M1.primeFactors := by
      rw [hpf_eq]; intro x hx; exact mem_union_left _ (mem_union_left _ (mem_union_left _ hx))
    have hsubB : B.primeFactors ⊆ M1.primeFactors := by
      rw [hpf_eq]; intro x hx; exact mem_union_left _ (mem_union_left _ (mem_union_right _ hx))
    have hsubC : C.primeFactors ⊆ M1.primeFactors := by
      rw [hpf_eq]; intro x hx; exact mem_union_left _ (mem_union_right _ hx)
    have hsubD : D.primeFactors ⊆ M1.primeFactors := by
      rw [hpf_eq]; intro x hx; exact mem_union_right _ hx
    have hrew : ∀ (S : Finset ℕ), S ⊆ M1.primeFactors →
        ∑ p ∈ S, (1 : ℚ) / p = ∑ p ∈ M1.primeFactors, if p ∈ S then (1 : ℚ) / p else 0 := by
      intro S hS
      rw [← sum_filter, filter_mem_eq_inter, inter_eq_right.mpr hS]
    rw [hrew _ hsubA, hrew _ hsubB, hrew _ hsubC, hrew _ hsubD]
    rw [← sum_add_distrib, ← sum_add_distrib, ← sum_add_distrib]
    have hextra : (∑ p ∈ M1.primeFactors, (1 : ℚ) / p) + 1 / 2 + 1 / 3 =
        ∑ p ∈ M1.primeFactors, ((1 : ℚ) / p + (if p = 2 then 1 / 2 else 0) +
          (if p = 3 then 1 / 3 else 0)) := by
      rw [sum_add_distrib, sum_add_distrib]
      simp [sum_ite_eq', h2M, h3M]
    rw [hextra]
    refine sum_congr rfl fun p hpM => ?_
    have hp : p.Prime := Nat.prime_of_mem_primeFactors hpM
    have hp_or : p = 2 ∨ p = 3 ∨ 5 ≤ p := by
      have := hp.two_le
      by_contra h
      push Not at h
      have : p = 4 := by omega
      subst this
      exact absurd hp (by decide)
    rcases hp_or with rfl | rfl | hp5
    · have h2A : 2 ∈ A.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_two, by omega, hA_pos.ne'⟩
      have h2B : 2 ∈ B.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_two, by omega, hB_pos.ne'⟩
      have h2C : 2 ∉ C.primeFactors := fun h => by
        have := Nat.dvd_of_mem_primeFactors h; omega
      have h2D : 2 ∉ D.primeFactors := fun h => by
        have := Nat.dvd_of_mem_primeFactors h; omega
      simp [h2A, h2B, h2C, h2D]
    · have hm3 : m % 3 = 1 ∨ m % 3 = 2 := by omega
      rcases hm3 with h3 | h3
      · have h3A : 3 ∈ A.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_three, by omega, hA_pos.ne'⟩
        have h3B : 3 ∉ B.primeFactors := fun h => by have := Nat.dvd_of_mem_primeFactors h; omega
        have h3C : 3 ∉ C.primeFactors := fun h => by have := Nat.dvd_of_mem_primeFactors h; omega
        have h3D : 3 ∈ D.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_three, by omega, hD_pos.ne'⟩
        simp [h3A, h3B, h3C, h3D]
      · have h3A : 3 ∉ A.primeFactors := fun h => by have := Nat.dvd_of_mem_primeFactors h; omega
        have h3B : 3 ∈ B.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_three, by omega, hB_pos.ne'⟩
        have h3C : 3 ∈ C.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_three, by omega, hC_pos.ne'⟩
        have h3D : 3 ∉ D.primeFactors := fun h => by have := Nat.dvd_of_mem_primeFactors h; omega
        simp [h3A, h3B, h3C, h3D]
    · have hnc := hno_common_ge5 p hp hp5
      have hp2 : p ≠ 2 := by omega
      have hp3 : p ≠ 3 := by omega
      simp only [hp2, hp3, ↓reduceIte, add_zero]
      rw [hpf_eq] at hpM
      simp only [mem_union] at hpM
      rcases hpM with ((hA | hB) | hC) | hD
      · have hB : p ∉ B.primeFactors := fun h => hnc.1 ⟨Nat.dvd_of_mem_primeFactors hA, Nat.dvd_of_mem_primeFactors h⟩
        have hC : p ∉ C.primeFactors := fun h => hnc.2.1 ⟨Nat.dvd_of_mem_primeFactors hA, Nat.dvd_of_mem_primeFactors h⟩
        have hD : p ∉ D.primeFactors := fun h => hnc.2.2.1 ⟨Nat.dvd_of_mem_primeFactors hA, Nat.dvd_of_mem_primeFactors h⟩
        simp [hA, hB, hC, hD]
      · have hA : p ∉ A.primeFactors := fun h => hnc.1 ⟨Nat.dvd_of_mem_primeFactors h, Nat.dvd_of_mem_primeFactors hB⟩
        have hC : p ∉ C.primeFactors := fun h => hnc.2.2.2.1 ⟨Nat.dvd_of_mem_primeFactors hB, Nat.dvd_of_mem_primeFactors h⟩
        have hD : p ∉ D.primeFactors := fun h => hnc.2.2.2.2.1 ⟨Nat.dvd_of_mem_primeFactors hB, Nat.dvd_of_mem_primeFactors h⟩
        simp [hA, hB, hC, hD]
      · have hA : p ∉ A.primeFactors := fun h => hnc.2.1 ⟨Nat.dvd_of_mem_primeFactors h, Nat.dvd_of_mem_primeFactors hC⟩
        have hB : p ∉ B.primeFactors := fun h => hnc.2.2.2.1 ⟨Nat.dvd_of_mem_primeFactors h, Nat.dvd_of_mem_primeFactors hC⟩
        have hD : p ∉ D.primeFactors := fun h => hnc.2.2.2.2.2 ⟨Nat.dvd_of_mem_primeFactors hC, Nat.dvd_of_mem_primeFactors h⟩
        simp [hA, hB, hC, hD]
      · have hA : p ∉ A.primeFactors := fun h => hnc.2.2.1 ⟨Nat.dvd_of_mem_primeFactors h, Nat.dvd_of_mem_primeFactors hD⟩
        have hB : p ∉ B.primeFactors := fun h => hnc.2.2.2.2.1 ⟨Nat.dvd_of_mem_primeFactors h, Nat.dvd_of_mem_primeFactors hD⟩
        have hC : p ∉ C.primeFactors := fun h => hnc.2.2.2.2.2 ⟨Nat.dvd_of_mem_primeFactors h, Nat.dvd_of_mem_primeFactors hD⟩
        simp [hA, hB, hC, hD]
  refine ⟨h12dvd, hsqM1, hM1_dvd_k, ?_⟩
  have h1B : (1 : ℚ) / B = 2 / (m + 1 : ℚ) := by
    have h2B : (2 : ℚ) * B = m + 1 := by exact_mod_cast (show 2 * B = m + 1 by omega)
    have hBne : (B : ℚ) ≠ 0 := by exact_mod_cast hB_pos.ne'
    have hm1ne : (m + 1 : ℚ) ≠ 0 := by positivity
    field_simp
    linarith
  have h1A : (1 : ℚ) / A = 1 / (m - 1 : ℚ) := by
    have : (A : ℚ) = m - 1 := by
      dsimp only [A]
      rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
    rw [this]
  have h2C : (2 : ℚ) / C = 2 / (2 * m - 1 : ℚ) := by
    have : (C : ℚ) = 2 * m - 1 := by
      dsimp only [C]
      rw [Nat.cast_sub (by omega : 1 ≤ 2 * m), Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    rw [this]
  have h4D : (4 : ℚ) / D = 4 / (2 * m + 1 : ℚ) := by
    have : (D : ℚ) = 2 * m + 1 := by
      dsimp only [D]
      push_cast; rfl
    rw [this]
  have hIAQ : (1 : ℚ) ≤ IA := by exact_mod_cast hIA
  have hIBQ : (1 : ℚ) ≤ IB := by exact_mod_cast hIB
  have hICQ : (1 : ℚ) ≤ IC := by exact_mod_cast hIC
  have hIDQ : (1 : ℚ) ≤ ID := by exact_mod_cast hID
  simp only [Nat.cast_one, Nat.cast_ofNat] at hsumA hsumB hsumC hsumD
  rw [h1A] at hsumA
  rw [h1B] at hsumB
  rw [h2C] at hsumC
  rw [h4D] at hsumD
  linarith

/- ### Section 5: Small-m exclusion (m > 1000), greedy primorial lemma, and bootstrap (m > 10^8) -/

lemma m_gt_thousand {k m : ℕ} (hk : 0 < k) (hm : 0 < m) (heven : Even k)
    (heq : ErdosMoser.powerSum k m = m ^ k) : 1000 < m := by
  by_contra hle
  push Not at hle
  have hm16 := m_mod_sixteen hk hm heven heq
  have h3nm := three_not_dvd_m hk hm heven heq
  have hm_ge : 8 < m := by
    have := krzysztofek_lower hk hm heven heq
    have := k_ge_six hk hm heven heq
    omega
  let W : List (ℕ × ℕ) :=
    [(1, 37), (2, 3), (4, 19), (5, 11), (7, 229), (8, 3), (10, 5), (11, 3),
     (13, 421), (14, 151), (16, 11), (17, 3), (19, 613), (20, 3), (22, 709), (23, 13),
     (25, 5), (26, 3), (28, 17), (29, 3), (31, 997), (32, 7), (34, 1093), (35, 3),
     (37, 29), (38, 3), (40, 5), (41, 439), (43, 1381), (44, 3), (46, 7), (47, 3),
     (49, 11), (50, 5), (52, 1669), (53, 3), (55, 353), (56, 3), (58, 1861), (59, 631),
     (61, 19), (62, 3)]
  have hcover : (List.range' 1 62).all (fun j =>
      decide ((16 * j + 3) % 3 = 0) ||
      W.any (fun jp => decide (jp.1 = j))) = true := by
    decide
  have hvalid : W.all (fun jp =>
      decide (2 ≤ jp.2 ∧ jp.2 ≤ 2000) &&
      (List.range' 2 43).all (fun d => decide (jp.2 ≤ d ∨ jp.2 % d ≠ 0)) &&
      decide ((32 * jp.1 + 5) % jp.2 = 0 ∧ ((32 * jp.1 + 5) / jp.2 + 2) % jp.2 ≠ 0)) = true := by
    decide
  set j := m / 16
  have hmj : m = 16 * j + 3 := by omega
  have hj_mem : j ∈ List.range' 1 62 := List.mem_range'.mpr ⟨j - 1, by omega, by omega⟩
  rw [List.all_eq_true] at hcover
  have hcov := hcover j hj_mem
  simp only [Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true] at hcov
  have h3ne : (16 * j + 3) % 3 ≠ 0 := by
    rw [← hmj]
    exact fun hz => h3nm (Nat.dvd_of_mod_eq_zero hz)
  rcases hcov with h3 | ⟨⟨j', p⟩, hmemW, hj'⟩
  · exact h3ne h3
  · dsimp only at hj'
    subst hj'
    rw [List.all_eq_true] at hvalid
    have hv := hvalid (j, p) hmemW
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hv
    rcases hv with ⟨⟨⟨hp2, hp_le⟩, htrial⟩, hpdvd0, hfail⟩
    have hp_prime : p.Prime := by
      rw [Nat.prime_def_lt']
      refine ⟨hp2, fun d hd2 hdlt hdvd => ?_⟩
      have hq_dvd : (p / d) ∣ p := Nat.div_dvd_of_dvd hdvd
      have hmul : d * (p / d) = p := Nat.mul_div_cancel' hdvd
      have hq_ge : 2 ≤ p / d := by
        by_contra hlt
        push Not at hlt
        have h0 : p / d = 0 ∨ p / d = 1 := by
          cases hq : p / d with
          | zero => exact Or.inl rfl
          | succ n =>
            cases n with
            | zero => exact Or.inr rfl
            | succ r => rw [hq] at hlt; omega
        rcases h0 with h0 | h1 <;> nlinarith
      have hmin : min d (p / d) < 45 := by
        by_contra hge
        push Not at hge
        have hd45 : 45 ≤ d := le_trans hge (min_le_left _ _)
        have hq45 : 45 ≤ p / d := le_trans hge (min_le_right _ _)
        nlinarith
      rcases le_total d (p / d) with hle_dq | hle_qd
      · have hd45 : d < 45 := by omega
        have hd_mem : d ∈ List.range' 2 43 := List.mem_range'.mpr ⟨d - 2, by omega, by omega⟩
        rcases htrial d hd_mem with hple | hmod
        · omega
        · exact hmod (Nat.mod_eq_zero_of_dvd hdvd)
      · have hq45 : p / d < 45 := by omega
        have hqlt : p / d < p := by nlinarith
        have hq_mem : p / d ∈ List.range' 2 43 := List.mem_range'.mpr ⟨p / d - 2, by omega, by omega⟩
        rcases htrial (p / d) hq_mem with hple | hmod
        · omega
        · exact hmod (Nat.mod_eq_zero_of_dvd hq_dvd)
    have h2m1 : 2 * m - 1 = 32 * j + 5 := by omega
    have hpdvd : p ∣ 2 * m - 1 := by rw [h2m1]; exact Nat.dvd_of_mod_eq_zero hpdvd0
    have hmod := (moser_two_m_sub_one hk hm heven heq hp_prime hpdvd).2
    rw [h2m1] at hmod
    exact hfail (Nat.mod_eq_zero_of_dvd hmod)

lemma primorial_lt_of_sum_inv_lt {M X : ℕ} (_hM : 0 < M) (hX : 0 < X) (hsq : Squarefree M)
    (hsum : ∑ p ∈ Nat.primesLE X, (1 : ℝ) / p < ∑ p ∈ M.primeFactors, (1 : ℝ) / p) :
    primorial X < M := by
  set Q := Nat.primesLE X
  set P := M.primeFactors
  have hQ_eq : ∏ p ∈ Q, p = primorial X := by
    simp only [Q, primorial, Nat.primesLE_eq_filter_range]
  have hP_eq : ∏ p ∈ P, p = M := Nat.prod_primeFactors_of_squarefree hsq
  rw [← hQ_eq, ← hP_eq]
  set A := Q \ P
  set B := P \ Q
  have hsplitQ : ∑ p ∈ Q, (1 : ℝ) / p =
      (∑ p ∈ Q ∩ P, (1 : ℝ) / p) + ∑ p ∈ A, (1 : ℝ) / p := by
    have h1 : Q \ (Q ∩ P) = A := by ext x; simp [A]
    rw [add_comm, ← h1, sum_sdiff inter_subset_left]
  have hsplitP : ∑ p ∈ P, (1 : ℝ) / p =
      (∑ p ∈ Q ∩ P, (1 : ℝ) / p) + ∑ p ∈ B, (1 : ℝ) / p := by
    have h1 : P \ (Q ∩ P) = B := by ext x; simp [B]
    rw [add_comm, ← h1, sum_sdiff inter_subset_right]
  have hAB_sum : ∑ p ∈ A, (1 : ℝ) / p < ∑ p ∈ B, (1 : ℝ) / p := by linarith
  have hB_nonempty : B.Nonempty := by
    by_contra hemp
    rw [not_nonempty_iff_eq_empty] at hemp
    rw [hemp, sum_empty] at hAB_sum
    have hnonneg : 0 ≤ ∑ p ∈ A, (1 : ℝ) / p := sum_nonneg fun p _ => by positivity
    linarith
  have hA_ge : (A.card : ℝ) / X ≤ ∑ p ∈ A, (1 : ℝ) / p := by
    have h1 : (A.card : ℝ) / X = ∑ _p ∈ A, (1 : ℝ) / X := by
      rw [sum_const, nsmul_eq_mul, mul_one_div]
    rw [h1]
    refine sum_le_sum fun p hp => ?_
    have hpQ : p ∈ Q := (mem_sdiff.mp hp).1
    have hp_pos : (0 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primesLE hpQ).pos
    have hp_le : (p : ℝ) ≤ X := by exact_mod_cast Nat.le_of_mem_primesLE hpQ
    exact one_div_le_one_div_of_le hp_pos hp_le
  have hB_lt : ∑ p ∈ B, (1 : ℝ) / p < (B.card : ℝ) / X := by
    have h1 : (B.card : ℝ) / X = ∑ _p ∈ B, (1 : ℝ) / X := by
      rw [sum_const, nsmul_eq_mul, mul_one_div]
    rw [h1]
    refine sum_lt_sum_of_nonempty hB_nonempty fun q hq => ?_
    have hqP : q ∈ P := (mem_sdiff.mp hq).1
    have hq_notQ : q ∉ Q := (mem_sdiff.mp hq).2
    have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hqP
    have hq_gt : X < q := by
      by_contra hle
      push Not at hle
      exact hq_notQ (Nat.mem_primesLE.mpr ⟨hle, hq_prime⟩)
    have hX_pos : (0 : ℝ) < X := by exact_mod_cast hX
    exact one_div_lt_one_div_of_lt hX_pos (by exact_mod_cast hq_gt)
  have hcard_lt : A.card < B.card := by
    have hX_pos : (0 : ℝ) < X := by exact_mod_cast hX
    have hltR : (A.card : ℝ) < B.card := by
      have hdiv : (A.card : ℝ) / X < (B.card : ℝ) / X := lt_of_le_of_lt hA_ge (lt_trans hAB_sum hB_lt)
      exact (div_lt_div_iff_of_pos_right hX_pos).mp hdiv
    exact_mod_cast hltR
  have hprodA : ∏ p ∈ A, p ≤ X ^ A.card := by
    calc ∏ p ∈ A, p ≤ ∏ _p ∈ A, X := prod_le_prod' fun p hp =>
          Nat.le_of_mem_primesLE (mem_sdiff.mp hp).1
      _ = X ^ A.card := prod_const X
  have hprodB : X ^ B.card < ∏ q ∈ B, q := by
    have h1 : ∏ _q ∈ B, X < ∏ q ∈ B, q := by
      refine prod_lt_prod_of_nonempty (fun q hq => ?_) (fun q hq => ?_) hB_nonempty
      · exact hX
      · have hqP : q ∈ P := (mem_sdiff.mp hq).1
        have hq_notQ : q ∉ Q := (mem_sdiff.mp hq).2
        have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hqP
        by_contra hle
        push Not at hle
        exact hq_notQ (Nat.mem_primesLE.mpr ⟨hle, hq_prime⟩)
    simpa [prod_const] using h1
  have hX_pow : X ^ A.card ≤ X ^ B.card := Nat.pow_le_pow_right hX (le_of_lt hcard_lt)
  have hprod_lt : ∏ p ∈ A, p < ∏ q ∈ B, q := lt_of_le_of_lt (le_trans hprodA hX_pow) hprodB
  have hprodQ_split : ∏ p ∈ Q, p = (∏ p ∈ Q ∩ P, p) * ∏ p ∈ A, p := by
    have h1 : Q \ (Q ∩ P) = A := by ext x; simp [A]
    rw [mul_comm, ← h1, prod_sdiff inter_subset_left]
  have hprodP_split : ∏ p ∈ P, p = (∏ p ∈ Q ∩ P, p) * ∏ p ∈ B, p := by
    have h1 : P \ (Q ∩ P) = B := by ext x; simp [B]
    rw [mul_comm, ← h1, prod_sdiff inter_subset_right]
  have hinter_pos : 0 < ∏ p ∈ Q ∩ P, p :=
    prod_pos fun p hp => (Nat.prime_of_mem_primeFactors (mem_inter.mp hp).2).pos
  rw [hprodQ_split, hprodP_split]
  exact Nat.mul_lt_mul_of_pos_left hprod_lt hinter_pos

lemma sum_inv_primes_le_via_sieve (N B D U : ℕ) (hN : 2 ≤ N) (hD : 0 < D)
    (hcheck : (((List.range' 2 (N - 1)).filter (fun n =>
        (List.range' 2 B).all (fun d => decide (n ≤ d ∨ n % d ≠ 0)))).map
        (fun n => D / n + 1)).sum ≤ U) :
    ∑ p ∈ Nat.primesLE N, (1 : ℝ) / p ≤ (U : ℝ) / D := by
  let L : List ℕ := (List.range' 2 (N - 1)).filter (fun n =>
      (List.range' 2 B).all (fun d => decide (n ≤ d ∨ n % d ≠ 0)))
  have hnodup : L.Nodup := List.Nodup.filter _ List.nodup_range'
  have hsub : Nat.primesLE N ⊆ L.toFinset := by
    intro p hp
    have hp_prime : p.Prime := Nat.prime_of_mem_primesLE hp
    have hp2 : 2 ≤ p := hp_prime.two_le
    have hp_le : p ≤ N := Nat.le_of_mem_primesLE hp
    rw [List.mem_toFinset]
    refine List.mem_filter.mpr ⟨List.mem_range'.mpr ⟨p - 2, by omega, by omega⟩, ?_⟩
    rw [List.all_eq_true]
    intro d hd
    rw [decide_eq_true_eq]
    rcases le_or_gt p d with hle | hlt
    · exact Or.inl hle
    · right
      intro hmod0
      have hd_ge : 2 ≤ d := by
        rw [List.mem_range'] at hd
        obtain ⟨j, _, rfl⟩ := hd; omega
      have hdvd : d ∣ p := Nat.dvd_of_mod_eq_zero hmod0
      rcases hp_prime.eq_one_or_self_of_dvd d hdvd with h1 | hself <;> omega
  have hterm : ∀ n ∈ L.toFinset, (1 : ℝ) / n ≤ ((D / n + 1 : ℕ) : ℝ) / D := by
    intro n hn
    rw [List.mem_toFinset] at hn
    have hn_pos : 0 < n := by
      have hmem := (List.mem_filter.mp hn).1
      rw [List.mem_range'] at hmem
      obtain ⟨j, _, rfl⟩ := hmem
      omega
    have hD_pos : (0 : ℝ) < D := by exact_mod_cast hD
    have hn_posR : (0 : ℝ) < n := by exact_mod_cast hn_pos
    rw [div_le_div_iff₀ hn_posR hD_pos, one_mul]
    have hnat : D < n * (D / n + 1) := Nat.lt_mul_div_succ D hn_pos
    have hnat' : D ≤ (D / n + 1) * n := by nlinarith
    exact_mod_cast hnat'
  have hsum_eq : ∑ n ∈ L.toFinset, (D / n + 1) = (L.map (fun n => D / n + 1)).sum := by
    rw [List.sum_toFinset _ hnodup]
  calc ∑ p ∈ Nat.primesLE N, (1 : ℝ) / p
      ≤ ∑ n ∈ L.toFinset, (1 : ℝ) / n :=
        sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
    _ ≤ ∑ n ∈ L.toFinset, ((D / n + 1 : ℕ) : ℝ) / D :=
        sum_le_sum hterm
    _ = ((∑ n ∈ L.toFinset, (D / n + 1) : ℕ) : ℝ) / D := by
        rw [← sum_div, Nat.cast_sum]
    _ = (((L.map (fun n => D / n + 1)).sum : ℕ) : ℝ) / D := by
        rw [hsum_eq]
    _ ≤ (U : ℝ) / D := by
        gcongr

lemma m_gt_ten_pow_eight {k m : ℕ} (hk : 0 < k) (hm : 0 < m) (heven : Even k)
    (heq : ErdosMoser.powerSum k m = m ^ k) : 10 ^ 8 < m := by
  have hm1000 : 1000 < m := m_gt_thousand hk hm heven heq
  obtain ⟨h12, hsqM1, _, hineq⟩ := moser_M1_structure hk hm heven heq
  set M1 := (m ^ 2 - 1) * (4 * m ^ 2 - 1) / 12
  have hM1_pos : 0 < M1 := by
    dsimp only [M1]
    have hm2 : 100 ≤ m ^ 2 := by nlinarith
    have h1 : 12 ≤ (m ^ 2 - 1) * (4 * m ^ 2 - 1) := by
      have ha : 12 ≤ m ^ 2 - 1 := by omega
      have hb : 1 ≤ 4 * m ^ 2 - 1 := by omega
      nlinarith
    exact Nat.div_pos h1 (by norm_num)
  have hsum100 : ∑ p ∈ Nat.primesLE 100, (1 : ℝ) / p ≤ (1820000 : ℝ) / 1000000 :=
    sum_inv_primes_le_via_sieve 100 10 1000000 1820000 (by norm_num) (by norm_num) (by decide)
  have hineqR : (19 / 6 : ℝ) ≤
      (∑ p ∈ M1.primeFactors, (1 : ℝ) / p) +
        1 / (m - 1 : ℝ) + 2 / (m + 1 : ℝ) + 2 / (2 * m - 1 : ℝ) + 4 / (2 * m + 1 : ℝ) := by
    have hcast := Rat.cast_le (K := ℝ).mpr hineq
    push_cast at hcast
    exact hcast
  have hmR : (1000 : ℝ) < m := by exact_mod_cast hm1000
  have herr : 1 / (m - 1 : ℝ) + 2 / (m + 1 : ℝ) + 2 / (2 * m - 1 : ℝ) + 4 / (2 * m + 1 : ℝ) <
      (1 : ℝ) / 100 := by
    have h1 : 1 / (m - 1 : ℝ) < 1 / 999 := one_div_lt_one_div_of_lt (by norm_num) (by linarith)
    have h2 : 2 / (m + 1 : ℝ) < 2 / 1000 := by
      rw [div_lt_div_iff₀ (by linarith) (by norm_num)]; linarith
    have h3 : 2 / (2 * m - 1 : ℝ) < 2 / 1999 := by
      rw [div_lt_div_iff₀ (by linarith) (by norm_num)]; linarith
    have h4 : 4 / (2 * m + 1 : ℝ) < 4 / 2000 := by
      rw [div_lt_div_iff₀ (by linarith) (by norm_num)]; linarith
    linarith
  have hsum_lt : ∑ p ∈ Nat.primesLE 100, (1 : ℝ) / p < ∑ p ∈ M1.primeFactors, (1 : ℝ) / p := by
    linarith
  have hprim_lt : primorial 100 < M1 :=
    primorial_lt_of_sum_inv_lt hM1_pos (by norm_num) hsqM1 hsum_lt
  have hprim100 : 10 ^ 32 < primorial 100 := by decide
  have hM1_le : M1 < m ^ 4 := by
    dsimp only [M1]
    have h1 : (m ^ 2 - 1) * (4 * m ^ 2 - 1) < 12 * m ^ 4 := by
      have hsub1 : m ^ 2 - 1 ≤ m ^ 2 := Nat.sub_le _ _
      have hsub2 : 4 * m ^ 2 - 1 ≤ 4 * m ^ 2 := Nat.sub_le _ _
      have hmul : (m ^ 2 - 1) * (4 * m ^ 2 - 1) ≤ m ^ 2 * (4 * m ^ 2) :=
        Nat.mul_le_mul hsub1 hsub2
      have h4eq : m ^ 2 * (4 * m ^ 2) = 4 * m ^ 4 := by ring
      have hpos4 : 0 < m ^ 4 := by positivity
      omega
    exact Nat.div_lt_of_lt_mul h1
  have hm4 : (10 ^ 8) ^ 4 < m ^ 4 := by
    have hpow : (10 ^ 8) ^ 4 = 10 ^ 32 := by norm_num
    omega
  by_contra hle
  push Not at hle
  have := Nat.pow_le_pow_left hle 4
  omega

/- ### Section 6: Elementary log bounds, Chebyshev's 30-identity, and Moser's 1953 bound (m > 10^{10^6}) -/

lemma log_one_add_ge_sub_sq {t : ℝ} (ht : 0 ≤ t) :
    t - t ^ 2 / 2 ≤ Real.log (1 + t) := by
  let f : ℝ → ℝ := fun x => Real.log (1 + x) - (x - x ^ 2 / 2)
  have hderiv : ∀ x : ℝ, 0 < x → HasDerivAt f (1 / (1 + x) - (1 - x)) x := by
    intro x hx0
    have h1 : HasDerivAt (fun y => 1 + y) 1 x := (hasDerivAt_id x).const_add 1
    have hlog : HasDerivAt (fun y => Real.log (1 + y)) (1 / (1 + x)) x := by
      simpa using h1.log (by linarith)
    have hsq : HasDerivAt (fun y : ℝ => y ^ 2 / 2) x x :=
      ((hasDerivAt_pow 2 x).div_const 2).congr_deriv (by simp)
    exact hlog.sub ((hasDerivAt_id x).sub hsq)
  have hmono : MonotoneOn f (Set.Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) ?_ ?_ ?_
    · refine ContinuousOn.sub ?_ (by fun_prop)
      refine ContinuousOn.log (by fun_prop) fun x hx => ?_
      have : 0 ≤ x := hx
      linarith
    · intro x hx
      have hx0 : 0 < x := by simpa [interior_Ici] using hx
      exact (hderiv x hx0).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx0 : 0 < x := by simpa [interior_Ici] using hx
      rw [(hderiv x hx0).deriv]
      have hden : 0 < 1 + x := by linarith
      have heq : 1 / (1 + x) - (1 - x) = x ^ 2 / (1 + x) := by field_simp; ring
      rw [heq]
      positivity
  have h0 : f 0 ≤ f t := hmono (Set.mem_Ici.mpr le_rfl) ht ht
  simp only [f, add_zero, Real.log_one, sub_self, zero_pow (by norm_num : 2 ≠ 0), zero_div] at h0
  linarith

lemma log_one_add_le_add_cube {t : ℝ} (ht : 0 ≤ t) :
    Real.log (1 + t) ≤ t - t ^ 2 / 2 + t ^ 3 / 3 := by
  let g : ℝ → ℝ := fun x => (x - x ^ 2 / 2 + x ^ 3 / 3) - Real.log (1 + x)
  have hderiv : ∀ x : ℝ, 0 < x → HasDerivAt g (1 - x + x ^ 2 - 1 / (1 + x)) x := by
    intro x hx0
    have h1 : HasDerivAt (fun y => 1 + y) 1 x := (hasDerivAt_id x).const_add 1
    have hlog : HasDerivAt (fun y => Real.log (1 + y)) (1 / (1 + x)) x := by
      simpa using h1.log (by linarith)
    have h2 : HasDerivAt (fun y : ℝ => y ^ 2 / 2) x x :=
      ((hasDerivAt_pow 2 x).div_const 2).congr_deriv (by simp)
    have h3 : HasDerivAt (fun y : ℝ => y ^ 3 / 3) (x ^ 2) x :=
      ((hasDerivAt_pow 3 x).div_const 3).congr_deriv (by simp)
    exact (((hasDerivAt_id x).sub h2).add h3).sub hlog
  have hmono : MonotoneOn g (Set.Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) ?_ ?_ ?_
    · refine ContinuousOn.sub (by fun_prop) ?_
      refine ContinuousOn.log (by fun_prop) fun x hx => ?_
      have : 0 ≤ x := hx
      linarith
    · intro x hx
      have hx0 : 0 < x := by simpa [interior_Ici] using hx
      exact (hderiv x hx0).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx0 : 0 < x := by simpa [interior_Ici] using hx
      rw [(hderiv x hx0).deriv]
      have hden : 0 < 1 + x := by linarith
      have heq : 1 - x + x ^ 2 - 1 / (1 + x) = x ^ 3 / (1 + x) := by field_simp; ring
      rw [heq]
      positivity
  have h0 : g 0 ≤ g t := hmono (Set.mem_Ici.mpr le_rfl) ht ht
  simp only [g, add_zero, Real.log_one, sub_self, zero_pow (by norm_num : 2 ≠ 0),
    zero_pow (by norm_num : 3 ≠ 0), zero_div] at h0
  linarith

lemma log_one_add_ge_sub_fourth {t : ℝ} (ht : 0 ≤ t) :
    t - t ^ 2 / 2 + t ^ 3 / 3 - t ^ 4 / 4 ≤ Real.log (1 + t) := by
  let f : ℝ → ℝ := fun x => Real.log (1 + x) - (x - x ^ 2 / 2 + x ^ 3 / 3 - x ^ 4 / 4)
  have hderiv : ∀ x : ℝ, 0 < x → HasDerivAt f (1 / (1 + x) - (1 - x + x ^ 2 - x ^ 3)) x := by
    intro x hx0
    have h1 : HasDerivAt (fun y => 1 + y) 1 x := (hasDerivAt_id x).const_add 1
    have hlog : HasDerivAt (fun y => Real.log (1 + y)) (1 / (1 + x)) x := by
      simpa using h1.log (by linarith)
    have h2 : HasDerivAt (fun y : ℝ => y ^ 2 / 2) x x :=
      ((hasDerivAt_pow 2 x).div_const 2).congr_deriv (by simp)
    have h3 : HasDerivAt (fun y : ℝ => y ^ 3 / 3) (x ^ 2) x :=
      ((hasDerivAt_pow 3 x).div_const 3).congr_deriv (by simp)
    have h4 : HasDerivAt (fun y : ℝ => y ^ 4 / 4) (x ^ 3) x :=
      ((hasDerivAt_pow 4 x).div_const 4).congr_deriv (by simp)
    exact hlog.sub ((((hasDerivAt_id x).sub h2).add h3).sub h4)
  have hmono : MonotoneOn f (Set.Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) ?_ ?_ ?_
    · refine ContinuousOn.sub ?_ (by fun_prop)
      refine ContinuousOn.log (by fun_prop) fun x hx => ?_
      have : 0 ≤ x := hx
      linarith
    · intro x hx
      have hx0 : 0 < x := by simpa [interior_Ici] using hx
      exact (hderiv x hx0).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx0 : 0 < x := by simpa [interior_Ici] using hx
      rw [(hderiv x hx0).deriv]
      have hden : 0 < 1 + x := by linarith
      have heq : 1 / (1 + x) - (1 - x + x ^ 2 - x ^ 3) = x ^ 4 / (1 + x) := by field_simp; ring
      rw [heq]
      positivity
  have h0 : f 0 ≤ f t := hmono (Set.mem_Ici.mpr le_rfl) ht ht
  simp only [f, add_zero, Real.log_one, sub_self, zero_pow (by norm_num : 2 ≠ 0),
    zero_pow (by norm_num : 3 ≠ 0), zero_pow (by norm_num : 4 ≠ 0), zero_div] at h0
  linarith

lemma log_small_constants :
    (1.0986 : ℝ) < Real.log 3 ∧ Real.log 3 < 1.0987 ∧
    (1.6094 : ℝ) < Real.log 5 ∧ Real.log 5 < 1.6095 ∧
    (2.3025 : ℝ) < Real.log 10 ∧ Real.log 10 < 2.3026 := by
  have hl2_lo : (0.69314718 : ℝ) < Real.log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
  have hl2_hi : Real.log 2 < (0.69314719 : ℝ) := lt_trans Real.log_two_lt_d9 (by norm_num)
  have h98 : Real.log (1 + (1 / 8 : ℝ)) = 2 * Real.log 3 - 3 * Real.log 2 := by
    have h1 : (1 + (1 / 8 : ℝ)) = (3 : ℝ) ^ 2 / (2 : ℝ) ^ 3 := by norm_num
    rw [h1, Real.log_div (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]
    push_cast; ring
  have h98_lo := log_one_add_ge_sub_fourth (by norm_num : (0 : ℝ) ≤ 1 / 8)
  have h98_hi := log_one_add_le_add_cube (by norm_num : (0 : ℝ) ≤ 1 / 8)
  rw [h98] at h98_lo h98_hi
  have hl3_lo : (1.0986 : ℝ) < Real.log 3 := by linarith
  have hl3_hi : Real.log 3 < (1.0987 : ℝ) := by linarith
  have h2524 : Real.log (1 + (1 / 24 : ℝ)) = 2 * Real.log 5 - (3 * Real.log 2 + Real.log 3) := by
    have h1 : (1 + (1 / 24 : ℝ)) = (5 : ℝ) ^ 2 / ((2 : ℝ) ^ 3 * 3) := by norm_num
    rw [h1, Real.log_div (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow, Real.log_pow]
    push_cast; ring
  have h2524_lo := log_one_add_ge_sub_sq (by norm_num : (0 : ℝ) ≤ 1 / 24)
  have h2524_hi := log_one_add_le_add_cube (by norm_num : (0 : ℝ) ≤ 1 / 24)
  rw [h2524] at h2524_lo h2524_hi
  have hl5_lo : (1.6094 : ℝ) < Real.log 5 := by linarith
  have hl5_hi : Real.log 5 < (1.6095 : ℝ) := by linarith
  have h10 : Real.log (10 : ℝ) = Real.log 2 + Real.log 5 := by
    rw [show (10 : ℝ) = 2 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  exact ⟨hl3_lo, hl3_hi, hl5_lo, hl5_hi, by linarith, by linarith⟩

/- Legendre's factorial-psi identity and Chebyshev's 30-identity -/

lemma log_factorial_eq_sum_log (n : ℕ) :
    Real.log (n.factorial : ℝ) = ∑ j ∈ Icc 1 n, Real.log (j : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.factorial_succ, Nat.cast_mul,
      Real.log_mul (by positivity) (by positivity), ih, sum_Icc_succ_top (Nat.succ_pos n)]
    ring

lemma log_factorial_eq_sum_psi (n : ℕ) :
    Real.log (n.factorial : ℝ) = ∑ k ∈ Icc 1 n, Chebyshev.psi ((n : ℝ) / k) := by
  rw [log_factorial_eq_sum_log]
  have h1 : ∀ j ∈ Icc 1 n, Real.log (j : ℝ) =
      ∑ d ∈ j.divisors, ArithmeticFunction.vonMangoldt d := fun j _ =>
    (ArithmeticFunction.vonMangoldt_sum).symm
  rw [sum_congr rfl h1]
  have h2 : ∑ j ∈ Icc 1 n, ∑ d ∈ j.divisors, ArithmeticFunction.vonMangoldt d =
      ∑ k ∈ Icc 1 n, ∑ d ∈ Icc 1 (n / k), ArithmeticFunction.vonMangoldt d := by
    rw [sum_sigma', sum_sigma']
    refine sum_bij (fun p _ => ⟨p.1 / p.2, p.2⟩) ?_ ?_ ?_ ?_
    · rintro ⟨j, d⟩ h
      simp only [mem_sigma, mem_Icc, Nat.mem_divisors] at h ⊢
      rcases h with ⟨⟨hj1, hjn⟩, ⟨hdvd, hj0⟩⟩
      have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos hdvd (by omega)
      have hq_pos : 0 < j / d := Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) hd_pos
      have hq_le : j / d ≤ n := le_trans (Nat.div_le_self j d) hjn
      have hd_le : d ≤ n / (j / d) := by
        rw [Nat.le_div_iff_mul_le hq_pos, mul_comm, Nat.div_mul_cancel hdvd]
        exact hjn
      exact ⟨⟨hq_pos, hq_le⟩, ⟨hd_pos, hd_le⟩⟩
    · rintro ⟨j1, d1⟩ h1 ⟨j2, d2⟩ h2 heq
      simp only [Sigma.mk.inj_iff, heq_eq_eq] at heq
      rcases heq with ⟨hq, rfl⟩
      simp only [mem_sigma, mem_Icc, Nat.mem_divisors] at h1 h2
      have hmul1 : (j1 / d1) * d1 = j1 := Nat.div_mul_cancel h1.2.1
      have hmul2 : (j2 / d1) * d1 = j2 := Nat.div_mul_cancel h2.2.1
      simp only [Sigma.mk.inj_iff, heq_eq_eq, and_true]
      rw [← hmul1, ← hmul2, hq]
    · rintro ⟨k, d⟩ h
      simp only [mem_sigma, mem_Icc] at h
      rcases h with ⟨⟨hk1, hkn⟩, ⟨hd1, hdn⟩⟩
      have hkd_le : k * d ≤ n := by
        rw [Nat.le_div_iff_mul_le (by omega)] at hdn
        linarith
      refine ⟨⟨k * d, d⟩, ?_, ?_⟩
      · simp only [mem_sigma, mem_Icc, Nat.mem_divisors]
        exact ⟨⟨by nlinarith, hkd_le⟩, dvd_mul_left d k, by positivity⟩
      · simp only [Sigma.mk.inj_iff, heq_eq_eq, and_true]
        exact Nat.mul_div_cancel k (by omega)
    · intro _ _; rfl
  rw [h2]
  refine sum_congr rfl fun k _ => ?_
  rw [Chebyshev.psi, ← Icc_add_one_left_eq_Ioc, Nat.floor_div_eq_div]
  rfl

lemma floor_div_nat_eq (x : ℝ) (hx : 0 ≤ x) (d : ℕ) :
    ⌊x / (d : ℝ)⌋₊ = ⌊x⌋₊ / d := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  · rw [Nat.floor_eq_iff (by positivity)]
    have hfl := Nat.floor_le hx
    have hlt := Nat.lt_floor_add_one x
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd
    constructor
    · rw [le_div_iff₀ hdR]
      have hnat : (⌊x⌋₊ / d) * d ≤ ⌊x⌋₊ := Nat.div_mul_le_self ⌊x⌋₊ d
      exact le_trans (by exact_mod_cast hnat) hfl
    · rw [div_lt_iff₀ hdR]
      have hnat : ⌊x⌋₊ + 1 ≤ (⌊x⌋₊ / d + 1) * d := by
        have := Nat.lt_mul_div_succ ⌊x⌋₊ hd
        nlinarith
      exact lt_of_lt_of_le hlt (by exact_mod_cast hnat)

lemma log_factorial_div_sum (x : ℝ) (hx : 0 ≤ x) {d : ℕ} (hd : 0 < d) :
    Real.log ((⌊x / (d : ℝ)⌋₊).factorial : ℝ) =
      ∑ k ∈ (Icc 1 ⌊x⌋₊).filter (fun k => d ∣ k), Chebyshev.psi (x / (k : ℝ)) := by
  rw [log_factorial_eq_sum_psi]
  have hfl_d : ⌊x / (d : ℝ)⌋₊ = ⌊x⌋₊ / d := floor_div_nat_eq x hx d
  rw [hfl_d]
  refine sum_bij (fun m _ => d * m) ?_ ?_ ?_ ?_
  · intro m hm
    simp only [mem_Icc, mem_filter] at hm ⊢
    have hdm : d * m ≤ ⌊x⌋₊ := by
      have := (Nat.le_div_iff_mul_le hd).mp hm.2
      linarith
    exact ⟨⟨by nlinarith, hdm⟩, dvd_mul_right d m⟩
  · intro a _ b _ hab
    exact Nat.eq_of_mul_eq_mul_left hd hab
  · intro k hk
    simp only [mem_filter, mem_Icc] at hk
    rcases hk with ⟨⟨hk1, hkx⟩, ⟨m, rfl⟩⟩
    refine ⟨m, mem_Icc.mpr ⟨by nlinarith, ?_⟩, rfl⟩
    rw [Nat.le_div_iff_mul_le hd]
    linarith
  · intro m hm
    have hm_pos : 0 < m := (mem_Icc.mp hm).1
    rw [Chebyshev.psi_eq_psi_coe_floor (((⌊x⌋₊ / d : ℕ) : ℝ) / m),
      Chebyshev.psi_eq_psi_coe_floor (x / ((d * m : ℕ) : ℝ))]
    congr 1
    norm_cast
    rw [Nat.floor_div_eq_div, floor_div_nat_eq x hx (d * m), Nat.div_div_eq_div_mul]

lemma chebyshev_E_bounds {x : ℝ} (hx : 0 ≤ x) :
    (Chebyshev.psi x - Chebyshev.psi (x / 6) ≤
      Real.log ((⌊x⌋₊).factorial : ℝ) - Real.log ((⌊x / 2⌋₊).factorial : ℝ) -
      Real.log ((⌊x / 3⌋₊).factorial : ℝ) - Real.log ((⌊x / 5⌋₊).factorial : ℝ) +
      Real.log ((⌊x / 30⌋₊).factorial : ℝ)) ∧
    (Real.log ((⌊x⌋₊).factorial : ℝ) - Real.log ((⌊x / 2⌋₊).factorial : ℝ) -
      Real.log ((⌊x / 3⌋₊).factorial : ℝ) - Real.log ((⌊x / 5⌋₊).factorial : ℝ) +
      Real.log ((⌊x / 30⌋₊).factorial : ℝ) ≤ Chebyshev.psi x) := by
  let C30 : ℕ → ℕ := fun k => k + k / 30 - k / 2 - k / 3 - k / 5
  have hC30_per : ∀ k : ℕ, C30 k = C30 (k % 30) := by
    intro k
    dsimp only [C30]
    set q := k / 30
    set r := k % 30
    have hk : k = 30 * q + r := (Nat.div_add_mod k 30).symm
    have h2 : k / 2 = 15 * q + r / 2 := by omega
    have h3 : k / 3 = 10 * q + r / 3 := by omega
    have h5 : k / 5 = 6 * q + r / 5 := by omega
    omega
  have hC30_01 : ∀ k : ℕ, C30 k = 0 ∨ C30 k = 1 := by
    intro k
    rw [hC30_per k]
    have hr : k % 30 < 30 := Nat.mod_lt k (by norm_num)
    have hdec : ∀ r < 30, C30 r = 0 ∨ C30 r = 1 := by decide
    exact hdec (k % 30) hr
  have hC30_diff : ∀ k : ℕ, 1 ≤ k →
      ((C30 k : ℝ) - (C30 (k - 1) : ℝ)) =
        1 - (if 2 ∣ k then 1 else 0) - (if 3 ∣ k then 1 else 0) -
        (if 5 ∣ k then 1 else 0) + (if 30 ∣ k then 1 else 0) := by
    intro k hk
    have hC_int : (C30 k : ℤ) - (C30 (k - 1) : ℤ) =
        1 - (if 2 ∣ k then 1 else 0) - (if 3 ∣ k then 1 else 0) -
        (if 5 ∣ k then 1 else 0) + (if 30 ∣ k then 1 else 0) := by
      -- Reduce to k % 30 via periodicity of C30 and divisibility by 2, 3, 5, 30
      have hper1 : C30 k = C30 (k % 30) := hC30_per k
      have hper2 : C30 (k - 1) = C30 ((k - 1) % 30) := hC30_per (k - 1)
      rw [hper1, hper2]
      have hd2 : (2 ∣ k) ↔ (2 ∣ k % 30) := by omega
      have hd3 : (3 ∣ k) ↔ (3 ∣ k % 30) := by omega
      have hd5 : (5 ∣ k) ↔ (5 ∣ k % 30) := by omega
      have hd30 : (30 ∣ k) ↔ (30 ∣ k % 30) := by omega
      simp only [hd2, hd3, hd5, hd30]
      set r := k % 30
      have hr : r < 30 := Nat.mod_lt k (by norm_num)
      have hprev : (k - 1) % 30 = if r = 0 then 29 else r - 1 := by
        dsimp only [r]
        split_ifs <;> omega
      rw [hprev]
      have hdec : ∀ r < 30,
          (C30 r : ℤ) - (C30 (if r = 0 then 29 else r - 1) : ℤ) =
          1 - (if 2 ∣ r then 1 else 0) - (if 3 ∣ r then 1 else 0) -
          (if 5 ∣ r then 1 else 0) + (if 30 ∣ r then 1 else 0) := by decide
      exact hdec r hr
    have hcast : ((C30 k : ℤ) - (C30 (k - 1) : ℤ) : ℝ) =
        ((1 - (if 2 ∣ k then (1 : ℤ) else 0) - (if 3 ∣ k then 1 else 0) -
          (if 5 ∣ k then 1 else 0) + (if 30 ∣ k then 1 else 0) : ℤ) : ℝ) := by
      exact_mod_cast hC_int
    push_cast at hcast
    exact hcast
  set N := ⌊x⌋₊
  have hE1 : Real.log ((⌊x⌋₊).factorial : ℝ) =
      ∑ k ∈ Icc 1 N, Chebyshev.psi (x / (k : ℝ)) := by
    rw [show ⌊x⌋₊ = N from rfl]
    have h := log_factorial_div_sum x hx (d := 1) (by norm_num)
    simpa [div_one] using h
  have hE2 := log_factorial_div_sum x hx (d := 2) (by norm_num)
  have hE3 := log_factorial_div_sum x hx (d := 3) (by norm_num)
  have hE5 := log_factorial_div_sum x hx (d := 5) (by norm_num)
  have hE30 := log_factorial_div_sum x hx (d := 30) (by norm_num)
  push_cast at hE2 hE3 hE5 hE30
  have hE_sum :
      Real.log ((⌊x⌋₊).factorial : ℝ) - Real.log ((⌊x / 2⌋₊).factorial : ℝ) -
      Real.log ((⌊x / 3⌋₊).factorial : ℝ) - Real.log ((⌊x / 5⌋₊).factorial : ℝ) +
      Real.log ((⌊x / 30⌋₊).factorial : ℝ) =
      ∑ k ∈ Icc 1 N, ((C30 k : ℝ) - (C30 (k - 1) : ℝ)) * Chebyshev.psi (x / (k : ℝ)) := by
    rw [hE1, hE2, hE3, hE5, hE30]
    simp_rw [sum_filter]
    rw [← sum_sub_distrib, ← sum_sub_distrib, ← sum_sub_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun k hk => ?_
    rw [hC30_diff k (mem_Icc.mp hk).1]
    split_ifs <;> ring
  have hsbp : ∀ M : ℕ,
      ∑ k ∈ Icc 1 M, ((C30 k : ℝ) - (C30 (k - 1) : ℝ)) * Chebyshev.psi (x / (k : ℝ)) =
      (C30 M : ℝ) * Chebyshev.psi (x / ((M + 1 : ℕ) : ℝ)) +
      ∑ k ∈ Icc 1 M, (C30 k : ℝ) *
        (Chebyshev.psi (x / (k : ℝ)) - Chebyshev.psi (x / ((k + 1 : ℕ) : ℝ))) := by
    intro M
    induction M with
    | zero => simp [C30]
    | succ M ih =>
      rw [sum_Icc_succ_top (Nat.succ_pos M), sum_Icc_succ_top (Nat.succ_pos M), ih]
      simp only [Nat.add_sub_cancel]
      ring
  have htail_zero : Chebyshev.psi (x / ((N + 1 : ℕ) : ℝ)) = 0 := by
    refine Chebyshev.psi_eq_zero_of_lt_two ?_
    have hlt : x < (N : ℝ) + 1 := Nat.lt_floor_add_one x
    have hpos : (0 : ℝ) < (N + 1 : ℕ) := by positivity
    rw [div_lt_iff₀ hpos]
    push_cast
    linarith
  have hE_sbp :
      Real.log ((⌊x⌋₊).factorial : ℝ) - Real.log ((⌊x / 2⌋₊).factorial : ℝ) -
      Real.log ((⌊x / 3⌋₊).factorial : ℝ) - Real.log ((⌊x / 5⌋₊).factorial : ℝ) +
      Real.log ((⌊x / 30⌋₊).factorial : ℝ) =
      ∑ k ∈ Icc 1 N, (C30 k : ℝ) *
        (Chebyshev.psi (x / (k : ℝ)) - Chebyshev.psi (x / ((k + 1 : ℕ) : ℝ))) := by
    rw [hE_sum, hsbp N, htail_zero, mul_zero, zero_add]
  have hdiff_nonneg : ∀ k ∈ Icc 1 N,
      0 ≤ Chebyshev.psi (x / (k : ℝ)) - Chebyshev.psi (x / ((k + 1 : ℕ) : ℝ)) := by
    intro k hk
    have hk_pos : (0 : ℝ) < k := by exact_mod_cast (mem_Icc.mp hk).1
    have hle : x / ((k + 1 : ℕ) : ℝ) ≤ x / (k : ℝ) := by
      apply div_le_div_of_nonneg_left hx hk_pos
      push_cast; linarith
    linarith [Chebyshev.psi_mono hle]
  have htele : ∀ M : ℕ, 1 ≤ M →
      ∑ k ∈ Icc 1 M, (Chebyshev.psi (x / (k : ℝ)) - Chebyshev.psi (x / ((k + 1 : ℕ) : ℝ))) =
      Chebyshev.psi x - Chebyshev.psi (x / ((M + 1 : ℕ) : ℝ)) := by
    intro M hM
    induction M with
    | zero => omega
    | succ m ih =>
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp; norm_num
      · rw [sum_Icc_succ_top (Nat.succ_pos m), ih hm]
        ring
  rw [hE_sbp]
  constructor
  · rcases lt_or_ge N 6 with hN6 | hN6
    · have hx6 : Chebyshev.psi (x / 6) = 0 := by
        refine Chebyshev.psi_eq_zero_of_lt_two ?_
        have hlt : x < (N : ℝ) + 1 := Nat.lt_floor_add_one x
        have hN5 : (N : ℝ) ≤ 5 := by exact_mod_cast (show N ≤ 5 by omega)
        linarith
      rw [hx6, sub_zero]
      rcases Nat.eq_zero_or_pos N with hN0 | hNpos
      · have hx1 : x < 1 := by
          have hlt : x < (N : ℝ) + 1 := Nat.lt_floor_add_one x
          rw [hN0] at hlt; simpa using hlt
        rw [Chebyshev.psi_eq_zero_of_lt_two (by linarith), hN0]
        simp
      · have hC1 : ∀ k ∈ Icc 1 N, (C30 k : ℝ) = 1 := by
          intro k hk
          have hk1 := (mem_Icc.mp hk).1
          have hk5 : k ≤ 5 := by have := (mem_Icc.mp hk).2; omega
          have : C30 k = 1 := by dsimp only [C30]; omega
          exact_mod_cast this
        have heq : ∑ k ∈ Icc 1 N, (C30 k : ℝ) *
            (Chebyshev.psi (x / (k : ℝ)) - Chebyshev.psi (x / ((k + 1 : ℕ) : ℝ))) =
            ∑ k ∈ Icc 1 N, (Chebyshev.psi (x / (k : ℝ)) - Chebyshev.psi (x / ((k + 1 : ℕ) : ℝ))) :=
          sum_congr rfl fun k hk => by rw [hC1 k hk, one_mul]
        rw [heq, htele N hNpos, htail_zero, sub_zero]
    · have hsub : Icc 1 5 ⊆ Icc 1 N := Icc_subset_Icc_right (by omega)
      have hnonneg : ∀ k ∈ Icc 1 N, 0 ≤ (C30 k : ℝ) *
          (Chebyshev.psi (x / (k : ℝ)) - Chebyshev.psi (x / ((k + 1 : ℕ) : ℝ))) := fun k hk =>
        mul_nonneg (Nat.cast_nonneg _) (hdiff_nonneg k hk)
      have hge := sum_le_sum_of_subset_of_nonneg hsub fun k hk _ => hnonneg k hk
      have hC1 : ∀ k ∈ Icc 1 5, (C30 k : ℝ) = 1 := by
        intro k hk
        have hk1 := (mem_Icc.mp hk).1
        have hk5 := (mem_Icc.mp hk).2
        have : C30 k = 1 := by dsimp only [C30]; omega
        exact_mod_cast this
      have h5 : ∑ k ∈ Icc (1 : ℕ) 5, (C30 k : ℝ) *
          (Chebyshev.psi (x / (k : ℝ)) - Chebyshev.psi (x / ((k + 1 : ℕ) : ℝ))) =
          Chebyshev.psi x - Chebyshev.psi (x / 6) := by
        have heq : ∑ k ∈ Icc (1 : ℕ) 5, (C30 k : ℝ) *
            (Chebyshev.psi (x / (k : ℝ)) - Chebyshev.psi (x / ((k + 1 : ℕ) : ℝ))) =
            ∑ k ∈ Icc (1 : ℕ) 5, (Chebyshev.psi (x / (k : ℝ)) - Chebyshev.psi (x / ((k + 1 : ℕ) : ℝ))) :=
          sum_congr rfl fun k hk => by rw [hC1 k hk, one_mul]
        rw [heq, htele 5 (by norm_num)]
        norm_num
      linarith
  · rcases Nat.eq_zero_or_pos N with hN0 | hNpos
    · rw [hN0]; simp [Chebyshev.psi_nonneg]
    · calc ∑ k ∈ Icc 1 N, (C30 k : ℝ) *
            (Chebyshev.psi (x / (k : ℝ)) - Chebyshev.psi (x / ((k + 1 : ℕ) : ℝ)))
          ≤ ∑ k ∈ Icc 1 N, 1 *
            (Chebyshev.psi (x / (k : ℝ)) - Chebyshev.psi (x / ((k + 1 : ℕ) : ℝ))) := by
            refine sum_le_sum fun k hk => ?_
            have hCle : (C30 k : ℝ) ≤ 1 := by
              rcases hC30_01 k with h | h <;> simp [h]
            exact mul_le_mul_of_nonneg_right hCle (hdiff_nonneg k hk)
        _ = Chebyshev.psi x - Chebyshev.psi (x / ((N + 1 : ℕ) : ℝ)) := by
            simp_rw [one_mul]; exact htele N hNpos
        _ = Chebyshev.psi x := by rw [htail_zero, sub_zero]

/- Zero-integral elementary Stirling bounds on log(⌊x⌋!) -/

lemma log_factorial_bounds_nat {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) * Real.log n - n + 1 ≤ Real.log (n.factorial : ℝ) ∧
    Real.log (n.factorial : ℝ) ≤ (n : ℝ) * Real.log n - n + 1 + Real.log n := by
  induction n with
  | zero => omega
  | succ m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · have ⟨hlo, hhi⟩ := ih hm
      have hmR : (0 : ℝ) < m := by exact_mod_cast hm
      have hm1R : (0 : ℝ) < (m + 1 : ℕ) := by positivity
      have hfac : Real.log ((m + 1).factorial : ℝ) = Real.log (m.factorial : ℝ) + Real.log (m + 1 : ℝ) := by
        rw [Nat.factorial_succ, Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]
        push_cast; ring
      rw [hfac]
      push_cast
      constructor
      · -- (m+1) log (m+1) - (m+1) + 1 ≤ m log m - m + 1 + log (m+1)
        -- ↔ m (log (m+1) - log m) ≤ 1 ↔ m log ((m+1)/m) ≤ 1
        have h1 : Real.log (((m : ℝ) + 1) / m) ≤ ((m : ℝ) + 1) / m - 1 :=
          Real.log_le_sub_one_of_pos (by positivity)
        rw [Real.log_div (by linarith) hmR.ne'] at h1
        have h2 : (m : ℝ) * (Real.log ((m : ℝ) + 1) - Real.log m) ≤ 1 := by
          have := mul_le_mul_of_nonneg_left h1 hmR.le
          have hrhs : (m : ℝ) * (((m : ℝ) + 1) / m - 1) = 1 := by field_simp; ring
          linarith
        linarith
      · -- m log m - m + 1 + log m + log (m+1) ≤ (m+1) log (m+1) - (m+1) + 1 + log (m+1)
        -- ↔ m log m + log m + 1 ≤ (m+1) log (m+1) ↔ (m+1) log (m/(m+1)) ≤ -1
        have h1 : Real.log ((m : ℝ) / ((m : ℝ) + 1)) ≤ (m : ℝ) / ((m : ℝ) + 1) - 1 :=
          Real.log_le_sub_one_of_pos (by positivity)
        rw [Real.log_div hmR.ne' (by linarith)] at h1
        have h2 : ((m : ℝ) + 1) * (Real.log m - Real.log ((m : ℝ) + 1)) ≤ -1 := by
          have := mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ (m : ℝ) + 1)
          have hrhs : ((m : ℝ) + 1) * ((m : ℝ) / ((m : ℝ) + 1) - 1) = -1 := by field_simp; ring
          linarith
        linarith

lemma log_factorial_floor_bounds {x : ℝ} (hx : 1 ≤ x) :
    x * Real.log x - x + 1 - Real.log x ≤ Real.log ((⌊x⌋₊).factorial : ℝ) ∧
    Real.log ((⌊x⌋₊).factorial : ℝ) ≤ x * Real.log x - x + 1 + Real.log x := by
  set n := ⌊x⌋₊
  have hn1 : 1 ≤ n := (Nat.one_le_floor_iff x).mpr hx
  have ⟨hlo, hhi⟩ := log_factorial_bounds_nat hn1
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn_le : (n : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hx_lt : x < (n : ℝ) + 1 := Nat.lt_floor_add_one x
  have hlog_le : Real.log n ≤ Real.log x := Real.log_le_log hn_pos hn_le
  have hlog_nonneg : 0 ≤ Real.log x := Real.log_nonneg hx
  constructor
  · -- x log x - x - (n log n - n) = (x - n) log x + n log (x / n) - (x - n) ≤ (x - n) log x ≤ log x
    have h1 : Real.log (x / n) ≤ x / n - 1 := Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div (by linarith) hn_pos.ne'] at h1
    have h2 : (n : ℝ) * (Real.log x - Real.log n) ≤ x - n := by
      have := mul_le_mul_of_nonneg_left h1 hn_pos.le
      have hrhs : (n : ℝ) * (x / n - 1) = x - n := by field_simp
      linarith
    have h3 : (x - n) * Real.log x ≤ Real.log x := by nlinarith
    linarith
  · -- n log n - n ≤ x log x - x since x log (n / x) ≤ n - x → n log n - n ≤ x log x - x
    have h1 : Real.log ((n : ℝ) / x) ≤ (n : ℝ) / x - 1 := Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div hn_pos.ne' (by linarith)] at h1
    have h2 : x * (Real.log n - Real.log x) ≤ n - x := by
      have := mul_le_mul_of_nonneg_left h1 (by linarith : 0 ≤ x)
      have hrhs : x * ((n : ℝ) / x - 1) = n - x := by field_simp
      linarith
    have h3 : (x - n) * Real.log n ≥ 0 := by
      have : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn1)
      nlinarith
    linarith

lemma chebyshev_E_analytic_bounds {x : ℝ} (hx : 30 ≤ x) :
    ((7 / 15 : ℝ) * Real.log 2 + (3 / 10 : ℝ) * Real.log 3 + (1 / 6 : ℝ) * Real.log 5) * x -
        5 * Real.log x - 1 ≤
      Real.log ((⌊x⌋₊).factorial : ℝ) - Real.log ((⌊x / 2⌋₊).factorial : ℝ) -
      Real.log ((⌊x / 3⌋₊).factorial : ℝ) - Real.log ((⌊x / 5⌋₊).factorial : ℝ) +
      Real.log ((⌊x / 30⌋₊).factorial : ℝ) ∧
    Real.log ((⌊x⌋₊).factorial : ℝ) - Real.log ((⌊x / 2⌋₊).factorial : ℝ) -
      Real.log ((⌊x / 3⌋₊).factorial : ℝ) - Real.log ((⌊x / 5⌋₊).factorial : ℝ) +
      Real.log ((⌊x / 30⌋₊).factorial : ℝ) ≤
      ((7 / 15 : ℝ) * Real.log 2 + (3 / 10 : ℝ) * Real.log 3 + (1 / 6 : ℝ) * Real.log 5) * x +
        5 * Real.log x := by
  have h1 := log_factorial_floor_bounds (x := x) (by linarith)
  have h2 := log_factorial_floor_bounds (x := x / 2) (by linarith)
  have h3 := log_factorial_floor_bounds (x := x / 3) (by linarith)
  have h5 := log_factorial_floor_bounds (x := x / 5) (by linarith)
  have h30 := log_factorial_floor_bounds (x := x / 30) (by linarith)
  have hl2 : Real.log (x / 2) = Real.log x - Real.log 2 :=
    Real.log_div (by linarith) (by norm_num)
  have hl3 : Real.log (x / 3) = Real.log x - Real.log 3 :=
    Real.log_div (by linarith) (by norm_num)
  have hl5 : Real.log (x / 5) = Real.log x - Real.log 5 :=
    Real.log_div (by linarith) (by norm_num)
  have hl30 : Real.log (x / 30) = Real.log x - Real.log 2 - Real.log 3 - Real.log 5 := by
    rw [Real.log_div (by linarith) (by norm_num),
      show (30 : ℝ) = 2 * 3 * 5 by norm_num,
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num)]
    ring
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog3_pos : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlog5_pos : 0 < Real.log 5 := Real.log_pos (by norm_num)
  rw [hl2] at h2
  rw [hl3] at h3
  rw [hl5] at h5
  rw [hl30] at h30
  constructor <;> linarith

lemma psi_30_lower {x : ℝ} (hx : 30 ≤ x) :
    ((7 / 15 : ℝ) * Real.log 2 + (3 / 10 : ℝ) * Real.log 3 + (1 / 6 : ℝ) * Real.log 5) * x -
        5 * Real.log x - 1 ≤ Chebyshev.psi x := by
  have h1 := (chebyshev_E_analytic_bounds hx).1
  have h2 := (chebyshev_E_bounds (by linarith : 0 ≤ x)).2
  linarith

lemma psi_30_upper {x : ℝ} (hx : 1 ≤ x) :
    Chebyshev.psi x ≤
      (6 / 5 : ℝ) * ((7 / 15 : ℝ) * Real.log 2 + (3 / 10 : ℝ) * Real.log 3 +
        (1 / 6 : ℝ) * Real.log 5) * x + 2 * (Real.log x) ^ 2 + 30 := by
  set A : ℝ := (7 / 15 : ℝ) * Real.log 2 + (3 / 10 : ℝ) * Real.log 3 + (1 / 6 : ℝ) * Real.log 5
  have hstrong : ∀ n : ℕ, 1 ≤ n → ∀ y : ℝ, 1 ≤ y → ⌊y⌋₊ = n →
      Chebyshev.psi y ≤ (6 / 5 : ℝ) * A * y + 2 * (Real.log y) ^ 2 + 30 := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro hn y hy hfl
      rcases lt_or_ge y 30 with hy30 | hy30
      · -- Base case: y < 30 → psi y ≤ psi 29 ≤ log 4 * 29? Even simpler: psi y ≤ log (lcmUpto 29) < 30!
        have hylt : ⌊y⌋₊ ≤ 29 := by
          have : ⌊y⌋₊ < 30 := (Nat.floor_lt (by linarith)).mpr hy30
          omega
        have hle29 : Chebyshev.psi y ≤ Chebyshev.psi 29 := by
          rw [Chebyshev.psi_eq_psi_coe_floor y]
          exact Chebyshev.psi_mono (by exact_mod_cast hylt)
        have hlcm29 : Nat.lcmUpto 29 < 2 ^ 42 := by decide
        have hpsi29 : Chebyshev.psi 29 ≤ 30 := by
          change Chebyshev.psi ((29 : ℕ) : ℝ) ≤ 30
          rw [Chebyshev.psi_eq_log_lcmUpto]
          have h1 : Real.log (Nat.lcmUpto 29 : ℝ) ≤ Real.log ((2 : ℝ) ^ 42) :=
            Real.log_le_log (by exact_mod_cast Nat.lcmUpto_pos 29) (by exact_mod_cast hlcm29.le)
          rw [Real.log_pow] at h1
          have hl2 := Real.log_two_lt_d9
          push_cast at h1
          linarith
        have hApos : 0 < A := by
          have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
          have := Real.log_pos (by norm_num : (1 : ℝ) < 3)
          have := Real.log_pos (by norm_num : (1 : ℝ) < 5)
          dsimp only [A]; positivity
        nlinarith [sq_nonneg (Real.log y)]
      · -- Inductive step: y ≥ 30 → y / 6 ≥ 5 ≥ 1 and ⌊y / 6⌋₊ < ⌊y⌋₊
        have hstep := (chebyshev_E_bounds (by linarith : 0 ≤ y)).1
        have hana := (chebyshev_E_analytic_bounds hy30).2
        have hy6_ge : 1 ≤ y / 6 := by linarith
        have hfl6_lt : ⌊y / 6⌋₊ < n := by
          rw [← hfl]
          have h6eq : ⌊y / 6⌋₊ = ⌊y⌋₊ / 6 := by
            simpa using floor_div_nat_eq y (by linarith) 6
          rw [h6eq]
          have hn30 : 30 ≤ ⌊y⌋₊ := (Nat.le_floor_iff (by linarith)).mpr hy30
          omega
        have hfl6_pos : 1 ≤ ⌊y / 6⌋₊ := (Nat.one_le_floor_iff _).mpr hy6_ge
        have hih := ih ⌊y / 6⌋₊ hfl6_lt hfl6_pos (y / 6) hy6_ge rfl
        have hl6 : Real.log (y / 6) = Real.log y - Real.log 6 :=
          Real.log_div (by linarith) (by norm_num)
        rw [hl6] at hih
        have hlog6_lo : (1.79 : ℝ) < Real.log 6 := by
          rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
          have := Real.log_two_gt_d9
          have := log_small_constants.1
          linarith
        have hlog6_hi : Real.log 6 < (1.80 : ℝ) := by
          rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
          have := Real.log_two_lt_d9
          have := log_small_constants.2.1
          linarith
        have hlogy_ge : (3.4 : ℝ) ≤ Real.log y := by
          have h30 : Real.log (30 : ℝ) ≤ Real.log y := Real.log_le_log (by norm_num) hy30
          have h30_val : (3.4 : ℝ) ≤ Real.log (30 : ℝ) := by
            rw [show (30 : ℝ) = 2 * 3 * 5 by norm_num,
              Real.log_mul (by norm_num) (by norm_num),
              Real.log_mul (by norm_num) (by norm_num)]
            have := Real.log_two_gt_d9
            have := log_small_constants
            linarith
          linarith
        have hquad : 5 * Real.log y ≤ 2 * ((Real.log y) ^ 2 - (Real.log y - Real.log 6) ^ 2) := by
          have hid : 2 * ((Real.log y) ^ 2 - (Real.log y - Real.log 6) ^ 2) =
              4 * Real.log 6 * Real.log y - 2 * (Real.log 6) ^ 2 := by ring
          rw [hid]
          nlinarith
        dsimp only [A] at hih ⊢
        linarith
  exact hstrong ⌊x⌋₊ ((Nat.one_le_floor_iff x).mpr hx) x hx rfl

/- Discrete summation by parts for ∑_{x0 < p ≤ X} 1 / p (zero MeasureTheory) -/

lemma inv_mul_log_diff_le {n : ℕ} (hn : 3 ≤ n) :
    1 / ((n : ℝ) * Real.log n) - 1 / (((n + 1 : ℕ) : ℝ) * Real.log (n + 1 : ℕ)) ≤
      (Real.log n + 1) / ((n : ℝ) ^ 2 * (Real.log n) ^ 2) := by
  let h : ℝ → ℝ := fun t => (t * Real.log t)⁻¹
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog3 : (1 : ℝ) < Real.log 3 := by have := log_small_constants.1; linarith
  have hderiv : ∀ t ∈ Set.Ioo (n : ℝ) ((n : ℝ) + 1),
      HasDerivAt h (-(Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2)) t := by
    intro t ⟨ht1, _⟩
    have ht0 : t ≠ 0 := by linarith
    have hlt_pos : 0 < Real.log t := lt_trans (by linarith) (Real.log_lt_log (by norm_num) (by linarith))
    have hprod : HasDerivAt (fun u => u * Real.log u) (Real.log t + 1) t :=
      ((hasDerivAt_id t).mul (Real.hasDerivAt_log ht0)).congr_deriv (by
        simp [mul_inv_cancel₀ ht0])
    have hinv : HasDerivAt (fun u => (u * Real.log u)⁻¹)
        (-(Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2)) t :=
      (hprod.inv (mul_ne_zero ht0 hlt_pos.ne')).congr_deriv (by rw [mul_pow])
    exact hinv
  have hcont : ContinuousOn h (Set.Icc (n : ℝ) ((n : ℝ) + 1)) := by
    refine ContinuousOn.inv₀ (continuousOn_id.mul ?_) ?_
    · exact ContinuousOn.log continuousOn_id fun t ht => by linarith [ht.1]
    · intro t ht
      have hlt_pos : 0 < Real.log t := lt_of_lt_of_le (by linarith) (Real.log_le_log (by norm_num) (by linarith [ht.1]))
      exact mul_ne_zero (by linarith [ht.1]) hlt_pos.ne'
  obtain ⟨ξ, ⟨hξ1, hξ2⟩, hslope⟩ :=
    exists_hasDerivAt_eq_slope h (fun t => -(Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2))
      (by linarith : (n : ℝ) < (n : ℝ) + 1) hcont hderiv
  have hdiff : h n - h ((n : ℝ) + 1) = (Real.log ξ + 1) / (ξ ^ 2 * (Real.log ξ) ^ 2) := by
    simp only [add_sub_cancel_left, div_one, neg_div] at hslope
    linarith
  have hlogn_pos : 0 < Real.log n := lt_of_lt_of_le (by linarith) (Real.log_le_log (by norm_num) hnR)
  have hlogξ_ge : Real.log n ≤ Real.log ξ := Real.log_le_log (by linarith) hξ1.le
  have hlogξ_pos : 0 < Real.log ξ := lt_of_lt_of_le hlogn_pos hlogξ_ge
  have hsplitξ : (Real.log ξ + 1) / (ξ ^ 2 * (Real.log ξ) ^ 2) =
      1 / (ξ ^ 2 * Real.log ξ) + 1 / (ξ ^ 2 * (Real.log ξ) ^ 2) := by field_simp
  have hsplitn : (Real.log n + 1) / ((n : ℝ) ^ 2 * (Real.log n) ^ 2) =
      1 / ((n : ℝ) ^ 2 * Real.log n) + 1 / ((n : ℝ) ^ 2 * (Real.log n) ^ 2) := by field_simp
  have hbound1 : 1 / (ξ ^ 2 * Real.log ξ) ≤ 1 / ((n : ℝ) ^ 2 * Real.log n) := by
    refine one_div_le_one_div_of_le (by positivity) ?_
    exact mul_le_mul (by nlinarith) hlogξ_ge hlogn_pos.le (by positivity)
  have hbound2 : 1 / (ξ ^ 2 * (Real.log ξ) ^ 2) ≤ 1 / ((n : ℝ) ^ 2 * (Real.log n) ^ 2) := by
    refine one_div_le_one_div_of_le (by positivity) ?_
    exact mul_le_mul (by nlinarith) (by nlinarith) (by positivity) (by positivity)
  have hcast : (((n + 1 : ℕ) : ℝ)) = (n : ℝ) + 1 := by push_cast; rfl
  rw [hcast]
  have h1 : 1 / ((n : ℝ) * Real.log n) = h n := by simp [h]
  have h2 : 1 / (((n : ℝ) + 1) * Real.log ((n : ℝ) + 1)) = h ((n : ℝ) + 1) := by simp [h]
  rw [h1, h2]
  linarith

lemma log_log_sub_inv_log_step {n : ℕ} (hn : 4 ≤ n) :
    (Real.log n + 1) / ((n : ℝ) * (Real.log n) ^ 2) ≤
      (Real.log (Real.log n) - 1 / Real.log n) -
      (Real.log (Real.log ((n - 1 : ℕ) : ℝ)) - 1 / Real.log ((n - 1 : ℕ) : ℝ)) := by
  let G : ℝ → ℝ := fun t => Real.log (Real.log t) - (Real.log t)⁻¹
  have hn4 : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hnm1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  rw [hnm1]
  have hlog3 : (1 : ℝ) < Real.log 3 := by have := log_small_constants.1; linarith
  have hderiv : ∀ t ∈ Set.Ioo ((n : ℝ) - 1) (n : ℝ),
      HasDerivAt G ((Real.log t + 1) / (t * (Real.log t) ^ 2)) t := by
    intro t ⟨ht1, _⟩
    have ht3 : (3 : ℝ) < t := by linarith
    have ht0 : t ≠ 0 := by linarith
    have hlt_pos : 0 < Real.log t := lt_trans (by linarith) (Real.log_lt_log (by norm_num) ht3)
    have h1 : HasDerivAt (fun u => Real.log (Real.log u)) (t⁻¹ / Real.log t) t :=
      (Real.hasDerivAt_log ht0).log hlt_pos.ne'
    have h2 : HasDerivAt (fun u => (Real.log u)⁻¹) (-t⁻¹ / (Real.log t) ^ 2) t :=
      (Real.hasDerivAt_log ht0).inv hlt_pos.ne'
    exact (h1.sub h2).congr_deriv (by field_simp; ring)
  have hcont : ContinuousOn G (Set.Icc ((n : ℝ) - 1) (n : ℝ)) := by
    have hlog_cont : ContinuousOn Real.log (Set.Icc ((n : ℝ) - 1) (n : ℝ)) :=
      ContinuousOn.log continuousOn_id fun t ht => by linarith [ht.1]
    have hlog_ne : ∀ t ∈ Set.Icc ((n : ℝ) - 1) (n : ℝ), Real.log t ≠ 0 := fun t ht =>
      (lt_of_lt_of_le (by linarith) (Real.log_le_log (by norm_num) (by linarith [ht.1]))).ne'
    exact (hlog_cont.log hlog_ne).sub (hlog_cont.inv₀ hlog_ne)
  obtain ⟨ξ, ⟨hξ1, hξ2⟩, hslope⟩ :=
    exists_hasDerivAt_eq_slope G (fun t => (Real.log t + 1) / (t * (Real.log t) ^ 2))
      (by linarith : (n : ℝ) - 1 < (n : ℝ)) hcont hderiv
  have hdiff : G n - G ((n : ℝ) - 1) = (Real.log ξ + 1) / (ξ * (Real.log ξ) ^ 2) := by
    have hsub1 : (n : ℝ) - ((n : ℝ) - 1) = 1 := by ring
    rw [hsub1, div_one] at hslope
    exact hslope.symm
  have hξ3 : (3 : ℝ) < ξ := by linarith
  have hlogξ_pos : 0 < Real.log ξ := lt_trans (by linarith) (Real.log_lt_log (by norm_num) hξ3)
  have hlogξ_le : Real.log ξ ≤ Real.log n := Real.log_le_log (by linarith) hξ2.le
  have hlogn_pos : 0 < Real.log n := lt_of_lt_of_le hlogξ_pos hlogξ_le
  have hsplitξ : (Real.log ξ + 1) / (ξ * (Real.log ξ) ^ 2) =
      1 / (ξ * Real.log ξ) + 1 / (ξ * (Real.log ξ) ^ 2) := by field_simp
  have hsplitn : (Real.log n + 1) / ((n : ℝ) * (Real.log n) ^ 2) =
      1 / ((n : ℝ) * Real.log n) + 1 / ((n : ℝ) * (Real.log n) ^ 2) := by field_simp
  have hbound1 : 1 / ((n : ℝ) * Real.log n) ≤ 1 / (ξ * Real.log ξ) := by
    refine one_div_le_one_div_of_le (by positivity) ?_
    exact mul_le_mul hξ2.le hlogξ_le hlogξ_pos.le (by linarith)
  have hbound2 : 1 / ((n : ℝ) * (Real.log n) ^ 2) ≤ 1 / (ξ * (Real.log ξ) ^ 2) := by
    refine one_div_le_one_div_of_le (by positivity) ?_
    exact mul_le_mul hξ2.le (by nlinarith) (by positivity) (by linarith)
  have hGn : Real.log (Real.log n) - 1 / Real.log n = G n := by simp [G]
  have hGm : Real.log (Real.log ((n : ℝ) - 1)) - 1 / Real.log ((n : ℝ) - 1) = G ((n : ℝ) - 1) := by
    simp [G]
  rw [hGn, hGm]
  linarith

lemma log_div_sq_step {n : ℕ} (hn : 4 ≤ n) :
    Real.log n / (n : ℝ) ^ 2 ≤
      (Real.log ((n - 1 : ℕ) : ℝ) + 1) / ((n - 1 : ℕ) : ℝ) - (Real.log n + 1) / (n : ℝ) := by
  let H : ℝ → ℝ := fun t => -((Real.log t + 1) / t)
  have hn4 : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hnm1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  rw [hnm1]
  have hlog3 : (1 : ℝ) < Real.log 3 := by have := log_small_constants.1; linarith
  have hderiv : ∀ t ∈ Set.Ioo ((n : ℝ) - 1) (n : ℝ),
      HasDerivAt H (Real.log t / t ^ 2) t := by
    intro t ⟨ht1, _⟩
    have ht0 : t ≠ 0 := by linarith
    have hnum : HasDerivAt (fun u => Real.log u + 1) t⁻¹ t :=
      (Real.hasDerivAt_log ht0).add_const 1
    have hdiv := hnum.div (hasDerivAt_id t) ht0
    exact hdiv.neg.congr_deriv (by simp only [id_eq]; field_simp; ring)
  have hcont : ContinuousOn H (Set.Icc ((n : ℝ) - 1) (n : ℝ)) := by
    refine ContinuousOn.neg ?_
    refine ContinuousOn.div ?_ (continuousOn_id (s := Set.Icc ((n : ℝ) - 1) (n : ℝ))) ?_
    · exact (ContinuousOn.log continuousOn_id fun t ht => by simp only [id_eq]; linarith [ht.1]).add
        continuousOn_const
    · intro t ht; change t ≠ 0; linarith [ht.1]
  obtain ⟨ξ, ⟨hξ1, hξ2⟩, hslope⟩ :=
    exists_hasDerivAt_eq_slope H (fun t => Real.log t / t ^ 2)
      (by linarith : (n : ℝ) - 1 < (n : ℝ)) hcont hderiv
  have hdiff : H n - H ((n : ℝ) - 1) = Real.log ξ / ξ ^ 2 := by
    have hsub1 : (n : ℝ) - ((n : ℝ) - 1) = 1 := by ring
    rw [hsub1, div_one] at hslope
    exact hslope.symm
  let F : ℝ → ℝ := fun t => Real.log t / t ^ 2
  have hFderiv : ∀ t : ℝ, 3 < t →
      HasDerivAt F ((t⁻¹ * t ^ 2 - Real.log t * (2 * t)) / (t ^ 2) ^ 2) t := by
    intro t ht3
    have h1 := (Real.hasDerivAt_log (by linarith : t ≠ 0)).div (hasDerivAt_pow 2 t) (by positivity)
    exact h1.congr_deriv (by simp)
  have hanti : AntitoneOn F (Set.Ici 3) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici 3) ?_ ?_ ?_
    · refine ContinuousOn.div (ContinuousOn.log continuousOn_id fun t ht => by linarith [Set.mem_Ici.mp ht])
        (by fun_prop) fun t ht => by positivity [Set.mem_Ici.mp ht]
    · intro t ht
      have ht3 : (3 : ℝ) < t := by simpa [interior_Ici] using ht
      exact (hFderiv t ht3).differentiableAt.differentiableWithinAt
    · intro t ht
      have ht3 : (3 : ℝ) < t := by simpa [interior_Ici] using ht
      rw [(hFderiv t ht3).deriv]
      have hlogt : (1 : ℝ) < Real.log t := lt_trans hlog3 (Real.log_lt_log (by norm_num) ht3)
      have heq : (t⁻¹ * t ^ 2 - Real.log t * (2 * t)) / (t ^ 2) ^ 2 =
          (1 - 2 * Real.log t) / t ^ 3 := by field_simp
      rw [heq]
      exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  have hle : Real.log n / (n : ℝ) ^ 2 ≤ Real.log ξ / ξ ^ 2 :=
    hanti (Set.mem_Ici.mpr (by linarith)) (Set.mem_Ici.mpr (by linarith)) hξ2.le
  have hHeq : H n - H ((n : ℝ) - 1) =
      (Real.log ((n : ℝ) - 1) + 1) / ((n : ℝ) - 1) - (Real.log n + 1) / (n : ℝ) := by
    simp [H]; ring
  linarith

lemma sum_inv_primes_Ioc_le {x0 X : ℕ} (hx0 : 5000 ≤ x0) (hX : x0 + 1 < X) :
    ∑ p ∈ (Nat.primesLE X \ Nat.primesLE x0), (1 : ℝ) / p ≤
      (6 / 5 : ℝ) * ((7 / 15 : ℝ) * Real.log 2 + (3 / 10 : ℝ) * Real.log 3 +
        (1 / 6 : ℝ) * Real.log 5) *
        (Real.log (Real.log X) - Real.log (Real.log x0) + 1 / Real.log x0) -
      Chebyshev.theta x0 / (((x0 + 1 : ℕ) : ℝ) * Real.log (x0 + 1 : ℕ)) +
      3 * ((Real.log x0 + 1) / (x0 : ℝ)) +
      (2 * (Real.log X) ^ 2 + 30) / ((X : ℝ) * Real.log X) := by
  set A : ℝ := (7 / 15 : ℝ) * Real.log 2 + (3 / 10 : ℝ) * Real.log 3 + (1 / 6 : ℝ) * Real.log 5
  set C0 : ℝ := (6 / 5 : ℝ) * A
  -- Express ∑_{x0 < p ≤ X} 1 / p as ∑_{n = x0 + 1}^X (θ(n) - θ(n - 1)) / (n log n)
  have htheta_step : ∀ n : ℕ, 2 ≤ n →
      Chebyshev.theta n - Chebyshev.theta (n - 1 : ℕ) = if n.Prime then Real.log n else 0 := by
    intro n hn
    rw [Chebyshev.theta_eq_sum_Icc, Chebyshev.theta_eq_sum_Icc]
    simp only [Nat.floor_natCast]
    have hsplit : Icc 0 n = insert n (Icc 0 (n - 1)) := by
      ext k; simp only [mem_Icc, mem_insert]; omega
    have hnotmem : n ∉ Icc 0 (n - 1) := by simp only [mem_Icc]; omega
    rw [hsplit, sum_filter, sum_filter, sum_insert hnotmem]
    ring
  have hsum_eq : ∑ p ∈ (Nat.primesLE X \ Nat.primesLE x0), (1 : ℝ) / p =
      ∑ n ∈ Icc (x0 + 1) X,
        (Chebyshev.theta n - Chebyshev.theta (n - 1 : ℕ)) / ((n : ℝ) * Real.log n) := by
    have hset : Nat.primesLE X \ Nat.primesLE x0 = (Icc (x0 + 1) X).filter Nat.Prime := by
      ext p
      simp only [mem_sdiff, Nat.mem_primesLE, mem_filter, mem_Icc]
      constructor
      · rintro ⟨⟨hpX, hp⟩, hnot⟩
        refine ⟨⟨?_, hpX⟩, hp⟩
        by_contra hle; push Not at hle
        exact hnot ⟨by omega, hp⟩
      · rintro ⟨⟨hplo, hpX⟩, hp⟩
        exact ⟨⟨hpX, hp⟩, fun h => by omega⟩
    rw [hset, sum_filter]
    refine sum_congr rfl fun n hn => ?_
    have hn2 : 2 ≤ n := by have := (mem_Icc.mp hn).1; omega
    rw [htheta_step n hn2]
    split_ifs with hp
    · have hlogn : Real.log (n : ℝ) ≠ 0 :=
        (Real.log_pos (by exact_mod_cast (show 1 < n by omega))).ne'
      field_simp
    · simp
  -- Discrete summation by parts on Icc (x0 + 1) X
  let w : ℕ → ℝ := fun n => 1 / ((n : ℝ) * Real.log n)
  have hsbp : ∀ M : ℕ, x0 + 1 ≤ M →
      ∑ n ∈ Icc (x0 + 1) M, (Chebyshev.theta n - Chebyshev.theta (n - 1 : ℕ)) * w n =
      Chebyshev.theta M * w M - Chebyshev.theta x0 * w (x0 + 1) +
      ∑ n ∈ Icc (x0 + 1) (M - 1), Chebyshev.theta n * (w n - w (n + 1)) := by
    intro M hM
    induction M with
    | zero => omega
    | succ m ih =>
      rcases eq_or_lt_of_le hM with hEq | hLt
      · have hm : m = x0 := by omega
        rw [hm, Icc_self, sum_singleton, Nat.add_sub_cancel,
          Icc_eq_empty (by omega : ¬ x0 + 1 ≤ x0), sum_empty, add_zero]
        ring
      · have ih' := ih (by omega)
        rw [sum_Icc_succ_top (by omega : x0 + 1 ≤ m + 1), ih']
        have hsub : m + 1 - 1 = m := Nat.add_sub_cancel m 1
        rw [hsub]
        have hsplit : Icc (x0 + 1) m = insert m (Icc (x0 + 1) (m - 1)) := by
          ext k; simp only [mem_Icc, mem_insert]; omega
        have hnotmem : m ∉ Icc (x0 + 1) (m - 1) := by simp only [mem_Icc]; omega
        rw [hsplit, sum_insert hnotmem]
        ring
  rw [hsum_eq]
  have hsum_w : ∑ n ∈ Icc (x0 + 1) X,
      (Chebyshev.theta n - Chebyshev.theta (n - 1 : ℕ)) / ((n : ℝ) * Real.log n) =
      ∑ n ∈ Icc (x0 + 1) X, (Chebyshev.theta n - Chebyshev.theta (n - 1 : ℕ)) * w n := by
    refine sum_congr rfl fun n _ => by simp [w, div_eq_mul_inv]
  rw [hsum_w, hsbp X (by omega)]
  -- Bound each term in ∑_{n = x0 + 1}^{X - 1} θ(n) * (w n - w (n + 1))
  have hterm_le : ∀ n ∈ Icc (x0 + 1) (X - 1),
      Chebyshev.theta n * (w n - w (n + 1)) ≤
        C0 * ((Real.log (Real.log n) - 1 / Real.log n) -
          (Real.log (Real.log ((n - 1 : ℕ) : ℝ)) - 1 / Real.log ((n - 1 : ℕ) : ℝ))) +
        3 * ((Real.log ((n - 1 : ℕ) : ℝ) + 1) / ((n - 1 : ℕ) : ℝ) -
          (Real.log n + 1) / (n : ℝ)) := by
    intro n hn
    have hn5000 : 5000 ≤ n := by have := (mem_Icc.mp hn).1; omega
    have hnR : (5000 : ℝ) ≤ n := by exact_mod_cast hn5000
    have hlog5000 : (8.5 : ℝ) ≤ Real.log 5000 := by
      have h5000 : (5000 : ℝ) = 2 ^ 3 * 5 ^ 4 := by norm_num
      rw [h5000, Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]
      have := Real.log_two_gt_d9
      have := log_small_constants.2.2.1
      push_cast; linarith
    have hlogn_ge : (8.5 : ℝ) ≤ Real.log n :=
      le_trans hlog5000 (Real.log_le_log (by norm_num) hnR)
    have hth_le : Chebyshev.theta n ≤ C0 * n + (2 * (Real.log n) ^ 2 + 30) := by
      have h1 := Chebyshev.theta_le_psi n
      have h2 := psi_30_upper (x := n) (by linarith)
      dsimp only [C0, A]
      linarith
    have hw_nonneg : 0 ≤ w n - w (n + 1) := by
      dsimp only [w]
      have hlogn_pos : 0 < Real.log n := by linarith
      have hle : (n : ℝ) * Real.log n ≤ ((n + 1 : ℕ) : ℝ) * Real.log (n + 1 : ℕ) := by
        apply mul_le_mul (by push_cast; linarith)
          (Real.log_le_log (by linarith) (by push_cast; linarith)) hlogn_pos.le (by positivity)
      linarith [one_div_le_one_div_of_le (by positivity) hle]
    have hw_le := inv_mul_log_diff_le (n := n) (by omega)
    have h1 : Chebyshev.theta n * (w n - w (n + 1)) ≤
        (C0 * n + (2 * (Real.log n) ^ 2 + 30)) *
          ((Real.log n + 1) / ((n : ℝ) ^ 2 * (Real.log n) ^ 2)) := by
      calc Chebyshev.theta n * (w n - w (n + 1))
          ≤ (C0 * n + (2 * (Real.log n) ^ 2 + 30)) * (w n - w (n + 1)) :=
            mul_le_mul_of_nonneg_right hth_le hw_nonneg
        _ ≤ (C0 * n + (2 * (Real.log n) ^ 2 + 30)) *
              ((Real.log n + 1) / ((n : ℝ) ^ 2 * (Real.log n) ^ 2)) := by
            have hC0_pos : 0 ≤ C0 := by
              have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
              have := Real.log_pos (by norm_num : (1 : ℝ) < 3)
              have := Real.log_pos (by norm_num : (1 : ℝ) < 5)
              dsimp only [C0, A]; positivity
            exact mul_le_mul_of_nonneg_left hw_le (by positivity)
    have hmain : (n : ℝ) * ((Real.log n + 1) / ((n : ℝ) ^ 2 * (Real.log n) ^ 2)) =
        (Real.log n + 1) / ((n : ℝ) * (Real.log n) ^ 2) := by
      have : (n : ℝ) ≠ 0 := by linarith
      field_simp
    have herr : (2 * (Real.log n) ^ 2 + 30) * ((Real.log n + 1) / ((n : ℝ) ^ 2 * (Real.log n) ^ 2)) ≤
        3 * (Real.log n / (n : ℝ) ^ 2) := by
      have hden : 0 < (n : ℝ) ^ 2 * (Real.log n) ^ 2 := by positivity
      have hrew : (2 * (Real.log n) ^ 2 + 30) * ((Real.log n + 1) / ((n : ℝ) ^ 2 * (Real.log n) ^ 2)) =
          ((2 * (Real.log n) ^ 2 + 30) * (Real.log n + 1)) / ((n : ℝ) ^ 2 * (Real.log n) ^ 2) := by ring
      have hrew2 : 3 * (Real.log n / (n : ℝ) ^ 2) =
          (3 * (Real.log n) ^ 3) / ((n : ℝ) ^ 2 * (Real.log n) ^ 2) := by field_simp
      rw [hrew, hrew2]
      refine div_le_div_of_nonneg_right ?_ hden.le
      nlinarith
    have hC0_pos : 0 ≤ C0 := by
      have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
      have := Real.log_pos (by norm_num : (1 : ℝ) < 3)
      have := Real.log_pos (by norm_num : (1 : ℝ) < 5)
      dsimp only [C0, A]; positivity
    have hg := log_log_sub_inv_log_step (n := n) (by omega)
    have hh := log_div_sq_step (n := n) (by omega)
    have hsplit_mul : (C0 * n + (2 * (Real.log n) ^ 2 + 30)) *
        ((Real.log n + 1) / ((n : ℝ) ^ 2 * (Real.log n) ^ 2)) =
        C0 * ((Real.log n + 1) / ((n : ℝ) * (Real.log n) ^ 2)) +
        (2 * (Real.log n) ^ 2 + 30) * ((Real.log n + 1) / ((n : ℝ) ^ 2 * (Real.log n) ^ 2)) := by
      rw [add_mul, mul_assoc, hmain]
    nlinarith
  have hsum_le := sum_le_sum hterm_le
  rw [sum_add_distrib, ← mul_sum, ← mul_sum] at hsum_le
  -- Telescope both sums on Icc (x0 + 1) (X - 1)
  have htele_gen : ∀ (f : ℕ → ℝ) (a b : ℕ), a ≤ b →
      ∑ n ∈ Icc (a + 1) b, (f n - f (n - 1)) = f b - f a := by
    intro f a b hab
    induction b with
    | zero =>
      have ha : a = 0 := by omega
      subst ha; simp
    | succ m ih =>
      rcases eq_or_lt_of_le hab with rfl | hlt
      · simp
      · rw [sum_Icc_succ_top (by omega : a + 1 ≤ m + 1), ih (by omega)]
        simp only [Nat.add_sub_cancel]
        ring
  have hteleG := htele_gen (fun n => Real.log (Real.log n) - 1 / Real.log n) x0 (X - 1) (by omega)
  have hteleH := htele_gen (fun n => -((Real.log n + 1) / (n : ℝ))) x0 (X - 1) (by omega)
  have hteleH' : ∑ n ∈ Icc (x0 + 1) (X - 1),
      ((Real.log ((n - 1 : ℕ) : ℝ) + 1) / ((n - 1 : ℕ) : ℝ) - (Real.log n + 1) / (n : ℝ)) =
      (Real.log x0 + 1) / (x0 : ℝ) - (Real.log ((X - 1 : ℕ) : ℝ) + 1) / ((X - 1 : ℕ) : ℝ) := by
    have h1 : ∀ n ∈ Icc (x0 + 1) (X - 1),
        (Real.log ((n - 1 : ℕ) : ℝ) + 1) / ((n - 1 : ℕ) : ℝ) - (Real.log n + 1) / (n : ℝ) =
        (-((Real.log n + 1) / (n : ℝ))) - (-((Real.log ((n - 1 : ℕ) : ℝ) + 1) / ((n - 1 : ℕ) : ℝ))) := by
      intro n _; ring
    rw [sum_congr rfl h1, hteleH]
    ring
  rw [hteleG, hteleH'] at hsum_le
  -- Combine with boundary term Chebyshev.theta X * w X
  have hthX : Chebyshev.theta X * w X ≤
      C0 / Real.log X + (2 * (Real.log X) ^ 2 + 30) / ((X : ℝ) * Real.log X) := by
    have h1 := Chebyshev.theta_le_psi X
    have h2 := psi_30_upper (x := X) (by exact_mod_cast (show 1 ≤ X by omega))
    have hXpos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
    have hlogX_pos : 0 < Real.log X := Real.log_pos (by exact_mod_cast (show 1 < X by omega))
    have hwpos : 0 ≤ w X := by dsimp only [w]; positivity
    have h3 : Chebyshev.theta X * w X ≤ (C0 * X + (2 * (Real.log X) ^ 2 + 30)) * w X :=
      mul_le_mul_of_nonneg_right (by dsimp only [C0, A]; linarith) hwpos
    have h4 : (C0 * X + (2 * (Real.log X) ^ 2 + 30)) * w X =
        C0 / Real.log X + (2 * (Real.log X) ^ 2 + 30) / ((X : ℝ) * Real.log X) := by
      dsimp only [w]
      field_simp
    linarith
  have hC0_pos : 0 ≤ C0 := by
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    have := Real.log_pos (by norm_num : (1 : ℝ) < 3)
    have := Real.log_pos (by norm_num : (1 : ℝ) < 5)
    dsimp only [C0, A]; positivity
  have hlogXm1_le : Real.log ((X - 1 : ℕ) : ℝ) ≤ Real.log X :=
    Real.log_le_log (by exact_mod_cast (show 0 < X - 1 by omega))
      (by exact_mod_cast (show X - 1 ≤ X by omega))
  have hlogXm1_pos : 0 < Real.log ((X - 1 : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X - 1 by omega))
  have hll_le : Real.log (Real.log ((X - 1 : ℕ) : ℝ)) ≤ Real.log (Real.log X) :=
    Real.log_le_log hlogXm1_pos hlogXm1_le
  have hinv_le : 1 / Real.log X ≤ 1 / Real.log ((X - 1 : ℕ) : ℝ) :=
    one_div_le_one_div_of_le hlogXm1_pos hlogXm1_le
  have hHtail_nonneg : 0 ≤ (Real.log ((X - 1 : ℕ) : ℝ) + 1) / ((X - 1 : ℕ) : ℝ) := by
    have : (0 : ℝ) < ((X - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < X - 1 by omega)
    positivity
  have hw_x0 : Chebyshev.theta x0 * w (x0 + 1) =
      Chebyshev.theta x0 / (((x0 + 1 : ℕ) : ℝ) * Real.log (x0 + 1 : ℕ)) := by
    simp [w, div_eq_mul_inv]
  rw [hw_x0]
  have hfinal_le : Chebyshev.theta X * w X +
      ∑ n ∈ Icc (x0 + 1) (X - 1), Chebyshev.theta n * (w n - w (n + 1)) ≤
      C0 * (Real.log (Real.log X) - Real.log (Real.log x0) + 1 / Real.log x0) +
      3 * ((Real.log x0 + 1) / (x0 : ℝ)) +
      (2 * (Real.log X) ^ 2 + 30) / ((X : ℝ) * Real.log X) := by
    have hC0_cancel : C0 / Real.log X +
        C0 * (Real.log (Real.log ((X - 1 : ℕ) : ℝ)) - 1 / Real.log ((X - 1 : ℕ) : ℝ) -
          (Real.log (Real.log x0) - 1 / Real.log x0)) ≤
        C0 * (Real.log (Real.log X) - Real.log (Real.log x0) + 1 / Real.log x0) := by
      have h1 : C0 / Real.log X = C0 * (1 / Real.log X) := by ring
      rw [h1]
      nlinarith
    linarith
  linarith

lemma sum_inv_primes_Icc_le_sieve (a b B D U : ℕ) (ha : 2 ≤ a) (hab : a ≤ b) (hD : 0 < D)
    (hcheck : (((List.range' a (b - a + 1)).filter (fun n =>
        (List.range' 2 B).all (fun d => decide (n ≤ d ∨ n % d ≠ 0)))).map
        (fun n => D / n + 1)).sum ≤ U) :
    ∑ p ∈ (Icc a b).filter Nat.Prime, (1 : ℝ) / p ≤ (U : ℝ) / D := by
  let L : List ℕ := (List.range' a (b - a + 1)).filter (fun n =>
      (List.range' 2 B).all (fun d => decide (n ≤ d ∨ n % d ≠ 0)))
  have hnodup : L.Nodup := List.Nodup.filter _ List.nodup_range'
  have hsub : (Icc a b).filter Nat.Prime ⊆ L.toFinset := by
    intro p hp
    rw [mem_filter, mem_Icc] at hp
    rcases hp with ⟨⟨hpa, hpb⟩, hp_prime⟩
    rw [List.mem_toFinset]
    refine List.mem_filter.mpr ⟨List.mem_range'.mpr ⟨p - a, by omega, by omega⟩, ?_⟩
    rw [List.all_eq_true]
    intro d hd
    rw [decide_eq_true_eq]
    rcases le_or_gt p d with hle | hlt
    · exact Or.inl hle
    · right
      intro hmod0
      have hd_ge : 2 ≤ d := by
        rw [List.mem_range'] at hd
        obtain ⟨j, _, rfl⟩ := hd; omega
      have hdvd : d ∣ p := Nat.dvd_of_mod_eq_zero hmod0
      rcases hp_prime.eq_one_or_self_of_dvd d hdvd with h1 | hself <;> omega
  have hterm : ∀ n ∈ L.toFinset, (1 : ℝ) / n ≤ ((D / n + 1 : ℕ) : ℝ) / D := by
    intro n hn
    rw [List.mem_toFinset] at hn
    have hn_pos : 0 < n := by
      have hmem := (List.mem_filter.mp hn).1
      rw [List.mem_range'] at hmem
      obtain ⟨j, _, rfl⟩ := hmem
      omega
    have hD_pos : (0 : ℝ) < D := by exact_mod_cast hD
    have hn_posR : (0 : ℝ) < n := by exact_mod_cast hn_pos
    rw [div_le_div_iff₀ hn_posR hD_pos, one_mul]
    have hnat : D < n * (D / n + 1) := Nat.lt_mul_div_succ D hn_pos
    have hnat' : D ≤ (D / n + 1) * n := by nlinarith
    exact_mod_cast hnat'
  have hsum_eq : ∑ n ∈ L.toFinset, (D / n + 1) = (L.map (fun n => D / n + 1)).sum := by
    rw [List.sum_toFinset _ hnodup]
  calc ∑ p ∈ (Icc a b).filter Nat.Prime, (1 : ℝ) / p
      ≤ ∑ n ∈ L.toFinset, (1 : ℝ) / n :=
        sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
    _ ≤ ∑ n ∈ L.toFinset, ((D / n + 1 : ℕ) : ℝ) / D := sum_le_sum hterm
    _ = ((∑ n ∈ L.toFinset, (D / n + 1) : ℕ) : ℝ) / D := by rw [← sum_div, Nat.cast_sum]
    _ = (((L.map (fun n => D / n + 1)).sum : ℕ) : ℝ) / D := by rw [hsum_eq]
    _ ≤ (U : ℝ) / D := by gcongr

lemma sum_inv_primes_5000_le :
    ∑ p ∈ Nat.primesLE 5000, (1 : ℝ) / p ≤ (2405530 : ℝ) / 1000000 := by
  have hpart : ∀ (a b c : ℕ), a ≤ b → b < c →
      ∑ p ∈ (Icc a c).filter Nat.Prime, (1 : ℝ) / p =
      (∑ p ∈ (Icc a b).filter Nat.Prime, (1 : ℝ) / p) +
      (∑ p ∈ (Icc (b + 1) c).filter Nat.Prime, (1 : ℝ) / p) := by
    intro a b c hab hbc
    have hunion : (Icc a c).filter Nat.Prime =
        ((Icc a b).filter Nat.Prime) ∪ ((Icc (b + 1) c).filter Nat.Prime) := by
      rw [← filter_union]
      congr 1
      ext p; simp only [mem_Icc, mem_union]; omega
    have hdisj : Disjoint ((Icc a b).filter Nat.Prime) ((Icc (b + 1) c).filter Nat.Prime) := by
      rw [disjoint_left]; intro p h1 h2; simp only [mem_filter, mem_Icc] at h1 h2; omega
    rw [hunion, sum_union hdisj]
  have h5000 : Nat.primesLE 5000 = (Icc 2 5000).filter Nat.Prime := by
    ext p; simp only [Nat.mem_primesLE, mem_filter, mem_Icc]
    exact ⟨fun ⟨h1, h2⟩ => ⟨⟨h2.two_le, h1⟩, h2⟩, fun ⟨⟨_, h1⟩, h2⟩ => ⟨h1, h2⟩⟩
  rw [h5000]
  have c1 := sum_inv_primes_Icc_le_sieve 2 500 22 1000000 2096761 (by norm_num) (by norm_num) (by norm_num) (by decide)
  have c2 := sum_inv_primes_Icc_le_sieve 501 1000 31 1000000 101414 (by norm_num) (by norm_num) (by norm_num) (by decide)
  have c3 := sum_inv_primes_Icc_le_sieve 1001 1500 38 1000000 57583 (by norm_num) (by norm_num) (by norm_num) (by decide)
  have c4 := sum_inv_primes_Icc_le_sieve 1501 2000 44 1000000 36853 (by norm_num) (by norm_num) (by norm_num) (by decide)
  have c5 := sum_inv_primes_Icc_le_sieve 2001 2500 50 1000000 28636 (by norm_num) (by norm_num) (by norm_num) (by decide)
  have c6 := sum_inv_primes_Icc_le_sieve 2501 3000 54 1000000 23028 (by norm_num) (by norm_num) (by norm_num) (by decide)
  have c7 := sum_inv_primes_Icc_le_sieve 3001 3500 59 1000000 18199 (by norm_num) (by norm_num) (by norm_num) (by decide)
  have c8 := sum_inv_primes_Icc_le_sieve 3501 4000 63 1000000 16390 (by norm_num) (by norm_num) (by norm_num) (by decide)
  have c9 := sum_inv_primes_Icc_le_sieve 4001 4500 67 1000000 14214 (by norm_num) (by norm_num) (by norm_num) (by decide)
  have c10 := sum_inv_primes_Icc_le_sieve 4501 5000 70 1000000 12452 (by norm_num) (by norm_num) (by norm_num) (by decide)
  rw [hpart 2 4500 5000 (by norm_num) (by norm_num),
      hpart 2 4000 4500 (by norm_num) (by norm_num),
      hpart 2 3500 4000 (by norm_num) (by norm_num),
      hpart 2 3000 3500 (by norm_num) (by norm_num),
      hpart 2 2500 3000 (by norm_num) (by norm_num),
      hpart 2 2000 2500 (by norm_num) (by norm_num),
      hpart 2 1500 2000 (by norm_num) (by norm_num),
      hpart 2 1000 1500 (by norm_num) (by norm_num),
      hpart 2 500 1000 (by norm_num) (by norm_num)]
  linarith

lemma theta_5000_ge : (4300 : ℝ) ≤ Chebyshev.theta (5000 : ℕ) := by
  have hl2_lo : (0.69314718 : ℝ) < Real.log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
  have hl2_hi : Real.log 2 < (0.69314719 : ℝ) := lt_trans Real.log_two_lt_d9 (by norm_num)
  have ⟨hl3_lo, hl3_hi, hl5_lo, hl5_hi, _, _⟩ := log_small_constants
  have hlog5000_eq : Real.log (5000 : ℝ) = 3 * Real.log 2 + 4 * Real.log 5 := by
    rw [show (5000 : ℝ) = 2 ^ 3 * 5 ^ 4 by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]
    push_cast; ring
  have hl5000_hi : Real.log (5000 : ℝ) < (8.518 : ℝ) := by rw [hlog5000_eq]; linarith
  have hpsi_lo := psi_30_lower (x := 5000) (by norm_num)
  have hcp := Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi (5000 : ℝ)
  have h5000_2 : (5000 : ℝ) ^ (2 : ℝ)⁻¹ ≤ 71 := by
    rw [← one_div, ← Real.sqrt_eq_rpow]
    exact Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have h5000_3 : (5000 : ℝ) ^ (3 : ℝ)⁻¹ ≤ 18 := by
    have h1 : ((5000 : ℝ) ^ (3 : ℝ)⁻¹) ^ (3 : ℕ) ≤ 18 ^ (3 : ℕ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      norm_num
    exact le_of_pow_le_pow_left₀ (by norm_num : 3 ≠ 0) (by norm_num) h1
  have h5000_5 : (5000 : ℝ) ^ (5 : ℝ)⁻¹ ≤ 6 := by
    have h1 : ((5000 : ℝ) ^ (5 : ℝ)⁻¹) ^ (5 : ℕ) ≤ 6 ^ (5 : ℕ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      norm_num
    exact le_of_pow_le_pow_left₀ (by norm_num : 5 ≠ 0) (by norm_num) h1
  have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  have hp71 : Chebyshev.psi 71 ≤ 180 := by
    have h := Chebyshev.psi_le (x := 71) (by norm_num)
    have hsq71 : Real.sqrt 71 ≤ 8.5 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
    have hlog71 : Real.log (71 : ℝ) ≤ 4.5 := by
      have hlt : (71 : ℝ) ≤ 2 ^ 6 * (1 + 1 / 8) := by norm_num
      have hl := Real.log_le_log (by norm_num) hlt
      rw [Real.log_mul (by norm_num) (by norm_num), Real.log_pow] at hl
      have h98 := log_one_add_le_add_cube (by norm_num : (0 : ℝ) ≤ 1 / 8)
      push_cast at hl; linarith
    rw [hlog4] at h
    nlinarith [Real.sqrt_nonneg 71]
  have hp18 : Chebyshev.psi 18 ≤ 55 := by
    have h := Chebyshev.psi_le (x := 18) (by norm_num)
    have hsq18 : Real.sqrt 18 ≤ 4.3 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
    have hlog18 : Real.log (18 : ℝ) ≤ 3.0 := by
      have hlt : (18 : ℝ) ≤ 2 * 3 ^ 2 := by norm_num
      have hl := Real.log_le_log (by norm_num) hlt
      rw [Real.log_mul (by norm_num) (by norm_num), Real.log_pow] at hl
      push_cast at hl; linarith
    rw [hlog4] at h
    nlinarith [Real.sqrt_nonneg 18]
  have hp6 : Chebyshev.psi 6 ≤ 20 := by
    have h := Chebyshev.psi_le (x := 6) (by norm_num)
    have hsq6 : Real.sqrt 6 ≤ 2.5 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
    have hlog6 : Real.log (6 : ℝ) ≤ 2.0 := by
      rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
      linarith
    rw [hlog4] at h
    nlinarith [Real.sqrt_nonneg 6]
  have h2' := le_trans (Chebyshev.psi_mono h5000_2) hp71
  have h3' := le_trans (Chebyshev.psi_mono h5000_3) hp18
  have h5' := le_trans (Chebyshev.psi_mono h5000_5) hp6
  have h5000_cast : ((5000 : ℕ) : ℝ) = (5000 : ℝ) := by norm_num
  rw [h5000_cast]
  linarith

lemma sum_inv_primes_10300000_lt :
    ∑ p ∈ Nat.primesLE 10300000, (1 : ℝ) / p < (3.16 : ℝ) := by
  have hl2_lo : (0.69314718 : ℝ) < Real.log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
  have hl2_hi : Real.log 2 < (0.69314719 : ℝ) := lt_trans Real.log_two_lt_d9 (by norm_num)
  have ⟨hl3_lo, hl3_hi, hl5_lo, hl5_hi, hl10_lo, hl10_hi⟩ := log_small_constants
  set A : ℝ := (7 / 15 : ℝ) * Real.log 2 + (3 / 10 : ℝ) * Real.log 3 + (1 / 6 : ℝ) * Real.log 5
  have hA_lo : (0.92128 : ℝ) < A := by dsimp only [A]; linarith
  have hA_hi : A < (0.92135 : ℝ) := by dsimp only [A]; linarith
  have hlog5000_eq : Real.log (5000 : ℝ) = 3 * Real.log 2 + 4 * Real.log 5 := by
    rw [show (5000 : ℝ) = 2 ^ 3 * 5 ^ 4 by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]
    push_cast; ring
  have hl5000_lo : (8.517 : ℝ) < Real.log (5000 : ℝ) := by rw [hlog5000_eq]; linarith
  have hl5000_hi : Real.log (5000 : ℝ) < (8.518 : ℝ) := by rw [hlog5000_eq]; linarith
  have hlogX_eq : Real.log (10300000 : ℝ) = 7 * Real.log 10 + Real.log (1 + (3 / 100 : ℝ)) := by
    rw [show (10300000 : ℝ) = (10 : ℝ) ^ 7 * (1 + 3 / 100) by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    push_cast; ring
  have hl103_lo := log_one_add_ge_sub_sq (by norm_num : (0 : ℝ) ≤ 3 / 100)
  have hl103_hi := log_one_add_le_add_cube (by norm_num : (0 : ℝ) ≤ 3 / 100)
  have hlX_lo : (16.147 : ℝ) < Real.log (10300000 : ℝ) := by rw [hlogX_eq]; linarith
  have hlX_hi : Real.log (10300000 : ℝ) < (16.148 : ℝ) := by rw [hlogX_eq]; linarith
  have hll_diff : Real.log (Real.log (10300000 : ℝ)) - Real.log (Real.log (5000 : ℝ)) < (0.642 : ℝ) := by
    rw [← Real.log_div (by linarith) (by linarith)]
    have hratio : Real.log (10300000 : ℝ) / Real.log (5000 : ℝ) < (19 / 10 : ℝ) := by
      rw [div_lt_iff₀ (by linarith)]; linarith
    have h1 : Real.log (Real.log (10300000 : ℝ) / Real.log (5000 : ℝ)) < Real.log (19 / 10 : ℝ) :=
      Real.log_lt_log (by positivity) hratio
    have h19 : Real.log (19 / 10 : ℝ) = Real.log 2 - Real.log (1 + (1 / 19 : ℝ)) := by
      have h2 : (19 / 10 : ℝ) = 2 / (1 + 1 / 19) := by norm_num
      rw [h2, Real.log_div (by norm_num) (by norm_num)]
    have h19_lo := log_one_add_ge_sub_sq (by norm_num : (0 : ℝ) ≤ 1 / 19)
    linarith
  have hth5000 : (4300 : ℝ) ≤ Chebyshev.theta (5000 : ℕ) := theta_5000_ge
  have hl5001_hi : Real.log ((5000 + 1 : ℕ) : ℝ) < (8.519 : ℝ) := by
    have h1 : ((5000 + 1 : ℕ) : ℝ) = 5000 * (1 + 1 / 5000) := by norm_num
    rw [h1, Real.log_mul (by norm_num) (by norm_num)]
    have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1 + 1 / 5000)
    linarith only [hl5000_hi, h2]
  have hterm_th : (4300 : ℝ) / (5001 * 8.519) ≤
      Chebyshev.theta (5000 : ℕ) / (((5000 + 1 : ℕ) : ℝ) * Real.log (5000 + 1 : ℕ)) := by
    have hden_pos : 0 < ((5000 + 1 : ℕ) : ℝ) * Real.log (5000 + 1 : ℕ) := by
      have h1 : (1 : ℝ) < ((5000 + 1 : ℕ) : ℝ) := by norm_num
      have h2 := Real.log_pos h1
      positivity
    have hden_le : ((5000 + 1 : ℕ) : ℝ) * Real.log (5000 + 1 : ℕ) ≤ 5001 * 8.519 := by
      have h5001 : ((5000 + 1 : ℕ) : ℝ) = 5001 := by norm_num
      rw [h5001] at hl5001_hi ⊢
      linarith only [hl5001_hi]
    exact div_le_div₀ (Chebyshev.theta_nonneg _) hth5000 hden_pos hden_le
  have hinv5000 : 1 / Real.log (5000 : ℝ) ≤ 1 / 8.517 :=
    one_div_le_one_div_of_le (by norm_num) hl5000_lo.le
  have herr_bnd : (2 * (Real.log (10300000 : ℝ)) ^ 2 + 30) /
      ((10300000 : ℝ) * Real.log (10300000 : ℝ)) ≤ (0.001 : ℝ) := by
    have hden : 0 < (10300000 : ℝ) * Real.log (10300000 : ℝ) := by
      have : 0 < Real.log (10300000 : ℝ) := by linarith only [hlX_lo]
      positivity
    rw [div_le_iff₀ hden]
    have hsq : (Real.log (10300000 : ℝ)) ^ 2 ≤ 16.148 ^ 2 := by
      nlinarith only [hlX_lo, hlX_hi]
    linarith only [hsq, hlX_lo]
  have hC0_le : (6 / 5 : ℝ) * A ≤ 1.1057 := by linarith only [hA_hi]
  have hterm_main : (6 / 5 : ℝ) * A *
      (Real.log (Real.log (10300000 : ℝ)) - Real.log (Real.log (5000 : ℝ)) +
        1 / Real.log (5000 : ℝ)) ≤ 1.1057 * (0.642 + 1 / 8.517) := by
    have hbr_nonneg : 0 ≤ Real.log (Real.log (10300000 : ℝ)) -
        Real.log (Real.log (5000 : ℝ)) + 1 / Real.log (5000 : ℝ) := by
      have h1 : Real.log (5000 : ℝ) ≤ Real.log (10300000 : ℝ) :=
        Real.log_le_log (by norm_num) (by norm_num)
      have h2 := Real.log_le_log (by linarith only [hl5000_lo]) h1
      have hpos : 0 < 1 / Real.log (5000 : ℝ) := by
        have : 0 < Real.log (5000 : ℝ) := by linarith only [hl5000_lo]
        positivity
      linarith only [h2, hpos]
    exact mul_le_mul hC0_le (by linarith only [hll_diff, hinv5000]) hbr_nonneg (by norm_num)
  have hsub : Nat.primesLE 5000 ⊆ Nat.primesLE 10300000 := Nat.primesLE_mono (by norm_num)
  have hsplit : ∑ p ∈ Nat.primesLE 10300000, (1 : ℝ) / p =
      (∑ p ∈ Nat.primesLE 5000, (1 : ℝ) / p) +
      (∑ p ∈ Nat.primesLE 10300000 \ Nat.primesLE 5000, (1 : ℝ) / p) := by
    rw [add_comm, sum_sdiff hsub]
  rw [hsplit]
  have hpart1 := sum_inv_primes_5000_le
  have hpart2 := sum_inv_primes_Ioc_le (x0 := 5000) (X := 10300000) (by norm_num) (by norm_num)
  have h5000_c : ((5000 : ℕ) : ℝ) = (5000 : ℝ) := by norm_num
  have hX_c : ((10300000 : ℕ) : ℝ) = (10300000 : ℝ) := by norm_num
  rw [h5000_c, hX_c] at hpart2
  dsimp only [A] at hterm_main
  linarith only [hpart1, hpart2, hterm_main, hterm_th, hl5000_hi, herr_bnd]

lemma theta_10300000_gt :
    4 * (1000000 : ℝ) * Real.log 10 < Chebyshev.theta (10300000 : ℝ) := by
  have hl2_lo : (0.69314718 : ℝ) < Real.log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
  have ⟨hl3_lo, _, hl5_lo, _, _, hl10_hi⟩ := log_small_constants
  have hlogX_eq : Real.log (10300000 : ℝ) = 7 * Real.log 10 + Real.log (1 + (3 / 100 : ℝ)) := by
    rw [show (10300000 : ℝ) = (10 : ℝ) ^ 7 * (1 + 3 / 100) by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    push_cast; ring
  have hl103_hi := log_one_add_le_add_cube (by norm_num : (0 : ℝ) ≤ 3 / 100)
  have hlX_hi : Real.log (10300000 : ℝ) < (16.148 : ℝ) := by rw [hlogX_eq]; linarith
  have hpsi_lo := psi_30_lower (x := 10300000) (by norm_num)
  have hdiff := Chebyshev.psi_sub_theta_le (x := 10300000) (by norm_num)
  have hsqX : Real.sqrt 10300000 ≤ 3210 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have hsq_nn : 0 ≤ Real.sqrt 10300000 := Real.sqrt_nonneg 10300000
  nlinarith only [hpsi_lo, hdiff, hsqX, hsq_nn, hl2_lo, hl3_lo, hl5_lo, hlX_hi, hl10_hi]

lemma ten_pow_lt_of_log_lt {m N : ℕ} (hm : 0 < m)
    (h : (N : ℝ) * Real.log 10 < Real.log (m : ℝ)) :
    10 ^ N < m := by
  have hlog : Real.log ((10 ^ N : ℕ) : ℝ) < Real.log (m : ℝ) := by
    rw [Nat.cast_pow, Real.log_pow]
    simpa using h
  have hm_real : ((10 ^ N : ℕ) : ℝ) < (m : ℝ) := by
    by_contra hle
    push Not at hle
    exact not_le_of_gt hlog (Real.log_le_log (Nat.cast_pos.mpr hm) hle)
  exact Nat.cast_lt.mp hm_real

lemma moser_1953_bound {k m : ℕ} (hk : 0 < k) (hm : 0 < m) (heven : Even k)
    (heq : ErdosMoser.powerSum k m = m ^ k) : 10 ^ 1000000 < m := by
  have hm8 : 10 ^ 8 < m := m_gt_ten_pow_eight hk hm heven heq
  obtain ⟨_, hsqM1, _, hineq⟩ := moser_M1_structure hk hm heven heq
  set M1 := (m ^ 2 - 1) * (4 * m ^ 2 - 1) / 12
  have hM1_pos : 0 < M1 := by
    dsimp only [M1]
    have hm2 : 100 ≤ m ^ 2 := by nlinarith
    have h1 : 12 ≤ (m ^ 2 - 1) * (4 * m ^ 2 - 1) := by
      have ha : 12 ≤ m ^ 2 - 1 := by omega
      have hb : 1 ≤ 4 * m ^ 2 - 1 := by omega
      nlinarith
    exact Nat.div_pos h1 (by norm_num)
  have hsum_X : ∑ p ∈ Nat.primesLE 10300000, (1 : ℝ) / p < (3.16 : ℝ) :=
    sum_inv_primes_10300000_lt
  have hineqR : (19 / 6 : ℝ) ≤
      (∑ p ∈ M1.primeFactors, (1 : ℝ) / p) +
        1 / (m - 1 : ℝ) + 2 / (m + 1 : ℝ) + 2 / (2 * m - 1 : ℝ) + 4 / (2 * m + 1 : ℝ) := by
    have hcast := Rat.cast_le (K := ℝ).mpr hineq
    push_cast at hcast
    exact hcast
  have hmR : (10 ^ 8 : ℝ) < m := by exact_mod_cast hm8
  have herrM : 1 / (m - 1 : ℝ) + 2 / (m + 1 : ℝ) + 2 / (2 * m - 1 : ℝ) + 4 / (2 * m + 1 : ℝ) <
      (1 : ℝ) / 1000 := by
    have h1 : 1 / (m - 1 : ℝ) < 1 / 10000 := one_div_lt_one_div_of_lt (by norm_num) (by linarith only [hmR])
    have h2 : 2 / (m + 1 : ℝ) < 2 / 10000 := by rw [div_lt_div_iff₀ (by linarith only [hmR]) (by norm_num)]; linarith only [hmR]
    have h3 : 2 / (2 * m - 1 : ℝ) < 2 / 10000 := by rw [div_lt_div_iff₀ (by linarith only [hmR]) (by norm_num)]; linarith only [hmR]
    have h4 : 4 / (2 * m + 1 : ℝ) < 4 / 10000 := by rw [div_lt_div_iff₀ (by linarith only [hmR]) (by norm_num)]; linarith only [hmR]
    linarith only [h1, h2, h3, h4]
  have hsum_lt : ∑ p ∈ Nat.primesLE 10300000, (1 : ℝ) / p <
      ∑ p ∈ M1.primeFactors, (1 : ℝ) / p := by linarith only [hsum_X, hineqR, herrM]
  have hprim_lt : primorial 10300000 < M1 :=
    primorial_lt_of_sum_inv_lt hM1_pos (by norm_num) hsqM1 hsum_lt
  have hM1_lt : M1 < m ^ 4 := by
    dsimp only [M1]
    have h1 : (m ^ 2 - 1) * (4 * m ^ 2 - 1) < 12 * m ^ 4 := by
      have hmul : (m ^ 2 - 1) * (4 * m ^ 2 - 1) ≤ m ^ 2 * (4 * m ^ 2) :=
        Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _)
      have h4eq : m ^ 2 * (4 * m ^ 2) = 4 * m ^ 4 := by ring
      have hpos4 : 0 < m ^ 4 := by positivity
      omega
    exact Nat.div_lt_of_lt_mul h1
  have hlog_lt : Chebyshev.theta (10300000 : ℝ) < 4 * Real.log (m : ℝ) := by
    rw [Chebyshev.theta_eq_log_primorial]
    have hfl : ⌊(10300000 : ℝ)⌋₊ = 10300000 := Nat.floor_natCast 10300000
    rw [hfl]
    have hlt1 : Real.log (primorial 10300000 : ℝ) < Real.log ((m : ℝ) ^ 4) :=
      Real.log_lt_log (by exact_mod_cast primorial_pos 10300000)
        (by exact_mod_cast lt_trans hprim_lt hM1_lt)
    rw [Real.log_pow] at hlt1
    push_cast at hlt1
    exact hlt1
  have hthX_gt : 4 * (1000000 : ℝ) * Real.log 10 < Chebyshev.theta (10300000 : ℝ) :=
    theta_10300000_gt
  refine ten_pow_lt_of_log_lt hm (N := 1000000) ?_
  have h1M : ((1000000 : ℕ) : ℝ) = (1000000 : ℝ) := by norm_num
  rw [h1M]
  linarith only [hthX_gt, hlog_lt]

lemma three_adic_m_mod_one {k m : ℕ} (hk : 0 < k) (hm : 0 < m) (heven : Even k)
    (heq : ErdosMoser.powerSum k m = m ^ k) (hm3 : m % 3 = 1) :
    3 ^ (padicValNat 3 k + 2) ∣ 2 * m - 5 := by
  have hm_ge : 8 < m := by
    have := krzysztofek_lower hk hm heven heq
    have := k_ge_six hk hm heven heq
    omega
  have hcong := unified_prime_pow_congr hk hm heven heq Nat.prime_three (by norm_num)
    (even_iff_two_dvd.mp heven)
  rw [hm3] at hcong
  have hrew : (3 - 1) * m + 1 = (2 * m - 5) + 2 * 3 := by omega
  rw [hrew] at hcong
  have h0 : 2 * m - 5 ≡ 0 [MOD 3 ^ (padicValNat 3 k + 2)] :=
    Nat.ModEq.add_right_cancel' (2 * 3) (by simpa using hcong)
  exact Nat.modEq_zero_iff_dvd.mp h0

lemma three_adic_m_mod_two {k m : ℕ} (hk : 0 < k) (hm : 0 < m) (heven : Even k)
    (heq : ErdosMoser.powerSum k m = m ^ k) (hm3 : m % 3 = 2) :
    3 ^ (padicValNat 3 k + 2) ∣ m - 2 := by
  have hm_ge : 8 < m := by
    have := krzysztofek_lower hk hm heven heq
    have := k_ge_six hk hm heven heq
    omega
  have hcong := unified_prime_pow_congr hk hm heven heq Nat.prime_three (by norm_num)
    (even_iff_two_dvd.mp heven)
  rw [hm3] at hcong
  have hrew : (3 - 1) * m + 2 = 2 * (m - 2) + 2 * 3 := by omega
  rw [hrew] at hcong
  have h0 : 2 * (m - 2) ≡ 0 [MOD 3 ^ (padicValNat 3 k + 2)] :=
    Nat.ModEq.add_right_cancel' (2 * 3) (by simpa using hcong)
  have hdvd : 3 ^ (padicValNat 3 k + 2) ∣ 2 * (m - 2) := Nat.modEq_zero_iff_dvd.mp h0
  have hcop : Nat.Coprime (3 ^ (padicValNat 3 k + 2)) 2 :=
    Nat.Coprime.pow_left _ (by decide)
  exact hcop.dvd_of_dvd_mul_left hdvd

/- ### Section 7: Voronoi (1889) / Kellner (2011) Bernoulli numerator divisibility (m ∣ |N_k|) -/

lemma padicValNat_add_one_le_sub_two {p d : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hd : 2 ≤ d) :
    padicValNat p (d + 1) ≤ d - 2 := by
  have : Fact p.Prime := ⟨hp⟩
  set t := padicValNat p (d + 1)
  rcases Nat.eq_zero_or_pos t with ht0 | htpos
  · omega
  · have hpow : p ^ t ≤ d + 1 := Nat.le_of_dvd (Nat.succ_pos d) pow_padicValNat_dvd
    have h5t : ∀ n : ℕ, 1 ≤ n → n + 3 ≤ 5 ^ n := by
      intro n hn
      induction n with
      | zero => omega
      | succ n ih =>
        rcases Nat.eq_zero_or_pos n with rfl | hn'
        · norm_num
        · have ih' := ih hn'
          have : 1 ≤ 5 ^ n := Nat.one_le_pow n 5 (by norm_num)
          rw [pow_succ]
          omega
    have h5t' : t + 3 ≤ 5 ^ t := h5t t htpos
    have hpt : 5 ^ t ≤ p ^ t := Nat.pow_le_pow_left hp5 t
    omega

lemma padicValuation_p_mul_bernoulli_even_le_one {p s : ℕ} [Fact p.Prime] :
    Rat.padicValuation p ((p : ℚ) * bernoulli (2 * s)) ≤ 1 := by
  have hp : p.Prime := Fact.out
  obtain ⟨Z, hZ⟩ := Bernoulli.vonStaudt_clausen s
  set S := (range (2 * s + 2)).filter fun q => q.Prime ∧ (q - 1) ∣ 2 * s
  have heq : (p : ℚ) * bernoulli (2 * s) =
      (p : ℚ) * (Z : ℚ) - ∑ q ∈ S, (p : ℚ) / (q : ℚ) := by
    have h1 : bernoulli (2 * s) = (Z : ℚ) - ∑ q ∈ S, (1 : ℚ) / q := by linarith
    rw [h1, mul_sub, mul_sum]
    congr 1
    refine sum_congr rfl fun q _ => by ring
  rw [heq]
  refine (Rat.padicValuation p).map_sub_le ?_ ?_
  · have hZ_eq : (p : ℚ) * (Z : ℚ) = ((p * Z : ℤ) : ℚ) := by push_cast; rfl
    rw [hZ_eq]
    exact Int.padicValuation_le_one p (p * Z)
  · refine (Rat.padicValuation p).map_sum_le fun q hq => ?_
    have hq_prime : q.Prime := (mem_filter.mp hq).2.1
    rcases eq_or_ne p q with rfl | hne
    · rw [div_self (by exact_mod_cast hp.ne_zero)]
      exact (Rat.padicValuation p).map_one.le
    · rw [Rat.padicValuation_le_one_iff]
      have hdiv : ((p : ℚ) / (q : ℚ)) = Rat.divInt (p : ℤ) (q : ℤ) := by
        rw [Rat.divInt_eq_div]; rfl
      have hdvd : ((p : ℚ) / (q : ℚ)).den ∣ q := by
        rw [hdiv]
        exact Int.ofNat_dvd.mp (Rat.den_dvd (p : ℤ) (q : ℤ))
      intro hpdvd
      have hpq : p ∣ q := dvd_trans hpdvd hdvd
      have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq_prime).mpr hne
      exact hp.not_dvd_one (hcop.gcd_eq_one ▸ Nat.dvd_gcd (dvd_refl p) hpq)

lemma padicValuation_nat_div_le_one {p a b : ℕ} [Fact p.Prime] (hb : b ≠ 0)
    (hv : padicValNat p b ≤ padicValNat p a) :
    Rat.padicValuation p ((a : ℚ) / (b : ℚ)) ≤ 1 := by
  have hp : p.Prime := Fact.out
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  · set vb := padicValNat p b
    have hbdvd : p ^ vb ∣ b := pow_padicValNat_dvd
    have hadvd : p ^ vb ∣ a := (padicValNat_dvd_iff_le ha).mpr hv
    obtain ⟨a', ha'⟩ := hadvd
    obtain ⟨b', hb'⟩ := hbdvd
    have hpb' : ¬ p ∣ b' := by
      intro hd
      obtain ⟨r, rfl⟩ := hd
      have hd' : p ^ (vb + 1) ∣ b := ⟨r, by rw [hb', pow_succ]; ring⟩
      exact pow_succ_padicValNat_not_dvd hb hd'
    have hpow_ne : ((p ^ vb : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (pow_pos hp.pos vb).ne'
    have hrew : (a : ℚ) / (b : ℚ) = (a' : ℚ) / (b' : ℚ) := by
      rw [ha', hb', Nat.cast_mul, Nat.cast_mul, mul_div_mul_left _ _ hpow_ne]
    rw [hrew, Rat.padicValuation_le_one_iff]
    have hdiv : ((a' : ℚ) / (b' : ℚ)) = Rat.divInt (a' : ℤ) (b' : ℤ) := by
      rw [Rat.divInt_eq_div]; rfl
    have hdvd : ((a' : ℚ) / (b' : ℚ)).den ∣ b' := by
      rw [hdiv]
      exact Int.ofNat_dvd.mp (Rat.den_dvd (a' : ℤ) (b' : ℤ))
    exact fun hpdvd => hpb' (dvd_trans hpdvd hdvd)

lemma voronoi_m_dvd_bernoulli_num {k m : ℕ} (hk : 0 < k) (hm : 0 < m) (heven : Even k)
    (heq : ErdosMoser.powerSum k m = m ^ k) :
    m ∣ (bernoulli k).num.natAbs := by
  have hk6 : 6 ≤ k := k_ge_six hk hm heven heq
  have hodd : Odd m := odd_m hk hm heven heq
  have h3nm : ¬ 3 ∣ m := three_not_dvd_m hk hm heven heq
  -- Express bernoulli k via Faulhaber's formula sum_range_pow
  have hfaul : (m : ℚ) ^ k =
      (∑ i ∈ range k, bernoulli i * ((k + 1).choose i : ℚ) * (m : ℚ) ^ (k + 1 - i) / (k + 1 : ℚ)) +
      (m : ℚ) * bernoulli k := by
    have hsumQ : (∑ i ∈ range m, (i : ℚ) ^ k) = (m : ℚ) ^ k := by
      have hnat := powerSum_eq_range (k := k) (m := m) hk
      rw [hnat] at heq
      have hcast : ((∑ i ∈ range m, i ^ k : ℕ) : ℚ) = ((m ^ k : ℕ) : ℚ) := by exact_mod_cast heq
      push_cast at hcast
      exact hcast
    rw [← hsumQ, sum_range_pow, sum_range_succ, Nat.choose_succ_self_right,
      show k + 1 - k = 1 by omega, pow_one]
    have hk1 : (k : ℚ) + 1 ≠ 0 := by positivity
    push_cast
    congr 1
    field_simp
  have hBk : bernoulli k =
      (m : ℚ) ^ (k - 1) -
      ∑ i ∈ range k, bernoulli i * ((k + 1).choose i : ℚ) * (m : ℚ) ^ (k - i) / (k + 1 : ℚ) := by
    have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
    have h1 : (m : ℚ) * bernoulli k =
        (m : ℚ) ^ k - ∑ i ∈ range k, bernoulli i * ((k + 1).choose i : ℚ) * (m : ℚ) ^ (k + 1 - i) / (k + 1 : ℚ) := by
      linarith
    have h2 : bernoulli k = ((m : ℚ) ^ k -
        ∑ i ∈ range k, bernoulli i * ((k + 1).choose i : ℚ) * (m : ℚ) ^ (k + 1 - i) / (k + 1 : ℚ)) / (m : ℚ) := by
      rw [← h1, mul_div_cancel_left₀ _ hmQ]
    rw [h2, sub_div, sum_div]
    congr 1
    · conv_lhs => rw [show k = (k - 1) + 1 by omega]
      rw [pow_succ, mul_div_cancel_right₀ _ hmQ]
    · refine sum_congr rfl fun i hi => ?_
      have hik : i < k := mem_range.mp hi
      rw [show k + 1 - i = (k - i) + 1 by omega, pow_succ]
      field_simp
  -- Show p ^ (padicValNat p m) ∣ (bernoulli k).num.natAbs for every prime p ∣ m
  have hprime_pow : ∀ p ∈ m.primeFactors, p ^ (padicValNat p m) ∣ (bernoulli k).num.natAbs := by
    intro p hpM
    have hp : p.Prime := Nat.prime_of_mem_primeFactors hpM
    have hpm : p ∣ m := Nat.dvd_of_mem_primeFactors hpM
    have : Fact p.Prime := ⟨hp⟩
    have hp5 : 5 ≤ p := by
      have hp2 : p ≠ 2 := by intro h; subst h; obtain ⟨r, rfl⟩ := hodd; omega
      have hp3 : p ≠ 3 := by intro h; subst h; exact h3nm hpm
      have := hp.two_le
      by_contra hlt; push Not at hlt
      have : p = 4 := by omega
      subst this; exact absurd hp (by decide)
    set e := padicValNat p m
    have he_pos : 1 ≤ e := one_le_padicValNat_of_dvd hm.ne' hpm
    have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hpeQ : (p : ℚ) ^ e ≠ 0 := pow_ne_zero e hpQ
    have hval_le : Rat.padicValuation p (bernoulli k / (p : ℚ) ^ e) ≤ 1 := by
      rw [hBk, sub_div, sum_div]
      refine (Rat.padicValuation p).map_sub_le ?_ ?_
      · -- m ^ (k - 1) / p ^ e is a natural number
        have hdvd : p ^ e ∣ m ^ (k - 1) :=
          dvd_trans pow_padicValNat_dvd (dvd_pow_self m (by omega))
        have hcast : (m : ℚ) ^ (k - 1) / (p : ℚ) ^ e = ((m ^ (k - 1) / p ^ e : ℕ) : ℚ) := by
          rw [Nat.cast_div hdvd (by exact_mod_cast (pow_pos hp.pos e).ne')]
          push_cast; rfl
        rw [hcast]
        exact_mod_cast Int.padicValuation_le_one p (m ^ (k - 1) / p ^ e)
      · refine (Rat.padicValuation p).map_sum_le fun i hi => ?_
        have hik : i < k := mem_range.mp hi
        rcases i with _ | _ | i'
        · -- i = 0: m^k / ((k + 1) * p^e)
          simp only [bernoulli_zero, one_mul, Nat.choose_zero_right, Nat.cast_one, Nat.sub_zero]
          rw [div_div]
          have hrew : (m : ℚ) ^ k / ((k + 1 : ℚ) * (p : ℚ) ^ e) =
              ((m ^ k : ℕ) : ℚ) / (((k + 1) * p ^ e : ℕ) : ℚ) := by push_cast; rfl
          rw [hrew]
          refine padicValuation_nat_div_le_one (by positivity) ?_
          rw [padicValNat.mul (by omega) (pow_pos hp.pos e).ne', padicValNat.pow (p := p) (a := m) k,
            padicValNat.pow (p := p) (a := p) e, padicValNat.self hp.one_lt, mul_one]
          have hv1 := padicValNat_add_one_le_sub_two hp hp5 (by omega : 2 ≤ k)
          have h1 : 1 * (k - 1) ≤ e * (k - 1) := Nat.mul_le_mul_right (k - 1) he_pos
          have h2 : e * (k - 1) + e = k * e := by
            rw [← Nat.mul_succ, show (k - 1).succ = k by omega, mul_comm]
          change padicValNat p (k + 1) + e ≤ k * e
          omega
        · -- i = 1: (-1/2) * (k + 1) * m^(k - 1) / ((k + 1) * p^e)
          simp only [zero_add, bernoulli_one, Nat.choose_one_right]
          have hk1 : (k : ℚ) + 1 ≠ 0 := by positivity
          have hrew : (-1 / 2 : ℚ) * ((k + 1 : ℕ) : ℚ) * (m : ℚ) ^ (k - 1) / (k + 1 : ℚ) / (p : ℚ) ^ e =
              -(((m ^ (k - 1) : ℕ) : ℚ) / ((2 * p ^ e : ℕ) : ℚ)) := by
            push_cast; field_simp
          rw [hrew, Valuation.map_neg]
          refine padicValuation_nat_div_le_one (by positivity) ?_
          have hp_ndvd2 : ¬ p ∣ 2 := fun hd => by
            have := Nat.le_of_dvd (by norm_num) hd; omega
          rw [padicValNat.mul (by norm_num) (pow_pos hp.pos e).ne',
            padicValNat.eq_zero_of_not_dvd hp_ndvd2, zero_add,
            padicValNat.pow (p := p) (a := m) (k - 1),
            padicValNat.pow (p := p) (a := p) e, padicValNat.self hp.one_lt, mul_one]
          change e ≤ (k - 1) * e
          exact Nat.le_mul_of_pos_left e (by omega)
        · -- i = i' + 2: split by parity
          rcases Nat.even_or_odd (i' + 2) with ⟨s, hs⟩ | hodd_i
          · have h2s : i' + 2 = 2 * s := by omega
            rw [h2s]
            set d := k - 2 * s
            have hd2 : 2 ≤ d := by
              obtain ⟨t, ht⟩ := heven
              omega
            have hch : ((k + 1).choose (2 * s) : ℚ) / (k + 1 : ℚ) =
                (k.choose (2 * s) : ℚ) / ((d + 1 : ℕ) : ℚ) := by
              have hnat : (k + 1) * k.choose (2 * s) = (d + 1) * (k + 1).choose (2 * s) := by
                have := choose_mul_sub_eq k (2 * s) (by omega)
                have hsub : k + 1 - 2 * s = d + 1 := by omega
                rw [hsub] at this
                exact this
              have hcast : ((k + 1 : ℕ) : ℚ) * (k.choose (2 * s) : ℚ) =
                  ((d + 1 : ℕ) : ℚ) * ((k + 1).choose (2 * s) : ℚ) := by exact_mod_cast hnat
              rw [div_eq_div_iff (by positivity) (by positivity)]
              push_cast at hcast ⊢
              linarith
            have hrew : bernoulli (2 * s) * ((k + 1).choose (2 * s) : ℚ) * (m : ℚ) ^ d /
                (k + 1 : ℚ) / (p : ℚ) ^ e =
                (k.choose (2 * s) : ℚ) * ((p : ℚ) * bernoulli (2 * s)) *
                (((m ^ d : ℕ) : ℚ) / (((d + 1) * p ^ (e + 1) : ℕ) : ℚ)) := by
              have h1 : bernoulli (2 * s) * ((k + 1).choose (2 * s) : ℚ) * (m : ℚ) ^ d / (k + 1 : ℚ) =
                  bernoulli (2 * s) * (((k + 1).choose (2 * s) : ℚ) / (k + 1 : ℚ)) * (m : ℚ) ^ d := by ring
              rw [h1, hch]
              push_cast
              rw [pow_succ]
              field_simp
            rw [hrew]
            have hmul_le : ∀ x y : ℚ, Rat.padicValuation p x ≤ 1 → Rat.padicValuation p y ≤ 1 →
                Rat.padicValuation p (x * y) ≤ 1 := fun x y hx hy =>
              ((Rat.padicValuation p).map_mul x y).trans_le (mul_le_one' hx hy)
            refine hmul_le _ _ (hmul_le _ _ ?_ padicValuation_p_mul_bernoulli_even_le_one) ?_
            · exact_mod_cast Int.padicValuation_le_one p (k.choose (2 * s))
            · refine padicValuation_nat_div_le_one (by positivity) ?_
              rw [padicValNat.mul (by omega) (pow_pos hp.pos (e + 1)).ne',
                padicValNat.pow (p := p) (a := m) d,
                padicValNat.pow (p := p) (a := p) (e + 1), padicValNat.self hp.one_lt, mul_one]
              have hv1 := padicValNat_add_one_le_sub_two hp hp5 hd2
              have h1 : 1 * (d - 1) ≤ e * (d - 1) := Nat.mul_le_mul_right (d - 1) he_pos
              have h2 : e * (d - 1) + e = d * e := by
                rw [← Nat.mul_succ, show (d - 1).succ = d by omega, mul_comm]
              change padicValNat p (d + 1) + (e + 1) ≤ d * e
              omega
          · simp [bernoulli_eq_zero_of_odd hodd_i (by omega)]
    -- Extract p^e ∣ (bernoulli k).num.natAbs from Rat.padicValuation p (bernoulli k / p^e) ≤ 1
    set y : ℚ := bernoulli k / (p : ℚ) ^ e
    have hy_ndvd : ¬ p ∣ y.den := Rat.padicValuation_le_one_iff.mp hval_le
    have hy_eq : bernoulli k = y * (p : ℚ) ^ e := by dsimp only [y]; field_simp
    have hnum_eq : ((bernoulli k).num : ℚ) / ((bernoulli k).den : ℚ) =
        ((y.num : ℚ) * (p : ℚ) ^ e) / (y.den : ℚ) := by
      calc ((bernoulli k).num : ℚ) / ((bernoulli k).den : ℚ)
          = bernoulli k := Rat.num_div_den (bernoulli k)
        _ = y * (p : ℚ) ^ e := hy_eq
        _ = ((y.num : ℚ) / (y.den : ℚ)) * (p : ℚ) ^ e := by rw [Rat.num_div_den y]
        _ = ((y.num : ℚ) * (p : ℚ) ^ e) / (y.den : ℚ) := div_mul_eq_mul_div _ _ _
    have hcrossQ : ((bernoulli k).num : ℚ) * (y.den : ℚ) =
        (y.num : ℚ) * (p : ℚ) ^ e * ((bernoulli k).den : ℚ) := by
      have h1 : ((bernoulli k).den : ℚ) ≠ 0 := by exact_mod_cast (bernoulli k).pos.ne'
      have h2 : (y.den : ℚ) ≠ 0 := by exact_mod_cast y.pos.ne'
      exact (div_eq_div_iff h1 h2).mp hnum_eq
    have hcrossZ : (bernoulli k).num * (y.den : ℤ) =
        y.num * (p : ℤ) ^ e * ((bernoulli k).den : ℤ) := by exact_mod_cast hcrossQ
    have hcrossN : (bernoulli k).num.natAbs * y.den =
        y.num.natAbs * p ^ e * (bernoulli k).den := by
      have h := congrArg Int.natAbs hcrossZ
      simp only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast] at h
      exact h
    have hdvd_prod : p ^ e ∣ (bernoulli k).num.natAbs * y.den :=
      ⟨y.num.natAbs * (bernoulli k).den, by linarith⟩
    have hcop : Nat.Coprime (p ^ e) y.den :=
      (hp.coprime_iff_not_dvd.mpr hy_ndvd).pow_left e
    exact hcop.dvd_of_dvd_mul_right hdvd_prod
  -- Combine prime powers into m ∣ (bernoulli k).num.natAbs
  have hm_prod : ∏ p ∈ m.primeFactors, p ^ (padicValNat p m) = m := by
    conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hm.ne']
    rw [Finsupp.prod, Nat.support_factorization]
    refine prod_congr rfl fun p hp => ?_
    rw [Nat.factorization_def m (Nat.prime_of_mem_primeFactors hp)]
  rw [← hm_prod]
  have haux : ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime ∧ p ^ (padicValNat p m) ∣ (bernoulli k).num.natAbs) →
      (∏ p ∈ S, p ^ (padicValNat p m)) ∣ (bernoulli k).num.natAbs := by
    intro S
    induction S using Finset.induction_on with
    | empty => intro _; simp
    | @insert a s has ih =>
      intro h
      rw [prod_insert has]
      have ha := h a (mem_insert_self a s)
      have hs := ih (fun p hp => h p (mem_insert_of_mem hp))
      have hcop : Nat.Coprime (a ^ (padicValNat a m)) (∏ p ∈ s, p ^ (padicValNat p m)) := by
        refine Nat.Coprime.prod_right fun p hp => ?_
        have hne : a ≠ p := fun heq => has (heq ▸ hp)
        exact ((Nat.coprime_primes ha.1 (h p (mem_insert_of_mem hp)).1).mpr hne).pow _ _
      exact hcop.mul_dvd_of_dvd_of_dvd ha.2 hs
  exact haux m.primeFactors fun p hp => ⟨Nat.prime_of_mem_primeFactors hp, hprime_pow p hp⟩

theorem main : H1 → H2 → H3 → OMA.R_ErdosMoser_erdos_moser_conjecture_R1.H2 := by
  intro h1 h2 h3 k m hk hm heven heq
  have hklo := krzysztofek_lower hk hm heven heq
  have hkhi := krzysztofek_upper hk hm heven heq
  have hm_moser := moser_1953_bound hk hm heven heq
  have hm9 : 10 ^ 9 < m :=
    lt_trans (Nat.pow_lt_pow_right (by omega) (by omega : 9 < 1000000)) hm_moser
  have hv2 := padicValNat_two_m_sub_three hk hm heven heq
  have hbern := voronoi_m_dvd_bernoulli_num hk hm heven heq
  have hsq1 := squarefree_m_sub_one hk hm heven heq
  have hsq2 := squarefree_m_add_one_div_two hk hm heven heq
  have hsq3 := squarefree_two_m_sub_one hk hm heven heq
  have hsq4 := squarefree_two_m_add_one hk hm heven heq
  obtain ⟨_, hsqM1, _, hineq⟩ := moser_M1_structure hk hm heven heq
  have hmoser_dvd : ∀ p : ℕ, p.Prime →
      (p ∣ m - 1 ∨ p ∣ m + 1 ∨ p ∣ 2 * m - 1 ∨ p ∣ 2 * m + 1) → p - 1 ∣ k := by
    intro p hp hdiv
    rcases hdiv with hA | hB | hC | hD
    · exact (moser_m_sub_one hk hm heven heq hp hA).1
    · exact (moser_m_add_one hk hm heven heq hp hB).1
    · exact (moser_two_m_sub_one hk hm heven heq hp hC).1
    · exact (moser_two_m_add_one hk hm heven heq hp hD).1
  have hunif : ∀ p : ℕ, p.Prime → p - 1 ∣ k →
      ¬ p ∣ m ∧ (p = 2 ∨ p ^ 2 ≤ m ∨ m = p ^ 2 - p + 1) ∧
      (p ≠ 2 → ((p - 1) * m + m % p) ≡ 2 * p [MOD p ^ (padicValNat p k + 2)]) := by
    intro p hp hpk
    refine ⟨not_dvd_m_of_sub_one_dvd_k hk hm heven heq hp hpk, ?_, ?_⟩
    · rcases eq_or_ne p 2 with rfl | hp2
      · exact Or.inl rfl
      · exact Or.inr (sqrt_m_smooth hk hm heven heq hp hp2 hpk)
    · intro hp2
      exact unified_prime_pow_congr hk hm heven heq hp hp2 hpk
  obtain ⟨hgmz_lo, hgmz_hi, hgmz_conv⟩ := h1 k m hk hm9 heven hklo hkhi heq
  have h3nm := three_not_dvd_m hk hm heven heq
  have hm3 : m % 3 = 1 ∨ m % 3 = 2 := by omega
  rcases hm3 with hm3_1 | hm3_2
  · exact h2 k m hk heven hm_moser hklo hkhi hm3_1
      (three_adic_m_mod_one hk hm heven heq hm3_1) hv2 hbern heq
      ⟨hsq1, hsq2, hsq3, hsq4, hsqM1⟩ hmoser_dvd hunif hineq
      hgmz_lo hgmz_hi hgmz_conv
  · exact h3 k m hk heven hm_moser hklo hkhi hm3_2
      (three_adic_m_mod_two hk hm heven heq hm3_2) hv2 hbern heq
      ⟨hsq1, hsq2, hsq3, hsq4, hsqM1⟩ hmoser_dvd hunif hineq
      hgmz_lo hgmz_hi hgmz_conv

end OMA.R_ErdosMoser_erdos_moser_conjecture_R1_H2_R2
