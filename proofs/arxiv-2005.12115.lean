import OMAStatements.S_arxiv_2005_12115
import Mathlib

-- Problem: arxiv-2005.12115, a primitive non-deficient number n with k distinct prime factors has
-- a prime power component p ^ (a + 1) below 2 k rad(n) (Zelinsky, arXiv:2005.12115, Theorem 2).
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- The argument follows the idea of the source (compare sigma(n) / n with the product of
-- p / (p - 1) over the primes dividing n); the Lean proof is our own.

/-!
Proof of Theorem 2 of Zelinsky, arXiv:2005.12115, following the idea of the paper.
Write `x p = p ^ (a_p + 1)`, `R = rad n`, `Φ = ∏ (p - 1)`, `T = 2 k R`. Then
`σ(n) Φ = ∏ (x p - 1)` and `n R = ∏ x p`, so non-deficiency gives `2 Φ < R`, hence `2 Φ + 1 ≤ R`,
and (comparing the `k` distinct primes with consecutive integers) the least prime `q` is at
most `k`. If every `x p` were at least `T`, then for `m = n / q` a Bernoulli-type product bound
gives `σ(m) Φ T² ≥ m R (T - q) (T - (k - 1))`, while deficiency of `m` gives
`σ(m) Φ < m (R - 1)`. Together these force `q > k + 1`, a contradiction.
-/

namespace F2Zel

open Finset

theorem telescoping : ∀ (k : ℕ) (S : Finset ℕ), S.card = k → ∀ r : ℕ, (∀ p ∈ S, r + 1 ≤ p) →
    r * ∏ p ∈ S, p ≤ (r + k) * ∏ p ∈ S, (p - 1) := by
  intro k
  induction k with
  | zero =>
    intro S hS r _
    rw [Finset.card_eq_zero] at hS
    subst hS
    simp
  | succ k ih =>
    intro S hS r hr
    have hne : S.Nonempty := Finset.card_pos.mp (by omega)
    have hM : S.max' hne ∈ S := S.max'_mem hne
    have hmax : ∀ p ∈ S, p ≤ S.max' hne := fun p hp => S.le_max' p hp
    obtain ⟨M, hMdef⟩ : ∃ M, M = S.max' hne := ⟨_, rfl⟩
    rw [← hMdef] at hM hmax
    have hcard' : (S.erase M).card = k := by
      rw [Finset.card_erase_of_mem hM, hS]
      rfl
    have hIH := ih (S.erase M) hcard' r (fun p hp => hr p (Finset.mem_of_mem_erase hp))
    have hMbig : r + k + 1 ≤ M := by
      have hsub : S ⊆ Finset.Icc (r + 1) M := fun p hp => Finset.mem_Icc.mpr ⟨hr p hp, hmax p hp⟩
      have h1 := Finset.card_le_card hsub
      rw [Nat.card_Icc, hS] at h1
      omega
    have e1 : ∏ p ∈ S, p = M * ∏ p ∈ S.erase M, p := (Finset.mul_prod_erase S (fun p => p) hM).symm
    have e2 : ∏ p ∈ S, (p - 1) = (M - 1) * ∏ p ∈ S.erase M, (p - 1) :=
      (Finset.mul_prod_erase S (fun p => p - 1) hM).symm
    rw [e1, e2]
    obtain ⟨N, rfl⟩ : ∃ N, M = N + 1 := ⟨M - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    have h2 : (N + 1) * (r + k) ≤ (r + (k + 1)) * N := by nlinarith
    calc r * ((N + 1) * ∏ p ∈ S.erase (N + 1), p)
        = (N + 1) * (r * ∏ p ∈ S.erase (N + 1), p) := by ring
      _ ≤ (N + 1) * ((r + k) * ∏ p ∈ S.erase (N + 1), (p - 1)) := Nat.mul_le_mul_left _ hIH
      _ = ((N + 1) * (r + k)) * ∏ p ∈ S.erase (N + 1), (p - 1) := by ring
      _ ≤ ((r + (k + 1)) * N) * ∏ p ∈ S.erase (N + 1), (p - 1) := Nat.mul_le_mul_right _ h2
      _ = (r + (k + 1)) * (N * ∏ p ∈ S.erase (N + 1), (p - 1)) := by ring

theorem bernoulli (x : ℕ → ℝ) (T : ℝ) (hT : 1 ≤ T) : ∀ s : Finset ℕ, (∀ p ∈ s, T ≤ x p) →
    (T - s.card) * ∏ p ∈ s, x p ≤ T * ∏ p ∈ s, (x p - 1) := by
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro _
    simp
  | insert a s ha ih =>
    intro h
    have hxa : T ≤ x a := h a (Finset.mem_insert_self a s)
    have hs : ∀ p ∈ s, T ≤ x p := fun p hp => h p (Finset.mem_insert_of_mem hp)
    have hIH := ih hs
    have hX : 0 ≤ ∏ p ∈ s, x p := Finset.prod_nonneg (fun p hp => by linarith [hs p hp])
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    push_cast
    have h1 : (x a - 1) * ((T - s.card) * ∏ p ∈ s, x p) ≤ (x a - 1) * (T * ∏ p ∈ s, (x p - 1)) :=
      mul_le_mul_of_nonneg_left hIH (by linarith)
    have hc : (0 : ℝ) ≤ s.card := Nat.cast_nonneg _
    have h2 : 0 ≤ (x a - T + s.card) * ∏ p ∈ s, x p := mul_nonneg (by linarith) hX
    nlinarith [h1, h2]

theorem sigma_eq (n : ℕ) : ArithmeticFunction.sigma 1 n = ∑ i ∈ n.properDivisors, i + n := by
  rw [ArithmeticFunction.sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]

theorem sigma_prod (n : ℕ) (hn : n ≠ 0) : ArithmeticFunction.sigma 1 n =
    ∏ p ∈ n.primeFactors, ArithmeticFunction.sigma 1 (p ^ n.factorization p) := by
  rw [ArithmeticFunction.IsMultiplicative.multiplicative_factorization _
    ArithmeticFunction.isMultiplicative_sigma hn]
  exact Nat.prod_factorization_eq_prod_primeFactors _

theorem self_prod (n : ℕ) (hn : n ≠ 0) : n = ∏ p ∈ n.primeFactors, p ^ n.factorization p :=
  (Nat.prod_factorization_pow_eq_self hn).symm.trans (Nat.prod_factorization_eq_prod_primeFactors _)

theorem sigma_pp (p a : ℕ) (hp : p.Prime) :
    ((ArithmeticFunction.sigma 1 (p ^ a) : ℕ) : ℝ) * ((p : ℝ) - 1) = (p : ℝ) ^ (a + 1) - 1 := by
  rw [ArithmeticFunction.sigma_one_apply_prime_pow hp]
  push_cast
  rw [mul_comm]
  exact mul_geom_sum (p : ℝ) (a + 1)


set_option maxHeartbeats 2000000 in
theorem zelinsky (n : ℕ) (hpos : 0 < n) (hnd : ¬ n.Deficient)
    (hprim : ∀ d : ℕ, d ∣ n → d ≠ n → d.Deficient) :
    ∃ p ∈ n.primeFactors,
      p ^ (n.factorization p + 1) < 2 * n.primeFactors.card * ∏ q ∈ n.primeFactors, q := by
  by_contra hcon
  have hbig : ∀ p ∈ n.primeFactors,
      2 * n.primeFactors.card * ∏ q ∈ n.primeFactors, q ≤ p ^ (n.factorization p + 1) :=
    fun p hp => not_lt.mp (fun h => hcon ⟨p, hp, h⟩)
  have hn0 : n ≠ 0 := hpos.ne'
  have hσn : 2 * n ≤ ArithmeticFunction.sigma 1 n := by
    rw [sigma_eq]
    unfold Nat.Deficient at hnd
    omega
  have hprime : ∀ p ∈ n.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  obtain ⟨k, hk⟩ : ∃ k, k = n.primeFactors.card := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R, R = ∏ q ∈ n.primeFactors, q := ⟨_, rfl⟩
  obtain ⟨Φ, hΦ⟩ : ∃ Φ, Φ = ∏ q ∈ n.primeFactors, (q - 1) := ⟨_, rfl⟩
  rw [← hk, ← hR] at hbig
  have hRr : (R : ℝ) = ∏ q ∈ n.primeFactors, (q : ℝ) := by
    rw [hR, Nat.cast_prod]
  have hΦr : (Φ : ℝ) = ∏ q ∈ n.primeFactors, ((q : ℝ) - 1) := by
    rw [hΦ, Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro q hq
    exact Nat.cast_pred (hprime q hq).pos
  have I1 : ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) * (Φ : ℝ) =
      ∏ p ∈ n.primeFactors, ((p : ℝ) ^ (n.factorization p + 1) - 1) := by
    rw [hΦr, sigma_prod n hn0, Nat.cast_prod, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro p hp
    exact sigma_pp p _ (hprime p hp)
  have hself : (n : ℝ) = ∏ p ∈ n.primeFactors, (p : ℝ) ^ n.factorization p := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) (self_prod n hn0)
  have I2 : (n : ℝ) * (R : ℝ) = ∏ p ∈ n.primeFactors, (p : ℝ) ^ (n.factorization p + 1) := by
    rw [hRr, hself, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro p _
    rw [pow_succ]
  have hx1 : ∀ p ∈ n.primeFactors, (1 : ℝ) < (p : ℝ) ^ (n.factorization p + 1) := by
    intro p hp
    have h2 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (hprime p hp).one_lt
    exact one_lt_pow₀ h2 (by omega)
  have hne : n.primeFactors.Nonempty := by
    rw [Nat.nonempty_primeFactors]
    by_contra h1
    have hn1 : n = 1 := by omega
    rw [hn1, sigma_eq] at hσn
    simp at hσn
  have hlt : ∏ p ∈ n.primeFactors, ((p : ℝ) ^ (n.factorization p + 1) - 1) <
      ∏ p ∈ n.primeFactors, (p : ℝ) ^ (n.factorization p + 1) :=
    Finset.prod_lt_prod_of_nonempty (fun p hp => by linarith [hx1 p hp])
      (fun p _ => by linarith) hne
  have hnR : (0 : ℝ) < n := by exact_mod_cast hpos
  have h2Φr : 2 * (Φ : ℝ) < (R : ℝ) := by
    have h1 : (2 : ℝ) * n ≤ ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) := by exact_mod_cast hσn
    have hΦ0 : (0 : ℝ) ≤ Φ := Nat.cast_nonneg _
    have h3 := mul_le_mul_of_nonneg_right h1 hΦ0
    rw [I1] at h3
    have h4 : (n : ℝ) * (2 * (Φ : ℝ)) < (n : ℝ) * (R : ℝ) := by
      rw [I2]
      linarith
    exact lt_of_mul_lt_mul_left h4 hnR.le
  have h2Φ : 2 * Φ + 1 ≤ R := by
    have h1 : 2 * Φ < R := by exact_mod_cast h2Φr
    omega
  obtain ⟨q, hqdef⟩ : ∃ q, q = n.primeFactors.min' hne := ⟨_, rfl⟩
  have hqS : q ∈ n.primeFactors := by
    rw [hqdef]
    exact Finset.min'_mem _ _
  have hqmin : ∀ p ∈ n.primeFactors, q ≤ p := by
    intro p hp
    rw [hqdef]
    exact Finset.min'_le _ p hp
  have hq : q.Prime := hprime q hqS
  obtain ⟨r, hr⟩ : ∃ r, q = r + 1 := ⟨q - 1, by have := hq.pos; omega⟩
  have hL := telescoping k n.primeFactors hk.symm r (fun p hp => by have := hqmin p hp; omega)
  rw [← hR, ← hΦ] at hL
  have hr1 : 1 ≤ r := by
    have := hq.two_le
    omega
  have hqk : q ≤ k := by
    by_contra hcon2
    have hkr : k ≤ r := by omega
    have h1 : k * Φ ≤ r * Φ := Nat.mul_le_mul_right _ hkr
    have h3 : r * (2 * Φ + 1) ≤ r * R := Nat.mul_le_mul_left _ h2Φ
    nlinarith
  obtain ⟨m, hm⟩ := Nat.dvd_of_mem_primeFactors hqS
  have hmpos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0, mul_zero] at hm
      omega
    · exact h0
  have hmdvd : m ∣ n := ⟨q, by rw [hm, mul_comm]⟩
  have hmne : m ≠ n := by
    intro h
    rw [← h] at hm
    have := hq.two_le
    nlinarith
  have hmdef : m.Deficient := hprim m hmdvd hmne
  have hσm : ArithmeticFunction.sigma 1 m < 2 * m := by
    rw [sigma_eq]
    unfold Nat.Deficient at hmdef
    omega
  obtain ⟨a, ha⟩ : ∃ a, a = n.factorization q := ⟨_, rfl⟩
  have ha1 : 1 ≤ a := by
    rw [ha]
    exact hq.factorization_pos_of_dvd hn0 (Nat.dvd_of_mem_primeFactors hqS)
  obtain ⟨u, hu⟩ : ∃ u, u = n / q ^ a := ⟨_, rfl⟩
  have hnu : q ^ a * u = n := by
    rw [hu, ha]
    exact Nat.ordProj_mul_ordCompl_eq_self n q
  have hcop : Nat.Coprime q u := by
    rw [hu, ha]
    exact Nat.coprime_ordCompl hq hn0
  have hmu : m = q ^ (a - 1) * u := by
    have h1 : q * m = q * (q ^ (a - 1) * u) := by
      rw [← hm, ← mul_assoc, ← pow_succ', Nat.sub_add_cancel ha1, hnu]
    exact Nat.eq_of_mul_eq_mul_left hq.pos h1
  have hσn' : ArithmeticFunction.sigma 1 n =
      ArithmeticFunction.sigma 1 (q ^ a) * ArithmeticFunction.sigma 1 u := by
    rw [← hnu]
    exact ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (Nat.Coprime.pow_left a hcop)
  have hσm' : ArithmeticFunction.sigma 1 m =
      ArithmeticFunction.sigma 1 (q ^ (a - 1)) * ArithmeticFunction.sigma 1 u := by
    rw [hmu]
    exact ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime
      (Nat.Coprime.pow_left (a - 1) hcop)
  have hsa := sigma_pp q a hq
  have hsa' := sigma_pp q (a - 1) hq
  rw [Nat.sub_add_cancel ha1] at hsa'
  have hqr2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq.two_le
  have hrel : ((ArithmeticFunction.sigma 1 m : ℕ) : ℝ) * ((q : ℝ) ^ (a + 1) - 1) =
      ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) * ((q : ℝ) ^ a - 1) := by
    rw [hσn', hσm', ← hsa, ← hsa']
    push_cast
    ring
  have eY : ∏ p ∈ n.primeFactors, ((p : ℝ) ^ (n.factorization p + 1) - 1) =
      ((q : ℝ) ^ (a + 1) - 1) *
        ∏ p ∈ n.primeFactors.erase q, ((p : ℝ) ^ (n.factorization p + 1) - 1) := by
    rw [ha]
    exact (Finset.mul_prod_erase n.primeFactors
      (fun p : ℕ => (p : ℝ) ^ (n.factorization p + 1) - 1) hqS).symm
  have eX : ∏ p ∈ n.primeFactors, (p : ℝ) ^ (n.factorization p + 1) =
      (q : ℝ) ^ (a + 1) * ∏ p ∈ n.primeFactors.erase q, (p : ℝ) ^ (n.factorization p + 1) := by
    rw [ha]
    exact (Finset.mul_prod_erase n.primeFactors
      (fun p : ℕ => (p : ℝ) ^ (n.factorization p + 1)) hqS).symm
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = 2 * (k : ℝ) * (R : ℝ) := ⟨_, rfl⟩
  have hbigr : ∀ p ∈ n.primeFactors, T ≤ (p : ℝ) ^ (n.factorization p + 1) := by
    intro p hp
    rw [hT]
    exact_mod_cast hbig p hp
  have hk1 : 1 ≤ k := by
    have := hq.two_le
    omega
  have hR1 : 1 ≤ R := by omega
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hRr1 : (1 : ℝ) ≤ R := by exact_mod_cast hR1
  have hTk : (k : ℝ) ≤ T := by
    rw [hT]
    nlinarith
  have hT1 : 1 ≤ T := by linarith
  have hX0 : 0 ≤ ∏ p ∈ n.primeFactors.erase q, (p : ℝ) ^ (n.factorization p + 1) :=
    Finset.prod_nonneg (fun p hp => by
      have := hx1 p (Finset.mem_of_mem_erase hp)
      linarith)
  have hcard : ((n.primeFactors.erase q).card : ℝ) = (k : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem hqS, ← hk, Nat.cast_pred (by omega)]
  have hB : (T - ((n.primeFactors.erase q).card : ℝ)) *
      ∏ p ∈ n.primeFactors.erase q, (p : ℝ) ^ (n.factorization p + 1) ≤
      T * ∏ p ∈ n.primeFactors.erase q, ((p : ℝ) ^ (n.factorization p + 1) - 1) :=
    bernoulli (fun p : ℕ => (p : ℝ) ^ (n.factorization p + 1)) T hT1 _
      (fun p hp => hbigr p (Finset.mem_of_mem_erase hp))
  rw [hcard] at hB
  obtain ⟨X, hX⟩ : ∃ X : ℝ,
      X = ∏ p ∈ n.primeFactors.erase q, (p : ℝ) ^ (n.factorization p + 1) := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y : ℝ,
      Y = ∏ p ∈ n.primeFactors.erase q, ((p : ℝ) ^ (n.factorization p + 1) - 1) := ⟨_, rfl⟩
  rw [← hX] at eX hB hX0
  rw [← hY] at eY hB
  obtain ⟨z, hz⟩ : ∃ z : ℝ, z = (q : ℝ) ^ a := ⟨_, rfl⟩
  have hzq : (q : ℝ) ^ (a + 1) = z * (q : ℝ) := by rw [hz, pow_succ]
  have hxq := hbigr q hqS
  have hxq1 := hx1 q hqS
  rw [← ha, hzq] at hxq hxq1
  rw [hzq] at eX eY hrel
  rw [← hz] at hrel
  have hσmΦ : ((ArithmeticFunction.sigma 1 m : ℕ) : ℝ) * (Φ : ℝ) = (z - 1) * Y := by
    have h1 : (z * (q : ℝ) - 1) * (((ArithmeticFunction.sigma 1 m : ℕ) : ℝ) * (Φ : ℝ)) =
        (z * (q : ℝ) - 1) * ((z - 1) * Y) := by
      have h2 : ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) * (Φ : ℝ) = (z * (q : ℝ) - 1) * Y := by
        rw [I1, eY]
      linear_combination (Φ : ℝ) * hrel + (z - 1) * h2
    exact mul_left_cancel₀ (by linarith) h1
  have hqpos : (0 : ℝ) < (q : ℝ) := by linarith
  have hnm : (n : ℝ) = (q : ℝ) * (m : ℝ) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) hm
  have hmR : (m : ℝ) * (R : ℝ) = z * X := by
    have h1 : (q : ℝ) * ((m : ℝ) * (R : ℝ)) = (q : ℝ) * (z * X) := by
      have h2 := I2
      rw [eX, hnm] at h2
      linear_combination h2
    exact mul_left_cancel₀ hqpos.ne' h1
  have hz1 : 1 ≤ z := by
    rw [hz]
    exact one_le_pow₀ (by linarith)
  have hg : z * (T - (q : ℝ)) ≤ T * (z - 1) := by nlinarith
  have hqkr : (q : ℝ) ≤ (k : ℝ) := by exact_mod_cast hqk
  have hc1 : 0 ≤ (T - ((k : ℝ) - 1)) * X := mul_nonneg (by linarith) hX0
  have hc2 : 0 ≤ T * (z - 1) := mul_nonneg (by linarith) (by linarith)
  have hmain := mul_le_mul hg hB hc1 hc2
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hmpos
  have hΦpos : (0 : ℝ) < (Φ : ℝ) := by
    have h1 : 0 < Φ := by
      rw [hΦ]
      exact Finset.prod_pos (fun p hp => Nat.sub_pos_of_lt (hprime p hp).one_lt)
    exact_mod_cast h1
  have hup : ((ArithmeticFunction.sigma 1 m : ℕ) : ℝ) * (Φ : ℝ) < (m : ℝ) * ((R : ℝ) - 1) := by
    have h1 : ((ArithmeticFunction.sigma 1 m : ℕ) : ℝ) < 2 * (m : ℝ) := by exact_mod_cast hσm
    have h2 : 2 * (Φ : ℝ) ≤ (R : ℝ) - 1 := by
      have h3 : ((2 * Φ + 1 : ℕ) : ℝ) ≤ (R : ℝ) := by exact_mod_cast h2Φ
      push_cast at h3
      linarith
    nlinarith [mul_lt_mul_of_pos_right h1 hΦpos, mul_le_mul_of_nonneg_left h2 hm0.le]
  have e1 : z * (T - (q : ℝ)) * ((T - ((k : ℝ) - 1)) * X) =
      (m : ℝ) * ((R : ℝ) * ((T - (q : ℝ)) * (T - ((k : ℝ) - 1)))) := by
    have h1 : z * (T - (q : ℝ)) * ((T - ((k : ℝ) - 1)) * X) =
        (z * X) * ((T - (q : ℝ)) * (T - ((k : ℝ) - 1))) := by ring
    rw [h1, ← hmR]
    ring
  have e2 : T * (z - 1) * (T * Y) =
      T * T * (((ArithmeticFunction.sigma 1 m : ℕ) : ℝ) * (Φ : ℝ)) := by
    rw [hσmΦ]
    ring
  rw [e1, e2] at hmain
  have hTT : 0 < T * T := by nlinarith
  have h6 := mul_lt_mul_of_pos_left hup hTT
  have h7 : (m : ℝ) * ((R : ℝ) * ((T - (q : ℝ)) * (T - ((k : ℝ) - 1)))) <
      (m : ℝ) * (T * T * ((R : ℝ) - 1)) := by linarith
  have h7' := lt_of_mul_lt_mul_left h7 hm0.le
  have h8 : T * T - T * ((q : ℝ) + ((k : ℝ) - 1)) ≤ (T - (q : ℝ)) * (T - ((k : ℝ) - 1)) := by
    nlinarith [mul_nonneg hqpos.le (sub_nonneg.mpr hkr)]
  have h9 : T * T < T * ((R : ℝ) * ((q : ℝ) + ((k : ℝ) - 1))) := by
    nlinarith [mul_le_mul_of_nonneg_left h8 (by linarith : (0 : ℝ) ≤ (R : ℝ))]
  have h10 := lt_of_mul_lt_mul_left h9 (by linarith : (0 : ℝ) ≤ T)
  rw [hT] at h10
  nlinarith [mul_le_mul_of_nonneg_left hqkr (by linarith : (0 : ℝ) ≤ (R : ℝ))]

end F2Zel

theorem OMA.solution : type_of% @OMA.S_arxiv_2005_12115.main := by
  intro n h
  unfold OMA.S_arxiv_2005_12115.PrimitiveNonDeficient at h
  exact F2Zel.zelinsky n h.1 h.2.1 h.2.2
