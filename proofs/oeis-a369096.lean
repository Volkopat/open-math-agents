import OMAStatements.S_oeis_a369096
import Mathlib

/-!
# OEIS A369096: the primes have relative density zero among the terms

Since `T(k) + T(k+1) = (k+1)^2`, every product `p * q` of two distinct odd primes is a term
(it has two distinct prime divisors and `(k+1)^2` is even). For a fixed `M`, the products `p * q`
with `p` an odd prime at most `M` and `q` a prime in `(M, N / p]` are pairwise distinct, so
`count N ≥ ∑_{3 ≤ p ≤ M} (π (N / p) - (M + 1))`. Chebyshev's bounds give
`π (N / p) ≥ d * π N / p` for large `N`, and the sum of the reciprocals of the primes diverges,
so `count N / π N` tends to infinity.
-/

open Filter Finset

namespace OMA.A369096

/-- The odd primes up to `M`. -/
def P (M : ℕ) : Finset ℕ := (range (M + 1)).filter (fun p => p.Prime ∧ 3 ≤ p)

theorem member_mul {p q : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hq : q.Prime) (hpq : p < q) :
    OMA.S_oeis_a369096.member (p * q) := by
  have hpo : Odd p := hp.odd_of_ne_two (by omega)
  have hqo : Odd q := hq.odd_of_ne_two (by omega)
  have hk : Odd (p * q) := hpo.mul hqo
  refine ⟨by nlinarith, ?_⟩
  have hc : (p * q).primeFactors.card = 2 := by
    rw [Nat.primeFactors_mul hp.ne_zero hq.ne_zero, hp.primeFactors, hq.primeFactors]
    have h : ({p} ∪ {q} : Finset ℕ) = {p, q} := by
      ext x
      simp
    rw [h]
    exact Finset.card_pair (by omega)
  rw [hc]
  obtain ⟨j, hj⟩ := hk
  rw [hj]
  unfold OMA.S_oeis_a369096.triangular
  have h1 : (2 * j + 1) * (2 * j + 1 + 1) = 2 * ((2 * j + 1) * (j + 1)) := by ring
  have h2 : (2 * j + 1 + 1) * (2 * j + 1 + 1 + 1) = 2 * ((j + 1) * (2 * j + 3)) := by ring
  rw [h1, h2, Nat.mul_div_cancel_left _ (by norm_num), Nat.mul_div_cancel_left _ (by norm_num)]
  exact ⟨(j + 1) * (2 * j + 2), by ring⟩

theorem count_ge (M N : ℕ) :
    ∑ p ∈ P M, (Nat.primeCounting (N / p) - (M + 1)) ≤ OMA.S_oeis_a369096.count N := by
  classical
  have each : ∀ p, Nat.primeCounting (N / p) - (M + 1) ≤
      ((Icc (M + 1) (N / p)).filter Nat.Prime).card := by
    intro p
    have hsub : (range (N / p + 1)).filter Nat.Prime ⊆
        range (M + 1) ∪ (Icc (M + 1) (N / p)).filter Nat.Prime := by
      intro q hq
      simp only [mem_filter, mem_range, mem_union, mem_Icc] at hq ⊢
      by_cases h : q < M + 1
      · exact Or.inl h
      · exact Or.inr ⟨⟨by omega, by omega⟩, hq.2⟩
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le (range (M + 1)) ((Icc (M + 1) (N / p)).filter Nat.Prime)
    have h3 : Nat.primeCounting (N / p) = ((range (N / p + 1)).filter Nat.Prime).card := by
      simp [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
    rw [card_range] at h2
    omega
  calc ∑ p ∈ P M, (Nat.primeCounting (N / p) - (M + 1))
      ≤ ∑ p ∈ P M, ((Icc (M + 1) (N / p)).filter Nat.Prime).card :=
        Finset.sum_le_sum (fun p _ => each p)
    _ = ((P M).sigma (fun p => (Icc (M + 1) (N / p)).filter Nat.Prime)).card :=
        (Finset.card_sigma _ _).symm
    _ ≤ OMA.S_oeis_a369096.count N := by
      unfold OMA.S_oeis_a369096.count
      apply Finset.card_le_card_of_injOn (fun x => x.1 * x.2)
      · rintro ⟨p, q⟩ hx
        simp only [P, coe_sigma, Set.mem_sigma_iff, mem_coe, mem_filter, mem_range, mem_Icc] at hx
        obtain ⟨⟨hpM, hp, hp3⟩, ⟨hq1, hq2⟩, hq⟩ := hx
        have hmem := member_mul hp hp3 hq (by omega)
        have hle : q * p ≤ N := (Nat.le_div_iff_mul_le hp.pos).1 hq2
        simp only [mem_coe, mem_filter, mem_Icc]
        exact ⟨⟨hmem.1, by rw [Nat.mul_comm]; exact hle⟩, hmem⟩
      · rintro ⟨p, q⟩ hx ⟨p', q'⟩ hy hxy
        simp only [P, coe_sigma, Set.mem_sigma_iff, mem_coe, mem_filter, mem_range, mem_Icc]
          at hx hy
        obtain ⟨⟨hpM, hp, hp3⟩, ⟨hq1, hq2⟩, hq⟩ := hx
        obtain ⟨⟨hpM', hp', hp3'⟩, ⟨hq1', hq2'⟩, hq'⟩ := hy
        have hxy' : p * q = p' * q' := hxy
        have hdvd : p ∣ p' * q' := ⟨q, hxy'.symm⟩
        have hpp : p = p' := by
          rcases (Nat.Prime.dvd_mul hp).1 hdvd with h | h
          · exact (Nat.prime_dvd_prime_iff_eq hp hp').1 h
          · have := (Nat.prime_dvd_prime_iff_eq hp hq').1 h
            omega
        subst hpp
        have hqq : q = q' := Nat.eq_of_mul_eq_mul_left hp.pos hxy'
        subst hqq
        rfl

theorem pi_lower : ∀ᶠ n : ℕ in atTop,
    Real.log 2 / 2 * n / Real.log n ≤ (Nat.primeCounting n : ℝ) := by
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h := Real.isLittleO_log_id_atTop.bound (show 0 < Real.log 2 / 8 by positivity)
  have h' := (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)).eventually h
  filter_upwards [h', eventually_ge_atTop 2] with n hn hn2
  simp only [Function.comp_apply, id, Real.norm_eq_abs] at hn
  have hn2' : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hx : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by positivity
  rw [abs_of_nonneg hx] at hn
  have hlog1 : Real.log ((n + 1 : ℕ) : ℝ) ≤ Real.log 2 / 8 * ((n + 1 : ℕ) : ℝ) :=
    (le_abs_self _).trans hn
  push_cast at hlog1
  have hlogn : 0 < Real.log n := Real.log_pos (by linarith)
  have hge := Chebyshev.pi_ge n
  refine le_trans ?_ hge
  have hLn : Real.log 2 * 1 ≤ Real.log 2 * n := by
    apply mul_le_mul_of_nonneg_left _ hL.le
    linarith
  apply div_le_div_of_nonneg_right _ hlogn.le
  linarith

theorem pi_upper : ∀ᶠ n : ℕ in atTop,
    (Nat.primeCounting n : ℝ) ≤ (Real.log 4 + 1) * n / Real.log n := by
  have h := tendsto_natCast_atTop_atTop.eventually
    (Chebyshev.eventually_primeCounting_le (ε := 1) one_pos)
  filter_upwards [h] with n hn
  simpa using hn

theorem pi_div_ge (M : ℕ) : ∀ᶠ N : ℕ in atTop, ∀ p ∈ P M,
    Real.log 2 / (4 * (Real.log 4 + 1)) * (Nat.primeCounting N : ℝ) / p ≤
      (Nat.primeCounting (N / p) : ℝ) := by
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  obtain ⟨n1, hn1⟩ := eventually_atTop.1 pi_lower
  filter_upwards [pi_upper, eventually_ge_atTop ((n1 + 2) * (M + 1))] with N hB hN
  intro p hp
  simp only [P, mem_filter, mem_range] at hp
  obtain ⟨hpM, hpp, hp3⟩ := hp
  have hn : n1 + 2 ≤ N / p := by
    rw [Nat.le_div_iff_mul_le hpp.pos]
    calc (n1 + 2) * p ≤ (n1 + 2) * (M + 1) := Nat.mul_le_mul_left _ (by omega)
      _ ≤ N := hN
  have hA := hn1 (N / p) (by omega)
  have hlt : N < p * (N / p + 1) := Nat.lt_mul_div_succ N hpp.pos
  have hle : N / p ≤ N := Nat.div_le_self N p
  have hpR : (0 : ℝ) < p := by exact_mod_cast hpp.pos
  have hnR : (2 : ℝ) ≤ ((N / p : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 ≤ N / p)
  have hleR : ((N / p : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hle
  have hltR : (N : ℝ) < p * (((N / p : ℕ) : ℝ) + 1) := by exact_mod_cast hlt
  have hlogn : 0 < Real.log ((N / p : ℕ) : ℝ) := Real.log_pos (by linarith)
  have hlogle : Real.log ((N / p : ℕ) : ℝ) ≤ Real.log (N : ℝ) :=
    Real.log_le_log (by linarith) hleR
  have hlogN : 0 < Real.log (N : ℝ) := lt_of_lt_of_le hlogn hlogle
  have hhalf : (N : ℝ) / (2 * p) ≤ ((N / p : ℕ) : ℝ) := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  calc Real.log 2 / (4 * (Real.log 4 + 1)) * (Nat.primeCounting N : ℝ) / p
      ≤ Real.log 2 / (4 * (Real.log 4 + 1)) * ((Real.log 4 + 1) * N / Real.log N) / p := by
        gcongr
    _ = Real.log 2 / 2 * ((N : ℝ) / (2 * p)) / Real.log N := by
        field_simp
        ring
    _ ≤ Real.log 2 / 2 * ((N / p : ℕ) : ℝ) / Real.log N := by
        gcongr
    _ ≤ Real.log 2 / 2 * ((N / p : ℕ) : ℝ) / Real.log ((N / p : ℕ) : ℝ) := by
        apply div_le_div_of_nonneg_left _ hlogn hlogle
        positivity
    _ ≤ (Nat.primeCounting (N / p) : ℝ) := hA

theorem recip_large (X : ℝ) : ∃ M : ℕ, X ≤ ∑ p ∈ P M, (1 : ℝ) / p := by
  have hdiv := (not_summable_iff_tendsto_nat_atTop_of_nonneg (f :=
    Set.indicator {p : ℕ | p.Prime} (fun n : ℕ => (1 : ℝ) / n)) (fun n => by
      apply Set.indicator_nonneg
      intro i _
      positivity)).1 not_summable_one_div_on_primes
  obtain ⟨M, hM⟩ := ((hdiv.comp (tendsto_add_atTop_nat 1)).eventually_ge_atTop (X + 1 / 2)).exists
  refine ⟨M, ?_⟩
  simp only [Function.comp_apply] at hM
  have hS : ∑ p ∈ P M, (1 : ℝ) / p =
      ∑ n ∈ range (M + 1), if (n.Prime ∧ 3 ≤ n) then (1 : ℝ) / n else 0 := by
    rw [P, Finset.sum_filter]
  have hT : ∑ n ∈ range (M + 1), (if n = 2 then (1 : ℝ) / 2 else 0) ≤ 1 / 2 := by
    rw [Finset.sum_ite_eq']
    split_ifs <;> norm_num
  have hle : ∑ n ∈ range (M + 1), Set.indicator {p : ℕ | p.Prime} (fun n : ℕ => (1 : ℝ) / n) n ≤
      ∑ n ∈ range (M + 1), ((if (n.Prime ∧ 3 ≤ n) then (1 : ℝ) / n else 0) +
        (if n = 2 then (1 : ℝ) / 2 else 0)) := by
    apply Finset.sum_le_sum
    intro n _
    by_cases hn : n.Prime
    · rw [Set.indicator_of_mem (by exact hn)]
      by_cases h2 : n = 2
      · subst h2
        norm_num
      · have h3 : 3 ≤ n := by
          have := hn.two_le
          omega
        rw [if_pos ⟨hn, h3⟩, if_neg h2]
        linarith
    · rw [Set.indicator_of_notMem (by exact hn)]
      rw [if_neg (fun h => hn h.1)]
      split_ifs <;> norm_num
  rw [Finset.sum_add_distrib] at hle
  linarith

theorem count_ge_mul (K : ℝ) : ∀ᶠ N : ℕ in atTop,
    1 ≤ Nat.primeCounting N ∧
      K * (Nat.primeCounting N : ℝ) ≤ (OMA.S_oeis_a369096.count N : ℝ) := by
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hd : 0 < Real.log 2 / (4 * (Real.log 4 + 1)) := by positivity
  obtain ⟨M, hM⟩ := recip_large ((K + 1) / (Real.log 2 / (4 * (Real.log 4 + 1))))
  rw [div_le_iff₀ hd] at hM
  filter_upwards [pi_div_ge M, Nat.tendsto_primeCounting.eventually_ge_atTop ((M + 1) * (M + 1))]
    with N hN hpi
  have hpi1 : 1 ≤ Nat.primeCounting N := le_trans (by nlinarith) hpi
  refine ⟨hpi1, ?_⟩
  have hpiR : (((M + 1) * (M + 1) : ℕ) : ℝ) ≤ (Nat.primeCounting N : ℝ) := by exact_mod_cast hpi
  have hpi0 : (0 : ℝ) ≤ (Nat.primeCounting N : ℝ) := by positivity
  have hcount : ((∑ p ∈ P M, (Nat.primeCounting (N / p) - (M + 1)) : ℕ) : ℝ) ≤
      (OMA.S_oeis_a369096.count N : ℝ) := by exact_mod_cast count_ge M N
  have hcard : ((P M).card : ℝ) ≤ (M : ℝ) + 1 := by
    have : (P M).card ≤ M + 1 := by
      calc (P M).card ≤ (range (M + 1)).card := Finset.card_le_card (Finset.filter_subset _ _)
        _ = M + 1 := card_range _
    exact_mod_cast this
  have hterm : ∀ p ∈ P M,
      Real.log 2 / (4 * (Real.log 4 + 1)) * (Nat.primeCounting N : ℝ) * ((1 : ℝ) / p)
        - ((M : ℝ) + 1) ≤ ((Nat.primeCounting (N / p) - (M + 1) : ℕ) : ℝ) := by
    intro p hp
    have h1 := hN p hp
    have h2 : Nat.primeCounting (N / p) ≤ (Nat.primeCounting (N / p) - (M + 1)) + (M + 1) := by
      omega
    have h3 : (Nat.primeCounting (N / p) : ℝ) ≤
        ((Nat.primeCounting (N / p) - (M + 1) : ℕ) : ℝ) + ((M : ℝ) + 1) := by exact_mod_cast h2
    have h4 : Real.log 2 / (4 * (Real.log 4 + 1)) * (Nat.primeCounting N : ℝ) * ((1 : ℝ) / p) =
        Real.log 2 / (4 * (Real.log 4 + 1)) * (Nat.primeCounting N : ℝ) / p := by ring
    rw [h4]
    linarith
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul] at hsum
  push_cast at hcount hpiR
  have hM' : (K + 1) * (Nat.primeCounting N : ℝ) ≤
      Real.log 2 / (4 * (Real.log 4 + 1)) * (Nat.primeCounting N : ℝ) *
        ∑ p ∈ P M, (1 : ℝ) / p := by
    have := mul_le_mul_of_nonneg_right hM hpi0
    linarith
  have hcm : ((P M).card : ℝ) * ((M : ℝ) + 1) ≤ ((M : ℝ) + 1) * ((M : ℝ) + 1) := by
    apply mul_le_mul_of_nonneg_right hcard
    positivity
  linarith

end OMA.A369096

theorem OMA.solution : type_of% @OMA.S_oeis_a369096.main := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 (OMA.A369096.count_ge_mul (2 / ε))
  refine ⟨N0, fun N hN => ?_⟩
  obtain ⟨hpi, hc⟩ := hN0 N hN
  have hpiR : (1 : ℝ) ≤ (Nat.primeCounting N : ℝ) := by exact_mod_cast hpi
  have hK : 0 < 2 / ε := by positivity
  have hcpos : 0 < (OMA.S_oeis_a369096.count N : ℝ) :=
    lt_of_lt_of_le (mul_pos hK (by linarith)) hc
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity), div_lt_iff₀ hcpos]
  have h1 : 2 / ε * (Nat.primeCounting N : ℝ) * ε = 2 * (Nat.primeCounting N : ℝ) := by
    field_simp
  have h2 := mul_le_mul_of_nonneg_right hc hε.le
  linarith
