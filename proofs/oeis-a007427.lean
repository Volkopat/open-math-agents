import OMAStatements.S_oeis_a007427

/-!
There is no sign cancellation in the convolution of two Möbius functions:
every nonzero summand has the Liouville sign of the argument. The
Dirichlet series of the absolute Möbius function has local factor
1 + p^(-s), which becomes the zeta factor at s after multiplying
by the zeta factor at 2s.
-/

namespace OMA.A007427

open ArithmeticFunction Finset Nat Complex OMA.S_oeis_a007427
open scoped ArithmeticFunction.Moebius

private def absMoebius (n : ℕ) : ℂ := ((|μ n| : ℤ) : ℂ)

private theorem transform_delta (n : ℕ) : moebiusTransform delta n = μ n := by
  classical
  by_cases hn : n = 0
  · simp [hn, moebiusTransform]
  · simp [moebiusTransform, delta, mul_ite, Nat.mem_divisors, hn]

private theorem moebius_signed (n : ℕ) : μ n = liouville n * |μ n| := by
  by_cases hn : Squarefree n
  · rw [abs_moebius_eq_one_of_squarefree hn, mul_one, moebius_apply_of_squarefree hn,
      liouville_apply hn.ne_zero]
  · simp [moebius_eq_zero_of_not_squarefree hn]

private theorem abs_coefficients : (fun n => ((|a n| : ℤ) : ℂ)) = LSeries.convolution absMoebius absMoebius := by
  funext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp [a, moebiusTransform]
  have ha : a n = liouville n * ∑ d ∈ n.divisors, |μ (n / d)| * |μ d| := by
    unfold a
    simp only [funext transform_delta]
    rw [moebiusTransform, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun d hd => ?_)
    have hsign := liouville_apply_mul (n / d) d
    rw [Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hd)] at hsign
    conv_lhs =>
      rw [moebius_signed (n / d), moebius_signed d]
    calc
      _ = (liouville (n / d) * liouville d) * (|μ (n / d)| * |μ d|) := by ring
      _ = _ := by rw [← hsign]
  have hl : |liouville n| = 1 := by
    rw [liouville_apply hn]
    simp
  rw [ha, abs_mul, hl, one_mul, abs_of_nonneg, Int.cast_sum, LSeries.convolution_def]
  · change _ = ∑ q ∈ n.divisorsAntidiagonal, absMoebius q.1 * absMoebius q.2
    rw [Nat.sum_divisorsAntidiagonal' (fun d e => absMoebius d * absMoebius e)]
    simp only [absMoebius, Int.cast_mul]
  · exact sum_nonneg (fun _ _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))

private theorem sf_summable {s : ℂ} (hs : 1 < s.re) : LSeriesSummable absMoebius s :=
  LSeriesSummable_of_bounded_of_one_lt_re (m := 1) (fun n _ => by
    rw [absMoebius, Complex.norm_intCast, ← Int.cast_abs, abs_abs]
    exact_mod_cast (abs_moebius_le_one (n := n))) hs

private theorem sf_term {s : ℂ} (hs : 1 < s.re) (n : ℕ) :
    LSeries.term absMoebius s n = absMoebius n * riemannZetaSummandHom (ne_zero_of_one_lt_re hs) n := by
  rw [LSeries.term_of_ne_zero' (ne_zero_of_one_lt_re hs)]
  change _ = absMoebius n * (n : ℂ) ^ (-s)
  rw [Complex.cpow_neg, div_eq_mul_inv]

private theorem local_factor {s : ℂ} (hs : 1 < s.re) (p : Nat.Primes) :
    (∑' e : ℕ, LSeries.term absMoebius s ((p : ℕ) ^ e)) = 1 + (p : ℂ) ^ (-s) := by
  rw [tsum_eq_sum (s := Finset.range 2)]
  · simp [Finset.sum_range_succ, sf_term hs, absMoebius, riemannZetaSummandHom,
      moebius_apply_prime p.property]
  · intro e he
    have he' : 2 ≤ e := le_of_not_gt (fun h => he (Finset.mem_range.mpr h))
    rw [sf_term hs, absMoebius, moebius_apply_prime_pow p.property (by omega),
      if_neg (by omega)]
    simp

private theorem squarefreeProduct {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes => 1 + (p : ℂ) ^ (-s)) (LSeries absMoebius s) := by
  have hm {m n : ℕ} (h : m.Coprime n) :
      LSeries.term absMoebius s (m * n) = LSeries.term absMoebius s m * LSeries.term absMoebius s n := by
    simp only [sf_term hs, absMoebius, isMultiplicative_moebius.map_mul_of_coprime h, abs_mul,
      Int.cast_mul, map_mul]
    ring
  have h1 : LSeries.term absMoebius s 1 = 1 := by
    simp [absMoebius]
  exact (EulerProduct.eulerProduct_hasProd h1 hm (sf_summable hs).norm
    (LSeries.term_zero _ _)).congr_fun (fun p => (local_factor hs p).symm)

private theorem sf_value {s : ℂ} (hs : 1 < s.re) :
    LSeries absMoebius s = riemannZeta s / riemannZeta (2 * s) := by
  have h2s : 1 < (2 * s).re := by
    simp [Complex.mul_re]
    linarith
  have hm := (squarefreeProduct hs).mul (riemannZeta_eulerProduct_hasProd h2s)
  have hprod : HasProd (fun p : Nat.Primes => (1 - (p : ℂ) ^ (-s))⁻¹)
      (LSeries absMoebius s * riemannZeta (2 * s)) := by
    apply hm.congr_fun
    intro p
    have ha := Complex.one_sub_prime_cpow_ne_zero p.property hs
    have hb := Complex.one_sub_prime_cpow_ne_zero p.property h2s
    have he : (p : ℂ) ^ (-(2 * s)) = ((p : ℂ) ^ (-s)) ^ (2 : ℕ) := by
      rw [show -(2 * s) = (2 : ℂ) * (-s) by ring]
      exact Complex.cpow_nat_mul (p : ℂ) 2 (-s)
    change (1 - (p : ℂ) ^ (-s))⁻¹ =
      (1 + (p : ℂ) ^ (-s)) * (1 - (p : ℂ) ^ (-(2 * s)))⁻¹
    rw [he] at hb ⊢
    field_simp
    ring
  exact (eq_div_iff (riemannZeta_ne_zero_of_one_lt_re h2s)).mpr
    (hprod.unique (riemannZeta_eulerProduct_hasProd hs))

theorem solution : type_of% @OMA.S_oeis_a007427.main := by
  intro s hs
  rw [abs_coefficients]
  have hc := (sf_summable hs).LSeriesHasSum.convolution (sf_summable hs).LSeriesHasSum
  refine ⟨hc.LSeriesSummable, ?_⟩
  rw [hc.LSeries_eq, sf_value hs, ← pow_two, div_pow]

end OMA.A007427

theorem OMA.solution : type_of% @OMA.S_oeis_a007427.main := OMA.A007427.solution
