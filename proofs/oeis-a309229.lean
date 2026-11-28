import OMAStatements.S_oeis_a309229
import Mathlib

namespace OMA.A309229Proof

open OMA.S_oeis_a309229

/-- Sum of the Moebius function over the divisors: `[m = 1]`. -/
theorem sum_mu (m : ℕ) :
    ∑ d ∈ m.divisors, (ArithmeticFunction.moebius d : ℤ) = if m = 1 then 1 else 0 := by
  have h : (ArithmeticFunction.moebius * (ArithmeticFunction.zeta : ArithmeticFunction ℤ)) m =
      (1 : ArithmeticFunction ℤ) m := by
    rw [ArithmeticFunction.moebius_mul_coe_zeta]
  rwa [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h

/-- For `m ∣ N`: `Sum_{k=1..N} g(gcd(m,k)) = N * Sum_{d ∣ m} μ(d)`. -/
theorem key (m N : ℕ) (hm : m ≠ 0) (hmN : m ∣ N) :
    ∑ k ∈ Finset.Icc 1 N, g (Nat.gcd m k) =
      (N : ℤ) * ∑ d ∈ m.divisors, (ArithmeticFunction.moebius d : ℤ) := by
  have h1 : ∀ k, g (Nat.gcd m k) =
      ∑ d ∈ m.divisors, if d ∣ k then (ArithmeticFunction.moebius d : ℤ) * d else 0 := by
    intro k
    unfold g
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext d
    simp only [Nat.mem_divisors, Finset.mem_filter, Nat.dvd_gcd_iff, ne_eq, Nat.gcd_eq_zero_iff]
    tauto
  rw [Finset.sum_congr rfl (fun k _ => h1 k), Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  have hdN : d ∣ N := (Nat.dvd_of_mem_divisors hd).trans hmN
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hI : Finset.Icc 1 N = Finset.Ioc 0 N := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [hI, Nat.Ioc_filter_dvd_card_eq_div]
  have hc : ((N / d : ℕ) : ℤ) * (d : ℤ) = N := by
    rw [← Nat.cast_mul, Nat.div_mul_cancel hdN]
  rw [← hc]
  ring

theorem T_zero (n : ℕ) : T 0 n = 0 := by
  simp [T, Finset.Icc_eq_empty_of_lt]

theorem T_succ (i n : ℕ) : T (i + 1) n = T i n + g (Nat.gcd (i + 1) n) := by
  unfold T A191898
  rw [Finset.sum_Icc_succ_top (show 1 ≤ i + 1 by omega)]

/-- Period sum: `T(n, n) = 0` for `n > 1`. -/
theorem T_self (n : ℕ) (hn : 1 < n) : T n n = 0 := by
  have h := key n n (by omega) (dvd_refl n)
  rw [sum_mu, if_neg (show n ≠ 1 by omega), mul_zero] at h
  unfold T A191898
  rw [← h]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Nat.gcd_comm]

theorem T_pred (n : ℕ) (hn : 1 < n) : T (n - 1) n = -g n := by
  have h := T_succ (n - 1) n
  rw [show n - 1 + 1 = n by omega, T_self n hn, Nat.gcd_self] at h
  linarith

/-- Reflection: `T(i, n) + T(n-1-i, n) = -g(n)` for `i ≤ n - 1`. -/
theorem T_reflect (n : ℕ) (hn : 1 < n) : ∀ i, i ≤ n - 1 → T i n + T (n - 1 - i) n = -g n := by
  intro i
  induction i with
  | zero =>
    intro _
    rw [Nat.sub_zero, T_zero, T_pred n hn, zero_add]
  | succ i ih =>
    intro hi
    have h1 := T_succ i n
    have ha : n - 1 - i = (n - 1 - (i + 1)) + 1 := by omega
    have h2 := T_succ (n - 1 - (i + 1)) n
    rw [← ha] at h2
    have hc : Nat.gcd (n - 1 - i) n = Nat.gcd (i + 1) n := by
      rw [show n - 1 - i = n - (i + 1) by omega, Nat.gcd_self_sub_left (show i + 1 ≤ n by omega)]
    rw [hc] at h2
    have h3 := ih (by omega)
    linarith

theorem conj1 (n : ℕ) (hn : 1 < n) :
    (Finset.Icc 1 n).sup' (Finset.nonempty_Icc.mpr hn.le) (fun i => T i n) +
      (Finset.Icc 1 n).inf' (Finset.nonempty_Icc.mpr hn.le) (fun i => T i n) = -g n := by
  have hpair : ∀ i ∈ Finset.Icc 1 n, ∃ j ∈ Finset.Icc 1 n, T j n = -g n - T i n := by
    intro i hi
    rw [Finset.mem_Icc] at hi
    rcases (show i = n ∨ i = n - 1 ∨ i < n - 1 by omega) with h | h | h
    · refine ⟨n - 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
      rw [h]
      linarith [T_self n hn, T_pred n hn]
    · refine ⟨n, Finset.mem_Icc.mpr ⟨by omega, le_refl n⟩, ?_⟩
      rw [h]
      linarith [T_self n hn, T_pred n hn]
    · refine ⟨n - 1 - i, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
      have := T_reflect n hn i (by omega)
      linarith
  obtain ⟨i0, hi0, hM⟩ :=
    Finset.exists_mem_eq_sup' (Finset.nonempty_Icc.mpr hn.le) (fun i => T i n)
  obtain ⟨i1, hi1, hm⟩ :=
    Finset.exists_mem_eq_inf' (Finset.nonempty_Icc.mpr hn.le) (fun i => T i n)
  obtain ⟨j0, hj0, hj0e⟩ := hpair i0 hi0
  obtain ⟨j1, hj1, hj1e⟩ := hpair i1 hi1
  have e1 : (Finset.Icc 1 n).inf' (Finset.nonempty_Icc.mpr hn.le) (fun i => T i n) ≤ T j0 n :=
    Finset.inf'_le (fun i => T i n) hj0
  have e2 : T j1 n ≤ (Finset.Icc 1 n).sup' (Finset.nonempty_Icc.mpr hn.le) (fun i => T i n) :=
    Finset.le_sup' (fun i => T i n) hj1
  have hM' : (Finset.Icc 1 n).sup' (Finset.nonempty_Icc.mpr hn.le) (fun i => T i n) = T i0 n := hM
  have hm' : (Finset.Icc 1 n).inf' (Finset.nonempty_Icc.mpr hn.le) (fun i => T i n) = T i1 n := hm
  linarith

theorem sum_Icc_eq_range (f : ℕ → ℤ) (m : ℕ) :
    ∑ i ∈ Finset.Icc 1 m, f i + f 0 = ∑ i ∈ Finset.range (m + 1), f i := by
  induction m with
  | zero => simp [Finset.Icc_eq_empty_of_lt]
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (show 1 ≤ m + 1 by omega), Finset.sum_range_succ, ← ih]
    ring

/-- Column sum: `2 * Sum_{i=1..n} T(i, n) = -n g(n)` for `n > 1`. -/
theorem sum_col (n : ℕ) (hn : 1 < n) : 2 * ∑ i ∈ Finset.Icc 1 n, T i n = -((n : ℤ) * g n) := by
  have h1 := sum_Icc_eq_range (fun i => T i n) n
  rw [Finset.sum_range_succ, T_zero, T_self n hn] at h1
  have h2 : ∑ i ∈ Finset.Icc 1 n, T i n = ∑ i ∈ Finset.range n, T i n := by linarith
  have h3 : ∑ i ∈ Finset.range n, T (n - 1 - i) n = ∑ i ∈ Finset.range n, T i n :=
    Finset.sum_range_reflect (fun i => T i n) n
  calc 2 * ∑ i ∈ Finset.Icc 1 n, T i n
      = ∑ i ∈ Finset.range n, T i n + ∑ i ∈ Finset.range n, T (n - 1 - i) n := by
        rw [h2, h3]; ring
    _ = ∑ i ∈ Finset.range n, (T i n + T (n - 1 - i) n) := by rw [Finset.sum_add_distrib]
    _ = ∑ _i ∈ Finset.range n, (-g n) := by
        refine Finset.sum_congr rfl (fun i hi => ?_)
        rw [Finset.mem_range] at hi
        exact T_reflect n hn i (by omega)
    _ = -((n : ℤ) * g n) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring

theorem mean_part (n : ℕ) (hn : 1 < n) :
    2 * ((∑ i ∈ Finset.Icc 1 n, T i n : ℚ) / n) = -g n := by
  have hZ := sum_col n hn
  have hQ : 2 * (∑ i ∈ Finset.Icc 1 n, T i n : ℚ) = -((n : ℚ) * (g n : ℚ)) := by
    exact_mod_cast hZ
  have hn0 : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [← mul_div_assoc, hQ, neg_div, mul_div_cancel_left₀ _ hn0]

/-- Row sum over a full period: `Sum_{k=1..n!} T(n, k) = n!` for `n ≥ 1`. -/
theorem conj2_int (n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ Finset.Icc 1 n.factorial, T n k = (n.factorial : ℤ) := by
  unfold T A191898
  rw [Finset.sum_comm, Finset.sum_eq_single 1]
  · rw [key 1 n.factorial one_ne_zero (one_dvd _), sum_mu, if_pos rfl, mul_one]
  · intro i hi hi1
    rw [Finset.mem_Icc] at hi
    rw [key i n.factorial (by omega) (Nat.dvd_factorial (by omega) hi.2), sum_mu, if_neg hi1,
      mul_zero]
  · intro h
    exact absurd (Finset.mem_Icc.mpr ⟨le_refl 1, hn⟩) h

theorem conj2 (n : ℕ) (hn : 1 ≤ n) :
    (∑ k ∈ Finset.Icc 1 n.factorial, T n k : ℚ) / n.factorial = 1 := by
  have h : (∑ k ∈ Finset.Icc 1 n.factorial, T n k : ℚ) = (n.factorial : ℚ) := by
    exact_mod_cast conj2_int n hn
  rw [h]
  exact div_self (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))

end OMA.A309229Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a309229.main := by
  exact ⟨fun n hn => ⟨OMA.A309229Proof.conj1 n hn, OMA.A309229Proof.mean_part n hn⟩,
    fun n hn => OMA.A309229Proof.conj2 n hn⟩
