import FormalConjectures.Wikipedia.HardyLittlewood
import Mathlib.NumberTheory.Chebyshev

/-!
# Reduction R2: First Hardy–Littlewood conjecture via von Mangoldt correlations

This reduction splits `HardyLittlewood.first_hardy_littlewood_conjecture` into two standard
analytic number theory statements:
- `H1`: the Prime Number Theorem in Chebyshev `ψ` form (`k = 0`),
  `(∑ n ∈ Finset.Ioc 0 N, Λ n) / N → 1`.
- `H2`: the Hardy–Littlewood von Mangoldt correlation conjecture for all admissible injective
  even `(k + 2)`-tuples (`k ≥ 0`),
  `(∑ n ∈ Finset.Ioc 0 N, ∏ i, Λ (n + m i)) / N → C_m`.

Everything else is proved unconditionally inside this file:
1. The locally obstructed case (both sides vanish).
2. Convergence and strict positivity of the singular series `C_m > 0` for all admissible
   injective tuples (adapting @senamakel and @hoodbroskillson).
3. The general `k`-tuple higher-prime-power error bound `O_m(√(N+H) (log(N+H))^(k+1)) = o(N)`.
4. Replacement of `∏ i, log (n + m i)` by `(log n)^(k + 1)`.
5. General discrete Abel summation from `∑ a_n (log n)^d ~ C N` to
   `∑ a_n ~ C N / (log N)^d`.
6. The logarithmic integral asymptotic `∫ t in 2..N, 1 / (log t)^d ~ N / (log N)^d`.
-/

namespace OMA.R_HardyLittlewood_first_hardy_littlewood_conjecture_R2

open HardyLittlewood Filter Asymptotics Finset ArithmeticFunction
open scoped Topology

/-- The Prime Number Theorem in Chebyshev `ψ` form (`k = 0` case). -/
def H1 : Prop :=
  Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.Ioc 0 N, ArithmeticFunction.vonMangoldt n) / (N : ℝ))
    atTop (𝓝 1)

/-- The Hardy–Littlewood von Mangoldt correlation conjecture for all admissible injective even
tuples with at least one positive shift (`k + 2` entries). -/
def H2 : Prop :=
  ∀ {k : ℕ} (m : Fin (k + 2) → ℕ), m 0 = 0 → (∀ i ≠ 0, Even (m i)) →
    Function.Injective m →
    (∀ q : {q : ℕ // q.Prime ∧ 3 ≤ q}, ¬ Function.Surjective (fun i => (m i : ZMod q))) →
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.Ioc 0 N, ∏ i : Fin (k + 2), ArithmeticFunction.vonMangoldt (n + m i)) /
        (N : ℝ))
      atTop (𝓝 (2 ^ (k + 1) * ∏' (q : {q : ℕ // q.Prime ∧ 3 ≤ q}),
        (1 - (Nat.numResidues q m : ℝ) / q) / (1 - 1 / q) ^ (k + 2)))

/- ### Part 1: Singular series convergence, positivity, and local obstruction -/

lemma factor_sub_one_le (n : ℕ) (x : ℝ) (hx0 : 0 < x) (hx1' : x ≤ 1)
    (hx1 : (n : ℝ) * x ≤ 1 / 2) :
    |(1 - n * x) / (1 - x) ^ n - 1| ≤ 2 * (n : ℝ) ^ 2 * x ^ 2 := by
  have hnx : 0 ≤ (n : ℝ) * x := mul_nonneg (Nat.cast_nonneg n) hx0.le
  obtain ⟨P, hP⟩ : ∃ P : ℝ, P = (1 - x) ^ n := ⟨_, rfl⟩
  rw [← hP]
  have hlow : 1 - n * x ≤ P := by
    have h := one_add_mul_le_pow (a := -x) (by linarith) n
    rw [← sub_eq_add_neg, ← hP] at h
    linarith
  have hup : P ≤ 1 - n * x + (n * x) ^ 2 := by
    have h1 : P ≤ Real.exp (-x) ^ n := by
      rw [hP]
      exact pow_le_pow_left₀ (by linarith) (Real.one_sub_le_exp_neg x) n
    have h2 : Real.exp (-x) ^ n = Real.exp (-(n * x)) := by
      rw [← Real.exp_nat_mul]; congr 1; ring
    have h3 := Real.abs_exp_sub_one_sub_id_le (x := -(n * x))
      (by rw [abs_neg, abs_of_nonneg hnx]; linarith)
    have h4 := (abs_le.mp h3).2
    rw [neg_sq] at h4
    linarith
  have hP0 : 0 < P := by linarith
  rw [div_sub_one hP0.ne', abs_div, abs_of_pos hP0, div_le_iff₀ hP0,
    abs_of_nonpos (by linarith)]
  nlinarith [mul_nonneg (mul_nonneg (sq_nonneg (n : ℝ)) (sq_nonneg x))
    (by linarith : (0 : ℝ) ≤ 2 * P - 1)]

lemma factor_sub_one_le' (n : ℕ) (q : ℝ) (hq : 2 * (n : ℝ) ≤ q) (hq1 : 1 ≤ q) :
    |(1 - (n : ℝ) / q) / (1 - 1 / q) ^ n - 1| ≤ 2 * (n : ℝ) ^ 2 * (1 / q ^ 2) := by
  have hq0 : 0 < q := by linarith
  have h := factor_sub_one_le n (1 / q) (by positivity) (by rw [div_le_one hq0]; exact hq1)
    (by rw [mul_one_div, div_le_iff₀ hq0]; linarith)
  rwa [mul_one_div, one_div_pow] at h

lemma positive_product {k : ℕ} (t : Fin k.succ → ℕ) (B : ℕ)
    (hlt : ∀ q : {q : ℕ // q.Prime ∧ 3 ≤ q}, Nat.numResidues q t < q)
    (heq : ∀ q : ℕ, B < q → Nat.numResidues q t = k.succ) :
    0 < ∏' (q : {q : ℕ // q.Prime ∧ 3 ≤ q}),
        (1 - (Nat.numResidues q t : ℝ) / q) / (1 - 1 / q) ^ k.succ := by
  set f : {q : ℕ // q.Prime ∧ 3 ≤ q} → ℝ :=
    fun q => (1 - (Nat.numResidues q t : ℝ) / q) / (1 - 1 / q) ^ k.succ with hf
  have hpos : ∀ q, 0 < f q := by
    intro q
    have hq3 : (3 : ℝ) ≤ (q : ℕ) := by exact_mod_cast q.2.2
    have hl : (Nat.numResidues q t : ℝ) < (q : ℕ) := by exact_mod_cast hlt q
    apply div_pos
    · rw [sub_pos, div_lt_one (by linarith)]; exact hl
    · apply pow_pos
      rw [sub_pos, div_lt_one (by linarith)]; linarith
  have hg : Summable fun q => f q - 1 := by
    have hs : Summable fun q : {q : ℕ // q.Prime ∧ 3 ≤ q} =>
        2 * ((k.succ : ℕ) : ℝ) ^ 2 * (1 / ((q : ℕ) : ℝ) ^ 2) :=
      ((Real.summable_one_div_nat_pow.mpr one_lt_two).comp_injective
        Subtype.val_injective).mul_left _
    refine hs.of_norm_bounded_eventually ?_
    rw [Filter.eventually_cofinite]
    refine ((Set.finite_Iic (B + 2 * k.succ)).preimage Subtype.val_injective.injOn).subset ?_
    intro q hq
    simp only [Set.mem_preimage, Set.mem_Iic]
    by_contra hbig
    apply hq
    have hbig' : B + 2 * k.succ < (q : ℕ) := by omega
    have hq' : 2 * ((k.succ : ℕ) : ℝ) ≤ ((q : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 2 * k.succ ≤ (q : ℕ))
    have hq1 : (1 : ℝ) ≤ ((q : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ (q : ℕ))
    rw [Real.norm_eq_abs, hf]
    dsimp only
    rw [heq _ (by omega)]
    exact factor_sub_one_le' k.succ _ hq' hq1
  have hlog : Summable fun q => Real.log (f q) :=
    (Real.summable_log_one_add_of_summable hg).congr fun q => by rw [add_sub_cancel]
  rw [← Real.rexp_tsum_eq_tprod hpos hlog]
  exact Real.exp_pos _

lemma singular_series_pos {k : ℕ} (m : Fin k.succ → ℕ)
    (hinj : Function.Injective m)
    (hlocal : ∀ q : {q : ℕ // q.Prime ∧ 3 ≤ q},
      ¬ Function.Surjective (fun i => (m i : ZMod q))) :
    0 < (2 : ℝ) ^ k * ∏' (q : {q : ℕ // q.Prime ∧ 3 ≤ q}),
      (1 - (Nat.numResidues q m : ℝ) / q) / (1 - 1 / q) ^ k.succ := by
  classical
  apply mul_pos (by positivity)
  let B := Finset.univ.sup m
  apply positive_product m B
  · intro q
    have : NeZero (q : ℕ) := ⟨q.property.1.ne_zero⟩
    unfold HardyLittlewood.Nat.numResidues
    calc
      _ < Nat.card (ZMod (q : ℕ)) := Set.ncard_lt_card (fun h => hlocal q (Set.range_eq_univ.mp h))
      _ = (q : ℕ) := Nat.card_zmod _
  · intro q hq
    have hsmall (i) : m i < q := (Finset.le_sup (f := m) (Finset.mem_univ i)).trans_lt hq
    have hj : Function.Injective (fun i => (m i : ZMod q)) := by
      intro i j he
      have h := (ZMod.natCast_eq_natCast_iff' _ _ _).mp he
      rw [Nat.mod_eq_of_lt (hsmall i), Nat.mod_eq_of_lt (hsmall j)] at h
      exact hinj h
    unfold HardyLittlewood.Nat.numResidues
    rw [Set.ncard_range_of_injective hj]
    simp

lemma obstructed {k : ℕ} (m : Fin k.succ → ℕ) (q : {q : ℕ // q.Prime ∧ 3 ≤ q})
    (hs : Function.Surjective (fun i => (m i : ZMod q))) :
    FirstHardyLittlewoodConjectureFor m := by
  classical
  intro _ _ _
  have hcount (n : ℕ) : Nat.primeTupleCounting m n = 0 := by
    unfold Nat.primeTupleCounting
    rw [Nat.count_eq_card_filter_range, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro p _ hp
    apply hp.2 q q.property.1
    intro z
    obtain ⟨i, hi⟩ := hs (z - (p : ZMod q))
    exact ⟨i, by dsimp at hi ⊢; rw [hi]; exact add_sub_cancel (p : ZMod q) z⟩
  have hnum : Nat.numResidues q m = q := by
    unfold Nat.numResidues
    rw [Set.range_eq_univ.mpr hs, Set.ncard_univ, Nat.card_zmod]
  have hq : ((q : ℕ) : ℝ) ≠ 0 := by exact_mod_cast q.property.1.ne_zero
  have hprod : (∏' p : {p : ℕ // p.Prime ∧ 3 ≤ p},
      (1 - (Nat.numResidues p m : ℝ) / p) / (1 - 1 / p) ^ k.succ) = 0 := by
    apply (hasProd_zero_of_exists_eq_zero _).tprod_eq
    exact ⟨q, by simp [hnum, hq]⟩
  simp only [hcount, Nat.cast_zero, hprod, mul_zero, zero_mul]
  exact IsEquivalent.refl

lemma k0_singular_series (m : Fin 1 → ℕ) :
    (2 : ℝ) ^ 0 * ∏' (q : {q : ℕ // q.Prime ∧ 3 ≤ q}),
      (1 - (Nat.numResidues q m : ℝ) / q) / (1 - 1 / q) ^ (0 : ℕ).succ = 1 := by
  have h1 : ∀ q : {q : ℕ // q.Prime ∧ 3 ≤ q},
      (1 - (Nat.numResidues q m : ℝ) / q) / (1 - 1 / q) ^ (0 : ℕ).succ = 1 := by
    intro q
    have hnum : Nat.numResidues q m = 1 := by
      unfold Nat.numResidues
      rw [Set.ncard_range_of_injective (Function.injective_of_subsingleton _)]
      simp
    have hq3 : (3 : ℝ) ≤ (q : ℕ) := by exact_mod_cast q.2.2
    have hne : (1 : ℝ) - 1 / (q : ℕ) ≠ 0 := by
      have : (1 : ℝ) / (q : ℕ) < 1 := by rw [div_lt_one (by linarith)]; linarith
      linarith
    rw [hnum, Nat.cast_one, pow_one, div_self hne]
  rw [show (∏' (q : {q : ℕ // q.Prime ∧ 3 ≤ q}),
      (1 - (Nat.numResidues q m : ℝ) / q) / (1 - 1 / q) ^ (0 : ℕ).succ) =
      ∏' (_q : {q : ℕ // q.Prime ∧ 3 ≤ q}), (1 : ℝ) from tprod_congr h1,
    tprod_one, pow_zero, mul_one]

/- ### Part 2: General `k`-tuple prime-power error -/

lemma prod_le_excess_mul {k : ℕ} (f : Fin k.succ → ℕ) (L : ℝ) (hL : 0 ≤ L)
    (hup : ∀ i, vonMangoldt (f i) ≤ L) :
    0 ≤ (∏ i, vonMangoldt (f i)) -
        (if ∀ i, (f i).Prime then ∏ i, Real.log (f i : ℕ) else 0) ∧
    (∏ i, vonMangoldt (f i)) -
        (if ∀ i, (f i).Prime then ∏ i, Real.log (f i : ℕ) else 0) ≤
      (∑ i : Fin k.succ, if (f i).Prime then (0 : ℝ) else vonMangoldt (f i)) * L ^ k := by
  by_cases hp : ∀ i, (f i).Prime
  · have heq : (∏ i, vonMangoldt (f i)) = ∏ i, Real.log (f i : ℕ) := by
      apply Finset.prod_congr rfl
      intro i _
      exact vonMangoldt_apply_prime (hp i)
    simp [hp, heq]
  · simp only [hp, if_false, sub_zero]
    constructor
    · exact Finset.prod_nonneg fun i _ => vonMangoldt_nonneg
    · push Not at hp
      obtain ⟨j, hj⟩ := hp
      have hterm : ∏ i, vonMangoldt (f i) ≤ vonMangoldt (f j) * L ^ k := by
        rw [← Finset.mul_prod_erase Finset.univ (fun i => vonMangoldt (f i)) (Finset.mem_univ j)]
        apply mul_le_mul_of_nonneg_left _ vonMangoldt_nonneg
        calc
          ∏ i ∈ Finset.univ.erase j, vonMangoldt (f i)
              ≤ ∏ _i ∈ Finset.univ.erase j, L :=
            Finset.prod_le_prod (fun i _ => vonMangoldt_nonneg) (fun i _ => hup i)
          _ = L ^ k := by
            rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_fin]
            simp
      have hle_sum : vonMangoldt (f j) ≤
          ∑ i : Fin k.succ, if (f i).Prime then (0 : ℝ) else vonMangoldt (f i) := by
        have := Finset.single_le_sum
          (f := fun i : Fin k.succ => if (f i).Prime then (0 : ℝ) else vonMangoldt (f i))
          (fun i _ => by split <;> positivity) (Finset.mem_univ j)
        simpa [hj] using this
      exact hterm.trans (mul_le_mul_of_nonneg_right hle_sum (pow_nonneg hL k))

lemma sum_excess_shift (N h H : ℕ) (hh : h ≤ H) :
    (∑ n ∈ Ioc 0 N, if (n + h).Prime then (0 : ℝ) else vonMangoldt (n + h)) ≤
      Chebyshev.psi (N + H : ℕ) - Chebyshev.theta (N + H : ℕ) := by
  classical
  rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, Nat.floor_natCast, sum_filter]
  calc
    (∑ n ∈ Ioc 0 N, if (n + h).Prime then (0 : ℝ) else vonMangoldt (n + h))
        = ∑ j ∈ (Ioc 0 N).image (fun n => n + h),
            if j.Prime then (0 : ℝ) else vonMangoldt j := by
          rw [sum_image]; intro i _ j _ hij; exact Nat.add_right_cancel hij
    _ ≤ ∑ j ∈ Ioc 0 (N + H), if j.Prime then (0 : ℝ) else vonMangoldt j := by
          apply sum_le_sum_of_subset_of_nonneg
          · intro j hj
            obtain ⟨n, hn, rfl⟩ := mem_image.mp hj
            simp only [mem_Ioc] at hn ⊢
            omega
          · intro j _ _; split <;> positivity
    _ = _ := by
          apply sum_congr rfl
          intro j _
          by_cases hjp : j.Prime <;> simp [hjp]

lemma vonMangoldt_tuple_error {k : ℕ} (m : Fin k.succ → ℕ) (H : ℕ)
    (hm : ∀ i, m i ≤ H) (N : ℕ) (hNH : 1 ≤ N + H) :
    |(∑ n ∈ Ioc 0 N, ∏ i, vonMangoldt (n + m i)) -
      (∑ n ∈ Ioc 0 N, if ∀ i, (n + m i).Prime then ∏ i, Real.log (n + m i : ℕ) else 0)| ≤
      2 * (k.succ : ℝ) * Real.sqrt (N + H : ℕ) * (Real.log (N + H : ℕ)) ^ k.succ := by
  let L := Real.log (N + H : ℕ)
  have hL : 0 ≤ L := Real.log_nonneg (by exact_mod_cast hNH)
  have hup (n : ℕ) (hn : n ∈ Ioc 0 N) (i : Fin k.succ) : vonMangoldt (n + m i) ≤ L := by
    have h0 := (mem_Ioc.mp hn).1
    have hN := (mem_Ioc.mp hn).2
    have hmi := hm i
    exact vonMangoldt_le_log.trans
      (Real.log_le_log (by exact_mod_cast (by omega : 0 < n + m i))
        (by exact_mod_cast (by omega : n + m i ≤ N + H)))
  rw [← sum_sub_distrib,
    abs_of_nonneg (sum_nonneg fun n hn => (prod_le_excess_mul (fun i => n + m i) L hL (hup n hn)).1)]
  calc
    _ ≤ ∑ n ∈ Ioc 0 N,
          (∑ i : Fin k.succ, if (n + m i).Prime then (0 : ℝ) else vonMangoldt (n + m i)) * L ^ k :=
      sum_le_sum fun n hn => (prod_le_excess_mul (fun i => n + m i) L hL (hup n hn)).2
    _ = (∑ i : Fin k.succ,
          ∑ n ∈ Ioc 0 N, if (n + m i).Prime then (0 : ℝ) else vonMangoldt (n + m i)) * L ^ k := by
      rw [← sum_mul, sum_comm]
    _ ≤ (∑ _i : Fin k.succ, (Chebyshev.psi (N + H : ℕ) - Chebyshev.theta (N + H : ℕ))) * L ^ k := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hL k)
      exact sum_le_sum fun i _ => sum_excess_shift N (m i) H (hm i)
    _ = (k.succ : ℝ) * (Chebyshev.psi (N + H : ℕ) - Chebyshev.theta (N + H : ℕ)) * L ^ k := by
      rw [sum_const, card_fin, nsmul_eq_mul]
    _ ≤ (k.succ : ℝ) * (2 * Real.sqrt (N + H : ℕ) * L) * L ^ k := by
      have hc := Chebyshev.psi_sub_theta_le (x := (N + H : ℕ)) (by exact_mod_cast hNH)
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg _)) (pow_nonneg hL k)
    _ = 2 * (k.succ : ℝ) * Real.sqrt (N + H : ℕ) * L ^ k.succ := by
      rw [pow_succ]; ring

lemma log_pow_div_sqrt_tendsto_zero (d : ℕ) :
    Tendsto (fun x : ℝ => Real.log x ^ d / Real.sqrt x) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_rpow_atTop (d : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  rw [Real.sqrt_eq_rpow, Real.rpow_natCast]

lemma vonMangoldt_tuple_error_tendsto_zero {k : ℕ} (m : Fin k.succ → ℕ) :
    Tendsto (fun N : ℕ =>
      ((∑ n ∈ Ioc 0 N, ∏ i, vonMangoldt (n + m i)) -
        (∑ n ∈ Ioc 0 N, if ∀ i, (n + m i).Prime then ∏ i, Real.log (n + m i : ℕ) else 0)) /
        (N : ℝ)) atTop (𝓝 0) := by
  let H := Finset.univ.sup m + 1
  have hm : ∀ i, m i ≤ H := fun i => (Finset.le_sup (f := m) (Finset.mem_univ i)).trans (Nat.le_succ _)
  have hH : 1 ≤ H := Nat.succ_le_succ (Nat.zero_le _)
  have ht : Tendsto (fun N : ℕ => ((N + H : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat H)
  have hsmall : Tendsto (fun N : ℕ =>
      ((∑ n ∈ Ioc 0 N, ∏ i, vonMangoldt (n + m i)) -
        (∑ n ∈ Ioc 0 N, if ∀ i, (n + m i).Prime then ∏ i, Real.log (n + m i : ℕ) else 0)) /
        ((N + H : ℕ) : ℝ)) atTop (𝓝 0) := by
    have hbound : Tendsto (fun N : ℕ =>
        2 * (k.succ : ℝ) * (Real.log ((N + H : ℕ) : ℝ) ^ k.succ / Real.sqrt ((N + H : ℕ) : ℝ)))
        atTop (𝓝 0) := by
      have h := ((log_pow_div_sqrt_tendsto_zero k.succ).comp ht).const_mul (2 * (k.succ : ℝ))
      rwa [mul_zero] at h
    apply squeeze_zero_norm' _ hbound
    filter_upwards with N
    have hpos : 0 < ((N + H : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < N + H)
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hpos]
    calc
      _ ≤ (2 * (k.succ : ℝ) * Real.sqrt (N + H : ℕ) * (Real.log (N + H : ℕ)) ^ k.succ) /
            ((N + H : ℕ) : ℝ) :=
        div_le_div_of_nonneg_right (vonMangoldt_tuple_error m H hm N (by omega)) hpos.le
      _ = 2 * (k.succ : ℝ) * ((Real.log (N + H : ℕ)) ^ k.succ / Real.sqrt (N + H : ℕ)) := by
        have hsq := Real.sq_sqrt hpos.le
        have hsp := (Real.sqrt_pos.mpr hpos).ne'
        field_simp
        rw [hsq]
        ring
  have hratio : Tendsto (fun N : ℕ => ((N + H : ℕ) : ℝ) / (N : ℝ)) atTop (𝓝 1) := by
    have h := (tendsto_const_nhds (x := (1 : ℝ)) (f := (atTop : Filter ℕ))).add
      ((tendsto_natCast_atTop_atTop (R := ℝ)).inv_tendsto_atTop.const_mul (H : ℝ))
    rw [mul_zero, add_zero] at h
    apply Tendsto.congr' _ h
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    simp only [Pi.inv_apply]
    push_cast
    field_simp
  have hmul := hsmall.mul hratio
  rw [zero_mul] at hmul
  apply Tendsto.congr' _ hmul
  filter_upwards with N
  have hNH : ((N + H : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (by omega : N + H ≠ 0)
  exact div_mul_div_cancel₀ hNH

/- ### Part 3: Replacing `∏ i, log (n + m i)` by `(log n)^(k + 1)` -/

lemma log_add_div_log_tendsto_one (c : ℕ) :
    Tendsto (fun n : ℕ => Real.log (n + c : ℕ) / Real.log (n : ℝ)) atTop (𝓝 1) := by
  have h1 : Tendsto (fun n : ℕ => Real.log (1 + (c : ℝ) / (n : ℝ)) / Real.log (n : ℝ))
      atTop (𝓝 0) := by
    have hnum : Tendsto (fun n : ℕ => Real.log (1 + (c : ℝ) / (n : ℝ))) atTop (𝓝 0) := by
      have h0 : Tendsto (fun n : ℕ => 1 + (c : ℝ) / (n : ℝ)) atTop (𝓝 1) := by
        have h := (tendsto_const_nhds (x := (1 : ℝ))).add
          ((tendsto_natCast_atTop_atTop (R := ℝ)).inv_tendsto_atTop.const_mul (c : ℝ))
        simpa [div_eq_mul_inv] using h
      have hc := (Real.continuousAt_log one_ne_zero).tendsto.comp h0
      rw [Real.log_one] at hc
      exact hc
    have hden : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    exact hnum.div_atTop hden
  have h2 := (tendsto_const_nhds (x := (1 : ℝ)) (f := (atTop : Filter ℕ))).add h1
  rw [add_zero] at h2
  apply Tendsto.congr' _ h2
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hlog0 : Real.log (n : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (by omega : 1 < n))).ne'
  have hpos : (0 : ℝ) < 1 + (c : ℝ) / (n : ℝ) := by positivity
  have hmul : ((n + c : ℕ) : ℝ) = (n : ℝ) * (1 + (c : ℝ) / (n : ℝ)) := by
    push_cast; field_simp
  rw [hmul, Real.log_mul hn0.ne' hpos.ne', add_div, div_self hlog0]

lemma weighted_to_log_pow {k : ℕ} (m : Fin k.succ → ℕ) (C : ℝ) (hC : 0 < C)
    (hW : Tendsto (fun N : ℕ =>
      (∑ n ∈ Ioc 0 N, if ∀ i, (n + m i).Prime then ∏ i, Real.log (n + m i : ℕ) else 0) /
        (N : ℝ)) atTop (𝓝 C)) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Icc 2 N, if ∀ i, (n + m i).Prime then (Real.log (n : ℝ)) ^ k.succ else 0) /
        (N : ℝ)) atTop (𝓝 C) := by
  have hprod_ratio : Tendsto (fun n : ℕ =>
      (∏ i : Fin k.succ, Real.log (n + m i : ℕ)) / (Real.log (n : ℝ)) ^ k.succ)
      atTop (𝓝 1) := by
    have h := tendsto_finsetProd (Finset.univ : Finset (Fin k.succ))
      fun i _ => log_add_div_log_tendsto_one (m i)
    refine (by simpa using h : Tendsto (fun n : ℕ =>
      ∏ i : Fin k.succ, (Real.log (n + m i : ℕ) / Real.log (n : ℝ))) atTop (𝓝 1)).congr' ?_
    filter_upwards with n
    rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_fin]
  have hW2 : Tendsto (fun N : ℕ =>
      (∑ n ∈ Icc 2 N, if ∀ i, (n + m i).Prime then ∏ i, Real.log (n + m i : ℕ) else 0) /
        (N : ℝ)) atTop (𝓝 C) := by
    let c1 : ℝ := if ∀ i, (1 + m i).Prime then ∏ i, Real.log (1 + m i : ℕ) else 0
    have hc1 : Tendsto (fun N : ℕ => c1 / (N : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    have hsub := hW.sub hc1
    rw [sub_zero] at hsub
    apply Tendsto.congr' _ hsub
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hsplit : Ioc 0 N = insert 1 (Icc 2 N) := by
      ext x; simp only [mem_Ioc, mem_insert, mem_Icc]; omega
    dsimp only [c1]
    rw [hsplit, sum_insert (by simp), add_div, add_sub_cancel_left]
  rw [Metric.tendsto_nhds]
  intro ε hε
  let δ : ℝ := min (ε / (4 * (C + 1))) (1 / 2)
  have hδ0 : 0 < δ := lt_min (by positivity) (by norm_num)
  have hδ1 : δ ≤ 1 / 2 := min_le_right _ _
  have hδC : δ * (C + 1) ≤ ε / 4 := by
    have h1 : δ ≤ ε / (4 * (C + 1)) := min_le_left _ _
    have h2 : 0 < 4 * (C + 1) := by positivity
    have := (le_div_iff₀ h2).mp h1
    linarith
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp (Metric.tendsto_nhds.mp hprod_ratio δ hδ0)
  let M := max N0 2
  let tailW : ℝ := ∑ n ∈ Icc 2 M,
    if ∀ i, (n + m i).Prime then ∏ i, Real.log (n + m i : ℕ) else 0
  let tailA : ℝ := ∑ n ∈ Icc 2 M,
    if ∀ i, (n + m i).Prime then (Real.log (n : ℝ)) ^ k.succ else 0
  have htailW : Tendsto (fun N : ℕ => tailW / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have htailA : Tendsto (fun N : ℕ => tailA / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop M,
    Metric.tendsto_nhds.mp hW2 (ε / 4) (by positivity),
    Metric.tendsto_nhds.mp htailW (ε / 4) (by positivity),
    Metric.tendsto_nhds.mp htailA (ε / 4) (by positivity)] with N hNM hWN hTW hTA
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hsplit : Icc 2 N = Icc 2 M ∪ Ioc M N := by
    ext x; simp only [mem_Icc, mem_union, mem_Ioc]; omega
  have hdisj : Disjoint (Icc 2 M) (Ioc M N) := by
    rw [Finset.disjoint_left]; intro x hx1 hx2
    simp only [mem_Icc, mem_Ioc] at hx1 hx2; omega
  set W := ∑ n ∈ Icc 2 N, if ∀ i, (n + m i).Prime then ∏ i, Real.log (n + m i : ℕ) else 0
  set A := ∑ n ∈ Icc 2 N, if ∀ i, (n + m i).Prime then (Real.log (n : ℝ)) ^ k.succ else 0
  have hA_le_W : A ≤ W := by
    apply sum_le_sum
    intro n hn
    have hn2 : 2 ≤ n := (mem_Icc.mp hn).1
    split_ifs with hp
    · have hlog_nn : 0 ≤ Real.log (n : ℝ) :=
        Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
      calc
        (Real.log (n : ℝ)) ^ k.succ = ∏ _i : Fin k.succ, Real.log (n : ℝ) := by
          rw [Finset.prod_const, Finset.card_fin]
        _ ≤ ∏ i : Fin k.succ, Real.log (n + m i : ℕ) := by
          apply Finset.prod_le_prod (fun _ _ => hlog_nn)
          intro i _
          exact Real.log_le_log (by exact_mod_cast (by omega : 0 < n))
            (by exact_mod_cast (by omega : n ≤ n + m i))
    · exact le_rfl
  have hW_tail_le : (∑ n ∈ Ioc M N,
      if ∀ i, (n + m i).Prime then ∏ i, Real.log (n + m i : ℕ) else 0) ≤
      (1 + δ) * (∑ n ∈ Ioc M N,
      if ∀ i, (n + m i).Prime then (Real.log (n : ℝ)) ^ k.succ else 0) := by
    rw [mul_sum]
    apply sum_le_sum
    intro n hn
    have hnM : M < n := (mem_Ioc.mp hn).1
    have hnN0 : N0 ≤ n := le_trans (le_max_left _ _) hnM.le
    have hn2 : 2 ≤ n := le_trans (le_max_right _ _) hnM.le
    have hlog_pos : 0 < (Real.log (n : ℝ)) ^ k.succ :=
      pow_pos (Real.log_pos (by exact_mod_cast (by omega : 1 < n))) _
    have hdist := hN0 n hnN0
    rw [Real.dist_eq, abs_lt] at hdist
    have hrat : (∏ i : Fin k.succ, Real.log (n + m i : ℕ)) ≤
        (1 + δ) * (Real.log (n : ℝ)) ^ k.succ := by
      have hlt : (∏ i : Fin k.succ, Real.log (n + m i : ℕ)) / (Real.log (n : ℝ)) ^ k.succ <
          1 + δ := by linarith [hdist.2]
      exact ((div_lt_iff₀ hlog_pos).mp hlt).le
    split_ifs with hp
    · exact hrat
    · simp
  have hW_eq : W = tailW + ∑ n ∈ Ioc M N,
      if ∀ i, (n + m i).Prime then ∏ i, Real.log (n + m i : ℕ) else 0 := by
    dsimp [W, tailW]; rw [hsplit, sum_union hdisj]
  have hA_eq : A = tailA + ∑ n ∈ Ioc M N,
      if ∀ i, (n + m i).Prime then (Real.log (n : ℝ)) ^ k.succ else 0 := by
    dsimp [A, tailA]; rw [hsplit, sum_union hdisj]
  have hA_nonneg : 0 ≤ A := sum_nonneg fun n hn => by
    split_ifs
    · exact pow_nonneg (Real.log_nonneg (by exact_mod_cast (by have := (mem_Icc.mp hn).1; omega : 1 ≤ n))) _
    · exact le_rfl
  have htailA_nonneg : 0 ≤ tailA := sum_nonneg fun n hn => by
    split_ifs
    · exact pow_nonneg (Real.log_nonneg (by exact_mod_cast (by have := (mem_Icc.mp hn).1; omega : 1 ≤ n))) _
    · exact le_rfl
  have hW_le_A : W ≤ tailW + (1 + δ) * A := by
    have h1 : W - tailW ≤ (1 + δ) * (A - tailA) := by
      rw [hW_eq, hA_eq]
      simpa only [add_sub_cancel_left] using hW_tail_le
    have h2 : (1 + δ) * (A - tailA) ≤ (1 + δ) * A := by nlinarith
    linarith
  rw [Real.dist_eq] at hWN hTW hTA ⊢
  rw [sub_zero] at hTW hTA
  have hWN' := abs_lt.mp hWN
  have hTW' := abs_lt.mp hTW
  have hAN_le_WN : A / (N : ℝ) ≤ W / (N : ℝ) := div_le_div_of_nonneg_right hA_le_W hNpos.le
  have hWN_le_AN : W / (N : ℝ) ≤ tailW / (N : ℝ) + (1 + δ) * (A / (N : ℝ)) := by
    have := div_le_div_of_nonneg_right hW_le_A hNpos.le
    simpa [add_div, mul_div_assoc] using this
  have hupper : A / (N : ℝ) < C + ε := by linarith
  have hlower : C - ε < A / (N : ℝ) := by
    have h1 : C - ε / 2 < (1 + δ) * (A / (N : ℝ)) := by linarith
    have h2 : δ * (A / (N : ℝ)) ≤ δ * (C + ε / 4) := by
      apply mul_le_mul_of_nonneg_left _ hδ0.le
      linarith
    have h3 : δ * (C + ε / 4) ≤ ε / 4 + ε / 8 := by
      have : δ * (C + 1) ≤ ε / 4 := hδC
      have : δ * (ε / 4) ≤ (1 / 2) * (ε / 4) := by nlinarith
      nlinarith
    linarith
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

/- ### Part 4: Discrete Abel summation and logarithmic integral asymptotic -/

lemma inv_log_pow_sub_le (d : ℕ) (hd : 1 ≤ d) (n : ℕ) (hn : 2 ≤ n) :
    0 ≤ 1 / (Real.log (n : ℝ)) ^ d - 1 / (Real.log ((n + 1 : ℕ) : ℝ)) ^ d ∧
    1 / (Real.log (n : ℝ)) ^ d - 1 / (Real.log ((n + 1 : ℕ) : ℝ)) ^ d ≤
      (d : ℝ) / ((n : ℝ) * (Real.log (n : ℝ)) ^ (d + 1)) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hlogn : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hlogn1 : Real.log (n : ℝ) ≤ Real.log ((n + 1 : ℕ) : ℝ) :=
    Real.log_le_log hn0 (by exact_mod_cast (by omega : n ≤ n + 1))
  have hlogn1_pos : 0 < Real.log ((n + 1 : ℕ) : ℝ) := lt_of_lt_of_le hlogn hlogn1
  constructor
  · rw [sub_nonneg]
    exact one_div_le_one_div_of_le (pow_pos hlogn d) (pow_le_pow_left₀ hlogn.le hlogn1 d)
  · have hlt : (n : ℝ) < ((n + 1 : ℕ) : ℝ) := by exact_mod_cast (Nat.lt_succ_self n)
    have hderiv : ∀ x ∈ Set.Icc (n : ℝ) ((n + 1 : ℕ) : ℝ),
        HasDerivAt (fun t : ℝ => (Real.log t) ^ (-(d : ℤ)))
          (-(d : ℝ) / (x * (Real.log x) ^ (d + 1))) x := by
      intro x hx
      have hx0 : 0 < x := lt_of_lt_of_le hn0 hx.1
      have hlogx : 0 < Real.log x :=
        lt_of_lt_of_le hlogn (Real.log_le_log hn0 hx.1)
      have h1 := (hasDerivAt_zpow (-(d : ℤ)) (Real.log x) (Or.inl hlogx.ne')).comp x
        (Real.hasDerivAt_log hx0.ne')
      have heq : ((-(d : ℤ) : ℤ) : ℝ) * (Real.log x) ^ (-(d : ℤ) - 1) * x⁻¹ =
          -(d : ℝ) / (x * (Real.log x) ^ (d + 1)) := by
        rw [Int.cast_neg, Int.cast_natCast, show -(d : ℤ) - 1 = -((d + 1 : ℕ) : ℤ) by omega,
          zpow_neg, zpow_natCast]
        field_simp
      rw [heq] at h1
      exact h1
    have hcont : ContinuousOn (fun t : ℝ => (Real.log t) ^ (-(d : ℤ)))
        (Set.Icc (n : ℝ) ((n + 1 : ℕ) : ℝ)) :=
      fun x hx => (hderiv x hx).continuousAt.continuousWithinAt
    obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope
      (fun t : ℝ => (Real.log t) ^ (-(d : ℤ)))
      (fun x => -(d : ℝ) / (x * (Real.log x) ^ (d + 1)))
      hlt hcont (fun x hx => hderiv x (Set.Ioo_subset_Icc_self hx))
    have hdiff_one : ((n + 1 : ℕ) : ℝ) - (n : ℝ) = 1 := by push_cast; ring
    rw [hdiff_one, div_one] at hslope
    have heq : 1 / (Real.log (n : ℝ)) ^ d - 1 / (Real.log ((n + 1 : ℕ) : ℝ)) ^ d =
        (d : ℝ) / (c * (Real.log c) ^ (d + 1)) := by
      have h1 : (Real.log (n : ℝ)) ^ (-(d : ℤ)) = 1 / (Real.log (n : ℝ)) ^ d := by
        rw [zpow_neg, zpow_natCast, one_div]
      have h2 : (Real.log ((n + 1 : ℕ) : ℝ)) ^ (-(d : ℤ)) =
          1 / (Real.log ((n + 1 : ℕ) : ℝ)) ^ d := by
        rw [zpow_neg, zpow_natCast, one_div]
      rw [h1, h2, neg_div] at hslope
      linarith
    rw [heq]
    have hc_ge : (n : ℝ) ≤ c := hc.1.le
    have hlogc_ge : Real.log (n : ℝ) ≤ Real.log c := Real.log_le_log hn0 hc_ge
    apply div_le_div_of_nonneg_left (Nat.cast_nonneg d) (mul_pos hn0 (pow_pos hlogn (d + 1)))
    exact mul_le_mul hc_ge (pow_le_pow_left₀ hlogn.le hlogc_ge (d + 1))
      (pow_nonneg hlogn.le (d + 1)) (lt_of_lt_of_le hn0 hc_ge).le

lemma sum_inv_log_pow_littleO (d : ℕ) (_hd : 1 ≤ d) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Icc 2 N, 1 / (Real.log (n : ℝ)) ^ (d + 1)) /
        ((N : ℝ) / (Real.log (N : ℝ)) ^ d)) atTop (𝓝 0) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have ht1 : Tendsto (fun N : ℕ =>
      (Real.log (N : ℝ)) ^ d / Real.sqrt (N : ℝ) * (1 / (Real.log 2) ^ (d + 1)))
      atTop (𝓝 0) := by
    have h := ((log_pow_div_sqrt_tendsto_zero d).comp tendsto_natCast_atTop_atTop).mul_const
      (1 / (Real.log 2) ^ (d + 1))
    rwa [zero_mul] at h
  have ht2 : Tendsto (fun N : ℕ => (2 : ℝ) ^ (d + 1) / Real.log (N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hadd := ht1.add ht2
  rw [add_zero] at hadd
  apply squeeze_zero_norm' _ hadd
  filter_upwards [eventually_ge_atTop 16] with N hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hden_pos : 0 < (N : ℝ) / (Real.log (N : ℝ)) ^ d := div_pos hNpos (pow_pos hlogN d)
  have hsum_nn : 0 ≤ ∑ n ∈ Icc 2 N, 1 / (Real.log (n : ℝ)) ^ (d + 1) :=
    sum_nonneg fun n hn => by
      have hn2 : 2 ≤ n := (mem_Icc.mp hn).1
      have : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
      positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hsum_nn hden_pos.le)]
  let M := Nat.sqrt N
  have hM2 : 2 ≤ M := by
    have : 4 ≤ M := Nat.le_sqrt.mpr (by omega)
    omega
  have hMN : M ≤ N := Nat.sqrt_le_self N
  have hsplit : Icc 2 N = Icc 2 M ∪ Ioc M N := by
    ext x; simp only [mem_Icc, mem_union, mem_Ioc]; omega
  have hdisj : Disjoint (Icc 2 M) (Ioc M N) := by
    rw [Finset.disjoint_left]; intro x hx1 hx2
    simp only [mem_Icc, mem_Ioc] at hx1 hx2; omega
  have hpart1 : ∑ n ∈ Icc 2 M, 1 / (Real.log (n : ℝ)) ^ (d + 1) ≤
      Real.sqrt (N : ℝ) * (1 / (Real.log 2) ^ (d + 1)) := by
    calc
      ∑ n ∈ Icc 2 M, 1 / (Real.log (n : ℝ)) ^ (d + 1)
          ≤ ∑ _n ∈ Icc 2 M, 1 / (Real.log 2) ^ (d + 1) := by
        apply sum_le_sum; intro n hn
        have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (mem_Icc.mp hn).1
        exact one_div_le_one_div_of_le (pow_pos hlog2 _)
          (pow_le_pow_left₀ hlog2.le (Real.log_le_log (by norm_num) hn2) _)
      _ = ((Icc 2 M).card : ℝ) * (1 / (Real.log 2) ^ (d + 1)) := by
        rw [sum_const, nsmul_eq_mul]
      _ ≤ Real.sqrt (N : ℝ) * (1 / (Real.log 2) ^ (d + 1)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        have hc : (Icc 2 M).card ≤ M := by rw [Nat.card_Icc]; omega
        have hMsq : ((M : ℝ)) ^ 2 ≤ (N : ℝ) := by
          have := Nat.sqrt_le N
          exact_mod_cast (by nlinarith : M ^ 2 ≤ N)
        have hMle : (M : ℝ) ≤ Real.sqrt (N : ℝ) :=
          (Real.le_sqrt (Nat.cast_nonneg M) hNpos.le).mpr hMsq
        exact le_trans (by exact_mod_cast hc) hMle
  have hpart2 : ∑ n ∈ Ioc M N, 1 / (Real.log (n : ℝ)) ^ (d + 1) ≤
      (N : ℝ) * ((2 : ℝ) ^ (d + 1) / (Real.log (N : ℝ)) ^ (d + 1)) := by
    have hlog_sqrt : Real.log (Real.sqrt (N : ℝ)) = Real.log (N : ℝ) / 2 := by
      rw [Real.log_sqrt hNpos.le]
    have hsqrt_pos : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNpos
    have hlog_sqrt_pos : 0 < Real.log (Real.sqrt (N : ℝ)) := by rw [hlog_sqrt]; positivity
    calc
      ∑ n ∈ Ioc M N, 1 / (Real.log (n : ℝ)) ^ (d + 1)
          ≤ ∑ _n ∈ Ioc M N, 1 / (Real.log (Real.sqrt (N : ℝ))) ^ (d + 1) := by
        apply sum_le_sum; intro n hn
        have hMn : M < n := (mem_Ioc.mp hn).1
        have hsq_lt : (N : ℝ) < ((n : ℝ)) ^ 2 := by
          have : N < (M + 1) ^ 2 := by
            have := Nat.lt_succ_sqrt N
            nlinarith
          have : N < n ^ 2 := lt_of_lt_of_le this (Nat.pow_le_pow_left (by omega) 2)
          exact_mod_cast this
        have hle : Real.sqrt (N : ℝ) ≤ (n : ℝ) :=
          (Real.sqrt_le_left (Nat.cast_nonneg n)).mpr hsq_lt.le
        exact one_div_le_one_div_of_le (pow_pos hlog_sqrt_pos _)
          (pow_le_pow_left₀ hlog_sqrt_pos.le (Real.log_le_log hsqrt_pos hle) _)
      _ = ((Ioc M N).card : ℝ) * (1 / (Real.log (N : ℝ) / 2) ^ (d + 1)) := by
        rw [sum_const, nsmul_eq_mul, hlog_sqrt]
      _ ≤ (N : ℝ) * ((2 : ℝ) ^ (d + 1) / (Real.log (N : ℝ)) ^ (d + 1)) := by
        have hc : ((Ioc M N).card : ℝ) ≤ (N : ℝ) := by
          rw [Nat.card_Ioc]; exact_mod_cast (by omega : N - M ≤ N)
        have heq : 1 / (Real.log (N : ℝ) / 2) ^ (d + 1) =
            (2 : ℝ) ^ (d + 1) / (Real.log (N : ℝ)) ^ (d + 1) := by
          rw [div_pow, one_div_div]
        rw [heq]
        exact mul_le_mul_of_nonneg_right hc (by positivity)
  have htot : ∑ n ∈ Icc 2 N, 1 / (Real.log (n : ℝ)) ^ (d + 1) ≤
      Real.sqrt (N : ℝ) * (1 / (Real.log 2) ^ (d + 1)) +
      (N : ℝ) * ((2 : ℝ) ^ (d + 1) / (Real.log (N : ℝ)) ^ (d + 1)) := by
    rw [hsplit, sum_union hdisj]; exact add_le_add hpart1 hpart2
  calc
    (∑ n ∈ Icc 2 N, 1 / (Real.log (n : ℝ)) ^ (d + 1)) / ((N : ℝ) / (Real.log (N : ℝ)) ^ d)
        ≤ (Real.sqrt (N : ℝ) * (1 / (Real.log 2) ^ (d + 1)) +
          (N : ℝ) * ((2 : ℝ) ^ (d + 1) / (Real.log (N : ℝ)) ^ (d + 1))) /
            ((N : ℝ) / (Real.log (N : ℝ)) ^ d) :=
      div_le_div_of_nonneg_right htot hden_pos.le
    _ = (Real.log (N : ℝ)) ^ d / Real.sqrt (N : ℝ) * (1 / (Real.log 2) ^ (d + 1)) +
        (2 : ℝ) ^ (d + 1) / Real.log (N : ℝ) := by
      have hsq : Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) = (N : ℝ) := Real.mul_self_sqrt hNpos.le
      have hsp := (Real.sqrt_pos.mpr hNpos).ne'
      have hlp := hlogN.ne'
      rw [add_div]
      congr 1
      · field_simp
        exact Real.sq_sqrt hNpos.le
      · field_simp
        exact (pow_succ _ _).symm

lemma abel_Icc2 (b f : ℕ → ℝ) (N : ℕ) (hN : 2 ≤ N) :
    ∑ n ∈ Icc 2 N, b n * f n =
      (∑ n ∈ Icc 2 N, b n) * f N +
      ∑ n ∈ Ico 2 N, (∑ j ∈ Icc 2 n, b j) * (f n - f (n + 1)) := by
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ N hN ih =>
    have hIcc : Icc 2 (N + 1) = insert (N + 1) (Icc 2 N) := by
      ext x; simp only [mem_Icc, mem_insert]; omega
    have hIco : Ico 2 (N + 1) = insert N (Ico 2 N) := by
      ext x; simp only [mem_Ico, mem_insert]; omega
    rw [hIcc, sum_insert (by simp), ih, sum_insert (by simp), hIco, sum_insert (by simp)]
    ring

lemma abel_unweight (a : ℕ → ℝ) (d : ℕ) (hd : 1 ≤ d) (C : ℝ)
    (ha : ∀ n, 0 ≤ a n)
    (hS : Tendsto (fun N : ℕ =>
      (∑ n ∈ Icc 2 N, a n * (Real.log (n : ℝ)) ^ d) / (N : ℝ)) atTop (𝓝 C)) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Icc 2 N, a n) / ((N : ℝ) / (Real.log (N : ℝ)) ^ d)) atTop (𝓝 C) := by
  have hS_bound : ∃ M : ℝ, 0 < M ∧ ∀ n : ℕ, 2 ≤ n →
      ∑ j ∈ Icc 2 n, a j * (Real.log (j : ℝ)) ^ d ≤ M * (n : ℝ) := by
    obtain ⟨N0, hN0⟩ := eventually_atTop.mp (Metric.tendsto_nhds.mp hS 1 one_pos)
    let N1 := max N0 2
    let M0 : ℝ := max (|C| + 1)
      ((Finset.Icc 2 N1).sup' ⟨2, by simp [N1]⟩ fun n =>
        (∑ j ∈ Icc 2 n, a j * (Real.log (j : ℝ)) ^ d) / (n : ℝ))
    refine ⟨max M0 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
    intro n hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    rw [← div_le_iff₀ hn0]
    by_cases hle : N1 ≤ n
    · have hdist := hN0 n (le_trans (le_max_left _ _) hle)
      rw [Real.dist_eq] at hdist
      have h1 : (∑ j ∈ Icc 2 n, a j * (Real.log (j : ℝ)) ^ d) / (n : ℝ) ≤ |C| + 1 := by
        linarith [(abs_lt.mp hdist).2, le_abs_self C]
      exact h1.trans ((le_max_left _ _).trans (le_max_left _ _))
    · have hmem : n ∈ Finset.Icc 2 N1 := by simp only [mem_Icc]; omega
      have h1 := Finset.le_sup' (f := fun n =>
        (∑ j ∈ Icc 2 n, a j * (Real.log (j : ℝ)) ^ d) / (n : ℝ)) hmem
      exact h1.trans ((le_max_right _ _).trans (le_max_left _ _))
  obtain ⟨M, hM0, hM⟩ := hS_bound
  have hrem_zero : Tendsto (fun N : ℕ =>
      (∑ n ∈ Ico 2 N, (∑ j ∈ Icc 2 n, a j * (Real.log (j : ℝ)) ^ d) *
        (1 / (Real.log (n : ℝ)) ^ d - 1 / (Real.log ((n + 1 : ℕ) : ℝ)) ^ d)) /
        ((N : ℝ) / (Real.log (N : ℝ)) ^ d)) atTop (𝓝 0) := by
    have hmul := (sum_inv_log_pow_littleO d hd).const_mul (M * (d : ℝ))
    rw [mul_zero] at hmul
    apply squeeze_zero_norm' _ hmul
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
    have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
    have hden_pos : 0 < (N : ℝ) / (Real.log (N : ℝ)) ^ d := div_pos hNpos (pow_pos hlogN d)
    have hterm_nn : ∀ n ∈ Ico 2 N,
        0 ≤ (∑ j ∈ Icc 2 n, a j * (Real.log (j : ℝ)) ^ d) *
          (1 / (Real.log (n : ℝ)) ^ d - 1 / (Real.log ((n + 1 : ℕ) : ℝ)) ^ d) := by
      intro n hn
      have hn2 : 2 ≤ n := (mem_Ico.mp hn).1
      apply mul_nonneg
      · exact sum_nonneg fun j hj => mul_nonneg (ha j)
          (pow_nonneg (Real.log_nonneg (by exact_mod_cast (by have := (mem_Icc.mp hj).1; omega : 1 ≤ j))) d)
      · exact (inv_log_pow_sub_le d hd n hn2).1
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sum_nonneg hterm_nn) hden_pos.le)]
    have hsum_le : ∑ n ∈ Ico 2 N, (∑ j ∈ Icc 2 n, a j * (Real.log (j : ℝ)) ^ d) *
        (1 / (Real.log (n : ℝ)) ^ d - 1 / (Real.log ((n + 1 : ℕ) : ℝ)) ^ d) ≤
        M * (d : ℝ) * ∑ n ∈ Icc 2 N, 1 / (Real.log (n : ℝ)) ^ (d + 1) := by
      calc
        _ ≤ ∑ n ∈ Ico 2 N, (M * (n : ℝ)) * ((d : ℝ) / ((n : ℝ) * (Real.log (n : ℝ)) ^ (d + 1))) := by
          apply sum_le_sum; intro n hn
          have hn2 : 2 ≤ n := (mem_Ico.mp hn).1
          exact mul_le_mul (hM n hn2) (inv_log_pow_sub_le d hd n hn2).2
            (inv_log_pow_sub_le d hd n hn2).1 (mul_nonneg hM0.le (Nat.cast_nonneg n))
        _ = M * (d : ℝ) * ∑ n ∈ Ico 2 N, 1 / (Real.log (n : ℝ)) ^ (d + 1) := by
          rw [mul_sum]
          apply sum_congr rfl; intro n hn
          have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by have := (mem_Ico.mp hn).1; omega : n ≠ 0)
          field_simp
        _ ≤ M * (d : ℝ) * ∑ n ∈ Icc 2 N, 1 / (Real.log (n : ℝ)) ^ (d + 1) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply sum_le_sum_of_subset_of_nonneg
          · intro x hx; simp only [mem_Ico, mem_Icc] at hx ⊢; omega
          · intro x hx _
            have hx2 : 2 ≤ x := (mem_Icc.mp hx).1
            have : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < x))
            positivity
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right hsum_le hden_pos.le
  have hadd := hS.add hrem_zero
  rw [add_zero] at hadd
  apply Tendsto.congr' _ hadd
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hlogN : Real.log (N : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (by omega : 1 < N))).ne'
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have heq : ∑ n ∈ Icc 2 N, a n =
      ∑ n ∈ Icc 2 N, (a n * (Real.log (n : ℝ)) ^ d) * (1 / (Real.log (n : ℝ)) ^ d) := by
    apply sum_congr rfl; intro n hn
    have hlogn : Real.log (n : ℝ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast (by have := (mem_Icc.mp hn).1; omega : 1 < n))).ne'
    have hp : (Real.log (n : ℝ)) ^ d ≠ 0 := pow_ne_zero d hlogn
    field_simp
  rw [heq, abel_Icc2 (fun n => a n * (Real.log (n : ℝ)) ^ d)
    (fun n => 1 / (Real.log (n : ℝ)) ^ d) N hN, add_div]
  congr 1
  have hp : (Real.log (N : ℝ)) ^ d ≠ 0 := pow_ne_zero d hlogN
  field_simp

lemma integral_inv_log_pow_asymp (d : ℕ) (hd : 1 ≤ d) :
    Tendsto (fun N : ℕ =>
      (∫ t in (2 : ℝ)..(N : ℝ), 1 / t.log ^ d) / ((N : ℝ) / (Real.log (N : ℝ)) ^ d))
      atTop (𝓝 1) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have htail : Tendsto (fun N : ℕ =>
      (∫ t in (2 : ℝ)..(N : ℝ), 1 / t.log ^ (d + 1)) /
        ((N : ℝ) / (Real.log (N : ℝ)) ^ d)) atTop (𝓝 0) := by
    have ht1 : Tendsto (fun N : ℕ =>
        (Real.log (N : ℝ)) ^ d / Real.sqrt (N : ℝ) * (1 / (Real.log 2) ^ (d + 1)))
        atTop (𝓝 0) := by
      have h := ((log_pow_div_sqrt_tendsto_zero d).comp tendsto_natCast_atTop_atTop).mul_const
        (1 / (Real.log 2) ^ (d + 1))
      rwa [zero_mul] at h
    have ht2 : Tendsto (fun N : ℕ => (2 : ℝ) ^ (d + 1) / Real.log (N : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
    have hadd := ht1.add ht2
    rw [add_zero] at hadd
    apply squeeze_zero_norm' _ hadd
    filter_upwards [eventually_ge_atTop 16] with N hN
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
    have h1N : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
    have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
    have hden_pos : 0 < (N : ℝ) / (Real.log (N : ℝ)) ^ d := div_pos hNpos (pow_pos hlogN d)
    have h2sq : (2 : ℝ) ≤ Real.sqrt (N : ℝ) :=
      (Real.le_sqrt (by norm_num) hNpos.le).mpr (by exact_mod_cast (by omega : 4 ≤ N))
    have hsqN : Real.sqrt (N : ℝ) ≤ (N : ℝ) :=
      (Real.sqrt_le_left hNpos.le).mpr (by nlinarith)
    have hint : ∀ a b : ℝ, 2 ≤ a → a ≤ b →
        IntervalIntegrable (fun t : ℝ => 1 / t.log ^ (d + 1)) MeasureTheory.volume a b := by
      intro a b ha hab
      apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.div continuousOn_const
      · exact (Real.continuousOn_log.mono (fun x hx => by
          have := (Set.uIcc_of_le hab ▸ hx).1
          exact (by linarith : x ≠ 0))).pow (d + 1)
      · intro x hx
        have hx2 : 2 ≤ x := le_trans ha (Set.uIcc_of_le hab ▸ hx).1
        exact (pow_pos (Real.log_pos (by linarith)) (d + 1)).ne'
    have hint_nn : 0 ≤ ∫ t in (2 : ℝ)..(N : ℝ), 1 / t.log ^ (d + 1) := by
      apply intervalIntegral.integral_nonneg (by exact_mod_cast (by omega : 2 ≤ N))
      intro x hx
      have : 0 < Real.log x := Real.log_pos (by linarith [hx.1])
      positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hint_nn hden_pos.le)]
    have hsplit : (∫ t in (2 : ℝ)..(N : ℝ), 1 / t.log ^ (d + 1)) =
        (∫ t in (2 : ℝ)..Real.sqrt (N : ℝ), 1 / t.log ^ (d + 1)) +
        (∫ t in Real.sqrt (N : ℝ)..(N : ℝ), 1 / t.log ^ (d + 1)) :=
      (intervalIntegral.integral_add_adjacent_intervals
        (hint 2 (Real.sqrt (N : ℝ)) le_rfl h2sq)
        (hint (Real.sqrt (N : ℝ)) (N : ℝ) h2sq hsqN)).symm
    have hp1 : (∫ t in (2 : ℝ)..Real.sqrt (N : ℝ), 1 / t.log ^ (d + 1)) ≤
        Real.sqrt (N : ℝ) * (1 / (Real.log 2) ^ (d + 1)) := by
      calc
        _ ≤ ∫ _t in (2 : ℝ)..Real.sqrt (N : ℝ), 1 / (Real.log 2) ^ (d + 1) := by
          apply intervalIntegral.integral_mono_on h2sq
            (hint 2 (Real.sqrt (N : ℝ)) le_rfl h2sq) intervalIntegrable_const
          intro x hx
          exact one_div_le_one_div_of_le (pow_pos hlog2 _)
            (pow_le_pow_left₀ hlog2.le (Real.log_le_log (by norm_num) hx.1) _)
        _ = (Real.sqrt (N : ℝ) - 2) * (1 / (Real.log 2) ^ (d + 1)) := by
          rw [intervalIntegral.integral_const, smul_eq_mul]
        _ ≤ Real.sqrt (N : ℝ) * (1 / (Real.log 2) ^ (d + 1)) := by
          apply mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have hp2 : (∫ t in Real.sqrt (N : ℝ)..(N : ℝ), 1 / t.log ^ (d + 1)) ≤
        (N : ℝ) * ((2 : ℝ) ^ (d + 1) / (Real.log (N : ℝ)) ^ (d + 1)) := by
      have hlog_sqrt : Real.log (Real.sqrt (N : ℝ)) = Real.log (N : ℝ) / 2 :=
        Real.log_sqrt hNpos.le
      have hlog_sqrt_pos : 0 < Real.log (Real.sqrt (N : ℝ)) := by rw [hlog_sqrt]; positivity
      calc
        _ ≤ ∫ _t in Real.sqrt (N : ℝ)..(N : ℝ), 1 / (Real.log (Real.sqrt (N : ℝ))) ^ (d + 1) := by
          apply intervalIntegral.integral_mono_on hsqN
            (hint (Real.sqrt (N : ℝ)) (N : ℝ) h2sq hsqN) intervalIntegrable_const
          intro x hx
          exact one_div_le_one_div_of_le (pow_pos hlog_sqrt_pos _)
            (pow_le_pow_left₀ hlog_sqrt_pos.le
              (Real.log_le_log (Real.sqrt_pos.mpr hNpos) hx.1) _)
        _ = ((N : ℝ) - Real.sqrt (N : ℝ)) * ((2 : ℝ) ^ (d + 1) / (Real.log (N : ℝ)) ^ (d + 1)) := by
          rw [intervalIntegral.integral_const, smul_eq_mul, hlog_sqrt, div_pow, one_div_div]
        _ ≤ (N : ℝ) * ((2 : ℝ) ^ (d + 1) / (Real.log (N : ℝ)) ^ (d + 1)) := by
          apply mul_le_mul_of_nonneg_right (by linarith [Real.sqrt_nonneg (N : ℝ)]) (by positivity)
    calc
      (∫ t in (2 : ℝ)..(N : ℝ), 1 / t.log ^ (d + 1)) / ((N : ℝ) / (Real.log (N : ℝ)) ^ d)
          ≤ (Real.sqrt (N : ℝ) * (1 / (Real.log 2) ^ (d + 1)) +
            (N : ℝ) * ((2 : ℝ) ^ (d + 1) / (Real.log (N : ℝ)) ^ (d + 1))) /
              ((N : ℝ) / (Real.log (N : ℝ)) ^ d) := by
        rw [hsplit]; exact div_le_div_of_nonneg_right (add_le_add hp1 hp2) hden_pos.le
      _ = (Real.log (N : ℝ)) ^ d / Real.sqrt (N : ℝ) * (1 / (Real.log 2) ^ (d + 1)) +
          (2 : ℝ) ^ (d + 1) / Real.log (N : ℝ) := by
        have hsq : Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) = (N : ℝ) := Real.mul_self_sqrt hNpos.le
        have hsp := (Real.sqrt_pos.mpr hNpos).ne'
        have hlp := hlogN.ne'
        rw [add_div]
        congr 1
        · field_simp
          exact Real.sq_sqrt hNpos.le
        · field_simp
          exact (pow_succ _ _).symm
  have hconst : Tendsto (fun N : ℕ =>
      (2 / (Real.log 2) ^ d) / ((N : ℝ) / (Real.log (N : ℝ)) ^ d)) atTop (𝓝 0) := by
    have hden : Tendsto (fun N : ℕ => (N : ℝ) / (Real.log (N : ℝ)) ^ d) atTop atTop := by
      have h := (isLittleO_log_rpow_rpow_atTop (d : ℝ) zero_lt_one).tendsto_div_nhds_zero
      have hinv : Tendsto (fun N : ℕ => (Real.log (N : ℝ)) ^ d / (N : ℝ)) atTop (𝓝 0) := by
        refine (h.comp tendsto_natCast_atTop_atTop).congr' ?_
        filter_upwards [eventually_ge_atTop 2] with N hN
        simp [Real.rpow_natCast, Real.rpow_one]
      have hpos : ∀ᶠ N : ℕ in atTop, (Real.log (N : ℝ)) ^ d / (N : ℝ) ∈ Set.Ioi (0 : ℝ) := by
        filter_upwards [eventually_ge_atTop 2] with N hN
        have : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
        exact div_pos (pow_pos this d) (by exact_mod_cast (by omega : 0 < N))
      have hcomp := tendsto_inv_nhdsGT_zero.comp
        (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hinv hpos)
      refine hcomp.congr' ?_
      filter_upwards with N
      simp [Function.comp_apply]
    exact tendsto_const_nhds.div_atTop hden
  have hcomb := ((tendsto_const_nhds (x := (1 : ℝ)) (f := (atTop : Filter ℕ))).sub hconst).add
    (htail.const_mul (d : ℝ))
  rw [sub_zero, mul_zero, add_zero] at hcomb
  apply Tendsto.congr' _ hcomb
  filter_upwards [eventually_ge_atTop 3] with N hN
  have h2N : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 2 ≤ N)
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hden_ne : ((N : ℝ) / (Real.log (N : ℝ)) ^ d) ≠ 0 := (div_pos hNpos (pow_pos hlogN d)).ne'
  have hint_fn : ∀ m : ℕ,
      IntervalIntegrable (fun t : ℝ => 1 / t.log ^ m) MeasureTheory.volume (2 : ℝ) (N : ℝ) := by
    intro m
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_const
    · exact (Real.continuousOn_log.mono (fun x hx => by
        have := (Set.uIcc_of_le h2N ▸ hx).1
        exact (by linarith : x ≠ 0))).pow m
    · intro x hx
      have hx2 : 2 ≤ x := (Set.uIcc_of_le h2N ▸ hx).1
      exact (pow_pos (Real.log_pos (by linarith)) m).ne'
  have hderiv : ∀ t ∈ Set.uIcc (2 : ℝ) (N : ℝ),
      HasDerivAt (fun x : ℝ => x / x.log ^ d)
        (1 / t.log ^ d - (d : ℝ) * (1 / t.log ^ (d + 1))) t := by
    intro t ht
    have ht2 : 2 ≤ t := (Set.uIcc_of_le h2N ▸ ht).1
    have ht0 : t ≠ 0 := by linarith
    have hlogt : Real.log t ≠ 0 := (Real.log_pos (by linarith)).ne'
    have h1 : HasDerivAt (fun x : ℝ => x / x.log ^ d)
        ((1 * (Real.log t) ^ d - t * ((d : ℝ) * (Real.log t) ^ (d - 1) * t⁻¹)) /
          ((Real.log t) ^ d) ^ 2) t :=
      (hasDerivAt_id t).div ((Real.hasDerivAt_log ht0).pow d) (pow_ne_zero d hlogt)
    have hd1 : d = (d - 1) + 1 := (Nat.sub_add_cancel hd).symm
    have heq : (1 * (Real.log t) ^ d - t * ((d : ℝ) * (Real.log t) ^ (d - 1) * t⁻¹)) /
        ((Real.log t) ^ d) ^ 2 = 1 / t.log ^ d - (d : ℝ) * (1 / t.log ^ (d + 1)) := by
      set L := Real.log t
      set A := L ^ (d - 1)
      have hA : A ≠ 0 := pow_ne_zero (d - 1) hlogt
      have hp : L ^ d = A * L := by dsimp [A]; conv_lhs => rw [hd1, pow_succ]
      have hp1 : L ^ (d + 1) = A * L ^ 2 := by rw [pow_succ, hp]; ring
      rw [hp1, hp]
      field_simp [ht0, hlogt, hA]
    rwa [heq] at h1
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((hint_fn d).sub ((hint_fn (d + 1)).const_mul (d : ℝ)))
  rw [intervalIntegral.integral_sub (hint_fn d) ((hint_fn (d + 1)).const_mul (d : ℝ)),
    intervalIntegral.integral_const_mul] at hftc
  have hibp : (∫ t in (2 : ℝ)..(N : ℝ), 1 / t.log ^ d) =
      (N : ℝ) / (Real.log (N : ℝ)) ^ d - 2 / (Real.log 2) ^ d +
      (d : ℝ) * ∫ t in (2 : ℝ)..(N : ℝ), 1 / t.log ^ (d + 1) := by
    linarith
  rw [hibp, add_div, sub_div, div_self hden_ne, mul_div_assoc]

/- ### Part 5: Main reduction theorem -/

theorem main : H1 → H2 → type_of% @HardyLittlewood.first_hardy_littlewood_conjecture := by
  intro hH1 hH2 k m
  classical
  by_cases hlocal : ∀ q : {q : ℕ // q.Prime ∧ 3 ≤ q},
      ¬ Function.Surjective (fun i => (m i : ZMod q))
  · intro hzero heven hinj
    let C : ℝ := 2 ^ k * ∏' (q : {q : ℕ // q.Prime ∧ 3 ≤ q}),
      (1 - (Nat.numResidues q m : ℝ) / q) / (1 - 1 / q) ^ k.succ
    have hCpos : 0 < C := singular_series_pos m hinj hlocal
    have hcorr : Tendsto (fun N : ℕ =>
        (∑ n ∈ Ioc 0 N, ∏ i : Fin k.succ, vonMangoldt (n + m i)) / (N : ℝ))
        atTop (𝓝 C) := by
      cases k with
      | zero =>
        have hC1 : C = 1 := k0_singular_series m
        rw [hC1]
        unfold H1 at hH1
        simpa [Fin.prod_univ_one, hzero] using hH1
      | succ k' =>
        exact hH2 m hzero heven hinj hlocal
    have hW : Tendsto (fun N : ℕ =>
        (∑ n ∈ Ioc 0 N, if ∀ i, (n + m i).Prime then ∏ i, Real.log (n + m i : ℕ) else 0) /
          (N : ℝ)) atTop (𝓝 C) := by
      have hsub := hcorr.sub (vonMangoldt_tuple_error_tendsto_zero m)
      rw [sub_zero] at hsub
      apply Tendsto.congr' _ hsub
      filter_upwards with N
      rw [← sub_div, sub_sub_cancel]
    have hA : Tendsto (fun N : ℕ =>
        (∑ n ∈ Icc 2 N, if ∀ i, (n + m i).Prime then (Real.log (n : ℝ)) ^ k.succ else 0) /
          (N : ℝ)) atTop (𝓝 C) :=
      weighted_to_log_pow m C hCpos hW
    have hcount_lim : Tendsto (fun N : ℕ =>
        (∑ n ∈ Icc 2 N, if ∀ i, (n + m i).Prime then (1 : ℝ) else 0) /
          ((N : ℝ) / (Real.log (N : ℝ)) ^ k.succ)) atTop (𝓝 C) := by
      have h := abel_unweight (fun n => if ∀ i, (n + m i).Prime then (1 : ℝ) else 0)
        k.succ (Nat.succ_pos k) C (fun n => by split_ifs <;> norm_num)
      apply h
      refine hA.congr' ?_
      filter_upwards with N
      congr 1
      apply sum_congr rfl; intro n _
      split_ifs <;> simp
    have hcount_eq : ∀ N : ℕ, 2 ≤ N →
        (Nat.primeTupleCounting m N : ℝ) =
          ∑ n ∈ Icc 2 N, if ∀ i, (n + m i).Prime then (1 : ℝ) else 0 := by
      intro N hN
      have hadm : ∀ p : ℕ, IsAdmissiblePrimeConstellation m p ↔ ∀ i, (p + m i).Prime := by
        intro p
        constructor
        · exact fun h => h.1.2.2
        · intro h
          refine ⟨⟨hzero, ?_, h⟩, ?_⟩
          · intro i hi
            refine ⟨?_, heven i hi⟩
            by_contra h0
            have hmi : m i = 0 := by omega
            exact hi (hinj (hmi.trans hzero.symm))
          · intro q hq hsurj
            by_cases h2 : q = 2
            · subst q
              obtain ⟨i, hi⟩ := hsurj ((p : ZMod 2) + 1)
              have hev : Even (m i) := by
                by_cases hi0 : i = 0
                · rw [hi0, hzero]; exact Even.zero
                · exact heven i hi0
              obtain ⟨r, hr⟩ := hev
              have hm2 : (m i : ZMod 2) = 0 := by
                rw [hr, show r + r = 2 * r by omega, Nat.cast_mul, ZMod.natCast_self, zero_mul]
              dsimp at hi
              rw [hm2, add_zero] at hi
              have : (1 : ZMod 2) = 0 := by
                have := congrArg (fun x : ZMod 2 => x - (p : ZMod 2)) hi
                simpa using this.symm
              exact (by decide : (1 : ZMod 2) ≠ 0) this
            · have hq3 : 3 ≤ q := by have := hq.two_le; omega
              apply hlocal ⟨q, hq, hq3⟩
              intro z
              obtain ⟨i, hi⟩ := hsurj ((p : ZMod q) + z)
              exact ⟨i, add_left_cancel hi⟩
      unfold Nat.primeTupleCounting
      rw [Nat.count_eq_card_filter_range, ← Finset.sum_boole]
      have hsub : (Finset.range (N + 1)).filter (IsAdmissiblePrimeConstellation m) =
          (Finset.Icc 2 N).filter (fun p => ∀ i, (p + m i).Prime) := by
        ext p
        simp only [mem_filter, mem_range, mem_Icc, hadm]
        constructor
        · rintro ⟨hpN, hp⟩
          have hp2 : 2 ≤ p := by
            have := (hp 0).two_le
            rw [hzero, Nat.add_zero] at this
            exact this
          exact ⟨⟨hp2, by omega⟩, hp⟩
        · rintro ⟨⟨_, hpN⟩, hp⟩
          exact ⟨by omega, hp⟩
      rw [← sum_filter, ← sum_filter, hsub]
    have hP_lim : Tendsto (fun N : ℕ =>
        (Nat.primeTupleCounting m N : ℝ) / ((N : ℝ) / (Real.log (N : ℝ)) ^ k.succ))
        atTop (𝓝 C) := by
      refine hcount_lim.congr' ?_
      filter_upwards [eventually_ge_atTop 2] with N hN
      rw [hcount_eq N hN]
    have hI_lim := integral_inv_log_pow_asymp k.succ (Nat.succ_pos k)
    have hCI_lim : Tendsto (fun N : ℕ =>
        (C * ∫ t in (2 : ℝ)..(N : ℝ), 1 / t.log ^ k.succ) /
          ((N : ℝ) / (Real.log (N : ℝ)) ^ k.succ)) atTop (𝓝 C) := by
      simpa [mul_div_assoc] using hI_lim.const_mul C
    apply isEquivalent_of_tendsto_one
    have hdiv := hP_lim.div hCI_lim hCpos.ne'
    rw [div_self hCpos.ne'] at hdiv
    refine hdiv.congr' ?_
    filter_upwards [eventually_ge_atTop 3] with N hN
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
    have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
    have hdne : ((N : ℝ) / (Real.log (N : ℝ)) ^ k.succ) ≠ 0 :=
      (div_pos hNpos (pow_pos hlogN k.succ)).ne'
    dsimp only [C]
    simp [Pi.div_apply, div_div_div_cancel_right₀ hdne]
  · push Not at hlocal
    obtain ⟨q, hq⟩ := hlocal
    exact obstructed m q hq

end OMA.R_HardyLittlewood_first_hardy_littlewood_conjecture_R2
