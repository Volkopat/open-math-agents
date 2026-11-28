import FormalConjectures.ErdosProblems.«694»

/-! Mertens' product and small prime moduli suffice for the asymptotic extrema of Euler's totient.
The extremal comparison and Landau estimate are adapted from Liam Price and GPT-5.5 Pro,
Shashi456/erdos-formalizations (286f856aa3fc08957b80950fd18a45aab8d045ea), as ported by
@marcusbuffett in Open Math Agents #4279 (Apache-2.0). The composite totient collisions
and height interpolation are adapted from the public plby/lean-proofs collection maintained by Boris Alexeev,
8822f7ddef30fadbd92e1c6ab4ed897af356af5e, ErdosProblems/Erdos694/{PrimeProducts,Height,Unconditional}.
The source names Pawan Sasanka Ammanamanchi, Claude Code 4.7 and GPT-5.5 Pro as formalizers.
Here the same dyadic interval serves all the moduli, with its exponent allowed to vary by one. -/

namespace OMA.R_Erdos694_erdos_694_R2
open Classical Filter Topology Asymptotics
open scoped BigOperators Nat

/-- Mertens’ product asymptotic over primes. -/
def H1 : Prop := Tendsto
      (fun y : ℝ =>
        (∏ p ∈ Finset.filter Nat.Prime (Finset.Icc 1 ⌊y⌋₊), ((p : ℝ) / (p - 1))) /
          (Real.exp Real.eulerMascheroniConstant * Real.log y))
      atTop (𝓝 1)

/-- A common supply of primes for prime moduli of polylogarithmic size. -/
def H2 : Prop := ∀ D : ℕ, ∀ᶠ k : ℕ in atTop, ∃ j : ℕ, (j = k ∨ j = k + 1) ∧
  ∀ q : ℕ, q.Prime → q ≤ k ^ D → 2 * k ^ D ≤
    ((Finset.Ioc (2 ^ j) (2 * 2 ^ j)).filter (fun p => p.Prime ∧ p % q = 1 % q)).card

end OMA.R_Erdos694_erdos_694_R2

/-! # An upper bound for totient fibers -/

open Filter
open scoped Topology
namespace TotientDyadic

/-- In a product split at the integer part of log X, the contribution of
large primes is at most exp (2/log(log X)), uniformly for m ≤ X. -/
theorem cutoff_upper (V P : ℕ → ℝ) {g : ℝ} (hg : 0 < g)
    (nonneg : ∀ y, 0 ≤ P y)
    (hprod : Tendsto (fun u : ℝ => P ⌊u⌋₊ / (g*Real.log u)) atTop (𝓝 1))
    (split : ∀ m Y : ℕ, m ≠ 0 → 1 ≤ Y → V m ≤ P Y *
      ((((Y+1 : ℕ):ℝ)/Y) ^ (Real.log m/Real.log ((Y:ℝ)+1))))
    {δ : ℝ} (hδ : 0 < δ) : ∀ᶠ X : ℝ in atTop,
      (⨆ m ∈ Set.Icc 1 ⌊X⌋₊, V m) / (g*Real.log (Real.log X)) ≤ 1+δ := by
  have ll := Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have little : Tendsto (fun X : ℝ => 2/Real.log (Real.log X)) atTop (𝓝 0) := by
    have hc : Tendsto (fun _ : ℝ => (2:ℝ)) atTop (𝓝 2) := tendsto_const_nhds
    simpa [div_eq_mul_inv,Function.comp_def] using hc.mul (tendsto_inv_atTop_zero.comp ll)
  have lim := (hprod.comp Real.tendsto_log_atTop).mul (Real.continuous_exp.continuousAt.tendsto.comp little)
  have hlim : Tendsto (fun X : ℝ => P ⌊Real.log X⌋₊/(g*Real.log (Real.log X))*Real.exp (2/Real.log (Real.log X))) atTop (𝓝 1) := by
    simpa only [Function.comp_apply,Real.exp_zero,mul_one] using lim
  filter_upwards [hlim.eventually_le_const (show 1 < 1+δ by linarith), Real.tendsto_log_atTop.eventually_ge_atTop 2,eventually_ge_atTop (0:ℝ)] with X result logX Xnn
  let Y := ⌊Real.log X⌋₊
  have yp : 1 ≤ Y := Nat.le_floor (by norm_num; linarith)
  have yp' : 0 < (Y:ℝ) := by exact_mod_cast (show 0 < Y by omega)
  have lly : 0 < Real.log (Real.log X) := Real.log_pos (by linarith)
  have floorBound : Real.log X ≤ (Y:ℝ)+1 := (Nat.lt_floor_add_one _).le
  have Ycomp : Real.log X ≤ 2*Y := by have := (show (1:ℝ) ≤ Y by exact_mod_cast yp); linarith
  have dcomp : Real.log (Real.log X) ≤ Real.log ((Y:ℝ)+1) := Real.log_le_log (by linarith) floorBound
  have den : 0 < g*Real.log (Real.log X) := mul_pos hg lly
  have major : P Y * Real.exp (2/Real.log (Real.log X)) ≤ (1+δ)*(g*Real.log (Real.log X)) := by
    apply (div_le_iff₀ den).mp
    convert result using 1
    dsimp [Y]
    ring
  apply (div_le_iff₀ den).mpr
  apply ciSup_le
  intro m
  by_cases hm : m ∈ Set.Icc 1 ⌊X⌋₊
  · rw [ciSup_pos hm]
    have mpos : 0 < (m:ℝ) := by exact_mod_cast (show 0 < m from hm.1)
    have mx : (m:ℝ) ≤ X := (Nat.le_floor_iff Xnn).mp hm.2
    have em : 0 ≤ Real.log m / Real.log ((Y:ℝ)+1) := div_nonneg (Real.log_nonneg (by exact_mod_cast hm.1)) (lly.le.trans dcomp)
    have base : 0 < (((Y+1:ℕ):ℝ)/(Y:ℝ)) := by positivity
    have lb : Real.log (((Y+1:ℕ):ℝ)/(Y:ℝ)) ≤ 1/(Y:ℝ) := by
      refine (Real.log_le_sub_one_of_pos base).trans_eq ?_
      push_cast
      field_simp; ring
    have leE : Real.log m / Real.log ((Y:ℝ)+1) ≤ (2*(Y:ℝ))/Real.log (Real.log X) := by
      exact div_le_div₀ (show 0 ≤ 2*(Y:ℝ) by positivity) ((Real.log_le_log mpos mx).trans Ycomp) lly dcomp
    apply (split m Y (Nat.ne_of_gt (show 0 < m from hm.1)) yp).trans
    apply le_trans _ major
    apply mul_le_mul_of_nonneg_left _ (nonneg Y)
    rw [Real.rpow_def_of_pos base,Real.exp_le_exp]
    calc _ ≤ (1/(Y:ℝ))*(2*Y/Real.log (Real.log X)) := mul_le_mul lb leE em (by positivity)
         _ = _ := by field_simp
  · rw [ciSup_neg hm,Real.sSup_empty]
    positivity

end TotientDyadic

namespace OMA.R_Erdos694_erdos_694_R2
open Classical Filter Topology Asymptotics
open scoped BigOperators Nat
theorem ratio_totient_eq_prod_primeFactors_q (m : ℕ) (hm : m ≠ 0) :
    (m : ℚ) / Nat.totient m =
      ∏ p ∈ m.primeFactors, ((p : ℚ) / (p - 1)) := by
  have hφ : (Nat.totient m : ℚ) =
      (m : ℚ) * ∏ p ∈ m.primeFactors, (1 - (p : ℚ)⁻¹) :=
    Nat.totient_eq_mul_prod_factors m
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast hm
  have hprod_nonzero :
      (∏ p ∈ m.primeFactors, (1 - (p : ℚ)⁻¹)) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr ?_
    intro p hp
    have hpprime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
    have hpne1 : (p : ℚ) ≠ 1 := by
      norm_num [hpprime.ne_one]
    have hpne0 : (p : ℚ) ≠ 0 := by
      norm_num [hpprime.ne_zero]
    have hrewrite : (1 - (p : ℚ)⁻¹) = ((p : ℚ) - 1) / p := by
      field_simp [hpne0]
    rw [hrewrite]
    exact div_ne_zero (sub_ne_zero.mpr hpne1) hpne0
  have hφne : (Nat.totient m : ℚ) ≠ 0 := by
    rw [hφ]
    exact mul_ne_zero hmQ hprod_nonzero
  calc
    (m : ℚ) / Nat.totient m
        = (∏ p ∈ m.primeFactors, (1 - (p : ℚ)⁻¹))⁻¹ := by
          rw [hφ]
          field_simp [hmQ, hprod_nonzero]
    _ = ∏ p ∈ m.primeFactors, ((p : ℚ) / (p - 1)) := by
      rw [← Finset.prod_inv_distrib]
      refine Finset.prod_congr rfl ?_
      intro p hp
      have hpprime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
      have hpne0 : (p : ℚ) ≠ 0 := by
        norm_num [hpprime.ne_zero]
      have hpne1 : (p : ℚ) ≠ 1 := by
        norm_num [hpprime.ne_one]
      field_simp [hpne0, hpne1]

theorem ratio_totient_eq_prod_primeFactors_real (m : ℕ) (hm : m ≠ 0) :
    (m : ℝ) / Nat.totient m =
      ∏ p ∈ m.primeFactors, ((p : ℝ) / (p - 1)) := by
  have hq := congrArg (fun q : ℚ => (q : ℝ)) (ratio_totient_eq_prod_primeFactors_q m hm)
  simpa [Rat.cast_prod] using hq

theorem one_le_prime_factor (p : ℕ) (hp : Nat.Prime p) :
    1 ≤ (p : ℝ) / (p - 1) := by
  have hden : 0 < (p : ℝ) - 1 := by
    norm_num [hp.one_lt]
  rw [one_le_div hden]
  norm_num

theorem prime_factor_le_succ_div_self {Y p : ℕ} (hY : 1 ≤ Y) (hp : Nat.Prime p) (hYp : Y < p) :
    (p : ℝ) / (p - 1) ≤ ((Y + 1 : ℕ) : ℝ) / Y := by
  have hpden : 0 < (p : ℝ) - 1 := by
    norm_num [hp.one_lt]
  have hYpos : 0 < (Y : ℝ) := by exact_mod_cast hY
  rw [div_le_div_iff₀ hpden hYpos]
  have hle : (Y + 1 : ℝ) ≤ p := by exact_mod_cast hYp
  norm_num at hle ⊢
  nlinarith

theorem ratio_totient_le_split_bound :
    let primeEulerProdNat (Y : ℕ) : ℝ :=
      ∏ p ∈ (Finset.Icc 1 Y).filter Nat.Prime, ((p : ℝ) / (p - 1))
    ∀ (m Y : ℕ) (hm : m ≠ 0) (hY : 1 ≤ Y),
    (m : ℝ) / Nat.totient m ≤
      primeEulerProdNat Y * (((Y + 1 : ℕ) : ℝ) / Y) ^
        (m.primeFactors.filter fun p => Y < p).card := by
  intro primeEulerProdNat m Y hm hY
  classical
  set S := m.primeFactors with hS
  set small := S.filter (fun p => p ≤ Y) with hsmall
  set large := S.filter (fun p => ¬ p ≤ Y) with hlarge
  have hsplit :
      (∏ p ∈ S, ((p : ℝ) / (p - 1))) =
        (∏ p ∈ small, ((p : ℝ) / (p - 1))) *
          (∏ p ∈ large, ((p : ℝ) / (p - 1))) := by
    rw [hsmall, hlarge]
    exact (Finset.prod_filter_mul_prod_filter_not S (fun p => p ≤ Y)
      (fun p => ((p : ℝ) / (p - 1)))).symm
  have hsmall_subset : small ⊆ (Finset.Icc 1 Y).filter Nat.Prime := by
    intro p hp
    rw [hsmall] at hp
    rcases Finset.mem_filter.mp hp with ⟨hpS, hpY⟩
    have hpprime : Nat.Prime p := Nat.prime_of_mem_primeFactors (by simpa [hS] using hpS)
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hpprime.one_le, hpY⟩, hpprime⟩
  have hsmall_le :
      (∏ p ∈ small, ((p : ℝ) / (p - 1))) ≤ primeEulerProdNat Y := by
    unfold primeEulerProdNat
    let all := (Finset.Icc 1 Y).filter Nat.Prime
    have hnonneg_small : 0 ≤ ∏ p ∈ small, ((p : ℝ) / (p - 1)) := by
      refine Finset.prod_nonneg ?_
      intro p hp
      have hpS : p ∈ S := by
        rw [hsmall] at hp
        exact (Finset.mem_filter.mp hp).1
      have hpprime : Nat.Prime p := Nat.prime_of_mem_primeFactors (by simpa [hS] using hpS)
      exact zero_le_one.trans (one_le_prime_factor p hpprime)
    have hone_rest : 1 ≤ ∏ p ∈ all \ small, ((p : ℝ) / (p - 1)) := by
      have aux : ∀ t : Finset ℕ, t ⊆ all \ small →
          1 ≤ ∏ p ∈ t, ((p : ℝ) / (p - 1)) := by
        intro t ht
        induction t using Finset.induction_on with
        | empty => simp
        | insert a s ha ih =>
            rw [Finset.prod_insert ha]
            have ha_mem : a ∈ all \ small := ht (Finset.mem_insert_self a s)
            have hs_sub : s ⊆ all \ small := fun x hx => ht (Finset.mem_insert_of_mem hx)
            exact one_le_mul_of_one_le_of_one_le
              (one_le_prime_factor a (Finset.mem_filter.mp (Finset.mem_sdiff.mp ha_mem).1).2)
              (ih hs_sub)
      exact aux (all \ small) (fun _ h => h)
    calc
      (∏ p ∈ small, ((p : ℝ) / (p - 1)))
          ≤ (∏ p ∈ small, ((p : ℝ) / (p - 1))) *
              ∏ p ∈ all \ small, ((p : ℝ) / (p - 1)) := by
            exact le_mul_of_one_le_right hnonneg_small hone_rest
      _ = ∏ p ∈ all, ((p : ℝ) / (p - 1)) := by
            rw [mul_comm, Finset.prod_sdiff hsmall_subset]
  have hlarge_le :
      (∏ p ∈ large, ((p : ℝ) / (p - 1))) ≤
        (((Y + 1 : ℕ) : ℝ) / Y) ^ large.card := by
    calc
      (∏ p ∈ large, ((p : ℝ) / (p - 1)))
          ≤ ∏ _p ∈ large, (((Y + 1 : ℕ) : ℝ) / Y) := by
            refine Finset.prod_le_prod ?nonneg ?le
            · intro p hp
              have hpS : p ∈ S := by
                rw [hlarge] at hp
                exact (Finset.mem_filter.mp hp).1
              have hpprime : Nat.Prime p := Nat.prime_of_mem_primeFactors (by simpa [hS] using hpS)
              exact zero_le_one.trans (one_le_prime_factor p hpprime)
            · intro p hp
              rw [hlarge] at hp
              rcases Finset.mem_filter.mp hp with ⟨hpS, hpYp⟩
              have hpprime : Nat.Prime p := Nat.prime_of_mem_primeFactors (by simpa [hS] using hpS)
              exact prime_factor_le_succ_div_self hY hpprime (Nat.lt_of_not_ge hpYp)
      _ = (((Y + 1 : ℕ) : ℝ) / Y) ^ large.card := by
        rw [Finset.prod_const]
  rw [ratio_totient_eq_prod_primeFactors_real m hm, hS, hsplit]
  have hlarge_le' :
      (∏ p ∈ large, ((p : ℝ) / (p - 1))) ≤
        (((Y + 1 : ℕ) : ℝ) / Y) ^
          (m.primeFactors.filter fun p => Y < p).card := by
    simpa [hlarge, hS, not_le] using hlarge_le
  exact mul_le_mul hsmall_le hlarge_le'
    (Finset.prod_nonneg fun p hp => by
      have hpS : p ∈ S := by
        rw [hlarge] at hp
        exact (Finset.mem_filter.mp hp).1
      have hpprime : Nat.Prime p := Nat.prime_of_mem_primeFactors (by simpa [hS] using hpS)
      exact zero_le_one.trans (one_le_prime_factor p hpprime))
    (by
      unfold primeEulerProdNat
      exact Finset.prod_nonneg fun p hp => by
        exact zero_le_one.trans (one_le_prime_factor p (Finset.mem_filter.mp hp).2))

theorem large_primeFactors_card_le_log (m Y : ℕ) (hm : m ≠ 0) (hY : 1 ≤ Y) :
    ((m.primeFactors.filter fun p => Y < p).card : ℝ) ≤
      Real.log m / Real.log (Y + 1) := by
  classical
  set L := m.primeFactors.filter fun p => Y < p with hL
  have hL_subset : L ⊆ m.primeFactors := by
    rw [hL]
    exact Finset.filter_subset _ _
  have hpow_le_prod : (Y + 1) ^ L.card ≤ ∏ p ∈ L, p := by
    calc
      (Y + 1) ^ L.card = ∏ _p ∈ L, (Y + 1) := by
        rw [Finset.prod_const]
      _ ≤ ∏ p ∈ L, p := by
        refine Finset.prod_le_prod ?nonneg ?le
        · intro p hp
          exact Nat.zero_le (Y + 1)
        · intro p hp
          have hpY : Y < p := by
            rw [hL] at hp
            exact (Finset.mem_filter.mp hp).2
          exact Nat.succ_le_of_lt hpY
  have hprod_le_all : (∏ p ∈ L, p) ≤ ∏ p ∈ m.primeFactors, p := by
    refine Finset.prod_le_prod_of_subset_of_one_le' hL_subset ?_
    intro p hpall hpnot
    have hpprime : Nat.Prime p := Nat.prime_of_mem_primeFactors hpall
    exact hpprime.one_le
  have hprod_all_le_m : (∏ p ∈ m.primeFactors, p) ≤ m := by
    exact Nat.le_of_dvd (Nat.pos_iff_ne_zero.mpr hm) (Nat.prod_primeFactors_dvd m)
  have hpow_le_m : (Y + 1) ^ L.card ≤ m :=
    hpow_le_prod.trans (hprod_le_all.trans hprod_all_le_m)
  have hbase_gt_one : (1 : ℝ) < (Y + 1 : ℕ) := by
    norm_num
    exact Nat.succ_le_iff.mp hY
  have hlog_pos : 0 < Real.log ((Y + 1 : ℕ) : ℝ) := Real.log_pos hbase_gt_one
  have hpow_pos : 0 < (((Y + 1) ^ L.card : ℕ) : ℝ) := by
    exact_mod_cast pow_pos (Nat.succ_pos Y) L.card
  have hm_pos_real : 0 < (m : ℝ) := by exact_mod_cast Nat.pos_iff_ne_zero.mpr hm
  have hlog_le :
      Real.log (((Y + 1) ^ L.card : ℕ) : ℝ) ≤ Real.log (m : ℝ) := by
    exact Real.log_le_log hpow_pos (by exact_mod_cast hpow_le_m)
  have hlog_pow :
      Real.log (((Y + 1) ^ L.card : ℕ) : ℝ) =
        (L.card : ℝ) * Real.log ((Y + 1 : ℕ) : ℝ) := by
    rw [Nat.cast_pow, Real.log_pow]
  rw [hL]
  rw [hlog_pow] at hlog_le
  simpa [Nat.cast_add, Nat.cast_one] using (le_div_iff₀ hlog_pos).mpr hlog_le

theorem ratio_totient_le_log_split_bound :
    let primeEulerProdNat (Y : ℕ) : ℝ :=
      ∏ p ∈ (Finset.Icc 1 Y).filter Nat.Prime, ((p : ℝ) / (p - 1))
    ∀ (m Y : ℕ) (hm : m ≠ 0) (hY : 1 ≤ Y),
    (m : ℝ) / Nat.totient m ≤
      primeEulerProdNat Y *
        ((((Y + 1 : ℕ) : ℝ) / Y) ^ (Real.log m / Real.log (Y + 1))) := by
  intro primeEulerProdNat m Y hm hY
  have hsplit := ratio_totient_le_split_bound m Y hm hY
  have hcard := large_primeFactors_card_le_log m Y hm hY
  have hbase_ge_one : 1 ≤ (((Y + 1 : ℕ) : ℝ) / Y) := by
    have hYpos : 0 < (Y : ℝ) := by exact_mod_cast hY
    rw [one_le_div hYpos]
    norm_num
  have hpow_le :
      (((Y + 1 : ℕ) : ℝ) / Y) ^
          (m.primeFactors.filter fun p => Y < p).card ≤
        (((Y + 1 : ℕ) : ℝ) / Y) ^ (Real.log m / Real.log (Y + 1)) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hbase_ge_one hcard
  exact hsplit.trans (mul_le_mul_of_nonneg_left hpow_le (by
    exact Finset.prod_nonneg fun p hp => by
      exact zero_le_one.trans (one_le_prime_factor p (Finset.mem_filter.mp hp).2)))

theorem totient_sq_ge_odd_prime_pow (p k : ℕ) (hp : p.Prime) (hp_odd : Odd p) (hk : 0 < k) :
    p ^ k ≤ (Nat.totient (p ^ k)) ^ 2 := by
  rcases Nat.exists_eq_succ_of_ne_zero hk.ne' with ⟨j, rfl⟩

  rw [Nat.totient_prime_pow_succ hp]
  have hp3 : 3 ≤ p := by
    rcases hp_odd with ⟨t, ht⟩
    have h2 := hp.two_le
    omega
  have hp_pos : 0 < p := hp.pos

  have hp_minus_one_sq_ge : p ≤ (p - 1) ^ 2 := by

    set q := p - 1 with hq
    have hq2 : 2 ≤ q := by omega
    have hpeq : p = q + 1 := by omega
    rw [hpeq]

    have h1 : q * q ≥ 2 * q := Nat.mul_le_mul_right q hq2
    have h2 : 2 * q ≥ q + q := by omega
    have h3 : q + q ≥ q + 1 := by omega
    calc q + 1 ≤ q + q := h3
      _ ≤ 2 * q := by omega
      _ ≤ q * q := h1
      _ = q ^ 2 := by ring
  have hpj_pos : 0 < p ^ j := pow_pos hp_pos _
  calc p ^ (j + 1) = p ^ j * p := by ring
    _ ≤ p ^ j * (p - 1) ^ 2 := Nat.mul_le_mul_left _ hp_minus_one_sq_ge
    _ ≤ p ^ j * (p ^ j * (p - 1) ^ 2) := Nat.le_mul_of_pos_left _ hpj_pos
    _ = (p ^ j * (p - 1)) ^ 2 := by ring

theorem totient_sq_ge_half_pow_two (k : ℕ) (hk : 0 < k) :
    2 ^ k ≤ 2 * (Nat.totient (2 ^ k)) ^ 2 := by
  rcases Nat.exists_eq_succ_of_ne_zero hk.ne' with ⟨j, rfl⟩
  rw [Nat.totient_prime_pow_succ Nat.prime_two]

  show 2 ^ (j + 1) ≤ 2 * (2 ^ j * (2 - 1)) ^ 2
  have heq : 2 * (2 ^ j * (2 - 1 : ℕ)) ^ 2 = 2 ^ (2 * j + 1) := by
    have h21 : (2 - 1 : ℕ) = 1 := rfl
    rw [h21, mul_one]
    rw [show (2 : ℕ) * (2 ^ j) ^ 2 = 2 ^ (2 * j + 1) from by
      rw [pow_succ]; ring]
  rw [heq]
  apply Nat.pow_le_pow_right (by norm_num : 1 ≤ 2)
  omega

theorem totient_sq_ge_half (m : ℕ) (_hm : 1 ≤ m) :
    m ≤ 2 * (Nat.totient m) ^ 2 := by

  suffices h : ∀ n : ℕ, n ≤ 2 * (Nat.totient n) ^ 2 ∧ (Odd n → n ≤ (Nat.totient n) ^ 2) by
    exact (h m).1
  intro n
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
    by_cases hp2 : p = 2
    · subst hp2
      refine ⟨totient_sq_ge_half_pow_two k hk, ?_⟩
      intro hodd
      exfalso
      have heven : Even (2 ^ k) := by
        rcases Nat.exists_eq_succ_of_ne_zero hk.ne' with ⟨j, rfl⟩
        exact ⟨2 ^ j, by rw [pow_succ]; ring⟩
      exact (Nat.not_odd_iff_even.mpr heven) hodd
    · have hp_odd : Odd p := hp.odd_of_ne_two hp2
      have hge : p ^ k ≤ (Nat.totient (p ^ k)) ^ 2 :=
        totient_sq_ge_odd_prime_pow p k hp hp_odd hk
      refine ⟨?_, fun _ => hge⟩
      have hle : (Nat.totient (p ^ k)) ^ 2 ≤ 2 * (Nat.totient (p ^ k)) ^ 2 := by
        have := Nat.zero_le ((Nat.totient (p ^ k)) ^ 2); omega
      exact hge.trans hle
  | zero =>
    refine ⟨?_, ?_⟩
    · exact Nat.zero_le _
    · intro hodd
      exfalso
      exact (Nat.not_odd_iff_even.mpr Even.zero) hodd
  | one =>
    refine ⟨?_, fun _ => ?_⟩
    ·
      rw [Nat.totient_one]; norm_num
    · rw [Nat.totient_one]; norm_num
  | coprime a b ha hb hcop iha ihb =>
    obtain ⟨iha1, iha2⟩ := iha
    obtain ⟨ihb1, ihb2⟩ := ihb
    have hφmul : Nat.totient (a * b) = Nat.totient a * Nat.totient b := Nat.totient_mul hcop
    have hsq : (Nat.totient a * Nat.totient b) ^ 2 =
        (Nat.totient a) ^ 2 * (Nat.totient b) ^ 2 := by ring
    refine ⟨?_, ?_⟩
    ·
      by_cases ha_odd : Odd a
      ·
        have ha_le : a ≤ (Nat.totient a) ^ 2 := iha2 ha_odd
        rw [hφmul, hsq]
        calc a * b ≤ (Nat.totient a) ^ 2 * (2 * (Nat.totient b) ^ 2) :=
              Nat.mul_le_mul ha_le ihb1
          _ = 2 * ((Nat.totient a) ^ 2 * (Nat.totient b) ^ 2) := by ring
      ·
        have ha_even : Even a := Nat.not_odd_iff_even.mp ha_odd
        have h2dvda : 2 ∣ a := ha_even.two_dvd
        have hb_odd : Odd b := by
          rw [Nat.odd_iff]
          by_contra hbe
          push Not at hbe
          have : 2 ∣ b := by omega
          have h2dvd_gcd : 2 ∣ Nat.gcd a b := Nat.dvd_gcd h2dvda this
          rw [hcop] at h2dvd_gcd
          omega
        have hb_le : b ≤ (Nat.totient b) ^ 2 := ihb2 hb_odd
        rw [hφmul, hsq]
        calc a * b ≤ (2 * (Nat.totient a) ^ 2) * (Nat.totient b) ^ 2 :=
              Nat.mul_le_mul iha1 hb_le
          _ = 2 * ((Nat.totient a) ^ 2 * (Nat.totient b) ^ 2) := by ring
    ·
      intro hab_odd
      have ha_odd : Odd a := (Nat.odd_mul.mp hab_odd).1
      have hb_odd : Odd b := (Nat.odd_mul.mp hab_odd).2
      rw [hφmul, hsq]
      exact Nat.mul_le_mul (iha2 ha_odd) (ihb2 hb_odd)

theorem totient_preimage_bound {m n : ℕ} (hm : 1 ≤ m) (h : Nat.totient m = n) :
    m ≤ 2 * n ^ 2 := by
  rw [← h]; exact totient_sq_ge_half m hm

theorem R_upper_bound :
    let R (x : ℕ) : ℝ :=
      ⨆ n ∈ {n | n ∈ Set.Icc 1 x ∧ ∃ m, Nat.totient m = n},
        let mmax := sSup {m | Nat.totient m = n}
        let mmin := sInf {m | Nat.totient m = n}
        (mmax : ℝ) / mmin
    ∀ [hm : Fact H1],
    ∀ ε > 0, ∀ᶠ x : ℕ in atTop,
      R x ≤ (Real.exp Real.eulerMascheroniConstant + ε) * Real.log (Real.log x) := by
  intro R hm
  intro ε hε_pos
  set γc : ℝ := Real.exp Real.eulerMascheroniConstant with hγc_def
  have hγc_pos : 0 < γc := Real.exp_pos _
  have hε2_pos : 0 < ε / 2 := by positivity
  have hδ_pos : 0 < ε / (2 * γc) := by positivity

  have h_evlt :
      ∀ᶠ T : ℝ in atTop,
        (⨆ m ∈ Set.Icc 1 ⌊T⌋₊, (m : ℝ) / Nat.totient m) /
          (γc * Real.log (Real.log T)) ≤ 1 + ε / (2 * γc) := by
    exact TotientDyadic.cutoff_upper
      (fun m : ℕ => (m:ℝ)/Nat.totient m)
      (fun Y : ℕ => ∏ p ∈ (Finset.Icc 1 Y).filter Nat.Prime, ((p:ℝ)/(p-1))) hγc_pos
      (fun Y => Finset.prod_nonneg (fun p hp =>
        zero_le_one.trans (one_le_prime_factor p (Finset.mem_filter.mp hp).2)))
      hm.out (fun m Y hm' hY => ratio_totient_le_log_split_bound m Y hm' hY) hδ_pos
  have h_pos_log_log : ∀ᶠ T : ℝ in atTop, 0 < Real.log (Real.log T) := by
    filter_upwards [Filter.eventually_gt_atTop (Real.exp 1)] with T hT
    have hexp_pos : (0:ℝ) < Real.exp 1 := Real.exp_pos _
    have hlogT : 1 < Real.log T := by
      have := Real.log_lt_log hexp_pos hT
      simpa [Real.log_exp] using this
    exact Real.log_pos hlogT
  have h_landau_bound :
      ∀ᶠ T : ℝ in atTop,
        (⨆ m ∈ Set.Icc 1 ⌊T⌋₊, (m : ℝ) / Nat.totient m) ≤
          (γc + ε/2) * Real.log (Real.log T) := by
    filter_upwards [h_evlt, h_pos_log_log] with T hT_le hT_llog_pos
    have hg_pos : 0 < γc * Real.log (Real.log T) := mul_pos hγc_pos hT_llog_pos
    have hf_le : (⨆ m ∈ Set.Icc 1 ⌊T⌋₊, (m : ℝ) / Nat.totient m) ≤
        (1 + ε / (2 * γc)) * (γc * Real.log (Real.log T)) :=
      (div_le_iff₀ hg_pos).mp hT_le
    have heq : (1 + ε / (2 * γc)) * (γc * Real.log (Real.log T)) =
        (γc + ε/2) * Real.log (Real.log T) := by
      field_simp
    rw [heq] at hf_le
    exact hf_le

  have htends_2xsq : Tendsto (fun x : ℕ => (2 : ℝ) * (x : ℝ)^2) atTop atTop := by
    have h1 : Tendsto (fun x : ℕ => ((x : ℝ))) atTop atTop := tendsto_natCast_atTop_atTop
    have h2 : Tendsto (fun x : ℕ => ((x : ℝ))^2) atTop atTop :=
      (tendsto_pow_atTop (n := 2) (by norm_num)).comp h1
    exact Tendsto.const_mul_atTop (by norm_num : (0:ℝ) < 2) h2
  have h_landau_at_T :
      ∀ᶠ x : ℕ in atTop,
        (⨆ m ∈ Set.Icc 1 ⌊(2 : ℝ) * (x : ℝ)^2⌋₊, (m : ℝ) / Nat.totient m) ≤
          (γc + ε/2) * Real.log (Real.log ((2 : ℝ) * (x : ℝ)^2)) :=
    htends_2xsq.eventually h_landau_bound

  have h_loglog_bound :
      ∀ᶠ x : ℕ in atTop,
        Real.log (Real.log ((2 : ℝ) * (x : ℝ)^2)) ≤ Real.log 4 + Real.log (Real.log x) := by
    filter_upwards [Filter.eventually_ge_atTop 2] with x hx
    have hx_ge_2 : (2 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
    have hx_pos : (0 : ℝ) < (x : ℝ) := by linarith
    have hlogx_pos : 0 < Real.log x := Real.log_pos (by linarith)
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlog2_le_logx : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx_ge_2
    have heq1 : Real.log ((2 : ℝ) * (x : ℝ)^2) = Real.log 2 + 2 * Real.log x := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      push_cast; ring
    have hlogargs : Real.log 2 + 2 * Real.log x ≤ 4 * Real.log x := by linarith
    have hlog_inner_pos : 0 < Real.log 2 + 2 * Real.log x := by linarith
    have h_le_log : Real.log (Real.log 2 + 2 * Real.log x) ≤ Real.log (4 * Real.log x) :=
      Real.log_le_log hlog_inner_pos hlogargs
    have heq2 : Real.log (4 * Real.log x) = Real.log 4 + Real.log (Real.log x) := by
      rw [Real.log_mul (by norm_num) hlogx_pos.ne']
    rw [heq1]; linarith

  have h_loglog_to_inf : Tendsto (fun x : ℕ => Real.log (Real.log x)) atTop atTop := by
    have h1 : Tendsto (fun x : ℕ => ((x : ℝ))) atTop atTop := tendsto_natCast_atTop_atTop
    exact Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp h1)

  have h_loglog_large :
      ∀ᶠ x : ℕ in atTop,
        (γc + ε/2) * Real.log 4 ≤ (ε / 2) * Real.log (Real.log x) := by

    set K : ℝ := (γc + ε/2) * Real.log 4 * 2 / ε
    have hK_eventually : ∀ᶠ x : ℕ in atTop, K ≤ Real.log (Real.log x) :=
      h_loglog_to_inf.eventually_ge_atTop K
    filter_upwards [hK_eventually] with x hxK
    have hε_pos' : (0 : ℝ) < ε := hε_pos
    have hKeq : (γc + ε/2) * Real.log 4 = (ε / 2) * K := by
      show (γc + ε/2) * Real.log 4 = (ε / 2) * ((γc + ε/2) * Real.log 4 * 2 / ε)
      field_simp
    rw [hKeq]
    have hε_half_pos : (0 : ℝ) < ε / 2 := hε2_pos
    exact (mul_le_mul_of_nonneg_left hxK hε_half_pos.le)

  have h_R_le_S :
      ∀ᶠ x : ℕ in atTop,
        R x ≤ (⨆ m ∈ Set.Icc 1 ⌊(2 : ℝ) * (x : ℝ)^2⌋₊, (m : ℝ) / Nat.totient m) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with x hx1

    set S2x : ℝ := ⨆ m ∈ Set.Icc 1 ⌊(2 : ℝ) * (x : ℝ)^2⌋₊, (m : ℝ) / Nat.totient m with hS2x_def

    have hfloor_pos : 1 ≤ ⌊(2 : ℝ) * (x : ℝ)^2⌋₊ := by
      apply Nat.le_floor
      have hx_pos : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx1
      have : (1 : ℝ) ≤ (2 : ℝ) * (x : ℝ)^2 := by nlinarith
      exact_mod_cast this

    have hbdd_inner :
        BddAbove (Set.range (fun (m : ℕ) =>
          ⨆ (_ : m ∈ Set.Icc 1 ⌊(2 : ℝ) * (x : ℝ)^2⌋₊), (m : ℝ) / Nat.totient m)) := by
      refine ⟨((⌊(2 : ℝ) * (x : ℝ)^2⌋₊ : ℕ) : ℝ), ?_⟩
      rintro _ ⟨m, rfl⟩
      simp only
      by_cases hm : m ∈ Set.Icc 1 ⌊(2 : ℝ) * (x : ℝ)^2⌋₊
      · rw [ciSup_pos hm]
        have hφ_pos : 0 < Nat.totient m := Nat.totient_pos.mpr hm.1
        have h_div_le : (m : ℝ) / Nat.totient m ≤ m := by
          rw [div_le_iff₀ (by exact_mod_cast hφ_pos)]
          have h1 : (1 : ℝ) ≤ (Nat.totient m : ℝ) := by exact_mod_cast hφ_pos
          have h2 : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast m.zero_le
          nlinarith
        have h_le : (m : ℝ) ≤ ((⌊(2 : ℝ) * (x : ℝ)^2⌋₊ : ℕ) : ℝ) := by exact_mod_cast hm.2
        linarith
      · rw [ciSup_neg hm, Real.sSup_empty]
        exact_mod_cast Nat.zero_le _

    have hS2x_nonneg : 0 ≤ S2x := by
      have h1mem : (1 : ℕ) ∈ Set.Icc 1 ⌊(2 : ℝ) * (x : ℝ)^2⌋₊ := ⟨le_refl _, hfloor_pos⟩
      have h1_term : (1 : ℝ) / Nat.totient 1 = 1 := by simp
      have h_ge : (1 : ℝ) ≤ S2x := by
        rw [hS2x_def]
        calc (1 : ℝ) = (1 : ℝ) / Nat.totient 1 := h1_term.symm
          _ ≤ ⨆ (_ : (1 : ℕ) ∈ Set.Icc 1 ⌊(2 : ℝ) * (x : ℝ)^2⌋₊),
                ((1 : ℕ) : ℝ) / Nat.totient 1 := by
              rw [ciSup_pos h1mem]
              push_cast; rfl
          _ ≤ _ := le_ciSup hbdd_inner 1
      linarith

    unfold R
    apply ciSup_le
    intro n

    by_cases hmem : n ∈ {n : ℕ | n ∈ Set.Icc 1 x ∧ ∃ m, Nat.totient m = n}
    · rw [ciSup_pos hmem]

      obtain ⟨hn_in_Icc, m_wit, hφm⟩ := hmem

      set A : Set ℕ := {m | Nat.totient m = n} with hA_def
      have hn_pos : 1 ≤ n := hn_in_Icc.1
      have hn_le_x : n ≤ x := hn_in_Icc.2

      have hm_wit_pos : 1 ≤ m_wit := by
        rcases Nat.eq_zero_or_pos m_wit with h0 | hpos
        · rw [h0, Nat.totient_zero] at hφm; omega
        · exact hpos

      have hA_ne : A.Nonempty := ⟨m_wit, hφm⟩

      have hA_bdd : BddAbove A := by
        refine ⟨2 * n ^ 2, ?_⟩
        intro m hm
        have hm_pos : 1 ≤ m := by
          rcases Nat.eq_zero_or_pos m with h0 | hpos
          · have hm' : Nat.totient m = n := hm
            rw [h0, Nat.totient_zero] at hm'; omega
          · exact hpos
        exact totient_preimage_bound hm_pos hm

      set mmax : ℕ := sSup A with hmmax_def
      have hmmax_in : mmax ∈ A := Nat.sSup_mem hA_ne hA_bdd
      have hφmmax : Nat.totient mmax = n := hmmax_in
      have hmmax_pos : 1 ≤ mmax := by
        rcases Nat.eq_zero_or_pos mmax with h0 | hpos
        · rw [h0, Nat.totient_zero] at hφmmax; omega
        · exact hpos

      have hmmax_le_2nsq : mmax ≤ 2 * n ^ 2 := totient_preimage_bound hmmax_pos hφmmax
      have hmmax_le_2xsq_R : (mmax : ℝ) ≤ (2 : ℝ) * (x : ℝ)^2 := by
        have h1 : (mmax : ℝ) ≤ (2 * n^2 : ℕ) := by exact_mod_cast hmmax_le_2nsq
        have h2 : ((2 * n^2 : ℕ) : ℝ) ≤ (2 : ℝ) * (x : ℝ)^2 := by
          push_cast
          have hn_le_x_R : (n : ℝ) ≤ (x : ℝ) := by exact_mod_cast hn_le_x
          have hn_nn : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le _
          nlinarith
        linarith
      have hmmax_le_floor : mmax ≤ ⌊(2 : ℝ) * (x : ℝ)^2⌋₊ := Nat.le_floor hmmax_le_2xsq_R
      have hmmax_in_Icc : mmax ∈ Set.Icc 1 ⌊(2 : ℝ) * (x : ℝ)^2⌋₊ := ⟨hmmax_pos, hmmax_le_floor⟩

      set mmin : ℕ := sInf A with hmmin_def
      have hmmin_in : mmin ∈ A := Nat.sInf_mem hA_ne
      have hφmmin : Nat.totient mmin = n := hmmin_in
      have hmmin_pos : 1 ≤ mmin := by
        rcases Nat.eq_zero_or_pos mmin with h0 | hpos
        · rw [h0, Nat.totient_zero] at hφmmin; omega
        · exact hpos

      have hmmin_ge_n : n ≤ mmin := by
        have := Nat.totient_le mmin; rw [hφmmin] at this; exact this

      show (mmax : ℝ) / mmin ≤ S2x
      have hn_pos_R : (0 : ℝ) < n := by exact_mod_cast hn_pos
      have hmmin_pos_R : (0 : ℝ) < mmin := by exact_mod_cast hmmin_pos
      have hmmax_nn_R : (0 : ℝ) ≤ mmax := by exact_mod_cast Nat.zero_le _
      have hmmin_ge_n_R : (n : ℝ) ≤ (mmin : ℝ) := by exact_mod_cast hmmin_ge_n
      have h_div_le : (mmax : ℝ) / mmin ≤ (mmax : ℝ) / n := by
        apply div_le_div_of_nonneg_left hmmax_nn_R hn_pos_R hmmin_ge_n_R
      have h_n_eq : ((n : ℝ)) = (Nat.totient mmax : ℝ) := by exact_mod_cast hφmmax.symm
      rw [h_n_eq] at h_div_le
      have h_term_le_S : (mmax : ℝ) / Nat.totient mmax ≤ S2x := by
        have h_inner_eq :
            (⨆ (_ : mmax ∈ Set.Icc 1 ⌊(2 : ℝ) * (x : ℝ)^2⌋₊),
                (mmax : ℝ) / Nat.totient mmax) = (mmax : ℝ) / Nat.totient mmax :=
          ciSup_pos hmmax_in_Icc
        rw [hS2x_def, ← h_inner_eq]
        exact le_ciSup hbdd_inner mmax
      linarith
    · rw [ciSup_neg hmem]
      rw [Real.sSup_empty]
      exact hS2x_nonneg

  have hllog_pos_ev : ∀ᶠ x : ℕ in atTop, 0 ≤ Real.log (Real.log x) := by
    filter_upwards [Filter.eventually_ge_atTop 3] with x hx
    have hx3 : (3 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
    have hexp_lt_three : Real.exp 1 < 3 := by
      have := Real.exp_one_lt_d9; linarith
    have hlog3_lt_logx : Real.log 3 ≤ Real.log x := Real.log_le_log (by norm_num) hx3
    have h1 : 1 < Real.log 3 := by
      have h := Real.log_lt_log (Real.exp_pos _) hexp_lt_three
      simpa [Real.log_exp] using h
    have h2 : 1 ≤ Real.log x := by linarith
    exact (Real.log_nonneg h2)
  filter_upwards [h_landau_at_T, h_loglog_bound, h_loglog_large, h_R_le_S, hllog_pos_ev]
    with x h1 h2 h3 h4 h5

  have hγε2_pos : 0 ≤ γc + ε / 2 := by linarith
  calc R x
      ≤ (⨆ m ∈ Set.Icc 1 ⌊(2 : ℝ) * (x : ℝ)^2⌋₊, (m : ℝ) / Nat.totient m) := h4
    _ ≤ (γc + ε/2) * Real.log (Real.log ((2 : ℝ) * (x : ℝ)^2)) := h1
    _ ≤ (γc + ε/2) * (Real.log 4 + Real.log (Real.log x)) :=
        mul_le_mul_of_nonneg_left h2 hγε2_pos
    _ = (γc + ε/2) * Real.log 4 + (γc + ε/2) * Real.log (Real.log x) := by ring
    _ ≤ (ε/2) * Real.log (Real.log x) + (γc + ε/2) * Real.log (Real.log x) := by linarith
    _ = (γc + ε) * Real.log (Real.log x) := by ring

end OMA.R_Erdos694_erdos_694_R2

namespace OMA.R_Erdos694_erdos_694_R2
open Classical Filter Topology Asymptotics
open scoped BigOperators Nat

theorem A_pos :
    let smallPrimes (Y : ℕ) : Finset ℕ :=
      (Finset.Icc 1 Y).filter Nat.Prime
    let predecessorProduct (Y : ℕ) : ℕ :=
      ∏ p ∈ smallPrimes Y, (p - 1)
    ∀ (Y : ℕ),
    0 < predecessorProduct Y := by
  intro smallPrimes predecessorProduct Y
  unfold predecessorProduct
  refine Finset.prod_pos ?_
  intro p hp
  simp only [smallPrimes] at hp
  rcases Finset.mem_filter.mp hp with ⟨_, hpprime⟩
  have h2 : 2 ≤ p := hpprime.two_le
  omega

theorem P_pos :
    let smallPrimes (Y : ℕ) : Finset ℕ :=
      (Finset.Icc 1 Y).filter Nat.Prime
    let smallPrimeProduct (Y : ℕ) : ℕ :=
      ∏ p ∈ smallPrimes Y, p
    ∀ (Y : ℕ),
    0 < smallPrimeProduct Y := by
  intro smallPrimes smallPrimeProduct Y
  unfold smallPrimeProduct
  refine Finset.prod_pos ?_
  intro p hp
  simp only [smallPrimes] at hp
  rcases Finset.mem_filter.mp hp with ⟨_, hpprime⟩
  exact hpprime.pos

theorem Q_pos :
    let largeFactors (Y U : ℕ) : Finset ℕ :=
      U.primeFactors.filter fun q => Y < q
    let largePrimeProduct (Y U : ℕ) : ℕ :=
      ∏ q ∈ largeFactors Y U, q
    ∀ (Y U : ℕ),
    0 < largePrimeProduct Y U := by
  intro largeFactors largePrimeProduct Y U
  unfold largePrimeProduct
  refine Finset.prod_pos ?_
  intro q hq
  simp only [largeFactors] at hq
  rcases Finset.mem_filter.mp hq with ⟨hqU, _⟩
  exact (Nat.prime_of_mem_primeFactors hqU).pos

theorem A_le_P :
    let smallPrimes (Y : ℕ) : Finset ℕ :=
      (Finset.Icc 1 Y).filter Nat.Prime
    let smallPrimeProduct (Y : ℕ) : ℕ :=
      ∏ p ∈ smallPrimes Y, p
    let predecessorProduct (Y : ℕ) : ℕ :=
      ∏ p ∈ smallPrimes Y, (p - 1)
    ∀ (Y : ℕ),
    predecessorProduct Y ≤ smallPrimeProduct Y := by
  intro smallPrimes smallPrimeProduct predecessorProduct Y
  unfold predecessorProduct smallPrimeProduct
  refine Finset.prod_le_prod ?_ ?_
  · intro p hp
    simp only [smallPrimes] at hp
    rcases Finset.mem_filter.mp hp with ⟨_, hpprime⟩
    have h2 : 2 ≤ p := hpprime.two_le
    omega
  · intro p _
    omega

theorem P_eq_primorial :
    let smallPrimes (Y : ℕ) : Finset ℕ :=
      (Finset.Icc 1 Y).filter Nat.Prime
    let smallPrimeProduct (Y : ℕ) : ℕ :=
      ∏ p ∈ smallPrimes Y, p
    ∀ (Y : ℕ),
    smallPrimeProduct Y = primorial Y := by
  intro smallPrimes smallPrimeProduct Y
  unfold smallPrimeProduct smallPrimes primorial
  apply Finset.prod_congr
  · ext p
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
    constructor
    · rintro ⟨⟨_, hpY⟩, hpprime⟩
      exact ⟨by omega, hpprime⟩
    · rintro ⟨hpY, hpprime⟩
      have h1 : 1 ≤ p := hpprime.one_le
      exact ⟨⟨h1, by omega⟩, hpprime⟩
  · intros; rfl

theorem P_le_four_pow :
    let smallPrimes (Y : ℕ) : Finset ℕ :=
      (Finset.Icc 1 Y).filter Nat.Prime
    let smallPrimeProduct (Y : ℕ) : ℕ :=
      ∏ p ∈ smallPrimes Y, p
    ∀ (Y : ℕ),
    smallPrimeProduct Y ≤ 4 ^ Y := by
  intro smallPrimes smallPrimeProduct Y
  rw [show smallPrimeProduct Y = primorial Y from P_eq_primorial Y]
  exact primorial_le_four_pow Y

theorem A_le_four_pow :
    let smallPrimes (Y : ℕ) : Finset ℕ :=
      (Finset.Icc 1 Y).filter Nat.Prime
    let predecessorProduct (Y : ℕ) : ℕ :=
      ∏ p ∈ smallPrimes Y, (p - 1)
    ∀ (Y : ℕ),
    predecessorProduct Y ≤ 4 ^ Y := by
  intro smallPrimes predecessorProduct Y
  exact (A_le_P Y).trans (P_le_four_pow Y)

theorem Q_dvd_U :
    let largeFactors (Y U : ℕ) : Finset ℕ :=
      U.primeFactors.filter fun q => Y < q
    let largePrimeProduct (Y U : ℕ) : ℕ :=
      ∏ q ∈ largeFactors Y U, q
    ∀ (Y U : ℕ) (_hU : U ≠ 0),
    largePrimeProduct Y U ∣ U := by
  intro largeFactors largePrimeProduct Y U _hU
  unfold largePrimeProduct largeFactors

  refine dvd_trans ?_ (Nat.prod_primeFactors_dvd U)
  exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)

theorem primeFactors_Q :
    let largeFactors (Y U : ℕ) : Finset ℕ :=
      U.primeFactors.filter fun q => Y < q
    let largePrimeProduct (Y U : ℕ) : ℕ :=
      ∏ q ∈ largeFactors Y U, q
    ∀ (Y U : ℕ) (_hU : U ≠ 0),
    (largePrimeProduct Y U).primeFactors = largeFactors Y U := by
  intro largeFactors largePrimeProduct Y U _hU
  unfold largePrimeProduct
  apply Nat.primeFactors_prod
  intro q hq
  simp only [largeFactors] at hq
  exact Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1

theorem primeFactors_P :
    let smallPrimes (Y : ℕ) : Finset ℕ :=
      (Finset.Icc 1 Y).filter Nat.Prime
    let smallPrimeProduct (Y : ℕ) : ℕ :=
      ∏ p ∈ smallPrimes Y, p
    ∀ (Y : ℕ),
    (smallPrimeProduct Y).primeFactors = smallPrimes Y := by
  intro smallPrimes smallPrimeProduct Y
  unfold smallPrimeProduct
  apply Nat.primeFactors_prod
  intro p hp
  simp only [smallPrimes] at hp
  exact (Finset.mem_filter.mp hp).2

theorem primeFactors_b :
    let smallPrimes (Y : ℕ) : Finset ℕ :=
      (Finset.Icc 1 Y).filter Nat.Prime
    let smallPrimeProduct (Y : ℕ) : ℕ :=
      ∏ p ∈ smallPrimes Y, p
    let largeFactors (Y U : ℕ) : Finset ℕ :=
      U.primeFactors.filter fun q => Y < q
    let largePrimeProduct (Y U : ℕ) : ℕ :=
      ∏ q ∈ largeFactors Y U, q
    ∀ (Y U : ℕ) (hU_pos : 0 < U) (_hU_dvd : largePrimeProduct Y U ∣ U),
    (smallPrimeProduct Y * U * largePrimeProduct Y U).primeFactors = smallPrimes Y ∪ largeFactors Y U := by
  intro smallPrimes smallPrimeProduct largeFactors largePrimeProduct Y U hU_pos _hU_dvd
  have hU_ne : U ≠ 0 := Nat.pos_iff_ne_zero.mp hU_pos
  have hP_ne : smallPrimeProduct Y ≠ 0 := Nat.pos_iff_ne_zero.mp (P_pos Y)
  have hQ_ne : largePrimeProduct Y U ≠ 0 := Nat.pos_iff_ne_zero.mp (Q_pos Y U)
  have hPU_ne : smallPrimeProduct Y * U ≠ 0 := mul_ne_zero hP_ne hU_ne
  rw [Nat.primeFactors_mul hPU_ne hQ_ne, Nat.primeFactors_mul hP_ne hU_ne,
    primeFactors_P, primeFactors_Q Y U hU_ne]
  ext r
  simp only [Finset.mem_union]
  constructor
  · rintro ((hr | hr) | hr)
    · exact Or.inl hr
    ·
      have hrp : r.Prime := Nat.prime_of_mem_primeFactors hr
      have hrU : r ∣ U := Nat.dvd_of_mem_primeFactors hr
      by_cases hY : Y < r
      · refine Or.inr ?_
        simp only [largeFactors]
        exact Finset.mem_filter.mpr ⟨hr, hY⟩
      · refine Or.inl ?_
        simp only [smallPrimes]
        push Not at hY
        have h1 : 1 ≤ r := hrp.one_le
        exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨h1, hY⟩, hrp⟩
    · exact Or.inr hr
  · rintro (hr | hr)
    · exact Or.inl (Or.inl hr)
    · exact Or.inr hr

theorem P_div_A_eq_primeEulerProdNat :
    let primeEulerProdNat (Y : ℕ) : ℝ :=
      ∏ p ∈ (Finset.Icc 1 Y).filter Nat.Prime, ((p : ℝ) / (p - 1))
    let smallPrimes (Y : ℕ) : Finset ℕ :=
      (Finset.Icc 1 Y).filter Nat.Prime
    let smallPrimeProduct (Y : ℕ) : ℕ :=
      ∏ p ∈ smallPrimes Y, p
    let predecessorProduct (Y : ℕ) : ℕ :=
      ∏ p ∈ smallPrimes Y, (p - 1)
    ∀ (Y : ℕ),
    (smallPrimeProduct Y : ℝ) / (predecessorProduct Y : ℝ) = primeEulerProdNat Y := by
  intro primeEulerProdNat smallPrimes smallPrimeProduct predecessorProduct Y
  unfold smallPrimeProduct predecessorProduct primeEulerProdNat
  rw [show ((Finset.Icc 1 Y).filter Nat.Prime) = smallPrimes Y from rfl]
  rw [Nat.cast_prod, Nat.cast_prod]
  rw [← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  simp only [smallPrimes] at hp
  rcases Finset.mem_filter.mp hp with ⟨_, hpprime⟩
  have h1 : 1 ≤ p := hpprime.one_le
  rw [Nat.cast_sub h1]
  push_cast
  rfl

theorem smallPrimes_disjoint_largeFactors :
    let smallPrimes (Y : ℕ) : Finset ℕ :=
      (Finset.Icc 1 Y).filter Nat.Prime
    let largeFactors (Y U : ℕ) : Finset ℕ :=
      U.primeFactors.filter fun q => Y < q
    ∀ (Y U : ℕ),
    Disjoint (smallPrimes Y) (largeFactors Y U) := by
  intro smallPrimes largeFactors Y U
  rw [Finset.disjoint_left]
  intro p hp_small hp_large
  simp only [smallPrimes, Finset.mem_filter, Finset.mem_Icc] at hp_small
  simp only [largeFactors, Finset.mem_filter] at hp_large
  have h1 : p ≤ Y := hp_small.1.2
  have h2 : Y < p := hp_large.2
  omega

theorem prod_largeFactors_eq_Q :
    let largeFactors (Y U : ℕ) : Finset ℕ :=
      U.primeFactors.filter fun q => Y < q
    let largePrimeProduct (Y U : ℕ) : ℕ :=
      ∏ q ∈ largeFactors Y U, q
    ∀ (Y U : ℕ),
    ∏ q ∈ largeFactors Y U, q = largePrimeProduct Y U := by
  intro largeFactors largePrimeProduct Y U
  exact rfl

theorem prod_smallPrimes_eq_P :
    let smallPrimes (Y : ℕ) : Finset ℕ :=
      (Finset.Icc 1 Y).filter Nat.Prime
    let smallPrimeProduct (Y : ℕ) : ℕ :=
      ∏ p ∈ smallPrimes Y, p
    ∀ (Y : ℕ),
    ∏ p ∈ smallPrimes Y, p = smallPrimeProduct Y := by
  intro smallPrimes smallPrimeProduct Y
  exact rfl

theorem prod_smallPrimes_sub_one_eq_A :
    let smallPrimes (Y : ℕ) : Finset ℕ :=
      (Finset.Icc 1 Y).filter Nat.Prime
    let predecessorProduct (Y : ℕ) : ℕ :=
      ∏ p ∈ smallPrimes Y, (p - 1)
    ∀ (Y : ℕ),
    ∏ p ∈ smallPrimes Y, (p - 1) = predecessorProduct Y := by
  intro smallPrimes predecessorProduct Y
  exact rfl

theorem totient_P_mul_U_mul_Q :
    let smallPrimes (Y : ℕ) : Finset ℕ :=
      (Finset.Icc 1 Y).filter Nat.Prime
    let smallPrimeProduct (Y : ℕ) : ℕ :=
      ∏ p ∈ smallPrimes Y, p
    let predecessorProduct (Y : ℕ) : ℕ :=
      ∏ p ∈ smallPrimes Y, (p - 1)
    let largeFactors (Y U : ℕ) : Finset ℕ :=
      U.primeFactors.filter fun q => Y < q
    let largePrimeProduct (Y U : ℕ) : ℕ :=
      ∏ q ∈ largeFactors Y U, q
    ∀ (Y U : ℕ) (hU : 0 < U),
    Nat.totient (smallPrimeProduct Y * U * largePrimeProduct Y U) =
      predecessorProduct Y * U * ∏ q ∈ largeFactors Y U, (q - 1) := by
  intro smallPrimes smallPrimeProduct predecessorProduct largeFactors largePrimeProduct Y U hU
  have hkey := Nat.totient_mul_prod_primeFactors (smallPrimeProduct Y * U * largePrimeProduct Y U)
  rw [primeFactors_b Y U hU (Q_dvd_U Y U hU.ne'),
    Finset.prod_union (smallPrimes_disjoint_largeFactors Y U),
    Finset.prod_union (smallPrimes_disjoint_largeFactors Y U),
    prod_smallPrimes_eq_P, prod_largeFactors_eq_Q,
    prod_smallPrimes_sub_one_eq_A] at hkey
  apply Nat.eq_of_mul_eq_mul_right (Nat.mul_pos (P_pos Y) (Q_pos Y U))
  rw [hkey]
  ring

theorem totient_Q :
    let largeFactors (Y U : ℕ) : Finset ℕ :=
      U.primeFactors.filter fun q => Y < q
    let largePrimeProduct (Y U : ℕ) : ℕ :=
      ∏ q ∈ largeFactors Y U, q
    ∀ (Y U : ℕ) (hU : U ≠ 0),
    Nat.totient (largePrimeProduct Y U) = ∏ q ∈ largeFactors Y U, (q - 1) := by
  intro largeFactors largePrimeProduct Y U hU
  have hkey := Nat.totient_mul_prod_primeFactors (largePrimeProduct Y U)
  rw [primeFactors_Q Y U hU, prod_largeFactors_eq_Q] at hkey
  apply Nat.eq_of_mul_eq_mul_right (Q_pos Y U)
  rw [hkey, mul_comm]

theorem composite_collision :
    let smallPrimes (Y : ℕ) : Finset ℕ :=
      (Finset.Icc 1 Y).filter Nat.Prime
    let smallPrimeProduct (Y : ℕ) : ℕ :=
      ∏ p ∈ smallPrimes Y, p
    let predecessorProduct (Y : ℕ) : ℕ :=
      ∏ p ∈ smallPrimes Y, (p - 1)
    let largeFactors (Y U : ℕ) : Finset ℕ :=
      U.primeFactors.filter fun q => Y < q
    let largePrimeProduct (Y U : ℕ) : ℕ :=
      ∏ q ∈ largeFactors Y U, q
    ∀ (Y N : ℕ) (hN : 0 < N)
    (hcop : N.Coprime (Nat.totient N)) (hA : predecessorProduct Y ∣ Nat.totient N),
    let U := Nat.totient N / predecessorProduct Y
    Nat.totient (N * largePrimeProduct Y U) = Nat.totient (smallPrimeProduct Y * U * largePrimeProduct Y U) := by
  intro smallPrimes smallPrimeProduct predecessorProduct largeFactors largePrimeProduct Y N hN hcop hA
  dsimp only
  let U := Nat.totient N / predecessorProduct Y
  have hAU : predecessorProduct Y * U = Nat.totient N := Nat.mul_div_cancel' hA
  have hU : 0 < U := Nat.div_pos (Nat.le_of_dvd (Nat.totient_pos.mpr hN) hA)
    (A_pos Y)
  have hUd : U ∣ Nat.totient N := by
    rw [← hAU]
    exact dvd_mul_left _ _
  have hQcop : N.Coprime (largePrimeProduct Y U) :=
    hcop.of_dvd_right ((Q_dvd_U Y U hU.ne').trans hUd)
  change Nat.totient (N * largePrimeProduct Y U) = Nat.totient (smallPrimeProduct Y * U * largePrimeProduct Y U)
  rw [Nat.totient_mul hQcop, totient_Q Y U hU.ne',
    totient_P_mul_U_mul_Q Y U hU, hAU]

theorem composite_collision_ratio :
    let primeEulerProdNat (Y : ℕ) : ℝ :=
      ∏ p ∈ (Finset.Icc 1 Y).filter Nat.Prime, ((p : ℝ) / (p - 1))
    let smallPrimes (Y : ℕ) : Finset ℕ :=
      (Finset.Icc 1 Y).filter Nat.Prime
    let smallPrimeProduct (Y : ℕ) : ℕ :=
      ∏ p ∈ smallPrimes Y, p
    let predecessorProduct (Y : ℕ) : ℕ :=
      ∏ p ∈ smallPrimes Y, (p - 1)
    let largeFactors (Y U : ℕ) : Finset ℕ :=
      U.primeFactors.filter fun q => Y < q
    let largePrimeProduct (Y U : ℕ) : ℕ :=
      ∏ q ∈ largeFactors Y U, q
    ∀ (Y N : ℕ) (hN : 0 < N)
    (hA : predecessorProduct Y ∣ Nat.totient N),
    let U := Nat.totient N / predecessorProduct Y
    ((smallPrimeProduct Y * U * largePrimeProduct Y U : ℕ) : ℝ) / (N * largePrimeProduct Y U : ℕ) =
      primeEulerProdNat Y * ((Nat.totient N : ℝ) / N) := by
  intro primeEulerProdNat smallPrimes smallPrimeProduct predecessorProduct largeFactors largePrimeProduct Y N hN hA
  dsimp only
  let U := Nat.totient N / predecessorProduct Y
  have hAU : predecessorProduct Y * U = Nat.totient N := Nat.mul_div_cancel' hA
  have hAU' : (predecessorProduct Y : ℝ) * U = Nat.totient N := by exact_mod_cast hAU
  have hAR : (predecessorProduct Y : ℝ) ≠ 0 := by exact_mod_cast (A_pos Y).ne'
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hQR : (largePrimeProduct Y U : ℝ) ≠ 0 := by exact_mod_cast (Q_pos Y U).ne'
  change ((smallPrimeProduct Y * U * largePrimeProduct Y U : ℕ) : ℝ) / (N * largePrimeProduct Y U : ℕ) = _
  rw [← (show (smallPrimeProduct Y : ℝ)/(predecessorProduct Y : ℝ)=primeEulerProdNat Y from P_div_A_eq_primeEulerProdNat Y)]
  push_cast
  rw [← hAU']
  field_simp

theorem composite_collision_size :
    let smallPrimes (Y : ℕ) : Finset ℕ :=
      (Finset.Icc 1 Y).filter Nat.Prime
    let predecessorProduct (Y : ℕ) : ℕ :=
      ∏ p ∈ smallPrimes Y, (p - 1)
    let largeFactors (Y U : ℕ) : Finset ℕ :=
      U.primeFactors.filter fun q => Y < q
    let largePrimeProduct (Y U : ℕ) : ℕ :=
      ∏ q ∈ largeFactors Y U, q
    ∀ (Y N : ℕ) (hN : 0 < N)
    (hA : predecessorProduct Y ∣ Nat.totient N),
    let U := Nat.totient N / predecessorProduct Y
    Nat.totient (N * largePrimeProduct Y U) ≤ N ^ 2 := by
  intro smallPrimes predecessorProduct largeFactors largePrimeProduct Y N hN hA
  dsimp only
  let U := Nat.totient N / predecessorProduct Y
  have hU : 0 < U := Nat.div_pos (Nat.le_of_dvd (Nat.totient_pos.mpr hN) hA)
    (A_pos Y)
  have hQ : largePrimeProduct Y U ≤ U := Nat.le_of_dvd hU (Q_dvd_U Y U hU.ne')
  calc
    Nat.totient (N * largePrimeProduct Y U) ≤ N * largePrimeProduct Y U := Nat.totient_le _
    _ ≤ N * N := Nat.mul_le_mul_left N
      (hQ.trans ((Nat.div_le_self _ _).trans (Nat.totient_le N)))
    _ = N ^ 2 := by ring

theorem totient_prod_primes (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p) :
    Nat.totient (∏ p ∈ S, p) = ∏ p ∈ S, (p - 1) := by
  have hpos : 0 < ∏ p ∈ S, p := Finset.prod_pos fun p hp => (hS p hp).pos
  have h := Nat.totient_mul_prod_primeFactors (∏ p ∈ S, p)
  rw [Nat.primeFactors_prod hS] at h
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [h, mul_comm]

theorem dyadic_prime_coprime_sub_one {T p q : ℕ} (hT : 2 ≤ T)
    (hp : p.Prime) (hq : q.Prime) (hTp : T < p) (hqT : q ≤ 2 * T) :
    p.Coprime (q - 1) := by
  apply hp.coprime_iff_not_dvd.mpr
  intro hdiv
  have hp2 : p ≠ 2 := by omega
  have hcop : Nat.Coprime 2 p := Nat.prime_two.coprime_iff_not_dvd.mpr
    (by intro hd; have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp hd; omega)
  have hq2 : q ≠ 2 := by
    intro heq
    subst q
    norm_num at hdiv
    omega
  have heven : 2 ∣ q - 1 := even_iff_two_dvd.mp (hq.even_sub_one hq2)
  have hboth : 2 * p ∣ q - 1 := hcop.mul_dvd_of_dvd_of_dvd heven hdiv
  have hle := Nat.le_of_dvd (by have := hq.two_le; omega : 0 < q - 1) hboth
  omega

theorem dyadic_product_coprime_totient (T : ℕ) (S : Finset ℕ) (hT : 2 ≤ T)
    (hS : ∀ p ∈ S, p.Prime ∧ T < p ∧ p ≤ 2 * T) :
    (∏ p ∈ S, p).Coprime (Nat.totient (∏ p ∈ S, p)) := by
  rw [totient_prod_primes S fun p hp => (hS p hp).1]
  apply Nat.Coprime.prod_left
  intro p hp
  apply Nat.Coprime.prod_right
  intro q hq
  exact dyadic_prime_coprime_sub_one hT (hS p hp).1 (hS q hq).1
    (hS p hp).2.1 (hS q hq).2.2

theorem A_primeFactorsList_length_le :
    let smallPrimes (Y : ℕ) : Finset ℕ :=
      (Finset.Icc 1 Y).filter Nat.Prime
    let predecessorProduct (Y : ℕ) : ℕ :=
      ∏ p ∈ smallPrimes Y, (p - 1)
    ∀ (Y : ℕ),
    (predecessorProduct Y).primeFactorsList.length ≤ 2 * Y := by
  intro smallPrimes predecessorProduct Y
  apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
  calc
    2 ^ (predecessorProduct Y).primeFactorsList.length ≤ (predecessorProduct Y).primeFactorsList.prod :=
      List.pow_card_le_prod _ _ fun p hp => (Nat.prime_of_mem_primeFactorsList hp).two_le
    _ = predecessorProduct Y := Nat.prod_primeFactorsList (A_pos Y).ne'
    _ ≤ 4 ^ Y := A_le_four_pow Y
    _ = 2 ^ (2 * Y) := by rw [pow_mul]; norm_num

theorem A_primeFactorsList_mem_le :
    let smallPrimes (Y : ℕ) : Finset ℕ :=
      (Finset.Icc 1 Y).filter Nat.Prime
    let predecessorProduct (Y : ℕ) : ℕ :=
      ∏ p ∈ smallPrimes Y, (p - 1)
    ∀ {Y p : ℕ} (hp : p ∈ (predecessorProduct Y).primeFactorsList),
    p ≤ Y := by
  intro smallPrimes predecessorProduct Y p hp
  have hpp := Nat.prime_of_mem_primeFactorsList hp
  have hd := Nat.dvd_of_mem_primeFactorsList hp
  unfold predecessorProduct at hd
  obtain ⟨q, hq, hpq⟩ := (hpp.prime.dvd_finsetProd_iff fun q => q - 1).mp hd
  have hqY := (Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1).2
  have hqprime := (Finset.mem_filter.mp hq).2
  exact (Nat.le_of_dvd (by have := hqprime.two_le; omega) hpq).trans (by omega)

theorem select_dyadic_primes (T : ℕ) (L : List ℕ)
    (hsupply : ∀ q ∈ L, L.length ≤ ((Finset.Ioc T (2 * T)).filter
      (fun p => p.Prime ∧ p % q = 1 % q)).card) :
    ∃ S : Finset ℕ, S.card = L.length ∧
      (∀ p ∈ S, p.Prime ∧ T < p ∧ p ≤ 2 * T) ∧
      L.prod ∣ ∏ p ∈ S, (p - 1) := by
  classical
  induction L with
  | nil => exact ⟨∅, by simp, by simp, by simp⟩
  | cons q L ih =>
    obtain ⟨S, hcard, hS, hdiv⟩ := ih (fun r hr =>
      (Nat.le_succ L.length).trans (hsupply r (List.mem_cons_of_mem q hr)))
    have hlt : S.card < ((Finset.Ioc T (2 * T)).filter
        (fun p => p.Prime ∧ p % q = 1 % q)).card := by
      have h := hsupply q List.mem_cons_self
      simpa only [hcard, List.length_cons] using Nat.lt_of_lt_of_le
        (Nat.lt_succ_self L.length) h
    obtain ⟨p, hp, hpS⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    obtain ⟨hpI, hpp, hmod⟩ := Finset.mem_filter.mp hp
    obtain ⟨hTp, hpT⟩ := Finset.mem_Ioc.mp hpI
    have hqd : q ∣ p - 1 :=
      (Nat.modEq_iff_dvd' hpp.one_le).mp (show 1 ≡ p [MOD q] from hmod.symm)
    refine ⟨insert p S, by simp [hpS, hcard], ?_, ?_⟩
    · intro r hr
      rcases Finset.mem_insert.mp hr with rfl | hr
      · exact ⟨hpp, hTp, hpT⟩
      · exact hS r hr
    · rw [List.prod_cons, Finset.prod_insert hpS]
      exact Nat.mul_dvd_mul hqd hdiv

theorem exists_dyadic_totient_multiple :
    let smallPrimes (Y : ℕ) : Finset ℕ :=
      (Finset.Icc 1 Y).filter Nat.Prime
    let predecessorProduct (Y : ℕ) : ℕ :=
      ∏ p ∈ smallPrimes Y, (p - 1)
    ∀ (Y T : ℕ) (hT : 2 ≤ T)
    (hsupply : ∀ q : ℕ, q.Prime → q ≤ Y →
      2 * Y ≤ ((Finset.Ioc T (2 * T)).filter
        (fun p => p.Prime ∧ p % q = 1 % q)).card),
    ∃ S : Finset ℕ, S.card ≤ 2 * Y ∧
      (∀ p ∈ S, p.Prime ∧ T < p ∧ p ≤ 2 * T) ∧
      predecessorProduct Y ∣ Nat.totient (∏ p ∈ S, p) ∧
      (∏ p ∈ S, p).Coprime (Nat.totient (∏ p ∈ S, p)) := by
  intro smallPrimes predecessorProduct Y T hT hsupply
  obtain ⟨S, hcard, hS, hdiv⟩ := select_dyadic_primes T (predecessorProduct Y).primeFactorsList
    (fun q hq => (A_primeFactorsList_length_le Y).trans
      (hsupply q (Nat.prime_of_mem_primeFactorsList hq) (A_primeFactorsList_mem_le hq)))
  refine ⟨S, hcard ▸ A_primeFactorsList_length_le Y, hS, ?_,
    dyadic_product_coprime_totient T S hT hS⟩
  rw [totient_prod_primes S fun p hp => (hS p hp).1]
  rwa [Nat.prod_primeFactorsList (A_pos Y).ne'] at hdiv

theorem dyadic_totient_ratio_lower (T : ℕ) (S : Finset ℕ) (hT : 1 ≤ T)
    (hS : ∀ p ∈ S, p.Prime ∧ T < p) :
    1 - (S.card : ℝ) / T ≤
      (Nat.totient (∏ p ∈ S, p) : ℝ) / (∏ p ∈ S, p : ℕ) := by
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  rw [totient_prod_primes S fun p hp => (hS p hp).1]
  push_cast
  rw [← Finset.prod_div_distrib]
  have hbase : (0 : ℝ) ≤ 1 - 1 / (T : ℝ) := by
    have hTone : (1 : ℝ) ≤ T := by exact_mod_cast hT
    exact sub_nonneg.mpr ((div_le_one hTpos).mpr hTone)
  calc
    1 - (S.card : ℝ) / T ≤ (1 - 1 / (T : ℝ)) ^ S.card := by
      have h := one_add_mul_le_pow (show (-2 : ℝ) ≤ -(1 / (T : ℝ)) by linarith) S.card
      simpa only [mul_neg, mul_one_div, ← sub_eq_add_neg] using h
    _ = ∏ _p ∈ S, (1 - 1 / (T : ℝ)) := by rw [Finset.prod_const]
    _ ≤ ∏ p ∈ S, ((p : ℝ) - 1) / p := by
      apply Finset.prod_le_prod (fun _ _ => hbase)
      intro p hp
      have hpR : (0 : ℝ) < p := by exact_mod_cast (hS p hp).1.pos
      have hTp : (T : ℝ) ≤ p := by exact_mod_cast (hS p hp).2.le
      have hle := one_div_le_one_div_of_le hTpos hTp
      rw [sub_div, div_self hpR.ne']
      linarith
    _ = ∏ p ∈ S, ((p - 1 : ℕ) : ℝ) / p := by
      apply Finset.prod_congr rfl
      intro p hp
      rw [Nat.cast_sub (hS p hp).1.one_le, Nat.cast_one]

theorem primeEulerProdNat_nonneg :
    let primeEulerProdNat (Y : ℕ) : ℝ :=
      ∏ p ∈ (Finset.Icc 1 Y).filter Nat.Prime, ((p : ℝ) / (p - 1))
    ∀ (Y : ℕ),
    0 ≤ primeEulerProdNat Y := by
  intro primeEulerProdNat Y
  apply Finset.prod_nonneg
  intro p hp
  exact (one_le_prime_factor p (Finset.mem_filter.mp hp).2).trans' zero_le_one

theorem dyadic_collision_height :
    let primeEulerProdNat (Y : ℕ) : ℝ :=
      ∏ p ∈ (Finset.Icc 1 Y).filter Nat.Prime, ((p : ℝ) / (p - 1))
    let smallPrimes (Y : ℕ) : Finset ℕ :=
      (Finset.Icc 1 Y).filter Nat.Prime
    let smallPrimeProduct (Y : ℕ) : ℕ :=
      ∏ p ∈ smallPrimes Y, p
    let predecessorProduct (Y : ℕ) : ℕ :=
      ∏ p ∈ smallPrimes Y, (p - 1)
    let largeFactors (Y U : ℕ) : Finset ℕ :=
      U.primeFactors.filter fun q => Y < q
    let largePrimeProduct (Y U : ℕ) : ℕ :=
      ∏ q ∈ largeFactors Y U, q
    let dyadicRatio (D k : ℕ) : ℝ :=
      primeEulerProdNat (k ^ D) * (1 - 2 * (k : ℝ) ^ D / (2 : ℝ) ^ k)
    ∀ [supply : Fact H2] (D : ℕ),
    ∀ᶠ k : ℕ in atTop,
      ∃ a b n : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ 1 ≤ n ∧
        Nat.totient a = n ∧ Nat.totient b = n ∧
        dyadicRatio D k ≤ (b : ℝ) / a ∧
        (n : ℝ) ≤ Real.exp (12 * (k : ℝ) ^ (D + 1)) := by
  intro primeEulerProdNat smallPrimes smallPrimeProduct predecessorProduct largeFactors largePrimeProduct dyadicRatio supply D
  filter_upwards [supply.out D, eventually_ge_atTop 1] with k hk hk1
  let Y := k ^ D
  obtain ⟨j, hj, hsupply⟩ := hk
  have hkj : k ≤ j := by omega
  have hjk : j ≤ k + 1 := by omega
  let T := 2 ^ j
  have hT : 2 ≤ T := by
    change 2 ^ 1 ≤ 2 ^ j
    exact Nat.pow_le_pow_right (by decide) (hk1.trans hkj)
  obtain ⟨S, hcard, hS, hA, hcop⟩ :=
    exists_dyadic_totient_multiple Y T hT hsupply
  let N := ∏ p ∈ S, p
  let U := Nat.totient N / predecessorProduct Y
  let Q := largePrimeProduct Y U
  have hN : 0 < N := Finset.prod_pos fun p hp => (hS p hp).1.pos
  have hU : 0 < U := Nat.div_pos (Nat.le_of_dvd (Nat.totient_pos.mpr hN) hA)
    (A_pos Y)
  have hQ : 0 < Q := Q_pos Y U
  have ha : 0 < N * Q := Nat.mul_pos hN hQ
  have hb : 0 < smallPrimeProduct Y * U * Q :=
    Nat.mul_pos (Nat.mul_pos (P_pos Y) hU) hQ
  refine ⟨N * Q, smallPrimeProduct Y * U * Q, Nat.totient (N * Q),
    ha, hb, Nat.totient_pos.mpr ha, rfl,
    (composite_collision Y N hN hcop hA).symm, ?_, ?_⟩
  · have hratio := dyadic_totient_ratio_lower T S (by omega)
      (fun p hp => ⟨(hS p hp).1, (hS p hp).2.1⟩)
    have hcardR : (S.card : ℝ) ≤ 2 * (k : ℝ) ^ D := by exact_mod_cast hcard
    have hratio' : 1 - 2 * (k : ℝ) ^ D / (2 : ℝ) ^ k ≤ (Nat.totient N : ℝ) / N := by
      have h := div_le_div_of_nonneg_right hcardR
        (show (0 : ℝ) ≤ (2 : ℝ) ^ k by positivity)
      dsimp only [T] at hratio
      push_cast at hratio
      have small : (2 : ℝ)^k ≤ (2 : ℝ)^j := pow_le_pow_right₀ (by norm_num) hkj
      have shrink : (S.card : ℝ)/(2 : ℝ)^j ≤ (S.card : ℝ)/(2 : ℝ)^k :=
        div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity) small
      exact (sub_le_sub_left (shrink.trans h) 1).trans (by simpa only [N, Nat.cast_prod] using hratio)
    rw [composite_collision_ratio Y N hN hA]
    exact mul_le_mul_of_nonneg_left hratio' (primeEulerProdNat_nonneg Y)
  · have hNle : N ≤ (2 * T) ^ (2 * Y) := by
      apply (Finset.prod_le_pow_card S (fun p => p) (2 * T)
        (fun p hp => (hS p hp).2.2)).trans
      exact Nat.pow_le_pow_right (by omega) hcard
    have hnle := composite_collision_size Y N hN hA
    have hnR : (Nat.totient (N * Q) : ℝ) ≤ ((2 * T : ℕ) : ℝ) ^ (4 * Y) := by
      exact_mod_cast hnle.trans ((Nat.pow_le_pow_left hNle 2).trans_eq (by
        rw [← pow_mul]
        congr 1
        ring))
    have hlog2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at this
      exact this
    have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    have hlogT : Real.log ((2 * T : ℕ) : ℝ) = (j + 1 : ℝ) * Real.log 2 := by
      dsimp [T]
      push_cast
      rw [← pow_succ', Real.log_pow]
      norm_num
    have hpowpos : (0 : ℝ) < ((2 * T : ℕ) : ℝ) ^ (4 * Y) := by positivity
    apply hnR.trans
    rw [← Real.exp_log hpowpos, Real.exp_le_exp, Real.log_pow, hlogT]
    have hkD : 0 ≤ (k : ℝ) ^ D := by positivity
    have hjR : (j : ℝ) ≤ (k : ℝ)+1 := by exact_mod_cast hjk
    have h1 : ((j : ℝ) + 1) * Real.log 2 ≤ 3 * k := by
      have := mul_le_mul_of_nonneg_left hlog2 (show 0 ≤ (j:ℝ)+1 by positivity)
      linarith
    have h2 := mul_le_mul_of_nonneg_left h1 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hkD)
    dsimp [Y]
    push_cast
    rw [pow_succ]
    nlinarith

theorem dyadicRatio_tendsto :
    let primeEulerProdNat (Y : ℕ) : ℝ :=
      ∏ p ∈ (Finset.Icc 1 Y).filter Nat.Prime, ((p : ℝ) / (p - 1))
    let dyadicRatio (D k : ℕ) : ℝ :=
      primeEulerProdNat (k ^ D) * (1 - 2 * (k : ℝ) ^ D / (2 : ℝ) ^ k)
    ∀ [hm : Fact H1] (D : ℕ) (hD : 0 < D),
    Tendsto (fun k : ℕ => dyadicRatio D k / Real.log k) atTop
      (𝓝 (Real.exp Real.eulerMascheroniConstant * D)) := by
  intro primeEulerProdNat dyadicRatio hm D hD
  have hpow : Tendsto (fun k : ℕ => k ^ D) atTop atTop :=
    tendsto_pow_atTop hD.ne'
  have hmertens : Tendsto
      (fun k : ℕ => primeEulerProdNat (k ^ D) /
        (Real.exp Real.eulerMascheroniConstant * Real.log (k ^ D : ℕ))) atTop (𝓝 1) := by
    simpa only [Function.comp_def, Nat.floor_natCast, primeEulerProdNat] using
      hm.out.comp (tendsto_natCast_atTop_atTop.comp hpow)
  have hsmall : Tendsto (fun k : ℕ => 2 * (k : ℝ) ^ D / (2 : ℝ) ^ k) atTop (𝓝 0) := by
    simpa only [mul_zero, mul_div_assoc] using
      (tendsto_pow_const_div_const_pow_of_one_lt D (by norm_num : (1 : ℝ) < 2)).const_mul 2
  have h := (hmertens.mul ((tendsto_const_nhds (x := (1 : ℝ))).sub hsmall)).mul_const
    (Real.exp Real.eulerMascheroniConstant * D)
  simp only [sub_zero, one_mul] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 2] with k hk
  have hlog : Real.log (k : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (show 1 < k by omega))).ne'
  have hγ : Real.exp Real.eulerMascheroniConstant ≠ 0 := (Real.exp_pos _).ne'
  have hDR : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  simp only [dyadicRatio, Nat.cast_pow, Real.log_pow]
  field_simp

theorem heightRoot_tendsto :
    let heightRoot (d x : ℕ) : ℝ :=
      (Real.log (x : ℝ) / 12) ^ (d : ℝ)⁻¹
    ∀ (d : ℕ) (hd : 0 < d),
    Tendsto (heightRoot d) atTop atTop := by
  intro heightRoot d hd
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  exact (tendsto_rpow_atTop (inv_pos.mpr hdR)).comp
    ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).atTop_div_const
      (by norm_num : (0 : ℝ) < 12))

theorem heightIndex_tendsto :
    let heightRoot (d x : ℕ) : ℝ :=
      (Real.log (x : ℝ) / 12) ^ (d : ℝ)⁻¹
    let heightIndex (d x : ℕ) : ℕ := ⌊heightRoot d x⌋₊
    ∀ (d : ℕ) (hd : 0 < d),
    Tendsto (heightIndex d) atTop atTop := by
  intro heightRoot heightIndex d hd
  exact tendsto_nat_floor_atTop.comp (heightRoot_tendsto d hd)

theorem heightIndex_bound :
    let heightRoot (d x : ℕ) : ℝ :=
      (Real.log (x : ℝ) / 12) ^ (d : ℝ)⁻¹
    let heightIndex (d x : ℕ) : ℕ := ⌊heightRoot d x⌋₊
    ∀ (d : ℕ) (hd : 0 < d) (x : ℕ) (hx : 2 ≤ x),
    Real.exp (12 * (heightIndex d x : ℝ) ^ d) ≤ x := by
  intro heightRoot heightIndex d hd x hx
  have hxR : (1 : ℝ) < x := by exact_mod_cast (show 1 < x by omega)
  have hlog : 0 ≤ Real.log (x : ℝ) / 12 := by positivity [Real.log_pos hxR]
  have hfloor : (heightIndex d x : ℝ) ≤ heightRoot d x :=
    Nat.floor_le (Real.rpow_nonneg hlog _)
  have hpow : (heightRoot d x) ^ d = Real.log (x : ℝ) / 12 :=
    Real.rpow_inv_natCast_pow hlog hd.ne'
  calc
    Real.exp (12 * (heightIndex d x : ℝ) ^ d) ≤
        Real.exp (12 * (heightRoot d x) ^ d) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (Nat.cast_nonneg _) hfloor d) (by norm_num)
    _ = x := by
      rw [hpow, mul_div_cancel₀ _ (by norm_num : (12 : ℝ) ≠ 0)]
      exact Real.exp_log (zero_lt_one.trans hxR)

theorem loglog_nat_tendsto :
    Tendsto (fun x : ℕ => Real.log (Real.log (x : ℝ))) atTop atTop := by
  exact Real.tendsto_log_atTop.comp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

theorem log_heightIndex_tendsto :
    let R (x : ℕ) : ℝ :=
      ⨆ n ∈ {n | n ∈ Set.Icc 1 x ∧ ∃ m, Nat.totient m = n},
        let mmax := sSup {m | Nat.totient m = n}
        let mmin := sInf {m | Nat.totient m = n}
        (mmax : ℝ) / mmin
    let heightRoot (d x : ℕ) : ℝ :=
      (Real.log (x : ℝ) / 12) ^ (d : ℝ)⁻¹
    let heightIndex (d x : ℕ) : ℕ := ⌊heightRoot d x⌋₊
    ∀ (d : ℕ) (hd : 0 < d),
    Tendsto (fun x : ℕ => Real.log (heightIndex d x : ℝ) /
      Real.log (Real.log (x : ℝ))) atTop (𝓝 (d : ℝ)⁻¹) := by
  intro R heightRoot heightIndex d hd
  have ht := heightRoot_tendsto d hd
  have hf := (Asymptotics.isEquivalent_nat_floor (R := ℝ)).comp_tendsto ht
  have hflog := hf.log ht
  have hlogt := Real.tendsto_log_atTop.comp ht
  have hfloor : Tendsto (fun x : ℕ =>
      Real.log (heightIndex d x : ℝ) / Real.log (heightRoot d x)) atTop (𝓝 1) :=
    (Asymptotics.isEquivalent_iff_tendsto_one (hlogt.eventually_ne_atTop 0)).mp hflog
  have hconst : Tendsto (fun x : ℕ => Real.log 12 / Real.log (Real.log (x : ℝ)))
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop loglog_nat_tendsto
  have hroot : Tendsto (fun x : ℕ => Real.log (heightRoot d x) /
      Real.log (Real.log (x : ℝ))) atTop (𝓝 (d : ℝ)⁻¹) := by
    have h := ((tendsto_const_nhds (x := (1 : ℝ))).sub hconst).const_mul (d : ℝ)⁻¹
    simp only [sub_zero, mul_one] at h
    apply h.congr'
    filter_upwards [eventually_ge_atTop 2, loglog_nat_tendsto.eventually_ne_atTop 0]
      with x hx hll
    have hlog : 0 < Real.log (x : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < x by omega))
    dsimp only [heightRoot]
    rw [Real.log_rpow (by positivity), Real.log_div hlog.ne' (by norm_num)]
    field_simp
  have h := hfloor.mul hroot
  simp only [one_mul] at h
  apply h.congr'
  filter_upwards [hlogt.eventually_ne_atTop 0] with x hx
  exact div_mul_div_cancel₀ hx

theorem rescaled_dyadicRatio_tendsto :
    let primeEulerProdNat (Y : ℕ) : ℝ :=
      ∏ p ∈ (Finset.Icc 1 Y).filter Nat.Prime, ((p : ℝ) / (p - 1))
    let dyadicRatio (D k : ℕ) : ℝ :=
      primeEulerProdNat (k ^ D) * (1 - 2 * (k : ℝ) ^ D / (2 : ℝ) ^ k)
    let heightRoot (d x : ℕ) : ℝ :=
      (Real.log (x : ℝ) / 12) ^ (d : ℝ)⁻¹
    let heightIndex (d x : ℕ) : ℕ := ⌊heightRoot d x⌋₊
    ∀ [hm : Fact H1] (D : ℕ) (hD : 0 < D),
    Tendsto (fun x : ℕ => dyadicRatio D (heightIndex (D + 1) x) /
      Real.log (Real.log (x : ℝ))) atTop
      (𝓝 (Real.exp Real.eulerMascheroniConstant * D / (D + 1 : ℕ))) := by
  intro primeEulerProdNat dyadicRatio heightRoot heightIndex hm D hD
  have hi := heightIndex_tendsto (D + 1) (Nat.succ_pos D)
  have h := ((dyadicRatio_tendsto D hD).comp hi).mul
    (log_heightIndex_tendsto (D + 1) (Nat.succ_pos D))
  simp only [← div_eq_mul_inv] at h
  apply h.congr'
  filter_upwards [hi.eventually_ge_atTop 2] with x hx
  change 2 ≤ heightIndex (D + 1) x at hx
  have hlog : Real.log (heightIndex (D + 1) x : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (show 1 < heightIndex (D + 1) x by omega))).ne'
  exact div_mul_div_cancel₀ hlog

theorem collision_of_dyadic_supply [hm : Fact H1] [supply : Fact H2] :
    ∀ ε > 0, ∀ᶠ x : ℕ in atTop,
      ∃ a b n : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ 1 ≤ n ∧ n ≤ x ∧
        Nat.totient a = n ∧ Nat.totient b = n ∧
        (b : ℝ) / a ≥ (Real.exp Real.eulerMascheroniConstant - ε) *
          Real.log (Real.log x) := by
  intro ε hε
  let γ := Real.exp Real.eulerMascheroniConstant
  obtain ⟨D, hD⟩ := exists_nat_gt (max (γ / ε) 1)
  have hD1 : (1 : ℝ) < D := (le_max_right _ _).trans_lt hD
  have hDpos : 0 < D := by exact_mod_cast (zero_lt_one.trans hD1)
  have hgap : γ - ε < γ * D / (D + 1 : ℕ) := by
    have hbound : γ / ε < D := (le_max_left _ _).trans_lt hD
    have hmul : γ < (D : ℝ) * ε := (div_lt_iff₀ hε).mp hbound
    apply (lt_div_iff₀ (by positivity : (0 : ℝ) < (D + 1 : ℕ))).mpr
    push_cast
    nlinarith
  have hratio := (rescaled_dyadicRatio_tendsto D hDpos).eventually (lt_mem_nhds hgap)
  have hi := heightIndex_tendsto (D + 1) (Nat.succ_pos D)
  filter_upwards [hi.eventually (dyadic_collision_height D), hratio,
    eventually_ge_atTop 2, loglog_nat_tendsto.eventually_gt_atTop 0]
    with x hx hratio hx2 hll
  obtain ⟨a, b, n, ha, hb, hn, hφa, hφb, hba, hsize⟩ := hx
  have hnx : n ≤ x := by
    exact_mod_cast hsize.trans (heightIndex_bound (D + 1) (Nat.succ_pos D) x hx2)
  refine ⟨a, b, n, ha, hb, hn, hnx, hφa, hφb, ?_⟩
  exact ((le_div_iff₀ hll).mp hratio.le).trans hba

theorem R_ge_of_totient_collision :
    let R (x : ℕ) : ℝ :=
      ⨆ n ∈ {n | n ∈ Set.Icc 1 x ∧ ∃ m, Nat.totient m = n},
        let mmax := sSup {m | Nat.totient m = n}
        let mmin := sInf {m | Nat.totient m = n}
        (mmax : ℝ) / mmin
    ∀ {x a b n : ℕ}
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hn : 1 ≤ n) (hnx : n ≤ x)
    (hφa : Nat.totient a = n) (hφb : Nat.totient b = n),
    (b : ℝ) / a ≤ R x := by
  intro R x a b n ha hb hn hnx hφa hφb

  set A : Set ℕ := {m | Nat.totient m = n} with hA_def
  have hb_in : b ∈ A := hφb
  have ha_in : a ∈ A := hφa
  have hA_ne : A.Nonempty := ⟨b, hb_in⟩

  have hA_bdd : BddAbove A := by
    refine ⟨2 * n ^ 2, ?_⟩
    intro m hm
    have hm_pos : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with h0 | hpos
      · have hm' : Nat.totient m = n := hm
        rw [h0, Nat.totient_zero] at hm'; omega
      · exact hpos
    exact totient_preimage_bound hm_pos hm
  set mmax : ℕ := sSup A with hmmax_def
  set mmin : ℕ := sInf A with hmmin_def
  have hmmax_in : mmax ∈ A := Nat.sSup_mem hA_ne hA_bdd
  have hmmin_in : mmin ∈ A := Nat.sInf_mem hA_ne

  have hb_le_mmax : b ≤ mmax := le_csSup hA_bdd hb_in

  have hmmin_le_a : mmin ≤ a := Nat.sInf_le ha_in

  have hmmin_pos : 1 ≤ mmin := by
    rcases Nat.eq_zero_or_pos mmin with h0 | hpos
    · have : Nat.totient mmin = n := hmmin_in
      rw [h0, Nat.totient_zero] at this; omega
    · exact hpos
  have hmmax_pos : 1 ≤ mmax := le_trans hb hb_le_mmax

  have ha_pos_R : (0 : ℝ) < a := by exact_mod_cast ha
  have hmmin_pos_R : (0 : ℝ) < mmin := by exact_mod_cast hmmin_pos
  have hb_le_mmax_R : (b : ℝ) ≤ mmax := by exact_mod_cast hb_le_mmax
  have hmmin_le_a_R : (mmin : ℝ) ≤ a := by exact_mod_cast hmmin_le_a
  have hratio_ge : (b : ℝ) / a ≤ (mmax : ℝ) / mmin := by

    have h1 : (b : ℝ) / a ≤ (mmax : ℝ) / a :=
      div_le_div_of_nonneg_right hb_le_mmax_R (le_of_lt ha_pos_R)
    have hmmax_nn : (0 : ℝ) ≤ mmax := by exact_mod_cast Nat.zero_le _
    have h2 : (mmax : ℝ) / a ≤ (mmax : ℝ) / mmin :=
      div_le_div_of_nonneg_left hmmax_nn hmmin_pos_R hmmin_le_a_R
    linarith

  have hn_in_idx : n ∈ {n | n ∈ Set.Icc 1 x ∧ ∃ m, Nat.totient m = n} := by
    refine ⟨⟨hn, hnx⟩, b, hφb⟩

  have hbdd_outer :
      BddAbove (Set.range (fun (n' : ℕ) =>
        ⨆ (_ : n' ∈ {n : ℕ | n ∈ Set.Icc 1 x ∧ ∃ m, Nat.totient m = n}),
          let mmax' := sSup {m | Nat.totient m = n'}
          let mmin' := sInf {m | Nat.totient m = n'}
          (mmax' : ℝ) / mmin')) := by
    refine ⟨((2 * x ^ 2 : ℕ) : ℝ), ?_⟩
    rintro _ ⟨n', rfl⟩
    simp only
    by_cases hn'mem : n' ∈ {n : ℕ | n ∈ Set.Icc 1 x ∧ ∃ m, Nat.totient m = n}
    · rw [ciSup_pos hn'mem]
      obtain ⟨⟨hn'_pos, hn'_le_x⟩, m_w, hφm_w⟩ := hn'mem
      have hm_w_pos : 1 ≤ m_w := by
        rcases Nat.eq_zero_or_pos m_w with h0 | hpos
        · rw [h0, Nat.totient_zero] at hφm_w; omega
        · exact hpos
      set A' : Set ℕ := {m | Nat.totient m = n'} with hA'_def
      have hA'_ne : A'.Nonempty := ⟨m_w, hφm_w⟩
      have hA'_bdd : BddAbove A' := by
        refine ⟨2 * n' ^ 2, ?_⟩
        intro m hm
        have hm_pos : 1 ≤ m := by
          rcases Nat.eq_zero_or_pos m with h0 | hpos
          · have : Nat.totient m = n' := hm
            rw [h0, Nat.totient_zero] at this; omega
          · exact hpos
        exact totient_preimage_bound hm_pos hm
      set mmax' : ℕ := sSup A' with hmmax'_def
      set mmin' : ℕ := sInf A' with hmmin'_def
      have hmmax'_in : mmax' ∈ A' := Nat.sSup_mem hA'_ne hA'_bdd
      have hmmin'_in : mmin' ∈ A' := Nat.sInf_mem hA'_ne
      have hφmmax' : Nat.totient mmax' = n' := hmmax'_in
      have hφmmin' : Nat.totient mmin' = n' := hmmin'_in
      have hmmax'_pos : 1 ≤ mmax' := by
        rcases Nat.eq_zero_or_pos mmax' with h0 | hpos
        · rw [h0, Nat.totient_zero] at hφmmax'; omega
        · exact hpos
      have hmmin'_pos : 1 ≤ mmin' := by
        rcases Nat.eq_zero_or_pos mmin' with h0 | hpos
        · rw [h0, Nat.totient_zero] at hφmmin'; omega
        · exact hpos
      have hmmax'_le : mmax' ≤ 2 * n' ^ 2 := totient_preimage_bound hmmax'_pos hφmmax'
      have hmmax'_le_2xsq : mmax' ≤ 2 * x ^ 2 := by
        have : 2 * n' ^ 2 ≤ 2 * x ^ 2 :=
          Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hn'_le_x 2)
        omega

      have hmmin'_pos_R : (0 : ℝ) < mmin' := by exact_mod_cast hmmin'_pos
      have hmmax'_nn_R : (0 : ℝ) ≤ mmax' := by exact_mod_cast Nat.zero_le _
      have h1' : (mmax' : ℝ) / mmin' ≤ mmax' := by
        rw [div_le_iff₀ hmmin'_pos_R]
        have : (1 : ℝ) ≤ (mmin' : ℝ) := by exact_mod_cast hmmin'_pos
        nlinarith
      have h2' : (mmax' : ℝ) ≤ ((2 * x ^ 2 : ℕ) : ℝ) := by exact_mod_cast hmmax'_le_2xsq
      linarith
    · rw [ciSup_neg hn'mem]
      simp only [Real.sSup_empty]
      exact_mod_cast Nat.zero_le _

  have hR_ge : (mmax : ℝ) / mmin ≤ R x := by
    unfold R
    have h_inner_eq :
        (⨆ (_ : n ∈ {n : ℕ | n ∈ Set.Icc 1 x ∧ ∃ m, Nat.totient m = n}),
            let mmax' := sSup {m | Nat.totient m = n}
            let mmin' := sInf {m | Nat.totient m = n}
            (mmax' : ℝ) / mmin') = (mmax : ℝ) / mmin :=
      ciSup_pos hn_in_idx
    rw [← h_inner_eq]
    exact le_ciSup hbdd_outer n
  exact le_trans hratio_ge hR_ge

theorem R_lower_bound :
    let R (x : ℕ) : ℝ :=
      ⨆ n ∈ {n | n ∈ Set.Icc 1 x ∧ ∃ m, Nat.totient m = n},
        let mmax := sSup {m | Nat.totient m = n}
        let mmin := sInf {m | Nat.totient m = n}
        (mmax : ℝ) / mmin
    ∀ [hm : Fact H1] [supply : Fact H2],
    ∀ ε > 0, ∀ᶠ x : ℕ in atTop,
      R x ≥ (Real.exp Real.eulerMascheroniConstant - ε) * Real.log (Real.log x) := by
  intro R hm supply
  intro ε hε
  filter_upwards [collision_of_dyadic_supply ε hε, Filter.eventually_ge_atTop 1]
    with x hx hx1
  obtain ⟨a, b, n, ha, hb, hn, hnx, hφa, hφb, hba⟩ := hx
  have hR_ge : (b : ℝ) / a ≤ R x :=
    R_ge_of_totient_collision ha hb hn hnx hφa hφb
  linarith

theorem totient_fibre_extremes :
    let R (x : ℕ) : ℝ :=
      ⨆ n ∈ {n | n ∈ Set.Icc 1 x ∧ ∃ m, Nat.totient m = n},
        let mmax := sSup {m | Nat.totient m = n}
        let mmin := sInf {m | Nat.totient m = n}
        (mmax : ℝ) / mmin
    ∀ [hm : Fact H1] [supply : Fact H2],
    Tendsto
      (fun x : ℕ => R x / (Real.exp Real.eulerMascheroniConstant * Real.log (Real.log x)))
      atTop (𝓝 1) := by
  intro R hm supply
  rw [Metric.tendsto_atTop]
  intro δ hδ
  set γc : ℝ := Real.exp Real.eulerMascheroniConstant with hγc_def
  have hγc_pos : 0 < γc := Real.exp_pos _
  set ε : ℝ := δ * γc / 2 with hε_def
  have hε_pos : 0 < ε := by positivity
  have hev := (R_upper_bound ε hε_pos).and
    ((R_lower_bound ε hε_pos).and (Filter.eventually_ge_atTop 3))
  rw [Filter.eventually_atTop] at hev
  obtain ⟨N, hN⟩ := hev
  refine ⟨N, fun x hxN => ?_⟩
  obtain ⟨hxu, hxl, hx3⟩ := hN x hxN
  change R x ≤ (Real.exp Real.eulerMascheroniConstant + ε) * Real.log (Real.log (x : ℝ)) at hxu
  change (Real.exp Real.eulerMascheroniConstant - ε) * Real.log (Real.log (x : ℝ)) ≤ R x at hxl
  have hx3R : (3 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx3
  have hlogx_gt_one : 1 < Real.log x := by
    have hle : Real.log 3 ≤ Real.log x := Real.log_le_log (by norm_num) hx3R
    have hexp_lt_three : Real.exp 1 < 3 := by
      have := Real.exp_one_lt_d9
      linarith
    have hlog3 : 1 < Real.log 3 := by
      have h := Real.log_lt_log (Real.exp_pos _) hexp_lt_three
      simpa [Real.log_exp] using h
    linarith
  have hllogx_pos : 0 < Real.log (Real.log x) := Real.log_pos hlogx_gt_one
  set L : ℝ := Real.log (Real.log x) with hL_def
  have hdenom_pos : 0 < γc * L := mul_pos hγc_pos hllogx_pos
  rw [Real.dist_eq]
  have key : R x / (γc * L) - 1 = (R x - γc * L) / (γc * L) := by
    field_simp
  rw [key, abs_div, abs_of_pos hdenom_pos]
  have hub : R x - γc * L ≤ ε * L := by
    have h1 : (γc + ε) * L = γc * L + ε * L := by ring
    linarith
  have hlb : -(ε * L) ≤ R x - γc * L := by
    have h1 : (γc - ε) * L = γc * L - ε * L := by ring
    linarith
  have habs : |R x - γc * L| ≤ ε * L := abs_le.mpr ⟨hlb, hub⟩
  have hratio : |R x - γc * L| / (γc * L) ≤ ε * L / (γc * L) :=
    div_le_div_of_nonneg_right habs (le_of_lt hdenom_pos)
  have hsimp : ε * L / (γc * L) = ε / γc := by
    field_simp
  rw [hsimp] at hratio
  have hε_over_γc : ε / γc = δ / 2 := by
    rw [hε_def]
    field_simp
  rw [hε_over_γc] at hratio
  have hδ2_lt : δ / 2 < δ := by linarith
  exact lt_of_le_of_lt hratio hδ2_lt

theorem agree :
    let R (x : ℕ) : ℝ :=
      ⨆ n ∈ {n | n ∈ Set.Icc 1 x ∧ ∃ m, Nat.totient m = n},
        let mmax := sSup {m | Nat.totient m = n}
        let mmin := sInf {m | Nat.totient m = n}
        (mmax : ℝ) / mmin
    ∀ (x : ℕ) (fmax fmin : ℕ → ℕ)
    (hmax : ∀ n, (∃ m, Nat.totient m = n) → IsGreatest (Nat.totient ⁻¹' {n}) (fmax n))
    (hmin : ∀ n, (∃ m, Nat.totient m = n) → IsLeast (Nat.totient ⁻¹' {n}) (fmin n)),
    sSup { (fmax n : ℝ) / fmin n | (n : ℕ) (_ : n ≤ x) (_ : ∃ m, Nat.totient m = n) } =
      R x := by
  intro R x fmax fmin hmax hmin
  let good (n : ℕ) := n ∈ Set.Icc 1 x ∧ ∃ m, Nat.totient m = n
  let val (n : ℕ) : ℝ := (sSup {m : ℕ | Nat.totient m = n} : ℕ) /
    (sInf {m : ℕ | Nat.totient m = n} : ℕ)
  have hv (n : ℕ) (h : ∃ m, Nat.totient m = n) : val n = (fmax n : ℝ) / fmin n := by
    change ((sSup (Nat.totient ⁻¹' {n}) : ℕ) : ℝ) / (sInf (Nat.totient ⁻¹' {n}) : ℕ) = _
    rw [(hmax n h).csSup_eq, (hmin n h).csInf_eq]
  have hz : ∃ m, Nat.totient m = 0 := ⟨0, rfl⟩
  have hzero : fmax 0 = 0 := Nat.totient_eq_zero.mp (hmax 0 hz).1
  have hyes {n : ℕ} (h : good n) : (⨆ _ : good n, val n) = val n :=
    ciSup_pos (f := fun _ : good n => val n) h
  have hno {n : ℕ} (h : ¬good n) : (⨆ _ : good n, val n) = 0 :=
    (ciSup_neg (f := fun _ : good n => val n) h).trans Real.sSup_empty
  change sSup _ = sSup (Set.range (fun n : ℕ => ⨆ _ : good n, val n))
  congr 1
  ext y
  constructor
  · rintro ⟨n, hn, hf, rfl⟩
    refine ⟨n, ?_⟩
    by_cases hn0 : n = 0
    · subst n
      have hbad : ¬good 0 := by simp [good]
      exact (hno hbad).trans (by simp [hzero])
    · have hg : good n := ⟨⟨by omega, hn⟩, hf⟩
      exact (hyes hg).trans (hv n hf)
  · rintro ⟨n, rfl⟩
    by_cases hg : good n
    · exact ⟨n, hg.1.2, hg.2, (hv n hg.2).symm.trans (hyes hg).symm⟩
    · refine ⟨0, Nat.zero_le _, hz, ?_⟩
      exact (show (fmax 0 : ℝ) / fmin 0 = 0 by simp [hzero]).trans (hno hg).symm

theorem main : H1 → H2 → type_of% @Erdos694.erdos_694 := by
  intro hM hL fmax fmin hmax hmin
  letI : Fact H1 := ⟨hM⟩
  letI : Fact H2 := ⟨hL⟩
  let R (x : ℕ) : ℝ :=
    ⨆ n ∈ {n | n ∈ Set.Icc 1 x ∧ ∃ m, Nat.totient m = n},
      let mmax := sSup {m | Nat.totient m = n}
      let mmin := sInf {m | Nat.totient m = n}
      (mmax : ℝ) / mmin
  let E := Real.exp Real.eulerMascheroniConstant
  let L (x : ℕ) := Real.log (Real.log (x : ℝ))
  have h : Tendsto (fun x : ℕ => R x / (E * L x)) atTop (𝓝 1) := totient_fibre_extremes
  have h' : Tendsto (fun x => E * (R x / (E * L x) - 1)) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := E)).mul (h.sub (tendsto_const_nhds (x := (1 : ℝ))))
  refine ⟨_, h', ?_⟩
  filter_upwards [eventually_ge_atTop 3] with x hx
  have hx' : (3 : ℝ) ≤ x := by exact_mod_cast hx
  have hlog : 0 < L x := Real.log_pos ((Real.lt_log_iff_exp_lt (by linarith : 0 < (x : ℝ))).2
    (Real.exp_one_lt_three.trans_le hx'))
  have he : E ≠ 0 := (Real.exp_pos _).ne'
  rw [agree x fmax fmin hmax hmin]
  change R x = (E + E * (R x / (E * L x) - 1)) * L x
  field_simp [he, hlog.ne']
  <;> ring
end OMA.R_Erdos694_erdos_694_R2
