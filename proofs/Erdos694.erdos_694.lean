import FormalConjectures.ErdosProblems.«694»
import Mathlib

/-! Erdős 694. Finite prime products give collisions in Euler’s totient fibres.
Mertens’ product theorem supplies the leading constant. A common dyadic band
contains enough primes in every small prime modulus, using a coarse truncation
of Perron’s integral and a Siegel–Walfisz zero-free region. -/

section
/- Mertens' product and small prime moduli suffice for the asymptotic extrema of Euler's totient.
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

noncomputable def primeEulerProdNat (Y : ℕ) : ℝ :=
  ∏ p ∈ (Finset.Icc 1 Y).filter Nat.Prime, ((p : ℝ) / (p - 1))

noncomputable def R (x : ℕ) : ℝ :=
  ⨆ n ∈ {n | n ∈ Set.Icc 1 x ∧ ∃ m, Nat.totient m = n},
    let mmax := sSup {m | Nat.totient m = n}
    let mmin := sInf {m | Nat.totient m = n}
    (mmax : ℝ) / mmin

noncomputable def smallPrimes (Y : ℕ) : Finset ℕ :=
  (Finset.Icc 1 Y).filter Nat.Prime

noncomputable def predecessorProduct (Y : ℕ) : ℕ :=
  ∏ p ∈ smallPrimes Y, (p - 1)

noncomputable def smallPrimeProduct (Y : ℕ) : ℕ :=
  ∏ p ∈ smallPrimes Y, p

noncomputable def largeFactors (Y U : ℕ) : Finset ℕ :=
  U.primeFactors.filter fun q => Y < q

noncomputable def largePrimeProduct (Y U : ℕ) : ℕ :=
  ∏ q ∈ largeFactors Y U, q

noncomputable def dyadicRatio (D k : ℕ) : ℝ :=
  primeEulerProdNat (k ^ D) * (1 - 2 * (k : ℝ) ^ D / (2 : ℝ) ^ k)

noncomputable def heightRoot (d x : ℕ) : ℝ :=
  (Real.log (x : ℝ) / 12) ^ (d : ℝ)⁻¹

noncomputable def heightIndex (d x : ℕ) : ℕ := ⌊heightRoot d x⌋₊

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

/- An upper bound for totient fibers -/

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
    ∀ (m Y : ℕ) (_hm : m ≠ 0) (_hY : 1 ≤ Y),
    (m : ℝ) / Nat.totient m ≤
      primeEulerProdNat Y * (((Y + 1 : ℕ) : ℝ) / Y) ^
        (m.primeFactors.filter fun p => Y < p).card := by
  intro m Y hm hY
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
    ∀ (m Y : ℕ) (_hm : m ≠ 0) (_hY : 1 ≤ Y),
    (m : ℝ) / Nat.totient m ≤
      primeEulerProdNat Y *
        ((((Y + 1 : ℕ) : ℝ) / Y) ^ (Real.log m / Real.log (Y + 1))) := by
  intro m Y hm hY
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
    ∀ [_hm : Fact H1],
    ∀ ε > 0, ∀ᶠ x : ℕ in atTop,
      R x ≤ (Real.exp Real.eulerMascheroniConstant + ε) * Real.log (Real.log x) := by
  intro hm ε hε_pos
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
    ∀ (Y : ℕ),
    0 < predecessorProduct Y := by
  intro Y
  unfold predecessorProduct
  refine Finset.prod_pos ?_
  intro p hp
  simp only [smallPrimes] at hp
  rcases Finset.mem_filter.mp hp with ⟨_, hpprime⟩
  have h2 : 2 ≤ p := hpprime.two_le
  omega

theorem P_pos :
    ∀ (Y : ℕ),
    0 < smallPrimeProduct Y := by
  intro Y
  unfold smallPrimeProduct
  refine Finset.prod_pos ?_
  intro p hp
  simp only [smallPrimes] at hp
  rcases Finset.mem_filter.mp hp with ⟨_, hpprime⟩
  exact hpprime.pos

theorem Q_pos :
    ∀ (Y U : ℕ),
    0 < largePrimeProduct Y U := by
  intro Y U
  unfold largePrimeProduct
  refine Finset.prod_pos ?_
  intro q hq
  simp only [largeFactors] at hq
  rcases Finset.mem_filter.mp hq with ⟨hqU, _⟩
  exact (Nat.prime_of_mem_primeFactors hqU).pos

theorem A_le_P :
    ∀ (Y : ℕ),
    predecessorProduct Y ≤ smallPrimeProduct Y := by
  intro Y
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
    ∀ (Y : ℕ),
    smallPrimeProduct Y = primorial Y := by
  intro Y
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
    ∀ (Y : ℕ),
    smallPrimeProduct Y ≤ 4 ^ Y := by
  intro Y
  rw [show smallPrimeProduct Y = primorial Y from P_eq_primorial Y]
  exact primorial_le_four_pow Y

theorem A_le_four_pow :
    ∀ (Y : ℕ),
    predecessorProduct Y ≤ 4 ^ Y := by
  intro Y
  exact (A_le_P Y).trans (P_le_four_pow Y)

theorem Q_dvd_U :
    ∀ (Y U : ℕ) (_hU : U ≠ 0),
    largePrimeProduct Y U ∣ U := by
  intro Y U _hU
  unfold largePrimeProduct largeFactors

  refine dvd_trans ?_ (Nat.prod_primeFactors_dvd U)
  exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)

theorem primeFactors_Q :
    ∀ (Y U : ℕ) (_hU : U ≠ 0),
    (largePrimeProduct Y U).primeFactors = largeFactors Y U := by
  intro Y U _hU
  unfold largePrimeProduct
  apply Nat.primeFactors_prod
  intro q hq
  simp only [largeFactors] at hq
  exact Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1

theorem primeFactors_P :
    ∀ (Y : ℕ),
    (smallPrimeProduct Y).primeFactors = smallPrimes Y := by
  intro Y
  unfold smallPrimeProduct
  apply Nat.primeFactors_prod
  intro p hp
  simp only [smallPrimes] at hp
  exact (Finset.mem_filter.mp hp).2

theorem primeFactors_b :
    ∀ (Y U : ℕ) (_hU_pos : 0 < U) (_hU_dvd : largePrimeProduct Y U ∣ U),
    (smallPrimeProduct Y * U * largePrimeProduct Y U).primeFactors = smallPrimes Y ∪ largeFactors Y U := by
  intro Y U hU_pos _hU_dvd
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
    ∀ (Y : ℕ),
    (smallPrimeProduct Y : ℝ) / (predecessorProduct Y : ℝ) = primeEulerProdNat Y := by
  intro Y
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
    ∀ (Y U : ℕ),
    Disjoint (smallPrimes Y) (largeFactors Y U) := by
  intro Y U
  rw [Finset.disjoint_left]
  intro p hp_small hp_large
  simp only [smallPrimes, Finset.mem_filter, Finset.mem_Icc] at hp_small
  simp only [largeFactors, Finset.mem_filter] at hp_large
  have h1 : p ≤ Y := hp_small.1.2
  have h2 : Y < p := hp_large.2
  omega

theorem prod_largeFactors_eq_Q :
    ∀ (Y U : ℕ),
    ∏ q ∈ largeFactors Y U, q = largePrimeProduct Y U := by
  intro Y U
  exact rfl

theorem prod_smallPrimes_eq_P :
    ∀ (Y : ℕ),
    ∏ p ∈ smallPrimes Y, p = smallPrimeProduct Y := by
  intro Y
  exact rfl

theorem prod_smallPrimes_sub_one_eq_A :
    ∀ (Y : ℕ),
    ∏ p ∈ smallPrimes Y, (p - 1) = predecessorProduct Y := by
  intro Y
  exact rfl

theorem totient_P_mul_U_mul_Q :
    ∀ (Y U : ℕ) (_hU : 0 < U),
    Nat.totient (smallPrimeProduct Y * U * largePrimeProduct Y U) =
      predecessorProduct Y * U * ∏ q ∈ largeFactors Y U, (q - 1) := by
  intro Y U hU
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
    ∀ (Y U : ℕ) (_hU : U ≠ 0),
    Nat.totient (largePrimeProduct Y U) = ∏ q ∈ largeFactors Y U, (q - 1) := by
  intro Y U hU
  have hkey := Nat.totient_mul_prod_primeFactors (largePrimeProduct Y U)
  rw [primeFactors_Q Y U hU, prod_largeFactors_eq_Q] at hkey
  apply Nat.eq_of_mul_eq_mul_right (Q_pos Y U)
  rw [hkey, mul_comm]

theorem composite_collision :
    ∀ (Y N : ℕ) (_hN : 0 < N)
    (_hcop : N.Coprime (Nat.totient N)) (_hA : predecessorProduct Y ∣ Nat.totient N),
    let U := Nat.totient N / predecessorProduct Y
    Nat.totient (N * largePrimeProduct Y U) = Nat.totient (smallPrimeProduct Y * U * largePrimeProduct Y U) := by
  intro Y N hN hcop hA
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
    ∀ (Y N : ℕ) (_hN : 0 < N)
    (_hA : predecessorProduct Y ∣ Nat.totient N),
    let U := Nat.totient N / predecessorProduct Y
    ((smallPrimeProduct Y * U * largePrimeProduct Y U : ℕ) : ℝ) / (N * largePrimeProduct Y U : ℕ) =
      primeEulerProdNat Y * ((Nat.totient N : ℝ) / N) := by
  intro Y N hN hA
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
    ∀ (Y N : ℕ) (_hN : 0 < N)
    (_hA : predecessorProduct Y ∣ Nat.totient N),
    let U := Nat.totient N / predecessorProduct Y
    Nat.totient (N * largePrimeProduct Y U) ≤ N ^ 2 := by
  intro Y N hN hA
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
    ∀ (Y : ℕ),
    (predecessorProduct Y).primeFactorsList.length ≤ 2 * Y := by
  intro Y
  apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
  calc
    2 ^ (predecessorProduct Y).primeFactorsList.length ≤ (predecessorProduct Y).primeFactorsList.prod :=
      List.pow_card_le_prod _ _ fun p hp => (Nat.prime_of_mem_primeFactorsList hp).two_le
    _ = predecessorProduct Y := Nat.prod_primeFactorsList (A_pos Y).ne'
    _ ≤ 4 ^ Y := A_le_four_pow Y
    _ = 2 ^ (2 * Y) := by rw [pow_mul]; norm_num

theorem A_primeFactorsList_mem_le :
    ∀ {Y p : ℕ} (_hp : p ∈ (predecessorProduct Y).primeFactorsList),
    p ≤ Y := by
  intro Y p hp
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
    ∀ (Y T : ℕ) (_hT : 2 ≤ T)
    (_hsupply : ∀ q : ℕ, q.Prime → q ≤ Y →
      2 * Y ≤ ((Finset.Ioc T (2 * T)).filter
        (fun p => p.Prime ∧ p % q = 1 % q)).card),
    ∃ S : Finset ℕ, S.card ≤ 2 * Y ∧
      (∀ p ∈ S, p.Prime ∧ T < p ∧ p ≤ 2 * T) ∧
      predecessorProduct Y ∣ Nat.totient (∏ p ∈ S, p) ∧
      (∏ p ∈ S, p).Coprime (Nat.totient (∏ p ∈ S, p)) := by
  intro Y T hT hsupply
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
    ∀ (Y : ℕ),
    0 ≤ primeEulerProdNat Y := by
  intro Y
  apply Finset.prod_nonneg
  intro p hp
  exact (one_le_prime_factor p (Finset.mem_filter.mp hp).2).trans' zero_le_one

theorem dyadic_collision_height :
    ∀ [_supply : Fact H2] (D : ℕ),
    ∀ᶠ k : ℕ in atTop,
      ∃ a b n : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ 1 ≤ n ∧
        Nat.totient a = n ∧ Nat.totient b = n ∧
        dyadicRatio D k ≤ (b : ℝ) / a ∧
        (n : ℝ) ≤ Real.exp (12 * (k : ℝ) ^ (D + 1)) := by
  intro supply D
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
    ∀ [_hm : Fact H1] (D : ℕ) (_hD : 0 < D),
    Tendsto (fun k : ℕ => dyadicRatio D k / Real.log k) atTop
      (𝓝 (Real.exp Real.eulerMascheroniConstant * D)) := by
  intro hm D hD
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
    ∀ (d : ℕ) (_hd : 0 < d),
    Tendsto (heightRoot d) atTop atTop := by
  intro d hd
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  exact (tendsto_rpow_atTop (inv_pos.mpr hdR)).comp
    ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).atTop_div_const
      (by norm_num : (0 : ℝ) < 12))

theorem heightIndex_tendsto :
    ∀ (d : ℕ) (_hd : 0 < d),
    Tendsto (heightIndex d) atTop atTop := by
  intro d hd
  exact tendsto_nat_floor_atTop.comp (heightRoot_tendsto d hd)

theorem heightIndex_bound :
    ∀ (d : ℕ) (_hd : 0 < d) (x : ℕ) (_hx : 2 ≤ x),
    Real.exp (12 * (heightIndex d x : ℝ) ^ d) ≤ x := by
  intro d hd x hx
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
    ∀ (d : ℕ) (_hd : 0 < d),
    Tendsto (fun x : ℕ => Real.log (heightIndex d x : ℝ) /
      Real.log (Real.log (x : ℝ))) atTop (𝓝 (d : ℝ)⁻¹) := by
  intro d hd
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
    ∀ [_hm : Fact H1] (D : ℕ) (_hD : 0 < D),
    Tendsto (fun x : ℕ => dyadicRatio D (heightIndex (D + 1) x) /
      Real.log (Real.log (x : ℝ))) atTop
      (𝓝 (Real.exp Real.eulerMascheroniConstant * D / (D + 1 : ℕ))) := by
  intro hm D hD
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
    ∀ {x a b n : ℕ}
    (_ha : 1 ≤ a) (_hb : 1 ≤ b) (_hn : 1 ≤ n) (_hnx : n ≤ x)
    (_hφa : Nat.totient a = n) (_hφb : Nat.totient b = n),
    (b : ℝ) / a ≤ R x := by
  intro x a b n ha hb hn hnx hφa hφb

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
    ∀ [_hm : Fact H1] [_supply : Fact H2],
    ∀ ε > 0, ∀ᶠ x : ℕ in atTop,
      R x ≥ (Real.exp Real.eulerMascheroniConstant - ε) * Real.log (Real.log x) := by
  intro hm supply ε hε
  filter_upwards [collision_of_dyadic_supply ε hε, Filter.eventually_ge_atTop 1]
    with x hx hx1
  obtain ⟨a, b, n, ha, hb, hn, hnx, hφa, hφb, hba⟩ := hx
  have hR_ge : (b : ℝ) / a ≤ R x :=
    R_ge_of_totient_collision ha hb hn hnx hφa hφb
  linarith

theorem totient_fibre_extremes :
    ∀ [_hm : Fact H1] [_supply : Fact H2],
    Tendsto
      (fun x : ℕ => R x / (Real.exp Real.eulerMascheroniConstant * Real.log (Real.log x)))
      atTop (𝓝 1) := by
  intro hm supply
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
    ∀ (x : ℕ) (fmax fmin : ℕ → ℕ)
    (_hmax : ∀ n, (∃ m, Nat.totient m = n) → IsGreatest (Nat.totient ⁻¹' {n}) (fmax n))
    (_hmin : ∀ n, (∃ m, Nat.totient m = n) → IsLeast (Nat.totient ⁻¹' {n}) (fmin n)),
    sSup { (fmax n : ℝ) / fmin n | (n : ℕ) (_ : n ≤ x) (_ : ∃ m, Nat.totient m = n) } =
      R x := by
  intro x fmax fmin hmax hmin
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
  let : Fact H1 := ⟨hM⟩
  let : Fact H2 := ⟨hL⟩
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
  ring
end OMA.R_Erdos694_erdos_694_R2
end

section
/- Reuses the existing open-math-agents #12357 proof of the identical Mertens product
input. The statements differ only by the parent reduction namespace. -/

-- Port of the PrimeNumberTheoremAnd project contributors,
-- AlexKontorovich/PrimeNumberTheoremAnd at 55270df80721, Apache-2.0.
-- Mertens contributions include Terence Tao, A. J. Irving, Giuseppe Sorge,
-- Robby Sneiderman and Yan Yablonovskiy. The comparison uses the reciprocal product.
-- The last step inverts the standard prime product to match the target.
-- Credit: @marcusbuffett

section
open Finset Interval MeasureTheory

variable {𝕜 : Type*} [RCLike 𝕜] {f : ℝ → 𝕜} {a b : ℝ}

end

section

namespace Real

open Filter Asymptotics

theorem inv_log_eq_o_one : (fun x ↦ 1 / log x) =o[atTop] (fun _ ↦ (1:ℝ)) := by
    rw [isLittleO_one_iff]
    convert tendsto_log_atTop.inv_tendsto_atTop using 1
    ext; simp

end Real

section Issue1584
open MeasureTheory Set Filter Topology

private lemma integrableOn_log_mul_exp_neg :
    IntegrableOn (fun v : ℝ => Real.log v * Real.exp (-v)) (Ioi 0) := by
  rw [← Set.Ioc_union_Ioi_eq_Ioi (zero_le_one' ℝ), integrableOn_union]
  constructor
  ·
    have hlog : IntegrableOn (fun v : ℝ => Real.log v) (Ioc 0 1) volume := by
      have := (intervalIntegral.intervalIntegrable_log' (a := 0) (b := 1))
      rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le (zero_le_one' ℝ)] at this
    apply Integrable.mono' hlog.norm
    · apply (Measurable.aestronglyMeasurable ?_)
      exact (Real.measurable_log.mul (Real.measurable_exp.comp measurable_neg))
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with v hv
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      have h1 : |Real.exp (-v)| = Real.exp (-v) := abs_of_pos (Real.exp_pos _)
      have h2 : Real.exp (-v) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [hv.1])
      rw [h1]
      nlinarith [abs_nonneg (Real.log v), Real.exp_pos (-v)]
  ·
    have hexp : IntegrableOn (fun v : ℝ => (2 : ℝ) * Real.exp ((-1/2) * v)) (Ioi 1) volume := by
      exact (integrableOn_exp_mul_Ioi (by norm_num : (-1/2 : ℝ) < 0) 1).const_mul 2
    apply Integrable.mono' hexp
    · apply (Measurable.aestronglyMeasurable ?_)
      exact (Real.measurable_log.mul (Real.measurable_exp.comp measurable_neg))
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with v hv
      have hv1 : (1 : ℝ) ≤ v := le_of_lt hv
      have hvpos : (0 : ℝ) < v := by linarith
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      have hlogabs : |Real.log v| = Real.log v :=
        abs_of_nonneg (Real.log_nonneg hv1)
      have hexpabs : |Real.exp (-v)| = Real.exp (-v) := abs_of_pos (Real.exp_pos _)
      rw [hlogabs, hexpabs]

      have hlogv : Real.log v ≤ v := (Real.log_le_sub_one_of_pos hvpos).trans (by linarith)

      have hvexp : v ≤ 2 * Real.exp (v/2) := by
        have := Real.add_one_le_exp (v/2)
        nlinarith [Real.exp_pos (v/2)]

      have hstep : Real.log v * Real.exp (-v) ≤ 2 * Real.exp (v/2) * Real.exp (-v) := by
        apply mul_le_mul_of_nonneg_right (hlogv.trans hvexp) (le_of_lt (Real.exp_pos _))
      have heq : 2 * Real.exp (v/2) * Real.exp (-v) = 2 * Real.exp ((-1/2) * v) := by
        rw [mul_assoc, ← Real.exp_add]
        ring_nf
      rw [heq] at hstep
      exact hstep

private lemma integral_log_mul_exp_neg_eq_deriv_Gamma :
    ∫ t in Ioi (0:ℝ), Real.log t * Real.exp (-t) = deriv Real.Gamma 1 := by
  set I : ℝ := ∫ t in Ioi (0:ℝ), Real.log t * Real.exp (-t) with hI

  have h1 := Complex.hasDerivAt_GammaIntegral (s := (1 : ℂ)) (by norm_num)

  have hval : (∫ t : ℝ in Ioi 0, (↑t : ℂ) ^ ((1 : ℂ) - 1) * (↑(Real.log t) * ↑(Real.exp (-t))))
      = (I : ℂ) := by
    have key : ∀ t : ℝ, (↑t : ℂ) ^ ((1 : ℂ) - 1) * (↑(Real.log t) * ↑(Real.exp (-t)))
        = ((Real.log t * Real.exp (-t) : ℝ) : ℂ) := by
      intro t
      rw [sub_self, Complex.cpow_zero, one_mul, Complex.ofReal_mul]
    simp_rw [key]
    rw [integral_complex_ofReal, hI]
  rw [hval] at h1

  have h2 : HasDerivAt Complex.Gamma (I : ℂ) 1 := by
    apply h1.congr_of_eventuallyEq
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (0:ℝ) < (1:ℂ).re by norm_num)] with z hz
    exact Complex.Gamma_eq_integral hz

  have h3 := h2.real_of_complex
  have h4 : HasDerivAt Real.Gamma I 1 := by
    have hcongr : (fun x : ℝ => (Complex.Gamma ↑x).re) = Real.Gamma := by
      funext x
      rw [Complex.Gamma_ofReal, Complex.ofReal_re]
    rw [hcongr, Complex.ofReal_re] at h3
    exact h3
  rw [← h4.deriv]

private theorem mul_integ_log_log_eq_aux (s : ℝ) (hs : 1 < s) :
    (s - 1) * ∫ x in Ioi (1:ℝ), Real.log (Real.log x) * x ^ (-s) =
      - Real.log (s - 1) + deriv Real.Gamma 1 := by
  have hs0 : 0 < s - 1 := by linarith
  set f : ℝ → ℝ := fun x => (s - 1) * Real.log x with hf_def
  set f' : ℝ → ℝ := fun x => (s - 1) / x with hf'_def
  set g : ℝ → ℝ := fun u => (Real.log u - Real.log (s - 1)) * Real.exp (-u) with hg_def

  have hf1 : f 1 = 0 := by simp [hf_def]

  have hf_cont : ContinuousOn f (Ici 1) := by
    apply ContinuousOn.mul continuousOn_const
    apply Real.continuousOn_log.mono
    intro x hx
    simp only [mem_Ici] at hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    linarith

  have hft : Tendsto f atTop atTop := by
    apply Filter.Tendsto.const_mul_atTop hs0
    exact Real.tendsto_log_atTop

  have hff' : ∀ x ∈ Ioi (1:ℝ), HasDerivWithinAt f (f' x) (Ioi x) x := by
    intro x hx
    simp only [mem_Ioi] at hx
    have hxne : x ≠ 0 := by linarith
    have := (Real.hasDerivAt_log hxne).const_mul (s - 1)
    have h2 : HasDerivAt f ((s - 1) * x⁻¹) x := this
    have : (s - 1) * x⁻¹ = f' x := by rw [hf'_def]; field_simp
    rw [this] at h2
    exact h2.hasDerivWithinAt

  have hmono : StrictMonoOn f (Ici 1) := by
    intro a ha b hb hab
    simp only [mem_Ici] at ha hb
    apply mul_lt_mul_of_pos_left _ hs0
    exact Real.log_lt_log (by linarith) hab
  have himg_Ioi : f '' Ioi 1 = Ioi 0 := by
    ext y
    simp only [Set.mem_image, mem_Ioi]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have : 0 < Real.log x := Real.log_pos hx
      positivity
    · intro hy
      refine ⟨Real.exp (y / (s - 1)), ?_, ?_⟩
      · exact Real.one_lt_exp_iff.mpr (div_pos hy hs0)
      · rw [hf_def]
        simp only [Real.log_exp]
        field_simp
  have himg_Ici : f '' Ici 1 = Ici 0 := by
    ext y
    simp only [Set.mem_image, mem_Ici]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have : 0 ≤ Real.log x := Real.log_nonneg hx
      rw [hf_def]; positivity
    · intro hy
      refine ⟨Real.exp (y / (s - 1)), ?_, ?_⟩
      · exact Real.one_le_exp_iff.mpr (div_nonneg hy hs0.le)
      · rw [hf_def]
        simp only [Real.log_exp]
        field_simp

  have hg_cont : ContinuousOn g (f '' Ioi 1) := by
    rw [himg_Ioi]
    apply ContinuousOn.mul
    · apply ContinuousOn.sub _ continuousOn_const
      apply Real.continuousOn_log.mono
      intro u hu
      simp only [mem_Ioi] at hu
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      linarith
    · exact (Real.continuous_exp.comp continuous_neg).continuousOn

  have hg1 : IntegrableOn g (f '' Ici 1) := by
    rw [himg_Ici, integrableOn_Ici_iff_integrableOn_Ioi]
    have e1 : IntegrableOn (fun u => Real.log u * Real.exp (-u)) (Ioi 0) :=
      integrableOn_log_mul_exp_neg
    have e2 : IntegrableOn (fun u => Real.log (s - 1) * Real.exp (-u)) (Ioi 0) :=
      (integrableOn_exp_neg_Ioi 0).const_mul _
    have : g = fun u => Real.log u * Real.exp (-u) - Real.log (s - 1) * Real.exp (-u) := by
      funext u; rw [hg_def]; ring
    rw [this]
    exact e1.sub e2

  have hg2 : IntegrableOn (fun x => (g ∘ f) x * f' x) (Ici 1) := by

    have hff'_Ici : ∀ x ∈ Ici (1:ℝ), HasDerivWithinAt f (f' x) (Ici 1) x := by
      intro x hx
      simp only [mem_Ici] at hx
      have hxne : x ≠ 0 := by linarith
      have hd : HasDerivAt f ((s - 1) * x⁻¹) x := (Real.hasDerivAt_log hxne).const_mul (s - 1)
      have heq : (s - 1) * x⁻¹ = f' x := by rw [hf'_def]; field_simp
      rw [heq] at hd
      exact hd.hasDerivWithinAt

    have hinj : InjOn f (Ici 1) := hmono.injOn

    have hiff := integrableOn_image_iff_integrableOn_abs_deriv_smul
      (s := Ici (1:ℝ)) (f := f) (f' := f') measurableSet_Ici hff'_Ici hinj g
    rw [hiff] at hg1

    apply hg1.congr
    filter_upwards [self_mem_ae_restrict measurableSet_Ici] with x hx
    simp only [mem_Ici] at hx
    have hxpos : (0:ℝ) < x := by linarith
    have hf'pos : 0 < f' x := by rw [hf'_def]; positivity
    simp only [smul_eq_mul, Function.comp, abs_of_pos hf'pos]
    ring

  have hcov := integral_comp_mul_deriv_Ioi hf_cont hft hff' hg_cont hg1 hg2
  rw [hf1] at hcov

  have hrhs : ∫ u in Ioi (0:ℝ), g u = deriv Real.Gamma 1 - Real.log (s - 1) := by
    have e1 : IntegrableOn (fun u => Real.log u * Real.exp (-u)) (Ioi 0) :=
      integrableOn_log_mul_exp_neg
    have e2 : IntegrableOn (fun u => Real.log (s - 1) * Real.exp (-u)) (Ioi 0) :=
      (integrableOn_exp_neg_Ioi 0).const_mul _
    have hsplit : (fun u => g u)
        = fun u => Real.log u * Real.exp (-u) - Real.log (s - 1) * Real.exp (-u) := by
      funext u; rw [hg_def]; ring
    rw [show (∫ u in Ioi (0:ℝ), g u)
        = ∫ u in Ioi (0:ℝ), (Real.log u * Real.exp (-u) - Real.log (s - 1) * Real.exp (-u))
        from by rw [hsplit]]
    rw [integral_sub e1 e2, integral_log_mul_exp_neg_eq_deriv_Gamma]
    rw [integral_const_mul, integral_exp_neg_Ioi_zero, mul_one]

  have hlhs : ∫ x in Ioi (1:ℝ), (g ∘ f) x * f' x
      = (s - 1) * ∫ x in Ioi (1:ℝ), Real.log (Real.log x) * x ^ (-s) := by
    have hpt : ∀ x ∈ Ioi (1:ℝ), (g ∘ f) x * f' x
        = (s - 1) * (Real.log (Real.log x) * x ^ (-s)) := by
      intro x hx
      simp only [mem_Ioi] at hx
      have hxpos : (0:ℝ) < x := by linarith
      have hlogpos : 0 < Real.log x := Real.log_pos hx
      have hlogne : Real.log x ≠ 0 := ne_of_gt hlogpos
      have hs1ne : s - 1 ≠ 0 := ne_of_gt hs0
      simp only [Function.comp, hf_def, hg_def, hf'_def]

      rw [Real.log_mul hs1ne hlogne]

      have hexp : Real.exp (-((s - 1) * Real.log x)) = x ^ (-(s - 1)) := by
        rw [Real.rpow_def_of_pos hxpos]
        ring_nf
      rw [hexp]

      have hx1 : x ^ (-(s - 1)) * ((s - 1) / x) = (s - 1) * x ^ (-s) := by
        rw [div_eq_mul_inv, ← Real.rpow_neg_one x]
        rw [show x ^ (-(s - 1)) * ((s - 1) * x ^ (-1 : ℝ))
            = (s - 1) * (x ^ (-(s - 1)) * x ^ (-1 : ℝ)) by ring]
        rw [← Real.rpow_add hxpos]
        ring_nf
      rw [show (Real.log (s - 1) + Real.log (Real.log x) - Real.log (s - 1))
          = Real.log (Real.log x) by ring]
      linear_combination Real.log (Real.log x) * hx1
    rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul]
  rw [hlhs, hrhs] at hcov
  rw [hcov]
  ring

end Issue1584

namespace Mertens

open Real Finset Filter Asymptotics Topology
open ArithmeticFunction hiding log

lemma sum_Ioc_one_eq_sum_Ioc_zero {f : ℕ → ℝ} {x : ℕ} (hx : 1 ≤ x) (hf : f 1 = 0) :
    ∑ n ∈ Ioc 1 x, f n = ∑ n ∈ Ioc 0 x, f n := by
  rw [(by rfl : Ioc 0 x = Icc 1 x), ← add_sum_Ioc_eq_sum_Icc hx]
  simpa

theorem sum_log_le {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log n ≤ x * log x := by
  calc
  _ ≤ ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log x := by
    refine sum_le_sum fun n hn ↦ ?_
    simp only [mem_Ioc] at hn
    exact log_le_log (by exact_mod_cast hn.1) (Nat.le_floor_iff (by linarith)|>.mp hn.2)
  _ = ⌊x⌋₊ * log x := by simp
  _ ≤ _ := by
    gcongr
    · exact log_nonneg hx
    · exact Nat.floor_le (by linarith)

lemma integral_log_le {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    ∫ t in a..b, log t ≤ log b * (b - a) := by
  apply le_of_abs_le
  have : ∀ t ∈ Set.uIoc a b, ‖log t‖ ≤ log b := by
    intro t ht
    rw [Set.uIoc_of_le hab, Set.mem_Ioc] at ht
    rw [norm_of_nonneg <| log_nonneg (by linarith)]
    gcongr <;> linarith
  grw [← norm_eq_abs, intervalIntegral.norm_integral_le_of_norm_le_const this,
    abs_of_nonneg (by linarith)]

theorem sum_log_ge {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log n ≥ x * log x - 2 * x := by
  have one_le_floor : 1 ≤ ⌊x⌋₊ := by simpa
  calc
  _ = ∑ n ∈ Icc 1 ⌊ x ⌋₊, log n := by rfl
  _ = ∑ n ∈ Ico (1 + 1) (⌊ x ⌋₊ + 1), log n := by
    rw [← add_sum_Ioc_eq_sum_Icc one_le_floor]
    simp
    rfl
  _ = ∑ n ∈ Ico 1 ⌊ x ⌋₊, log ((n + 1 : ℕ)) := by
    rw [← Finset.sum_Ico_add']
  _ ≥ ∫ t in 1..⌊x⌋₊, log t := by
    convert MonotoneOn.integral_le_sum_Ico one_le_floor ?_|>.ge
    · norm_cast
    · exact StrictMonoOn.monotoneOn (strictMonoOn_log.mono fun y hy ↦ (by simp_all; linarith))
  _ = (∫ t in 1..x, log t) - ∫ t in ⌊x⌋₊..x, log t := by
    nth_rw 3 [intervalIntegral.integral_symm]
    rw [sub_neg_eq_add, intervalIntegral.integral_add_adjacent_intervals] <;> exact intervalIntegral.intervalIntegrable_log'
  _ ≥ (∫ t in 1..x, log t) - log x := by
    gcongr
    grw [integral_log_le (by simpa) (Nat.floor_le (by linarith))]
    nth_rw 2 [← mul_one (log x)]
    gcongr
    · exact log_nonneg hx
    · linarith [Nat.lt_floor_add_one x]
  _ ≥ x * log x - x - log x := by simp only [integral_log, log_one, mul_zero, sub_zero, ge_iff_le,
    tsub_le_iff_right, sub_add_cancel, le_add_iff_nonneg_right, zero_le_one]
  _ ≥ _ := by linarith [log_le_self (by linarith : 0 ≤ x)]

theorem sum_log_eq_sum_mangoldt {x : ℝ} :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, log n = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * ⌊x / d⌋₊ := by
  have : ∀ n : ℕ, log n = (Λ * zeta) n := by simp [vonMangoldt_mul_zeta]
  simp_rw [this, sum_Ioc_mul_zeta_eq_sum, ← Nat.floor_div_natCast]

noncomputable abbrev E₁Λ (x : ℝ) : ℝ := ∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / d - log x

theorem sum_mangoldt_div_eq (x : ℝ) : ∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / d = log x + E₁Λ x := by
    grind

theorem E₁Λ.ge {x : ℝ} (hx : 1 ≤ x) :
    E₁Λ x  ≥ -2 := by
  unfold E₁Λ
  suffices x * ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d  ≥ x * (log x - 2) by
    linarith [le_of_mul_le_mul_left this (by linarith)]
  calc
  _ = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (x / d) := by
    rw [Finset.mul_sum]
    ring_nf
  _ ≥ ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * ⌊x / d⌋₊ := by
    gcongr
    exact Nat.floor_le <| div_nonneg (by linarith) (by linarith)
  _ ≥ x * log x - 2 * x :=
    sum_log_eq_sum_mangoldt ▸ sum_log_ge hx
  _ = _ := by ring

theorem E₁Λ.le {x : ℝ} (hx : 1 ≤ x) :
    E₁Λ x ≤ log 4 + 4 := by
  unfold E₁Λ
  suffices x * ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d ≤ x * (log x + log 4 + 4) by
    linarith [le_of_mul_le_mul_left this (by linarith)]
  calc
  _ = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (x / d) := by
    rw [Finset.mul_sum]
    ring_nf
  _ ≤ ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (⌊x / d⌋₊ + 1) := by
    gcongr
    exact Nat.lt_floor_add_one _|>.le
  _ = (∑ d ∈ Ioc 0 ⌊x⌋₊, log d) + ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d := by
    simp_rw [mul_add, mul_one]
    rw [Finset.sum_add_distrib, sum_log_eq_sum_mangoldt]
  _ ≤ x * log x + (log 4 + 4) * x := by
    gcongr
    · exact sum_log_le hx
    · exact Chebyshev.psi_le_const_mul_self (by linarith)
  _ = _ := by ring

theorem sum_mangoldt_div_eq_log {x : ℝ} (hx : 1 ≤ x) :
    |∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / d - log x| ≤ log 4 + 4 := by
  grind [E₁Λ.le hx, E₁Λ.ge hx, log_nonneg]

theorem E₁Λ.bounded' : ∃ c > 0, ∀ x ≥ 1, |E₁Λ x| ≤ c := by
  exact ⟨log 4 + 4, (by positivity), fun x hx ↦ sum_mangoldt_div_eq_log hx⟩

noncomputable abbrev γ : ℝ := (∫ t in Set.Ioi 2, E₁Λ t / (t * log t^2)) + 1 - log (log 2)

noncomputable abbrev E₂Λ (x : ℝ) : ℝ := ∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / (d * log d) - log (log x) - γ

lemma sum_Ioc_one_eq_sum_Icc_zero {f : ℕ → ℝ} {x : ℕ} (hx : 1 ≤ x) (hf1 : f 1 = 0) (hf0 : f 0 = 0) :
    ∑ n ∈ Ioc 1 x, f n = ∑ n ∈ Icc 0 x, f n := by
  rw [sum_Ioc_one_eq_sum_Ioc_zero hx hf1, ← add_sum_Ioc_eq_sum_Icc (by linarith)]
  simpa

private theorem sum_div_log_eq {x : ℝ} (hx : 2 ≤ x) (f : ℕ → ℝ) :
    ∑ n ∈ Ioc 1 ⌊ x ⌋₊, f n / log n =
      (∑ n ∈ Ioc 1 ⌊ x ⌋₊, f n) / log x + ∫ t in 2..x, (∑ n ∈ Ioc 1 ⌊ t ⌋₊, f n) / (t * log t^2) := by
  let g : ℕ → ℝ := (fun n ↦ if n < 2 then 0 else f n)
  trans ∑ n ∈ Icc 0 ⌊ x ⌋₊, (log n)⁻¹ * g n
  · rw [← sum_Ioc_one_eq_sum_Icc_zero (Nat.le_floor (by grind)) (by simp) (by simp)]
    refine sum_congr rfl fun n hn ↦ ?_
    have : ¬(n ≤ 1) := by simp_all
    simp [g, this]
    field
  rw [sum_mul_eq_sub_integral_mul₁ g (f := (fun n ↦ (log n)⁻¹)) (by simp [g]) (by simp [g])]
  · rw [intervalIntegral.integral_of_le hx, mul_comm, ← div_eq_mul_inv, ← sub_neg_eq_add]
    simp_rw [deriv_inv_log]
    congr 1
    · rw [← sum_Ioc_one_eq_sum_Icc_zero (Nat.le_floor (by grind)) (by simp [g]) (by simp [g])]
      congr 1
      refine sum_congr rfl fun n hn ↦ ?_
      simp only [mem_Ioc] at hn
      have : ¬(n ≤ 1) := by linarith
      simp [g, this]
    · rw [← MeasureTheory.integral_neg]
      refine  MeasureTheory.setIntegral_congr_fun (by measurability) fun t ht ↦ ?_
      simp only [Set.mem_Ioc] at ht
      rw [← sum_Ioc_one_eq_sum_Icc_zero (Nat.le_floor (by grind)) (by simp [g]) (by simp [g])]
      field_simp
      congr 2
      refine sum_congr rfl fun n hn ↦ ?_
      simp only [mem_Ioc] at hn
      have : ¬(n ≤ 1) := by linarith
      simp [g, this]
  · intro t ht
    simp only [Set.mem_Icc] at ht
    have : log t ≠ 0 := by simp; grind
    fun_prop (disch := grind)
  · refine ContinuousOn.integrableOn_Icc fun t ht ↦ ContinuousAt.continuousWithinAt ?_
    simp only [Set.mem_Icc] at ht
    conv => arg 1; ext x; rw [deriv_inv_log]
    have : log t ^2 ≠ 0 := by simp; grind
    fun_prop (disch := grind)

private theorem integrable_const_div_mul_log_sq {x : ℝ} (c : ℝ) (hx : 2 ≤ x) :
    MeasureTheory.IntegrableOn (fun x ↦ c / (x * log x ^ 2)) (Set.Ioi x) MeasureTheory.volume := by
  conv => arg 1; ext t; rw [← mul_one_div]
  apply MeasureTheory.Integrable.const_mul
  refine MeasureTheory.integrableOn_Ioi_deriv_of_nonneg' ?_ ?_ tendsto_log_atTop.inv_tendsto_atTop.neg
  · intro t ht
    simp only [Set.mem_Ici] at ht
    have : log t ≠ 0 := by simp; grind
    have : DifferentiableAt ℝ (fun t ↦ -(log t)⁻¹) t := by
      fun_prop (disch := grind)
    convert! this.hasDerivAt using 1
    simp [deriv_inv_log]
    field
  · intro t ht
    simp only [Set.mem_Ioi] at ht
    exact one_div_nonneg.mpr <| mul_nonneg (by linarith) (sq_nonneg _)

private theorem integrable_E₁Λ_div_mul_log_sq {x : ℝ} (hx : 2 ≤ x) :
    MeasureTheory.IntegrableOn (fun x ↦ E₁Λ x / (x * log x ^ 2)) (Set.Ioi x) MeasureTheory.volume := by
  obtain ⟨c, hc1, hc2⟩ := E₁Λ.bounded'
  apply MeasureTheory.Integrable.mono (integrable_const_div_mul_log_sq c hx)
  · exact Measurable.aestronglyMeasurable (by fun_prop)
  · filter_upwards [MeasureTheory.ae_restrict_mem (by measurability)] with t ht
    simp only [Set.mem_Ioi] at ht
    simp only [norm_div, norm_eq_abs, norm_mul, norm_pow, sq_abs, abs_of_pos hc1]
    gcongr
    exact hc2 t (by linarith)

lemma deriv_log_log {x : ℝ} (hx : 1 < x) :
    deriv (fun t ↦ log (log t)) x = 1 / (x * log x) := by
  rw [deriv.log (differentiableAt_log (by linarith)) (by simp; grind), deriv_log]
  field

lemma integral_one_div_mul_log {x : ℝ} (hx : 2 ≤ x) :
    ∫ t in 2..x, 1 / (t * log t) = log (log x) - log (log 2) := by
  rw [← intervalIntegral.integral_deriv_eq_sub (f := fun t ↦ log (log t))]
  · refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [deriv_log_log]
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
    linarith
  · intro t ht
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
    have : log t ≠ 0 := by simp; grind
    fun_prop (disch := grind)
  · refine ContinuousOn.intervalIntegrable ?_
    apply ContinuousOn.congr (f := (fun t ↦ 1 / (t * log t)))
    · refine fun t ht ↦ ContinuousAt.continuousWithinAt ?_
      rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
      have : log t ≠ 0 := by simp; grind
      fun_prop (disch := grind)
    · intro t ht
      rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
      exact deriv_log_log (by linarith)

lemma intervalIntegrable_one_div_mul_log {x : ℝ} (hx : 2 ≤ x) :
    IntervalIntegrable (fun t ↦ 1 / (t * log t)) MeasureTheory.volume 2 x := by
  refine ContinuousOn.intervalIntegrable fun t ht ↦ ContinuousAt.continuousWithinAt ?_
  rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
  have : log t ≠ 0 := by simp; grind
  fun_prop (disch := grind)

theorem E₂Λ.eq {x : ℝ} (hx : 2 ≤ x) :
    E₂Λ x = E₁Λ x / log x - ∫ t in Set.Ioi x, E₁Λ t / (t * log t^2) := by
  unfold E₂Λ
  rw [← sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp)]
  conv => lhs; arg 1; arg 1; arg 2; ext n; rw [(by field : Λ n / (n * log n) = (Λ n / n) / log n)]
  rw [sum_div_log_eq hx]
  rw [sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp), sum_mangoldt_div_eq]
  have : ∫ t in 2..x, (∑ n ∈ Ioc 1 ⌊t⌋₊, Λ n / n) / (t * log t ^ 2) = ∫ t in 2..x, (1 / (t * log t) + E₁Λ t / (t * log t ^ 2)) := by
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
    rw [sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp), sum_mangoldt_div_eq]
    field
  rw [this, intervalIntegral.integral_add]
  · rw [integral_one_div_mul_log hx, add_div, div_self (by simp; grind)]
    unfold γ
    calc
    _ = E₁Λ x / log x + (∫ (x : ℝ) in 2..x, E₁Λ x / (x * log x ^ 2)) -
      ((∫ (t : ℝ) in Set.Ioi 2, E₁Λ t / (t * log t ^ 2))) := by ring
    _ = _ := by
      rw [← intervalIntegral.integral_interval_add_Ioi (integrable_E₁Λ_div_mul_log_sq (by rfl)) (integrable_E₁Λ_div_mul_log_sq hx)]
      ring
  · exact intervalIntegrable_one_div_mul_log hx
  · rw [intervalIntegrable_iff, Set.uIoc_of_le hx]
    exact integrable_E₁Λ_div_mul_log_sq (x := 2) (by rfl)|>.mono (by grind) (by rfl)

private theorem integ_div_mul_log_sq {x : ℝ} (c : ℝ) (hx : 2 ≤ x) :
    ∫ t in Set.Ioi x, c / (t * log t^2) = c / log x := by
    convert! MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto' (m := 0) (f := fun x ↦ - c / log x) ?_
      (integrable_const_div_mul_log_sq c hx) ?_ using 1
    · grind
    · intro t ht; simp at ht
      convert! HasDerivAt.fun_div (hasDerivAt_const _ (-c)) (hasDerivAt_log (by linarith)) ?_ using 1
      · grind
      simp; grind
    convert! tendsto_log_atTop.inv_tendsto_atTop.const_mul (-c) using 1
    simp

theorem E₂Λ.abs_le {x : ℝ} (hx : 2 ≤ x) :
    |E₂Λ x| ≤ (log 4 + 6) / log x := by
    have : 0 < log x := by apply log_pos; linarith
    rw [E₂Λ.eq hx, abs_le']
    constructor
    · grw [E₁Λ.le (by linarith)]
      have : ∫ t in Set.Ioi x, E₁Λ t / (t * log t^2) ≥ - 2 / log x := calc
        _ ≥ ∫ t in Set.Ioi x, (-2) / (t * log t^2) := by
          apply MeasureTheory.setIntegral_mono_on (integrable_const_div_mul_log_sq (-2) hx)
            (integrable_E₁Λ_div_mul_log_sq hx) (by measurability)
          intro y hy; simp at hy
          have : 1 < y := by linarith
          have : 0 < log y := log_pos this
          gcongr; exact E₁Λ.ge (by linarith)
        _ = _ := integ_div_mul_log_sq (-2) hx
      grw [this]
      grind
    grw [E₁Λ.ge (by linarith)]
    have : ∫ t in Set.Ioi x, E₁Λ t / (t * log t^2) ≤ (log 4 + 4) / log x := calc
        _ ≤ ∫ t in Set.Ioi x, (log 4 + 4) / (t * log t^2) := by
          apply MeasureTheory.setIntegral_mono_on (integrable_E₁Λ_div_mul_log_sq hx)
            (integrable_const_div_mul_log_sq (log 4 + 4) hx) (by measurability)
          intro y hy; simp at hy
          have : 1 < y := by linarith
          have : 0 < log y := log_pos this
          gcongr; exact E₁Λ.le (by linarith)
        _ = _ := integ_div_mul_log_sq (log 4 + 4) hx
    grw [this]
    grind

theorem E₂Λ.bound : E₂Λ =O[atTop] (fun x ↦ 1 / log x) := by
    simp only [one_div, isBigO_iff, norm_eq_abs, norm_inv, eventually_atTop]
    use log 4 + 6, 2
    intro x hx
    convert E₂Λ.abs_le hx using 1
    have : 0 < log x := by apply log_pos; linarith
    grind [abs_of_pos this]

theorem E₂Λ.bound' : E₂Λ =o[atTop] (fun _ ↦ (1:ℝ)) := E₂Λ.bound.trans_isLittleO inv_log_eq_o_one

theorem log_zeta_eq_sum (s : ℝ) (hs : 1 < s) :
    log (riemannZeta (s:ℂ)).re = ∑' n, Λ n / (n^s * log n) := log_riemannZeta_eq hs

section
open MeasureTheory Set

namespace LogZetaInteg

private noncomputable def c (d : ℕ) : ℝ := Λ d / (d * Real.log d)

private noncomputable def f (s : ℝ) (d : ℕ) (x : ℝ) : ℝ :=
    c d * (Set.Ici (d:ℝ)).indicator (fun x => x ^ (-s)) x

@[simp] private lemma c_zero : c 0 = 0 := by simp [c]
@[simp] private lemma c_one : c 1 = 0 := by simp [c, vonMangoldt_apply_one]

private lemma c_nonneg (d : ℕ) : 0 ≤ c d := by
  unfold c
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd; simp
  · apply div_nonneg vonMangoldt_nonneg
    have : (0:ℝ) ≤ (d:ℝ) := Nat.cast_nonneg d
    have hlog : 0 ≤ Real.log d := Real.log_natCast_nonneg d
    positivity

private lemma summable_log_rpow_div_rpow (a : ℝ) {s : ℝ} (hs : 1 < s) :
    Summable (fun n : ℕ => (Real.log n) ^ a / (n:ℝ) ^ s) := by
  have hε : (0:ℝ) < (s - 1) / 2 := by linarith
  refine summable_of_isBigO_nat (g := fun n : ℕ => (n:ℝ) ^ ((s - 1) / 2 - s)) ?_ ?_
  · rw [Real.summable_nat_rpow]; linarith
  · have ho : (fun x : ℝ => (Real.log x) ^ a) =O[atTop] (fun x : ℝ => x ^ ((s - 1) / 2)) :=
      (isLittleO_log_rpow_rpow_atTop a hε).isBigO
    have hmul : (fun x : ℝ => (Real.log x) ^ a / x ^ s)
        =O[atTop] (fun x : ℝ => x ^ ((s - 1) / 2) / x ^ s) := by
      simpa only [div_eq_mul_inv] using ho.mul (isBigO_refl (fun x : ℝ => (x ^ s)⁻¹) atTop)
    have heq : (fun x : ℝ => x ^ ((s - 1) / 2) / x ^ s)
        =ᶠ[atTop] (fun x : ℝ => x ^ ((s - 1) / 2 - s)) := by
      filter_upwards [eventually_gt_atTop 0] with x hx
      rw [← Real.rpow_sub hx]
    exact (hmul.trans_eventuallyEq heq).natCast_atTop

private lemma summable_vonMangoldt_div_rpow (s : ℝ) (hs : 1 < s) :
    Summable (fun n : ℕ => (Λ n : ℝ) / (n:ℝ) ^ s) := by
  refine Summable.of_nonneg_of_le (fun n => div_nonneg vonMangoldt_nonneg (by positivity)) ?_
    (summable_log_rpow_div_rpow 1 hs)
  intro n
  rw [Real.rpow_one]
  gcongr
  exact vonMangoldt_le_log

private lemma summable_c_term (s : ℝ) (hs : 1 < s) :
    Summable (fun d : ℕ => c d * ((d:ℝ) ^ (1 - s) / (s - 1))) := by
  have hs1 : (0:ℝ) < s - 1 := by linarith
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)

  refine Summable.of_nonneg_of_le (fun d => ?_) (fun d => ?_)
    ((summable_vonMangoldt_div_rpow s hs).mul_left (1 / (Real.log 2 * (s - 1))))
  ·
    refine mul_nonneg (c_nonneg d) (div_nonneg ?_ hs1.le)
    rcases eq_or_ne (d:ℝ) 0 with hd | hd
    · rw [hd, Real.zero_rpow (by linarith : (1 - s) ≠ 0)]
    · positivity
  ·
    rcases lt_or_ge d 2 with hd | hd
    · have hc : c d = 0 := by interval_cases d <;> simp
      rw [hc, zero_mul]
      exact mul_nonneg (by positivity) (div_nonneg vonMangoldt_nonneg (by positivity))
    · have hd2 : (2:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
      have hd0 : (0:ℝ) < (d:ℝ) := by linarith
      have hlogge : Real.log 2 ≤ Real.log d := Real.log_le_log (by norm_num) hd2
      have hds : (0:ℝ) < (d:ℝ) ^ s := Real.rpow_pos_of_pos hd0 s
      have hkey : c d * ((d:ℝ) ^ (1 - s) / (s - 1)) = Λ d / ((d:ℝ) ^ s * Real.log d * (s - 1)) := by
        unfold c
        rw [show (1 - s : ℝ) = -s + 1 by ring, Real.rpow_add hd0, Real.rpow_one, Real.rpow_neg hd0.le]
        field_simp

      have hcb : (d:ℝ) ^ s * Real.log 2 * (s - 1) ≤ (d:ℝ) ^ s * Real.log d * (s - 1) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlogge hds.le) hs1.le
      rw [hkey, show (1 / (Real.log 2 * (s - 1))) * ((Λ d : ℝ) / (d:ℝ) ^ s)
          = Λ d / ((d:ℝ) ^ s * Real.log 2 * (s - 1)) from by field_simp]
      exact div_le_div_of_nonneg_left vonMangoldt_nonneg (by positivity) hcb

theorem log_zeta_eq_integ_aux (s : ℝ) (hs : 1 < s) :
    Real.log (riemannZeta (s:ℂ)).re =
      (s - 1) * ∫ x in Set.Ioi 1, (Real.log (Real.log x) + γ + E₂Λ x) * x ^ (-s) := by
  rw [Mertens.log_zeta_eq_sum s hs]
  symm
  have hstep1 : ∀ x ∈ Set.Ioi (1:ℝ),
      (Real.log (Real.log x) + γ + E₂Λ x) * x ^ (-s)
        = (∑ d ∈ Finset.Ioc 0 ⌊x⌋₊, c d) * x ^ (-s) := by
    intro x hx
    simp only [Mertens.E₂Λ, c]
    ring
  have hstep2 : ∀ x ∈ Set.Ioi (1:ℝ),
      (Real.log (Real.log x) + γ + E₂Λ x) * x ^ (-s) = ∑' d : ℕ, f s d x := by
    intro x hx
    rw [hstep1 x hx]
    simp only [f]
    rw [Finset.sum_mul]
    have hx0 : (0:ℝ) ≤ x := by have := hx; simp only [Set.mem_Ioi] at this; linarith
    rw [tsum_eq_sum (s := Finset.Ioc 0 ⌊x⌋₊) ?_]
    · apply Finset.sum_congr rfl
      intro d hd
      simp only [Finset.mem_Ioc] at hd
      have hdx : (d:ℝ) ≤ x := by
        rw [← Nat.le_floor_iff hx0]; exact hd.2
      rw [Set.indicator_of_mem (by simpa using hdx)]
    · intro d hd
      simp only [Finset.mem_Ioc, not_and, not_le] at hd
      rcases Nat.eq_zero_or_pos d with hd0 | hd0
      · subst hd0; simp
      · have hfloor : ⌊x⌋₊ < d := hd hd0
        have hdx : x < (d:ℝ) := by
          rw [← Nat.floor_lt hx0]; exact hfloor
        rw [Set.indicator_of_notMem (by simpa using not_le.mpr hdx)]
        ring
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hstep2]
  have hperterm : ∀ d : ℕ, ∫ x in Set.Ioi (1:ℝ), f s d x = c d * ((d:ℝ) ^ (1 - s) / (s - 1)) := by
    intro d
    rcases Nat.eq_zero_or_pos d with hd0 | hd0
    · subst hd0; simp [f]
    simp only [f]
    rw [MeasureTheory.integral_const_mul, MeasureTheory.setIntegral_indicator measurableSet_Ici]
    congr 1
    have hdR : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd0
    have hdR0 : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd0
    set A : Set ℝ := Set.Ioi (1:ℝ) ∩ Set.Ici (d:ℝ) with hA
    have hae : A =ᵐ[volume] Set.Ioi (d:ℝ) := by
      have h1 : A =ᵐ[volume] (Set.Ici (1:ℝ) ∩ Set.Ici (d:ℝ) : Set ℝ) :=
        MeasureTheory.ae_eq_set_inter MeasureTheory.Ioi_ae_eq_Ici (ae_eq_refl _)
      rw [Set.Ici_inter_Ici, max_eq_right hdR] at h1
      exact h1.trans MeasureTheory.Ioi_ae_eq_Ici.symm
    rw [MeasureTheory.setIntegral_congr_set hae]
    rw [integral_Ioi_rpow_of_lt (by linarith : (-s:ℝ) < -1) hdR0,
      show (-s + 1 : ℝ) = 1 - s by ring]
    have hs1 : (1 - s) ≠ 0 := by linarith
    have hs2 : (s - 1) ≠ 0 := by linarith
    field_simp
    ring
  have hint : ∀ d : ℕ, MeasureTheory.IntegrableOn (f s d) (Set.Ioi (1:ℝ)) := by
    intro d
    unfold f
    apply MeasureTheory.Integrable.const_mul
    rw [show MeasureTheory.Integrable ((Set.Ici (d:ℝ)).indicator fun x => x ^ (-s))
        (volume.restrict (Set.Ioi (1:ℝ)))
      ↔ MeasureTheory.IntegrableOn ((Set.Ici (d:ℝ)).indicator fun x => x ^ (-s))
          (Set.Ioi (1:ℝ)) volume from Iff.rfl,
      MeasureTheory.integrableOn_indicator_iff measurableSet_Ici]
    apply MeasureTheory.IntegrableOn.mono_set
      (integrableOn_Ioi_rpow_of_lt (by linarith : (-s:ℝ) < -1) (by norm_num : (0:ℝ) < 1/2))
    intro x hx
    simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Ioi] at hx ⊢
    linarith [hx.2]
  have hnorm_int : ∀ d : ℕ,
      ∫ x in Set.Ioi (1:ℝ), ‖f s d x‖ = c d * ((d:ℝ) ^ (1 - s) / (s - 1)) := by
    intro d
    rw [← hperterm d]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    simp only [Set.mem_Ioi] at hx
    have hfnn : 0 ≤ f s d x := by
      simp only [f]
      apply mul_nonneg (c_nonneg d)
      by_cases hxd : (d:ℝ) ≤ x
      · rw [Set.indicator_of_mem (by simpa using hxd)]
        exact le_of_lt (Real.rpow_pos_of_pos (by linarith) _)
      · rw [Set.indicator_of_notMem (by simpa using hxd)]
    change ‖f s d x‖ = f s d x
    rw [Real.norm_eq_abs, abs_of_nonneg hfnn]
  have hinterchange : ∫ x in Set.Ioi (1:ℝ), ∑' d : ℕ, f s d x
      = ∑' d : ℕ, ∫ x in Set.Ioi (1:ℝ), f s d x := by
    refine (MeasureTheory.integral_tsum_of_summable_integral_norm hint ?_).symm
    apply (summable_c_term s hs).congr
    intro d
    exact (hnorm_int d).symm
  rw [hinterchange]
  simp_rw [hperterm]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro d
  rcases Nat.eq_zero_or_pos d with hd0 | hd0
  · subst hd0; simp
  · have hdR : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd0
    have hsub : (d:ℝ) ^ (1 - s) = (d:ℝ) ^ (-s) * (d:ℝ) := by
      rw [show (1 - s : ℝ) = -s + 1 by ring, Real.rpow_add hdR, Real.rpow_one]
    have hs1 : s - 1 ≠ 0 := by linarith
    have hneg : (d:ℝ) ^ (-s) = ((d:ℝ) ^ s)⁻¹ := by
      rw [Real.rpow_neg (le_of_lt hdR)]
    unfold c
    rw [hsub, hneg]
    field_simp

end LogZetaInteg
end

private theorem log_zeta_eq_integ (s : ℝ) (hs : 1 < s) :
    log (riemannZeta (s:ℂ)).re = (s - 1) * ∫ x in .Ioi 1, (log (log x) + γ + E₂Λ x) * x^(-s) :=
  LogZetaInteg.log_zeta_eq_integ_aux s hs

private theorem mul_integ_log_log_eq (s : ℝ) (hs : 1 < s) :
    (s - 1) * ∫ x in .Ioi 1, log (log x) * x^(-s) = - log (s - 1) + deriv Gamma 1 :=
  mul_integ_log_log_eq_aux s hs

private theorem mul_integ_gamma_eq (s) (hs : 1 < s) : (s - 1) * ∫ x in .Ioi 1, γ * x^(-s) = γ := by
  rw [MeasureTheory.integral_const_mul γ (· ^ (-s)), @integral_Ioi_rpow_of_lt (-s), one_rpow] <;>
    grind

private theorem integrableOn_Ioi_mul_rpow_neg_of_abs_le
    {c B a s : ℝ} (hc : 0 < c) (has : a + 1 < s) {f : ℝ → ℝ} (hf : Measurable f)
    (hbound : ∀ x ∈ Set.Ioi c, |f x| ≤ B * x ^ a) :
    MeasureTheory.IntegrableOn (fun x => f x * x ^ (-s)) (Set.Ioi c) := by
  have hg : MeasureTheory.IntegrableOn (fun x => B * x ^ (a - s)) (Set.Ioi c) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : a - s < -1) hc).const_mul B
  refine MeasureTheory.Integrable.mono' hg
    (hf.mul (measurable_id.pow_const (-s))).aestronglyMeasurable ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
  have hxpos : (0:ℝ) < x := hc.trans hx
  have hxs : (0:ℝ) < x ^ (-s) := Real.rpow_pos_of_pos hxpos _
  rw [norm_mul, norm_eq_abs, norm_eq_abs, abs_of_pos hxs]
  calc |f x| * x ^ (-s) ≤ B * x ^ a * x ^ (-s) :=
        mul_le_mul_of_nonneg_right (hbound x hx) hxs.le
    _ = B * x ^ (a - s) := by rw [mul_assoc, ← Real.rpow_add hxpos, sub_eq_add_neg]

private theorem integrableOn_log_log_mul_rpow (s : ℝ) (hs : 1 < s) :
    MeasureTheory.IntegrableOn (fun x => log (log x) * x ^ (-s)) (Set.Ioi 1) := by
  rw [← Set.Ioc_union_Ioi_eq_Ioi (by norm_num : (1:ℝ) ≤ 2)]
  apply MeasureTheory.IntegrableOn.union
  ·
    have hll : MeasureTheory.IntegrableOn (fun x => log (log x)) (Set.Ioc 1 2) := by
      have h : IntervalIntegrable (log ∘ log) MeasureTheory.volume 1 2 := by
        apply MeromorphicOn.intervalIntegrable_log
        intro x hx
        rw [Set.uIcc_of_le (by norm_num : (1:ℝ) ≤ 2)] at hx
        exact (analyticAt_log (by linarith [hx.1] : 0 < x)).meromorphicAt
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp h
    have hmul : MeasureTheory.IntegrableOn (fun x => x ^ (-s) * log (log x)) (Set.Ioc 1 2) := by
      apply hll.bdd_mul (c := 1)
      · fun_prop
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with x hx
        rw [norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by linarith [hx.1] : (0:ℝ) ≤ x) _)]
        calc x ^ (-s) ≤ (1:ℝ) ^ (-s) :=
              Real.rpow_le_rpow_of_nonpos (by norm_num) hx.1.le (by linarith)
          _ = 1 := Real.one_rpow _
    simpa [mul_comm] using hmul
  ·
    set ε := (s - 1) / 2 with hε
    have hεpos : 0 < ε := by rw [hε]; linarith
    refine integrableOn_Ioi_mul_rpow_neg_of_abs_le (a := ε) (B := 1 / ε + |log (log 2)|)
      (by norm_num) (by rw [hε]; linarith) (Real.measurable_log.comp Real.measurable_log) ?_
    intro x hx
    simp only [Set.mem_Ioi] at hx
    have hx1 : (1:ℝ) ≤ x ^ ε := Real.one_le_rpow (by linarith) hεpos.le
    have hlogx : 0 < log x := Real.log_pos (by linarith)
    have hlog2 : 0 < log 2 := Real.log_pos (by norm_num)
    have hmono : log 2 ≤ log x := Real.log_le_log (by norm_num) (by linarith)
    have hub : log (log x) ≤ x ^ ε / ε :=
      calc log (log x) ≤ log x := (Real.log_le_sub_one_of_pos hlogx).trans (by linarith)
        _ ≤ x ^ ε / ε := Real.log_le_rpow_div (by linarith) hεpos
    have hlb : log (log 2) ≤ log (log x) := Real.log_le_log hlog2 hmono
    have hxε : 0 ≤ x ^ ε / ε := by positivity
    calc |log (log x)| ≤ x ^ ε / ε + |log (log 2)| := by
          rw [abs_le]
          exact ⟨by linarith [neg_abs_le (log (log 2))],
            by linarith [abs_nonneg (log (log 2))]⟩
      _ ≤ (1 / ε + |log (log 2)|) * x ^ ε := by
          have h2 : |log (log 2)| ≤ |log (log 2)| * x ^ ε := le_mul_of_one_le_right (abs_nonneg _) hx1
          have h1 : x ^ ε / ε = 1 / ε * x ^ ε := by ring
          rw [add_mul]; linarith

private theorem integrableOn_γ_mul_rpow (s : ℝ) (hs : 1 < s) :
    MeasureTheory.IntegrableOn (fun x => γ * x ^ (-s)) (Set.Ioi 1) := by
  exact (integrableOn_Ioi_rpow_of_lt (by linarith : -s < -1) one_pos).const_mul γ

private theorem integrableOn_E₂Λ_mul_rpow (s : ℝ) (hs : 1 < s) :
    MeasureTheory.IntegrableOn (fun x => E₂Λ x * x ^ (-s)) (Set.Ioi 1) := by
  rw [← Set.Ioo_union_Ici_eq_Ioi (by norm_num : (1:ℝ) < 2)]
  apply MeasureTheory.IntegrableOn.union
  ·
    have hsub : Set.Ioo (1:ℝ) 2 ⊆ Set.Ioi 1 := fun x hx => hx.1
    have h1 := (integrableOn_γ_mul_rpow s hs).mono_set hsub
    have h2 := (integrableOn_log_log_mul_rpow s hs).mono_set hsub
    have hb : MeasureTheory.IntegrableOn
        (fun x => -(log (log x) * x ^ (-s)) - γ * x ^ (-s)) (Set.Ioo 1 2) :=
      h2.neg.sub h1
    apply hb.congr_fun _ measurableSet_Ioo
    intro x hx
    simp only [Set.mem_Ioo] at hx
    have hfloor : ⌊ x ⌋₊ = 1 := by
      rw [Nat.floor_eq_iff (by linarith)]
      exact ⟨by push_cast; linarith [hx.1], by push_cast; linarith [hx.2]⟩
    have hsum : (∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / ((d:ℝ) * log d)) = 0 := by rw [hfloor]; norm_num
    change -(log (log x) * x ^ (-s)) - γ * x ^ (-s)
        = (∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / (d * log d) - log (log x) - γ) * x ^ (-s)
    rw [hsum]; ring
  ·
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    refine integrableOn_Ioi_mul_rpow_neg_of_abs_le (a := 0) (B := (log 4 + 6) / log 2)
      (by norm_num) (by linarith) (by fun_prop) ?_
    intro x hx
    simp only [Set.mem_Ioi] at hx
    have hlog2 : 0 < log 2 := Real.log_pos (by norm_num)
    have hc : 0 ≤ log 4 + 6 := by positivity
    rw [Real.rpow_zero, mul_one]
    have hb2 : (log 4 + 6) / log x ≤ (log 4 + 6) / log 2 :=
      div_le_div_of_nonneg_left hc hlog2 (Real.log_le_log (by norm_num) (le_of_lt hx))
    exact (E₂Λ.abs_le (le_of_lt hx)).trans hb2

private theorem log_zeta_eq (s : ℝ) (hs : 1 < s) :
    log (riemannZeta (s:ℂ)).re = - log (s - 1) + deriv Gamma 1 + γ + (s - 1) * ∫ x in Set.Ioi 1, E₂Λ x * x^(-s) := by

  rw [log_zeta_eq_integ s hs]

  have key : (∫ x in Set.Ioi 1, (log (log x) + γ + E₂Λ x) * x ^ (-s))
      = (∫ x in Set.Ioi 1, log (log x) * x ^ (-s))
        + (∫ x in Set.Ioi 1, γ * x ^ (-s))
        + (∫ x in Set.Ioi 1, E₂Λ x * x ^ (-s)) := by
    rw [← MeasureTheory.integral_add (integrableOn_log_log_mul_rpow s hs)
      (integrableOn_γ_mul_rpow s hs)]
    rw [← MeasureTheory.integral_add (f := fun x => log (log x) * x ^ (-s) + γ * x ^ (-s))
      (g := fun x => E₂Λ x * x ^ (-s))
      ((integrableOn_log_log_mul_rpow s hs).add (integrableOn_γ_mul_rpow s hs))
      (integrableOn_E₂Λ_mul_rpow s hs)]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro x _
    ring

  rw [key, mul_add, mul_add, mul_integ_log_log_eq s hs, mul_integ_gamma_eq s hs]

private lemma zeta_pole_mul_re_tendsto_one :
    Filter.Tendsto (fun s : ℝ => (s - 1) * (riemannZeta (s : ℂ)).re)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds 1) := by
  have hofReal :
      Filter.Tendsto (fun s : ℝ => (s : ℂ)) (nhdsWithin 1 (Set.Ioi 1))
        (nhdsWithin (1 : ℂ) ({1} : Set ℂ)ᶜ) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · exact (Complex.continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact Set.mem_compl_singleton_iff.mpr (by
        norm_num
        exact ne_of_gt (Set.mem_Ioi.mp hs))
  have hcomplex :
      Filter.Tendsto (fun s : ℝ => ((s : ℂ) - 1) * riemannZeta (s : ℂ))
        (nhdsWithin 1 (Set.Ioi 1)) (nhds 1) :=
    riemannZeta_residue_one.comp hofReal
  have hreal :
      Filter.Tendsto
        (fun s : ℝ => (((s : ℂ) - 1) * riemannZeta (s : ℂ)).re)
        (nhdsWithin 1 (Set.Ioi 1)) (nhds (1 : ℝ)) :=
    (Complex.continuous_re.tendsto (1 : ℂ)).comp hcomplex
  simpa [Complex.ofReal_sub, Complex.ofReal_mul] using hreal

private theorem log_zeta_limit :
    Filter.Tendsto
      (fun s : ℝ => Real.log (riemannZeta (s : ℂ)).re + Real.log (s - 1))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds 0) := by
  have hlog :
      Filter.Tendsto
        (fun s : ℝ => Real.log ((s - 1) * (riemannZeta (s : ℂ)).re))
        (nhdsWithin 1 (Set.Ioi 1)) (nhds (Real.log 1)) :=
    (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp
      zeta_pole_mul_re_tendsto_one
  have hEq :
      (fun s : ℝ => Real.log (riemannZeta (s : ℂ)).re + Real.log (s - 1))
        =ᶠ[nhdsWithin 1 (Set.Ioi 1)]
      fun s : ℝ => Real.log ((s - 1) * (riemannZeta (s : ℂ)).re) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hspos : 0 < s - 1 := sub_pos.mpr (Set.mem_Ioi.mp hs)
    have hzpos : 0 < (riemannZeta (s : ℂ)).re :=
      riemannZeta_re_pos_of_one_lt (Set.mem_Ioi.mp hs)
    rw [Real.log_mul hspos.ne' hzpos.ne']
    ring
  simpa using hlog.congr' (hEq.mono fun s hs => hs.symm)

section
open MeasureTheory Set

private lemma measurable_E₂Λ : Measurable E₂Λ := by fun_prop

private lemma E₂Λ_eq_on_Ioo {x : ℝ} (hx : x ∈ Set.Ioo (1 : ℝ) 2) :
    E₂Λ x = - log (log x) - γ := by
  obtain ⟨h1, h2⟩ := hx
  have hf : ⌊x⌋₊ = 1 := by
    rw [Nat.floor_eq_iff (by linarith)]
    exact ⟨by exact_mod_cast h1.le, by exact_mod_cast h2⟩
  unfold E₂Λ
  rw [hf]
  simp

private lemma abs_E₂Λ_le_on_Ioo {x : ℝ} (hx : x ∈ Set.Ioo (1 : ℝ) 2) :
    |E₂Λ x| ≤ |log (x - 1)| + log 2 + |γ| := by
  obtain ⟨hx1, hx2⟩ := hx
  have hloglog : |log (log x)| ≤ |log (x - 1)| + log 2 := by
    have hxpos : (0:ℝ) < x := by linarith
    have hlogx_pos : 0 < log x := Real.log_pos hx1
    have hxm1 : 0 < x - 1 := by linarith
    have hub : log x ≤ x - 1 := by have := Real.log_le_sub_one_of_pos hxpos; linarith
    have hlb2 : (x - 1) / 2 ≤ log x := by
      have h := Real.log_le_sub_one_of_pos (x := 1 / x) (by positivity)
      rw [Real.log_div one_ne_zero (by positivity), Real.log_one] at h
      simp only [zero_sub] at h
      have h12 : (x - 1) / 2 ≤ 1 - 1 / x := by
        rw [← sub_nonneg]
        have e : (1 - 1 / x) - (x - 1) / 2 = (3 * x - 2 - x ^ 2) / (2 * x) := by field_simp; ring
        rw [e]; exact div_nonneg (by nlinarith [hx1, hx2]) (by positivity)
      linarith
    have hupper : log (log x) ≤ log (x - 1) := Real.log_le_log hlogx_pos hub
    have hlower : log (x - 1) - log 2 ≤ log (log x) := by
      have := Real.log_le_log (show (0:ℝ) < (x - 1) / 2 by positivity) hlb2
      rwa [Real.log_div (by linarith) (by norm_num)] at this
    have h2 : (0:ℝ) ≤ log 2 := Real.log_nonneg (by norm_num)
    rw [abs_le]
    exact ⟨by have := neg_abs_le (log (x - 1)); linarith,
          by have := le_abs_self (log (x - 1)); linarith⟩
  rw [E₂Λ_eq_on_Ioo ⟨hx1, hx2⟩]
  have htri : |(- log (log x) - γ)| ≤ |log (log x)| + |γ| := by
    have h := abs_sub (-log (log x)) γ
    rwa [abs_neg] at h
  linarith

private lemma abs_E₂Λ_le_const {x : ℝ} (hx : 2 ≤ x) :
    |E₂Λ x| ≤ (log 4 + 6) / log 2 :=
  (E₂Λ.abs_le hx).trans <| div_le_div_of_nonneg_left (by positivity)
    (Real.log_pos (by norm_num)) (Real.log_le_log (by norm_num) hx)

private lemma integrableOn_log_sub_one_bound :
    IntegrableOn (fun x => |log (x - 1)| + log 2 + |γ|) (Set.Ioo 1 2) volume := by
  have hlog : IntegrableOn (fun x => |log (x - 1)|) (Set.Ioo 1 2) volume := by
    have h0 : IntervalIntegrable (fun x => log x) volume 0 1 :=
      intervalIntegral.intervalIntegrable_log'
    have h1 : IntervalIntegrable (fun x => log (x - 1)) volume (0 + 1) (1 + 1) :=
      h0.comp_sub_right 1
    norm_num at h1
    exact (h1.1.mono_set Set.Ioo_subset_Ioc_self).abs
  have hc : IntegrableOn (fun _ : ℝ => log 2 + |γ|) (Set.Ioo (1 : ℝ) 2) volume :=
    integrableOn_const (measure_Ioo_lt_top).ne (by finiteness)
  have hsum : IntegrableOn (fun x => |log (x - 1)| + (log 2 + |γ|)) (Set.Ioo 1 2) volume :=
    hlog.add hc
  exact hsum.congr_fun (fun x _ => by ring) measurableSet_Ioo

private lemma integrableOn_E₂Λ_Ioo {X : ℝ} (_hX : 2 ≤ X) :
    IntegrableOn E₂Λ (Set.Ioo 1 X) volume := by
  have hsub : Set.Ioo (1 : ℝ) X ⊆ Set.Ioo 1 2 ∪ Set.Icc 2 X := by
    intro x hx; simp only [Set.mem_Ioo, Set.mem_union, Set.mem_Icc] at *
    rcases lt_or_ge x 2 with h | h
    · exact Or.inl ⟨hx.1, h⟩
    · exact Or.inr ⟨h, hx.2.le⟩
  apply IntegrableOn.mono_set _ hsub
  apply IntegrableOn.union
  · have hg := integrableOn_log_sub_one_bound
    refine Integrable.mono' hg measurable_E₂Λ.aestronglyMeasurable ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with x hx
    rw [Real.norm_eq_abs]; exact abs_E₂Λ_le_on_Ioo hx
  · refine Integrable.mono' (g := fun _ => (log 4 + 6) / log 2) ?_
      measurable_E₂Λ.aestronglyMeasurable ?_
    · exact integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top) (by finiteness)
    · filter_upwards [self_mem_ae_restrict measurableSet_Icc] with x hx
      rw [Real.norm_eq_abs]; exact abs_E₂Λ_le_const hx.1

private lemma sub_one_mul_integral_E₂Λ_tendsto :
    Filter.Tendsto (fun s : ℝ => (s - 1) * ∫ x in Set.Ioi 1, E₂Λ x * x ^ (-s))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds 0) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε

  obtain ⟨X₀, hX₀⟩ : ∃ X, ∀ x ≥ X, |E₂Λ x| ≤ ε / 2 := by
    have := E₂Λ.bound'.def (by positivity : (0:ℝ) < ε / 2)
    simp only [Real.norm_eq_abs, abs_one, mul_one] at this
    rw [Filter.eventually_atTop] at this; exact this
  set X := max X₀ 2 with hXdef
  have hX2 : 2 ≤ X := le_max_right _ _
  have hXge : ∀ x ≥ X, |E₂Λ x| ≤ ε / 2 := fun x hx => hX₀ x (le_trans (le_max_left _ _) hx)

  set B := ∫ x in Set.Ioo 1 X, |E₂Λ x| with hBdef
  have hB0 : 0 ≤ B := setIntegral_nonneg measurableSet_Ioo (fun x _ => abs_nonneg _)
  refine ⟨min 1 (ε / 2 / (B + 1)), by positivity, ?_⟩
  intro s hs hdist
  simp only [Set.mem_Ioi] at hs
  rw [Real.dist_eq] at hdist
  have hs1 : s - 1 < min 1 (ε / 2 / (B + 1)) := by
    rw [abs_of_pos (by linarith)] at hdist; exact hdist
  have hsm1 : 0 < s - 1 := by linarith

  have hintAbs : IntegrableOn (fun x => |E₂Λ x| * x ^ (-s)) (Set.Ioi 1) volume := by
    have h2 : IntegrableOn (fun x => |E₂Λ x * x ^ (-s)|) (Set.Ioi 1) volume :=
      (integrableOn_E₂Λ_mul_rpow s hs).abs
    refine h2.congr_fun ?_ measurableSet_Ioi
    intro x hx; simp only [Set.mem_Ioi] at hx
    change |E₂Λ x * x ^ (-s)| = |E₂Λ x| * x ^ (-s)
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (by linarith) _)]
  have hintAbsIoc : IntegrableOn (fun x => |E₂Λ x| * x ^ (-s)) (Set.Ioc 1 X) volume :=
    hintAbs.mono_set Set.Ioc_subset_Ioi_self
  have hintAbsIoiX : IntegrableOn (fun x => |E₂Λ x| * x ^ (-s)) (Set.Ioi X) volume :=
    hintAbs.mono_set (Set.Ioi_subset_Ioi (by linarith))

  have hsplit : ∫ x in Set.Ioi 1, |E₂Λ x| * x ^ (-s) =
      (∫ x in Set.Ioc 1 X, |E₂Λ x| * x ^ (-s)) + ∫ x in Set.Ioi X, |E₂Λ x| * x ^ (-s) := by
    have hu : Set.Ioi (1:ℝ) = Set.Ioc 1 X ∪ Set.Ioi X :=
      (Set.Ioc_union_Ioi_eq_Ioi (by linarith)).symm
    rw [hu, setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hintAbs.mono_set (by rw [hu]; exact Set.subset_union_left))
      (hintAbs.mono_set (by rw [hu]; exact Set.subset_union_right))]

  have hp1 : ∫ x in Set.Ioc 1 X, |E₂Λ x| * x ^ (-s) ≤ B := by
    rw [hBdef]
    have ha : IntegrableOn (fun x => |E₂Λ x|) (Set.Ioo 1 X) volume := (integrableOn_E₂Λ_Ioo hX2).abs
    have habsIoc : IntegrableOn (fun x => |E₂Λ x|) (Set.Ioc 1 X) volume :=
      ha.congr_set_ae (Ioo_ae_eq_Ioc).symm
    rw [← integral_Ioc_eq_integral_Ioo]
    apply setIntegral_mono_on hintAbsIoc habsIoc measurableSet_Ioc
    intro x hx
    have hx1 : (1:ℝ) ≤ x := by have := hx.1; linarith
    have hle1 : x ^ (-s) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by linarith)
    calc |E₂Λ x| * x ^ (-s) ≤ |E₂Λ x| * 1 := by gcongr
      _ = |E₂Λ x| := mul_one _

  have hp2 : ∫ x in Set.Ioi X, |E₂Λ x| * x ^ (-s) ≤ (ε / 2) * (X ^ (1 - s) / (s - 1)) := by
    have hrpow_int : IntegrableOn (fun x : ℝ => x ^ (-s)) (Set.Ioi X) volume :=
      integrableOn_Ioi_rpow_of_lt (by linarith) (by linarith : (0:ℝ) < X)
    have hval : ∫ x in Set.Ioi X, x ^ (-s) = X ^ (1 - s) / (s - 1) := by
      rw [integral_Ioi_rpow_of_lt (by linarith) (by linarith : (0:ℝ) < X),
        show -s + 1 = 1 - s by ring, show (1:ℝ) - s = -(s - 1) by ring]
      rw [div_neg, neg_div, neg_neg]
    rw [← hval, ← integral_const_mul]
    apply setIntegral_mono_on hintAbsIoiX (hrpow_int.const_mul (ε / 2)) measurableSet_Ioi
    intro x hx
    have hxpos : (0:ℝ) < x := by simp only [Set.mem_Ioi] at hx; linarith
    have hnn : 0 ≤ x ^ (-s) := Real.rpow_nonneg hxpos.le _
    have hb : |E₂Λ x| ≤ ε / 2 := hXge x (by simp only [Set.mem_Ioi] at hx; linarith)
    gcongr
  have hXpow : X ^ (1 - s) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)

  have hbound : (s - 1) * ∫ x in Set.Ioi 1, |E₂Λ x| * x ^ (-s) ≤ (s - 1) * B + ε / 2 := by
    rw [hsplit, mul_add]
    have ht2 : (s - 1) * ∫ x in Set.Ioi X, |E₂Λ x| * x ^ (-s) ≤ ε / 2 := by
      calc (s - 1) * ∫ x in Set.Ioi X, |E₂Λ x| * x ^ (-s)
          ≤ (s - 1) * ((ε / 2) * (X ^ (1 - s) / (s - 1))) :=
            mul_le_mul_of_nonneg_left hp2 hsm1.le
        _ = (ε / 2) * X ^ (1 - s) := by
              have hne : s - 1 ≠ 0 := by linarith
              field_simp
        _ ≤ (ε / 2) * 1 := by gcongr
        _ = ε / 2 := mul_one _
    have ht1 : (s - 1) * ∫ x in Set.Ioc 1 X, |E₂Λ x| * x ^ (-s) ≤ (s - 1) * B :=
      mul_le_mul_of_nonneg_left hp1 hsm1.le
    linarith

  have habs_le : |(s - 1) * ∫ x in Set.Ioi 1, E₂Λ x * x ^ (-s)|
      ≤ (s - 1) * ∫ x in Set.Ioi 1, |E₂Λ x| * x ^ (-s) := by
    rw [abs_mul, abs_of_pos hsm1]
    gcongr
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_integral_norm _).trans_eq ?_
    refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    simp only [Set.mem_Ioi] at hx
    change ‖E₂Λ x * x ^ (-s)‖ = |E₂Λ x| * x ^ (-s)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (by linarith) _)]
  rw [Real.dist_eq, sub_zero]

  have hfin : (s - 1) * B + ε / 2 < ε := by
    have hlt : s - 1 < ε / 2 / (B + 1) := lt_of_lt_of_le hs1 (min_le_right _ _)
    have hBp : 0 < B + 1 := by linarith
    have h1 : (s - 1) * B ≤ (s - 1) * (B + 1) := by nlinarith
    have h2 : (s - 1) * (B + 1) < (ε / 2 / (B + 1)) * (B + 1) := mul_lt_mul_of_pos_right hlt hBp
    have h3 : (ε / 2 / (B + 1)) * (B + 1) = ε / 2 := by field_simp
    linarith
  calc |(s - 1) * ∫ x in Set.Ioi 1, E₂Λ x * x ^ (-s)|
      ≤ (s - 1) * ∫ x in Set.Ioi 1, |E₂Λ x| * x ^ (-s) := habs_le
    _ ≤ (s - 1) * B + ε / 2 := hbound
    _ < ε := hfin

end

theorem deriv_gamma_add_γ_eq_zero : deriv Gamma 1 + γ = 0 := by

  have key : ∀ s : ℝ, 1 < s →
      (Real.log (riemannZeta (s:ℂ)).re + Real.log (s - 1))
        - (s - 1) * ∫ x in Set.Ioi 1, E₂Λ x * x ^ (-s) = deriv Gamma 1 + γ := by
    intro s hs
    have h := log_zeta_eq s hs
    linarith

  have hconst : Filter.Tendsto
      (fun s : ℝ => (Real.log (riemannZeta (s:ℂ)).re + Real.log (s - 1))
        - (s - 1) * ∫ x in Set.Ioi 1, E₂Λ x * x ^ (-s))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds (deriv Gamma 1 + γ)) := by
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (key s hs).symm

  have hlim := log_zeta_limit.sub sub_one_mul_integral_E₂Λ_tendsto
  rw [sub_zero] at hlim
  exact tendsto_nhds_unique hconst hlim

theorem γ.eq_eulerMascheroni : γ = eulerMascheroniConstant := by
  linarith [Real.eulerMascheroniConstant_eq_neg_deriv, deriv_gamma_add_γ_eq_zero]

theorem sum_mangoldt_div_log_eq (x : ℝ) : ∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / (d * log d) = log (log x) + eulerMascheroniConstant + E₂Λ x := by
    grind [γ.eq_eulerMascheroni]

lemma HasSum_log_one_sub_one_div_prime {p : ℕ} (hp : p.Prime) :
    HasSum (fun n : ℕ ↦ (-1 : ℝ) / (( n + 1) * p ^ (n + 1))) (log (1 - 1 / p)) := by
  convert! Real.hasSum_pow_div_log_of_abs_lt_one (x := 1 / p) _|>.neg using 1
  · ext
    rw [div_pow, one_pow, div_div]
    ring
  · ring
  · simp only [one_div, abs_inv, Nat.abs_cast]
    exact inv_lt_one_of_one_lt₀ (mod_cast hp.one_lt)

noncomputable abbrev M_eq_f (n : ℕ) :=
    if ¬n.Prime then Λ n /(n * log n) else 0

lemma M_eq_f.sum_primes :
    ∑' (p : Nat.Primes), M_eq_f p = 0 := by
  convert! tsum_zero with p
  grind

lemma tsum_primes_eq_tsum_ite (f : ℕ → ℝ) :
    ∑' (n : Nat.Primes), f n = ∑' (n : ℕ), if n.Prime then f n else 0 := by
  convert! _root_.tsum_subtype Nat.Prime f using 2
  ext
  simp [Set.indicator]
  congr

noncomputable def E₃ (x : ℝ) : ℝ := ∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, log (1 - (1:ℝ) / p) + log (log x) + eulerMascheroniConstant

theorem prod_one_minus_div_prime_eq {x : ℝ} (hx : 1 < x) :
    ∏ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, (1 - (1 : ℝ) / p) =
      exp (-eulerMascheroniConstant) * exp (E₃ x) / log x := by
  have hlog : 0 < log x := log_pos hx
  have hpos : ∀ {p : ℕ}, p.Prime → (0 : ℝ) < 1 - 1 / p := fun {p} hp ↦ by
    have : (2 : ℝ) ≤ p := mod_cast hp.two_le
    grind [one_div_le_one_div_of_le two_pos this]
  rw [E₃, exp_add, exp_add, exp_sum, exp_log hlog, exp_neg,
    prod_congr rfl fun p hp ↦ exp_log (hpos (mem_filter.mp hp).2)]
  field_simp

noncomputable abbrev M_eq_summand (p : ℕ) := if p.Prime then log (1 - 1 / p) + 1 / p else 0

lemma M_eq_summand_bound (n : ℕ) :
    |M_eq_summand n| ≤ 2 / n ^ 2 := by
  unfold M_eq_summand
  split_ifs with h
  · trans 1 / n ^ 2 / (1 - 1 / n)
    · convert abs_log_sub_add_sum_range_le (x := 1 / n) _ 1 using 1
      · rw [add_comm]
        simp
      · rw [abs_of_nonneg (by simp)]
        ring
      · simpa using inv_lt_one_of_one_lt₀ (mod_cast h.one_lt)
    rw [(by ring : (2 : ℝ) / n ^ 2 = 1 / n ^ 2 / (1 / 2))]
    gcongr
    suffices (1 : ℝ) / n ≤ 1 / 2 by linarith
    gcongr
    exact_mod_cast h.two_le
  · rw [abs_zero]
    positivity

lemma M_eq_summable : Summable M_eq_summand := by
  apply Summable.of_abs
  exact Summable.of_nonneg_of_le (by simp) M_eq_summand_bound (Summable.const_div (by simp) _)

lemma M_eq_f.summable : Summable M_eq_f := by
  refine (vonMangoldt.summable_residueClass_non_primes_div (0 : ZMod 1)).of_norm_bounded_eventually_nat ?_
  filter_upwards [eventually_ge_atTop 3] with n hn
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hl : 1 ≤ log (n : ℝ) := (le_log_iff_exp_le (by linarith : 0 < (n : ℝ))).2
    (exp_one_lt_three.le.trans hn')
  by_cases hp : n.Prime
  · simp [M_eq_f, hp]
  · simp only [M_eq_f, hp, not_false_eq_true, if_true, if_false]
    have hΛ : vonMangoldt.residueClass (0 : ZMod 1) n = Λ n := by
      simp [vonMangoldt.residueClass, Set.indicator, Subsingleton.elim (n : ZMod 1) 0]
    rw [hΛ, ← div_div, Real.norm_of_nonneg (by positivity)]
    exact div_le_self (by positivity) hl

lemma tsum_M_eq_f_eq_tsum :
    -∑' (n : ℕ), M_eq_f n = ∑' p : ℕ, if p.Prime then log (1 - 1 / p) + 1 / p else 0 := by
  rw [tsum_eq_tsum_primes_add_tsum_primes_of_support_subset_prime_powers M_eq_f.summable
    (fun n hn ↦ (by simp_all [vonMangoldt_ne_zero_iff])), M_eq_f.sum_primes, zero_add,
    tsum_primes_eq_tsum_ite (fun p ↦ ∑' (k : ℕ), M_eq_f (p ^ (k + 2))), ← tsum_neg]
  refine tsum_congr fun n ↦ ?_
  split_ifs with hn
  · rw [← HasSum_log_one_sub_one_div_prime hn|>.tsum_eq, HasSum_log_one_sub_one_div_prime hn|>.summable.tsum_eq_zero_add]
    simp only [ite_not, Nat.cast_pow, log_pow, Nat.cast_add, Nat.cast_ofNat, CharP.cast_eq_zero,
      zero_add, pow_one, one_mul, Nat.cast_one, one_div]
    trans -∑' (k : ℕ), (1 : ℝ) / ((k + 2) * n ^ (k + 2))
    · congr
      ext k
      have : ¬(Nat.Prime (n ^ (k + 2))) := by exact Nat.Prime.not_prime_pow (by grind)
      simp only [this, ↓reduceIte, one_div, mul_inv_rev]
      rw [vonMangoldt_apply_pow (by grind), vonMangoldt_apply_prime hn]
      have : log n ≠ 0 := by simp; grind [hn.two_le]
      field
    · rw [← tsum_neg]
      ring_nf
      congr
      ext
      ring_nf
  · ring

private lemma partial_zero_floor {f : ℕ → ℝ} (hf : Summable f) (h0 : f 0=0) :
    Tendsto (fun x : ℝ => ∑ n ∈ Ioc 0 ⌊x⌋₊, f n) atTop (𝓝 (∑' n, f n)) := by
  have h := hf.hasSum.tendsto_sum_nat.comp ((tendsto_add_atTop_nat 1).comp (tendsto_nat_floor_atTop (α:=ℝ)))
  apply h.congr
  intro x
  change ∑ n ∈ range (⌊x⌋₊+1), f n = _
  rw [Nat.range_succ_eq_Icc_zero, ←add_sum_Ioc_eq_sum_Icc (Nat.zero_le _), h0, zero_add]

lemma qualitative_product_error (hf : Summable M_eq_f)
    (cancel : -(∑' n : ℕ, M_eq_f n)=∑' p : ℕ, M_eq_summand p) :
    Tendsto E₃ atTop (𝓝 0) := by
  have hs := partial_zero_floor M_eq_summable (by simp [M_eq_summand])
  have hn := partial_zero_floor hf (by simp [M_eq_f])
  have herr : Tendsto E₂Λ atTop (𝓝 0) := (isLittleO_one_iff ℝ).mp E₂Λ.bound'
  have both := (hs.add hn).sub herr
  rw [←cancel, neg_add_cancel, sub_zero] at both
  apply both.congr
  intro x
  have split (n : ℕ) : M_eq_summand n + M_eq_f n =
      (if n.Prime then log (1-1/(n:ℝ)) else 0) + Λ n / (n*log n) := by
    by_cases prime : n.Prime
    · simp only [M_eq_summand,M_eq_f,prime,not_true_eq_false,↓reduceIte,add_zero,
        vonMangoldt_apply_prime prime]
      have ne : log n ≠ 0 := by simp; grind [prime.two_le]
      field_simp
    · simp [M_eq_summand,M_eq_f,prime]
  change (∑ p ∈ Ioc 0 ⌊x⌋₊, M_eq_summand p) + (∑ p ∈ Ioc 0 ⌊x⌋₊, M_eq_f p) - E₂Λ x = _
  rw [←sum_add_distrib]
  simp_rw [split]
  rw [sum_add_distrib, sum_mangoldt_div_log_eq, E₃, sum_filter]
  ring

theorem E₃.bound'' : (fun x ↦ ∏ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (1 - (1:ℝ) / p)) ~[atTop] (fun x ↦ exp (-eulerMascheroniConstant) / log x) := by
   rw [isEquivalent_iff_tendsto_one]
   · convert Tendsto.congr' ?_ (Tendsto.rexp (qualitative_product_error M_eq_f.summable tsum_M_eq_f_eq_tsum)) using 2 with x
     · simp
     simp only [Filter.EventuallyEq, Pi.div_apply, eventually_atTop]; use 2; intro x hx
     rw [prod_one_minus_div_prime_eq (by linarith)]
     have : 0 < log x := by apply log_pos; linarith
     field_simp
   simp only [ne_eq, div_eq_zero_iff, exp_ne_zero, log_eq_zero, eventually_atTop]; use 2
   grind

end Mertens
end
open Finset Filter Asymptotics Real Topology

theorem Mertens.qualitative_H1 : OMA.R_Erdos694_erdos_694_R2.H1 := by
  let F (y : ℝ) := ∏ p ∈ (Icc 1 ⌊y⌋₊).filter Nat.Prime, ((p : ℝ) / (p - 1))
  let G (y : ℝ) := exp eulerMascheroniConstant * log y
  have hF : (fun y : ℝ ↦ ∏ p ∈ (Ioc 0 ⌊y⌋₊).filter Nat.Prime, (1 - (1 : ℝ) / p))⁻¹ = F := by
    funext y
    change (∏ p ∈ (Icc 1 ⌊y⌋₊).filter Nat.Prime, (1 - (1 : ℝ) / p))⁻¹ = _
    rw [← Finset.prod_inv_distrib]
    apply Finset.prod_congr rfl
    intro p hp
    have h0 : (p : ℝ) ≠ 0 := by exact_mod_cast (mem_filter.mp hp).2.ne_zero
    rw [one_sub_div h0, inv_div]
  have hG : (fun y : ℝ ↦ exp (-eulerMascheroniConstant) / log y)⁻¹ = G := by
    funext y
    simp [G, Real.exp_neg, mul_comm, div_eq_mul_inv]
  have he := Mertens.E₃.bound''.inv
  rw [hF, hG] at he
  apply (isEquivalent_iff_tendsto_one (u := F) (v := G) ?_).1 he
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with y hy
  exact mul_ne_zero (exp_ne_zero _) (log_pos hy).ne'
end

section
/- The character-sum input below is the previously checked Siegel–Walfisz estimate
from open-math-agents #8180, commit 0675effa26d78cdd4eb11a9fd04c6c4ec6f10809.
The original notices, authors and source pins are retained.
The new argument chooses a common interval using elementary Chebyshev estimates,
then applies character orthogonality and removes prime powers to obtain the supply
simultaneously for every prime modulus at most a fixed power of the dyadic exponent. -/
/- Adapted and modified from Whidden (7a1748306e026825ed6a5555516cc2f28989b2ac), PrimeNumberTheoremAnd, Robin1984 and openai/math (3344da59991ed94f9ba711217b29c1d760badfa6, BombieriVinogradov character blocks). Modified for the frozen H1 checker. Sources: kimihiro64/bombieri-vinogradov, kimihiro64/PrimeNumberTheoremAnd@0f15a38c619298b5cd786d39a84dd4bb8997324c, kimihiro64/Robin1984@bfa72aec0c25c8ee29cefe4449d778ff30412bee; openai/math. All four distribute the following Apache-2.0 license.
Authors: James Sundstrom
Authors: Matteo Cipollina
Authors: Michael Stoll
Authors: Robby Sneiderman
Authors: Stefan Kebekus, Matteo Cipollina
Copyright (c) 2024 James Sundstrom. All rights reserved.
Copyright (c) 2024 Michael Stoll. All rights reserved.
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Copyright (c) 2026. All rights reserved.
                                 Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      "License" shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      "Licensor" shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      "Legal Entity" shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      "control" means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      "You" (or "Your") shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      "Source" form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      "Object" form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      "Work" shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      "Derivative Works" shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      "Contribution" shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, "submitted"
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as "Not a Contribution."

      "Contributor" shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a "NOTICE" text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an "AS IS" BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

   END OF TERMS AND CONDITIONS

   APPENDIX: How to apply the Apache License to your work.

      To apply the Apache License to your work, attach the following
      boilerplate notice, with the fields enclosed by brackets "[]"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright [yyyy] [name of copyright owner]

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
 -/

section

section

open Complex Set Topology

open scoped Interval

variable {z w : ℂ} {c : ℝ}

namespace Rectangle

end Rectangle

def RectangleBorder (z w : ℂ) : Set ℂ :=
  [[z.re, w.re]] ×ℂ {z.im} ∪ {z.re} ×ℂ [[z.im, w.im]] ∪
    [[z.re, w.re]] ×ℂ {w.im} ∪ {w.re} ×ℂ [[z.im, w.im]]

lemma mem_Rect {z w : ℂ} (zRe_lt_wRe : z.re ≤ w.re) (zIm_lt_wIm : z.im ≤ w.im) (p : ℂ) :
    p ∈ Rectangle z w ↔
      z.re ≤ p.re ∧ p.re ≤ w.re ∧ z.im ≤ p.im ∧ p.im ≤ w.im := by
  rw [Rectangle, uIcc_of_le zRe_lt_wRe, uIcc_of_le zIm_lt_wIm]
  exact and_assoc

theorem Set.left_not_mem_uIoo {a b : ℝ} : a ∉ Set.uIoo a b :=
  fun ⟨h1, h2⟩ ↦ (left_lt_sup.mp h2) (le_of_not_ge (inf_lt_left.mp h1))

theorem Set.right_not_mem_uIoo {a b : ℝ} : b ∉ Set.uIoo a b :=
  fun ⟨h1, h2⟩ ↦ (right_lt_sup.mp h2) (le_of_not_ge (inf_lt_right.mp h1))

theorem Set.ne_left_of_mem_uIoo {a b c : ℝ} (hc : c ∈ Set.uIoo a b) : c ≠ a :=
  fun h ↦ Set.left_not_mem_uIoo (h ▸ hc)

theorem Set.ne_right_of_mem_uIoo {a b c : ℝ} (hc : c ∈ Set.uIoo a b) : c ≠ b :=
  fun h ↦ Set.right_not_mem_uIoo (h ▸ hc)

lemma rectangleBorder_subset_rectangle (z w : ℂ) : RectangleBorder z w ⊆ Rectangle z w := by
  intro x hx
  obtain ⟨⟨h | h⟩ | h⟩ | h := hx
  · exact ⟨h.1, h.2 ▸ left_mem_uIcc⟩
  · exact ⟨h.1 ▸ left_mem_uIcc, h.2⟩
  · exact ⟨h.1, h.2 ▸ right_mem_uIcc⟩
  · exact ⟨h.1 ▸ right_mem_uIcc, h.2⟩

lemma rectangleBorder_disjoint_singleton {z w p : ℂ}
    (h : p.re ≠ z.re ∧ p.re ≠ w.re ∧ p.im ≠ z.im ∧ p.im ≠ w.im) :
    Disjoint (RectangleBorder z w) {p} := by
  refine disjoint_singleton_right.mpr ?_
  simp_rw [RectangleBorder, Set.mem_union, not_or]
  exact ⟨⟨⟨fun hc ↦ h.2.2.1 hc.2, fun hc ↦ h.1 hc.1⟩, fun hc ↦ h.2.2.2 hc.2⟩,
    fun hc ↦ h.2.1 hc.1⟩

lemma rectangle_mem_nhds_iff {z w p : ℂ} :
    Rectangle z w ∈ 𝓝 p ↔ p ∈ (Set.uIoo z.re w.re) ×ℂ (Set.uIoo z.im w.im) := by
  simp_rw [← mem_interior_iff_mem_nhds, Rectangle, Complex.interior_reProdIm, uIoo, uIcc,
    interior_Icc]

lemma mapsTo_rectangleBorder_left_re (z w : ℂ) :
    MapsTo (fun (y : ℝ) => ↑z.re + ↑y * I) [[z.im, w.im]] (RectangleBorder z w) :=
  (Set.mapsTo_image _ _).mono subset_rfl fun _ ↦
    by simp_all [verticalSegment_eq, RectangleBorder]

lemma mapsTo_rectangleBorder_right_re (z w : ℂ) :
    MapsTo (fun (y : ℝ) => ↑w.re + ↑y * I) [[z.im, w.im]] (RectangleBorder z w) :=
  (Set.mapsTo_image _ _).mono subset_rfl fun _ ↦
    by simp_all [verticalSegment_eq, RectangleBorder]

lemma mapsTo_rectangleBorder_left_im (z w : ℂ) :
    MapsTo (fun (x : ℝ) => ↑x + z.im * I) [[z.re, w.re]] (RectangleBorder z w) :=
  (Set.mapsTo_image _ _).mono subset_rfl fun _ ↦
    by simp_all [horizontalSegment_eq, RectangleBorder]

lemma mapsTo_rectangleBorder_right_im (z w : ℂ) :
    MapsTo (fun (x : ℝ) => ↑x + w.im * I) [[z.re, w.re]] (RectangleBorder z w) :=
  (Set.mapsTo_image _ _).mono subset_rfl fun _ ↦
    by simp_all [horizontalSegment_eq, RectangleBorder]

theorem not_mem_rectangleBorder_of_rectangle_mem_nhds {z w p : ℂ}
    (hp : Rectangle z w ∈ 𝓝 p) :
    p ∉ RectangleBorder z w := by
  refine Set.disjoint_right.mp (rectangleBorder_disjoint_singleton ?_) rfl
  have h1 := rectangle_mem_nhds_iff.mp hp
  exact ⟨Set.ne_left_of_mem_uIoo h1.1, Set.ne_right_of_mem_uIoo h1.1,
    Set.ne_left_of_mem_uIoo h1.2, Set.ne_right_of_mem_uIoo h1.2⟩

end

section

open Complex BigOperators Nat Classical Real Topology Filter
open Set MeasureTheory intervalIntegral Asymptotics

open scoped Interval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f g : ℂ → E} {z w p c A : ℂ}
  {x x₁ x₂ y y₁ y₂ σ : ℝ}

noncomputable def HIntegral (f : ℂ → E) (x₁ x₂ y : ℝ) : E :=
    ∫ x in x₁..x₂, f (x + y * I)

noncomputable def VIntegral (f : ℂ → E) (x y₁ y₂ : ℝ) : E :=
    I • ∫ y in y₁..y₂, f (x + y * I)

noncomputable def HIntegral' (f : ℂ → E) (x₁ x₂ y : ℝ) : E :=
    (1 / (2 * π * I)) • HIntegral f x₁ x₂ y

noncomputable def VIntegral' (f : ℂ → E) (x y₁ y₂ : ℝ) : E :=
    (1 / (2 * π * I)) • VIntegral f x y₁ y₂

noncomputable def RectangleIntegral (f : ℂ → E) (z w : ℂ) : E :=
    HIntegral f z.re w.re z.im - HIntegral f z.re w.re w.im +
    VIntegral f w.re z.im w.im - VIntegral f z.re z.im w.im

noncomputable abbrev RectangleIntegral' (f : ℂ → E) (z w : ℂ) : E :=
    (1 / (2 * π * I)) • RectangleIntegral f z w

abbrev HolomorphicOn (f : ℂ → E) (s : Set ℂ) : Prop :=
    DifferentiableOn ℂ f s

theorem HolomorphicOn.vanishesOnRectangle [CompleteSpace E]
    {U : Set ℂ} (f_holo : HolomorphicOn f U)
    (hU : Rectangle z w ⊆ U) :
    RectangleIntegral f z w = 0 :=
  integral_boundary_rect_eq_zero_of_differentiableOn f z w
    (f_holo.mono hU)

theorem RectangleIntegral_congr (h : Set.EqOn f g (RectangleBorder z w)) :
    RectangleIntegral f z w = RectangleIntegral g z w := by
  unfold RectangleIntegral VIntegral
  congrm ?_ - ?_ + I • ?_ - I • ?_
  all_goals refine integral_congr fun _ _ ↦ h ?_
  · exact Or.inl <| Or.inl <| Or.inl ⟨by simpa, by simp⟩
  · exact Or.inl <| Or.inr ⟨by simpa, by simp⟩
  · exact Or.inr ⟨by simp, by simpa⟩
  · exact Or.inl <| Or.inl <| Or.inr ⟨by simp, by simpa⟩

theorem RectangleIntegral'_congr (h : Set.EqOn f g (RectangleBorder z w)) :
    RectangleIntegral' f z w = RectangleIntegral' g z w := by
  rw [RectangleIntegral', RectangleIntegral_congr h]

def RectangleBorderIntegrable (f : ℂ → E) (z w : ℂ) : Prop :=
    IntervalIntegrable (fun x => f (x + z.im * I)) volume z.re w.re ∧
    IntervalIntegrable (fun x => f (x + w.im * I)) volume z.re w.re ∧
    IntervalIntegrable (fun y => f (w.re + y * I)) volume z.im w.im ∧
    IntervalIntegrable (fun y => f (z.re + y * I)) volume z.im w.im

theorem RectangleBorderIntegrable.add {f g : ℂ → E}
    (hf : RectangleBorderIntegrable f z w) (hg : RectangleBorderIntegrable g z w) :
    RectangleIntegral (f + g) z w = RectangleIntegral f z w + RectangleIntegral g z w := by
  dsimp [RectangleIntegral, HIntegral, VIntegral]
  have h₁ := intervalIntegral.integral_add hf.1 hg.1
  have h₂ := intervalIntegral.integral_add hf.2.1 hg.2.1
  have h₃ := intervalIntegral.integral_add hf.2.2.1 hg.2.2.1
  have h₄ := intervalIntegral.integral_add hf.2.2.2 hg.2.2.2
  rw [h₁, h₂, h₃, h₄]
  module

theorem ContinuousOn.rectangleBorder_integrable {F : Type*} [NormedAddCommGroup F] {f : ℂ → F} (hf : ContinuousOn f (RectangleBorder z w)) :
    RectangleBorderIntegrable f z w :=
  ⟨(hf.comp (by fun_prop) (mapsTo_rectangleBorder_left_im z w)).intervalIntegrable,
    (hf.comp (by fun_prop) (mapsTo_rectangleBorder_right_im z w)).intervalIntegrable,
    (hf.comp (by fun_prop) (mapsTo_rectangleBorder_right_re z w)).intervalIntegrable,
    (hf.comp (by fun_prop) (mapsTo_rectangleBorder_left_re z w)).intervalIntegrable⟩

theorem ContinuousOn.rectangleBorderIntegrable {F : Type*} [NormedAddCommGroup F] {f : ℂ → F} (hf : ContinuousOn f (Rectangle z w)) :
    RectangleBorderIntegrable f z w :=
  ContinuousOn.rectangleBorder_integrable (hf.mono (rectangleBorder_subset_rectangle z w))

theorem ContinuousOn.rectangleBorderNoPIntegrable {F : Type*} [NormedAddCommGroup F] {f : ℂ → F}
    (hf : ContinuousOn f (Rectangle z w \ {p})) (pNotOnBorder : p ∉ RectangleBorder z w) :
    RectangleBorderIntegrable f z w := by
  refine ContinuousOn.rectangleBorder_integrable (hf.mono (Set.subset_sdiff.mpr ?_))
  exact ⟨rectangleBorder_subset_rectangle z w, disjoint_singleton_right.mpr pNotOnBorder⟩

theorem HolomorphicOn.rectangleBorderIntegrable'
    (hf : HolomorphicOn f (Rectangle z w \ {p})) (hp : Rectangle z w ∈ nhds p) :
    RectangleBorderIntegrable f z w :=
  hf.continuousOn.rectangleBorderNoPIntegrable (not_mem_rectangleBorder_of_rectangle_mem_nhds hp)

theorem HolomorphicOn.rectangleBorderIntegrable (hf : HolomorphicOn f (Rectangle z w)) :
    RectangleBorderIntegrable f z w := hf.continuousOn.rectangleBorderIntegrable

theorem RectangleIntegral.translate (f : ℂ → E) (z w p : ℂ) :
    RectangleIntegral (fun s => f (s - p)) z w = RectangleIntegral f (z - p) (w - p) := by
  simp_rw [RectangleIntegral, HIntegral, VIntegral, sub_re, sub_im,
    ← intervalIntegral.integral_comp_sub_right]
  congr <;> ext <;> congr 1 <;> simp [Complex.ext_iff]

theorem RectangleIntegral.translate' (f : ℂ → E) (z w p : ℂ) :
    RectangleIntegral' (fun s => f (s - p)) z w = RectangleIntegral' f (z - p) (w - p) := by
  simp_rw [RectangleIntegral', RectangleIntegral.translate]

lemma Complex.inv_re_add_im : (x + y * I)⁻¹ = (x - I * y) / (x ^ 2 + y ^ 2) := by
  rw [Complex.inv_def, div_eq_mul_inv]
  congr <;> simp [conj_ofReal, normSq] <;> ring

lemma sq_add_sq_ne_zero (hy : y ≠ 0) : x ^ 2 + y ^ 2 ≠ 0 := by
  linarith [sq_nonneg x, sq_pos_iff.mpr hy]

lemma continuous_self_div_sq_add_sq (hy : y ≠ 0) :
    Continuous fun x => x / (x ^ 2 + y ^ 2) :=
  continuous_id.div (continuous_id.pow 2 |>.add continuous_const) (fun _ => sq_add_sq_ne_zero hy)

lemma integral_self_div_sq_add_sq (hy : y ≠ 0) :
    ∫ x in x₁..x₂, x / (x ^ 2 + y ^ 2) =
    Real.log (x₂ ^ 2 + y ^ 2) / 2 - Real.log (x₁ ^ 2 + y ^ 2) / 2 := by
  let f (x : ℝ) : ℝ := Real.log (x ^ 2 + y ^ 2) / 2
  have e1 {x} := HasDerivAt.add_const (y ^ 2) (by simpa using hasDerivAt_pow 2 x)
  have e2 {x} : HasDerivAt f (x / (x ^ 2 + y ^ 2)) x := by
    convert! (e1.log (sq_add_sq_ne_zero hy)).div_const 2 using 1
    field_simp
  have e3 : deriv f = fun x => x / (x ^ 2 + y ^ 2) := funext (fun _ => e2.deriv)
  have e4 : Continuous (deriv f) := by simpa only [e3] using continuous_self_div_sq_add_sq hy
  simp_rw [← e2.deriv]
  exact integral_deriv_eq_sub (fun _ _ => e2.differentiableAt) (e4.intervalIntegrable _ _)

lemma integral_const_div_sq_add_sq (hy : y ≠ 0) :
    ∫ x in x₁..x₂, y / (x ^ 2 + y ^ 2) = Real.arctan (x₂ / y) - Real.arctan (x₁ / y) := by
  nth_rewrite 1 [← div_mul_cancel₀ x₁ hy, ← div_mul_cancel₀ x₂ hy]
  simp_rw [← mul_integral_comp_mul_right, ← intervalIntegral.integral_const_mul,
    ← integral_one_div_one_add_sq]
  exact integral_congr fun x _ => by
    field_simp
    ring

lemma integral_const_div_self_add_im (hy : y ≠ 0) :
    ∫ x : ℝ in x₁..x₂, A / (x + y * I) =
    A * (Real.log (x₂ ^ 2 + y ^ 2) / 2 - Real.log (x₁ ^ 2 + y ^ 2) / 2) -
    A * I * (Real.arctan (x₂ / y) - Real.arctan (x₁ / y)) := by
  have e1 {x : ℝ} : A / (x + y * I) = A * x / (x ^ 2 + y ^ 2) - A * I * y / (x ^ 2 + y ^ 2) := by
    ring_nf
    simp_rw [inv_re_add_im]
    ring
  have e2 : IntervalIntegrable (fun x ↦ A * x / (x ^ 2 + y ^ 2)) volume x₁ x₂ := by
    apply Continuous.intervalIntegrable
    simp_rw [mul_div_assoc]
    norm_cast
    exact continuous_const.mul (continuous_ofReal.comp (continuous_self_div_sq_add_sq hy))
  have e3 : IntervalIntegrable (fun x ↦ A * I * y / (x ^ 2 + y ^ 2)) volume x₁ x₂ := by
    apply Continuous.intervalIntegrable
    refine continuous_const.div (by fun_prop) (fun x => ?_)
    norm_cast
    exact sq_add_sq_ne_zero hy
  simp_rw [integral_congr (fun _ _ => e1), integral_sub e2 e3, mul_div_assoc]
  norm_cast
  simp_rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal,
    integral_self_div_sq_add_sq hy, integral_const_div_sq_add_sq hy]

lemma integral_const_div_re_add_self (hx : x ≠ 0) :
    ∫ y : ℝ in y₁..y₂, A / (x + y * I) =
    A / I * (Real.log (y₂ ^ 2 + (-x) ^ 2) / 2 - Real.log (y₁ ^ 2 + (-x) ^ 2) / 2) -
    A / I * I * (Real.arctan (y₂ / -x) - Real.arctan (y₁ / -x)) := by
  have l1 {y : ℝ} : A / (x + y * I) = A / I / (y + ↑(-x) * I) := by
    have e1 : x + y * I ≠ 0 := by
      contrapose! hx
      simpa using congr_arg re hx
    have e2 : y + I * ↑(-x) ≠ 0 := by
      contrapose! hx
      simpa using congr_arg im hx
    field_simp [*]
    push_cast
    ring_nf
    simp
  have l2 : -x ≠ 0 := by rwa [neg_ne_zero]
  simp_rw [l1, integral_const_div_self_add_im l2]

lemma ResidueTheoremAtOrigin' {z w c : ℂ}
    (h1 : z.re < 0) (h2 : z.im < 0) (h3 : 0 < w.re) (h4 : 0 < w.im) :
    RectangleIntegral (fun s => c / s) z w = 2 * I * π * c := by
  simp only [RectangleIntegral, HIntegral, VIntegral, smul_eq_mul]
  rw [integral_const_div_re_add_self h1.ne, integral_const_div_re_add_self h3.ne.symm]
  rw [integral_const_div_self_add_im h2.ne, integral_const_div_self_add_im h4.ne.symm]
  have l1 : z.im * w.re⁻¹ = (w.re * z.im⁻¹)⁻¹ := by group
  have l3 := arctan_inv_of_neg <| mul_neg_of_pos_of_neg h3 <| inv_lt_zero.mpr h2
  have l4 : w.im * z.re⁻¹ = (z.re * w.im⁻¹)⁻¹ := by group
  have l6 := arctan_inv_of_neg <| mul_neg_of_neg_of_pos h1 <| inv_pos.mpr h4
  have r1 : z.im * z.re⁻¹ = (z.re * z.im⁻¹)⁻¹ := by group
  have r3 := arctan_inv_of_pos <| mul_pos_of_neg_of_neg h1 <| inv_lt_zero.mpr h2
  have r4 : w.im * w.re⁻¹ = (w.re * w.im⁻¹)⁻¹ := by group
  have r6 := arctan_inv_of_pos <| mul_pos h3 <| inv_pos.mpr h4
  ring_nf
  simp only [one_div, inv_I, mul_neg, neg_mul, I_sq, neg_neg, arctan_neg, ofReal_neg,
    sub_neg_eq_add]
  rw [l1, l3, l4, l6, r1, r3, r4, r6]
  ring_nf
  simp only [I_sq, ofReal_sub, ofReal_mul, ofReal_ofNat, ofReal_div, ofReal_neg, ofReal_one]
  ring_nf

theorem ResidueTheoremInRectangle
    (zRe_le_wRe : z.re ≤ w.re) (zIm_le_wIm : z.im ≤ w.im)
    (pInRectInterior : Rectangle z w ∈ 𝓝 p) :
    RectangleIntegral' (fun s => c / (s - p)) z w = c := by
  simp only [rectangle_mem_nhds_iff, uIoo_of_le zRe_le_wRe, uIoo_of_le zIm_le_wIm,
    mem_reProdIm, mem_Ioo] at pInRectInterior
  rw [RectangleIntegral.translate', RectangleIntegral']
  have : 1 / (2 * ↑π * I) * (2 * I * ↑π * c) = c := by
    field_simp
  rwa [ResidueTheoremAtOrigin']
  all_goals simp [*]

lemma ResidueTheoremOnRectangleWithSimplePole {f g : ℂ → ℂ} {z w p A : ℂ}
    (zRe_le_wRe : z.re ≤ w.re) (zIm_le_wIm : z.im ≤ w.im)
    (pInRectInterior : Rectangle z w ∈ 𝓝 p) (gHolo : HolomorphicOn g (Rectangle z w))
    (principalPart : Set.EqOn (f - fun s ↦ A / (s - p)) g (Rectangle z w \ {p})) :
    RectangleIntegral' f z w = A := by
  have principalPart' : Set.EqOn f (g + (fun s ↦ A / (s - p))) (Rectangle z w \ {p}) :=
    fun s hs => by rw [Pi.add_apply, ← principalPart hs, Pi.sub_apply, sub_add_cancel]
  have : Set.EqOn f (g + (fun s ↦ A / (s - p))) (RectangleBorder z w) :=
    principalPart'.mono <| Set.subset_sdiff.mpr
      ⟨rectangleBorder_subset_rectangle z w,
        disjoint_singleton_right.mpr
          (not_mem_rectangleBorder_of_rectangle_mem_nhds pInRectInterior)⟩
  rw [RectangleIntegral'_congr this]
  have t1 : RectangleBorderIntegrable g z w :=
    gHolo.rectangleBorderIntegrable
  have t2 : HolomorphicOn (fun s ↦ A / (s - p)) (Rectangle z w \ {p}) := by
    apply DifferentiableOn.mono (t := {p}ᶜ)
    · apply DifferentiableOn.div
      · exact differentiableOn_const _
      · exact DifferentiableOn.sub differentiableOn_id (differentiableOn_const _)
      · exact fun x hx => by
          rw [sub_ne_zero]
          exact hx
    · rintro s ⟨_, hs⟩
      exact hs
  have t3 : RectangleBorderIntegrable (fun s ↦ A / (s - p)) z w :=
    HolomorphicOn.rectangleBorderIntegrable' t2 pInRectInterior
  rw [RectangleIntegral', RectangleBorderIntegrable.add t1 t3, smul_add]
  rw [gHolo.vanishesOnRectangle (by rfl), smul_zero, zero_add]
  exact ResidueTheoremInRectangle zRe_le_wRe zIm_le_wIm pInRectInterior

end

section

open Filter Set Complex Real

open scoped Topology in
private theorem riemannZetaLogDerivResidueBigO :
    (-(deriv riemannZeta) / riemannZeta - fun z ↦ (z - 1)⁻¹) =O[nhdsWithin 1 {1}ᶜ] (1 : ℂ → ℂ) := by
  have H := log_deriv_riemannZeta_add_inv_sub_bounded.neg_left
  apply H.congr_left
  intro z
  change -(deriv riemannZeta z / riemannZeta z + (z-1)⁻¹) = -deriv riemannZeta z / riemannZeta z - (z-1)⁻¹
  ring

lemma ShiftZeroBound :
    ∃ (C : ℝ), C ≥ 1 ∧
      ∀ (δ : ℝ), δ ∈ Ioo 0 1 →
        -((deriv riemannZeta) (1 + δ) / riemannZeta (1 + δ)).re ≤ 1 / δ + C := by
  have zetaAnalyticOnNhd : AnalyticOnNhd ℂ riemannZeta {(1 : ℂ)}ᶜ := DifferentiableOn.analyticOnNhd
    (fun _ hs => (differentiableAt_riemannZeta hs).differentiableWithinAt) isOpen_compl_singleton
  have oneAddContinuous : Continuous (fun x : ℝ => (1 + (x : ℂ))) :=
    Continuous.add continuous_const continuous_ofReal
  have ShiftZeroBoundNear :
      ∃ (C r : ℝ), r ∈ Ioo 0 1 ∧
        ∀ (δ : ℝ), δ ∈ Ioo 0 r →
          -((deriv riemannZeta) (1 + δ) / riemannZeta (1 + δ)).re ≤ 1 / δ + C := by
    obtain ⟨C, hC⟩ := riemannZetaLogDerivResidueBigO.bound
    rcases Metric.mem_nhdsWithin_iff.mp hC with ⟨ε, εpos, hε⟩
    refine ⟨C, min ε (1 / 2), ⟨?_, fun δ δrange => ?_⟩⟩
    · constructor
      · positivity
      · exact lt_of_le_of_lt (min_le_right ε (1 / 2)) (by norm_num)
    · have δin : ((1 : ℂ) + δ) ∈ Metric.ball 1 ε ∩ {1}ᶜ := by
        simp only [mem_inter_iff, Metric.mem_ball, dist_self_add_left, norm_real, norm_eq_abs,
          mem_compl_iff, mem_singleton_iff, add_eq_left, ofReal_eq_zero, abs_lt]
        exact ⟨⟨by linarith [δrange.1], by linarith [δrange.2, min_le_left ε (1 / 2)]⟩,
          by linarith [δrange.1]⟩
      have reBound := (Complex.re_le_norm _).trans (hε δin)
      simp only [Pi.sub_apply, Pi.div_apply, Pi.neg_apply, add_sub_cancel_left, sub_re, inv_re,
        ofReal_re, normSq_ofReal, div_self_mul_self', Pi.one_apply, norm_one, mul_one,
        tsub_le_iff_right] at reBound
      simp only [one_div, ← Complex.neg_re, ← neg_div, add_comm _ C, reBound]
  obtain ⟨C₀, r, rIn, boundNear⟩ := ShiftZeroBoundNear
  have ShiftZeroBoundCompact :
      ∃ (C : ℝ), ∀ (δ : ℝ), δ ∈ Icc r 1 →
        -((deriv riemannZeta) (1 + δ) / riemannZeta (1 + δ)).re ≤ 1 / δ + C := by
    simp only [← sub_le_iff_le_add', ← Complex.neg_re]
    refine ⟨_, fun δ hδ => le_csSup (IsCompact.bddAbove (isCompact_Icc.image_of_continuousOn ?_))
      (Set.mem_image_of_mem _ hδ)⟩
    refine ContinuousOn.add (Complex.continuous_re.comp_continuousOn
      (ContinuousOn.neg (ContinuousOn.div (ContinuousOn.comp zetaAnalyticOnNhd.deriv.continuousOn
        (by apply fun x hx => oneAddContinuous.continuousOn) ?_)
      (ContinuousOn.comp zetaAnalyticOnNhd.continuousOn
        (by apply fun x hx => oneAddContinuous.continuousOn) ?_)
      (fun x hx => riemannZeta_ne_zero_of_one_lt_re ?_)))) (ContinuousOn.neg
        (ContinuousOn.div continuousOn_const continuousOn_id ?_))
    · simp only [MapsTo, mem_Icc, mem_compl_iff, mem_singleton_iff, add_eq_left,
        ofReal_eq_zero, and_imp]
      exact fun x hx _ => by linarith [rIn.1, hx]
    · simp only [MapsTo, mem_Icc, mem_compl_iff, mem_singleton_iff, add_eq_left,
        ofReal_eq_zero, and_imp]
      exact fun x hx _ => by linarith [rIn.1, hx]
    · simp only [add_re, one_re, ofReal_re, lt_add_iff_pos_right]
      linarith [rIn.1, hx.1]
    · simp only [ne_eq]
      exact fun x hx => by linarith [rIn.1, hx.1]
  obtain ⟨C₁, boundCompact⟩ := ShiftZeroBoundCompact
  refine ⟨1 + max |C₀| |C₁|, ?_, fun δ δrange => ?_⟩
  · simp only [ge_iff_le, le_add_iff_nonneg_right, le_sup_iff, abs_nonneg, or_self]
  · by_cases δ_lt_r : δ < r
    · have δIn : δ ∈ Ioo 0 r := by simp only [mem_Ioo, δrange.1, δ_lt_r, and_self]
      apply le_trans (boundNear δ δIn)
      simp only [one_div, add_le_add_iff_left]
      linarith [le_abs_self C₀, le_max_left |C₀| |C₁|]
    · have δIn : δ ∈ Icc r 1 := by
        simp only [mem_Icc, δrange.2.le, ← not_lt, δ_lt_r, not_false_eq_true, and_self]
      apply le_trans (boundCompact δ δIn)
      simp only [one_div, add_le_add_iff_left]
      linarith [le_abs_self C₁, le_max_right |C₀| |C₁|]

end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

def explicitFormulaIntegrand {N : Nat} [NeZero N]
    (chi : DirichletCharacter Complex N) (x : Nat) (s : Complex) : Complex :=
  logDeriv chi.LFunction s * (-((x : Complex) ^ s / s))

def perronStepWeight (y : Real) : Real :=
  if y < 1 then 0 else if y = 1 then 1 / 2 else 1

def perronKernelIntegrand (y : Real) (s : Complex) : Complex :=
  (y : Complex) ^ s / s

def truncatedPerronKernel (y c T : Real) : Complex :=
  VIntegral' (perronKernelIntegrand y) c (-T) T

@[simp] theorem perronStepWeight_one : perronStepWeight 1 = 1 / 2 := by
  simp [perronStepWeight]

theorem perronKernelIntegrand_eq_exp {y : Real} (hy : 0 < y) (s : Complex) :
    perronKernelIntegrand y s =
      Complex.exp ((Real.log y : Complex) * s) / s := by
  rw [perronKernelIntegrand,
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hy.ne')]
  rw [Complex.ofReal_log hy.le]

theorem holomorphicOn_perronKernelIntegrand {y : Real} (hy : 0 < y) :
    HolomorphicOn (perronKernelIntegrand y) {s : Complex | 0 < s.re} := by
  intro s hs
  have hsne : Ne s 0 := by
    intro hzero
    subst s
    simp at hs
  have hEq :
      perronKernelIntegrand y =
        fun z : Complex => Complex.exp ((Real.log y : Complex) * z) / z := by
    funext z
    exact perronKernelIntegrand_eq_exp hy z
  rw [hEq]
  fun_prop

theorem norm_perronKernelIntegrand {y : Real} (hy : 0 < y) (s : Complex) :
    norm (perronKernelIntegrand y s) = y ^ s.re / norm s := by
  rw [perronKernelIntegrand, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hy]

def twistedMangoldtSequence {N : Nat}
    (chi : DirichletCharacter Complex N) (n : Nat) : Complex :=
  chi n * (ArithmeticFunction.vonMangoldt n : Complex)

def explicitFormulaDirichletTerm {N : Nat}
    (chi : DirichletCharacter Complex N) (x n : Nat) (s : Complex) : Complex :=
  LSeries.term (twistedMangoldtSequence chi) s n *
    ((x : Complex) ^ s / s)

def explicitFormulaVerticalIntegral {N : Nat} [NeZero N]
    (chi : DirichletCharacter Complex N) (x : Nat) (c T : Real) : Complex :=
  VIntegral' (explicitFormulaIntegrand chi x) c (-T) T

def scalarPerronSeriesTerm {N : Nat}
    (chi : DirichletCharacter Complex N) (x : Nat) (c T : Real) (n : Nat) : Complex :=
  if n = 0 then 0 else
    twistedMangoldtSequence chi n *
      truncatedPerronKernel ((x : Real) / (n : Real)) c T

theorem explicitFormulaDirichletTerm_eq_coeff_mul_perronKernel
    {N : Nat} (chi : DirichletCharacter Complex N) (x n : Nat)
    (s : Complex) (hn : Ne n 0) :
    explicitFormulaDirichletTerm chi x n s =
      twistedMangoldtSequence chi n *
        perronKernelIntegrand ((x : Real) / (n : Real)) s := by
  rw [explicitFormulaDirichletTerm, LSeries.term_def, if_neg hn,
    perronKernelIntegrand]
  rw [Complex.ofReal_div]
  rw [Complex.div_cpow_ofReal_nonneg (Nat.cast_nonneg x)
    (Nat.cast_nonneg n)]
  simp only [Complex.ofReal_natCast]
  ring

theorem VIntegral_explicitFormulaDirichletTerm_eq_scalarPerronSeriesTerm
    {N : Nat} (chi : DirichletCharacter Complex N) (x n : Nat)
    (c T : Real) :
    VIntegral' (explicitFormulaDirichletTerm chi x n) c (-T) T =
      scalarPerronSeriesTerm chi x c T n := by
  by_cases hn : n = 0
  case pos =>
    subst n
    simp [scalarPerronSeriesTerm, explicitFormulaDirichletTerm,
      LSeries.term_def, VIntegral', VIntegral]
  case neg =>
    have hFunctions : (fun t : Real =>
        explicitFormulaDirichletTerm chi x n (c + t * Complex.I)) =
        fun t : Real => twistedMangoldtSequence chi n *
          perronKernelIntegrand ((x : Real) / (n : Real))
            (c + t * Complex.I) := by
      funext t
      exact explicitFormulaDirichletTerm_eq_coeff_mul_perronKernel chi x n
        (c + t * Complex.I) hn
    rw [scalarPerronSeriesTerm, if_neg hn]
    simp only [VIntegral', VIntegral, truncatedPerronKernel]
    rw [hFunctions, intervalIntegral.integral_const_mul]
    simp only [smul_eq_mul]
    ring

theorem neg_logDeriv_LFunction_eq_LSeries
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N) {s : Complex}
    (hs : 1 < s.re) :
    -logDeriv chi.LFunction s = LSeries (twistedMangoldtSequence chi) s := by
  have hSeries := DirichletCharacter.LSeries_twist_vonMangoldt_eq chi hs
  rw [logDeriv_apply,
    DirichletCharacter.deriv_LFunction_eq_deriv_LSeries chi hs,
    DirichletCharacter.LFunction_eq_LSeries chi hs]
  have hSequence : twistedMangoldtSequence chi =
      (fun n : Nat => chi n) *
        (fun n : Nat => (ArithmeticFunction.vonMangoldt n : Complex)) := by
    funext n
    rfl
  rw [hSequence, <- neg_div]
  exact hSeries.symm

theorem explicitFormulaIntegrand_eq_tsum
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    {x : Nat} (s : Complex) (hs : 1 < s.re) :
    explicitFormulaIntegrand chi x s =
      tsum (fun n : Nat => explicitFormulaDirichletTerm chi x n s) := by
  rw [explicitFormulaIntegrand]
  rw [show logDeriv chi.LFunction s * (-((x : Complex) ^ s / s)) =
      (-logDeriv chi.LFunction s) * ((x : Complex) ^ s / s) by ring]
  rw [neg_logDeriv_LFunction_eq_LSeries chi hs]
  rw [LSeries]
  simp only [explicitFormulaDirichletTerm]
  rw [<- tsum_mul_right]

def perronSeriesFunction {N : Nat}
    (chi : DirichletCharacter Complex N) (x n : Nat) (c : Real) (t : Real) : Complex :=
  explicitFormulaDirichletTerm chi x n (c + t * Complex.I)

theorem perronSeriesFunction_continuous
    {N : Nat} (chi : DirichletCharacter Complex N) {x : Nat} (hx : 0 < x)
    (n : Nat) {c : Real} (hc : 1 < c) :
    Continuous (perronSeriesFunction chi x n c) := by
  by_cases hn : n = 0
  case pos =>
    subst n
    change Continuous (fun t : Real =>
      explicitFormulaDirichletTerm chi x 0 (c + t * Complex.I))
    simpa [explicitFormulaDirichletTerm, LSeries.term_def] using
      (continuous_const : Continuous (fun _ : Real => (0 : Complex)))
  case neg =>
    have hnC : Ne (n : Complex) 0 := by exact_mod_cast hn
    have hxC : Ne (x : Complex) 0 := by exact_mod_cast (Nat.ne_of_gt hx)
    have hsNe : forall t : Real, Ne ((c : Complex) + t * Complex.I) 0 := by
      intro t h
      have hre := congrArg Complex.re h
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im,
        mul_one, sub_self, add_zero, Complex.zero_re] at hre
      linarith
    have hpath : Continuous (fun t : Real =>
        (c : Complex) + t * Complex.I) := by
      fun_prop
    have hnPow : Continuous (fun t : Real =>
        (n : Complex) ^ ((c : Complex) + t * Complex.I)) :=
      hpath.const_cpow (Or.inl hnC)
    have hxPow : Continuous (fun t : Real =>
        (x : Complex) ^ ((c : Complex) + t * Complex.I)) :=
      hpath.const_cpow (Or.inl hxC)
    change Continuous (fun t : Real =>
      explicitFormulaDirichletTerm chi x n (c + t * Complex.I))
    simp only [explicitFormulaDirichletTerm, LSeries.term_def, hn, if_false]
    exact (continuous_const.div hnPow (fun _ =>
        Complex.cpow_ne_zero_iff.mpr (Or.inl hnC))).mul
      (hxPow.div hpath hsNe)

def perronSeriesContinuousMap
    {N : Nat} (chi : DirichletCharacter Complex N) {x : Nat} (hx : 0 < x)
    (n : Nat) {c : Real} (hc : 1 < c) : C(Real, Complex) :=
  ContinuousMap.mk (perronSeriesFunction chi x n c)
    (perronSeriesFunction_continuous chi hx n hc)

end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

open Set

namespace BombieriVinogradov.SiegelWalfisz

theorem norm_perronSeriesFunction_le
    {N : Nat} (chi : DirichletCharacter Complex N) {x : Nat} (hx : 0 < x)
    (n : Nat) {c : Real} (hc : 1 < c) (t : Real) :
    norm (perronSeriesFunction chi x n c t) <=
      ((x : Real) ^ c / c) *
        norm (LSeries.term (twistedMangoldtSequence chi) (c : Complex) n) := by
  by_cases hn : n = 0
  case pos =>
    subst n
    simp [perronSeriesFunction, explicitFormulaDirichletTerm,
      LSeries.term_def]
  case neg =>
    have hcPos : 0 < c := lt_trans zero_lt_one hc
    have hcNe : Ne c 0 := ne_of_gt hcPos
    have hReNe : Ne (((c : Complex) + t * Complex.I).re) 0 := by
      simpa using hcNe
    have hNormLower : c <= norm ((c : Complex) + t * Complex.I) := by
      calc
        c = abs (((c : Complex) + t * Complex.I).re) := by
          simp [abs_of_pos hcPos]
        _ <= norm ((c : Complex) + t * Complex.I) :=
          Complex.abs_re_le_norm _
    simp only [perronSeriesFunction, explicitFormulaDirichletTerm,
      LSeries.term_def, hn, if_false, norm_mul, norm_div]
    rw [Complex.norm_natCast_cpow_of_re_ne_zero n hReNe,
      Complex.norm_natCast_cpow_of_re_ne_zero x hReNe,
      Complex.norm_natCast_cpow_of_re_ne_zero n (by simpa using hcNe)]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im,
      mul_one, sub_self, add_zero]
    have hNormPos : 0 < norm ((c : Complex) + t * Complex.I) :=
      lt_of_lt_of_le hcPos hNormLower
    have hxPowNonneg : 0 <= (x : Real) ^ c :=
      Real.rpow_nonneg (Nat.cast_nonneg x) c
    have hCoeffNonneg :
        0 <= norm (twistedMangoldtSequence chi n) / (n : Real) ^ c :=
      div_nonneg (norm_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg n) c)
    calc
      norm (twistedMangoldtSequence chi n) / (n : Real) ^ c *
          ((x : Real) ^ c / norm ((c : Complex) + t * Complex.I)) <=
          norm (twistedMangoldtSequence chi n) / (n : Real) ^ c *
            ((x : Real) ^ c / c) := by
        gcongr
      _ = (x : Real) ^ c / c *
          (norm (twistedMangoldtSequence chi n) / (n : Real) ^ c) := by
        ring

theorem norm_restrict_perronSeriesContinuousMap_le
    {N : Nat} (chi : DirichletCharacter Complex N) {x : Nat} (hx : 0 < x)
    (n : Nat) {c T : Real} (hc : 1 < c) :
    norm ((perronSeriesContinuousMap chi hx n hc).restrict
      (TopologicalSpace.Compacts.mk (uIcc (-T) T) isCompact_uIcc)) <=
      ((x : Real) ^ c / c) *
        norm (LSeries.term (twistedMangoldtSequence chi) (c : Complex) n) := by
  have hcPos : 0 < c := lt_trans zero_lt_one hc
  have hMajorantNonneg : 0 <=
      ((x : Real) ^ c / c) *
        norm (LSeries.term (twistedMangoldtSequence chi) (c : Complex) n) :=
    mul_nonneg
      (div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg x) c) (le_of_lt hcPos))
      (norm_nonneg _)
  apply (ContinuousMap.norm_le _ hMajorantNonneg).mpr
  intro t
  simpa [perronSeriesContinuousMap] using
    norm_perronSeriesFunction_le chi hx n hc t.1

theorem summable_norm_restrict_perronSeriesContinuousMap
    {N : Nat} (chi : DirichletCharacter Complex N) {x : Nat} (hx : 0 < x)
    {c T : Real} (hc : 1 < c) :
    Summable (fun n : Nat =>
      norm ((perronSeriesContinuousMap chi hx n hc).restrict
        (TopologicalSpace.Compacts.mk (uIcc (-T) T) isCompact_uIcc))) := by
  have hSequence : twistedMangoldtSequence chi =
      (fun n : Nat => chi n) *
        (fun n : Nat => (ArithmeticFunction.vonMangoldt n : Complex)) := by
    funext n
    rfl
  have hLSeries : LSeriesSummable (twistedMangoldtSequence chi) (c : Complex) := by
    rw [hSequence]
    exact DirichletCharacter.LSeriesSummable_twist_vonMangoldt chi (by simpa using hc)
  have hMajorant : Summable (fun n : Nat =>
      ((x : Real) ^ c / c) *
        norm (LSeries.term (twistedMangoldtSequence chi) (c : Complex) n)) :=
    hLSeries.norm.mul_left ((x : Real) ^ c / c)
  apply Summable.of_nonneg_of_le
    (fun _ => norm_nonneg _)
    (fun n => norm_restrict_perronSeriesContinuousMap_le chi hx n hc)
    hMajorant

theorem tsum_intervalIntegral_perronSeriesFunction
    {N : Nat} (chi : DirichletCharacter Complex N) {x : Nat} (hx : 0 < x)
    {c T : Real} (hc : 1 < c) :
    tsum (fun n : Nat => intervalIntegral
      (perronSeriesFunction chi x n c) (-T) T MeasureTheory.volume) =
      intervalIntegral (fun t : Real =>
        tsum (fun n : Nat => perronSeriesFunction chi x n c t))
        (-T) T MeasureTheory.volume := by
  exact intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm
    (summable_norm_restrict_perronSeriesContinuousMap chi hx hc)

theorem explicitFormulaVerticalIntegral_eq_tsum_VIntegral
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    {x : Nat} (hx : 0 < x) {c T : Real} (hc : 1 < c) :
    explicitFormulaVerticalIntegral chi x c T =
      tsum (fun n : Nat =>
        VIntegral' (explicitFormulaDirichletTerm chi x n) c (-T) T) := by
  have hFunctions : (fun t : Real =>
      explicitFormulaIntegrand chi x (c + t * Complex.I)) =
      fun t : Real => tsum (fun n : Nat =>
        perronSeriesFunction chi x n c t) := by
    funext t
    apply explicitFormulaIntegrand_eq_tsum
    simpa using hc
  have hInterchange := tsum_intervalIntegral_perronSeriesFunction
    (T := T) chi hx hc
  simp only [explicitFormulaVerticalIntegral, VIntegral', VIntegral]
  rw [hFunctions]
  rw [<- hInterchange]
  rw [<- tsum_const_smul'' Complex.I]
  rw [<- tsum_const_smul'' (1 / (2 * Real.pi * Complex.I))]
  rfl

theorem explicitFormulaVerticalIntegral_eq_tsum_scalarPerronSeriesTerm
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    {x : Nat} (hx : 0 < x) {c T : Real} (hc : 1 < c) :
    explicitFormulaVerticalIntegral chi x c T =
      tsum (scalarPerronSeriesTerm chi x c T) := by
  calc
    explicitFormulaVerticalIntegral chi x c T =
        tsum (fun n : Nat =>
          VIntegral' (explicitFormulaDirichletTerm chi x n) c (-T) T) :=
      explicitFormulaVerticalIntegral_eq_tsum_VIntegral chi hx hc
    _ = tsum (scalarPerronSeriesTerm chi x c T) := by
      apply tsum_congr
      intro n
      exact VIntegral_explicitFormulaDirichletTerm_eq_scalarPerronSeriesTerm
        chi x n c T

end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

open Finset
open scoped BigOperators

namespace BombieriVinogradov.SiegelWalfisz

def scalarPerronStepTerm {N : Nat}
    (chi : DirichletCharacter Complex N) (x n : Nat) : Complex :=
  if n = 0 then 0 else
    twistedMangoldtSequence chi n *
      (perronStepWeight ((x : Real) / (n : Real)) : Complex)

def characterChebyshevHalfSum {N : Nat}
    (x : Nat) (chi : DirichletCharacter Complex N) : Complex :=
  (Finset.sum (Finset.Ico 1 x) (twistedMangoldtSequence chi)) +
    (1 / 2 : Complex) * twistedMangoldtSequence chi x

def scalarPerronErrorTerm {N : Nat}
    (chi : DirichletCharacter Complex N) (x : Nat) (c T : Real) (n : Nat) : Complex :=
  scalarPerronSeriesTerm chi x c T n - scalarPerronStepTerm chi x n

def scalarPerronErrorMajorantTerm {N : Nat}
    (chi : DirichletCharacter Complex N) (x : Nat) (c T : Real) (n : Nat) : Real :=
  if n = 0 then 0 else
    norm (twistedMangoldtSequence chi n) *
      if (x : Real) / (n : Real) = 1 then c / (Real.pi * T)
      else ((x : Real) / (n : Real)) ^ c *
        min 1 (1 / (Real.pi * T *
          abs (Real.log ((x : Real) / (n : Real)))))

def sourcePerronErrorMajorantTerm (x : Nat) (c T : Real) (n : Nat) : Real :=
  if n = 0 then 0 else
    ArithmeticFunction.vonMangoldt n *
      if (x : Real) / (n : Real) = 1 then c / (Real.pi * T)
      else ((x : Real) / (n : Real)) ^ c *
        min 1 (1 / (Real.pi * T *
          abs (Real.log ((x : Real) / (n : Real)))))

theorem norm_twistedMangoldtSequence_le_vonMangoldt
    {N : Nat} (chi : DirichletCharacter Complex N) (n : Nat) :
    norm (twistedMangoldtSequence chi n) <= ArithmeticFunction.vonMangoldt n := by
  unfold twistedMangoldtSequence
  rw [norm_mul, Complex.norm_real,
    Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  exact mul_le_of_le_one_left ArithmeticFunction.vonMangoldt_nonneg
    (chi.norm_le_one n)

theorem scalarPerronErrorMajorantTerm_le_source
    {N : Nat} (chi : DirichletCharacter Complex N) {x : Nat} (hx : 0 < x)
    {c T : Real} (hc : 0 < c) (hT : 0 < T) (n : Nat) :
    scalarPerronErrorMajorantTerm chi x c T n <=
      sourcePerronErrorMajorantTerm x c T n := by
  by_cases hn : n = 0
  case pos =>
    simp [scalarPerronErrorMajorantTerm, sourcePerronErrorMajorantTerm, hn]
  case neg =>
    have hnPos : 0 < n := Nat.pos_of_ne_zero hn
    have hRatioPos : 0 < (x : Real) / (n : Real) :=
      div_pos (by exact_mod_cast hx) (by exact_mod_cast hnPos)
    by_cases hRatio : (x : Real) / (n : Real) = 1
    case pos =>
      simp only [scalarPerronErrorMajorantTerm,
        sourcePerronErrorMajorantTerm, hn, hRatio, if_false, if_true]
      apply mul_le_mul_of_nonneg_right
        (norm_twistedMangoldtSequence_le_vonMangoldt chi n)
      positivity
    case neg =>
      simp only [scalarPerronErrorMajorantTerm,
        sourcePerronErrorMajorantTerm, hn, hRatio, if_false]
      apply mul_le_mul_of_nonneg_right
        (norm_twistedMangoldtSequence_le_vonMangoldt chi n)
      have hReciprocal : 0 <= 1 / (Real.pi * T *
          abs (Real.log ((x : Real) / (n : Real)))) := by
        positivity
      exact mul_nonneg (Real.rpow_nonneg hRatioPos.le c)
        (le_min zero_le_one hReciprocal)

def optimizedPerronLine (x : Nat) : Real :=
  1 + 1 / Real.log (x : Real)

theorem one_le_log_natCast {x : Nat} (hx : 2 < x) :
    (1 : Real) <= Real.log (x : Real) := by
  have hLogThree := Real.le_log_one_add_of_nonneg
    (x := (2 : Real)) (by norm_num)
  norm_num at hLogThree
  have hxThree : (3 : Real) <= (x : Real) := by exact_mod_cast hx
  exact hLogThree.trans (Real.log_le_log (by norm_num) hxThree)

theorem optimizedPerronLine_gt_one {x : Nat} (hx : 2 < x) :
    1 < optimizedPerronLine x := by
  have hLogPos : 0 < Real.log (x : Real) :=
    lt_of_lt_of_le zero_lt_one (one_le_log_natCast hx)
  have hInvPos : 0 < 1 / Real.log (x : Real) := by positivity
  unfold optimizedPerronLine
  linarith

theorem optimizedPerronLine_le_two {x : Nat} (hx : 2 < x) :
    optimizedPerronLine x <= 2 := by
  have hLog := one_le_log_natCast hx
  have hInv : 1 / Real.log (x : Real) <= 1 := by
    have h := one_div_le_one_div_of_le zero_lt_one hLog
    norm_num at h
    simpa only [one_div] using h
  unfold optimizedPerronLine
  linarith

theorem rpow_optimizedPerronLine_eq {x : Nat} (hx : 2 < x) :
    (x : Real) ^ optimizedPerronLine x =
      (x : Real) * Real.exp 1 := by
  have hxPos : 0 < x := lt_trans zero_lt_two hx
  have hxReal : 0 < (x : Real) := by exact_mod_cast hxPos
  have hxNeOne : Ne (x : Real) 1 := by
    have hxThree : (3 : Real) <= (x : Real) := by exact_mod_cast hx
    linarith
  unfold optimizedPerronLine
  rw [Real.rpow_add hxReal, Real.rpow_one, one_div]
  rw [Real.rpow_inv_log hxReal hxNeOne]

def vonMangoldtLSeriesNormSum (c : Real) : Real :=
  tsum (fun n : Nat =>
    norm (LSeries.term
      (fun m : Nat => (ArithmeticFunction.vonMangoldt m : Complex))
      (c : Complex) n))

theorem LSeriesTerm_vonMangoldt_eq_ofReal
    {c : Real} (n : Nat) :
    LSeries.term
        (fun m : Nat => (ArithmeticFunction.vonMangoldt m : Complex))
        (c : Complex) n =
      ((ArithmeticFunction.vonMangoldt n / (n : Real) ^ c : Real) : Complex) := by
  by_cases hn : n = 0
  case pos =>
    subst n
    simp [LSeries.term_def]
  case neg =>
    rw [LSeries.term_def, if_neg hn]
    rw [Complex.ofReal_div]
    rw [Complex.ofReal_cpow (Nat.cast_nonneg n) c]
    norm_cast

theorem re_LSeriesTerm_vonMangoldt_eq_norm
    {c : Real} (n : Nat) :
    (LSeries.term
      (fun m : Nat => (ArithmeticFunction.vonMangoldt m : Complex))
      (c : Complex) n).re =
    norm (LSeries.term
      (fun m : Nat => (ArithmeticFunction.vonMangoldt m : Complex))
      (c : Complex) n) := by
  rw [LSeriesTerm_vonMangoldt_eq_ofReal]
  rw [Complex.ofReal_re, Complex.norm_real]
  apply Eq.symm
  rw [Real.norm_of_nonneg]
  exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg
    (Real.rpow_nonneg (Nat.cast_nonneg n) c)

theorem norm_LSeriesTerm_vonMangoldt_eq
    {c : Real} (n : Nat) :
    norm (LSeries.term
      (fun m : Nat => (ArithmeticFunction.vonMangoldt m : Complex))
      (c : Complex) n) =
      ArithmeticFunction.vonMangoldt n / (n : Real) ^ c := by
  rw [LSeriesTerm_vonMangoldt_eq_ofReal, Complex.norm_real,
    Real.norm_of_nonneg]
  exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg
    (Real.rpow_nonneg (Nat.cast_nonneg n) c)

theorem vonMangoldtLSeriesNormSum_eq_neg_logDeriv_re
    {c : Real} (hc : 1 < c) :
    vonMangoldtLSeriesNormSum c =
      (-deriv riemannZeta (c : Complex) / riemannZeta (c : Complex)).re := by
  have hSummable := ArithmeticFunction.LSeriesSummable_vonMangoldt
    (s := (c : Complex)) (by simpa using hc)
  have hSeries := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div
    (s := (c : Complex)) (by simpa using hc)
  rw [LSeries] at hSeries
  have hReal := congrArg Complex.re hSeries
  rw [Complex.re_tsum hSummable] at hReal
  have hTerms : (fun n : Nat =>
      (LSeries.term
        (fun m : Nat => (ArithmeticFunction.vonMangoldt m : Complex))
        (c : Complex) n).re) = fun n : Nat =>
      norm (LSeries.term
        (fun m : Nat => (ArithmeticFunction.vonMangoldt m : Complex))
        (c : Complex) n) := by
    funext n
    exact re_LSeriesTerm_vonMangoldt_eq_norm n
  rw [hTerms] at hReal
  exact hReal

theorem scalarPerronErrorMajorantTerm_le_summable
    {N : Nat} (chi : DirichletCharacter Complex N) {x : Nat} (hx : 0 < x)
    {c T : Real} (hc : 0 < c) (n : Nat) :
    scalarPerronErrorMajorantTerm chi x c T n <=
      (x : Real) ^ c *
          norm (LSeries.term (twistedMangoldtSequence chi) (c : Complex) n) +
        if n = x then
          norm (twistedMangoldtSequence chi n) * (c / (Real.pi * T))
        else 0 := by
  by_cases hn : n = 0
  case pos =>
    subst n
    simp [scalarPerronErrorMajorantTerm, LSeries.term_def,
      (Nat.ne_of_gt hx).symm]
  case neg =>
    have hnRealNe : Ne (n : Real) 0 := by exact_mod_cast hn
    by_cases hRatio : (x : Real) / (n : Real) = 1
    case pos =>
      have hxnReal : (x : Real) = (n : Real) :=
        (div_eq_one_iff_eq hnRealNe).mp hRatio
      have hxn : x = n := by exact_mod_cast hxnReal
      rw [scalarPerronErrorMajorantTerm, if_neg hn, if_pos hRatio,
        if_pos hxn.symm]
      exact le_add_of_nonneg_left (mul_nonneg
        (Real.rpow_nonneg (Nat.cast_nonneg x) c) (norm_nonneg _))
    case neg =>
      have hnx : Ne n x := by
        intro h
        subst n
        apply hRatio
        exact div_self (by exact_mod_cast (Nat.ne_of_gt hx))
      rw [scalarPerronErrorMajorantTerm, if_neg hn, if_neg hRatio,
        if_neg hnx]
      calc
        norm (twistedMangoldtSequence chi n) *
            (((x : Real) / (n : Real)) ^ c *
              min 1 (1 / (Real.pi * T *
                abs (Real.log ((x : Real) / (n : Real)))))) <=
            norm (twistedMangoldtSequence chi n) *
              (((x : Real) / (n : Real)) ^ c * 1) := by
          gcongr
          exact min_le_left _ _
        _ = (x : Real) ^ c *
            norm (LSeries.term (twistedMangoldtSequence chi)
              (c : Complex) n) := by
          rw [LSeries.term_def, if_neg hn, norm_div,
            Complex.norm_natCast_cpow_of_re_ne_zero n (by simpa using ne_of_gt hc),
            Real.div_rpow (Nat.cast_nonneg x) (Nat.cast_nonneg n) c]
          simp only [Complex.ofReal_re, mul_one]
          ring
        _ = (x : Real) ^ c *
              norm (LSeries.term (twistedMangoldtSequence chi)
                (c : Complex) n) + 0 := by
          ring

theorem scalarPerronErrorMajorantTerm_nonneg
    {N : Nat} (chi : DirichletCharacter Complex N) {x : Nat} (hx : 0 < x)
    {c T : Real} (hc : 0 < c) (hT : 0 < T) (n : Nat) :
    0 <= scalarPerronErrorMajorantTerm chi x c T n := by
  by_cases hn : n = 0
  case pos =>
    simp [scalarPerronErrorMajorantTerm, hn]
  case neg =>
    have hnPos : 0 < n := Nat.pos_of_ne_zero hn
    have hRatioPos : 0 < (x : Real) / (n : Real) :=
      div_pos (by exact_mod_cast hx) (by exact_mod_cast hnPos)
    by_cases hRatio : (x : Real) / (n : Real) = 1
    case pos =>
      rw [scalarPerronErrorMajorantTerm, if_neg hn, if_pos hRatio]
      positivity
    case neg =>
      rw [scalarPerronErrorMajorantTerm, if_neg hn, if_neg hRatio]
      have hReciprocal : 0 <= 1 / (Real.pi * T *
          abs (Real.log ((x : Real) / (n : Real)))) := by
        positivity
      exact mul_nonneg (norm_nonneg _)
        (mul_nonneg (Real.rpow_nonneg hRatioPos.le c)
          (le_min zero_le_one hReciprocal))

theorem summable_scalarPerronErrorMajorantTerm
    {N : Nat} (chi : DirichletCharacter Complex N) {x : Nat} (hx : 0 < x)
    {c T : Real} (hc : 1 < c) (hT : 0 < T) :
    Summable (scalarPerronErrorMajorantTerm chi x c T) := by
  have hSequence : twistedMangoldtSequence chi =
      (fun n : Nat => chi n) *
        (fun n : Nat => (ArithmeticFunction.vonMangoldt n : Complex)) := by
    funext n
    rfl
  have hLSeries : LSeriesSummable (twistedMangoldtSequence chi) (c : Complex) := by
    rw [hSequence]
    exact DirichletCharacter.LSeriesSummable_twist_vonMangoldt chi (by simpa using hc)
  have hBase : Summable (fun n : Nat =>
      (x : Real) ^ c *
        norm (LSeries.term (twistedMangoldtSequence chi) (c : Complex) n)) :=
    hLSeries.norm.mul_left ((x : Real) ^ c)
  have hEndpoint : Summable (fun n : Nat =>
      if n = x then
        norm (twistedMangoldtSequence chi n) * (c / (Real.pi * T))
      else 0) := by
    have hFunction : (fun n : Nat =>
        if n = x then
          norm (twistedMangoldtSequence chi n) * (c / (Real.pi * T))
        else 0) = fun n : Nat =>
          if n = x then
            norm (twistedMangoldtSequence chi x) * (c / (Real.pi * T))
          else 0 := by
      funext n
      by_cases hnx : n = x
      case pos =>
        subst n
        rfl
      case neg =>
        simp [hnx]
    rw [hFunction]
    exact (hasSum_ite_eq x
      (norm (twistedMangoldtSequence chi x) * (c / (Real.pi * T)))).summable
  apply Summable.of_nonneg_of_le
    (fun n => scalarPerronErrorMajorantTerm_nonneg chi hx
      (lt_trans zero_lt_one hc) hT n)
    (fun n => scalarPerronErrorMajorantTerm_le_summable chi hx
      (lt_trans zero_lt_one hc) n)
    (hBase.add hEndpoint)

theorem norm_twistedMangoldtSequence_one_eq (n : Nat) :
    norm (twistedMangoldtSequence (1 : DirichletCharacter Complex 1) n) =
      ArithmeticFunction.vonMangoldt n := by
  unfold twistedMangoldtSequence
  rw [norm_mul, Complex.norm_real,
    Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  have hOneFunction :
      ((fun m : Nat => (1 : DirichletCharacter Complex 1) m) : Nat -> Complex) = 1 :=
    DirichletCharacter.modOne_eq_one
  have hOneValue : (1 : DirichletCharacter Complex 1) n = 1 := by
    simpa using congrFun hOneFunction n
  rw [hOneValue, norm_one, one_mul]

theorem summable_sourcePerronErrorMajorantTerm
    {x : Nat} (hx : 0 < x) {c T : Real} (hc : 1 < c) (hT : 0 < T) :
    Summable (sourcePerronErrorMajorantTerm x c T) := by
  have hFunction : sourcePerronErrorMajorantTerm x c T =
      scalarPerronErrorMajorantTerm
        (1 : DirichletCharacter Complex 1) x c T := by
    funext n
    unfold sourcePerronErrorMajorantTerm
    unfold scalarPerronErrorMajorantTerm
    rw [norm_twistedMangoldtSequence_one_eq]
  rw [hFunction]
  exact summable_scalarPerronErrorMajorantTerm
    (1 : DirichletCharacter Complex 1) hx hc hT

theorem perronStepWeight_natRatio_eq_one_of_lt
    {x n : Nat} (hn : 0 < n) (hnx : n < x) :
    perronStepWeight ((x : Real) / (n : Real)) = 1 := by
  have hnReal : 0 < (n : Real) := by exact_mod_cast hn
  have hnxReal : (n : Real) < (x : Real) := by exact_mod_cast hnx
  have hRatio : 1 < (x : Real) / (n : Real) := by
    rw [one_lt_div hnReal]
    exact hnxReal
  simp [perronStepWeight, not_lt_of_ge hRatio.le, ne_of_gt hRatio]

theorem perronStepWeight_natRatio_eq_half
    {x : Nat} (hx : 0 < x) :
    perronStepWeight ((x : Real) / (x : Real)) = 1 / 2 := by
  have hxNe : Ne (x : Real) 0 := by exact_mod_cast (Nat.ne_of_gt hx)
  simp [hxNe, perronStepWeight]

theorem perronStepWeight_natRatio_eq_zero_of_lt
    {x n : Nat} (hn : 0 < n) (hxn : x < n) :
    perronStepWeight ((x : Real) / (n : Real)) = 0 := by
  have hnReal : 0 < (n : Real) := by exact_mod_cast hn
  have hxnReal : (x : Real) < (n : Real) := by exact_mod_cast hxn
  have hRatio : (x : Real) / (n : Real) < 1 := by
    rw [div_lt_one hnReal]
    exact hxnReal
  simp [perronStepWeight, hRatio]

theorem scalarPerronStepTerm_eq_coeff_of_lt
    {N x n : Nat} (chi : DirichletCharacter Complex N)
    (hn : 0 < n) (hnx : n < x) :
    scalarPerronStepTerm chi x n = twistedMangoldtSequence chi n := by
  simp [scalarPerronStepTerm, Nat.ne_of_gt hn,
    perronStepWeight_natRatio_eq_one_of_lt hn hnx]

theorem scalarPerronStepTerm_eq_half
    {N x : Nat} (chi : DirichletCharacter Complex N) (hx : 0 < x) :
    scalarPerronStepTerm chi x x =
      (1 / 2 : Complex) * twistedMangoldtSequence chi x := by
  rw [scalarPerronStepTerm, if_neg (Nat.ne_of_gt hx),
    perronStepWeight_natRatio_eq_half hx]
  simpa using mul_comm (twistedMangoldtSequence chi x) (1 / 2 : Complex)

theorem scalarPerronStepTerm_eq_zero_of_lt
    {N x n : Nat} (chi : DirichletCharacter Complex N)
    (hn : 0 < n) (hxn : x < n) :
    scalarPerronStepTerm chi x n = 0 := by
  simp [scalarPerronStepTerm, Nat.ne_of_gt hn,
    perronStepWeight_natRatio_eq_zero_of_lt hn hxn]

end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

open Finset
open scoped BigOperators

namespace BombieriVinogradov.SiegelWalfisz

theorem summable_scalarPerronStepTerm
    {N x : Nat} (chi : DirichletCharacter Complex N) :
    Summable (scalarPerronStepTerm chi x) := by
  apply summable_of_ne_finset_zero (s := Finset.Icc 1 x)
  intro n hnMem
  by_cases hnZero : n = 0
  case pos =>
    simp [scalarPerronStepTerm, hnZero]
  case neg =>
    have hnPos : 0 < n := Nat.pos_of_ne_zero hnZero
    have hOne : 1 <= n := hnPos
    have hNotLe : Not (n <= x) := by
      intro hnx
      exact hnMem (by simp [hOne, hnx])
    exact scalarPerronStepTerm_eq_zero_of_lt chi hnPos
      (Nat.lt_of_not_ge hNotLe)

theorem tsum_scalarPerronStepTerm_eq_characterChebyshevHalfSum
    {N x : Nat} (chi : DirichletCharacter Complex N) (hx : 0 < x) :
    tsum (scalarPerronStepTerm chi x) = characterChebyshevHalfSum x chi := by
  have hTail : forall n : Nat, Not (Membership.mem (Finset.Icc 1 x) n) ->
      scalarPerronStepTerm chi x n = 0 := by
    intro n hnMem
    by_cases hnZero : n = 0
    case pos =>
      simp [scalarPerronStepTerm, hnZero]
    case neg =>
      have hnPos : 0 < n := Nat.pos_of_ne_zero hnZero
      have hOne : 1 <= n := hnPos
      have hNotLe : Not (n <= x) := by
        intro hnx
        exact hnMem (by simp [hOne, hnx])
      exact scalarPerronStepTerm_eq_zero_of_lt chi hnPos
        (Nat.lt_of_not_ge hNotLe)
  rw [tsum_eq_sum hTail]
  have hInterior :
      Finset.sum (Finset.Ico 1 x) (scalarPerronStepTerm chi x) =
        Finset.sum (Finset.Ico 1 x) (twistedMangoldtSequence chi) := by
    apply Finset.sum_congr rfl
    intro n hnMem
    have hnBounds := Finset.mem_Ico.mp hnMem
    exact scalarPerronStepTerm_eq_coeff_of_lt chi
      (lt_of_lt_of_le zero_lt_one hnBounds.1) hnBounds.2
  have hxMem : Membership.mem (Finset.Icc 1 x) x :=
    Finset.mem_Icc.mpr (And.intro hx (le_refl x))
  have hDecomp := Finset.sum_erase_add (Finset.Icc 1 x)
    (scalarPerronStepTerm chi x) hxMem
  rw [Finset.Icc_erase_right] at hDecomp
  rw [<- hDecomp]
  rw [scalarPerronStepTerm_eq_half chi hx]
  unfold characterChebyshevHalfSum
  rw [hInterior]

end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

open MeasureTheory Set

namespace BombieriVinogradov.SiegelWalfisz

theorem integrableOn_rpow_Iic
    {y : Real} (hy1 : 1 < y) (c : Real) :
    IntegrableOn (fun x : Real => y ^ x) (Iic c) := by
  have hy : 0 < y := lt_trans Real.zero_lt_one hy1
  simpa [Real.rpow_def_of_pos hy] using
    integrableOn_exp_mul_Iic (Real.log_pos hy1) c

theorem integral_rpow_Iic
    {y : Real} (hy1 : 1 < y) (c : Real) :
    integral (volume.restrict (Iic c)) (fun x : Real => y ^ x) =
      y ^ c / abs (Real.log y) := by
  have hy : 0 < y := lt_trans Real.zero_lt_one hy1
  rw [show (fun x : Real => y ^ x) =
      fun x : Real => Real.exp (Real.log y * x) by
    funext x
    exact Real.rpow_def_of_pos hy x]
  rw [integral_exp_mul_Iic (Real.log_pos hy1)]
  rw [(Real.rpow_def_of_pos hy c).symm]
  rw [abs_of_pos (Real.log_pos hy1)]

end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

open Filter MeasureTheory Set Topology

namespace BombieriVinogradov.SiegelWalfisz

theorem norm_perron_left_horizontal_le
    {y t x : Real} (hy : 0 < y) (ht : 0 < abs t) :
    norm (perronKernelIntegrand y
      ((x : Complex) + (t : Complex) * Complex.I)) <= y ^ x / abs t := by
  rw [norm_perronKernelIntegrand hy]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero]
  have hLower : abs t <=
      norm ((x : Complex) + (t : Complex) * Complex.I) := by
    simpa using Complex.abs_im_le_norm
      ((x : Complex) + (t : Complex) * Complex.I)
  exact div_le_div_of_nonneg_left (Real.rpow_nonneg hy.le x) ht hLower

theorem integrableOn_perron_horizontal_Iic
    {y c t : Real} (hy1 : 1 < y) (ht : 0 < abs t) :
    IntegrableOn
      (fun x : Real => perronKernelIntegrand y
        ((x : Complex) + (t : Complex) * Complex.I))
      (Iic c) := by
  have hy : 0 < y := lt_trans Real.zero_lt_one hy1
  have hDom : IntegrableOn (fun x : Real => y ^ x / abs t) (Iic c) :=
    (integrableOn_rpow_Iic hy1 c).div_const (abs t)
  apply hDom.mono'
  next =>
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_Iic
    intro x _
    have hEq :
        (fun u : Real => perronKernelIntegrand y
          ((u : Complex) + (t : Complex) * Complex.I)) =
          fun u : Real =>
            Complex.exp
                ((Real.log y : Complex) *
                  ((u : Complex) + (t : Complex) * Complex.I)) /
              ((u : Complex) + (t : Complex) * Complex.I) := by
      funext u
      exact perronKernelIntegrand_eq_exp hy _
    rw [hEq]
    fun_prop (disch :=
      intro hzero
      have hImag := congrArg Complex.im hzero
      simp at hImag
      exact (ne_of_gt ht) (abs_eq_zero.mpr hImag))
  next =>
    filter_upwards [ae_restrict_mem measurableSet_Iic] with x _
    exact norm_perron_left_horizontal_le hy ht

def leftHorizontalIntegral (y c t : Real) : Complex :=
  integral (volume.restrict (Iic c))
    (fun x : Real => perronKernelIntegrand y
      ((x : Complex) + (t : Complex) * Complex.I))

theorem tendsto_hIntegral'_left_atTop
    {y c t : Real} (hy1 : 1 < y) (ht : 0 < abs t) :
    Tendsto
      (fun R : Real => HIntegral' (perronKernelIntegrand y) (-R) c t)
      atTop
      (nhds
        ((1 / (2 * Real.pi * Complex.I) : Complex) *
          leftHorizontalIntegral y c t)) := by
  have hLimit := intervalIntegral_tendsto_integral_Iic
    (f := fun x : Real => perronKernelIntegrand y
      ((x : Complex) + (t : Complex) * Complex.I)) c
    (integrableOn_perron_horizontal_Iic hy1 ht)
    tendsto_neg_atTop_atBot
  simpa [HIntegral', HIntegral, leftHorizontalIntegral, smul_eq_mul] using
    hLimit.const_smul (1 / (2 * Real.pi * Complex.I) : Complex)

end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

open Filter MeasureTheory Set

namespace BombieriVinogradov.SiegelWalfisz

theorem norm_integral_perron_horizontal_Iic_lt
    {y c t : Real} (hy1 : 1 < y) (hc : 0 < c) (ht : 0 < abs t) :
    norm
        (integral (volume.restrict (Iic c))
          (fun x : Real => perronKernelIntegrand y
            ((x : Complex) + (t : Complex) * Complex.I))) <
      y ^ c / (abs t * abs (Real.log y)) := by
  have hy : 0 < y := lt_trans Real.zero_lt_one hy1
  let mu := volume.restrict (Iic c)
  let f : Real -> Real := fun x =>
    norm (perronKernelIntegrand y
      ((x : Complex) + (t : Complex) * Complex.I))
  let g : Real -> Real := fun x => y ^ x / abs t
  have hf : Integrable f mu := by
    dsimp [f, mu]
    exact (integrableOn_perron_horizontal_Iic hy1 ht).norm
  have hg : Integrable g mu := by
    dsimp [g, mu]
    exact (integrableOn_rpow_Iic hy1 c).div_const (abs t)
  have hfg : Filter.Eventually (fun x => f x <= g x) (ae mu) :=
    Eventually.of_forall fun x => by
      exact norm_perron_left_horizontal_le hy ht
  have hdInt : Integrable (g - f) mu := hg.sub hf
  have hdNonneg : Filter.Eventually (fun x => 0 <= (g - f) x) (ae mu) :=
    hfg.mono fun x hx => by
      simpa only [Pi.sub_apply, sub_nonneg] using hx
  have hSmallSubset : Set.Ioc (-2 : Real) (-1) <= Set.Iic c := by
    intro x hx
    change x <= c
    linarith [hx.2]
  have hSmallSupport :
      Set.Ioc (-2 : Real) (-1) <= Function.support (g - f) := by
    intro x hx
    change Ne ((g - f) x) 0
    apply ne_of_gt
    rw [Pi.sub_apply, sub_pos]
    dsimp [f, g]
    rw [norm_perronKernelIntegrand hy]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one,
      sub_self, add_zero]
    have hx0 : Ne x 0 := by linarith [hx.2]
    have hDenom : abs t <
        norm ((x : Complex) + (t : Complex) * Complex.I) := by
      have hStrict := (Complex.abs_im_lt_norm).2 (by
        simpa using hx0 :
          Ne (((x : Complex) + (t : Complex) * Complex.I).re) 0)
      simpa using hStrict
    exact div_lt_div_of_pos_left (Real.rpow_pos_of_pos hy x) ht hDenom
  have hSmallMeasure : 0 < mu (Set.Ioc (-2 : Real) (-1)) := by
    dsimp [mu]
    rw [Measure.restrict_apply measurableSet_Ioc]
    rw [Set.inter_eq_left.mpr hSmallSubset]
    norm_num [Real.volume_Ioc]
  have hSupportMeasure : 0 < mu (Function.support (g - f)) :=
    hSmallMeasure.trans_le (measure_mono hSmallSupport)
  have hdPos : 0 < integral mu (g - f) :=
    (integral_pos_iff_support_of_nonneg_ae hdNonneg hdInt).2 hSupportMeasure
  change 0 < integral mu (fun x => g x - f x) at hdPos
  rw [integral_sub hg hf] at hdPos
  have hStrictIntegral : integral mu f < integral mu g := by linarith
  calc
    norm
        (integral (volume.restrict (Iic c))
          (fun x : Real => perronKernelIntegrand y
            ((x : Complex) + (t : Complex) * Complex.I))) <=
        integral mu f := by
      dsimp [mu, f]
      exact norm_integral_le_integral_norm _
    _ < integral mu g := hStrictIntegral
    _ = (1 / abs t) *
        integral (volume.restrict (Iic c)) (fun x : Real => y ^ x) := by
      dsimp [mu, g]
      rw [show (fun x : Real => y ^ x / abs t) =
          fun x : Real => (1 / abs t) * y ^ x by
        funext x
        ring]
      rw [integral_const_mul]
    _ = y ^ c / (abs t * abs (Real.log y)) := by
      rw [integral_rpow_Iic hy1]
      ring

def perronKernelRemainder (y : Real) (s : Complex) : Complex :=
  dslope (fun z : Complex =>
    Complex.exp ((Real.log y : Complex) * z)) 0 s

theorem differentiableAt_perronKernelRemainder
    (y : Real) (s : Complex) :
    DifferentiableAt Complex (perronKernelRemainder y) s := by
  let h : Complex -> Complex := fun z =>
    Complex.exp ((Real.log y : Complex) * z)
  by_cases hs : s = 0
  next =>
    subst s
    have hh : AnalyticAt Complex h 0 := by
      dsimp [h]
      fun_prop
    choose p hp using hh
    exact hp.has_fpower_series_dslope_fslope.differentiableAt
  next =>
    change DifferentiableAt Complex (dslope h 0) s
    exact (differentiableAt_dslope_of_ne hs).2 (by
      dsimp [h]
      fun_prop)

theorem perronKernelIntegrand_sub_pole_eq_remainder
    {y : Real} (hy : 0 < y) :
    Set.EqOn
      (perronKernelIntegrand y - fun s : Complex => 1 / (s - 0))
      (perronKernelRemainder y) (Set.compl ({0} : Set Complex)) := by
  intro s hs
  have hs0 : Ne s 0 := by
    intro h
    apply hs
    simp [h]
  rw [Pi.sub_apply, perronKernelIntegrand_eq_exp hy]
  rw [perronKernelRemainder, dslope_of_ne _ hs0]
  simp only [slope, sub_zero, Complex.exp_zero, mul_zero, one_div]
  simp only [vsub_eq_sub, smul_eq_mul]
  ring

theorem rectangleIntegral'_perron_eq_one
    {y : Real} (hy : 0 < y) {z w : Complex}
    (hRe : z.re <= w.re) (hIm : z.im <= w.im)
    (hZero : Membership.mem (nhds (0 : Complex)) (Complex.Rectangle z w)) :
    RectangleIntegral' (perronKernelIntegrand y) z w = 1 := by
  apply ResidueTheoremOnRectangleWithSimplePole hRe hIm hZero
    (g := perronKernelRemainder y)
  next =>
    intro s _
    exact (differentiableAt_perronKernelRemainder y s).differentiableWithinAt
  next =>
    exact (perronKernelIntegrand_sub_pole_eq_remainder hy).mono
      (Set.sdiff_subset_compl _ _)

theorem truncatedPerronKernel_sub_one_eq_left_rectangle_terms
    {y c T R : Real} (hy : 0 < y) (hc : 0 < c) (hT : 0 < T)
    (hR : 0 < R) :
    truncatedPerronKernel y c T - 1 =
      -HIntegral' (perronKernelIntegrand y) (-R) c (-T) +
        HIntegral' (perronKernelIntegrand y) (-R) c T +
          VIntegral' (perronKernelIntegrand y) (-R) (-T) T := by
  let z : Complex := ((-R : Real) : Complex) -
    Complex.I * (T : Complex)
  let w : Complex := (c : Complex) + Complex.I * (T : Complex)
  have hIm : z.im <= w.im := by
    dsimp [z, w]
    simp
    linarith
  have hRe : z.re <= w.re := by
    dsimp [z, w]
    simp
    linarith
  have hZero : Membership.mem (nhds (0 : Complex)) (Complex.Rectangle z w) := by
    rw [rectangle_mem_nhds_iff]
    simp only [Complex.mem_reProdIm, z, w, Complex.sub_re, Complex.ofReal_re,
      Complex.mul_re, Complex.I_re, zero_mul, Complex.I_im,
      Complex.ofReal_im, mul_zero, sub_self, sub_zero, Complex.add_re,
      add_zero, Complex.sub_im, Complex.mul_im, one_mul, zero_add,
      zero_sub, Complex.add_im, Complex.zero_re, Complex.zero_im]
    rw [Set.uIoo_of_lt (by linarith), Set.uIoo_of_lt (by linarith)]
    exact And.intro (And.intro (by linarith) hc)
      (And.intro (by linarith) hT)
  have hResidue := rectangleIntegral'_perron_eq_one hy hRe hIm hZero
  simp only [z, w, RectangleIntegral', RectangleIntegral, smul_eq_mul,
    Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    zero_mul, Complex.I_im, Complex.ofReal_im, mul_zero, sub_self,
    sub_zero, Complex.add_re, add_zero, Complex.sub_im, Complex.mul_im,
    one_mul, zero_add, zero_sub, Complex.add_im] at hResidue
  simp only [truncatedPerronKernel, HIntegral', VIntegral', smul_eq_mul]
  linear_combination hResidue

end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

open Filter Topology

namespace BombieriVinogradov.SiegelWalfisz

private lemma norm_perron_left_vertical_integrand_le_bv420
    {y R t : Real} (hy : 0 < y) (hR : 0 < R) :
    norm (perronKernelIntegrand y
      (((-R : Real) : Complex) + (t : Complex) * Complex.I)) <=
      y ^ (-R) / R := by
  rw [norm_perronKernelIntegrand hy]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero]
  have hLower : R <=
      norm (((-R : Real) : Complex) + (t : Complex) * Complex.I) := by
    have hAbs := Complex.abs_re_le_norm
      (((-R : Real) : Complex) + (t : Complex) * Complex.I)
    simpa [abs_of_pos hR] using hAbs
  exact div_le_div_of_nonneg_left (Real.rpow_nonneg hy.le (-R)) hR hLower

theorem norm_vIntegral'_perron_left_le
    {y R T : Real} (hy : 0 < y) (hR : 0 < R) (hT : 0 <= T) :
    norm (VIntegral' (perronKernelIntegrand y) (-R) (-T) T) <=
      (T / Real.pi) * (y ^ (-R) / R) := by
  rw [VIntegral', norm_smul]
  have hRaw :
      norm (VIntegral (perronKernelIntegrand y) (-R) (-T) T) <=
        2 * T * (y ^ (-R) / R) := by
    rw [VIntegral, norm_smul]
    simp only [Complex.norm_I, one_mul]
    have hIntegral := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := -T) (b := T)
      (f := fun t : Real => perronKernelIntegrand y
        (((-R : Real) : Complex) + (t : Complex) * Complex.I))
      (C := y ^ (-R) / R)
      (fun t _ => norm_perron_left_vertical_integrand_le_bv420 hy hR)
    calc
      norm
          (intervalIntegral
            (fun t : Real => perronKernelIntegrand y
              (((-R : Real) : Complex) + (t : Complex) * Complex.I))
            (-T) T MeasureTheory.volume) <=
          (y ^ (-R) / R) * abs (T - -T) := hIntegral
      _ = 2 * T * (y ^ (-R) / R) := by
        rw [abs_of_nonneg (by linarith)]
        ring
  calc
    norm (1 / (2 * (Real.pi : Complex) * Complex.I)) *
        norm (VIntegral (perronKernelIntegrand y) (-R) (-T) T) <=
        norm (1 / (2 * (Real.pi : Complex) * Complex.I)) *
          (2 * T * (y ^ (-R) / R)) := by
      gcongr
    _ = (T / Real.pi) * (y ^ (-R) / R) := by
      rw [norm_div, norm_one, norm_mul, norm_mul]
      simp [Complex.norm_I, abs_of_pos Real.pi_pos]
      field_simp [ne_of_gt Real.pi_pos]

theorem tendsto_vIntegral'_perron_left_atTop
    {y T : Real} (hy1 : 1 < y) (hT : 0 <= T) :
    Tendsto (fun R : Real =>
      VIntegral' (perronKernelIntegrand y) (-R) (-T) T) atTop (nhds 0) := by
  have hy : 0 < y := lt_trans Real.zero_lt_one hy1
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hY : Tendsto (fun R : Real => y ^ (-R)) atTop (nhds 0) :=
    (tendsto_rpow_atBot_of_base_gt_one y hy1).comp tendsto_neg_atTop_atBot
  have hInv : Tendsto (fun R : Real => Inv.inv R) atTop (nhds 0) :=
    tendsto_inv_atTop_zero
  have hMajorant :
      Tendsto (fun R : Real => (T / Real.pi) * (y ^ (-R) / R))
        atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using (hY.mul hInv).const_mul (T / Real.pi)
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ hMajorant
  filter_upwards [eventually_gt_atTop (0 : Real)] with R hR
  exact norm_vIntegral'_perron_left_le hy hR hT

end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

open Filter Topology

namespace BombieriVinogradov.SiegelWalfisz

theorem truncatedPerronKernel_sub_one_eq_leftHorizontalIntegrals
    {y c T : Real} (hy1 : 1 < y) (hc : 0 < c) (hT : 0 < T) :
    truncatedPerronKernel y c T - 1 =
      -(1 / (2 * Real.pi * Complex.I) : Complex) *
          leftHorizontalIntegral y c (-T) +
        (1 / (2 * Real.pi * Complex.I) : Complex) *
          leftHorizontalIntegral y c T := by
  have hy : 0 < y := lt_trans Real.zero_lt_one hy1
  have hMinusAbs : 0 < abs (-T) :=
    abs_pos.mpr (neg_ne_zero.mpr hT.ne')
  have hPlusAbs : 0 < abs T := abs_pos.mpr hT.ne'
  have hBottom := tendsto_hIntegral'_left_atTop
    (c := c) hy1 hMinusAbs
  have hTop := tendsto_hIntegral'_left_atTop
    (c := c) hy1 hPlusAbs
  have hLeft := tendsto_vIntegral'_perron_left_atTop hy1 hT.le
  have hCombined := (hBottom.neg.add hTop).add hLeft
  have hFinite : Filter.Eventually
      (fun R : Real => truncatedPerronKernel y c T - 1 =
        -HIntegral' (perronKernelIntegrand y) (-R) c (-T) +
          HIntegral' (perronKernelIntegrand y) (-R) c T +
            VIntegral' (perronKernelIntegrand y) (-R) (-T) T) atTop := by
    filter_upwards [eventually_gt_atTop (0 : Real)] with R hR
    exact truncatedPerronKernel_sub_one_eq_left_rectangle_terms hy hc hT hR
  have hConst : Tendsto
      (fun _ : Real => truncatedPerronKernel y c T - 1) atTop
      (nhds
        (-(1 / (2 * Real.pi * Complex.I) : Complex) *
            leftHorizontalIntegral y c (-T) +
          (1 / (2 * Real.pi * Complex.I) : Complex) *
            leftHorizontalIntegral y c T)) := by
    have hCombined' : Tendsto
        (fun R : Real =>
          -HIntegral' (perronKernelIntegrand y) (-R) c (-T) +
            HIntegral' (perronKernelIntegrand y) (-R) c T +
              VIntegral' (perronKernelIntegrand y) (-R) (-T) T)
        atTop
        (nhds
          (-(1 / (2 * Real.pi * Complex.I) : Complex) *
              leftHorizontalIntegral y c (-T) +
            (1 / (2 * Real.pi * Complex.I) : Complex) *
              leftHorizontalIntegral y c T)) := by
      simpa using hCombined
    apply hCombined'.congr'
    filter_upwards [hFinite] with R hR
    exact hR.symm
  exact tendsto_nhds_unique tendsto_const_nhds hConst

theorem norm_truncatedPerronKernel_sub_one_lt_log_bound
    {y c T : Real} (hy1 : 1 < y) (hc : 0 < c) (hT : 0 < T) :
    norm (truncatedPerronKernel y c T - 1) <
      y ^ c / (Real.pi * T * abs (Real.log y)) := by
  let a : Complex := 1 / (2 * Real.pi * Complex.I)
  let B : Real := y ^ c / (T * abs (Real.log y))
  have hMinusAbs : 0 < abs (-T) :=
    abs_pos.mpr (neg_ne_zero.mpr hT.ne')
  have hPlusAbs : 0 < abs T := abs_pos.mpr hT.ne'
  have hMinus : norm (leftHorizontalIntegral y c (-T)) < B := by
    simpa [B, leftHorizontalIntegral, abs_of_pos hT] using
      (norm_integral_perron_horizontal_Iic_lt hy1 hc hMinusAbs)
  have hPlus : norm (leftHorizontalIntegral y c T) < B := by
    simpa [B, leftHorizontalIntegral, abs_of_pos hT] using
      (norm_integral_perron_horizontal_Iic_lt hy1 hc hPlusAbs)
  have hCoeff : norm a = 1 / (2 * Real.pi) := by
    dsimp [a]
    rw [norm_div, norm_one, norm_mul, norm_mul]
    simp [Complex.norm_I, abs_of_pos Real.pi_pos]
  have hCoeffPos : 0 < norm a := by
    rw [hCoeff]
    positivity
  rw [truncatedPerronKernel_sub_one_eq_leftHorizontalIntegrals hy1 hc hT]
  change norm
      (-a * leftHorizontalIntegral y c (-T) +
        a * leftHorizontalIntegral y c T) < _
  calc
    norm
        (-a * leftHorizontalIntegral y c (-T) +
          a * leftHorizontalIntegral y c T) <=
        norm (-a * leftHorizontalIntegral y c (-T)) +
          norm (a * leftHorizontalIntegral y c T) := norm_add_le _ _
    _ = norm a * norm (leftHorizontalIntegral y c (-T)) +
          norm a * norm (leftHorizontalIntegral y c T) := by
      rw [norm_mul, norm_mul, norm_neg]
    _ < norm a * B + norm a * B := by
      exact add_lt_add (mul_lt_mul_of_pos_left hMinus hCoeffPos)
        (mul_lt_mul_of_pos_left hPlus hCoeffPos)
    _ = y ^ c / (Real.pi * T * abs (Real.log y)) := by
      rw [hCoeff]
      dsimp [B]
      field_simp [ne_of_gt Real.pi_pos]
      ring

theorem circleIntegral_perronKernelIntegrand_eq
    {y R : Real} (hy : 0 < y) (hR : 0 < R) :
    circleIntegral (perronKernelIntegrand y) 0 R =
      2 * Real.pi * Complex.I := by
  let h : Complex -> Complex := fun z =>
    Complex.exp ((Real.log y : Complex) * z)
  have hd : DifferentiableOn Complex h (Metric.closedBall 0 R) := by
    intro z _
    dsimp [h]
    fun_prop
  have hw : Metric.ball (0 : Complex) R 0 := Metric.mem_ball_self hR
  have hC := hd.circleIntegral_sub_inv_smul hw
  have hEq : perronKernelIntegrand y =
      fun z : Complex => Inv.inv (z - 0) * h z := by
    funext z
    rw [perronKernelIntegrand_eq_exp hy]
    dsimp [h]
    simp [div_eq_mul_inv, mul_comm]
  rw [hEq]
  simpa [smul_eq_mul, h] using hC

def perronRightArcRadius (c T : Real) : Real := Real.sqrt (c ^ 2 + T ^ 2)

def perronRightArcAngle (c T : Real) : Real := Real.arctan (T / c)

def perronRightArc (c T theta : Real) : Complex :=
  circleMap 0 (perronRightArcRadius c T) theta

private lemma sqrt_one_add_div_sq_bv424
    {c T : Real} (hc : 0 < c) :
    Real.sqrt (1 + (T / c) ^ 2) = perronRightArcRadius c T / c := by
  rw [show 1 + (T / c) ^ 2 = (c ^ 2 + T ^ 2) / c ^ 2 by
    field_simp]
  rw [Real.sqrt_div (by positivity)]
  rw [Real.sqrt_sq_eq_abs, abs_of_pos hc]
  rfl

theorem perronRightArc_angle
    {c T : Real} (hc : 0 < c) :
    perronRightArc c T (perronRightArcAngle c T) =
      (c : Complex) + (T : Complex) * Complex.I := by
  have hRoot := sqrt_one_add_div_sq_bv424 (T := T) hc
  apply Complex.ext
  next =>
    simp only [perronRightArc, circleMap_zero_re, perronRightArcAngle,
      Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero]
    rw [Real.cos_arctan, hRoot]
    field_simp [ne_of_gt (show 0 < perronRightArcRadius c T by
      dsimp [perronRightArcRadius]
      positivity)]
  next =>
    simp only [perronRightArc, circleMap_zero_im, perronRightArcAngle,
      Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im,
      mul_one, Complex.ofReal_re, Complex.I_re, mul_zero, add_zero]
    rw [Real.sin_arctan, hRoot]
    field_simp [ne_of_gt (show 0 < perronRightArcRadius c T by
      dsimp [perronRightArcRadius]
      positivity)]
    ring

theorem perronRightArc_neg_angle
    {c T : Real} (hc : 0 < c) :
    perronRightArc c T (-perronRightArcAngle c T) =
      (c : Complex) - (T : Complex) * Complex.I := by
  have hPlus := perronRightArc_angle (T := T) hc
  apply Complex.ext
  next =>
    simp only [perronRightArc, circleMap_zero_re, Complex.sub_re,
      Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_self]
    rw [Real.cos_neg]
    simpa [perronRightArc, circleMap_zero_re] using congrArg Complex.re hPlus
  next =>
    simp only [perronRightArc, circleMap_zero_im, Complex.sub_im,
      Complex.ofReal_im, Complex.mul_im, Complex.I_im, mul_one,
      Complex.ofReal_re, Complex.I_re, mul_zero, zero_sub]
    rw [Real.sin_neg]
    have hIm : perronRightArcRadius c T *
        Real.sin (perronRightArcAngle c T) = T := by
      simpa [perronRightArc, circleMap_zero_im] using congrArg Complex.im hPlus
    nlinarith

theorem perronRightArc_re_ge
    {c T theta : Real} (hc : 0 < c) (hT : 0 < T)
    (htheta : Set.uIcc (-perronRightArcAngle c T)
      (perronRightArcAngle c T) theta) :
    c <= (perronRightArc c T theta).re := by
  have hAnglePos : 0 < perronRightArcAngle c T := by
    rw [perronRightArcAngle]
    exact Real.arctan_pos.mpr (div_pos hT hc)
  have hThetaBounds :
      And (-perronRightArcAngle c T <= theta)
        (theta <= perronRightArcAngle c T) := by
    rw [Set.uIcc_of_le (by linarith :
      -perronRightArcAngle c T <= perronRightArcAngle c T)] at htheta
    change And (-perronRightArcAngle c T <= theta)
      (theta <= perronRightArcAngle c T) at htheta
    exact htheta
  have hAbs : abs theta <= perronRightArcAngle c T :=
    abs_le.mpr hThetaBounds
  have hAnglePi : perronRightArcAngle c T <= Real.pi :=
    (Real.arctan_lt_pi_div_two _).le.trans (by linarith [Real.pi_pos])
  have hCos :
      Real.cos (perronRightArcAngle c T) <= Real.cos theta := by
    have hCosAbs := Real.cos_le_cos_of_nonneg_of_le_pi
      (abs_nonneg theta) hAnglePi hAbs
    simpa using hCosAbs
  have hRadius : 0 <= perronRightArcRadius c T := by
    dsimp [perronRightArcRadius]
    positivity
  have hEndpointRe :
      perronRightArcRadius c T * Real.cos (perronRightArcAngle c T) = c := by
    simpa [perronRightArc, circleMap_zero_re] using
      congrArg Complex.re (perronRightArc_angle (T := T) hc)
  have hMul := mul_le_mul_of_nonneg_left hCos hRadius
  simpa [perronRightArc, circleMap_zero_re, hEndpointRe] using hMul

def perronLeftArc (c T theta : Real) : Complex :=
  circleMap 0 (perronRightArcRadius c T) theta

theorem perronLeftArc_re_le
    {c T theta : Real} (hc : 0 < c) (hT : 0 < T)
    (htheta : Set.uIcc (perronRightArcAngle c T)
      (2 * Real.pi - perronRightArcAngle c T) theta) :
    (perronLeftArc c T theta).re <= c := by
  have hAnglePos : 0 < perronRightArcAngle c T := by
    rw [perronRightArcAngle]
    exact Real.arctan_pos.mpr (div_pos hT hc)
  have hAngleLt : perronRightArcAngle c T < Real.pi / 2 :=
    Real.arctan_lt_pi_div_two _
  have hOrdered : perronRightArcAngle c T <=
      2 * Real.pi - perronRightArcAngle c T := by
    linarith [Real.pi_pos]
  have hBounds :
      And (perronRightArcAngle c T <= theta)
        (theta <= 2 * Real.pi - perronRightArcAngle c T) := by
    rw [Set.uIcc_of_le hOrdered] at htheta
    exact htheta
  have hCos : Real.cos theta <= Real.cos (perronRightArcAngle c T) := by
    rcases le_total theta Real.pi with hThetaPi | hPiTheta
    next =>
      exact Real.cos_le_cos_of_nonneg_of_le_pi hAnglePos.le hThetaPi hBounds.1
    next =>
      have hPhiNonneg : 0 <= 2 * Real.pi - theta := by
        linarith [hBounds.2, hAnglePos]
      have hPhiPi : 2 * Real.pi - theta <= Real.pi := by linarith
      have hAnglePhi : perronRightArcAngle c T <=
          2 * Real.pi - theta := by linarith
      have hCosPhi := Real.cos_le_cos_of_nonneg_of_le_pi
        hAnglePos.le hPhiPi hAnglePhi
      simpa [Real.cos_two_pi_sub] using hCosPhi
  have hRadius : 0 <= perronRightArcRadius c T := by
    dsimp [perronRightArcRadius]
    positivity
  have hEndpointRe :
      perronRightArcRadius c T * Real.cos (perronRightArcAngle c T) = c := by
    simpa [perronRightArc, circleMap_zero_re] using
      congrArg Complex.re (perronRightArc_angle (T := T) hc)
  have hMul := mul_le_mul_of_nonneg_left hCos hRadius
  simpa [perronLeftArc, circleMap_zero_re, hEndpointRe] using hMul

theorem perronLeftArc_length_lt_two_pi
    {c T : Real} (hc : 0 < c) (hT : 0 < T) :
    (2 * Real.pi - perronRightArcAngle c T) -
        perronRightArcAngle c T < 2 * Real.pi := by
  have hAnglePos : 0 < perronRightArcAngle c T := by
    rw [perronRightArcAngle]
    exact Real.arctan_pos.mpr (div_pos hT hc)
  linarith

def perronRightArcIntegral (y c T : Real) : Complex :=
  intervalIntegral
    (fun theta : Real =>
      (perronRightArc c T theta * Complex.I) *
        perronKernelIntegrand y (perronRightArc c T theta))
    (-perronRightArcAngle c T) (perronRightArcAngle c T)
    MeasureTheory.volume

private lemma continuous_perron_vertical_derivative_bv426
    {y c : Real} (hy : 0 < y) (hc : 0 < c) :
    Continuous
      (fun t : Real =>
        Complex.I * perronKernelIntegrand y
          ((c : Complex) + (t : Complex) * Complex.I)) := by
  have hEq :
      (fun t : Real =>
        Complex.I * perronKernelIntegrand y
          ((c : Complex) + (t : Complex) * Complex.I)) =
        fun t : Real => Complex.I *
          (Complex.exp
              ((Real.log y : Complex) *
                ((c : Complex) + (t : Complex) * Complex.I)) /
            ((c : Complex) + (t : Complex) * Complex.I)) := by
    funext t
    rw [perronKernelIntegrand_eq_exp hy]
  rw [hEq]
  fun_prop (disch :=
    intro t hzero
    have hReal := congrArg Complex.re hzero
    simp at hReal
    exact hc.ne' hReal)

private lemma continuous_perron_arc_derivative_bv426
    {y c T : Real} (hy : 0 < y) (hc : 0 < c) :
    Continuous
      (fun theta : Real =>
        (perronRightArc c T theta * Complex.I) *
          perronKernelIntegrand y (perronRightArc c T theta)) := by
  have hRadius : Ne (perronRightArcRadius c T) 0 := by
    apply ne_of_gt
    dsimp [perronRightArcRadius]
    positivity
  have hEq :
      (fun theta : Real =>
        (perronRightArc c T theta * Complex.I) *
          perronKernelIntegrand y (perronRightArc c T theta)) =
        fun theta : Real =>
          (perronRightArc c T theta * Complex.I) *
            (Complex.exp
                ((Real.log y : Complex) * perronRightArc c T theta) /
              perronRightArc c T theta) := by
    funext theta
    rw [perronKernelIntegrand_eq_exp hy]
  rw [hEq]
  simp only [perronRightArc]
  fun_prop (disch :=
    intro theta hzero
    have hCircleNe : Ne (circleMap 0 (perronRightArcRadius c T) theta) 0 :=
      circleMap_ne_center hRadius
    exact hCircleNe (by simpa [perronRightArc] using hzero))

theorem vIntegral_eq_perronRightArcIntegral
    {y c T : Real} (hy : 0 < y) (hc : 0 < c) (hT : 0 < T) :
    VIntegral (perronKernelIntegrand y) c (-T) T =
      perronRightArcIntegral y c T := by
  let S : Set Complex := {z : Complex | 0 < z.re}
  have hConvex : Convex Real S := by
    simpa [S] using convex_halfSpace_re_gt (0 : Real)
  have hOpen : IsOpen S := by
    dsimp [S]
    exact isOpen_lt continuous_const Complex.continuous_re
  choose F hF using hConvex.exists_forall_hasDerivWithinAt
    (holomorphicOn_perronKernelIntegrand hy)
  let vertical : Real -> Complex :=
    fun t => (c : Complex) + (t : Complex) * Complex.I
  have hVerticalMem (t : Real) : S (vertical t) := by
    change 0 < (vertical t).re
    simp [vertical, hc]
  have hVerticalDeriv (t : Real) :
      HasDerivAt (Function.comp F vertical)
        (Complex.I * perronKernelIntegrand y (vertical t)) t := by
    have hFAt := (hF (vertical t) (hVerticalMem t)).hasDerivAt
      (hOpen.mem_nhds (hVerticalMem t))
    have hPath : HasDerivAt vertical Complex.I t := by
      simpa [vertical] using
        (((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const Complex.I).const_add
          (c : Complex))
    simpa [smul_eq_mul, mul_comm] using hFAt.scomp t hPath
  have hVerticalFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := -T) (b := T)
    (f := Function.comp F vertical)
    (f' := fun t : Real =>
      Complex.I * perronKernelIntegrand y (vertical t))
    (fun t _ => hVerticalDeriv t)
    (by
      simpa [vertical] using
        (continuous_perron_vertical_derivative_bv426 hy hc).intervalIntegrable (-T) T)
  have hArcMem (theta : Real)
      (htheta : Set.uIcc (-perronRightArcAngle c T)
        (perronRightArcAngle c T) theta) :
      S (perronRightArc c T theta) := by
    change 0 < (perronRightArc c T theta).re
    exact hc.trans_le (perronRightArc_re_ge hc hT htheta)
  have hArcDeriv (theta : Real)
      (htheta : Set.uIcc (-perronRightArcAngle c T)
        (perronRightArcAngle c T) theta) :
      HasDerivAt (Function.comp F (perronRightArc c T))
        ((perronRightArc c T theta * Complex.I) *
          perronKernelIntegrand y (perronRightArc c T theta)) theta := by
    have hFAt := (hF (perronRightArc c T theta) (hArcMem theta htheta)).hasDerivAt
      (hOpen.mem_nhds (hArcMem theta htheta))
    have hPath : HasDerivAt (perronRightArc c T)
        (perronRightArc c T theta * Complex.I) theta := by
      change HasDerivAt (circleMap 0 (perronRightArcRadius c T))
        (circleMap 0 (perronRightArcRadius c T) theta * Complex.I) theta
      exact hasDerivAt_circleMap 0 (perronRightArcRadius c T) theta
    simpa [smul_eq_mul] using hFAt.scomp theta hPath
  have hArcFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := -perronRightArcAngle c T) (b := perronRightArcAngle c T)
    (f := Function.comp F (perronRightArc c T))
    (f' := fun theta : Real =>
      (perronRightArc c T theta * Complex.I) *
        perronKernelIntegrand y (perronRightArc c T theta))
    hArcDeriv
    (by
      exact (continuous_perron_arc_derivative_bv426 (T := T) hy hc).intervalIntegrable
        (-perronRightArcAngle c T) (perronRightArcAngle c T))
  rw [VIntegral, smul_eq_mul]
  have hVerticalValue :
      Complex.I * intervalIntegral
        (fun t : Real => perronKernelIntegrand y
          ((c : Complex) + (t : Complex) * Complex.I))
        (-T) T MeasureTheory.volume =
        Function.comp F vertical T - Function.comp F vertical (-T) := by
    rw [<- intervalIntegral.integral_const_mul]
    simpa [vertical] using hVerticalFTC
  rw [hVerticalValue]
  rw [perronRightArcIntegral, hArcFTC]
  simp only [Function.comp_apply, vertical]
  rw [perronRightArc_angle hc, perronRightArc_neg_angle hc]
  have hLower :
      (c : Complex) + ((-T : Real) : Complex) * Complex.I =
        (c : Complex) - (T : Complex) * Complex.I := by
    push_cast
    ring
  rw [hLower]

def perronLeftArcIntegral (y c T : Real) : Complex :=
  intervalIntegral
    (fun theta : Real =>
      (perronLeftArc c T theta * Complex.I) *
        perronKernelIntegrand y (perronLeftArc c T theta))
    (perronRightArcAngle c T)
    (2 * Real.pi - perronRightArcAngle c T)
    MeasureTheory.volume

private lemma continuous_perron_circle_integrand_bv427
    {y c T : Real} (hy : 0 < y) (hc : 0 < c) :
    Continuous
      (fun theta : Real =>
        (perronLeftArc c T theta * Complex.I) *
          perronKernelIntegrand y (perronLeftArc c T theta)) := by
  have hRadius : Ne (perronRightArcRadius c T) 0 := by
    apply ne_of_gt
    dsimp [perronRightArcRadius]
    positivity
  have hEq :
      (fun theta : Real =>
        (perronLeftArc c T theta * Complex.I) *
          perronKernelIntegrand y (perronLeftArc c T theta)) =
        fun theta : Real =>
          (perronLeftArc c T theta * Complex.I) *
            (Complex.exp
                ((Real.log y : Complex) * perronLeftArc c T theta) /
              perronLeftArc c T theta) := by
    funext theta
    rw [perronKernelIntegrand_eq_exp hy]
  rw [hEq]
  simp only [perronLeftArc]
  fun_prop (disch :=
    intro theta hzero
    have hCircleNe : Ne (circleMap 0 (perronRightArcRadius c T) theta) 0 :=
      circleMap_ne_center hRadius
    exact hCircleNe hzero)

theorem perronArcIntegrals_add_eq_circleIntegral
    {y c T : Real} (hy : 0 < y) (hc : 0 < c) :
    perronRightArcIntegral y c T + perronLeftArcIntegral y c T =
      circleIntegral (perronKernelIntegrand y) 0 (perronRightArcRadius c T) := by
  let a := perronRightArcAngle c T
  let b := 2 * Real.pi - a
  let q : Real -> Complex := fun theta =>
    (perronLeftArc c T theta * Complex.I) *
      perronKernelIntegrand y (perronLeftArc c T theta)
  have hCont : Continuous q := by
    simpa [q] using continuous_perron_circle_integrand_bv427 (T := T) hy hc
  have hPeriodic : Function.Periodic q (2 * Real.pi) := by
    intro theta
    dsimp [q, perronLeftArc]
    have hCircle := periodic_circleMap 0 (perronRightArcRadius c T) theta
    rw [hCircle]
  have hShiftBase := intervalIntegral.integral_comp_add_right
    (f := q) (a := -a) (b := 0) (2 * Real.pi)
  have hShift :
      intervalIntegral q (-a) 0 MeasureTheory.volume =
        intervalIntegral q b (2 * Real.pi) MeasureTheory.volume := by
    calc
      intervalIntegral q (-a) 0 MeasureTheory.volume =
          intervalIntegral (fun theta => q (theta + 2 * Real.pi))
            (-a) 0 MeasureTheory.volume := by
        apply intervalIntegral.integral_congr
        intro theta _
        exact (hPeriodic theta).symm
      _ = intervalIntegral q (-a + 2 * Real.pi)
          (0 + 2 * Real.pi) MeasureTheory.volume := hShiftBase
      _ = intervalIntegral q b (2 * Real.pi) MeasureTheory.volume := by
        dsimp [b]
        congr 1 <;> ring
  have hIntNegZero : IntervalIntegrable q MeasureTheory.volume (-a) 0 :=
    hCont.intervalIntegrable (-a) 0
  have hIntZeroA : IntervalIntegrable q MeasureTheory.volume 0 a :=
    hCont.intervalIntegrable 0 a
  have hIntAB : IntervalIntegrable q MeasureTheory.volume a b :=
    hCont.intervalIntegrable a b
  have hIntZeroB : IntervalIntegrable q MeasureTheory.volume 0 b :=
    hCont.intervalIntegrable 0 b
  have hIntBFull : IntervalIntegrable q MeasureTheory.volume b (2 * Real.pi) :=
    hCont.intervalIntegrable b (2 * Real.pi)
  have hRightSplit := intervalIntegral.integral_add_adjacent_intervals
    hIntNegZero hIntZeroA
  have hMiddleSplit := intervalIntegral.integral_add_adjacent_intervals
    hIntZeroA hIntAB
  have hFullSplit := intervalIntegral.integral_add_adjacent_intervals
    hIntZeroB hIntBFull
  rw [perronRightArcIntegral, perronLeftArcIntegral, circleIntegral]
  simp only [deriv_circleMap, smul_eq_mul, perronRightArc, perronLeftArc]
  change intervalIntegral q (-a) a MeasureTheory.volume +
      intervalIntegral q a b MeasureTheory.volume =
    intervalIntegral q 0 (2 * Real.pi) MeasureTheory.volume
  calc
    intervalIntegral q (-a) a MeasureTheory.volume +
        intervalIntegral q a b MeasureTheory.volume =
        (intervalIntegral q (-a) 0 MeasureTheory.volume +
          intervalIntegral q 0 a MeasureTheory.volume) +
            intervalIntegral q a b MeasureTheory.volume := by
      rw [hRightSplit]
    _ = (intervalIntegral q b (2 * Real.pi) MeasureTheory.volume +
          intervalIntegral q 0 a MeasureTheory.volume) +
            intervalIntegral q a b MeasureTheory.volume := by
      rw [hShift]
    _ = (intervalIntegral q 0 a MeasureTheory.volume +
          intervalIntegral q a b MeasureTheory.volume) +
            intervalIntegral q b (2 * Real.pi) MeasureTheory.volume := by
      abel
    _ = intervalIntegral q 0 b MeasureTheory.volume +
          intervalIntegral q b (2 * Real.pi) MeasureTheory.volume := by
      rw [hMiddleSplit]
    _ = intervalIntegral q 0 (2 * Real.pi) MeasureTheory.volume := hFullSplit

theorem truncatedPerronKernel_sub_one_eq_neg_leftArc
    {y c T : Real} (hy1 : 1 < y) (hc : 0 < c) (hT : 0 < T) :
    truncatedPerronKernel y c T - 1 =
      -(1 / (2 * Real.pi * Complex.I) : Complex) *
        perronLeftArcIntegral y c T := by
  have hy : 0 < y := lt_trans Real.zero_lt_one hy1
  have hRadius : 0 < perronRightArcRadius c T := by
    dsimp [perronRightArcRadius]
    positivity
  have hRaw :
      VIntegral (perronKernelIntegrand y) c (-T) T +
          perronLeftArcIntegral y c T =
        2 * Real.pi * Complex.I := by
    calc
      VIntegral (perronKernelIntegrand y) c (-T) T +
          perronLeftArcIntegral y c T =
          perronRightArcIntegral y c T +
            perronLeftArcIntegral y c T := by
        rw [vIntegral_eq_perronRightArcIntegral hy hc hT]
      _ = circleIntegral (perronKernelIntegrand y) 0
          (perronRightArcRadius c T) :=
        perronArcIntegrals_add_eq_circleIntegral hy hc
      _ = 2 * Real.pi * Complex.I :=
        circleIntegral_perronKernelIntegrand_eq hy hRadius
  let a : Complex := 1 / (2 * Real.pi * Complex.I)
  have hNormalize : a * (2 * Real.pi * Complex.I) = 1 := by
    dsimp [a]
    field_simp [ne_of_gt Real.pi_pos, Complex.I_ne_zero]
  rw [truncatedPerronKernel, VIntegral', smul_eq_mul]
  change a * VIntegral (perronKernelIntegrand y) c (-T) T - 1 =
    -a * perronLeftArcIntegral y c T
  rw [<- hNormalize]
  linear_combination a * hRaw

theorem norm_perronRightArc_integrand
    {y c T theta : Real} (hy : 0 < y) (hc : 0 < c) :
    norm ((perronRightArc c T theta * Complex.I) *
      perronKernelIntegrand y (perronRightArc c T theta)) =
      y ^ (perronRightArc c T theta).re := by
  have hRadius : 0 < perronRightArcRadius c T := by
    dsimp [perronRightArcRadius]
    positivity
  have hNorm : norm (perronRightArc c T theta) = perronRightArcRadius c T := by
    rw [perronRightArc, norm_circleMap_zero, abs_of_pos hRadius]
  rw [norm_mul, norm_mul, Complex.norm_I,
    norm_perronKernelIntegrand hy, hNorm]
  field_simp

theorem norm_perronRightArc_integrand_le
    {y c T theta : Real} (hy : 0 < y) (hy1 : y < 1)
    (hc : 0 < c) (hT : 0 < T)
    (htheta : Set.uIcc (-perronRightArcAngle c T)
      (perronRightArcAngle c T) theta) :
    norm ((perronRightArc c T theta * Complex.I) *
      perronKernelIntegrand y (perronRightArc c T theta)) <= y ^ c := by
  rw [norm_perronRightArc_integrand hy hc]
  exact Real.rpow_le_rpow_of_exponent_ge hy hy1.le
    (perronRightArc_re_ge hc hT htheta)

theorem norm_perronRightArcIntegral_le
    {y c T : Real} (hy : 0 < y) (hy1 : y < 1)
    (hc : 0 < c) (hT : 0 < T) :
    norm (perronRightArcIntegral y c T) <=
      y ^ c * abs (perronRightArcAngle c T -
        (-perronRightArcAngle c T)) := by
  rw [perronRightArcIntegral]
  exact intervalIntegral.norm_integral_le_of_norm_le_const
    (fun theta htheta =>
      norm_perronRightArc_integrand_le hy hy1 hc hT
        (Set.uIoc_subset_uIcc htheta))

theorem norm_perronRightArcIntegral_lt_pi_mul
    {y c T : Real} (hy : 0 < y) (hy1 : y < 1)
    (hc : 0 < c) (hT : 0 < T) :
    norm (perronRightArcIntegral y c T) < Real.pi * y ^ c := by
  have hAnglePos : 0 < perronRightArcAngle c T := by
    rw [perronRightArcAngle]
    exact Real.arctan_pos.mpr (div_pos hT hc)
  have hAngleLt : perronRightArcAngle c T < Real.pi / 2 := by
    exact Real.arctan_lt_pi_div_two (T / c)
  have hLength :
      abs (perronRightArcAngle c T -
        (-perronRightArcAngle c T)) < Real.pi := by
    rw [abs_of_pos (by linarith)]
    linarith
  calc
    norm (perronRightArcIntegral y c T) <=
        y ^ c * abs (perronRightArcAngle c T -
          (-perronRightArcAngle c T)) :=
      norm_perronRightArcIntegral_le hy hy1 hc hT
    _ < y ^ c * Real.pi :=
      mul_lt_mul_of_pos_left hLength (Real.rpow_pos_of_pos hy c)
    _ = Real.pi * y ^ c := by ring

theorem norm_perronLeftArc_integrand_le
    {y c T theta : Real} (hy1 : 1 < y) (hc : 0 < c) (hT : 0 < T)
    (htheta : Set.uIcc (perronRightArcAngle c T)
      (2 * Real.pi - perronRightArcAngle c T) theta) :
    norm ((perronLeftArc c T theta * Complex.I) *
      perronKernelIntegrand y (perronLeftArc c T theta)) <= y ^ c := by
  have hy : 0 < y := lt_trans Real.zero_lt_one hy1
  rw [show norm ((perronLeftArc c T theta * Complex.I) *
      perronKernelIntegrand y (perronLeftArc c T theta)) =
      y ^ (perronLeftArc c T theta).re by
    simpa [perronLeftArc, perronRightArc] using
      (norm_perronRightArc_integrand (T := T) (theta := theta) hy hc)]
  exact Real.rpow_le_rpow_of_exponent_le hy1.le
    (perronLeftArc_re_le hc hT htheta)

theorem norm_perronLeftArcIntegral_le
    {y c T : Real} (hy1 : 1 < y) (hc : 0 < c) (hT : 0 < T) :
    norm (perronLeftArcIntegral y c T) <=
      y ^ c * abs ((2 * Real.pi - perronRightArcAngle c T) -
        perronRightArcAngle c T) := by
  rw [perronLeftArcIntegral]
  exact intervalIntegral.norm_integral_le_of_norm_le_const
    (fun theta htheta =>
      norm_perronLeftArc_integrand_le hy1 hc hT
        (Set.uIoc_subset_uIcc htheta))

theorem norm_perronLeftArcIntegral_lt_two_pi_mul
    {y c T : Real} (hy1 : 1 < y) (hc : 0 < c) (hT : 0 < T) :
    norm (perronLeftArcIntegral y c T) < 2 * Real.pi * y ^ c := by
  have hy : 0 < y := lt_trans Real.zero_lt_one hy1
  have hAnglePos : 0 < perronRightArcAngle c T := by
    rw [perronRightArcAngle]
    exact Real.arctan_pos.mpr (div_pos hT hc)
  have hAngleLt : perronRightArcAngle c T < Real.pi / 2 :=
    Real.arctan_lt_pi_div_two _
  have hLengthPos : 0 <
      (2 * Real.pi - perronRightArcAngle c T) -
        perronRightArcAngle c T := by
    linarith [Real.pi_pos]
  have hLength := perronLeftArc_length_lt_two_pi hc hT
  calc
    norm (perronLeftArcIntegral y c T) <=
        y ^ c * abs ((2 * Real.pi - perronRightArcAngle c T) -
          perronRightArcAngle c T) :=
      norm_perronLeftArcIntegral_le hy1 hc hT
    _ = y ^ c * ((2 * Real.pi - perronRightArcAngle c T) -
          perronRightArcAngle c T) := by
      rw [abs_of_pos hLengthPos]
    _ < y ^ c * (2 * Real.pi) :=
      mul_lt_mul_of_pos_left hLength (Real.rpow_pos_of_pos hy c)
    _ = 2 * Real.pi * y ^ c := by ring

theorem norm_truncatedPerronKernel_sub_one_lt_unit_bound
    {y c T : Real} (hy1 : 1 < y) (hc : 0 < c) (hT : 0 < T) :
    norm (truncatedPerronKernel y c T - 1) < y ^ c := by
  let a : Complex := 1 / (2 * Real.pi * Complex.I)
  have hCoeff : norm a = 1 / (2 * Real.pi) := by
    dsimp [a]
    rw [norm_div, norm_one, norm_mul, norm_mul]
    simp [Complex.norm_I, abs_of_pos Real.pi_pos]
  have hCoeffPos : 0 < norm a := by
    rw [hCoeff]
    positivity
  rw [truncatedPerronKernel_sub_one_eq_neg_leftArc hy1 hc hT]
  change norm (-a * perronLeftArcIntegral y c T) < _
  rw [norm_mul, norm_neg]
  calc
    norm a * norm (perronLeftArcIntegral y c T) <
        norm a * (2 * Real.pi * y ^ c) :=
      mul_lt_mul_of_pos_left
        (norm_perronLeftArcIntegral_lt_two_pi_mul hy1 hc hT) hCoeffPos
    _ = y ^ c := by
      rw [hCoeff]
      field_simp [ne_of_gt Real.pi_pos]

theorem norm_truncatedPerronKernel_sub_one_lt_min_bound
    {y c T : Real} (hy1 : 1 < y) (hc : 0 < c) (hT : 0 < T) :
    norm (truncatedPerronKernel y c T - 1) <
      y ^ c * min 1 (1 / (Real.pi * T * abs (Real.log y))) := by
  have hy : 0 < y := lt_trans Real.zero_lt_one hy1
  have hPowerNonneg : 0 <= y ^ c := (Real.rpow_pos_of_pos hy c).le
  rw [mul_min_of_nonneg 1 (1 / (Real.pi * T * abs (Real.log y)))
    hPowerNonneg]
  apply lt_min
  next =>
    simpa using norm_truncatedPerronKernel_sub_one_lt_unit_bound hy1 hc hT
  next =>
    simpa [div_eq_mul_inv] using
      norm_truncatedPerronKernel_sub_one_lt_log_bound hy1 hc hT

theorem norm_truncatedPerronKernel_sub_stepWeight_lt_of_one_lt
    {y c T : Real} (hy1 : 1 < y) (hc : 0 < c) (hT : 0 < T) :
    norm (truncatedPerronKernel y c T -
      (perronStepWeight y : Complex)) <
      y ^ c * min 1 (1 / (Real.pi * T * abs (Real.log y))) := by
  have hWeight : perronStepWeight y = 1 := by
    simp [perronStepWeight, not_lt_of_ge hy1.le, ne_of_gt hy1]
  rw [hWeight, Complex.ofReal_one]
  exact norm_truncatedPerronKernel_sub_one_lt_min_bound hy1 hc hT

end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

open MeasureTheory Set

namespace BombieriVinogradov.SiegelWalfisz

theorem integrableOn_rpow_Ioi
    {y : Real} (hy : 0 < y) (hy1 : y < 1) (c : Real) :
    IntegrableOn (fun x : Real => y ^ x) (Ioi c) := by
  simpa [Real.rpow_def_of_pos hy] using
    integrableOn_exp_mul_Ioi (Real.log_neg hy hy1) c

theorem integral_rpow_Ioi
    {y : Real} (hy : 0 < y) (hy1 : y < 1) (c : Real) :
    integral (volume.restrict (Ioi c)) (fun x : Real => y ^ x) =
      y ^ c / abs (Real.log y) := by
  rw [show (fun x : Real => y ^ x) =
      fun x : Real => Real.exp (Real.log y * x) by
    funext x
    exact Real.rpow_def_of_pos hy x]
  rw [integral_exp_mul_Ioi (Real.log_neg hy hy1)]
  rw [(Real.rpow_def_of_pos hy c).symm]
  rw [abs_of_neg (Real.log_neg hy hy1)]
  ring

end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

open Filter MeasureTheory Set Topology

namespace BombieriVinogradov.SiegelWalfisz

private lemma sqrt_sq_add_sq_le_norm_add_mul_I_bv433
    {c t x : Real} (hc : 0 < c) (hcx : c <= x) :
    Real.sqrt (c ^ 2 + t ^ 2) <=
      norm ((x : Complex) + (t : Complex) * Complex.I) := by
  rw [Complex.norm_def, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero,
    Complex.add_im, Complex.mul_im, zero_add]
  apply Real.sqrt_le_sqrt
  nlinarith

theorem norm_perron_horizontal_le
    {y c t x : Real} (hy : 0 < y) (hc : 0 < c) (hcx : c <= x) :
    norm (perronKernelIntegrand y
      ((x : Complex) + (t : Complex) * Complex.I)) <=
      y ^ x / Real.sqrt (c ^ 2 + t ^ 2) := by
  rw [norm_perronKernelIntegrand hy]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero]
  have hLower : Real.sqrt (c ^ 2 + t ^ 2) <=
      norm ((x : Complex) + (t : Complex) * Complex.I) :=
    sqrt_sq_add_sq_le_norm_add_mul_I_bv433 hc hcx
  have hD : 0 < Real.sqrt (c ^ 2 + t ^ 2) := by positivity
  exact div_le_div_of_nonneg_left (Real.rpow_nonneg hy.le x) hD hLower

theorem integrableOn_perron_horizontal_Ioi
    {y c t : Real} (hy : 0 < y) (hy1 : y < 1) (hc : 0 < c) :
    IntegrableOn
      (fun x : Real => perronKernelIntegrand y
        ((x : Complex) + (t : Complex) * Complex.I))
      (Ioi c) := by
  let D : Real := Real.sqrt (c ^ 2 + t ^ 2)
  have hD : 0 < D := by
    dsimp [D]
    positivity
  have hDom : IntegrableOn (fun x : Real => y ^ x / D) (Ioi c) :=
    (integrableOn_rpow_Ioi hy hy1 c).div_const D
  apply hDom.mono'
  next =>
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    intro x hx
    have hEq :
        (fun u : Real => perronKernelIntegrand y
          ((u : Complex) + (t : Complex) * Complex.I)) =
          fun u : Real =>
            Complex.exp
                ((Real.log y : Complex) *
                  ((u : Complex) + (t : Complex) * Complex.I)) /
              ((u : Complex) + (t : Complex) * Complex.I) := by
      funext u
      exact perronKernelIntegrand_eq_exp hy _
    rw [hEq]
    have hNumerator :
        ContinuousAt
          (fun u : Real =>
            Complex.exp
              ((Real.log y : Complex) *
                ((u : Complex) + (t : Complex) * Complex.I))) x := by
      fun_prop
    have hDenominator :
        ContinuousAt
          (fun u : Real => (u : Complex) + (t : Complex) * Complex.I) x := by
      fun_prop
    have hNe : Ne ((x : Complex) + (t : Complex) * Complex.I) 0 := by
      intro hzero
      have hReal := congrArg Complex.re hzero
      simp at hReal
      change c < x at hx
      linarith
    exact (hNumerator.div hDenominator hNe).continuousWithinAt
  next =>
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact norm_perron_horizontal_le hy hc hx.le

theorem norm_integral_perron_horizontal_Ioi_le
    {y c t : Real} (hy : 0 < y) (hy1 : y < 1) (hc : 0 < c) :
    norm
        (integral (volume.restrict (Ioi c))
          (fun x : Real => perronKernelIntegrand y
            ((x : Complex) + (t : Complex) * Complex.I))) <=
      y ^ c /
        (Real.sqrt (c ^ 2 + t ^ 2) * abs (Real.log y)) := by
  let D : Real := Real.sqrt (c ^ 2 + t ^ 2)
  have hDom : IntegrableOn (fun x : Real => y ^ x / D) (Ioi c) :=
    (integrableOn_rpow_Ioi hy hy1 c).div_const D
  have hNorm :
      norm
          (integral (volume.restrict (Ioi c))
            (fun x : Real => perronKernelIntegrand y
              ((x : Complex) + (t : Complex) * Complex.I))) <=
        integral (volume.restrict (Ioi c)) (fun x : Real => y ^ x / D) := by
    apply MeasureTheory.norm_integral_le_of_norm_le hDom
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact norm_perron_horizontal_le hy hc hx.le
  calc
    norm
        (integral (volume.restrict (Ioi c))
          (fun x : Real => perronKernelIntegrand y
            ((x : Complex) + (t : Complex) * Complex.I))) <=
        integral (volume.restrict (Ioi c)) (fun x : Real => y ^ x / D) := hNorm
    _ = (1 / D) * integral (volume.restrict (Ioi c)) (fun x : Real => y ^ x) := by
      rw [show (fun x : Real => y ^ x / D) = fun x : Real => (1 / D) * y ^ x by
        funext x
        ring]
      rw [integral_const_mul]
    _ = y ^ c / (Real.sqrt (c ^ 2 + t ^ 2) * abs (Real.log y)) := by
      rw [integral_rpow_Ioi hy hy1]
      dsimp [D]
      ring

def rightHorizontalIntegral (y c t : Real) : Complex :=
  integral (volume.restrict (Ioi c))
    (fun x : Real => perronKernelIntegrand y
      ((x : Complex) + (t : Complex) * Complex.I))

theorem tendsto_hIntegral'_right_atTop
    {y c t : Real} (hy : 0 < y) (hy1 : y < 1) (hc : 0 < c) :
    Tendsto
      (fun R : Real => HIntegral' (perronKernelIntegrand y) c R t)
      atTop
      (nhds
        ((1 / (2 * Real.pi * Complex.I) : Complex) *
          rightHorizontalIntegral y c t)) := by
  have hLimit := intervalIntegral_tendsto_integral_Ioi
    (f := fun x : Real => perronKernelIntegrand y
      ((x : Complex) + (t : Complex) * Complex.I)) c
    (integrableOn_perron_horizontal_Ioi (t := t) hy hy1 hc) tendsto_id
  simpa [HIntegral', HIntegral, rightHorizontalIntegral, smul_eq_mul] using
    hLimit.const_smul (1 / (2 * Real.pi * Complex.I) : Complex)

theorem vIntegral_eq_right_rectangle_terms
    {y c T R : Real} (hy : 0 < y) (hc : 0 < c) (hT : 0 < T)
    (hcR : c <= R) :
    VIntegral (perronKernelIntegrand y) c (-T) T =
      HIntegral (perronKernelIntegrand y) c R (-T) -
        HIntegral (perronKernelIntegrand y) c R T +
          VIntegral (perronKernelIntegrand y) R (-T) T := by
  let z : Complex := (c : Complex) - Complex.I * (T : Complex)
  let w : Complex := (R : Complex) + Complex.I * (T : Complex)
  have hIm : z.im <= w.im := by
    dsimp [z, w]
    simp
    linarith
  have hRe : z.re <= w.re := by
    simpa [z, w] using hcR
  have hSubset : Complex.Rectangle z w <= {s : Complex | 0 < s.re} := by
    intro s hs
    have hCoords := (mem_Rect hRe hIm s).mp hs
    have hLower : c <= s.re := by
      simpa [z, w] using hCoords.1
    exact hc.trans_le hLower
  have hZero : RectangleIntegral (perronKernelIntegrand y) z w = 0 :=
    (holomorphicOn_perronKernelIntegrand hy).vanishesOnRectangle hSubset
  have hExpanded :
      HIntegral (perronKernelIntegrand y) c R (-T) -
          HIntegral (perronKernelIntegrand y) c R T +
          VIntegral (perronKernelIntegrand y) R (-T) T -
          VIntegral (perronKernelIntegrand y) c (-T) T = 0 := by
    simpa [z, w, RectangleIntegral] using hZero
  linear_combination -hExpanded

theorem truncatedPerronKernel_eq_right_rectangle_terms
    {y c T R : Real} (hy : 0 < y) (hc : 0 < c) (hT : 0 < T)
    (hcR : c <= R) :
    truncatedPerronKernel y c T =
      HIntegral' (perronKernelIntegrand y) c R (-T) -
        HIntegral' (perronKernelIntegrand y) c R T +
          VIntegral' (perronKernelIntegrand y) R (-T) T := by
  simp only [truncatedPerronKernel, HIntegral', VIntegral']
  rw [vIntegral_eq_right_rectangle_terms hy hc hT hcR]
  module

end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

open Filter Topology

namespace BombieriVinogradov.SiegelWalfisz

private lemma norm_perron_vertical_integrand_le_bv435
    {y R t : Real} (hy : 0 < y) (hR : 0 < R) :
    norm (perronKernelIntegrand y
      ((R : Complex) + (t : Complex) * Complex.I)) <= y ^ R / R := by
  rw [norm_perronKernelIntegrand hy]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero]
  have hLower : R <= norm ((R : Complex) + (t : Complex) * Complex.I) := by
    simpa using Complex.re_le_norm ((R : Complex) + (t : Complex) * Complex.I)
  exact div_le_div_of_nonneg_left (Real.rpow_nonneg hy.le R) hR hLower

theorem norm_vIntegral_perron_right_le
    {y R T : Real} (hy : 0 < y) (hR : 0 < R) (hT : 0 <= T) :
    norm (VIntegral (perronKernelIntegrand y) R (-T) T) <=
      2 * T * (y ^ R / R) := by
  rw [VIntegral, norm_smul]
  simp only [Complex.norm_I, one_mul]
  have hIntegral := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := -T) (b := T)
    (f := fun t : Real => perronKernelIntegrand y
      ((R : Complex) + (t : Complex) * Complex.I))
    (C := y ^ R / R)
    (fun t _ => norm_perron_vertical_integrand_le_bv435 hy hR)
  calc
    norm
        (intervalIntegral
          (fun t : Real => perronKernelIntegrand y
            ((R : Complex) + (t : Complex) * Complex.I))
          (-T) T MeasureTheory.volume) <=
        (y ^ R / R) * abs (T - -T) := hIntegral
    _ = 2 * T * (y ^ R / R) := by
      rw [abs_of_nonneg (by linarith)]
      ring

theorem norm_vIntegral'_perron_right_le
    {y R T : Real} (hy : 0 < y) (hR : 0 < R) (hT : 0 <= T) :
    norm (VIntegral' (perronKernelIntegrand y) R (-T) T) <=
      (T / Real.pi) * (y ^ R / R) := by
  rw [VIntegral', norm_smul]
  calc
    norm (1 / (2 * (Real.pi : Complex) * Complex.I)) *
        norm (VIntegral (perronKernelIntegrand y) R (-T) T) <=
        norm (1 / (2 * (Real.pi : Complex) * Complex.I)) *
          (2 * T * (y ^ R / R)) := by
      gcongr
      exact norm_vIntegral_perron_right_le hy hR hT
    _ = (T / Real.pi) * (y ^ R / R) := by
      rw [norm_div, norm_one, norm_mul, norm_mul]
      simp [Complex.norm_I, abs_of_pos Real.pi_pos]
      field_simp [ne_of_gt Real.pi_pos]

theorem tendsto_vIntegral'_perron_right_atTop
    {y T : Real} (hy : 0 < y) (hy1 : y < 1) (hT : 0 <= T) :
    Tendsto (fun R : Real =>
      VIntegral' (perronKernelIntegrand y) R (-T) T) atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hY : Tendsto (fun R : Real => y ^ R) atTop (nhds 0) :=
    tendsto_rpow_atTop_of_base_lt_one y (by linarith) hy1
  have hInv : Tendsto (fun R : Real => Inv.inv R) atTop (nhds 0) :=
    tendsto_inv_atTop_zero
  have hMajorant :
      Tendsto (fun R : Real => (T / Real.pi) * (y ^ R / R)) atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using (hY.mul hInv).const_mul (T / Real.pi)
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ hMajorant
  filter_upwards [eventually_gt_atTop (0 : Real)] with R hR
  exact norm_vIntegral'_perron_right_le hy hR hT

end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

open Filter Topology

namespace BombieriVinogradov.SiegelWalfisz

theorem truncatedPerronKernel_eq_rightHorizontalIntegrals
    {y c T : Real} (hy : 0 < y) (hy1 : y < 1) (hc : 0 < c)
    (hT : 0 < T) :
    truncatedPerronKernel y c T =
      (1 / (2 * Real.pi * Complex.I) : Complex) *
          rightHorizontalIntegral y c (-T) -
        (1 / (2 * Real.pi * Complex.I) : Complex) *
          rightHorizontalIntegral y c T := by
  have hBottom := tendsto_hIntegral'_right_atTop
    (t := -T) hy hy1 hc
  have hTop := tendsto_hIntegral'_right_atTop
    (t := T) hy hy1 hc
  have hRight := tendsto_vIntegral'_perron_right_atTop hy hy1 hT.le
  have hCombined := (hBottom.sub hTop).add hRight
  have hFinite : Filter.Eventually
      (fun R : Real => truncatedPerronKernel y c T =
        HIntegral' (perronKernelIntegrand y) c R (-T) -
          HIntegral' (perronKernelIntegrand y) c R T +
            VIntegral' (perronKernelIntegrand y) R (-T) T) atTop := by
    filter_upwards [eventually_ge_atTop c] with R hR
    exact truncatedPerronKernel_eq_right_rectangle_terms hy hc hT hR
  have hConst : Tendsto (fun _ : Real => truncatedPerronKernel y c T) atTop
      (nhds
        ((1 / (2 * Real.pi * Complex.I) : Complex) *
            rightHorizontalIntegral y c (-T) -
          (1 / (2 * Real.pi * Complex.I) : Complex) *
            rightHorizontalIntegral y c T)) := by
    have hCombined' : Tendsto
        (fun R : Real =>
          HIntegral' (perronKernelIntegrand y) c R (-T) -
            HIntegral' (perronKernelIntegrand y) c R T +
              VIntegral' (perronKernelIntegrand y) R (-T) T)
        atTop
        (nhds
          ((1 / (2 * Real.pi * Complex.I) : Complex) *
              rightHorizontalIntegral y c (-T) -
            (1 / (2 * Real.pi * Complex.I) : Complex) *
              rightHorizontalIntegral y c T)) := by
      simpa using hCombined
    apply hCombined'.congr'
    filter_upwards [hFinite] with R hR
    exact hR.symm
  exact tendsto_nhds_unique tendsto_const_nhds hConst

theorem norm_truncatedPerronKernel_le_sqrt_log_bound
    {y c T : Real} (hy : 0 < y) (hy1 : y < 1) (hc : 0 < c)
    (hT : 0 < T) :
    norm (truncatedPerronKernel y c T) <=
      y ^ c /
        (Real.pi * Real.sqrt (c ^ 2 + T ^ 2) * abs (Real.log y)) := by
  let a : Complex := 1 / (2 * Real.pi * Complex.I)
  let B : Real :=
    y ^ c / (Real.sqrt (c ^ 2 + T ^ 2) * abs (Real.log y))
  have hMinus : norm (rightHorizontalIntegral y c (-T)) <= B := by
    simpa [B, rightHorizontalIntegral] using
      (norm_integral_perron_horizontal_Ioi_le
        (t := -T) hy hy1 hc)
  have hPlus : norm (rightHorizontalIntegral y c T) <= B := by
    simpa [B, rightHorizontalIntegral] using
      (norm_integral_perron_horizontal_Ioi_le
        (t := T) hy hy1 hc)
  have hCoeff : norm a = 1 / (2 * Real.pi) := by
    dsimp [a]
    rw [norm_div, norm_one, norm_mul, norm_mul]
    simp [Complex.norm_I, abs_of_pos Real.pi_pos]
  rw [truncatedPerronKernel_eq_rightHorizontalIntegrals hy hy1 hc hT]
  change norm
      (a * rightHorizontalIntegral y c (-T) -
        a * rightHorizontalIntegral y c T) <= _
  calc
    norm
        (a * rightHorizontalIntegral y c (-T) -
          a * rightHorizontalIntegral y c T) <=
        norm (a * rightHorizontalIntegral y c (-T)) +
          norm (a * rightHorizontalIntegral y c T) := norm_sub_le _ _
    _ = norm a * norm (rightHorizontalIntegral y c (-T)) +
          norm a * norm (rightHorizontalIntegral y c T) := by
      rw [norm_mul, norm_mul]
    _ <= norm a * B + norm a * B := by
      gcongr
    _ = y ^ c /
          (Real.pi * Real.sqrt (c ^ 2 + T ^ 2) * abs (Real.log y)) := by
      rw [hCoeff]
      dsimp [B]
      field_simp [ne_of_gt Real.pi_pos]
      ring

theorem norm_truncatedPerronKernel_lt_log_bound
    {y c T : Real} (hy : 0 < y) (hy1 : y < 1) (hc : 0 < c)
    (hT : 0 < T) :
    norm (truncatedPerronKernel y c T) <
      y ^ c / (Real.pi * T * abs (Real.log y)) := by
  have hD : T < Real.sqrt (c ^ 2 + T ^ 2) := by
    have hSq : 0 <= c ^ 2 + T ^ 2 := by positivity
    have hSqrtSq := Real.sq_sqrt hSq
    have hSqrtNonneg := Real.sqrt_nonneg (c ^ 2 + T ^ 2)
    nlinarith [sq_pos_of_pos hc]
  have hLogAbs : 0 < abs (Real.log y) :=
    abs_pos.mpr (ne_of_lt (Real.log_neg hy hy1))
  have hNumerator : 0 < y ^ c := Real.rpow_pos_of_pos hy c
  have hSmallDenom : 0 < Real.pi * T * abs (Real.log y) := by positivity
  have hDenomLt :
      Real.pi * T * abs (Real.log y) <
        Real.pi * Real.sqrt (c ^ 2 + T ^ 2) * abs (Real.log y) := by
    nlinarith [Real.pi_pos]
  exact (norm_truncatedPerronKernel_le_sqrt_log_bound hy hy1 hc hT).trans_lt
    (div_lt_div_of_pos_left hNumerator hSmallDenom hDenomLt)

theorem norm_truncatedPerronKernel_lt_unit_bound
    {y c T : Real} (hy : 0 < y) (hy1 : y < 1)
    (hc : 0 < c) (hT : 0 < T) :
    norm (truncatedPerronKernel y c T) < y ^ c := by
  let a : Complex := 1 / (2 * Real.pi * Complex.I)
  have hCoeff : norm a = 1 / (2 * Real.pi) := by
    dsimp [a]
    rw [norm_div, norm_one, norm_mul, norm_mul]
    simp [Complex.norm_I, abs_of_pos Real.pi_pos]
  have hCoeffPos : 0 < norm a := by
    rw [hCoeff]
    positivity
  have hPowerPos : 0 < y ^ c := Real.rpow_pos_of_pos hy c
  rw [truncatedPerronKernel, VIntegral']
  change norm (a * VIntegral (perronKernelIntegrand y) c (-T) T) < _
  rw [vIntegral_eq_perronRightArcIntegral hy hc hT, norm_mul]
  calc
    norm a * norm (perronRightArcIntegral y c T) <
        norm a * (Real.pi * y ^ c) :=
      mul_lt_mul_of_pos_left
        (norm_perronRightArcIntegral_lt_pi_mul hy hy1 hc hT) hCoeffPos
    _ = y ^ c / 2 := by
      rw [hCoeff]
      field_simp [ne_of_gt Real.pi_pos]
    _ < y ^ c := by linarith

theorem norm_truncatedPerronKernel_lt_min_bound
    {y c T : Real} (hy : 0 < y) (hy1 : y < 1)
    (hc : 0 < c) (hT : 0 < T) :
    norm (truncatedPerronKernel y c T) <
      y ^ c * min 1 (1 / (Real.pi * T * abs (Real.log y))) := by
  have hPowerNonneg : 0 <= y ^ c := (Real.rpow_pos_of_pos hy c).le
  rw [mul_min_of_nonneg 1 (1 / (Real.pi * T * abs (Real.log y)))
    hPowerNonneg]
  apply lt_min
  next =>
    simpa using norm_truncatedPerronKernel_lt_unit_bound hy hy1 hc hT
  next =>
    simpa [div_eq_mul_inv] using
      norm_truncatedPerronKernel_lt_log_bound hy hy1 hc hT

theorem norm_truncatedPerronKernel_sub_stepWeight_lt_of_lt_one
    {y c T : Real} (hy : 0 < y) (hy1 : y < 1)
    (hc : 0 < c) (hT : 0 < T) :
    norm (truncatedPerronKernel y c T -
      (perronStepWeight y : Complex)) <
      y ^ c * min 1 (1 / (Real.pi * T * abs (Real.log y))) := by
  have hWeight : perronStepWeight y = 0 := by
    simp [perronStepWeight, hy1]
  rw [hWeight, Complex.ofReal_zero, sub_zero]
  exact norm_truncatedPerronKernel_lt_min_bound hy hy1 hc hT

end BombieriVinogradov.SiegelWalfisz

end
end

section

namespace Real

theorem arctan_lt_self_of_pos {x : Real} (hx : 0 < x) : arctan x < x := by
  have hArctanPos : 0 < arctan x := arctan_pos.mpr hx
  have hTangent := lt_tan hArctanPos (arctan_lt_pi_div_two x)
  simpa using hTangent

end Real

end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

private lemma inv_ofReal_add_ofReal_mul_I_bv441 (c t : Real) :
    Inv.inv ((c : Complex) + (t : Complex) * Complex.I) =
      ((c / (c ^ 2 + t ^ 2) : Real) : Complex) -
        ((t / (c ^ 2 + t ^ 2) : Real) : Complex) * Complex.I := by
  rw [Complex.inv_def]
  simp [Complex.normSq_apply, div_eq_mul_inv]
  ring

private lemma odd_fraction_integral_eq_zero_bv441 (c T : Real) :
    intervalIntegral (fun t : Real => t / (c ^ 2 + t ^ 2)) (-T) T
        MeasureTheory.volume = 0 := by
  let f : Real -> Real := fun t => t / (c ^ 2 + t ^ 2)
  have hOdd (t : Real) : f (-t) = -f t := by
    dsimp [f]
    ring
  have hComp := intervalIntegral.integral_comp_neg (f := f) (a := -T) (b := T)
  have hSame :
      intervalIntegral (fun t : Real => f (-t)) (-T) T MeasureTheory.volume =
        intervalIntegral f (-T) T MeasureTheory.volume := by
    simpa only [neg_neg] using hComp
  have hNeg :
      intervalIntegral (fun t : Real => f (-t)) (-T) T MeasureTheory.volume =
        -intervalIntegral f (-T) T MeasureTheory.volume := by
    calc
      intervalIntegral (fun t : Real => f (-t)) (-T) T MeasureTheory.volume =
          intervalIntegral (fun t : Real => -f t) (-T) T MeasureTheory.volume := by
        apply intervalIntegral.integral_congr
        intro t _
        exact hOdd t
      _ = -intervalIntegral f (-T) T MeasureTheory.volume :=
        intervalIntegral.integral_neg
  have hZero : intervalIntegral f (-T) T MeasureTheory.volume = 0 := by
    linarith
  simpa [f] using hZero

private lemma reciprocal_vertical_integral_eq_arctan_bv441
    {c T : Real} (hc : 0 < c) :
    intervalIntegral
        (fun t : Real => Inv.inv ((c : Complex) + (t : Complex) * Complex.I))
        (-T) T MeasureTheory.volume =
      ((2 * Real.arctan (T / c) : Real) : Complex) := by
  have hden (t : Real) : Ne (c ^ 2 + t ^ 2) 0 := by
    nlinarith [sq_nonneg t]
  have hRealContinuous : Continuous (fun t : Real => c / (c ^ 2 + t ^ 2)) := by
    fun_prop (disch := exact hden _)
  have hImagContinuous : Continuous (fun t : Real => t / (c ^ 2 + t ^ 2)) := by
    fun_prop (disch := exact hden _)
  have hRealComplexContinuous :
      Continuous (fun t : Real => ((c / (c ^ 2 + t ^ 2) : Real) : Complex)) := by
    fun_prop
  have hImagComplexContinuous :
      Continuous
        (fun t : Real =>
          ((t / (c ^ 2 + t ^ 2) : Real) : Complex) * Complex.I) := by
    fun_prop
  have hRealIntegral :
      intervalIntegral (fun t : Real => c / (c ^ 2 + t ^ 2)) (-T) T
          MeasureTheory.volume =
        2 * Real.arctan (T / c) := by
    calc
      intervalIntegral (fun t : Real => c / (c ^ 2 + t ^ 2)) (-T) T
          MeasureTheory.volume =
          Real.arctan (T / c) - Real.arctan (-T / c) := integral_div_sq_add_sq
      _ = 2 * Real.arctan (T / c) := by
        rw [neg_div, Real.arctan_neg]
        ring
  calc
    intervalIntegral
        (fun t : Real => Inv.inv ((c : Complex) + (t : Complex) * Complex.I))
        (-T) T MeasureTheory.volume =
        intervalIntegral
          (fun t : Real =>
            ((c / (c ^ 2 + t ^ 2) : Real) : Complex) -
              ((t / (c ^ 2 + t ^ 2) : Real) : Complex) * Complex.I)
          (-T) T MeasureTheory.volume := by
      apply intervalIntegral.integral_congr
      intro t _
      exact inv_ofReal_add_ofReal_mul_I_bv441 c t
    _ = intervalIntegral
          (fun t : Real => ((c / (c ^ 2 + t ^ 2) : Real) : Complex))
          (-T) T MeasureTheory.volume -
        intervalIntegral
          (fun t : Real =>
            ((t / (c ^ 2 + t ^ 2) : Real) : Complex) * Complex.I)
          (-T) T MeasureTheory.volume := by
      exact intervalIntegral.integral_sub
        (hRealComplexContinuous.intervalIntegrable _ _)
        (hImagComplexContinuous.intervalIntegrable _ _)
    _ = ((2 * Real.arctan (T / c) : Real) : Complex) := by
      rw [intervalIntegral.integral_mul_const]
      rw [intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal]
      rw [hRealIntegral, odd_fraction_integral_eq_zero_bv441]
      simp

theorem truncatedPerronKernel_one_eq_arctan
    {c T : Real} (hc : 0 < c) :
    truncatedPerronKernel 1 c T =
      (Real.arctan (T / c) / Real.pi : Complex) := by
  rw [truncatedPerronKernel]
  simp [perronKernelIntegrand, VIntegral', VIntegral]
  rw [reciprocal_vertical_integral_eq_arctan_bv441 hc]
  push_cast
  field_simp
  ring_nf
  simp [Complex.I_sq]

theorem norm_truncatedPerronKernel_one_sub_perronStepWeight_lt
    {c T : Real} (hc : 0 < c) (hT : 0 < T) :
    norm
        (truncatedPerronKernel 1 c T -
          (perronStepWeight 1 : Complex)) <
      c / (Real.pi * T) := by
  have hRatio : 0 < T / c := div_pos hT hc
  have hInverse : Inv.inv (T / c) = c / T := by
    field_simp
  have hComplement :
      Real.pi / 2 - Real.arctan (T / c) = Real.arctan (c / T) := by
    rw [hInverse.symm]
    exact (Real.arctan_inv_of_pos hRatio).symm
  have hArctanUpper : Real.arctan (T / c) < Real.pi / 2 :=
    Real.arctan_lt_pi_div_two _
  have hSmall : Real.arctan (c / T) < c / T :=
    Real.arctan_lt_self_of_pos (div_pos hc hT)
  have hDifferenceNeg :
      Real.arctan (T / c) / Real.pi - 1 / 2 < 0 := by
    have hScaledUpper :
        Real.arctan (T / c) / Real.pi < (Real.pi / 2) / Real.pi :=
      div_lt_div_of_pos_right hArctanUpper Real.pi_pos
    have hHalf : (Real.pi / 2) / Real.pi = 1 / 2 := by
      field_simp [ne_of_gt Real.pi_pos]
    rw [hHalf] at hScaledUpper
    exact sub_neg.mpr hScaledUpper
  rw [truncatedPerronKernel_one_eq_arctan hc, perronStepWeight_one]
  rw [(Complex.ofReal_div _ _).symm, (Complex.ofReal_sub _ _).symm,
    Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_neg hDifferenceNeg]
  rw [show
      Real.arctan (T / c) / Real.pi - 1 / 2 =
        -(Real.arctan (c / T) / Real.pi) by
      rw [hComplement.symm]
      field_simp [ne_of_gt Real.pi_pos]
      ring]
  rw [neg_neg]
  have hPi : 0 < Real.pi := Real.pi_pos
  have hScaled : Real.arctan (c / T) / Real.pi < (c / T) / Real.pi :=
    div_lt_div_of_pos_right hSmall hPi
  calc
    Real.arctan (c / T) / Real.pi < (c / T) / Real.pi := hScaled
    _ = c / (Real.pi * T) := by field_simp

theorem norm_truncatedPerronKernel_sub_stepWeight_lt
    {y c T : Real} (hy : 0 < y) (hc : 0 < c) (hT : 0 < T) :
    norm (truncatedPerronKernel y c T -
      (perronStepWeight y : Complex)) <
      if y = 1 then c / (Real.pi * T)
      else y ^ c * min 1 (1 / (Real.pi * T * abs (Real.log y))) := by
  rcases lt_trichotomy y 1 with hy1 | hyeq | hy1
  next =>
    rw [if_neg (ne_of_lt hy1)]
    exact norm_truncatedPerronKernel_sub_stepWeight_lt_of_lt_one
      hy hy1 hc hT
  next =>
    subst y
    rw [if_pos rfl]
    exact norm_truncatedPerronKernel_one_sub_perronStepWeight_lt hc hT
  next =>
    rw [if_neg (ne_of_gt hy1)]
    exact norm_truncatedPerronKernel_sub_stepWeight_lt_of_one_lt hy1 hc hT

theorem norm_scalarPerronErrorTerm_le_majorant
    {N : Nat} (chi : DirichletCharacter Complex N) {x : Nat} (hx : 0 < x)
    {c T : Real} (hc : 0 < c) (hT : 0 < T) (n : Nat) :
    norm (scalarPerronErrorTerm chi x c T n) <=
      scalarPerronErrorMajorantTerm chi x c T n := by
  by_cases hn : n = 0
  case pos =>
    subst n
    simp [scalarPerronErrorTerm, scalarPerronErrorMajorantTerm,
      scalarPerronSeriesTerm, scalarPerronStepTerm]
  case neg =>
    have hnPos : 0 < n := Nat.pos_of_ne_zero hn
    have hRatioPos : 0 < (x : Real) / (n : Real) :=
      div_pos (by exact_mod_cast hx) (by exact_mod_cast hnPos)
    have hPerron := norm_truncatedPerronKernel_sub_stepWeight_lt
      hRatioPos hc hT
    rw [scalarPerronErrorTerm, scalarPerronSeriesTerm,
      scalarPerronStepTerm, if_neg hn, if_neg hn,
      scalarPerronErrorMajorantTerm, if_neg hn]
    have hFactor :
        twistedMangoldtSequence chi n *
            truncatedPerronKernel ((x : Real) / (n : Real)) c T -
          twistedMangoldtSequence chi n *
            (perronStepWeight ((x : Real) / (n : Real)) : Complex) =
        twistedMangoldtSequence chi n *
          (truncatedPerronKernel ((x : Real) / (n : Real)) c T -
            (perronStepWeight ((x : Real) / (n : Real)) : Complex)) := by
      ring
    rw [hFactor, norm_mul]
    exact mul_le_mul_of_nonneg_left hPerron.le (norm_nonneg _)

theorem summable_norm_scalarPerronErrorTerm
    {N : Nat} (chi : DirichletCharacter Complex N) {x : Nat} (hx : 0 < x)
    {c T : Real} (hc : 1 < c) (hT : 0 < T) :
    Summable (fun n : Nat => norm (scalarPerronErrorTerm chi x c T n)) := by
  apply Summable.of_nonneg_of_le
    (fun _ => norm_nonneg _)
    (fun n => norm_scalarPerronErrorTerm_le_majorant chi hx
      (lt_trans zero_lt_one hc) hT n)
    (summable_scalarPerronErrorMajorantTerm chi hx hc hT)

theorem summable_scalarPerronErrorTerm
    {N : Nat} (chi : DirichletCharacter Complex N) {x : Nat} (hx : 0 < x)
    {c T : Real} (hc : 1 < c) (hT : 0 < T) :
    Summable (scalarPerronErrorTerm chi x c T) :=
  summable_norm_iff.mp (summable_norm_scalarPerronErrorTerm chi hx hc hT)

theorem summable_scalarPerronSeriesTerm
    {N : Nat} (chi : DirichletCharacter Complex N) {x : Nat} (hx : 0 < x)
    {c T : Real} (hc : 1 < c) (hT : 0 < T) :
    Summable (scalarPerronSeriesTerm chi x c T) := by
  have hFunction : scalarPerronSeriesTerm chi x c T = fun n : Nat =>
      scalarPerronErrorTerm chi x c T n + scalarPerronStepTerm chi x n := by
    funext n
    unfold scalarPerronErrorTerm
    ring
  rw [hFunction]
  exact (summable_scalarPerronErrorTerm chi hx hc hT).add
    (summable_scalarPerronStepTerm chi)

theorem norm_explicitFormulaVerticalIntegral_sub_halfSum_le
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    {x : Nat} (hx : 0 < x) {c T : Real} (hc : 1 < c) (hT : 0 < T) :
    norm (explicitFormulaVerticalIntegral chi x c T -
      characterChebyshevHalfSum x chi) <=
      tsum (scalarPerronErrorMajorantTerm chi x c T) := by
  have hErrorNorm := summable_norm_scalarPerronErrorTerm chi hx hc hT
  have hMajorant := summable_scalarPerronErrorMajorantTerm chi hx hc hT
  have hSeries := summable_scalarPerronSeriesTerm chi hx hc hT
  have hStep := summable_scalarPerronStepTerm (x := x) chi
  rw [explicitFormulaVerticalIntegral_eq_tsum_scalarPerronSeriesTerm chi hx hc]
  rw [<- tsum_scalarPerronStepTerm_eq_characterChebyshevHalfSum chi hx]
  rw [<- hSeries.tsum_sub hStep]
  change norm (tsum (scalarPerronErrorTerm chi x c T)) <= _
  exact (norm_tsum_le_tsum_norm hErrorNorm).trans
    (hErrorNorm.tsum_le_tsum
      (fun n => norm_scalarPerronErrorTerm_le_majorant chi hx
        (lt_trans zero_lt_one hc) hT n)
      hMajorant)

theorem norm_explicitFormulaVerticalIntegral_sub_halfSum_le_source
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    {x : Nat} (hx : 0 < x) {c T : Real} (hc : 1 < c) (hT : 0 < T) :
    norm (explicitFormulaVerticalIntegral chi x c T -
      characterChebyshevHalfSum x chi) <=
      tsum (sourcePerronErrorMajorantTerm x c T) := by
  exact (norm_explicitFormulaVerticalIntegral_sub_halfSum_le chi hx hc hT).trans
    ((summable_scalarPerronErrorMajorantTerm chi hx hc hT).tsum_le_tsum
      (fun n => scalarPerronErrorMajorantTerm_le_source chi hx
        (lt_trans zero_lt_one hc) hT n)
      (summable_sourcePerronErrorMajorantTerm hx hc hT))

end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

open Set

namespace BombieriVinogradov.SiegelWalfisz

theorem exists_vonMangoldtLSeriesNormSum_le_div :
    Exists fun C : Real => And (0 < C) (forall c : Real,
      1 < c -> c < 2 ->
        vonMangoldtLSeriesNormSum c <= C / (c - 1)) := by
  have hExist := ShiftZeroBound
  let C0 : Real := hExist.choose
  have hSpec := hExist.choose_spec
  have hC0 : 1 <= C0 := hSpec.1
  have hBound : forall delta : Real, Membership.mem (Ioo 0 1) delta ->
      -(deriv riemannZeta (1 + (delta : Complex)) /
        riemannZeta (1 + (delta : Complex))).re <= 1 / delta + C0 :=
    hSpec.2
  refine Exists.intro (1 + C0) (And.intro (by linarith) ?_)
  intro c hcLower hcUpper
  have hDelta : Membership.mem (Ioo 0 1) (c - 1) := by
    exact And.intro (sub_pos.mpr hcLower) (by linarith)
  have hRaw := hBound (c - 1) hDelta
  have hPoint : (1 : Complex) + ((c - 1 : Real) : Complex) = (c : Complex) := by
    push_cast
    ring
  have hSeriesBound : vonMangoldtLSeriesNormSum c <=
      1 / (c - 1) + C0 := by
    rw [vonMangoldtLSeriesNormSum_eq_neg_logDeriv_re hcLower]
    rw [hPoint] at hRaw
    rw [neg_div, Complex.neg_re]
    exact hRaw
  have hC0Nonneg : 0 <= C0 := le_trans zero_le_one hC0
  have hDenom : Ne (c - 1) 0 := ne_of_gt hDelta.1
  have hMulDiv : C0 / (c - 1) * (c - 1) = C0 := by
    field_simp [hDenom]
  have hC0Div : C0 <= C0 / (c - 1) := by
    nlinarith [hDelta.1, hDelta.2, hC0Nonneg, hMulDiv]
  calc
    vonMangoldtLSeriesNormSum c <= 1 / (c - 1) + C0 := hSeriesBound
    _ <= 1 / (c - 1) + C0 / (c - 1) := add_le_add_right hC0Div _
    _ = (1 + C0) / (c - 1) := by ring

theorem norm_LSeriesTerm_vonMangoldt_antitone
    {c d : Real} (hcd : c <= d) (n : Nat) :
    norm (LSeries.term
      (fun m : Nat => (ArithmeticFunction.vonMangoldt m : Complex))
      (d : Complex) n) <=
    norm (LSeries.term
      (fun m : Nat => (ArithmeticFunction.vonMangoldt m : Complex))
      (c : Complex) n) := by
  rw [norm_LSeriesTerm_vonMangoldt_eq,
    norm_LSeriesTerm_vonMangoldt_eq]
  by_cases hn : n = 0
  case pos =>
    subst n
    simp
  case neg =>
    have hnPos : 0 < n := Nat.pos_of_ne_zero hn
    have hnRealPos : 0 < (n : Real) := by exact_mod_cast hnPos
    have hnOne : (1 : Real) <= (n : Real) := by exact_mod_cast hnPos
    have hPow := Real.rpow_le_rpow_of_exponent_le hnOne hcd
    have hReciprocal : 1 / (n : Real) ^ d <= 1 / (n : Real) ^ c :=
      one_div_le_one_div_of_le (Real.rpow_pos_of_pos hnRealPos c) hPow
    calc
      ArithmeticFunction.vonMangoldt n / (n : Real) ^ d =
          ArithmeticFunction.vonMangoldt n * (1 / (n : Real) ^ d) := by ring
      _ <= ArithmeticFunction.vonMangoldt n * (1 / (n : Real) ^ c) :=
        mul_le_mul_of_nonneg_left hReciprocal
          ArithmeticFunction.vonMangoldt_nonneg
      _ = ArithmeticFunction.vonMangoldt n / (n : Real) ^ c := by ring

theorem vonMangoldtLSeriesNormSum_antitone
    {c d : Real} (hc : 1 < c) (hcd : c <= d) :
    vonMangoldtLSeriesNormSum d <= vonMangoldtLSeriesNormSum c := by
  have hd : 1 < d := lt_of_lt_of_le hc hcd
  have hSummableD := ArithmeticFunction.LSeriesSummable_vonMangoldt
    (s := (d : Complex)) (by simpa using hd)
  have hSummableC := ArithmeticFunction.LSeriesSummable_vonMangoldt
    (s := (c : Complex)) (by simpa using hc)
  unfold vonMangoldtLSeriesNormSum
  exact hSummableD.norm.tsum_le_tsum
    (norm_LSeriesTerm_vonMangoldt_antitone hcd) hSummableC.norm

theorem exists_vonMangoldtLSeriesNormSum_le_div_le_three :
    Exists fun C : Real => And (0 < C) (forall c : Real,
      1 < c -> c <= 3 ->
        vonMangoldtLSeriesNormSum c <= C / (c - 1)) := by
  have hExist := exists_vonMangoldtLSeriesNormSum_le_div
  let C0 : Real := hExist.choose
  have hSpec := hExist.choose_spec
  have hC0 : 0 < C0 := hSpec.1
  have hNarrow := hSpec.2
  refine Exists.intro (4 * C0) (And.intro (by positivity) ?_)
  intro c hc1 hc3
  have hDenomPos : 0 < c - 1 := sub_pos.mpr hc1
  by_cases hc2 : c < 2
  case pos =>
    have hRaw := hNarrow c hc1 hc2
    calc
      vonMangoldtLSeriesNormSum c <= C0 / (c - 1) := hRaw
      _ <= (4 * C0) / (c - 1) := by
        have hUnitNonneg : 0 <= 1 / (c - 1) := by positivity
        calc
          C0 / (c - 1) = C0 * (1 / (c - 1)) := by ring
          _ <= (4 * C0) * (1 / (c - 1)) :=
            mul_le_mul_of_nonneg_right (by nlinarith [hC0]) hUnitNonneg
          _ = (4 * C0) / (c - 1) := by ring
  case neg =>
    have hcTwo : (2 : Real) <= c := le_of_not_gt hc2
    have hMono := vonMangoldtLSeriesNormSum_antitone
      (c := (3 / 2 : Real)) (d := c) (by norm_num) (by linarith)
    have hAt := hNarrow (3 / 2 : Real) (by norm_num) (by norm_num)
    have hFixed : vonMangoldtLSeriesNormSum c <= 2 * C0 := by
      calc
        vonMangoldtLSeriesNormSum c <=
            vonMangoldtLSeriesNormSum (3 / 2 : Real) := hMono
        _ <= C0 / ((3 / 2 : Real) - 1) := hAt
        _ = 2 * C0 := by ring
    have hDenomUpper : c - 1 <= 2 := by linarith
    have hReciprocal : (1 / 2 : Real) <= 1 / (c - 1) :=
      one_div_le_one_div_of_le hDenomPos hDenomUpper
    calc
      vonMangoldtLSeriesNormSum c <= 2 * C0 := hFixed
      _ = (4 * C0) * (1 / 2 : Real) := by ring
      _ <= (4 * C0) * (1 / (c - 1)) :=
        mul_le_mul_of_nonneg_left hReciprocal (by positivity)
      _ = (4 * C0) / (c - 1) := by ring

end BombieriVinogradov.SiegelWalfisz

end
end

section

namespace BombieriVinogradov.SiegelWalfisz

noncomputable def quadraticCharacterFour : DirichletCharacter ℂ 4 :=
  ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)

theorem quadraticCharacterFour_sq : quadraticCharacterFour ^ 2 = 1 :=
  (ZMod.isQuadratic_χ₄.comp (Int.castRingHom ℂ)).sq_eq_one

theorem quadraticCharacterFour_ne_one : quadraticCharacterFour ≠ 1 := by
  rw [quadraticCharacterFour, MulChar.ringHomComp_ne_one_iff Int.cast_injective]
  intro hone
  have hvalue := congrArg (fun chi : MulChar (ZMod 4) ℤ ↦ chi (3 : ℕ)) hone
  have hthree : ZMod.χ₄ (3 : ℕ) = -1 :=
    ZMod.χ₄_nat_three_mod_four (by norm_num)
  rw [hthree] at hvalue
  have hunit : IsUnit (3 : ZMod 4) := by decide
  have honeValue : (1 : MulChar (ZMod 4) ℤ) ((3 : ℕ) : ZMod 4) = 1 :=
    MulChar.one_apply hunit
  rw [honeValue] at hvalue
  norm_num at hvalue

theorem three_le_level_of_ne_one {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchi : chi ≠ 1) : 3 ≤ N := by
  by_contra hN
  have hNle : N ≤ 2 := by omega
  interval_cases N
  · exact (NeZero.ne 0) rfl
  · exact hchi (Subsingleton.elim _ _)
  · apply hchi
    ext x
    have hx : x = 1 := Subsingleton.elim _ _
    subst x
    simp

theorem primitiveCharacter_ne_one {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchi : chi ≠ 1) :
    chi.primitiveCharacter ≠ 1 := by
  intro hprimitive
  apply hchi
  rw [← chi.changeLevel_primitiveCharacter, hprimitive]
  simp

theorem primitiveCharacter_sq_eq_one {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchi : chi ^ 2 = 1) :
    chi.primitiveCharacter ^ 2 = 1 := by
  apply DirichletCharacter.changeLevel_injective chi.conductor_dvd_level
  rw [map_pow, chi.changeLevel_primitiveCharacter, hchi, map_one]

theorem three_le_conductor_of_ne_one {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchi : chi ≠ 1) :
    3 ≤ chi.conductor := by
  let _ : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  exact three_le_level_of_ne_one chi.primitiveCharacter
    (primitiveCharacter_ne_one chi hchi)

theorem quadraticCharacterFour_isPrimitive :
    DirichletCharacter.IsPrimitive quadraticCharacterFour := by
  rw [DirichletCharacter.IsPrimitive]
  have hlower := three_le_conductor_of_ne_one quadraticCharacterFour
    quadraticCharacterFour_ne_one
  have hdvd := quadraticCharacterFour.conductor_dvd_level
  have hupper : quadraticCharacterFour.conductor ≤ 4 :=
    Nat.le_of_dvd (by norm_num) hdvd
  interval_cases quadraticCharacterFour.conductor
  · norm_num at hdvd
  · rfl

theorem crossLevelMul_sq_eq_one {N M : ℕ}
    [NeZero N] [NeZero M] [NeZero (N.lcm M)]
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M)
    (hchiSquare : chi ^ 2 = 1) (hpsiSquare : psi ^ 2 = 1) :
    DirichletCharacter.mul chi psi ^ 2 = 1 := by
  change (DirichletCharacter.changeLevel (Nat.dvd_lcm_left N M) chi *
      DirichletCharacter.changeLevel (Nat.dvd_lcm_right N M) psi) ^ 2 = 1
  rw [mul_pow, ← map_pow, hchiSquare, map_one, ← map_pow, hpsiSquare, map_one, one_mul]

theorem crossLevelMul_ne_one_of_primitive_of_ne {N M : ℕ}
    [NeZero N] [NeZero M] [NeZero (N.lcm M)]
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M)
    (hchi : DirichletCharacter.IsPrimitive chi)
    (hpsi : DirichletCharacter.IsPrimitive psi) (hNM : N ≠ M) :
    DirichletCharacter.mul chi psi ≠ 1 := by
  intro hmul
  change DirichletCharacter.changeLevel (Nat.dvd_lcm_left N M) chi *
      DirichletCharacter.changeLevel (Nat.dvd_lcm_right N M) psi = 1 at hmul
  have hinv : DirichletCharacter.changeLevel (Nat.dvd_lcm_left N M) chi =
      (DirichletCharacter.changeLevel (Nat.dvd_lcm_right N M) psi)⁻¹ :=
    eq_inv_of_mul_eq_one_left hmul
  have hconductor := congrArg DirichletCharacter.conductor hinv
  rw [DirichletCharacter.conductor_changeLevel,
    DirichletCharacter.conductor_inv,
    DirichletCharacter.conductor_changeLevel,
    hchi, hpsi] at hconductor
  exact hNM hconductor

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem quadraticValue_cases {N : ℕ} (χ : DirichletCharacter ℂ N)
    (hχ : χ ^ 2 = 1) (n : ℕ) :
    χ n = 0 ∨ χ n = 1 ∨ χ n = -1 :=
  MulChar.isQuadratic_iff_sq_eq_one.mpr hχ n

end BombieriVinogradov.SiegelWalfisz

end

section

open scoped ComplexOrder

namespace BombieriVinogradov.SiegelWalfisz

noncomputable def characterLevelCorrection {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (s : ℝ) : ℂ :=
  ∏ p ∈ N.primeFactors,
    (1 - chi.primitiveCharacter p * (p : ℂ) ^ (-(s : ℂ)))

theorem characterLevelCorrection_pos {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchiSquare : chi ^ 2 = 1)
    {s : ℝ} (hs : 0 < s) : 0 < characterLevelCorrection chi s := by
  rw [characterLevelCorrection]
  apply Finset.prod_pos
  intro p hp
  have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpgt : (1 : ℝ) < p := by exact_mod_cast hpPrime.one_lt
  have hpnonneg : (0 : ℝ) ≤ p := by positivity
  have hrpowPos : 0 < (p : ℝ) ^ (-s) := Real.rpow_pos_of_pos (by positivity) _
  have hrpowLt : (p : ℝ) ^ (-s) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hpgt (neg_neg_of_pos hs)
  rcases quadraticValue_cases chi.primitiveCharacter
      (primitiveCharacter_sq_eq_one chi hchiSquare) p with hzero | hone | hneg
  · simp [hzero]
  · rw [hone, one_mul, show (-(s : ℂ)) = ((-s : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_natCast p, ← Complex.ofReal_cpow hpnonneg (-s),
      ← Complex.ofReal_one, ← Complex.ofReal_sub]
    exact Complex.zero_lt_real.mpr (sub_pos.mpr hrpowLt)
  · rw [hneg, show (-(s : ℂ)) = ((-s : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_natCast p, ← Complex.ofReal_cpow hpnonneg (-s)]
    convert Complex.zero_lt_real.mpr (show 0 < 1 + (p : ℝ) ^ (-s) by positivity) using 1
    norm_num [Complex.ofReal_add]

theorem LFunction_eq_primitive_mul_correction {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) [NeZero chi.conductor]
    (hchi : chi ≠ 1) {s : ℝ} :
    chi.LFunction s =
      chi.primitiveCharacter.LFunction s * characterLevelCorrection chi s := by
  have hprimitive := primitiveCharacter_ne_one chi hchi
  have hchange := DirichletCharacter.LFunction_changeLevel chi.conductor_dvd_level
    chi.primitiveCharacter (s := (s : ℂ)) (.inl hprimitive)
  rw [chi.changeLevel_primitiveCharacter] at hchange
  exact hchange

end BombieriVinogradov.SiegelWalfisz

end

section

open Filter LSeries Set

namespace BombieriVinogradov.SiegelWalfisz

private theorem quadraticLFunction_im_eq_zero_of_one_lt_bv616 {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchi : chi ^ 2 = 1)
    {x : ℝ} (hx : 1 < x) : (chi.LFunction x).im = 0 := by
  rw [DirichletCharacter.LFunction_eq_LSeries chi (by simpa using hx)]
  rw [LSeries, Complex.im_tsum (chi.LSeriesSummable_of_one_lt_re (by simpa using hx))]
  convert tsum_zero with n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [LSeries.term_of_ne_zero hn]
    rcases quadraticValue_cases chi hchi n with hzero | hone | hneg
    · simp [hzero]
    · rw [hone, ← Complex.ofReal_natCast, ← Complex.ofReal_cpow (Nat.cast_nonneg n)]
      simp
    · rw [hneg, ← Complex.ofReal_natCast, ← Complex.ofReal_cpow (Nat.cast_nonneg n)]
      simp

private theorem quadraticLFunction_im_eq_zero_at_one_bv616 {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchi : chi ^ 2 = 1) (hchi_ne : chi ≠ 1) :
    (chi.LFunction 1).im = 0 := by
  let f : ℝ → ℝ := fun x ↦ (chi.LFunction x).im
  have hLcont : ContinuousAt chi.LFunction (1 : ℂ) :=
    (chi.differentiableAt_LFunction 1 (.inr hchi_ne)).continuousAt
  have hLreal : ContinuousAt (fun x : ℝ ↦ chi.LFunction x) 1 :=
    hLcont.comp_of_eq Complex.continuous_ofReal.continuousAt (by simp)
  have hfcont : ContinuousAt f 1 :=
    Complex.continuous_im.continuousAt.comp' hLreal
  have hlimit : Tendsto f (nhdsWithin 1 (Ioi 1)) (nhds (f 1)) :=
    hfcont.mono_left inf_le_left
  have hzero : Tendsto f (nhdsWithin 1 (Ioi 1)) (nhds 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (quadraticLFunction_im_eq_zero_of_one_lt_bv616 chi hchi hx).symm
  exact tendsto_nhds_unique hlimit hzero

theorem quadraticLFunction_one_re_pos {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchi : chi ^ 2 = 1) (hchi_ne : chi ≠ 1) :
    0 < (chi.LFunction 1).re := by
  have habs : LSeries.abscissaOfAbsConv (chi ·) < ⊤ := by
    rw [DirichletCharacter.absicssaOfAbsConv_eq_one (NeZero.ne N) chi]
    exact EReal.coe_lt_top 1
  have hseries : Tendsto (fun x : ℝ ↦ LSeries (chi ·) x) atTop (nhds 1) := by
    simpa using LSeries.tendsto_atTop habs
  have hL : Tendsto (fun x : ℝ ↦ chi.LFunction x) atTop (nhds 1) := by
    apply hseries.congr'
    filter_upwards [eventually_gt_atTop 1] with x hx
    exact (DirichletCharacter.LFunction_eq_LSeries chi (by simpa using hx)).symm
  have hre : Tendsto (fun x : ℝ ↦ (chi.LFunction x).re) atTop (nhds 1) := by
    convert Complex.continuous_re.continuousAt.tendsto.comp hL using 1 <;>
      simp [Function.comp_def]
  have heventuallyPos : ∀ᶠ x : ℝ in atTop, 0 < (chi.LFunction x).re :=
    hre (Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  obtain ⟨X, hXpos, hXone⟩ :=
    (heventuallyPos.and (eventually_gt_atTop (a := (1 : ℝ)))).exists
  by_contra hnot
  have himOne := quadraticLFunction_im_eq_zero_at_one_bv616 chi hchi hchi_ne
  have hreOne_ne : (chi.LFunction 1).re ≠ 0 := by
    intro hreOne
    apply chi.LFunction_apply_one_ne_zero hchi_ne
    apply Complex.ext
    · simpa using hreOne
    · simpa using himOne
  have hreOne_neg : (chi.LFunction 1).re < 0 :=
    lt_of_le_of_ne (le_of_not_gt hnot) hreOne_ne
  let f : ℝ → ℝ := fun x ↦ (chi.LFunction x).re
  have hfcont : Continuous f := by
    apply continuous_iff_continuousAt.mpr
    intro x
    have hLcont : ContinuousAt chi.LFunction (x : ℂ) :=
      (chi.differentiable_LFunction hchi_ne).continuous.continuousAt
    have hLreal : ContinuousAt (fun y : ℝ ↦ chi.LFunction y) x :=
      hLcont.comp_of_eq Complex.continuous_ofReal.continuousAt rfl
    exact Complex.continuous_re.continuousAt.comp' hLreal
  have hzeroMem : 0 ∈ Icc (f 1) (f X) := ⟨hreOne_neg.le, hXpos.le⟩
  obtain ⟨y, hy, hfy⟩ := intermediate_value_Icc hXone.le hfcont.continuousOn hzeroMem
  have himY : (chi.LFunction y).im = 0 := by
    rcases hy.1.eq_or_lt with rfl | hylt
    · exact himOne
    · exact quadraticLFunction_im_eq_zero_of_one_lt_bv616 chi hchi hylt
  have hLy : chi.LFunction y = 0 := by
    apply Complex.ext
    · simpa [f] using hfy
    · simpa using himY
  exact chi.LFunction_ne_zero_of_one_le_re (.inl hchi_ne) (by simpa using hy.1) hLy

theorem norm_quadraticLFunction_one_eq_re {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchi : chi ^ 2 = 1) (hchi_ne : chi ≠ 1) :
    ‖chi.LFunction 1‖ = (chi.LFunction 1).re := by
  have him := quadraticLFunction_im_eq_zero_at_one_bv616 chi hchi hchi_ne
  have hre := quadraticLFunction_one_re_pos chi hchi hchi_ne
  rw [Complex.norm_def, Complex.normSq_apply, him]
  norm_num [← pow_two, Real.sqrt_sq_eq_abs, abs_of_pos hre]

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

abbrev BoundedDirichletCharacter (N : ℕ) :=
  Σ M : Fin (N + 1), DirichletCharacter ℂ M.val

noncomputable def finiteLevelValue (epsilon : ℝ) {N : ℕ}
    (entry : BoundedDirichletCharacter N) : ℝ := by
  classical
  exact if hlevel : 0 < entry.1.val then
      let _ : NeZero entry.1.val := ⟨hlevel.ne'⟩
      if hquadratic : entry.2 ^ 2 = 1 ∧ Ne entry.2 1 then
        (entry.2.LFunction 1).re * (entry.1.val : ℝ) ^ epsilon
      else
        1
    else
      1

theorem finiteLevelValue_pos (epsilon : ℝ) {N : ℕ}
    (entry : BoundedDirichletCharacter N) :
    0 < finiteLevelValue epsilon entry := by
  classical
  rw [finiteLevelValue]
  split
  · next hlevel =>
      let _ : NeZero entry.1.val := ⟨hlevel.ne'⟩
      split
      · next hquadratic =>
          have hlevelReal : (0 : ℝ) < (entry.1.val : ℕ) := by
            exact_mod_cast hlevel
          exact mul_pos
            (quadraticLFunction_one_re_pos entry.2 hquadratic.1 hquadratic.2)
            (Real.rpow_pos_of_pos hlevelReal epsilon)
      · norm_num
  · norm_num

noncomputable def finiteLevelValues (epsilon : ℝ) (N : ℕ) : Finset ℝ := by
  classical
  exact (Finset.univ : Finset (BoundedDirichletCharacter N)).image
    (finiteLevelValue epsilon)

theorem finiteLevelValues_nonempty (epsilon : ℝ) (N : ℕ) :
    (finiteLevelValues epsilon N).Nonempty := by
  classical
  unfold finiteLevelValues
  exact Finset.image_nonempty.mpr Finset.univ_nonempty

noncomputable def finiteLevelConstant (epsilon : ℝ) (N : ℕ) : ℝ :=
  (finiteLevelValues epsilon N).min' (finiteLevelValues_nonempty epsilon N)

theorem finiteLevelConstant_pos (epsilon : ℝ) (N : ℕ) :
    0 < finiteLevelConstant epsilon N := by
  classical
  have hmem := Finset.min'_mem (finiteLevelValues epsilon N)
    (finiteLevelValues_nonempty epsilon N)
  unfold finiteLevelValues at hmem
  obtain ⟨entry, _, hentry⟩ := Finset.mem_image.mp hmem
  unfold finiteLevelConstant
  unfold finiteLevelValues
  rw [← hentry]
  exact finiteLevelValue_pos epsilon entry

theorem finiteLevelConstant_le_value {epsilon : ℝ} {N M : ℕ}
    [NeZero M] (hMN : M ≤ N) (hM : 3 ≤ M)
    (psi : DirichletCharacter ℂ M) (hpsiSquare : psi ^ 2 = 1)
    (hpsi : Ne psi 1) :
    finiteLevelConstant epsilon N * (M : ℝ) ^ (-epsilon) ≤
      (psi.LFunction 1).re := by
  classical
  let level : Fin (N + 1) := ⟨M, Nat.lt_succ_of_le hMN⟩
  let entry : BoundedDirichletCharacter N := ⟨level, psi⟩
  have hlevel : 0 < level.val := by
    dsimp [level]
    omega
  have hentryValue : finiteLevelValue epsilon entry =
      (psi.LFunction 1).re * (M : ℝ) ^ epsilon := by
    rw [finiteLevelValue]
    simp [entry, level, hlevel, hpsiSquare, hpsi]
  have hentryMem : finiteLevelValue epsilon entry ∈ finiteLevelValues epsilon N := by
    rw [finiteLevelValues]
    exact Finset.mem_image.mpr ⟨entry, Finset.mem_univ _, rfl⟩
  have hminimum : finiteLevelConstant epsilon N ≤ finiteLevelValue epsilon entry := by
    exact Finset.min'_le _ _ hentryMem
  rw [hentryValue] at hminimum
  have hMnonneg : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hMpos : (0 : ℝ) < M := by exact_mod_cast NeZero.pos M
  have hscaled := mul_le_mul_of_nonneg_right hminimum
    (Real.rpow_nonneg hMnonneg (-epsilon))
  calc
    finiteLevelConstant epsilon N * (M : ℝ) ^ (-epsilon) ≤
        ((psi.LFunction 1).re * (M : ℝ) ^ epsilon) *
          (M : ℝ) ^ (-epsilon) := hscaled
    _ = (psi.LFunction 1).re := by
      rw [mul_assoc, ← Real.rpow_add hMpos]
      norm_num

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

noncomputable def siegelLowerEndpoint (epsilon : ℝ) (D : ℕ) : ℝ :=
  max (7 / 8) (1 - epsilon / (2 * ((D : ℝ) + 1)))

theorem seven_eighths_le_siegelLowerEndpoint (epsilon : ℝ) (D : ℕ) :
    7 / 8 ≤ siegelLowerEndpoint epsilon D :=
  le_max_left _ _

theorem siegelLowerEndpoint_lt_one {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (D : ℕ) : siegelLowerEndpoint epsilon D < 1 := by
  apply max_lt
  · norm_num
  · have hdenominator : 0 < 2 * ((D : ℝ) + 1) := by positivity
    have : 0 < epsilon / (2 * ((D : ℝ) + 1)) := div_pos hepsilon hdenominator
    linarith

theorem siegel_exponent_control {epsilon s : ℝ} (hepsilon : 0 < epsilon)
    (D : ℕ) (hs : siegelLowerEndpoint epsilon D ≤ s) :
    (D : ℝ) * (1 - s) + epsilon / 2 ≤ epsilon := by
  have hDnonneg : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  have hDplus : 0 < (D : ℝ) + 1 := by positivity
  have hrange : 1 - epsilon / (2 * ((D : ℝ) + 1)) ≤ s :=
    (le_max_right (7 / 8) (1 - epsilon / (2 * ((D : ℝ) + 1)))).trans hs
  have hgap : 1 - s ≤ epsilon / (2 * ((D : ℝ) + 1)) := by linarith
  have hscaled : (D : ℝ) * (1 - s) ≤
      (D : ℝ) * (epsilon / (2 * ((D : ℝ) + 1))) :=
    mul_le_mul_of_nonneg_left hgap hDnonneg
  have hratio : (D : ℝ) / ((D : ℝ) + 1) ≤ 1 :=
    (div_le_one hDplus).2 (by linarith)
  have habsorb : (D : ℝ) * (epsilon / (2 * ((D : ℝ) + 1))) ≤ epsilon / 2 := by
    calc
      (D : ℝ) * (epsilon / (2 * ((D : ℝ) + 1))) =
          (epsilon / 2) * ((D : ℝ) / ((D : ℝ) + 1)) := by
        field_simp
      _ ≤ epsilon / 2 :=
        mul_le_of_le_one_right (div_nonneg hepsilon.le zero_le_two) hratio
  linarith

end BombieriVinogradov.SiegelWalfisz

end

section

open Metric Set

namespace BombieriVinogradov.SiegelWalfisz

def siegelCauchyCircle : Set ℂ := sphere 2 (3 / 2 : ℝ)

theorem siegelCauchyCircle_norm_sub_one_lower {s : ℂ}
    (hs : s ∈ siegelCauchyCircle) : (1 / 2 : ℝ) ≤ ‖s - 1‖ := by
  have hdist : dist s (2 : ℂ) = (3 / 2 : ℝ) := by
    simpa only [siegelCauchyCircle, mem_sphere] using hs
  have htriangle : dist s (2 : ℂ) ≤ dist s (1 : ℂ) + dist (1 : ℂ) (2 : ℂ) :=
    dist_triangle _ _ _
  rw [hdist] at htriangle
  simp only [Complex.dist_eq] at htriangle
  norm_num at htriangle
  have hone : ‖(1 : ℂ)‖ = 1 := by
    simpa only [Nat.cast_one] using Complex.norm_natCast 1
  try rw [hone] at htriangle
  linarith

theorem siegelCauchyCircle_ne_one {s : ℂ} (hs : s ∈ siegelCauchyCircle) : s ≠ 1 := by
  intro h
  subst s
  have hbound := siegelCauchyCircle_norm_sub_one_lower hs
  norm_num at hbound

end BombieriVinogradov.SiegelWalfisz

end

section

open Metric Set

namespace BombieriVinogradov.SiegelWalfisz

def siegelAnalyticDomain : Set ℂ := ball 2 (7 / 4 : ℝ)

theorem siegelCauchyCircle_subset_analyticDomain :
    siegelCauchyCircle ⊆ siegelAnalyticDomain := by
  intro s hs
  rw [siegelCauchyCircle, mem_sphere] at hs
  rw [siegelAnalyticDomain, mem_ball]
  linarith

theorem siegelAnalyticDomain_re_lower {s : ℂ} (hs : s ∈ siegelAnalyticDomain) :
    (1 / 4 : ℝ) < s.re := by
  have hnorm : ‖s - 2‖ < (7 / 4 : ℝ) := by
    simpa [siegelAnalyticDomain, mem_ball, Complex.dist_eq] using hs
  have hre : |s.re - 2| < (7 / 4 : ℝ) :=
    (Complex.abs_re_le_norm (s - 2)).trans_lt (by simpa using hnorm)
  linarith [neg_abs_le (s.re - 2)]

theorem siegelAnalyticDomain_norm_upper {s : ℂ} (hs : s ∈ siegelAnalyticDomain) :
    ‖s‖ < (15 / 4 : ℝ) := by
  have hdist : dist s (2 : ℂ) < (7 / 4 : ℝ) := by
    simpa only [siegelAnalyticDomain, mem_ball] using hs
  have htriangle : dist s (0 : ℂ) ≤ dist s (2 : ℂ) + dist (2 : ℂ) (0 : ℂ) :=
    dist_triangle _ _ _
  rw [Complex.dist_eq] at hdist
  simp only [Complex.dist_eq] at htriangle
  norm_num at htriangle
  linarith

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

noncomputable def characterLBlock {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (k : ℕ) (s : ℂ) : ℂ :=
  ∑ j : ZMod N, χ j * ((k * N + j.val : ℕ) : ℂ) ^ (-s)

theorem characterLBlock_recenter {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (k : ℕ) (s : ℂ) :
    characterLBlock χ k s =
      ∑ j : ZMod N, χ j *
        (((k * N + j.val : ℕ) : ℂ) ^ (-s) - (((k + 1) * N : ℕ) : ℂ) ^ (-s)) := by
  rw [characterLBlock]
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  rw [χ.sum_eq_zero_of_ne_one hχ, zero_mul, sub_zero]

theorem characterLBlock_differentiableOn {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (k : ℕ) :
    DifferentiableOn ℂ (characterLBlock χ k) siegelAnalyticDomain := by
  have hN : N ≠ 1 := by
    intro h
    subst N
    exact hχ (Subsingleton.elim _ _)
  rw [show characterLBlock χ k = fun s ↦
      ∑ j : ZMod N, χ j *
        (((k * N + j.val : ℕ) : ℂ) ^ (-s) - (((k + 1) * N : ℕ) : ℂ) ^ (-s)) by
    funext s
    exact characterLBlock_recenter χ hχ k s]
  intro s hs
  apply DifferentiableAt.differentiableWithinAt
  apply DifferentiableAt.fun_sum
  intro j hj
  by_cases hj0 : j = 0
  · subst j
    rw [χ.map_zero' hN]
    simp
  · have hx : ((k * N + j.val : ℕ) : ℂ) ≠ 0 := by
      exact Nat.cast_ne_zero.mpr (by
        have hjv : j.val ≠ 0 := (ZMod.val_ne_zero j).mpr hj0
        omega)
    have hy : ((((k + 1) * N : ℕ) : ℂ)) ≠ 0 := by
      exact Nat.cast_ne_zero.mpr (Nat.mul_ne_zero (by omega) (NeZero.ne N))
    exact (((differentiableAt_id.neg).const_cpow (Or.inl hx)).sub
      ((differentiableAt_id.neg).const_cpow (Or.inl hy))).const_mul (χ j)

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

private theorem sum_zmod_val_inv_le_harmonic_bv622 (N : ℕ) [NeZero N] :
    ∑ j : ZMod N, ((j.val : ℝ)⁻¹) ≤ 2 * (harmonic N : ℝ) := by
  calc
    ∑ j : ZMod N, ((j.val : ℝ)⁻¹) = ∑ i : Fin N, ((i.val : ℝ)⁻¹) := by
      symm
      apply Fintype.sum_equiv (ZMod.finEquiv N).toEquiv
      intro i
      change ((i.val : ℝ)⁻¹) = ((((ZMod.finEquiv N) i).val : ℝ)⁻¹)
      congr 2
      obtain _ | n := N
      · exact (NeZero.ne 0 rfl).elim
      · rfl
    _ ≤ ∑ i : Fin N, 2 * ((((i.val + 1 : ℕ) : ℝ))⁻¹) := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases hi0 : i.val = 0
      · simp [hi0]
      · have hipos : (0 : ℝ) < i.val := by exact_mod_cast Nat.pos_of_ne_zero hi0
        have hisucc : (0 : ℝ) < i.val + 1 := by positivity
        rw [← one_div, ← div_eq_mul_inv]
        norm_num only [Nat.cast_add, Nat.cast_one]
        rw [div_le_div_iff₀ hipos hisucc]
        norm_num
        have hiNat : i.val + 1 ≤ 2 * i.val := by omega
        exact_mod_cast hiNat
    _ = 2 * (harmonic N : ℝ) := by
      rw [← Finset.mul_sum]
      congr 1
      rw [Finset.sum_fin_eq_sum_range, harmonic, Rat.cast_sum]
      apply Finset.sum_congr rfl
      intro x hx
      simp [Finset.mem_range.mp hx]

theorem norm_characterLBlock_zero_one_le {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchi : chi ≠ 1) :
    ‖characterLBlock chi 0 1‖ ≤ 2 * (1 + Real.log N) := by
  have hN : N ≠ 1 := by
    intro h
    subst N
    exact hchi (Subsingleton.elim _ _)
  rw [characterLBlock]
  calc
    ‖∑ j : ZMod N, chi j * (((0 * N + j.val : ℕ) : ℂ) ^ (-(1 : ℂ)))‖ ≤
        ∑ j : ZMod N, ‖chi j * (((0 * N + j.val : ℕ) : ℂ) ^ (-(1 : ℂ)))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ j : ZMod N, ((j.val : ℝ)⁻¹) := by
      apply Finset.sum_le_sum
      intro j hj
      by_cases hj0 : j = 0
      · subst j
        rw [chi.map_zero' hN]
        simp
      · have hjv : j.val ≠ 0 := (ZMod.val_ne_zero j).mpr hj0
        rw [norm_mul]
        calc
          ‖chi j‖ * ‖((0 * N + j.val : ℕ) : ℂ) ^ (-(1 : ℂ))‖ ≤
              1 * ‖((j.val : ℕ) : ℂ) ^ (-(1 : ℂ))‖ := by
            norm_num only [Nat.zero_mul, Nat.zero_add]
            exact mul_le_mul_of_nonneg_right (chi.norm_le_one j) (norm_nonneg _)
          _ = ((j.val : ℝ)⁻¹) := by
            rw [one_mul, show (-(1 : ℂ)) = ((-1 : ℝ) : ℂ) by norm_num,
              ← Complex.ofReal_natCast j.val,
              ← Complex.ofReal_cpow (Nat.cast_nonneg j.val) (-1), Complex.norm_real,
              Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg j.val) _),
              Real.rpow_neg_one]
    _ ≤ 2 * (harmonic N : ℝ) := sum_zmod_val_inv_le_harmonic_bv622 N
    _ ≤ 2 * (1 + Real.log N) := by
      gcongr
      exact harmonic_le_one_add_log N

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem norm_cpow_neg_one_sub_le {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    ‖(x : ℂ) ^ ((-1 : ℝ) : ℂ) - (y : ℂ) ^ ((-1 : ℝ) : ℂ)‖ ≤
      (y - x) / x ^ 2 := by
  have hy : 0 < y := hx.trans_le hxy
  rw [← Complex.ofReal_cpow hx.le (-1), ← Complex.ofReal_cpow hy.le (-1),
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    Real.rpow_neg_one, Real.rpow_neg_one]
  have hinv : y⁻¹ ≤ x⁻¹ := (inv_le_inv₀ hy hx).mpr hxy
  rw [abs_of_nonneg (sub_nonneg.mpr hinv)]
  have hid : x⁻¹ - y⁻¹ = (y - x) / (x * y) := by
    field_simp
  rw [hid, pow_two]
  exact div_le_div_of_nonneg_left (sub_nonneg.mpr hxy) (mul_pos hx hx)
    (mul_le_mul_of_nonneg_left hxy hx.le)

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem norm_characterLBlock_one_le {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchi : chi ≠ 1) {k : ℕ} (hk : 1 ≤ k) :
    ‖characterLBlock chi k 1‖ ≤ ((k : ℝ) ^ 2)⁻¹ := by
  have hN : N ≠ 1 := by
    intro h
    subst N
    exact hchi (Subsingleton.elim _ _)
  rw [characterLBlock_recenter chi hchi]
  calc
    ‖∑ j : ZMod N, chi j *
        (((k * N + j.val : ℕ) : ℂ) ^ (-(1 : ℂ)) -
          (((k + 1) * N : ℕ) : ℂ) ^ (-(1 : ℂ)))‖ ≤
        ∑ j : ZMod N, ‖chi j *
          (((k * N + j.val : ℕ) : ℂ) ^ (-(1 : ℂ)) -
            (((k + 1) * N : ℕ) : ℂ) ^ (-(1 : ℂ)))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _j : ZMod N, (((k : ℝ) ^ 2) * (N : ℝ))⁻¹ := by
      apply Finset.sum_le_sum
      intro j hj
      by_cases hj0 : j = 0
      · subst j
        rw [chi.map_zero' hN]
        simp
        positivity
      · have hjv : j.val ≠ 0 := (ZMod.val_ne_zero j).mpr hj0
        have hxNat : 0 < k * N + j.val := by omega
        have hxyNat : k * N + j.val ≤ (k + 1) * N := by
          have hjlt := j.val_lt
          rw [Nat.add_mul, one_mul]
          omega
        have hlenNat : (k + 1) * N - (k * N + j.val) ≤ N := by
          have hjlt := j.val_lt
          rw [Nat.add_mul, one_mul]
          omega
        have hkN : k * N ≤ k * N + j.val := Nat.le_add_right _ _
        have hx : (0 : ℝ) < (k * N + j.val : ℕ) := by exact_mod_cast hxNat
        have hxy : ((k * N + j.val : ℕ) : ℝ) ≤ ((k + 1) * N : ℕ) := by
          exact_mod_cast hxyNat
        have hlen : (((k + 1) * N : ℕ) : ℝ) - (k * N + j.val : ℕ) ≤ N := by
          rw [← Nat.cast_sub hxyNat]
          exact_mod_cast hlenNat
        have hkNreal : ((k * N : ℕ) : ℝ) ≤ (k * N + j.val : ℕ) := by
          exact_mod_cast hkN
        have hkpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
        have hNpos : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
        have hvar := norm_cpow_neg_one_sub_le hx hxy
        rw [norm_mul]
        calc
          ‖chi j‖ * ‖((k * N + j.val : ℕ) : ℂ) ^ (-(1 : ℂ)) -
              (((k + 1) * N : ℕ) : ℂ) ^ (-(1 : ℂ))‖ ≤
              1 * (((((k + 1) * N : ℕ) : ℝ) - (k * N + j.val : ℕ)) /
                ((k * N + j.val : ℕ) : ℝ) ^ 2) := by
            have hvar' :
                ‖((k * N + j.val : ℕ) : ℂ) ^ (-(1 : ℂ)) -
                  (((k + 1) * N : ℕ) : ℂ) ^ (-(1 : ℂ))‖ ≤
                    ((((k + 1) * N : ℕ) : ℝ) - (k * N + j.val : ℕ)) /
                      ((k * N + j.val : ℕ) : ℝ) ^ 2 := by
              rw [show (-(1 : ℂ)) = ((-1 : ℝ) : ℂ) by norm_num]
              simpa only [Complex.ofReal_natCast] using hvar
            exact mul_le_mul (chi.norm_le_one j) hvar'
              (by positivity) (by positivity)
          _ ≤ (N : ℝ) / ((k * N + j.val : ℕ) : ℝ) ^ 2 := by
            simpa using div_le_div_of_nonneg_right hlen (sq_nonneg _)
          _ ≤ (N : ℝ) / ((k * N : ℕ) : ℝ) ^ 2 := by
            have hkNposNat : 0 < k * N := Nat.mul_pos (lt_of_lt_of_le Nat.zero_lt_one hk) (NeZero.pos N)
            have hdenpos : 0 < (((k * N : ℕ) : ℝ) ^ 2) := by
              exact pow_pos (by exact_mod_cast hkNposNat) 2
            have hsq : (((k * N : ℕ) : ℝ) ^ 2) ≤
                (((k * N + j.val : ℕ) : ℝ) ^ 2) := by
              nlinarith [show (0 : ℝ) ≤ (k * N : ℕ) by positivity]
            exact div_le_div_of_nonneg_left hNpos.le hdenpos hsq
          _ = (((k : ℝ) ^ 2) * (N : ℝ))⁻¹ := by
            norm_num [Nat.cast_mul]
            field_simp
    _ = ((k : ℝ) ^ 2)⁻¹ := by
      simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
      have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hk))
      have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
      field_simp

end BombieriVinogradov.SiegelWalfisz

end

section

open Set

namespace BombieriVinogradov.SiegelWalfisz

theorem norm_cpow_neg_sub_le {s : ℂ} {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y)
    (hre : (1 / 4 : ℝ) ≤ s.re) (hs : ‖s‖ ≤ (15 / 4 : ℝ)) :
    ‖(x : ℂ) ^ (-s) - (y : ℂ) ^ (-s)‖ ≤
      (15 / 4 : ℝ) * (y - x) * x ^ (-5 / 4 : ℝ) := by
  have hs0 : -s ≠ 0 := by
    intro h
    have : s = 0 := neg_eq_zero.mp h
    subst s
    norm_num at hre
  have hderiv (t : ℝ) (ht : t ∈ Icc x y) :
      HasDerivWithinAt (fun u : ℝ ↦ (u : ℂ) ^ (-s))
        ((-s) * (t : ℂ) ^ (-s - 1)) (Icc x y) t := by
    exact (hasDerivAt_ofReal_cpow_const (ne_of_gt (lt_of_lt_of_le zero_lt_one (hx.trans ht.1)))
      hs0).hasDerivWithinAt
  have hbound (t : ℝ) (ht : t ∈ Icc x y) :
      ‖(-s) * (t : ℂ) ^ (-s - 1)‖ ≤ (15 / 4 : ℝ) * x ^ (-5 / 4 : ℝ) := by
    have htpos : 0 < t := lt_of_lt_of_le zero_lt_one (hx.trans ht.1)
    have hpow_exp : t ^ (-s.re - 1) ≤ t ^ (-5 / 4 : ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le
      · exact hx.trans ht.1
      · linarith
    have hpow_base : t ^ (-5 / 4 : ℝ) ≤ x ^ (-5 / 4 : ℝ) := by
      exact Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le zero_lt_one hx) ht.1 (by norm_num)
    rw [norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos htpos]
    exact mul_le_mul hs (hpow_exp.trans hpow_base) (Real.rpow_nonneg htpos.le _) (by norm_num)
  have hmv := (convex_Icc x y : Convex ℝ (Icc x y)).norm_image_sub_le_of_norm_hasDerivWithin_le
    hderiv hbound (left_mem_Icc.mpr hxy) (right_mem_Icc.mpr hxy)
  rw [norm_sub_rev, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hxy)] at hmv
  calc
    ‖(x : ℂ) ^ (-s) - (y : ℂ) ^ (-s)‖
        ≤ ((15 / 4 : ℝ) * x ^ (-5 / 4 : ℝ)) * (y - x) := hmv
    _ = (15 / 4 : ℝ) * (y - x) * x ^ (-5 / 4 : ℝ) := by ring

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

noncomputable def characterLBlockMajorant (N k : ℕ) : ℝ :=
  (15 / 4 : ℝ) * (N : ℝ) ^ 2 * ((k + 1 : ℕ) : ℝ) ^ (-5 / 4 : ℝ)

theorem norm_characterLBlock_le {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (k : ℕ) {s : ℂ}
    (hs : s ∈ siegelAnalyticDomain) :
    ‖characterLBlock χ k s‖ ≤ characterLBlockMajorant N k := by
  have hN : N ≠ 1 := by
    intro h
    subst N
    exact hχ (Subsingleton.elim _ _)
  rw [characterLBlock_recenter χ hχ]
  calc
    ‖∑ j : ZMod N, χ j *
        (((k * N + j.val : ℕ) : ℂ) ^ (-s) - (((k + 1) * N : ℕ) : ℂ) ^ (-s))‖
        ≤ ∑ j : ZMod N, ‖χ j *
          (((k * N + j.val : ℕ) : ℂ) ^ (-s) - (((k + 1) * N : ℕ) : ℂ) ^ (-s))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _j : ZMod N,
        (15 / 4 : ℝ) * (N : ℝ) * ((k + 1 : ℕ) : ℝ) ^ (-5 / 4 : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      by_cases hj0 : j = 0
      · subst j
        rw [χ.map_zero' hN]
        simp only [zero_mul, norm_zero]
        positivity
      · have hjv : j.val ≠ 0 := (ZMod.val_ne_zero j).mpr hj0
        have hxoneNat : 1 ≤ k * N + j.val := by omega
        have hxyNat : k * N + j.val ≤ (k + 1) * N := by
          have hjlt := j.val_lt
          rw [Nat.add_mul, one_mul]
          omega
        have hlenNat : (k + 1) * N - (k * N + j.val) ≤ N := by
          have hjlt := j.val_lt
          rw [Nat.add_mul, one_mul]
          omega
        have hxkNat : k + 1 ≤ k * N + j.val := by
          have hNp := NeZero.pos N
          have hk : k ≤ k * N := by
            simpa using Nat.mul_le_mul_left k hNp
          omega
        have hxone : (1 : ℝ) ≤ (k * N + j.val : ℕ) := by exact_mod_cast hxoneNat
        have hxy : ((k * N + j.val : ℕ) : ℝ) ≤ ((k + 1) * N : ℕ) := by
          exact_mod_cast hxyNat
        have hlen : (((k + 1) * N : ℕ) : ℝ) - (k * N + j.val : ℕ) ≤ N := by
          rw [← Nat.cast_sub hxyNat]
          exact_mod_cast hlenNat
        have hxk : (((k + 1 : ℕ) : ℝ)) ≤ (k * N + j.val : ℕ) := by
          exact_mod_cast hxkNat
        have hpow : ((k * N + j.val : ℕ) : ℝ) ^ (-5 / 4 : ℝ) ≤
            ((k + 1 : ℕ) : ℝ) ^ (-5 / 4 : ℝ) := by
          exact Real.rpow_le_rpow_of_nonpos (by positivity) hxk (by norm_num)
        have hvar := norm_cpow_neg_sub_le hxone hxy
          (le_of_lt (siegelAnalyticDomain_re_lower hs))
          (le_of_lt (siegelAnalyticDomain_norm_upper hs))
        rw [norm_mul]
        calc
          ‖χ j‖ * ‖((k * N + j.val : ℕ) : ℂ) ^ (-s) -
              (((k + 1) * N : ℕ) : ℂ) ^ (-s)‖
              ≤ ‖χ j‖ * ((15 / 4 : ℝ) *
                ((((k + 1) * N : ℕ) : ℝ) - (k * N + j.val : ℕ)) *
                  ((k * N + j.val : ℕ) : ℝ) ^ (-5 / 4 : ℝ)) :=
            mul_le_mul_of_nonneg_left hvar (norm_nonneg _)
          _ ≤ 1 * ((15 / 4 : ℝ) *
                ((((k + 1) * N : ℕ) : ℝ) - (k * N + j.val : ℕ)) *
                  ((k * N + j.val : ℕ) : ℝ) ^ (-5 / 4 : ℝ)) := by
            gcongr
            exact χ.norm_le_one j
          _ = (15 / 4 : ℝ) *
                ((((k + 1) * N : ℕ) : ℝ) - (k * N + j.val : ℕ)) *
                  ((k * N + j.val : ℕ) : ℝ) ^ (-5 / 4 : ℝ) := by ring
          _ ≤ (15 / 4 : ℝ) * (N : ℝ) *
                ((k * N + j.val : ℕ) : ℝ) ^ (-5 / 4 : ℝ) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hlen (by norm_num)) (Real.rpow_nonneg (by positivity) _)
          _ ≤ (15 / 4 : ℝ) * (N : ℝ) * ((k + 1 : ℕ) : ℝ) ^ (-5 / 4 : ℝ) := by
            exact mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = characterLBlockMajorant N k := by
      simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
      rw [characterLBlockMajorant]
      ring

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

noncomputable def characterLBlockSeries {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
  ∑' k : ℕ, characterLBlock χ k s

theorem characterLBlockMajorant_summable (N : ℕ) :
    Summable (characterLBlockMajorant N) := by
  have hp : Summable (fun n : ℕ ↦ (n : ℝ) ^ (-5 / 4 : ℝ)) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  have hshift := (summable_nat_add_iff 1).mpr hp
  change Summable (fun k : ℕ ↦
    (15 / 4 : ℝ) * (N : ℝ) ^ 2 * ((k + 1 : ℕ) : ℝ) ^ (-5 / 4 : ℝ))
  exact hshift.mul_left ((15 / 4 : ℝ) * (N : ℝ) ^ 2)

theorem characterLBlockSeries_differentiableOn {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) :
    DifferentiableOn ℂ (characterLBlockSeries χ) siegelAnalyticDomain := by
  change DifferentiableOn ℂ (fun s ↦ ∑' k : ℕ, characterLBlock χ k s)
    siegelAnalyticDomain
  exact Complex.differentiableOn_tsum_of_summable_norm
    (characterLBlockMajorant_summable N)
    (fun k ↦ characterLBlock_differentiableOn χ hχ k)
    (by exact Metric.isOpen_ball)
    (fun k s hs ↦ norm_characterLBlock_le χ hχ k hs)

theorem norm_characterLBlockSeries_le {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {s : ℂ}
    (hs : s ∈ siegelAnalyticDomain) :
    ‖characterLBlockSeries χ s‖ ≤ ∑' k : ℕ, characterLBlockMajorant N k := by
  rw [characterLBlockSeries]
  exact tsum_of_norm_bounded (characterLBlockMajorant_summable N).hasSum
    (fun k ↦ norm_characterLBlock_le χ hχ k hs)

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

noncomputable def characterLTailConstant : ℝ :=
  ∑' k : ℕ, ((((k + 1 : ℕ) : ℝ) ^ 2)⁻¹)

theorem characterLTail_summable :
    Summable (fun k : ℕ ↦ ((((k + 1 : ℕ) : ℝ) ^ 2)⁻¹)) := by
  have hp : Summable (fun k : ℕ ↦ (((k : ℝ) ^ 2)⁻¹)) :=
    Real.summable_nat_pow_inv.mpr (by norm_num)
  exact (summable_nat_add_iff 1).mpr hp

theorem characterLTailConstant_nonneg : 0 ≤ characterLTailConstant := by
  rw [characterLTailConstant]
  exact tsum_nonneg fun k ↦ by positivity

theorem characterLBlock_one_norm_summable {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchi : chi ≠ 1) :
    Summable (fun k : ℕ ↦ ‖characterLBlock chi k 1‖) := by
  have hs : (1 : ℂ) ∈ siegelAnalyticDomain := by
    rw [siegelAnalyticDomain, Metric.mem_ball]
    norm_num [Complex.dist_eq]
  exact (characterLBlockMajorant_summable N).of_nonneg_of_le
    (fun k ↦ norm_nonneg _) fun k ↦ norm_characterLBlock_le chi hchi k hs

set_option maxHeartbeats 4000000 in
theorem characterLBlock_tail_norm_le {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchi : chi ≠ 1) :
    ∑' k : ℕ, ‖characterLBlock chi (k + 1) 1‖ ≤ characterLTailConstant := by
  have hnorm := characterLBlock_one_norm_summable chi hchi
  have htailNorm : Summable (fun k : ℕ ↦ ‖characterLBlock chi (k + 1) 1‖) :=
    (summable_nat_add_iff 1).mpr hnorm
  rw [characterLTailConstant]
  exact htailNorm.tsum_le_tsum
    (fun k ↦ norm_characterLBlock_one_le chi hchi (Nat.le_add_left 1 k))
    characterLTail_summable

theorem norm_characterLBlockSeries_one_le {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchi : chi ≠ 1) :
    ‖characterLBlockSeries chi 1‖ ≤
      2 * (1 + Real.log N) + characterLTailConstant := by
  have hnorm := characterLBlock_one_norm_summable chi hchi
  rw [characterLBlockSeries]
  calc
    ‖∑' k : ℕ, characterLBlock chi k 1‖ ≤
        ∑' k : ℕ, ‖characterLBlock chi k 1‖ :=
      norm_tsum_le_tsum_norm hnorm
    _ = ‖characterLBlock chi 0 1‖ +
        ∑' k : ℕ, ‖characterLBlock chi (k + 1) 1‖ := hnorm.tsum_eq_zero_add
    _ ≤ 2 * (1 + Real.log N) + characterLTailConstant :=
      add_le_add (norm_characterLBlock_zero_one_le chi hchi)
        (characterLBlock_tail_norm_le chi hchi)

end BombieriVinogradov.SiegelWalfisz

end

section

open Complex Filter LSeries Metric Set Topology

namespace BombieriVinogradov.SiegelWalfisz

theorem LFunction_eq_characterLBlockSeries_of_one_lt_re {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {s : ℂ} (hs : 1 < s.re) :
    χ.LFunction s = characterLBlockSeries χ s := by
  have hN : N ≠ 1 := by
    intro h
    subst N
    exact hχ (Subsingleton.elim _ _)
  have hzero : (fun n : ℕ ↦ χ n) 0 = 0 := by
    simpa using χ.map_zero' hN
  have hsum : Summable (fun n : ℕ ↦ χ n * (n : ℂ) ^ (-s)) := by
    rw [← funext (LSeries.term_def₀ hzero s)]
    exact DirichletCharacter.LSeriesSummable_of_one_lt_re χ hs
  have hterm (j : ZMod N) (k : ℕ) :
      χ ((j.val + N * k : ℕ) : ZMod N) * ((j.val + N * k : ℕ) : ℂ) ^ (-s) =
        χ j * ((k * N + j.val : ℕ) : ℂ) ^ (-s) := by
    have hcast : ((j.val + N * k : ℕ) : ZMod N) = j := by
      simp [Nat.cast_add, Nat.cast_mul]
    rw [hcast]
    congr 2
    simp only [Nat.add_comm, Nat.mul_comm]
  have hsub (j : ZMod N) :
      Summable (fun k : ℕ ↦ χ j * ((k * N + j.val : ℕ) : ℂ) ^ (-s)) := by
    have hinj : Function.Injective (fun k : ℕ ↦ j.val + N * k) := by
      intro a b hab
      exact Nat.mul_left_cancel (NeZero.pos N) (Nat.add_left_cancel hab)
    have h := hsum.comp_injective hinj
    exact h.congr (hterm j)
  have hswap := Summable.tsum_finsetSum (s := Finset.univ)
    (fun j _hj ↦ hsub j)
  calc
    χ.LFunction s = LSeries (χ ·) s := DirichletCharacter.LFunction_eq_LSeries χ hs
    _ = ∑' n : ℕ, χ n * (n : ℂ) ^ (-s) := by
      rw [LSeries_def₀ hzero]
      congr 1
      funext n
      rw [Complex.cpow_neg, div_eq_mul_inv]
    _ = ∑ j : ZMod N, ∑' k : ℕ,
        χ ((j.val + N * k : ℕ) : ZMod N) * ((j.val + N * k : ℕ) : ℂ) ^ (-s) :=
      Nat.sumByResidueClasses hsum N
    _ = ∑ j : ZMod N, ∑' k : ℕ,
        χ j * ((k * N + j.val : ℕ) : ℂ) ^ (-s) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact tsum_congr (hterm j)
    _ = ∑' k : ℕ, ∑ j : ZMod N,
        χ j * ((k * N + j.val : ℕ) : ℂ) ^ (-s) := by
      simpa only [Finset.mem_univ, ↓reduceIte] using hswap.symm
    _ = characterLBlockSeries χ s := rfl

theorem LFunction_eq_characterLBlockSeries {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {s : ℂ}
    (hs : s ∈ siegelAnalyticDomain) : χ.LFunction s = characterLBlockSeries χ s := by
  have hL : AnalyticOnNhd ℂ (χ.LFunction) siegelAnalyticDomain :=
    (DirichletCharacter.differentiable_LFunction hχ).differentiableOn.analyticOnNhd
      Metric.isOpen_ball
  have hB : AnalyticOnNhd ℂ (characterLBlockSeries χ) siegelAnalyticDomain :=
    (characterLBlockSeries_differentiableOn χ hχ).analyticOnNhd Metric.isOpen_ball
  have h2 : (2 : ℂ) ∈ siegelAnalyticDomain := by
    rw [siegelAnalyticDomain, mem_ball]
    norm_num
  have heq : χ.LFunction =ᶠ[𝓝 (2 : ℂ)] characterLBlockSeries χ := by
    have hV : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
      (continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds (by norm_num)
    filter_upwards [hV] with z hz
    exact LFunction_eq_characterLBlockSeries_of_one_lt_re χ hχ hz
  exact hL.eqOn_of_preconnected_of_eventuallyEq hB
    (convex_ball (2 : ℂ) (7 / 4 : ℝ)).isPreconnected h2 heq hs

end BombieriVinogradov.SiegelWalfisz

end

section

open Metric Set

namespace BombieriVinogradov.SiegelWalfisz

noncomputable def characterLLogBoundConstant : ℝ :=
  2 + characterLTailConstant

theorem characterLLogBoundConstant_pos : 0 < characterLLogBoundConstant := by
  rw [characterLLogBoundConstant]
  linarith [characterLTailConstant_nonneg]

theorem norm_LFunction_one_le_log {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchi : chi ≠ 1) :
    ‖chi.LFunction 1‖ ≤ characterLLogBoundConstant * (1 + Real.log N) := by
  have hs : (1 : ℂ) ∈ siegelAnalyticDomain := by
    rw [siegelAnalyticDomain, mem_ball]
    norm_num [Complex.dist_eq]
  have hlog : 1 ≤ 1 + Real.log N := by
    have hN : (1 : ℝ) ≤ N := by exact_mod_cast NeZero.pos N
    linarith [Real.log_nonneg hN]
  rw [LFunction_eq_characterLBlockSeries chi hchi hs]
  calc
    ‖characterLBlockSeries chi 1‖ ≤
        2 * (1 + Real.log N) + characterLTailConstant :=
      norm_characterLBlockSeries_one_le chi hchi
    _ ≤ characterLLogBoundConstant * (1 + Real.log N) := by
      rw [characterLLogBoundConstant]
      nlinarith [characterLTailConstant_nonneg]

end BombieriVinogradov.SiegelWalfisz

end

section

open Metric Set

namespace BombieriVinogradov.SiegelWalfisz

noncomputable def characterLAbsoluteMajorant (k : ℕ) : ℝ :=
  (15 / 4 : ℝ) * ((k + 1 : ℕ) : ℝ) ^ (-5 / 4 : ℝ)

noncomputable def characterLBoundConstant : ℝ :=
  1 + ∑' k : ℕ, characterLAbsoluteMajorant k

theorem characterLBoundConstant_pos : 0 < characterLBoundConstant := by
  have hnon : 0 ≤ ∑' k : ℕ, characterLAbsoluteMajorant k := by
    apply tsum_nonneg
    intro k
    rw [characterLAbsoluteMajorant]
    positivity
  rw [characterLBoundConstant]
  linarith

theorem norm_LFunction_le_square_on_analyticDomain {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {s : ℂ}
    (hs : s ∈ siegelAnalyticDomain) :
    ‖χ.LFunction s‖ ≤ characterLBoundConstant * (N : ℝ) ^ 2 := by
  rw [LFunction_eq_characterLBlockSeries χ hχ hs]
  apply (norm_characterLBlockSeries_le χ hχ hs).trans
  calc
    ∑' k : ℕ, characterLBlockMajorant N k =
        (N : ℝ) ^ 2 * ∑' k : ℕ, characterLAbsoluteMajorant k := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro k
      rw [characterLAbsoluteMajorant, characterLBlockMajorant]
      ring
    _ ≤ characterLBoundConstant * (N : ℝ) ^ 2 := by
      rw [mul_comm characterLBoundConstant]
      apply mul_le_mul_of_nonneg_left
      · rw [characterLBoundConstant]
        linarith
      · positivity

theorem norm_LFunction_one_le_square {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) :
    ‖χ.LFunction 1‖ ≤ characterLBoundConstant * (N : ℝ) ^ 2 := by
  apply norm_LFunction_le_square_on_analyticDomain χ hχ
  rw [siegelAnalyticDomain, mem_ball]
  norm_num [Complex.dist_eq]

end BombieriVinogradov.SiegelWalfisz

end

section

open ArithmeticFunction

namespace BombieriVinogradov.SiegelWalfisz

theorem arithmeticFunction_mul_apply_primePower (f g : ArithmeticFunction ℂ)
    {p r : ℕ} (hp : p.Prime) :
    (f * g) (p ^ r) = ∑ i ∈ Finset.range (r + 1), f (p ^ i) * g (p ^ (r - i)) := by
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun x y ↦ f x * g y),
    Nat.sum_divisors_prime_pow hp]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Nat.pow_div (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hp.pos]

noncomputable def characterPairArithmetic {N M : ℕ} (χ : DirichletCharacter ℂ N)
    (ψ : DirichletCharacter ℂ M) : ArithmeticFunction ℂ :=
  toArithmeticFunction fun n ↦ χ n * ψ n

theorem toArithmeticFunction_apply_of_ne_zero (f : ℕ → ℂ) {n : ℕ} (hn : n ≠ 0) :
    toArithmeticFunction f n = f n := by
  simp [toArithmeticFunction, hn]

theorem characterPairArithmetic_isMultiplicative {N M : ℕ}
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M) :
    (characterPairArithmetic χ ψ).IsMultiplicative := by
  refine ArithmeticFunction.IsMultiplicative.iff_ne_zero.mpr ⟨?_, fun {m n} hm hn _ ↦ ?_⟩
  · simp [characterPairArithmetic, toArithmeticFunction]
  · simp [characterPairArithmetic, toArithmeticFunction, hm, hn, map_mul]
    ring

theorem arithmeticZeta_primePower {p i : ℕ} (hp : p.Prime) :
    (ArithmeticFunction.zeta : ArithmeticFunction ℂ) (p ^ i) = 1 := by
  simp [hp.ne_zero]

theorem characterArithmetic_primePower {N : ℕ} (χ : DirichletCharacter ℂ N)
    {p i : ℕ} (hp : p.Prime) :
    toArithmeticFunction (χ ·) (p ^ i) = (χ p) ^ i := by
  rw [← χ.apply_eq_toArithmeticFunction_apply (pow_ne_zero i hp.ne_zero), Nat.cast_pow,
    map_pow]

theorem characterPairArithmetic_primePower {N M : ℕ}
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M)
    {p i : ℕ} (hp : p.Prime) :
    characterPairArithmetic χ ψ (p ^ i) = (χ p * ψ p) ^ i := by
  have hpPow : p ^ i ≠ 0 := pow_ne_zero i hp.ne_zero
  rw [characterPairArithmetic, toArithmeticFunction_apply_of_ne_zero _ hpPow]
  simp only [Nat.cast_pow, map_pow, mul_pow]

noncomputable def siegelProductCoefficients {N M : ℕ} (χ : DirichletCharacter ℂ N)
    (ψ : DirichletCharacter ℂ M) : ArithmeticFunction ℂ :=
  ArithmeticFunction.zeta * toArithmeticFunction (χ ·) * toArithmeticFunction (ψ ·) *
    characterPairArithmetic χ ψ

theorem siegelProductCoefficients_isMultiplicative {N M : ℕ}
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M) :
    (siegelProductCoefficients χ ψ).IsMultiplicative := by
  exact (((isMultiplicative_zeta.natCast.mul χ.isMultiplicative_toArithmeticFunction).mul
    ψ.isMultiplicative_toArithmeticFunction).mul (characterPairArithmetic_isMultiplicative χ ψ))

theorem siegelProductCoefficients_grouped {N M : ℕ}
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M) :
    siegelProductCoefficients χ ψ =
      ((ArithmeticFunction.zeta : ArithmeticFunction ℂ) * toArithmeticFunction (χ ·)) *
        (toArithmeticFunction (ψ ·) * characterPairArithmetic χ ψ) := by
  rw [siegelProductCoefficients, mul_assoc]

theorem siegelProductCoefficients_grouped_swap {N M : ℕ}
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M) :
    siegelProductCoefficients χ ψ =
      ((ArithmeticFunction.zeta : ArithmeticFunction ℂ) * toArithmeticFunction (ψ ·)) *
        (toArithmeticFunction (χ ·) * characterPairArithmetic χ ψ) := by
  rw [siegelProductCoefficients]
  ring

end BombieriVinogradov.SiegelWalfisz

end

section

open ArithmeticFunction
open scoped ComplexOrder

namespace BombieriVinogradov.SiegelWalfisz

noncomputable def localPairCoefficient (a b : ℂ) (r : ℕ) : ℂ :=
  ∑ i ∈ Finset.range (r + 1), a ^ i * b ^ (r - i)

theorem arithmeticFunction_mul_apply_primePower_eq_localPair
    (f g : ArithmeticFunction ℂ) (a b : ℂ) {p r : ℕ} (hp : p.Prime)
    (hf : ∀ i : ℕ, f (p ^ i) = a ^ i) (hg : ∀ i : ℕ, g (p ^ i) = b ^ i) :
    (f * g) (p ^ r) = localPairCoefficient a b r := by
  rw [arithmeticFunction_mul_apply_primePower f g hp, localPairCoefficient]
  apply Finset.sum_congr rfl
  intro i _
  rw [hf, hg]

theorem localPairCoefficient_comm (a b : ℂ) (r : ℕ) :
    localPairCoefficient a b r = localPairCoefficient b a r := by
  simpa [localPairCoefficient] using (Commute.all a b).geom_sum₂_comm (r + 1)

theorem localPairCoefficient_one_left_eq_geom (b : ℂ) (r : ℕ) :
    localPairCoefficient 1 b r = ∑ i ∈ Finset.range (r + 1), b ^ i := by
  calc
    localPairCoefficient 1 b r = localPairCoefficient b 1 r :=
      localPairCoefficient_comm 1 b r
    _ = ∑ i ∈ Finset.range (r + 1), b ^ i := by
      simp [localPairCoefficient]

theorem localPairCoefficient_one_left_nonneg (b : ℂ)
    (hb : b = 0 ∨ b = 1 ∨ b = -1) (r : ℕ) :
    0 ≤ localPairCoefficient 1 b r := by
  rw [localPairCoefficient_one_left_eq_geom]
  rcases hb with rfl | rfl | rfl
  · simp [zero_geom_sum]
  · simp only [one_geom_sum]
    exact_mod_cast Nat.zero_le (r + 1)
  · rw [neg_one_geom_sum]
    split_ifs <;> simp

theorem localPairCoefficient_one_right_nonneg (a : ℂ)
    (ha : a = 0 ∨ a = 1 ∨ a = -1) (r : ℕ) :
    0 ≤ localPairCoefficient a 1 r := by
  rw [localPairCoefficient_comm]
  exact localPairCoefficient_one_left_nonneg a ha r

theorem localPairCoefficient_zero_zero_nonneg (r : ℕ) :
    0 ≤ localPairCoefficient 0 0 r := by
  cases r with
  | zero => simp [localPairCoefficient]
  | succ r =>
      rw [localPairCoefficient]
      apply Finset.sum_nonneg
      intro i hi
      rcases eq_or_ne i 0 with rfl | hi0
      · simp
      · simp [zero_pow hi0]

theorem zeta_mul_character_primePower {N : ℕ} (χ : DirichletCharacter ℂ N)
    {p r : ℕ} (hp : p.Prime) :
    ((ArithmeticFunction.zeta : ArithmeticFunction ℂ) * toArithmeticFunction (χ ·))
        (p ^ r) = localPairCoefficient 1 (χ p) r :=
  arithmeticFunction_mul_apply_primePower_eq_localPair _ _ _ _ hp
    (fun _ ↦ by simpa using arithmeticZeta_primePower hp)
    (fun _ ↦ characterArithmetic_primePower χ hp)

theorem character_mul_pair_primePower {N M : ℕ}
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M)
    {p r : ℕ} (hp : p.Prime) :
    (toArithmeticFunction (χ ·) * characterPairArithmetic χ ψ) (p ^ r) =
      localPairCoefficient (χ p) (χ p * ψ p) r :=
  arithmeticFunction_mul_apply_primePower_eq_localPair _ _ _ _ hp
    (fun _ ↦ characterArithmetic_primePower χ hp)
    (fun _ ↦ characterPairArithmetic_primePower χ ψ hp)

theorem character_right_mul_pair_primePower {N M : ℕ}
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M)
    {p r : ℕ} (hp : p.Prime) :
    (toArithmeticFunction (ψ ·) * characterPairArithmetic χ ψ) (p ^ r) =
      localPairCoefficient (ψ p) (χ p * ψ p) r :=
  arithmeticFunction_mul_apply_primePower_eq_localPair _ _ _ _ hp
    (fun _ ↦ characterArithmetic_primePower ψ hp)
    (fun _ ↦ characterPairArithmetic_primePower χ ψ hp)

end BombieriVinogradov.SiegelWalfisz

end

section

open ArithmeticFunction
open scoped ComplexOrder

namespace BombieriVinogradov.SiegelWalfisz

theorem siegelProductCoefficients_primePower_nonneg {N M : ℕ}
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M)
    (hχ : χ ^ 2 = 1) (hψ : ψ ^ 2 = 1) {p r : ℕ} (hp : p.Prime) :
    0 ≤ siegelProductCoefficients χ ψ (p ^ r) := by
  rcases quadraticValue_cases χ hχ p with hχp | hχp | hχp
  · rw [siegelProductCoefficients_grouped_swap,
      arithmeticFunction_mul_apply_primePower _ _ hp]
    apply Finset.sum_nonneg
    intro i hi
    apply mul_nonneg
    · rw [zeta_mul_character_primePower ψ hp]
      exact localPairCoefficient_one_left_nonneg _ (quadraticValue_cases ψ hψ p) i
    · rw [character_mul_pair_primePower χ ψ hp, hχp, zero_mul]
      exact localPairCoefficient_zero_zero_nonneg (r - i)
  · rw [siegelProductCoefficients_grouped_swap,
      arithmeticFunction_mul_apply_primePower _ _ hp]
    apply Finset.sum_nonneg
    intro i hi
    apply mul_nonneg
    · rw [zeta_mul_character_primePower ψ hp]
      exact localPairCoefficient_one_left_nonneg _ (quadraticValue_cases ψ hψ p) i
    · rw [character_mul_pair_primePower χ ψ hp, hχp, one_mul]
      exact localPairCoefficient_one_left_nonneg _ (quadraticValue_cases ψ hψ p) (r - i)
  · rw [siegelProductCoefficients_grouped,
      arithmeticFunction_mul_apply_primePower _ _ hp]
    apply Finset.sum_nonneg
    intro i hi
    apply mul_nonneg
    · rw [zeta_mul_character_primePower χ hp, hχp]
      exact localPairCoefficient_one_left_nonneg (-1) (Or.inr (Or.inr rfl)) i
    · rw [character_right_mul_pair_primePower χ ψ hp, hχp]
      rcases quadraticValue_cases ψ hψ p with hψp | hψp | hψp
      · rw [hψp]
        norm_num
        exact localPairCoefficient_zero_zero_nonneg (r - i)
      · rw [hψp]
        norm_num
        exact localPairCoefficient_one_left_nonneg (-1) (Or.inr (Or.inr rfl)) (r - i)
      · rw [hψp]
        norm_num
        exact localPairCoefficient_one_right_nonneg (-1) (Or.inr (Or.inr rfl)) (r - i)

end BombieriVinogradov.SiegelWalfisz

end

section

open scoped ComplexOrder

namespace BombieriVinogradov.SiegelWalfisz

theorem siegelProductCoefficients_nonneg {N M : ℕ}
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M)
    (hχ : χ ^ 2 = 1) (hψ : ψ ^ 2 = 1) (n : ℕ) :
    0 ≤ siegelProductCoefficients χ ψ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [ArithmeticFunction.map_zero, le_refl]
  · simpa only [(siegelProductCoefficients_isMultiplicative χ ψ).multiplicative_factorization
      _ hn] using!
      Finset.prod_nonneg fun p hp ↦
        siegelProductCoefficients_primePower_nonneg χ ψ hχ hψ
          (Nat.prime_of_mem_primeFactors hp)

theorem siegelProductCoefficients_one {N M : ℕ}
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M) :
    siegelProductCoefficients χ ψ 1 = 1 :=
  (siegelProductCoefficients_isMultiplicative χ ψ).map_one

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem crossLevelMul_apply_nat {N M : ℕ} (χ : DirichletCharacter ℂ N)
    (ψ : DirichletCharacter ℂ M) (n : ℕ) :
    DirichletCharacter.mul χ ψ n = χ n * ψ n := by
  rw [DirichletCharacter.mul, MulChar.mul_apply]
  by_cases hN : n.Coprime N
  · by_cases hM : n.Coprime M
    · have hLcm : n.Coprime (N.lcm M) :=
        Nat.Coprime.of_dvd_right (Nat.lcm_dvd_mul N M) (hN.mul_right hM)
      have hLcmInt : IsCoprime (n : ℤ) (N.lcm M) :=
        Nat.isCoprime_iff_coprime.mpr hLcm
      have hχEval :
          DirichletCharacter.changeLevel (Nat.dvd_lcm_left N M) χ n = χ n := by
        simpa using DirichletCharacter.changeLevel_eq_cast_of_dvd' χ _ hLcmInt
      have hψEval :
          DirichletCharacter.changeLevel (Nat.dvd_lcm_right N M) ψ n = ψ n := by
        simpa using DirichletCharacter.changeLevel_eq_cast_of_dvd' ψ _ hLcmInt
      rw [hχEval, hψEval]
    · have hLcm : ¬n.Coprime (N.lcm M) := fun h ↦
        hM (Nat.Coprime.of_dvd_right (Nat.dvd_lcm_right N M) h)
      have hLcmInt : ¬IsCoprime (n : ℤ) (N.lcm M) := fun h ↦
        hLcm (Nat.isCoprime_iff_coprime.mp h)
      have hMInt : ¬IsCoprime (n : ℤ) M := fun h ↦
        hM (Nat.isCoprime_iff_coprime.mp h)
      have hLiftZero :
          DirichletCharacter.changeLevel (Nat.dvd_lcm_right N M) ψ n = 0 := by
        simpa using (DirichletCharacter.apply_eq_zero_iff _ _).mpr hLcmInt
      have hZero : ψ n = 0 := by
        simpa using (DirichletCharacter.apply_eq_zero_iff _ _).mpr hMInt
      rw [hLiftZero, hZero, mul_zero, mul_zero]
  · have hLcm : ¬n.Coprime (N.lcm M) := fun h ↦
      hN (Nat.Coprime.of_dvd_right (Nat.dvd_lcm_left N M) h)
    have hLcmInt : ¬IsCoprime (n : ℤ) (N.lcm M) := fun h ↦
      hLcm (Nat.isCoprime_iff_coprime.mp h)
    have hNInt : ¬IsCoprime (n : ℤ) N := fun h ↦
      hN (Nat.isCoprime_iff_coprime.mp h)
    have hLiftZero :
        DirichletCharacter.changeLevel (Nat.dvd_lcm_left N M) χ n = 0 := by
      simpa using (DirichletCharacter.apply_eq_zero_iff _ _).mpr hLcmInt
    have hZero : χ n = 0 := by
      simpa using (DirichletCharacter.apply_eq_zero_iff _ _).mpr hNInt
    rw [hLiftZero, hZero, zero_mul, zero_mul]

end BombieriVinogradov.SiegelWalfisz

end

section

open ArithmeticFunction
open LSeries

namespace BombieriVinogradov.SiegelWalfisz

theorem characterPairArithmetic_eq_crossLevel {N M : ℕ}
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M) :
    characterPairArithmetic χ ψ =
      toArithmeticFunction (DirichletCharacter.mul χ ψ ·) := by
  rw [characterPairArithmetic]
  apply toArithmeticFunction_congr
  intro n _
  exact (crossLevelMul_apply_nat χ ψ n).symm

theorem characterArithmetic_LSeriesSummable {N : ℕ}
    (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (toArithmeticFunction (χ ·)) s := by
  exact (LSeriesSummable_congr s fun hn ↦
    (χ.apply_eq_toArithmeticFunction_apply hn).symm).mpr
      (DirichletCharacter.LSeriesSummable_of_one_lt_re χ hs)

theorem characterPairArithmetic_LSeriesSummable {N M : ℕ}
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M)
    {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (characterPairArithmetic χ ψ) s := by
  rw [characterPairArithmetic_eq_crossLevel]
  exact characterArithmetic_LSeriesSummable (DirichletCharacter.mul χ ψ) hs

theorem siegelProductCoefficients_LSeriesSummable {N M : ℕ}
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M)
    {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (siegelProductCoefficients χ ψ) s := by
  rw [siegelProductCoefficients]
  exact ArithmeticFunction.LSeriesSummable_mul
    (ArithmeticFunction.LSeriesSummable_mul
      (ArithmeticFunction.LSeriesSummable_mul
        (ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hs)
        (characterArithmetic_LSeriesSummable χ hs))
      (characterArithmetic_LSeriesSummable ψ hs))
    (characterPairArithmetic_LSeriesSummable χ ψ hs)

end BombieriVinogradov.SiegelWalfisz

end

section

open ArithmeticFunction
open LSeries

namespace BombieriVinogradov.SiegelWalfisz

theorem characterArithmetic_LSeries_eq_LFunction {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    LSeries (toArithmeticFunction (χ ·)) s = χ.LFunction s := by
  rw [LSeries_congr (fun hn ↦ (χ.apply_eq_toArithmeticFunction_apply hn).symm) s]
  exact (DirichletCharacter.LFunction_eq_LSeries χ hs).symm

theorem characterPairArithmetic_LSeries_eq_LFunction {N M : ℕ} [NeZero N] [NeZero M]
    [NeZero (N.lcm M)]
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M)
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (characterPairArithmetic χ ψ) s =
      (DirichletCharacter.mul χ ψ).LFunction s := by
  rw [characterPairArithmetic_eq_crossLevel]
  exact characterArithmetic_LSeries_eq_LFunction (DirichletCharacter.mul χ ψ) hs

theorem siegelProduct_LSeries_eq {N M : ℕ} [NeZero N] [NeZero M]
    [NeZero (N.lcm M)]
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M)
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (siegelProductCoefficients χ ψ) s =
      riemannZeta s * χ.LFunction s * ψ.LFunction s *
        (DirichletCharacter.mul χ ψ).LFunction s := by
  have hzeta : LSeriesSummable (ArithmeticFunction.zeta : ArithmeticFunction ℂ) s :=
    ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hs
  have hχ := characterArithmetic_LSeriesSummable χ hs
  have hψ := characterArithmetic_LSeriesSummable ψ hs
  have hpair := characterPairArithmetic_LSeriesSummable χ ψ hs
  rw [siegelProductCoefficients,
    ArithmeticFunction.LSeries_mul'
      (ArithmeticFunction.LSeriesSummable_mul
        (ArithmeticFunction.LSeriesSummable_mul hzeta hχ) hψ) hpair,
    ArithmeticFunction.LSeries_mul'
      (ArithmeticFunction.LSeriesSummable_mul hzeta hχ) hψ,
    ArithmeticFunction.LSeries_mul' hzeta hχ,
    characterArithmetic_LSeries_eq_LFunction χ hs,
    characterArithmetic_LSeries_eq_LFunction ψ hs,
    characterPairArithmetic_LSeries_eq_LFunction χ ψ hs]
  simp_rw [← ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs,
    ← ArithmeticFunction.natCoe_apply]

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

noncomputable def siegelLProduct {N M : ℕ} [NeZero N] [NeZero M] [NeZero (N.lcm M)]
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M) (s : ℂ) : ℂ :=
  χ.LFunction s * ψ.LFunction s * (DirichletCharacter.mul χ ψ).LFunction s

noncomputable def siegelProductResidue {N M : ℕ} [NeZero N] [NeZero M]
    [NeZero (N.lcm M)] (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M) : ℂ :=
  χ.LFunction 1 * ψ.LFunction 1 * (DirichletCharacter.mul χ ψ).LFunction 1

theorem siegelLProduct_differentiable {N M : ℕ} [NeZero N] [NeZero M]
    [NeZero (N.lcm M)] (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M)
    (hχ : χ ≠ 1) (hψ : ψ ≠ 1) (hmul : DirichletCharacter.mul χ ψ ≠ 1) :
    Differentiable ℂ (siegelLProduct χ ψ) := by
  exact ((DirichletCharacter.differentiable_LFunction hχ).mul
    (DirichletCharacter.differentiable_LFunction hψ)).mul
      (DirichletCharacter.differentiable_LFunction hmul)

theorem siegelLProduct_one {N M : ℕ} [NeZero N] [NeZero M] [NeZero (N.lcm M)]
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M) :
    siegelLProduct χ ψ 1 = siegelProductResidue χ ψ :=
  rfl

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

noncomputable def siegelResidueBoundConstant : ℝ := characterLBoundConstant ^ 3

theorem siegelResidueBoundConstant_pos : 0 < siegelResidueBoundConstant := by
  rw [siegelResidueBoundConstant]
  exact pow_pos characterLBoundConstant_pos 3

theorem norm_siegelProductResidue_le {N M : ℕ} [NeZero N] [NeZero M]
    [NeZero (N.lcm M)] (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M)
    (hχ : χ ≠ 1) (hψ : ψ ≠ 1) (hmul : DirichletCharacter.mul χ ψ ≠ 1) :
    ‖siegelProductResidue χ ψ‖ ≤
      siegelResidueBoundConstant * ((N : ℝ) * (M : ℝ)) ^ 4 := by
  have hχb := norm_LFunction_one_le_square χ hχ
  have hψb := norm_LFunction_one_le_square ψ hψ
  have hmulb := norm_LFunction_one_le_square (DirichletCharacter.mul χ ψ) hmul
  have hC : 0 ≤ characterLBoundConstant := characterLBoundConstant_pos.le
  have hNMpos : 0 < N * M := Nat.mul_pos (NeZero.pos N) (NeZero.pos M)
  have hlcmNat : N.lcm M ≤ N * M := Nat.le_of_dvd hNMpos (Nat.lcm_dvd_mul N M)
  have hlcm : ((N.lcm M : ℕ) : ℝ) ≤ (N : ℝ) * (M : ℝ) := by
    exact_mod_cast hlcmNat
  have hlcmSq : ((N.lcm M : ℕ) : ℝ) ^ 2 ≤ ((N : ℝ) * (M : ℝ)) ^ 2 := by
    gcongr
  rw [siegelProductResidue, norm_mul, norm_mul]
  calc
    ‖χ.LFunction 1‖ * ‖ψ.LFunction 1‖ * ‖(DirichletCharacter.mul χ ψ).LFunction 1‖
        ≤ (characterLBoundConstant * (N : ℝ) ^ 2) *
            (characterLBoundConstant * (M : ℝ) ^ 2) *
              (characterLBoundConstant * ((N.lcm M : ℕ) : ℝ) ^ 2) := by
      have hχψ : ‖χ.LFunction 1‖ * ‖ψ.LFunction 1‖ ≤
          (characterLBoundConstant * (N : ℝ) ^ 2) *
            (characterLBoundConstant * (M : ℝ) ^ 2) := by
        exact mul_le_mul hχb hψb (norm_nonneg _) (mul_nonneg hC (sq_nonneg _))
      exact mul_le_mul hχψ hmulb (norm_nonneg _) (mul_nonneg
        (mul_nonneg hC (sq_nonneg _)) (mul_nonneg hC (sq_nonneg _)))
    _ = characterLBoundConstant ^ 3 * ((N : ℝ) * (M : ℝ)) ^ 2 *
          ((N.lcm M : ℕ) : ℝ) ^ 2 := by ring
    _ ≤ characterLBoundConstant ^ 3 * ((N : ℝ) * (M : ℝ)) ^ 2 *
          ((N : ℝ) * (M : ℝ)) ^ 2 := by
      exact mul_le_mul_of_nonneg_left hlcmSq
        (mul_nonneg (pow_nonneg hC _) (sq_nonneg _))
    _ = siegelResidueBoundConstant * ((N : ℝ) * (M : ℝ)) ^ 4 := by
      rw [siegelResidueBoundConstant]
      ring

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem norm_siegelLProduct_le {N M : ℕ} [NeZero N] [NeZero M]
    [NeZero (N.lcm M)] (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M)
    (hχ : χ ≠ 1) (hψ : ψ ≠ 1) (hmul : DirichletCharacter.mul χ ψ ≠ 1)
    {s : ℂ} (hs : s ∈ siegelCauchyCircle) :
    ‖siegelLProduct χ ψ s‖ ≤
      siegelResidueBoundConstant * ((N : ℝ) * (M : ℝ)) ^ 4 := by
  have hsDomain := siegelCauchyCircle_subset_analyticDomain hs
  have hχb := norm_LFunction_le_square_on_analyticDomain χ hχ hsDomain
  have hψb := norm_LFunction_le_square_on_analyticDomain ψ hψ hsDomain
  have hmulb := norm_LFunction_le_square_on_analyticDomain
    (DirichletCharacter.mul χ ψ) hmul hsDomain
  have hC : 0 ≤ characterLBoundConstant := characterLBoundConstant_pos.le
  have hNMpos : 0 < N * M := Nat.mul_pos (NeZero.pos N) (NeZero.pos M)
  have hlcmNat : N.lcm M ≤ N * M := Nat.le_of_dvd hNMpos (Nat.lcm_dvd_mul N M)
  have hlcm : ((N.lcm M : ℕ) : ℝ) ≤ (N : ℝ) * (M : ℝ) := by
    exact_mod_cast hlcmNat
  have hlcmSq : ((N.lcm M : ℕ) : ℝ) ^ 2 ≤ ((N : ℝ) * (M : ℝ)) ^ 2 := by
    gcongr
  rw [siegelLProduct, norm_mul, norm_mul]
  calc
    ‖χ.LFunction s‖ * ‖ψ.LFunction s‖ * ‖(DirichletCharacter.mul χ ψ).LFunction s‖
        ≤ (characterLBoundConstant * (N : ℝ) ^ 2) *
            (characterLBoundConstant * (M : ℝ) ^ 2) *
              (characterLBoundConstant * ((N.lcm M : ℕ) : ℝ) ^ 2) := by
      have hχψ : ‖χ.LFunction s‖ * ‖ψ.LFunction s‖ ≤
          (characterLBoundConstant * (N : ℝ) ^ 2) *
            (characterLBoundConstant * (M : ℝ) ^ 2) := by
        exact mul_le_mul hχb hψb (norm_nonneg _) (mul_nonneg hC (sq_nonneg _))
      exact mul_le_mul hχψ hmulb (norm_nonneg _) (mul_nonneg
        (mul_nonneg hC (sq_nonneg _)) (mul_nonneg hC (sq_nonneg _)))
    _ = characterLBoundConstant ^ 3 * ((N : ℝ) * (M : ℝ)) ^ 2 *
          ((N.lcm M : ℕ) : ℝ) ^ 2 := by ring
    _ ≤ characterLBoundConstant ^ 3 * ((N : ℝ) * (M : ℝ)) ^ 2 *
          ((N : ℝ) * (M : ℝ)) ^ 2 := by
      exact mul_le_mul_of_nonneg_left hlcmSq
        (mul_nonneg (pow_nonneg hC _) (sq_nonneg _))
    _ = siegelResidueBoundConstant * ((N : ℝ) * (M : ℝ)) ^ 4 := by
      rw [siegelResidueBoundConstant]
      ring

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem zetaRegularized_differentiable : Differentiable ℂ riemannZeta₀ :=
  differentiable_riemannZeta₀

theorem riemannZeta_eq_pole_add_regularized {s : ℂ} (hs : s ≠ 1) :
    riemannZeta s = (s - 1)⁻¹ + riemannZeta₀ s :=
  riemannZeta_eq_inv_sub_add hs

end BombieriVinogradov.SiegelWalfisz

end

section

open Metric Set

namespace BombieriVinogradov.SiegelWalfisz

theorem exists_zetaRegularized_circle_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ s ∈ siegelCauchyCircle, ‖riemannZeta₀ s‖ ≤ C := by
  obtain ⟨M, hM⟩ := (isCompact_sphere (2 : ℂ) (3 / 2 : ℝ)).bddAbove_image
    zetaRegularized_differentiable.continuous.norm.continuousOn
  refine ⟨max 1 M, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro s hs
  exact (hM (mem_image_of_mem _ hs)).trans (le_max_right _ _)

theorem exists_riemannZeta_circle_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ s ∈ siegelCauchyCircle, ‖riemannZeta s‖ ≤ C := by
  obtain ⟨C, hC, hregular⟩ := exists_zetaRegularized_circle_bound
  refine ⟨2 + C, by linarith, ?_⟩
  intro s hs
  have hdist := siegelCauchyCircle_norm_sub_one_lower hs
  have hnormpos : 0 < ‖s - 1‖ := lt_of_lt_of_le (by norm_num) hdist
  have hinv : ‖(s - 1)⁻¹‖ ≤ 2 := by
    rw [norm_inv]
    have : 1 * ‖s - 1‖⁻¹ ≤ 2 := by
      rw [mul_inv_le_iff₀ hnormpos]
      linarith
    simpa using this
  rw [riemannZeta_eq_pole_add_regularized (siegelCauchyCircle_ne_one hs)]
  exact (norm_add_le _ _).trans ((add_le_add hinv (hregular s hs)).trans_eq (by ring))

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

noncomputable def entireDividedDifference (f : ℂ → ℂ) (c : ℂ) : ℂ → ℂ :=
  Function.update (fun z ↦ (f z - f c) / (z - c)) c (deriv f c)

theorem entireDividedDifference_apply_of_ne (f : ℂ → ℂ) {c z : ℂ} (hz : z ≠ c) :
    entireDividedDifference f c z = (f z - f c) / (z - c) := by
  rw [entireDividedDifference, Function.update_of_ne hz]

theorem entireDividedDifference_differentiableAt_of_ne (f : ℂ → ℂ) {c z : ℂ}
    (hf : Differentiable ℂ f) (hz : z ≠ c) :
    DifferentiableAt ℂ (entireDividedDifference f c) z := by
  apply DifferentiableAt.congr_of_eventuallyEq
  · have hconst : DifferentiableAt ℂ (fun _ : ℂ ↦ f c) z := by fun_prop
    have hden : DifferentiableAt ℂ (fun w : ℂ ↦ w - c) z := by fun_prop
    exact ((hf z).sub hconst).div hden (sub_ne_zero.mpr hz)
  · filter_upwards [eventually_ne_nhds hz] with w hw
    exact entireDividedDifference_apply_of_ne f hw

theorem entireDividedDifference_differentiable (f : ℂ → ℂ) (c : ℂ)
    (hf : Differentiable ℂ f) :
    Differentiable ℂ (entireDividedDifference f c) := by
  intro z
  rcases eq_or_ne z c with rfl | hz
  · refine (Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ ?_).differentiableAt
    · filter_upwards [self_mem_nhdsWithin] with w hw
      exact entireDividedDifference_differentiableAt_of_ne f hf (by simpa using hw)
    · simpa [entireDividedDifference] using (hf z).hasDerivAt.continuousAt_div
  · exact entireDividedDifference_differentiableAt_of_ne f hf hz

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

noncomputable def siegelPoleSubtracted {N M : ℕ} [NeZero N] [NeZero M]
    [NeZero (N.lcm M)] (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M) :
    ℂ → ℂ := fun s ↦
  riemannZeta₀ s * siegelLProduct χ ψ s +
    entireDividedDifference (siegelLProduct χ ψ) 1 s

theorem siegelProduct_sub_pole_entire {N M : ℕ} [NeZero N] [NeZero M]
    [NeZero (N.lcm M)] (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M)
    (hχ : χ ≠ 1) (hψ : ψ ≠ 1) (hmul : DirichletCharacter.mul χ ψ ≠ 1) :
    Differentiable ℂ (siegelPoleSubtracted χ ψ) := by
  exact zetaRegularized_differentiable.mul (siegelLProduct_differentiable χ ψ hχ hψ hmul) |>.add
    (entireDividedDifference_differentiable _ _
      (siegelLProduct_differentiable χ ψ hχ hψ hmul))

theorem siegelPoleSubtracted_apply_of_ne {N M : ℕ} [NeZero N] [NeZero M]
    [NeZero (N.lcm M)] (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M)
    {s : ℂ} (hs : s ≠ 1) :
    siegelPoleSubtracted χ ψ s =
      riemannZeta s * siegelLProduct χ ψ s - siegelProductResidue χ ψ / (s - 1) := by
  rw [siegelPoleSubtracted, entireDividedDifference_apply_of_ne _ hs,
    siegelLProduct_one, riemannZeta_eq_pole_add_regularized hs]
  field_simp [sub_ne_zero.mpr hs]
  ring

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem siegelPoleSubtracted_circle_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ K : ℕ,
      ∀ {N M : ℕ} [NeZero N] [NeZero M] [NeZero (N.lcm M)]
        (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M),
        χ ≠ 1 → ψ ≠ 1 → DirichletCharacter.mul χ ψ ≠ 1 →
          ∀ {s : ℂ}, s ∈ siegelCauchyCircle →
            ‖siegelPoleSubtracted χ ψ s‖ ≤ C * ((N : ℝ) * (M : ℝ)) ^ K := by
  obtain ⟨CriemannZeta, hCriemannZeta, hzeta⟩ := exists_riemannZeta_circle_bound
  refine ⟨(CriemannZeta + 2) * siegelResidueBoundConstant,
    mul_pos (by linarith) siegelResidueBoundConstant_pos, 4, ?_⟩
  intro N M instN instM instLcm χ ψ hχ hψ hmul s hs
  have hL := norm_siegelLProduct_le χ ψ hχ hψ hmul hs
  have hres := norm_siegelProductResidue_le χ ψ hχ hψ hmul
  have hdist := siegelCauchyCircle_norm_sub_one_lower hs
  have hnormpos : 0 < ‖s - 1‖ := lt_of_lt_of_le (by norm_num) hdist
  have hinv : ‖s - 1‖⁻¹ ≤ 2 := by
    have : 1 * ‖s - 1‖⁻¹ ≤ 2 := by
      rw [mul_inv_le_iff₀ hnormpos]
      linarith
    simpa using this
  rw [siegelPoleSubtracted_apply_of_ne χ ψ (siegelCauchyCircle_ne_one hs)]
  calc
    ‖riemannZeta s * siegelLProduct χ ψ s - siegelProductResidue χ ψ / (s - 1)‖
        ≤ ‖riemannZeta s * siegelLProduct χ ψ s‖ +
          ‖siegelProductResidue χ ψ / (s - 1)‖ := norm_sub_le _ _
    _ = ‖riemannZeta s‖ * ‖siegelLProduct χ ψ s‖ +
          ‖siegelProductResidue χ ψ‖ * ‖s - 1‖⁻¹ := by
      rw [norm_mul, norm_div, div_eq_mul_inv]
    _ ≤ CriemannZeta * (siegelResidueBoundConstant * ((N : ℝ) * (M : ℝ)) ^ 4) +
          (siegelResidueBoundConstant * ((N : ℝ) * (M : ℝ)) ^ 4) * 2 := by
      apply add_le_add
      · exact mul_le_mul (hzeta s hs) hL (norm_nonneg _) hCriemannZeta.le
      · exact mul_le_mul hres hinv (inv_nonneg.mpr (norm_nonneg _))
          (mul_nonneg siegelResidueBoundConstant_pos.le (pow_nonneg (by positivity) _))
    _ = ((CriemannZeta + 2) * siegelResidueBoundConstant) * ((N : ℝ) * (M : ℝ)) ^ 4 := by
      ring

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.ComplexAnalysis

noncomputable def taylorCoefficient (f : ℂ → ℂ) (c : ℂ) (n : ℕ) : ℂ :=
  iteratedDeriv n f c / (n.factorial : ℂ)

theorem norm_taylorCoefficient_le {f : ℂ → ℂ} {c : ℂ} {R C : ℝ}
    (n : ℕ) (hR : 0 < R) (hf : Differentiable ℂ f)
    (hC : ∀ z ∈ Metric.sphere c R, ‖f z‖ ≤ C) :
    ‖taylorCoefficient f c n‖ ≤ C / R ^ n := by
  have hderiv := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    n hR hf.diffContOnCl hC
  have hfac : 0 < (n.factorial : ℝ) := by positivity
  rw [taylorCoefficient, norm_div]
  simp only [norm_natCast]
  calc
    ‖iteratedDeriv n f c‖ / n.factorial ≤
        (n.factorial * C / R ^ n) / n.factorial :=
      (div_le_div_iff_of_pos_right hfac).2 hderiv
    _ = C / R ^ n := by
      field_simp [Nat.factorial_ne_zero]

end BombieriVinogradov.ComplexAnalysis

end

section

namespace BombieriVinogradov.SiegelWalfisz

noncomputable def siegelRegularCoefficient {N M : ℕ} [NeZero N] [NeZero M]
    [NeZero (N.lcm M)] (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M)
    (m : ℕ) : ℂ :=
  (-1 : ℂ) ^ m * BombieriVinogradov.ComplexAnalysis.taylorCoefficient
    (siegelPoleSubtracted χ ψ) 2 m

theorem norm_siegelRegularCoefficient {N M : ℕ} [NeZero N] [NeZero M]
    [NeZero (N.lcm M)] (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M)
    (m : ℕ) :
    ‖siegelRegularCoefficient χ ψ m‖ =
      ‖BombieriVinogradov.ComplexAnalysis.taylorCoefficient
        (siegelPoleSubtracted χ ψ) 2 m‖ := by
  rw [siegelRegularCoefficient, norm_mul, norm_pow, norm_neg]
  have hone : ‖(1 : ℂ)‖ = 1 := by
    simpa only [Nat.cast_one] using Complex.norm_natCast 1
  rw [hone, one_pow, one_mul]

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem norm_siegelRegularCoefficient_le_of_circle_bound
    {N M : ℕ} [NeZero N] [NeZero M] [NeZero (N.lcm M)]
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M)
    (hχ : χ ≠ 1) (hψ : ψ ≠ 1) (hmul : DirichletCharacter.mul χ ψ ≠ 1)
    {C : ℝ} {K : ℕ}
    (hcircle : ∀ {s : ℂ}, s ∈ siegelCauchyCircle →
      ‖siegelPoleSubtracted χ ψ s‖ ≤ C * ((N : ℝ) * (M : ℝ)) ^ K)
    (m : ℕ) :
    ‖siegelRegularCoefficient χ ψ m‖ ≤
      C * ((N : ℝ) * (M : ℝ)) ^ K * (2 / 3 : ℝ) ^ m := by
  rw [norm_siegelRegularCoefficient]
  have hcauchy := BombieriVinogradov.ComplexAnalysis.norm_taylorCoefficient_le
    m (by norm_num : (0 : ℝ) < 3 / 2)
    (siegelProduct_sub_pole_entire χ ψ hχ hψ hmul)
    (fun z hz ↦ hcircle hz)
  calc
    ‖BombieriVinogradov.ComplexAnalysis.taylorCoefficient
        (siegelPoleSubtracted χ ψ) 2 m‖
        ≤ (C * ((N : ℝ) * (M : ℝ)) ^ K) / (3 / 2 : ℝ) ^ m := hcauchy
    _ = C * ((N : ℝ) * (M : ℝ)) ^ K * (2 / 3 : ℝ) ^ m := by
      rw [div_eq_mul_inv, ← inv_pow]
      norm_num

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem siegelProduct_coefficient_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ K : ℕ,
      ∀ {N M : ℕ} [NeZero N] [NeZero M] [NeZero (N.lcm M)]
        (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M),
        χ ≠ 1 → ψ ≠ 1 → DirichletCharacter.mul χ ψ ≠ 1 →
          ∀ m : ℕ, ‖siegelRegularCoefficient χ ψ m‖ ≤
            C * ((N : ℝ) * (M : ℝ)) ^ K * (2 / 3 : ℝ) ^ m := by
  obtain ⟨C, hC, K, hcircle⟩ := siegelPoleSubtracted_circle_bound
  refine ⟨C, hC, K, ?_⟩
  intro N M instN instM instLcm χ ψ hχ hψ hmul m
  exact norm_siegelRegularCoefficient_le_of_circle_bound χ ψ hχ hψ hmul
    (hcircle χ ψ hχ hψ hmul) m

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem hasSum_siegelRegularCoefficient {N M : ℕ}
    [NeZero N] [NeZero M] [NeZero (N.lcm M)]
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M)
    (hchi : chi ≠ 1) (hpsi : psi ≠ 1)
    (hmul : DirichletCharacter.mul chi psi ≠ 1) (s : ℂ) :
    HasSum (fun m : ℕ => siegelRegularCoefficient chi psi m * (2 - s) ^ m)
      (siegelPoleSubtracted chi psi s) := by
  have h := Complex.hasSum_taylorSeries_of_entire
    (siegelProduct_sub_pole_entire chi psi hchi hpsi hmul) 2 s
  refine HasSum.congr_fun h (fun m => ?_)
  unfold siegelRegularCoefficient BombieriVinogradov.ComplexAnalysis.taylorCoefficient
  simp only [smul_eq_mul]
  have hpow : (s - 2) ^ m = (-1 : ℂ) ^ m * (2 - s) ^ m := by
    rw [show s - 2 = -(2 - s) by ring, neg_pow]
  rw [hpow]
  field_simp [Nat.factorial_ne_zero]

end BombieriVinogradov.SiegelWalfisz

end

section

open scoped ComplexOrder

namespace BombieriVinogradov.SiegelWalfisz

noncomputable def siegelSourceCoefficient {N M : ℕ}
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M) (m : ℕ) : ℂ :=
  (-1 : ℂ) ^ m * BombieriVinogradov.ComplexAnalysis.taylorCoefficient
    (LSeries (siegelProductCoefficients chi psi)) 2 m

theorem siegelSourceCoefficient_nonneg {N M : ℕ}
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M)
    (hchi : chi ^ 2 = 1) (hpsi : psi ^ 2 = 1) (m : ℕ) :
    0 ≤ siegelSourceCoefficient chi psi m := by
  have hsumm : LSeriesSummable (siegelProductCoefficients chi psi) (3 / 2 : ℂ) :=
    siegelProductCoefficients_LSeriesSummable chi psi (by norm_num)
  have habs : LSeries.abscissaOfAbsConv (siegelProductCoefficients chi psi) < (2 : ℝ) :=
    hsumm.abscissaOfAbsConv_le.trans_lt (by norm_num)
  have hderiv := LSeries.iteratedDeriv_alternating
    (siegelProductCoefficients_nonneg chi psi hchi hpsi) habs m
  have hfactorial : (0 : ℂ) ≤ m.factorial := by positivity
  simpa [siegelSourceCoefficient,
    BombieriVinogradov.ComplexAnalysis.taylorCoefficient, mul_div_assoc] using
      div_nonneg hderiv hfactorial

theorem one_le_siegelSourceCoefficient_zero {N M : ℕ}
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M)
    (hchi : chi ^ 2 = 1) (hpsi : psi ^ 2 = 1) :
    (1 : ℂ) ≤ siegelSourceCoefficient chi psi 0 := by
  rw [siegelSourceCoefficient,
    BombieriVinogradov.ComplexAnalysis.taylorCoefficient]
  simp only [pow_zero, one_mul, iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, div_one]
  rw [LSeries]
  have hsumm : Summable (LSeries.term (siegelProductCoefficients chi psi) 2) :=
    siegelProductCoefficients_LSeriesSummable chi psi (by norm_num)
  calc
    (1 : ℂ) = ∑ n ∈ {1}, LSeries.term (siegelProductCoefficients chi psi) 2 n := by
      simp [LSeries.term_def, siegelProductCoefficients_one]
    _ ≤ ∑' n, LSeries.term (siegelProductCoefficients chi psi) 2 n :=
      hsumm.sum_le_tsum {1} fun n _ =>
        LSeries.term_nonneg (siegelProductCoefficients_nonneg chi psi hchi hpsi n) 2

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem pole_source_coefficient (residue : ℂ) (m : ℕ) :
    (-1 : ℂ) ^ m * BombieriVinogradov.ComplexAnalysis.taylorCoefficient
      (fun s : ℂ => residue / (s - 1)) 2 m = residue := by
  rw [BombieriVinogradov.ComplexAnalysis.taylorCoefficient,
    show (fun s : ℂ => residue / (s - 1)) = fun s : ℂ => residue * (s - 1)⁻¹ by
      funext s
      rw [div_eq_mul_inv],
    iteratedDeriv_const_mul_field]
  simp only [iteratedDeriv_eq_iterate]
  have hinv : deriv^[m] (fun s : ℂ => (s - 1)⁻¹) 2 =
      (-1 : ℂ) ^ m * m.factorial := by
    have h := congrFun (iter_deriv_inv_linear_sub m (1 : ℂ) 1) 2
    norm_num at h
    simpa using h
  rw [hinv]
  field_simp [Nat.factorial_ne_zero]
  have hsign : (((-1 : ℂ) ^ m) ^ 2) = 1 := by
    rw [← pow_mul]
    simp
  rw [hsign, one_mul]

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem siegelSourceCoefficient_eq_regular_add_residue {N M : ℕ}
    [NeZero N] [NeZero M] [NeZero (N.lcm M)]
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M)
    (hchi : chi ≠ 1) (hpsi : psi ≠ 1)
    (hmul : DirichletCharacter.mul chi psi ≠ 1) (m : ℕ) :
    siegelSourceCoefficient chi psi m =
      siegelRegularCoefficient chi psi m + siegelProductResidue chi psi := by
  let halfPlane : Set ℂ := {s | 1 < s.re}
  have hopen : IsOpen halfPlane := isOpen_lt continuous_const Complex.continuous_re
  have htwo : (2 : ℂ) ∈ halfPlane := by norm_num [halfPlane]
  have heq : halfPlane.EqOn (LSeries (siegelProductCoefficients chi psi))
      (fun s => siegelPoleSubtracted chi psi s + siegelProductResidue chi psi / (s - 1)) := by
    intro s hs
    have hsone : s ≠ 1 := by
      intro h
      subst s
      norm_num [halfPlane] at hs
    rw [siegelProduct_LSeries_eq chi psi hs]
    change _ = siegelPoleSubtracted chi psi s + siegelProductResidue chi psi / (s - 1)
    rw [siegelPoleSubtracted_apply_of_ne chi psi hsone]
    rw [siegelLProduct]
    ring
  have hderiv := heq.iteratedDeriv_of_isOpen hopen m htwo
  have hregular : ContDiffAt ℂ m (siegelPoleSubtracted chi psi) 2 :=
    (siegelProduct_sub_pole_entire chi psi hchi hpsi hmul).contDiff.contDiffAt
  have hpole : ContDiffAt ℂ m
      (fun s : ℂ => siegelProductResidue chi psi / (s - 1)) 2 := by
    fun_prop (disch := norm_num)
  change iteratedDeriv m (LSeries (siegelProductCoefficients chi psi)) 2 =
    iteratedDeriv m
      (siegelPoleSubtracted chi psi +
        fun s : ℂ => siegelProductResidue chi psi / (s - 1)) 2 at hderiv
  rw [iteratedDeriv_add hregular hpole] at hderiv
  rw [siegelSourceCoefficient, siegelRegularCoefficient,
    BombieriVinogradov.ComplexAnalysis.taylorCoefficient,
    BombieriVinogradov.ComplexAnalysis.taylorCoefficient, hderiv]
  calc
    (-1 : ℂ) ^ m *
          ((iteratedDeriv m (siegelPoleSubtracted chi psi) 2 +
            iteratedDeriv m (fun s : ℂ => siegelProductResidue chi psi / (s - 1)) 2) /
            (m.factorial : ℂ)) =
        (-1 : ℂ) ^ m *
            (iteratedDeriv m (siegelPoleSubtracted chi psi) 2 / (m.factorial : ℂ)) +
          (-1 : ℂ) ^ m *
            (iteratedDeriv m (fun s : ℂ => siegelProductResidue chi psi / (s - 1)) 2 /
              (m.factorial : ℂ)) := by ring
    _ = (-1 : ℂ) ^ m *
          (iteratedDeriv m (siegelPoleSubtracted chi psi) 2 / (m.factorial : ℂ)) +
        siegelProductResidue chi psi := by
      have hpoleCoefficient := pole_source_coefficient (siegelProductResidue chi psi) m
      rw [BombieriVinogradov.ComplexAnalysis.taylorCoefficient] at hpoleCoefficient
      rw [hpoleCoefficient]

end BombieriVinogradov.SiegelWalfisz

end

section

open scoped ComplexOrder

namespace BombieriVinogradov.SiegelWalfisz

noncomputable def siegelSourcePartialSum {N M : ℕ}
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M)
    (cutoff : ℕ) (t : ℝ) : ℂ :=
  ∑ m ∈ Finset.range cutoff, siegelSourceCoefficient chi psi m * (t : ℂ) ^ m

theorem one_le_siegelSourcePartialSum {N M : ℕ}
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M)
    (hchiSquare : chi ^ 2 = 1) (hpsiSquare : psi ^ 2 = 1)
    {cutoff : ℕ} (hcutoff : 0 < cutoff) {t : ℝ} (ht : 0 ≤ t) :
    (1 : ℂ) ≤ siegelSourcePartialSum chi psi cutoff t := by
  calc
    (1 : ℂ) ≤ siegelSourceCoefficient chi psi 0 :=
      one_le_siegelSourceCoefficient_zero chi psi hchiSquare hpsiSquare
    _ = siegelSourceCoefficient chi psi 0 * (t : ℂ) ^ 0 := by simp
    _ ≤ ∑ m ∈ Finset.range cutoff,
        siegelSourceCoefficient chi psi m * (t : ℂ) ^ m := by
      exact Finset.single_le_sum
        (fun m _ => mul_nonneg
          (siegelSourceCoefficient_nonneg chi psi hchiSquare hpsiSquare m)
          (pow_nonneg (by exact_mod_cast ht) m))
        (Finset.mem_range.mpr hcutoff)

theorem regularPartialSum_eq_source_sub_residue {N M : ℕ}
    [NeZero N] [NeZero M] [NeZero (N.lcm M)]
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M)
    (hchi : chi ≠ 1) (hpsi : psi ≠ 1)
    (hmul : DirichletCharacter.mul chi psi ≠ 1)
    (cutoff : ℕ) (t : ℝ) :
    (∑ m ∈ Finset.range cutoff,
        siegelRegularCoefficient chi psi m * (t : ℂ) ^ m) =
      siegelSourcePartialSum chi psi cutoff t -
        siegelProductResidue chi psi * ∑ m ∈ Finset.range cutoff, (t : ℂ) ^ m := by
  rw [siegelSourcePartialSum]
  simp_rw [siegelSourceCoefficient_eq_regular_add_residue chi psi hchi hpsi hmul]
  simp only [add_mul, Finset.sum_add_distrib, Finset.mul_sum]
  ring

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

noncomputable def regularCoefficientTail
    (a : ℕ → ℂ) (cutoff : ℕ) (t : ℝ) : ℂ :=
  ∑' k : ℕ, a (cutoff + k) * (t : ℂ) ^ (cutoff + k)

theorem norm_regularCoefficientTail_le
    (a : ℕ → ℂ) {A t : ℝ} (cutoff : ℕ)
    (hA : 0 ≤ A) (ht0 : 0 ≤ t) (ht : t ≤ 9 / 8)
    (ha : ∀ m, ‖a m‖ ≤ A * (2 / 3 : ℝ) ^ m) :
    ‖regularCoefficientTail a cutoff t‖ ≤
      4 * A * (3 / 4 : ℝ) ^ cutoff := by
  have hterm (k : ℕ) :
      ‖a (cutoff + k) * (t : ℂ) ^ (cutoff + k)‖ ≤
        A * (3 / 4 : ℝ) ^ (cutoff + k) := by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
    calc
      ‖a (cutoff + k)‖ * t ^ (cutoff + k) ≤
          (A * (2 / 3 : ℝ) ^ (cutoff + k)) * t ^ (cutoff + k) :=
        mul_le_mul_of_nonneg_right (ha _) (pow_nonneg ht0 _)
      _ = A * ((2 / 3 : ℝ) * t) ^ (cutoff + k) := by
        rw [mul_assoc, mul_pow]
      _ ≤ A * (3 / 4 : ℝ) ^ (cutoff + k) := by
        gcongr
        nlinarith
  have hgeom : HasSum (fun k : ℕ => (3 / 4 : ℝ) ^ k) 4 := by
    have h := hasSum_geometric_of_norm_lt_one (ξ := (3 / 4 : ℝ)) (by norm_num)
    norm_num at h
    exact h
  have hmajor : HasSum (fun k : ℕ => A * (3 / 4 : ℝ) ^ (cutoff + k))
      (4 * A * (3 / 4 : ℝ) ^ cutoff) := by
    have h := hgeom.mul_left (A * (3 / 4 : ℝ) ^ cutoff)
    simpa only [pow_add, mul_assoc, mul_comm, mul_left_comm] using h
  exact tsum_of_norm_bounded hmajor hterm

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

noncomputable def siegelProductValue {N M : ℕ}
    [NeZero N] [NeZero M] [NeZero (N.lcm M)]
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M) (s : ℂ) : ℂ :=
  riemannZeta s * siegelLProduct chi psi s

theorem siegelProductValue_eq_regular_add_pole {N M : ℕ}
    [NeZero N] [NeZero M] [NeZero (N.lcm M)]
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M)
    {s : ℂ} (hs : s ≠ 1) :
    siegelProductValue chi psi s =
      siegelPoleSubtracted chi psi s + siegelProductResidue chi psi / (s - 1) := by
  rw [siegelPoleSubtracted_apply_of_ne chi psi hs]
  unfold siegelProductValue
  ring

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem siegelProductValue_decomposition {N M : ℕ}
    [NeZero N] [NeZero M] [NeZero (N.lcm M)]
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M)
    (hchi : chi ≠ 1) (hpsi : psi ≠ 1)
    (hmul : DirichletCharacter.mul chi psi ≠ 1)
    (cutoff : ℕ) {delta : ℝ} (hdelta : 0 < delta) :
    siegelProductValue chi psi (1 - delta) =
      siegelSourcePartialSum chi psi cutoff (1 + delta) +
        regularCoefficientTail (siegelRegularCoefficient chi psi) cutoff (1 + delta) -
          siegelProductResidue chi psi * ((1 + delta : ℝ) : ℂ) ^ cutoff / delta := by
  let s : ℂ := (1 - delta : ℝ)
  let t : ℝ := 1 + delta
  have hs : s ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    dsimp [s] at hre
    norm_num at hre
    linarith
  have hexpansion := hasSum_siegelRegularCoefficient chi psi hchi hpsi hmul s
  have hsplit : siegelPoleSubtracted chi psi s =
      (∑ m ∈ Finset.range cutoff, siegelRegularCoefficient chi psi m * (t : ℂ) ^ m) +
        regularCoefficientTail (siegelRegularCoefficient chi psi) cutoff t := by
    have hsum := hexpansion.summable.sum_add_tsum_nat_add cutoff
    rw [hexpansion.tsum_eq] at hsum
    have hst : (2 - s : ℂ) = t := by
      dsimp [s, t]
      push_cast
      ring
    rw [hst] at hsum
    simpa only [regularCoefficientTail, Nat.add_comm] using hsum.symm
  have hsdef : (1 : ℂ) - delta = s := by
    dsimp [s]
    push_cast
    rfl
  have htdef : 1 + delta = t := rfl
  rw [hsdef, htdef]
  rw [siegelProductValue_eq_regular_add_pole chi psi hs, hsplit]
  rw [regularPartialSum_eq_source_sub_residue chi psi hchi hpsi hmul]
  have ht : (t : ℂ) ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    dsimp [t] at hre
    norm_num at hre
    linarith
  rw [geom_sum_eq ht]
  dsimp [s, t]
  push_cast
  field_simp
  ring

end BombieriVinogradov.SiegelWalfisz

end

section

open scoped ComplexOrder

namespace BombieriVinogradov.SiegelWalfisz

theorem siegelProductValue_re_lower_bound {N M : ℕ}
    [NeZero N] [NeZero M] [NeZero (N.lcm M)]
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M)
    (hchiSquare : chi ^ 2 = 1) (hpsiSquare : psi ^ 2 = 1)
    (hchi : chi ≠ 1) (hpsi : psi ≠ 1)
    (hmul : DirichletCharacter.mul chi psi ≠ 1)
    {A delta : ℝ} (hA : 0 ≤ A) (hdelta : 0 < delta) (hdeltaUpper : delta ≤ 1 / 8)
    {cutoff : ℕ} (hcutoff : 0 < cutoff)
    (hcoeff : ∀ m, ‖siegelRegularCoefficient chi psi m‖ ≤ A * (2 / 3 : ℝ) ^ m) :
    1 - (siegelProductResidue chi psi).re * (1 + delta) ^ cutoff / delta -
        4 * A * (3 / 4 : ℝ) ^ cutoff ≤
      (siegelProductValue chi psi (1 - delta)).re := by
  let partialSum := siegelSourcePartialSum chi psi cutoff (1 + delta)
  let tail := regularCoefficientTail (siegelRegularCoefficient chi psi) cutoff (1 + delta)
  have hpartialComplex : (1 : ℂ) ≤ partialSum :=
    one_le_siegelSourcePartialSum chi psi hchiSquare hpsiSquare hcutoff (by linarith)
  have hpartial : 1 ≤ partialSum.re := (Complex.le_def.mp hpartialComplex).1
  have htailNorm : ‖tail‖ ≤ 4 * A * (3 / 4 : ℝ) ^ cutoff :=
    norm_regularCoefficientTail_le (siegelRegularCoefficient chi psi) cutoff hA
      (by linarith) (by linarith) hcoeff
  have htailRe : -(4 * A * (3 / 4 : ℝ) ^ cutoff) ≤ tail.re := by
    exact (neg_le_neg htailNorm).trans ((abs_le.mp (Complex.abs_re_le_norm tail)).1)
  have hdecomp := congrArg Complex.re
    (siegelProductValue_decomposition chi psi hchi hpsi hmul cutoff hdelta)
  have hpowcast : (((1 + delta : ℝ) : ℂ) ^ cutoff) =
      (((1 + delta) ^ cutoff : ℝ) : ℂ) := by
    norm_cast
  have hbasecast : (1 : ℂ) + delta = ((1 + delta : ℝ) : ℂ) := by
    push_cast
    rfl
  have hpowRe : ((1 + (delta : ℂ)) ^ cutoff).re = (1 + delta) ^ cutoff := by
    rw [hbasecast, hpowcast]
    rfl
  have hpowIm : ((1 + (delta : ℂ)) ^ cutoff).im = 0 := by
    rw [hbasecast, hpowcast]
    rfl
  have hpoleRe :
      (siegelProductResidue chi psi * (((1 + delta : ℝ) : ℂ) ^ cutoff) / delta).re =
        (siegelProductResidue chi psi).re * (1 + delta) ^ cutoff / delta := by
    simp
    rw [hpowRe, hpowIm]
    ring
  rw [Complex.sub_re, Complex.add_re, hpoleRe] at hdecomp
  change (siegelProductValue chi psi (1 - delta)).re =
      partialSum.re + tail.re -
        (siegelProductResidue chi psi).re * (1 + delta) ^ cutoff / delta at hdecomp
  linarith

end BombieriVinogradov.SiegelWalfisz

end

section

open scoped ComplexOrder

open Filter
open Topology

namespace BombieriVinogradov.SiegelWalfisz

theorem siegelProductResidue_nonneg {N M : ℕ}
    [NeZero N] [NeZero M] [NeZero (N.lcm M)]
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M)
    (hchiSquare : chi ^ 2 = 1) (hpsiSquare : psi ^ 2 = 1)
    (hchi : chi ≠ 1) (hpsi : psi ≠ 1)
    (hmul : DirichletCharacter.mul chi psi ≠ 1) :
    0 ≤ siegelProductResidue chi psi := by
  obtain ⟨C, _hC, K, hbound⟩ := siegelProduct_coefficient_bound
  let A : ℝ := C * ((N : ℝ) * (M : ℝ)) ^ K
  have hregular : Tendsto (fun m => siegelRegularCoefficient chi psi m)
      atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun m => norm_nonneg (siegelRegularCoefficient chi psi m))
      (fun m => hbound chi psi hchi hpsi hmul m) ?_
    have hpow := tendsto_pow_atTop_nhds_zero_of_norm_lt_one
      (show ‖(2 / 3 : ℝ)‖ < 1 by norm_num)
    have hconst : Tendsto (fun _ : ℕ => A) atTop (𝓝 A) := tendsto_const_nhds
    have hmulZero := hconst.mul hpow
    simpa [A] using hmulZero
  have hsource : Tendsto (fun m => siegelSourceCoefficient chi psi m)
      atTop (𝓝 (siegelProductResidue chi psi)) := by
    have hseq : (fun m => siegelSourceCoefficient chi psi m) =
        fun m => siegelRegularCoefficient chi psi m + siegelProductResidue chi psi := by
      funext m
      exact siegelSourceCoefficient_eq_regular_add_residue chi psi hchi hpsi hmul m
    rw [hseq]
    simpa using hregular.add_const (siegelProductResidue chi psi)
  exact ge_of_tendsto hsource <| Eventually.of_forall fun m =>
    siegelSourceCoefficient_nonneg chi psi hchiSquare hpsiSquare m

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

noncomputable def siegelTruncationIndex (B Q : ℝ) (K : ℕ) : ℕ :=
  ⌈4 * Real.log (B * Q ^ K)⌉₊ + 1

theorem truncationIndex_lower {B Q : ℝ} {K : ℕ}
    (hB : 1 ≤ B) (hQ : 1 ≤ Q) :
    4 * Real.log (B * Q ^ K) < siegelTruncationIndex B Q K := by
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hQpow : 1 ≤ Q ^ K := one_le_pow₀ hQ
  have hX : 1 ≤ B * Q ^ K :=
    hB.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hQpow hB0)
  have hlog : 0 ≤ 4 * Real.log (B * Q ^ K) :=
    mul_nonneg (by norm_num) (Real.log_nonneg hX)
  unfold siegelTruncationIndex
  rw [Nat.cast_add, Nat.cast_one]
  have hceil := Nat.le_ceil (4 * Real.log (B * Q ^ K))
  exact hceil.trans_lt (lt_add_one _)

theorem truncationIndex_upper {B Q : ℝ} {K : ℕ}
    (hB : 1 ≤ B) (hQ : 1 ≤ Q) :
    (siegelTruncationIndex B Q K : ℝ) <
      4 * Real.log (B * Q ^ K) + 2 := by
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hQpow : 1 ≤ Q ^ K := one_le_pow₀ hQ
  have hX : 1 ≤ B * Q ^ K :=
    hB.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hQpow hB0)
  have hlog : 0 ≤ 4 * Real.log (B * Q ^ K) :=
    mul_nonneg (by norm_num) (Real.log_nonneg hX)
  unfold siegelTruncationIndex
  rw [Nat.cast_add, Nat.cast_one]
  linarith [Nat.ceil_lt_add_one hlog]

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem truncationPoleGrowth {B Q delta : ℝ} {K : ℕ}
    (hB : 1 ≤ B) (hQ : 1 ≤ Q) (hdelta0 : 0 ≤ delta) (hdelta : delta ≤ 1 / 8) :
    (1 + delta) ^ siegelTruncationIndex B Q K ≤
      Real.exp 2 * B * Q ^ ((4 * K : ℝ) * delta) := by
  let cutoff := siegelTruncationIndex B Q K
  let X := B * Q ^ K
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hQ0 : 0 ≤ Q := zero_le_one.trans hQ
  have hQpos : 0 < Q := zero_lt_one.trans_le hQ
  have hXpos : 0 < X := mul_pos (zero_lt_one.trans_le hB) (pow_pos hQpos K)
  have hcutoff := truncationIndex_upper (K := K) hB hQ
  have hmul : (cutoff : ℝ) * delta ≤
      (4 * Real.log X + 2) * delta :=
    mul_le_mul_of_nonneg_right hcutoff.le hdelta0
  have hexponent : (cutoff : ℝ) * delta ≤ 4 * delta * Real.log X + 2 := by
    calc
      (cutoff : ℝ) * delta ≤ (4 * Real.log X + 2) * delta := hmul
      _ ≤ 4 * delta * Real.log X + 2 := by nlinarith
  have hbase : 1 + delta ≤ Real.exp delta := by
    simpa only [add_comm] using Real.add_one_le_exp delta
  have hbase0 : 0 ≤ 1 + delta := by linarith
  have hpow : (1 + delta) ^ cutoff ≤ (Real.exp delta) ^ cutoff := by
    exact pow_le_pow_left₀ hbase0 hbase cutoff
  calc
    (1 + delta) ^ cutoff ≤ (Real.exp delta) ^ cutoff := hpow
    _ = Real.exp ((cutoff : ℝ) * delta) := by
      rw [← Real.exp_nat_mul]
    _ ≤ Real.exp (4 * delta * Real.log X + 2) := Real.exp_le_exp.mpr hexponent
    _ = Real.exp 2 * X ^ (4 * delta) := by
      rw [Real.exp_add, Real.rpow_def_of_pos hXpos]
      have harg : 4 * delta * Real.log X = Real.log X * (4 * delta) := by ring
      rw [harg]
      ring
    _ ≤ Real.exp 2 * B * Q ^ ((4 * K : ℝ) * delta) := by
      have hBrpow : B ^ (4 * delta) ≤ B := by
        simpa only [Real.rpow_one] using
          Real.rpow_le_rpow_of_exponent_le hB (by nlinarith : 4 * delta ≤ 1)
      have hQrpow : (Q ^ K) ^ (4 * delta) = Q ^ ((4 * K : ℝ) * delta) := by
        calc
          (Q ^ K) ^ (4 * delta) = (Q ^ (4 * delta)) ^ K :=
            (Real.rpow_pow_comm hQ0 (4 * delta) K).symm
          _ = Q ^ ((4 * delta) * K) :=
            (Real.rpow_mul_natCast hQ0 (4 * delta) K).symm
          _ = Q ^ ((4 * K : ℝ) * delta) := by
            congr 1
            ring
      dsimp [X]
      rw [Real.mul_rpow hB0 (pow_nonneg hQ0 K), hQrpow]
      have hQnonneg : 0 ≤ Q ^ ((4 * K : ℝ) * delta) := Real.rpow_nonneg hQ0 _
      calc
        Real.exp 2 * (B ^ (4 * delta) * Q ^ ((4 * K : ℝ) * delta)) ≤
            Real.exp 2 * (B * Q ^ ((4 * K : ℝ) * delta)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hBrpow hQnonneg) (Real.exp_nonneg 2)
        _ = Real.exp 2 * B * Q ^ ((4 * K : ℝ) * delta) := by ring

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem truncationTail_lt_half {A B Q : ℝ} {K : ℕ}
    (hA : 0 ≤ A) (hB : 1 ≤ B) (hAB : 8 * A ≤ B) (hQ : 1 ≤ Q) :
    4 * A * Q ^ K * (3 / 4 : ℝ) ^ siegelTruncationIndex B Q K < 1 / 2 := by
  let cutoff := siegelTruncationIndex B Q K
  let X := B * Q ^ K
  have hBpos : 0 < B := zero_lt_one.trans_le hB
  have hQpos : 0 < Q := zero_lt_one.trans_le hQ
  have hQpowpos : 0 < Q ^ K := pow_pos hQpos K
  have hXpos : 0 < X := mul_pos hBpos hQpowpos
  have hbase : Real.log (3 / 4 : ℝ) ≤ -1 / 4 := by
    have h := Real.log_le_sub_one_of_pos (show 0 < (3 / 4 : ℝ) by norm_num)
    norm_num at h ⊢
    exact h
  have hcutoff : 4 * Real.log X < (cutoff : ℝ) := by
    exact truncationIndex_lower hB hQ
  have hcutoff0 : 0 ≤ (cutoff : ℝ) := by positivity
  have hexponent : Real.log (3 / 4 : ℝ) * (cutoff : ℝ) < -Real.log X := by
    calc
      Real.log (3 / 4 : ℝ) * (cutoff : ℝ) ≤
          (-1 / 4 : ℝ) * (cutoff : ℝ) :=
        mul_le_mul_of_nonneg_right hbase hcutoff0
      _ < -Real.log X := by nlinarith
  have hpow : (3 / 4 : ℝ) ^ cutoff < 1 / X := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num)]
    have h := Real.exp_lt_exp.mpr hexponent
    rw [Real.exp_neg, Real.exp_log hXpos] at h
    simpa only [inv_eq_one_div] using h
  rcases hA.eq_or_lt with rfl | hApos
  · norm_num
  · have hpref : 0 < 4 * A * Q ^ K := mul_pos (mul_pos (by norm_num) hApos) hQpowpos
    calc
      4 * A * Q ^ K * (3 / 4 : ℝ) ^ cutoff <
          4 * A * Q ^ K * (1 / X) := mul_lt_mul_of_pos_left hpow hpref
      _ = 4 * A / B := by
        dsimp [X]
        field_simp
      _ ≤ 1 / 2 := by
        rw [div_le_iff₀ hBpos]
        nlinarith

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem siegelTruncation_spec {A B Q delta : ℝ} {K : ℕ}
    (hA : 0 ≤ A) (hB : 1 ≤ B) (hAB : 8 * A ≤ B) (hQ : 1 ≤ Q)
    (hdelta0 : 0 ≤ delta) (hdelta : delta ≤ 1 / 8) :
    4 * A * Q ^ K * (3 / 4 : ℝ) ^ siegelTruncationIndex B Q K < 1 / 2 ∧
      (1 + delta) ^ siegelTruncationIndex B Q K ≤
        Real.exp 2 * B * Q ^ ((4 * K : ℝ) * delta) :=
  ⟨truncationTail_lt_half hA hB hAB hQ,
    truncationPoleGrowth hB hQ hdelta0 hdelta⟩

end BombieriVinogradov.SiegelWalfisz

end

section

open scoped ComplexOrder

namespace BombieriVinogradov.SiegelWalfisz

theorem siegelProduct_pos_of_coefficient_bound {N M : ℕ}
    [NeZero N] [NeZero M] [NeZero (N.lcm M)]
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M)
    (hchiSquare : chi ^ 2 = 1) (hpsiSquare : psi ^ 2 = 1)
    (hchi : chi ≠ 1) (hpsi : psi ≠ 1)
    (hmul : DirichletCharacter.mul chi psi ≠ 1)
    {C B Q delta : ℝ} {K : ℕ}
    (hC : 0 < C) (hB : 1 ≤ B) (hCB : 8 * C ≤ B) (hQ : 1 ≤ Q)
    (hdelta : 0 < delta) (hdeltaUpper : delta ≤ 1 / 8)
    (hcoeff : ∀ m, ‖siegelRegularCoefficient chi psi m‖ ≤
      C * Q ^ K * (2 / 3 : ℝ) ^ m)
    (hsmall : 2 * (Real.exp 2 * B) * (siegelProductResidue chi psi).re *
      Q ^ ((4 * K : ℝ) * delta) < delta) :
    0 < (siegelProductValue chi psi (1 - delta)).re := by
  let cutoff := siegelTruncationIndex B Q K
  have hcutoff : 0 < cutoff := by
    dsimp [cutoff, siegelTruncationIndex]
    omega
  have hresidue := siegelProductResidue_nonneg chi psi hchiSquare hpsiSquare hchi hpsi hmul
  have hresidueRe : 0 ≤ (siegelProductResidue chi psi).re :=
    (Complex.le_def.mp hresidue).1
  have htruncation := siegelTruncation_spec (K := K)
    hC.le hB hCB hQ hdelta.le hdeltaUpper
  have htail : 4 * (C * Q ^ K) * (3 / 4 : ℝ) ^ cutoff < 1 / 2 := by
    simpa only [mul_assoc] using htruncation.1
  have hpoleGrowth : (1 + delta) ^ cutoff ≤
      Real.exp 2 * B * Q ^ ((4 * K : ℝ) * delta) := htruncation.2
  have hpoleNumerator :
      (siegelProductResidue chi psi).re * (1 + delta) ^ cutoff ≤
        (siegelProductResidue chi psi).re *
          (Real.exp 2 * B * Q ^ ((4 * K : ℝ) * delta)) :=
    mul_le_mul_of_nonneg_left hpoleGrowth hresidueRe
  have hpole :
      (siegelProductResidue chi psi).re * (1 + delta) ^ cutoff / delta < 1 / 2 := by
    calc
      (siegelProductResidue chi psi).re * (1 + delta) ^ cutoff / delta ≤
          (siegelProductResidue chi psi).re *
            (Real.exp 2 * B * Q ^ ((4 * K : ℝ) * delta)) / delta :=
        div_le_div_of_nonneg_right hpoleNumerator hdelta.le
      _ < 1 / 2 := by
        rw [div_lt_iff₀ hdelta]
        ring_nf at hsmall ⊢
        linarith
  have hlower := siegelProductValue_re_lower_bound chi psi hchiSquare hpsiSquare
    hchi hpsi hmul (mul_nonneg hC.le (pow_nonneg (zero_le_one.trans hQ) K))
    hdelta hdeltaUpper hcutoff hcoeff
  linarith

end BombieriVinogradov.SiegelWalfisz

end

section

open scoped ComplexOrder

namespace BombieriVinogradov.SiegelWalfisz

theorem siegelProduct_pos :
    ∃ C : ℝ, 0 < C ∧ ∃ D : ℕ,
      ∀ {N M : ℕ} [NeZero N] [NeZero M] [NeZero (N.lcm M)]
        (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M),
        chi ^ 2 = 1 → psi ^ 2 = 1 → chi ≠ 1 → psi ≠ 1 →
          DirichletCharacter.mul chi psi ≠ 1 →
          ∀ s : ℝ, 7 / 8 ≤ s → s < 1 →
            C * ‖siegelProductResidue chi psi‖ <
              (1 - s) * ((N : ℝ) * (M : ℝ)) ^ (-(D : ℝ) * (1 - s)) →
              0 < (siegelProductValue chi psi s).re := by
  obtain ⟨C0, hC0, K, hcoeff⟩ := siegelProduct_coefficient_bound
  let B : ℝ := max 1 (8 * C0)
  have hB : 1 ≤ B := le_max_left _ _
  have hC0B : 8 * C0 ≤ B := le_max_right _ _
  have hBpos : 0 < B := zero_lt_one.trans_le hB
  refine ⟨2 * (Real.exp 2 * B), mul_pos (by norm_num) (mul_pos (Real.exp_pos 2) hBpos),
    4 * K, ?_⟩
  intro N M instN instM instLcm chi psi hchiSquare hpsiSquare hchi hpsi hmul s hsLower hsUpper hsmall
  let Q : ℝ := (N : ℝ) * (M : ℝ)
  let delta : ℝ := 1 - s
  have hdelta : 0 < delta := sub_pos.mpr hsUpper
  have hdeltaUpper : delta ≤ 1 / 8 := by
    dsimp [delta]
    linarith
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast NeZero.pos N
  have hM : (1 : ℝ) ≤ M := by exact_mod_cast NeZero.pos M
  have hQ : 1 ≤ Q := by
    dsimp [Q]
    nlinarith [mul_le_mul hN hM (by norm_num : (0 : ℝ) ≤ 1) (by linarith : (0 : ℝ) ≤ N)]
  have hQpos : 0 < Q := zero_lt_one.trans_le hQ
  have hQ0 : 0 ≤ Q := hQpos.le
  have hresidue := siegelProductResidue_nonneg chi psi hchiSquare hpsiSquare hchi hpsi hmul
  have hresidueParts := Complex.le_def.mp hresidue
  have hnormResidue : ‖siegelProductResidue chi psi‖ =
      (siegelProductResidue chi psi).re := by
    have habs := Complex.abs_re_eq_norm.mpr hresidueParts.2.symm
    rw [abs_of_nonneg hresidueParts.1] at habs
    exact habs.symm
  have hsourceSmall :
      2 * (Real.exp 2 * B) * (siegelProductResidue chi psi).re *
        Q ^ ((4 * K : ℝ) * delta) < delta := by
    have hsmall' : 2 * (Real.exp 2 * B) * (siegelProductResidue chi psi).re <
        delta * Q ^ (-((4 * K : ℝ) * delta)) := by
      simpa [Q, delta, hnormResidue] using hsmall
    have hpowPos : 0 < Q ^ ((4 * K : ℝ) * delta) := Real.rpow_pos_of_pos hQpos _
    calc
      2 * (Real.exp 2 * B) * (siegelProductResidue chi psi).re *
          Q ^ ((4 * K : ℝ) * delta) <
        (delta * Q ^ (-((4 * K : ℝ) * delta))) *
          Q ^ ((4 * K : ℝ) * delta) :=
        mul_lt_mul_of_pos_right hsmall' hpowPos
      _ = delta := by
        rw [Real.rpow_neg hQ0]
        field_simp
  have hpositive := siegelProduct_pos_of_coefficient_bound chi psi hchiSquare hpsiSquare
    hchi hpsi hmul hC0 hB hC0B hQ hdelta hdeltaUpper
    (fun m => by simpa [Q, mul_assoc] using hcoeff chi psi hchi hpsi hmul m) hsourceSmall
  simpa [delta] using hpositive

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

def IsSiegelPositivityPair (C : ℝ) (D : ℕ) : Prop :=
  0 < C ∧
    ∀ {N M : ℕ} [NeZero N] [NeZero M] [NeZero (N.lcm M)]
      (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M),
      chi ^ 2 = 1 → psi ^ 2 = 1 → chi ≠ 1 → psi ≠ 1 →
        DirichletCharacter.mul chi psi ≠ 1 →
        ∀ s : ℝ, 7 / 8 ≤ s → s < 1 →
          C * ‖siegelProductResidue chi psi‖ <
            (1 - s) * ((N : ℝ) * (M : ℝ)) ^ (-(D : ℝ) * (1 - s)) →
            0 < (siegelProductValue chi psi s).re

theorem exists_siegelPositivityPair :
    ∃ C : ℝ, ∃ D : ℕ, IsSiegelPositivityPair C D := by
  obtain ⟨C, hC, D, hpos⟩ := siegelProduct_pos
  exact ⟨C, D, hC, hpos⟩

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem siegelProductResidue_lower_of_nonpos {C : ℝ} {D : ℕ}
    (hpair : IsSiegelPositivityPair C D)
    {N M : ℕ} [NeZero N] [NeZero M] [NeZero (N.lcm M)]
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M)
    (hchiSquare : chi ^ 2 = 1) (hpsiSquare : psi ^ 2 = 1)
    (hchi : chi ≠ 1) (hpsi : psi ≠ 1)
    (hmul : DirichletCharacter.mul chi psi ≠ 1)
    {s : ℝ} (hsLower : 7 / 8 ≤ s) (hsUpper : s < 1)
    (hnonpos : (siegelProductValue chi psi s).re ≤ 0) :
    (1 - s) * ((N : ℝ) * (M : ℝ)) ^ (-(D : ℝ) * (1 - s)) ≤
      C * ‖siegelProductResidue chi psi‖ := by
  apply le_of_not_gt
  intro hsmall
  have hpositive := hpair.2 chi psi hchiSquare hpsiSquare hchi hpsi hmul
    s hsLower hsUpper hsmall
  linarith

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem norm_siegelProductResidue_le_log {N M : ℕ}
    [NeZero N] [NeZero M] [NeZero (N.lcm M)]
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M)
    (hchi : chi ≠ 1) (hmul : DirichletCharacter.mul chi psi ≠ 1) :
    ‖siegelProductResidue chi psi‖ ≤
      characterLLogBoundConstant ^ 2 * (1 + Real.log N) *
        (1 + Real.log (N.lcm M)) * ‖psi.LFunction 1‖ := by
  have hchiBound := norm_LFunction_one_le_log chi hchi
  have hmulBound := norm_LFunction_one_le_log (DirichletCharacter.mul chi psi) hmul
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast NeZero.pos N
  have hlogN : 0 ≤ 1 + Real.log N := by linarith [Real.log_nonneg hN]
  have hfirstUpper : 0 ≤
      (characterLLogBoundConstant * (1 + Real.log N)) * ‖psi.LFunction 1‖ :=
    mul_nonneg (mul_nonneg characterLLogBoundConstant_pos.le hlogN) (norm_nonneg _)
  rw [siegelProductResidue, norm_mul, norm_mul]
  calc
    ‖chi.LFunction 1‖ * ‖psi.LFunction 1‖ *
        ‖(DirichletCharacter.mul chi psi).LFunction 1‖ ≤
      (characterLLogBoundConstant * (1 + Real.log N)) *
        ‖psi.LFunction 1‖ *
          (characterLLogBoundConstant * (1 + Real.log (N.lcm M))) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_right hchiBound (norm_nonneg _)) hmulBound
        (norm_nonneg _) hfirstUpper
    _ = characterLLogBoundConstant ^ 2 * (1 + Real.log N) *
        (1 + Real.log (N.lcm M)) * ‖psi.LFunction 1‖ := by ring

theorem targetLValue_transfer {C : ℝ} {D : ℕ}
    (hpair : IsSiegelPositivityPair C D)
    {N M : ℕ} [NeZero N] [NeZero M] [NeZero (N.lcm M)]
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M)
    (hchiSquare : chi ^ 2 = 1) (hpsiSquare : psi ^ 2 = 1)
    (hchi : chi ≠ 1) (hpsi : psi ≠ 1)
    (hmul : DirichletCharacter.mul chi psi ≠ 1)
    {s : ℝ} (hsLower : 7 / 8 ≤ s) (hsUpper : s < 1)
    (hnonpos : (siegelProductValue chi psi s).re ≤ 0) :
    (1 - s) * ((N : ℝ) * (M : ℝ)) ^ (-(D : ℝ) * (1 - s)) ≤
      C * (characterLLogBoundConstant ^ 2 * (1 + Real.log N) *
        (1 + Real.log (N.lcm M)) * ‖psi.LFunction 1‖) := by
  exact (siegelProductResidue_lower_of_nonpos hpair chi psi hchiSquare hpsiSquare
    hchi hpsi hmul hsLower hsUpper hnonpos).trans
      (mul_le_mul_of_nonneg_left (norm_siegelProductResidue_le_log chi psi hchi hmul)
        hpair.1.le)

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

noncomputable def siegelLargeLevelDenominator
    (C : ℝ) (N : ℕ) (delta : ℝ) : ℝ :=
  C * characterLLogBoundConstant ^ 2 * (1 + Real.log N) * (1 + delta⁻¹)

theorem siegelLargeLevelDenominator_pos {C delta : ℝ} {N : ℕ}
    (hC : 0 < C) (hN : 0 < N) (hdelta : 0 < delta) :
    0 < siegelLargeLevelDenominator C N delta := by
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog : 0 < 1 + Real.log N := by
    linarith [Real.log_nonneg hNreal]
  have hinverse : 0 < 1 + delta⁻¹ := by
    have : 0 < delta⁻¹ := inv_pos.mpr hdelta
    linarith
  unfold siegelLargeLevelDenominator
  exact mul_pos (mul_pos (mul_pos hC (pow_pos characterLLogBoundConstant_pos 2)) hlog)
    hinverse

noncomputable def siegelLargeLevelConstant
    (C epsilon s : ℝ) (N : ℕ) : ℝ :=
  ((1 - s) / siegelLargeLevelDenominator C N (epsilon / 2)) *
    (N : ℝ) ^ (-epsilon)

theorem siegelLargeLevelConstant_pos {C epsilon s : ℝ} {N : ℕ}
    (hC : 0 < C) (hepsilon : 0 < epsilon) (hN : 0 < N) (hs : s < 1) :
    0 < siegelLargeLevelConstant C epsilon s N := by
  have hdenominator := siegelLargeLevelDenominator_pos hC hN
    (div_pos hepsilon zero_lt_two)
  unfold siegelLargeLevelConstant
  exact mul_pos (div_pos (sub_pos.mpr hs) hdenominator)
    (Real.rpow_pos_of_pos (by exact_mod_cast hN) (-epsilon))

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem one_add_log_le_rpow_mul {x delta : ℝ}
    (hx : 1 ≤ x) (hdelta : 0 < delta) :
    1 + Real.log x ≤ (1 + delta⁻¹) * x ^ delta := by
  have hpow : 1 ≤ x ^ delta := by
    simpa using Real.rpow_le_rpow zero_le_one hx hdelta.le
  have hlog := Real.log_le_rpow_div (zero_le_one.trans hx) hdelta
  calc
    1 + Real.log x ≤ x ^ delta + x ^ delta / delta := add_le_add hpow hlog
    _ = (1 + delta⁻¹) * x ^ delta := by
      rw [div_eq_mul_inv]
      ring

theorem one_add_log_lcm_le_rpow_mul {N M : ℕ}
    (hN : 0 < N) (hM : 0 < M) {delta : ℝ} (hdelta : 0 < delta) :
    1 + Real.log (N.lcm M) ≤
      (1 + delta⁻¹) * ((N : ℝ) * (M : ℝ)) ^ delta := by
  have hmul : 0 < N * M := Nat.mul_pos hN hM
  have hlcmNat : N.lcm M ≤ N * M :=
    Nat.le_of_dvd hmul (Nat.lcm_dvd_mul N M)
  have hlcm : (0 : ℝ) < N.lcm M := by
    exact_mod_cast Nat.pos_of_ne_zero (Nat.lcm_ne_zero hN.ne' hM.ne')
  have hlcmMul : (N.lcm M : ℝ) ≤ (N * M : ℕ) := by
    exact_mod_cast hlcmNat
  have hproduct : (1 : ℝ) ≤ (N * M : ℕ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hmul.ne'
  calc
    1 + Real.log (N.lcm M) ≤ 1 + Real.log (N * M : ℕ) := by
      simpa [add_comm] using add_le_add_left (Real.log_le_log hlcm hlcmMul) 1
    _ ≤ (1 + delta⁻¹) * (N * M : ℕ) ^ delta :=
      one_add_log_le_rpow_mul hproduct hdelta
    _ = (1 + delta⁻¹) * ((N : ℝ) * (M : ℝ)) ^ delta := by
      norm_num

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem weighted_rpow_transfer {prefactor bound base exponent delta epsilon value : ℝ}
    (hprefactor : 0 < prefactor) (hbound : 0 < bound) (hbase : 1 ≤ base)
    (hsum : exponent + delta ≤ epsilon)
    (hweighted : prefactor * base ^ (-exponent) ≤
      bound * base ^ delta * value) :
    (prefactor / bound) * base ^ (-epsilon) ≤ value := by
  have hbasePos : 0 < base := zero_lt_one.trans_le hbase
  have hpowerDelta : 0 < base ^ delta := Real.rpow_pos_of_pos hbasePos delta
  have hdenominator : 0 < bound * base ^ delta := mul_pos hbound hpowerDelta
  have hdivided :
      (prefactor * base ^ (-exponent)) / (bound * base ^ delta) ≤ value := by
    rw [div_le_iff₀ hdenominator]
    simpa [mul_assoc, mul_comm, mul_left_comm] using hweighted
  have hquotient :
      (prefactor * base ^ (-exponent)) / (bound * base ^ delta) =
        (prefactor / bound) * base ^ (-(exponent + delta)) := by
    rw [show -(exponent + delta) = -exponent + -delta by ring,
      Real.rpow_add hbasePos, Real.rpow_neg hbasePos.le]
    field_simp
    rw [← Real.rpow_add hbasePos]
    norm_num
  have hpower : base ^ (-epsilon) ≤ base ^ (-(exponent + delta)) :=
    Real.rpow_le_rpow_of_exponent_le hbase (by linarith)
  calc
    (prefactor / bound) * base ^ (-epsilon) ≤
        (prefactor / bound) * base ^ (-(exponent + delta)) :=
      mul_le_mul_of_nonneg_left hpower (div_nonneg hprefactor.le hbound.le)
    _ = (prefactor * base ^ (-exponent)) / (bound * base ^ delta) :=
      hquotient.symm
    _ ≤ value := hdivided

end BombieriVinogradov.SiegelWalfisz

end

section

open Filter Metric Set

namespace BombieriVinogradov.SiegelWalfisz

theorem riemannZeta_im_real (s : ℝ) : (riemannZeta s).im = 0 := by
  have hsym := riemannZeta_conj (s : ℂ)
  have him := congrArg Complex.im hsym
  simp at him
  linarith

theorem exists_riemannZeta_neg_left :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ s : ℝ, 1 - eta < s → s < 1 → (riemannZeta s).re < 0 := by
  have hofReal : Tendsto (fun s : ℝ ↦ (s : ℂ))
      (nhdsWithin 1 (Iio 1)) (nhdsWithin 1 ({1}ᶜ : Set ℂ)) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · exact Complex.continuous_ofReal.continuousAt.tendsto.mono_left inf_le_left
    · filter_upwards [self_mem_nhdsWithin] with s hs
      have hsne : s ≠ 1 := ne_of_lt (Set.mem_Iio.mp hs)
      change (s : ℂ) ≠ 1
      exact_mod_cast hsne
  have hresidue : Tendsto
      (fun s : ℝ ↦ (((s : ℂ) - 1) * riemannZeta s).re)
      (nhdsWithin 1 (Iio 1)) (nhds 1) := by
    convert Complex.continuous_re.continuousAt.tendsto.comp
      (riemannZeta_residue_one.comp hofReal) using 1 <;>
        simp [Function.comp_def]
  have heventually : ∀ᶠ s : ℝ in nhdsWithin 1 (Iio 1),
      0 < (((s : ℂ) - 1) * riemannZeta s).re :=
    hresidue (Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  obtain ⟨eta, heta, hball⟩ := Metric.mem_nhdsWithin_iff.mp heventually
  refine ⟨eta, heta, ?_⟩
  intro s hsLower hsUpper
  have hdist : dist s 1 < eta := by
    rw [Real.dist_eq]
    rw [abs_of_nonpos (sub_nonpos.mpr hsUpper.le)]
    linarith
  have hproduct : 0 < (((s : ℂ) - 1) * riemannZeta s).re :=
    hball ⟨hdist, hsUpper⟩
  have him := riemannZeta_im_real s
  simp only [Complex.mul_re, Complex.sub_re, Complex.ofReal_re, Complex.one_re,
    Complex.sub_im, Complex.ofReal_im, Complex.one_im, zero_mul,
    sub_zero] at hproduct
  nlinarith

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem exists_siegelComparisonPoint {lower : ℝ}
    (hlower : 7 / 8 ≤ lower) (hupper : lower < 1) :
    ∃ s : ℝ, lower ≤ s ∧ 7 / 8 ≤ s ∧ s < 1 ∧ (riemannZeta s).re < 0 := by
  obtain ⟨eta, heta, hzeta⟩ := exists_riemannZeta_neg_left
  let s := max lower (1 - eta / 2)
  have hlowerS : lower ≤ s := le_max_left _ _
  have hsevenS : 7 / 8 ≤ s := hlower.trans hlowerS
  have hsUpper : s < 1 := by
    apply max_lt hupper
    linarith
  have hetaS : 1 - eta < s := by
    have : 1 - eta < 1 - eta / 2 := by linarith
    exact this.trans_le (le_max_right _ _)
  exact ⟨s, hlowerS, hsevenS, hsUpper, hzeta s hetaS hsUpper⟩

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem real_mem_siegelAnalyticDomain {s : ℝ} (hsLower : 7 / 8 ≤ s)
    (hsUpper : s ≤ 1) : (s : ℂ) ∈ siegelAnalyticDomain := by
  rw [siegelAnalyticDomain, Metric.mem_ball, Complex.dist_eq]
  have hnonpos : s - 2 ≤ 0 := by linarith
  rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonpos hnonpos]
  norm_num at hsLower ⊢
  linarith

private theorem characterLBlock_im_eq_zero_bv675 {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchiSquare : chi ^ 2 = 1)
    (k : ℕ) (s : ℝ) : (characterLBlock chi k s).im = 0 := by
  rw [characterLBlock, Complex.im_sum]
  apply Finset.sum_eq_zero
  intro j hj
  rcases MulChar.isQuadratic_iff_sq_eq_one.mpr hchiSquare j with hzero | hone | hneg
  · simp [hzero]
  · rw [hone, show (-(s : ℂ)) = ((-s : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_natCast (k * N + j.val),
      ← Complex.ofReal_cpow (Nat.cast_nonneg (k * N + j.val)) (-s)]
    simp
  · rw [hneg, show (-(s : ℂ)) = ((-s : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_natCast (k * N + j.val),
      ← Complex.ofReal_cpow (Nat.cast_nonneg (k * N + j.val)) (-s)]
    simp

theorem quadraticLFunction_im_eq_zero {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchiSquare : chi ^ 2 = 1) (hchi : chi ≠ 1)
    {s : ℝ} (hs : (s : ℂ) ∈ siegelAnalyticDomain) :
    (chi.LFunction s).im = 0 := by
  have hsum : Summable (fun k : ℕ ↦ characterLBlock chi k s) := by
    apply Summable.of_norm
    exact (characterLBlockMajorant_summable N).of_nonneg_of_le
      (fun k ↦ norm_nonneg _) fun k ↦ norm_characterLBlock_le chi hchi k hs
  rw [LFunction_eq_characterLBlockSeries chi hchi hs, characterLBlockSeries,
    Complex.im_tsum hsum]
  convert tsum_zero with k
  exact characterLBlock_im_eq_zero_bv675 chi hchiSquare k s

end BombieriVinogradov.SiegelWalfisz

end

section

open Set

namespace BombieriVinogradov.SiegelWalfisz

theorem quadraticLFunction_re_pos_of_no_zero {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchiSquare : chi ^ 2 = 1) (hchi : chi ≠ 1)
    {s : ℝ} (hsLower : 7 / 8 ≤ s) (hsUpper : s < 1)
    (hnozero : ∀ t : ℝ, s ≤ t → t ≤ 1 → chi.LFunction t ≠ 0) :
    0 < (chi.LFunction s).re := by
  let f : ℝ → ℝ := fun t ↦ (chi.LFunction t).re
  have hfcont : Continuous f := by
    exact Complex.continuous_re.comp
      ((chi.differentiable_LFunction hchi).continuous.comp Complex.continuous_ofReal)
  have hone : 0 < f 1 := quadraticLFunction_one_re_pos chi hchiSquare hchi
  by_contra hnot
  have himS := quadraticLFunction_im_eq_zero chi hchiSquare hchi
    (real_mem_siegelAnalyticDomain hsLower hsUpper.le)
  have hfs_ne : f s ≠ 0 := by
    intro hfs
    apply hnozero s le_rfl hsUpper.le
    apply Complex.ext
    · simpa [f] using hfs
    · simpa using himS
  have hfsNeg : f s < 0 := lt_of_le_of_ne (le_of_not_gt hnot) hfs_ne
  have hzeroMem : 0 ∈ Icc (f s) (f 1) := ⟨hfsNeg.le, hone.le⟩
  obtain ⟨t, ht, hft⟩ := intermediate_value_Icc hsUpper.le hfcont.continuousOn hzeroMem
  have himT := quadraticLFunction_im_eq_zero chi hchiSquare hchi
    (real_mem_siegelAnalyticDomain (hsLower.trans ht.1) ht.2)
  apply hnozero t ht.1 ht.2
  apply Complex.ext
  · simpa [f] using hft
  · simpa using himT

end BombieriVinogradov.SiegelWalfisz

end

section

open scoped ComplexOrder

namespace BombieriVinogradov.SiegelWalfisz

theorem quadraticLFunction_re_pos_of_primitive_no_zero {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) [NeZero chi.conductor]
    (hchiSquare : chi ^ 2 = 1) (hchi : chi ≠ 1)
    {s : ℝ} (hsLower : 7 / 8 ≤ s) (hsUpper : s < 1)
    (hnozero : ∀ t : ℝ, s ≤ t → t ≤ 1 →
      chi.primitiveCharacter.LFunction t ≠ 0) :
    0 < (chi.LFunction s).re := by
  have hprimitiveNe := primitiveCharacter_ne_one chi hchi
  have hprimitiveSquare := primitiveCharacter_sq_eq_one chi hchiSquare
  have hprimitivePos := quadraticLFunction_re_pos_of_no_zero chi.primitiveCharacter
    hprimitiveSquare hprimitiveNe hsLower hsUpper hnozero
  have hcorrection := characterLevelCorrection_pos chi hchiSquare
    (show 0 < s by linarith)
  have hcorrectionParts := Complex.lt_def.mp hcorrection
  have hprimitiveIm := quadraticLFunction_im_eq_zero chi.primitiveCharacter
    hprimitiveSquare hprimitiveNe
    (real_mem_siegelAnalyticDomain hsLower hsUpper.le)
  rw [LFunction_eq_primitive_mul_correction chi hchi, Complex.mul_re]
  rw [hprimitiveIm]
  norm_num
  exact mul_pos hprimitivePos (by simpa using hcorrectionParts.1)

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem siegelProductValue_re_eq_product {N M : ℕ}
    [NeZero N] [NeZero M] [NeZero (N.lcm M)]
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M)
    (hchiSquare : chi ^ 2 = 1) (hpsiSquare : psi ^ 2 = 1)
    (hchi : Ne chi 1) (hpsi : Ne psi 1)
    (hmul : Ne (DirichletCharacter.mul chi psi) 1)
    {s : ℝ} (hsLower : 7 / 8 ≤ s) (hsUpper : s < 1) :
    (siegelProductValue chi psi s).re =
      (riemannZeta s).re * (chi.LFunction s).re * (psi.LFunction s).re *
        ((DirichletCharacter.mul chi psi).LFunction s).re := by
  have hmulSquare := crossLevelMul_sq_eq_one chi psi hchiSquare hpsiSquare
  have hzetaIm := riemannZeta_im_real s
  have hchiIm := quadraticLFunction_im_eq_zero chi hchiSquare hchi
    (real_mem_siegelAnalyticDomain hsLower hsUpper.le)
  have hpsiIm := quadraticLFunction_im_eq_zero psi hpsiSquare hpsi
    (real_mem_siegelAnalyticDomain hsLower hsUpper.le)
  have hmulIm := quadraticLFunction_im_eq_zero (DirichletCharacter.mul chi psi)
    hmulSquare hmul (real_mem_siegelAnalyticDomain hsLower hsUpper.le)
  simp only [siegelProductValue, siegelLProduct, Complex.mul_re, Complex.mul_im,
    hzetaIm, hchiIm, hpsiIm, hmulIm, mul_zero, zero_mul, add_zero, sub_zero]
  ring

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

def PrimitiveQuadraticZeroFreeFrom (s : ℝ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (chi : DirichletCharacter ℂ N),
    DirichletCharacter.IsPrimitive chi -> chi ^ 2 = 1 -> Ne chi 1 ->
      ∀ t : ℝ, s ≤ t -> t ≤ 1 -> Ne (chi.LFunction t) 0

theorem PrimitiveQuadraticZeroFreeFrom.mono {lower s : ℝ}
    (hzeroFree : PrimitiveQuadraticZeroFreeFrom lower) (h : lower ≤ s) :
    PrimitiveQuadraticZeroFreeFrom s := by
  intro N _ chi hprimitive hsquare hne t hst ht
  exact hzeroFree N chi hprimitive hsquare hne t (h.trans hst) ht

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem siegelProductValue_nonpos_of_left_zero {N M : ℕ}
    [NeZero N] [NeZero M] [NeZero (N.lcm M)]
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M)
    {s : ℝ} (hzero : chi.LFunction s = 0) :
    (siegelProductValue chi psi s).re ≤ 0 := by
  simp [siegelProductValue, siegelLProduct, hzero]

theorem quadraticCharacterFour_product_nonpos_of_zeroFree {M : ℕ}
    [NeZero M] [NeZero ((4 : ℕ).lcm M)]
    (psi : DirichletCharacter ℂ M)
    (hpsiPrimitive : DirichletCharacter.IsPrimitive psi)
    (hpsiSquare : psi ^ 2 = 1) (hpsi : Ne psi 1)
    (hM : 4 < M) {s : ℝ} (hsLower : 7 / 8 ≤ s) (hsUpper : s < 1)
    (hzeta : (riemannZeta s).re < 0)
    (hzeroFree : PrimitiveQuadraticZeroFreeFrom s) :
    (siegelProductValue quadraticCharacterFour psi s).re ≤ 0 := by
  have hlevels : Ne 4 M := Ne.symm (Nat.ne_of_gt hM)
  have hmul := crossLevelMul_ne_one_of_primitive_of_ne quadraticCharacterFour psi
    quadraticCharacterFour_isPrimitive hpsiPrimitive hlevels
  have hmulSquare := crossLevelMul_sq_eq_one quadraticCharacterFour psi
    quadraticCharacterFour_sq hpsiSquare
  have hfourNoZero := hzeroFree 4 quadraticCharacterFour
    quadraticCharacterFour_isPrimitive quadraticCharacterFour_sq
      quadraticCharacterFour_ne_one
  have hfourPos := quadraticLFunction_re_pos_of_no_zero quadraticCharacterFour
    quadraticCharacterFour_sq quadraticCharacterFour_ne_one hsLower hsUpper hfourNoZero
  have hpsiNoZero := hzeroFree M psi hpsiPrimitive hpsiSquare hpsi
  have hpsiPos := quadraticLFunction_re_pos_of_no_zero psi hpsiSquare hpsi
    hsLower hsUpper hpsiNoZero
  let _ : NeZero (DirichletCharacter.mul quadraticCharacterFour psi).conductor :=
    ⟨(DirichletCharacter.mul quadraticCharacterFour psi).conductor_ne_zero⟩
  have hmulPrimitiveSquare := primitiveCharacter_sq_eq_one
    (DirichletCharacter.mul quadraticCharacterFour psi) hmulSquare
  have hmulPrimitiveNe := primitiveCharacter_ne_one
    (DirichletCharacter.mul quadraticCharacterFour psi) hmul
  have hmulPrimitiveNoZero := hzeroFree
    (DirichletCharacter.mul quadraticCharacterFour psi).conductor
    (DirichletCharacter.mul quadraticCharacterFour psi).primitiveCharacter
    (DirichletCharacter.mul quadraticCharacterFour psi).primitiveCharacter_isPrimitive
    hmulPrimitiveSquare hmulPrimitiveNe
  have hmulPos := quadraticLFunction_re_pos_of_primitive_no_zero
    (DirichletCharacter.mul quadraticCharacterFour psi) hmulSquare hmul
      hsLower hsUpper hmulPrimitiveNoZero
  rw [siegelProductValue_re_eq_product quadraticCharacterFour psi
    quadraticCharacterFour_sq hpsiSquare quadraticCharacterFour_ne_one hpsi hmul
      hsLower hsUpper]
  exact (mul_neg_of_neg_of_pos
    (mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hzeta hfourPos) hpsiPos)
      hmulPos).le

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

def IsSiegelSeed (lower : ℝ) (N : ℕ) (chi : DirichletCharacter ℂ N)
    (s : ℝ) : Prop :=
  0 < N ∧ DirichletCharacter.IsPrimitive chi ∧ chi ^ 2 = 1 ∧ Ne chi 1 ∧
    lower ≤ s ∧ 7 / 8 ≤ s ∧ s < 1 ∧
      ∀ (M : ℕ) [NeZero N] [NeZero M] [NeZero (N.lcm M)]
        (psi : DirichletCharacter ℂ M), N < M ->
          DirichletCharacter.IsPrimitive psi -> psi ^ 2 = 1 -> Ne psi 1 ->
            (siegelProductValue chi psi s).re ≤ 0

theorem exists_siegelSeed {lower : ℝ}
    (hlower : 7 / 8 ≤ lower) (hupper : lower < 1) :
    ∃ (N : ℕ) (chi : DirichletCharacter ℂ N) (s : ℝ),
      IsSiegelSeed lower N chi s := by
  by_cases hzeroFree : PrimitiveQuadraticZeroFreeFrom lower
  · obtain ⟨s, hlowerS, hsevenS, hsUpper, hzeta⟩ :=
      exists_siegelComparisonPoint hlower hupper
    have hzeroFreeS := hzeroFree.mono hlowerS
    refine ⟨4, quadraticCharacterFour, s, ?_⟩
    refine ⟨by norm_num, quadraticCharacterFour_isPrimitive,
      quadraticCharacterFour_sq, quadraticCharacterFour_ne_one,
      hlowerS, hsevenS, hsUpper, ?_⟩
    intro M _ _ _ psi hM hpsiPrimitive hpsiSquare hpsi
    exact quadraticCharacterFour_product_nonpos_of_zeroFree psi hpsiPrimitive
      hpsiSquare hpsi hM hsevenS hsUpper hzeta hzeroFreeS
  · rw [PrimitiveQuadraticZeroFreeFrom] at hzeroFree
    push Not at hzeroFree
    obtain ⟨N, hN, chi, hprimitive, hchiSquare, hchi, s,
      hlowerS, hsOne, hzero⟩ := hzeroFree
    let _ : NeZero N := hN
    have hsUpper : s < 1 := by
      apply lt_of_le_of_ne hsOne
      intro hs
      apply chi.LFunction_apply_one_ne_zero hchi
      simpa [hs] using hzero
    refine ⟨N, chi, s, ?_⟩
    refine ⟨NeZero.pos N, hprimitive, hchiSquare, hchi,
      hlowerS, hlower.trans hlowerS, hsUpper, ?_⟩
    intro M _ _ _ psi _ _ _ _
    exact siegelProductValue_nonpos_of_left_zero chi psi hzero

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem siegelLowerBound_largeLevel {C epsilon : ℝ} {D N : ℕ}
    {chi : DirichletCharacter ℂ N} {s : ℝ}
    (hpair : IsSiegelPositivityPair C D) (hepsilon : 0 < epsilon)
    (hseed : IsSiegelSeed (siegelLowerEndpoint epsilon D) N chi s) :
    ∀ (M : ℕ) [NeZero M] [NeZero (N.lcm M)]
      (psi : DirichletCharacter ℂ M), N < M ->
        DirichletCharacter.IsPrimitive psi -> psi ^ 2 = 1 -> Ne psi 1 ->
          siegelLargeLevelConstant C epsilon s N * (M : ℝ) ^ (-epsilon) ≤
            (psi.LFunction 1).re := by
  obtain ⟨hN, hchiPrimitive, hchiSquare, hchi, hlowerS,
    hsevenS, hsUpper, hseedNonpos⟩ := hseed
  let _ : NeZero N := ⟨hN.ne'⟩
  intro M _ _ psi hNM hpsiPrimitive hpsiSquare hpsi
  have hM : 0 < M := NeZero.pos M
  have hmul := crossLevelMul_ne_one_of_primitive_of_ne chi psi
    hchiPrimitive hpsiPrimitive (Ne.symm (Nat.ne_of_gt hNM))
  have hnonpos := hseedNonpos M psi hNM hpsiPrimitive hpsiSquare hpsi
  have hraw := targetLValue_transfer hpair chi psi hchiSquare hpsiSquare
    hchi hpsi hmul hsevenS hsUpper hnonpos
  have hnorm := norm_quadraticLFunction_one_eq_re psi hpsiSquare hpsi
  rw [hnorm] at hraw
  have hvaluePos := quadraticLFunction_one_re_pos psi hpsiSquare hpsi
  let delta : ℝ := epsilon / 2
  let base : ℝ := (N : ℝ) * (M : ℝ)
  let fixed : ℝ := C * characterLLogBoundConstant ^ 2 * (1 + Real.log N)
  have hdelta : 0 < delta := by
    dsimp [delta]
    positivity
  have hbase : 1 ≤ base := by
    dsimp [base]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hN.ne' hM.ne')
  have hfixed : 0 < fixed := by
    have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hlog : 0 < 1 + Real.log N := by
      linarith [Real.log_nonneg hNreal]
    dsimp [fixed]
    exact mul_pos (mul_pos hpair.1 (pow_pos characterLLogBoundConstant_pos 2)) hlog
  have hlogBound : 1 + Real.log (N.lcm M) ≤
      (1 + delta⁻¹) * base ^ delta := by
    simpa [delta, base] using one_add_log_lcm_le_rpow_mul hN hM hdelta
  have hscaled : fixed * (1 + Real.log (N.lcm M)) * (psi.LFunction 1).re ≤
      fixed * ((1 + delta⁻¹) * base ^ delta) * (psi.LFunction 1).re :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hlogBound hfixed.le) hvaluePos.le
  have hweighted :
      (1 - s) * base ^ (-((D : ℝ) * (1 - s))) ≤
        siegelLargeLevelDenominator C N delta * base ^ delta *
          (psi.LFunction 1).re := by
    calc
      (1 - s) * base ^ (-((D : ℝ) * (1 - s))) ≤
          fixed * (1 + Real.log (N.lcm M)) * (psi.LFunction 1).re := by
        simpa [base, fixed, mul_assoc] using hraw
      _ ≤ fixed * ((1 + delta⁻¹) * base ^ delta) *
          (psi.LFunction 1).re := hscaled
      _ = siegelLargeLevelDenominator C N delta * base ^ delta *
          (psi.LFunction 1).re := by
        dsimp [fixed]
        unfold siegelLargeLevelDenominator
        ring
  have hdirect := weighted_rpow_transfer (sub_pos.mpr hsUpper)
    (siegelLargeLevelDenominator_pos hpair.1 hN hdelta) hbase
      (siegel_exponent_control hepsilon D hlowerS) hweighted
  have hbasePower : base ^ (-epsilon) =
      (N : ℝ) ^ (-epsilon) * (M : ℝ) ^ (-epsilon) := by
    dsimp [base]
    exact Real.mul_rpow (by positivity) (by positivity)
  rw [hbasePower] at hdirect
  simpa [siegelLargeLevelConstant, delta, mul_assoc] using hdirect

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem siegelLowerBound :
    ∀ epsilon > (0 : ℝ), ∃ c > (0 : ℝ),
      ∀ (M : ℕ) [NeZero M] (psi : DirichletCharacter ℂ M), 3 ≤ M ->
        DirichletCharacter.IsPrimitive psi -> psi ^ 2 = 1 -> Ne psi 1 ->
          c * (M : ℝ) ^ (-epsilon) ≤ (psi.LFunction 1).re := by
  intro epsilon hepsilon
  obtain ⟨C, D, hpair⟩ := exists_siegelPositivityPair
  obtain ⟨N, chi, s, hseed⟩ := exists_siegelSeed
    (seven_eighths_le_siegelLowerEndpoint epsilon D)
    (siegelLowerEndpoint_lt_one hepsilon D)
  have hN : 0 < N := hseed.1
  have hsUpper : s < 1 := hseed.2.2.2.2.2.2.1
  let _ : NeZero N := ⟨hN.ne'⟩
  let c := min (finiteLevelConstant epsilon N)
    (siegelLargeLevelConstant C epsilon s N)
  have hcPositive : 0 < c := by
    apply lt_min
    · exact finiteLevelConstant_pos epsilon N
    · exact siegelLargeLevelConstant_pos hpair.1 hepsilon hN hsUpper
  refine ⟨c, hcPositive, ?_⟩
  intro M _ psi hM hpsiPrimitive hpsiSquare hpsi
  have hpowerNonneg : 0 ≤ (M : ℝ) ^ (-epsilon) :=
    Real.rpow_nonneg (Nat.cast_nonneg M) (-epsilon)
  by_cases hMN : M ≤ N
  · have hcoefficient : c ≤ finiteLevelConstant epsilon N := min_le_left _ _
    exact (mul_le_mul_of_nonneg_right hcoefficient hpowerNonneg).trans
      (finiteLevelConstant_le_value hMN hM psi hpsiSquare hpsi)
  · have hNM : N < M := Nat.lt_of_not_ge hMN
    let _ : NeZero (N.lcm M) :=
      ⟨Nat.lcm_ne_zero hN.ne' (NeZero.ne M)⟩
    have hcoefficient : c ≤ siegelLargeLevelConstant C epsilon s N :=
      min_le_right _ _
    exact (mul_le_mul_of_nonneg_right hcoefficient hpowerNonneg).trans
      (siegelLowerBound_largeLevel hpair hepsilon hseed M psi hNM
        hpsiPrimitive hpsiSquare hpsi)

end BombieriVinogradov.SiegelWalfisz

end

namespace BVShort
open Complex DirichletCharacter

theorem local_lower {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {x M t : ℝ} (hx : 0 < x) (hM : 0 < M) (hs : 16*M^8*x < 1)
    (hp : ‖LFunctionTrivChar q (1+x)‖ ≤ M/x)
    (hd : ‖(χ^2).LFunction (1+x+2*I*t)‖ ≤ M) :
    2*M*x < ‖χ.LFunction (1+x+I*t)‖ := by
  by_contra! h
  have H := χ.norm_LFunction_product_ge_one hx t
  simp only [norm_mul,norm_pow] at H
  have H' : (1:ℝ) ≤ (M/x)^3*(2*M*x)^4*M := H.trans (by gcongr)
  have e : (M/x)^3*(2*M*x)^4*M = 16*M^8*x := by field_simp; ring
  linarith [e]

theorem local_disk {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hn : χ ≠ 1)
    {x M t : ℝ} (hx : 0 < x) (hM : 0 < M) (hs : 16*M^8*x < 1)
    (hp : ‖LFunctionTrivChar q (1+x)‖ ≤ M/x)
    (hd : ‖(χ^2).LFunction (1+x+2*I*t)‖ ≤ M)
    (D : ∀ z ∈ Metric.closedBall (1+x+I*t) (3*x/2), ‖deriv χ.LFunction z‖ ≤ M)
    {z : ℂ} (hz : z ∈ Metric.closedBall (1+x+I*t) (3*x/2)) :
    M*x/2 < ‖χ.LFunction z‖ ∧ ‖deriv χ.LFunction z / χ.LFunction z‖ ≤ 2/x := by
  let c : ℂ := 1+x+I*t
  have hc : c ∈ Metric.closedBall c (3*x/2) := Metric.mem_closedBall_self (by positivity)
  have H := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun z _ => (differentiable_LFunction hn z)) D (convex_closedBall c _) hz hc
  have hb : ‖c-z‖ ≤ 3*x/2 := by rw [←dist_eq_norm,dist_comm]; exact hz
  have hh := local_lower χ hx hM hs hp hd
  change 2*M*x < ‖χ.LFunction c‖ at hh
  have hl : M*x/2 < ‖χ.LFunction z‖ := by
    linarith [norm_sub_norm_le (χ.LFunction c) (χ.LFunction z), mul_le_mul_of_nonneg_left hb hM.le]
  refine ⟨hl, ?_⟩
  rw [norm_div, div_le_div_iff₀ (lt_trans (by positivity) hl) hx]
  nlinarith [mul_le_mul_of_nonneg_right (D z hz) hx.le]
end BVShort

namespace BVShort
open Complex DirichletCharacter Filter
open scoped Topology
lemma principal_le_zeta {q : ℕ} [NeZero q] {u : ℝ} (hu : 1 < u) :
    ‖LFunctionTrivChar q u‖ ≤ ‖riemannZeta u‖ := by
  have h : (u:ℂ) ≠ 1 := by exact_mod_cast hu.ne'
  rw [LFunctionTrivChar_eq_mul_riemannZeta h, norm_mul, norm_prod]
  apply mul_le_of_le_one_left (norm_nonneg _)
  apply Finset.prod_le_one (fun _ _ => norm_nonneg _)
  intro p hp
  have h1 : 1 ≤ (p:ℝ) := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_le
  have ha : 0 ≤ (p:ℝ)^(-u) := by positivity
  have hb := Real.rpow_le_one_of_one_le_of_nonpos h1 (show -u ≤ 0 by linarith)
  have e : (1:ℂ) - (p:ℂ)^(-(u:ℂ)) = ((1-(p:ℝ)^(-u):ℝ):ℂ) := by
    push_cast; rw [Complex.ofReal_cpow (by positivity)]; simp
  rw [e, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]; linarith
lemma principal_uniform : ∀ᶠ u : ℝ in 𝓝[>] 1, ∀ (q : ℕ) [NeZero q],
    ‖LFunctionTrivChar q u‖ ≤ 2 / (u-1) := by
  have ht : Tendsto (fun x : ℝ => (x:ℂ)) (𝓝[>] 1) (𝓝[≠] 1) :=
    continuous_ofReal.continuousWithinAt.tendsto_nhdsWithin (by
      intro x hx; change (x:ℂ) ≠ 1; exact_mod_cast (show 1 < x from hx).ne')
  have hh := (riemannZeta_residue_one.comp ht).norm.eventually (gt_mem_nhds (show ‖(1:ℂ)‖ < 2 by norm_num))
  filter_upwards [hh, eventually_mem_nhdsWithin] with u hu hu1
  have hu' : 1 < u := hu1
  intro q _
  apply (principal_le_zeta hu').trans
  apply (le_div_iff₀ (sub_pos.mpr hu')).mpr
  change ‖((u:ℂ)-1)*riemannZeta u‖ < 2 at hu
  rw [norm_mul, ←ofReal_one, ←ofReal_sub, norm_real, Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hu')] at hu
  simpa [mul_comm] using hu.le
end BVShort

end

section

open Complex Filter LSeries Metric Set Topology
namespace BVHeight
noncomputable section
variable (t : ℝ)
lemma hre {s : ℂ} (hs : s ∈ (ball (2+I*t : ℂ) (7/4 : ℝ))) : 1/4 < s.re := by
  have h := Complex.abs_re_le_norm (s-(2+I*t))
  rw [mem_ball, dist_eq_norm] at hs
  norm_num [sub_re, add_re, mul_re] at h
  linarith [neg_abs_le (s.re-2)]
lemma hnorm {s : ℂ} (hs : s ∈ (ball (2+I*t : ℂ) (7/4 : ℝ))) : ‖s‖ ≤ (4+|t|) := by
  rw [mem_ball, dist_eq_norm] at hs
  have h := norm_sub_norm_le s (2+I*t)
  have h' := norm_add_le (2:ℂ) (I*t)
  simp [Real.norm_eq_abs] at h'
  linarith

noncomputable def characterLBlock {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (k : ℕ) (s : ℂ) : ℂ :=
  ∑ j : ZMod N, χ j * ((k * N + j.val : ℕ) : ℂ) ^ (-s)

theorem characterLBlock_recenter {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (k : ℕ) (s : ℂ) :
    characterLBlock χ k s =
      ∑ j : ZMod N, χ j *
        (((k * N + j.val : ℕ) : ℂ) ^ (-s) - (((k + 1) * N : ℕ) : ℂ) ^ (-s)) := by
  rw [characterLBlock]
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  rw [χ.sum_eq_zero_of_ne_one hχ, zero_mul, sub_zero]

theorem characterLBlock_differentiableOn {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (k : ℕ) :
    DifferentiableOn ℂ (characterLBlock χ k) (ball (2+I*t : ℂ) (7/4 : ℝ)) := by
  have hN : N ≠ 1 := by
    intro h
    subst N
    exact hχ (Subsingleton.elim _ _)
  rw [show characterLBlock χ k = fun s ↦
      ∑ j : ZMod N, χ j *
        (((k * N + j.val : ℕ) : ℂ) ^ (-s) - (((k + 1) * N : ℕ) : ℂ) ^ (-s)) by
    funext s
    exact characterLBlock_recenter χ hχ k s]
  intro s hs
  apply DifferentiableAt.differentiableWithinAt
  apply DifferentiableAt.fun_sum
  intro j hj
  by_cases hj0 : j = 0
  · subst j
    rw [χ.map_zero' hN]
    simp
  · have hx : ((k * N + j.val : ℕ) : ℂ) ≠ 0 := by
      exact Nat.cast_ne_zero.mpr (by
        have hjv : j.val ≠ 0 := (ZMod.val_ne_zero j).mpr hj0
        omega)
    have hy : ((((k + 1) * N : ℕ) : ℂ)) ≠ 0 := by
      exact Nat.cast_ne_zero.mpr (Nat.mul_ne_zero (by omega) (NeZero.ne N))
    exact (((differentiableAt_id.neg).const_cpow (Or.inl hx)).sub
      ((differentiableAt_id.neg).const_cpow (Or.inl hy))).const_mul (χ j)

theorem norm_cpow_neg_sub_le {s : ℂ} {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y)
    (hre : (1 / 4 : ℝ) ≤ s.re) (hs : ‖s‖ ≤ (4+|t|)) :
    ‖(x : ℂ) ^ (-s) - (y : ℂ) ^ (-s)‖ ≤
      (4+|t|) * (y - x) * x ^ (-5 / 4 : ℝ) := by
  have hs0 : -s ≠ 0 := by
    intro h
    have : s = 0 := neg_eq_zero.mp h
    subst s
    norm_num at hre
  have hderiv (t : ℝ) (ht : t ∈ Icc x y) :
      HasDerivWithinAt (fun u : ℝ ↦ (u : ℂ) ^ (-s))
        ((-s) * (t : ℂ) ^ (-s - 1)) (Icc x y) t := by
    exact (hasDerivAt_ofReal_cpow_const (ne_of_gt (lt_of_lt_of_le zero_lt_one (hx.trans ht.1)))
      hs0).hasDerivWithinAt
  have hbound (u : ℝ) (ht : u ∈ Icc x y) :
      ‖(-s) * (u : ℂ) ^ (-s - 1)‖ ≤ (4+|t|) * x ^ (-5 / 4 : ℝ) := by
    have htpos : 0 < u := lt_of_lt_of_le zero_lt_one (hx.trans ht.1)
    have hpow_exp : u ^ (-s.re - 1) ≤ u ^ (-5 / 4 : ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le
      · exact hx.trans ht.1
      · linarith
    have hpow_base : u ^ (-5 / 4 : ℝ) ≤ x ^ (-5 / 4 : ℝ) := by
      exact Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le zero_lt_one hx) ht.1 (by norm_num)
    rw [norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos htpos]
    exact mul_le_mul hs (hpow_exp.trans hpow_base) (Real.rpow_nonneg htpos.le _) (by positivity)
  have hmv := (convex_Icc x y : Convex ℝ (Icc x y)).norm_image_sub_le_of_norm_hasDerivWithin_le
    hderiv hbound (left_mem_Icc.mpr hxy) (right_mem_Icc.mpr hxy)
  rw [norm_sub_rev, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hxy)] at hmv
  calc
    ‖(x : ℂ) ^ (-s) - (y : ℂ) ^ (-s)‖
        ≤ ((4+|t|) * x ^ (-5 / 4 : ℝ)) * (y - x) := hmv
    _ = (4+|t|) * (y - x) * x ^ (-5 / 4 : ℝ) := by ring

noncomputable def characterLBlockMajorant (N k : ℕ) : ℝ :=
  (4+|t|) * (N : ℝ) ^ 2 * ((k + 1 : ℕ) : ℝ) ^ (-5 / 4 : ℝ)

theorem norm_characterLBlock_le {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (k : ℕ) {s : ℂ}
    (hs : s ∈ (ball (2+I*t : ℂ) (7/4 : ℝ))) :
    ‖characterLBlock χ k s‖ ≤ characterLBlockMajorant t N k := by
  have hN : N ≠ 1 := by
    intro h
    subst N
    exact hχ (Subsingleton.elim _ _)
  rw [characterLBlock_recenter χ hχ]
  calc
    ‖∑ j : ZMod N, χ j *
        (((k * N + j.val : ℕ) : ℂ) ^ (-s) - (((k + 1) * N : ℕ) : ℂ) ^ (-s))‖
        ≤ ∑ j : ZMod N, ‖χ j *
          (((k * N + j.val : ℕ) : ℂ) ^ (-s) - (((k + 1) * N : ℕ) : ℂ) ^ (-s))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _j : ZMod N,
        (4+|t|) * (N : ℝ) * ((k + 1 : ℕ) : ℝ) ^ (-5 / 4 : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      by_cases hj0 : j = 0
      · subst j
        rw [χ.map_zero' hN]
        simp only [zero_mul, norm_zero]
        positivity
      · have hjv : j.val ≠ 0 := (ZMod.val_ne_zero j).mpr hj0
        have hxoneNat : 1 ≤ k * N + j.val := by omega
        have hxyNat : k * N + j.val ≤ (k + 1) * N := by
          have hjlt := j.val_lt
          rw [Nat.add_mul, one_mul]
          omega
        have hlenNat : (k + 1) * N - (k * N + j.val) ≤ N := by
          have hjlt := j.val_lt
          rw [Nat.add_mul, one_mul]
          omega
        have hxkNat : k + 1 ≤ k * N + j.val := by
          have hNp := NeZero.pos N
          have hk : k ≤ k * N := by
            simpa using Nat.mul_le_mul_left k hNp
          omega
        have hxone : (1 : ℝ) ≤ (k * N + j.val : ℕ) := by exact_mod_cast hxoneNat
        have hxy : ((k * N + j.val : ℕ) : ℝ) ≤ ((k + 1) * N : ℕ) := by
          exact_mod_cast hxyNat
        have hlen : (((k + 1) * N : ℕ) : ℝ) - (k * N + j.val : ℕ) ≤ N := by
          rw [← Nat.cast_sub hxyNat]
          exact_mod_cast hlenNat
        have hxk : (((k + 1 : ℕ) : ℝ)) ≤ (k * N + j.val : ℕ) := by
          exact_mod_cast hxkNat
        have hpow : ((k * N + j.val : ℕ) : ℝ) ^ (-5 / 4 : ℝ) ≤
            ((k + 1 : ℕ) : ℝ) ^ (-5 / 4 : ℝ) := by
          exact Real.rpow_le_rpow_of_nonpos (by positivity) hxk (by norm_num)
        have hvar := norm_cpow_neg_sub_le t hxone hxy
          (le_of_lt (hre t hs))
          (hnorm t hs)
        rw [norm_mul]
        calc
          ‖χ j‖ * ‖((k * N + j.val : ℕ) : ℂ) ^ (-s) -
              (((k + 1) * N : ℕ) : ℂ) ^ (-s)‖
              ≤ ‖χ j‖ * ((4+|t|) *
                ((((k + 1) * N : ℕ) : ℝ) - (k * N + j.val : ℕ)) *
                  ((k * N + j.val : ℕ) : ℝ) ^ (-5 / 4 : ℝ)) :=
            mul_le_mul_of_nonneg_left hvar (norm_nonneg _)
          _ ≤ 1 * ((4+|t|) *
                ((((k + 1) * N : ℕ) : ℝ) - (k * N + j.val : ℕ)) *
                  ((k * N + j.val : ℕ) : ℝ) ^ (-5 / 4 : ℝ)) := by
            gcongr
            exact χ.norm_le_one j
          _ = (4+|t|) *
                ((((k + 1) * N : ℕ) : ℝ) - (k * N + j.val : ℕ)) *
                  ((k * N + j.val : ℕ) : ℝ) ^ (-5 / 4 : ℝ) := by ring
          _ ≤ (4+|t|) * (N : ℝ) *
                ((k * N + j.val : ℕ) : ℝ) ^ (-5 / 4 : ℝ) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hlen (by positivity)) (Real.rpow_nonneg (by positivity) _)
          _ ≤ (4+|t|) * (N : ℝ) * ((k + 1 : ℕ) : ℝ) ^ (-5 / 4 : ℝ) := by
            exact mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = characterLBlockMajorant t N k := by
      simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
      rw [characterLBlockMajorant]
      ring

noncomputable def characterLBlockSeries {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
  ∑' k : ℕ, characterLBlock χ k s

theorem characterLBlockMajorant_summable (N : ℕ) :
    Summable (characterLBlockMajorant t N) := by
  have hp : Summable (fun n : ℕ ↦ (n : ℝ) ^ (-5 / 4 : ℝ)) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  have hshift := (summable_nat_add_iff 1).mpr hp
  change Summable (fun k : ℕ ↦
    (4+|t|) * (N : ℝ) ^ 2 * ((k + 1 : ℕ) : ℝ) ^ (-5 / 4 : ℝ))
  exact hshift.mul_left ((4+|t|) * (N : ℝ) ^ 2)

theorem characterLBlockSeries_differentiableOn {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) :
    DifferentiableOn ℂ (characterLBlockSeries χ) (ball (2+I*t : ℂ) (7/4 : ℝ)) := by
  change DifferentiableOn ℂ (fun s ↦ ∑' k : ℕ, characterLBlock χ k s)
    (ball (2+I*t : ℂ) (7/4 : ℝ))
  exact Complex.differentiableOn_tsum_of_summable_norm
    (characterLBlockMajorant_summable t N)
    (fun k ↦ characterLBlock_differentiableOn t χ hχ k)
    (by exact Metric.isOpen_ball)
    (fun k s hs ↦ norm_characterLBlock_le t χ hχ k hs)

theorem LFunction_eq_characterLBlockSeries_of_one_lt_re {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hN : N ≠ 1) {s : ℂ} (hs : 1 < s.re) :
    χ.LFunction s = characterLBlockSeries χ s ∧ Summable (fun k => characterLBlock χ k s) := by
  have hzero : (fun n : ℕ ↦ χ n) 0 = 0 := by
    simpa using χ.map_zero' hN
  have hsum : Summable (fun n : ℕ ↦ χ n * (n : ℂ) ^ (-s)) := by
    rw [← funext (LSeries.term_def₀ hzero s)]
    exact DirichletCharacter.LSeriesSummable_of_one_lt_re χ hs
  have hterm (j : ZMod N) (k : ℕ) :
      χ ((j.val + N * k : ℕ) : ZMod N) * ((j.val + N * k : ℕ) : ℂ) ^ (-s) =
        χ j * ((k * N + j.val : ℕ) : ℂ) ^ (-s) := by
    have hcast : ((j.val + N * k : ℕ) : ZMod N) = j := by
      simp [Nat.cast_add, Nat.cast_mul]
    rw [hcast]
    congr 2
    simp only [Nat.add_comm, Nat.mul_comm]
  have hsub (j : ZMod N) :
      Summable (fun k : ℕ ↦ χ j * ((k * N + j.val : ℕ) : ℂ) ^ (-s)) := by
    have hinj : Function.Injective (fun k : ℕ ↦ j.val + N * k) := by
      intro a b hab
      exact Nat.mul_left_cancel (NeZero.pos N) (Nat.add_left_cancel hab)
    have h := hsum.comp_injective hinj
    exact h.congr (hterm j)
  have hswap := Summable.tsum_finsetSum (s := Finset.univ)
    (fun j _hj ↦ hsub j)
  refine ⟨?_, ?_⟩
  · exact calc
    χ.LFunction s = LSeries (χ ·) s := DirichletCharacter.LFunction_eq_LSeries χ hs
    _ = ∑' n : ℕ, χ n * (n : ℂ) ^ (-s) := by
      rw [LSeries_def₀ hzero]
      congr 1
      funext n
      rw [Complex.cpow_neg, div_eq_mul_inv]
    _ = ∑ j : ZMod N, ∑' k : ℕ,
        χ ((j.val + N * k : ℕ) : ZMod N) * ((j.val + N * k : ℕ) : ℂ) ^ (-s) :=
      Nat.sumByResidueClasses hsum N
    _ = ∑ j : ZMod N, ∑' k : ℕ,
        χ j * ((k * N + j.val : ℕ) : ℂ) ^ (-s) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact tsum_congr (hterm j)
    _ = ∑' k : ℕ, ∑ j : ZMod N,
        χ j * ((k * N + j.val : ℕ) : ℂ) ^ (-s) := by
      simpa only [Finset.mem_univ, ↓reduceIte] using hswap.symm
    _ = characterLBlockSeries χ s := rfl

  · classical
    have aux (S : Finset (ZMod N)) : Summable (fun k : ℕ => ∑ j ∈ S, χ j * ((k*N+j.val:ℕ):ℂ)^(-s)) := by
      induction S using Finset.induction_on with
      | empty => simp
      | insert j S hj ih => simpa [Finset.sum_insert hj] using (hsub j).add ih
    exact aux _

theorem LFunction_eq_characterLBlockSeries {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {s : ℂ}
    (hs : s ∈ (ball (2+I*t : ℂ) (7/4 : ℝ))) : χ.LFunction s = characterLBlockSeries χ s := by
  have hL : AnalyticOnNhd ℂ (χ.LFunction) (ball (2+I*t : ℂ) (7/4 : ℝ)) :=
    (DirichletCharacter.differentiable_LFunction hχ).differentiableOn.analyticOnNhd
      Metric.isOpen_ball
  have hB : AnalyticOnNhd ℂ (characterLBlockSeries χ) (ball (2+I*t : ℂ) (7/4 : ℝ)) :=
    (characterLBlockSeries_differentiableOn t χ hχ).analyticOnNhd Metric.isOpen_ball
  have h2 : (2+I*t : ℂ) ∈ (ball (2+I*t : ℂ) (7/4 : ℝ)) := by
    rw [mem_ball]
    norm_num
  have heq : χ.LFunction =ᶠ[𝓝 (2+I*t : ℂ)] characterLBlockSeries χ := by
    have hV : {z : ℂ | 1 < z.re} ∈ 𝓝 (2+I*t : ℂ) :=
      (continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds (by norm_num [mul_re])
    filter_upwards [hV] with z hz
    exact (LFunction_eq_characterLBlockSeries_of_one_lt_re χ (by rintro rfl; exact hχ (Subsingleton.elim _ _)) hz).1
  exact hL.eqOn_of_preconnected_of_eventuallyEq hB
    (convex_ball (2+I*t : ℂ) (7 / 4 : ℝ)).isPreconnected h2 heq hs

private theorem sum_zmod_val_inv_le_harmonic_bv622 (N : ℕ) [NeZero N] :
    ∑ j : ZMod N, ((j.val : ℝ)⁻¹) ≤ 2 * (harmonic N : ℝ) := by
  calc
    ∑ j : ZMod N, ((j.val : ℝ)⁻¹) = ∑ i : Fin N, ((i.val : ℝ)⁻¹) := by
      symm
      apply Fintype.sum_equiv (ZMod.finEquiv N).toEquiv
      intro i
      change ((i.val : ℝ)⁻¹) = ((((ZMod.finEquiv N) i).val : ℝ)⁻¹)
      congr 2
      obtain _ | n := N
      · exact (NeZero.ne 0 rfl).elim
      · rfl
    _ ≤ ∑ i : Fin N, 2 * ((((i.val + 1 : ℕ) : ℝ))⁻¹) := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases hi0 : i.val = 0
      · simp [hi0]
      · have hipos : (0 : ℝ) < i.val := by exact_mod_cast Nat.pos_of_ne_zero hi0
        have hisucc : (0 : ℝ) < i.val + 1 := by positivity
        rw [← one_div, ← div_eq_mul_inv]
        norm_num only [Nat.cast_add, Nat.cast_one]
        rw [div_le_div_iff₀ hipos hisucc]
        norm_num
        have hiNat : i.val + 1 ≤ 2 * i.val := by omega
        exact_mod_cast hiNat
    _ = 2 * (harmonic N : ℝ) := by
      rw [← Finset.mul_sum]
      congr 1
      rw [Finset.sum_fin_eq_sum_range, harmonic, Rat.cast_sum]
      apply Finset.sum_congr rfl
      intro x hx
      simp [Finset.mem_range.mp hx]

private lemma weight {s : ℂ} {x U : ℝ} (hx : 1 ≤ x) (hxU : x ≤ U)
    (h : (1-s.re)*Real.log U ≤ 1) : ‖(x:ℂ)^(-s)‖ ≤ Real.exp 1 / x := by
  have xp : 0 < x := by linarith
  rw [norm_cpow_eq_rpow_re_of_pos xp, neg_re, le_div_iff₀ xp]
  nth_rw 2 [← Real.rpow_one x]
  rw [← Real.rpow_add xp]
  rw [Real.rpow_def_of_pos xp, Real.exp_le_exp]
  by_cases hs : 0 ≤ 1-s.re
  · nlinarith [mul_le_mul_of_nonneg_left (Real.log_le_log xp hxU) hs]
  · nlinarith [mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hs) (Real.log_nonneg hx)]

private lemma first {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hn1 : N ≠ 1)
    {s : ℂ} {U : ℝ} (hN : (N:ℝ) ≤ U) (h : (1-s.re)*Real.log U ≤ 1) :
    ‖characterLBlock χ 0 s‖ ≤ Real.exp 1 * (2*(1+Real.log N)) := by
  simp only [characterLBlock, zero_mul, zero_add]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ j : ZMod N, Real.exp 1 * (j.val : ℝ)⁻¹ := by
      apply Finset.sum_le_sum; intro j _
      by_cases hj : j = 0
      · subst j; simp [χ.map_zero' hn1]
      have hv : 1 ≤ j.val := Nat.one_le_iff_ne_zero.mpr ((ZMod.val_ne_zero j).mpr hj)
      rw [norm_mul]
      apply (mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one j)).trans
      simpa only [ofReal_natCast, div_eq_mul_inv] using weight (s:=s) (x:=(j.val:ℝ)) (by exact_mod_cast hv)
        ((show (j.val:ℝ) ≤ N by exact_mod_cast j.val_lt.le).trans hN) h
    _ ≤ _ := by rw [← Finset.mul_sum]; gcongr; exact (sum_zmod_val_inv_le_harmonic_bv622 N).trans (by gcongr; exact harmonic_le_one_add_log N)

private lemma middle {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (k : ℕ) {s : ℂ} {U : ℝ} (hN : ((k+2:ℕ):ℝ)*N ≤ U) (h : (1-s.re)*Real.log U ≤ 1) :
    ‖characterLBlock χ (k+1) s‖ ≤ Real.exp 1 / (k+1) := by
  have hp : 0 < ((k+1)*N) := Nat.mul_pos (by omega) (NeZero.pos N)
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _j : ZMod N, Real.exp 1 / (((k+1)*N:ℕ):ℝ) := by
      apply Finset.sum_le_sum; intro j _
      let n := (k+1)*N+j.val
      have hn : 1 ≤ n := by dsimp [n]; omega
      have hnu : n ≤ (k+2)*N := by
        dsimp [n]
        have hj := j.val_lt
        nlinarith
      rw [norm_mul]; apply (mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one j)).trans
      change ‖(n:ℂ)^(-s)‖ ≤ _
      rw [← Complex.ofReal_natCast n]
      apply (weight (s:=s) (x:=(n:ℝ)) (by exact_mod_cast hn) ((show (n:ℝ) ≤ ((k+2:ℕ):ℝ)*N by exact_mod_cast hnu).trans hN) h).trans
      gcongr; first | exact_mod_cast hp | exact_mod_cast Nat.le_add_right ((k+1)*N) j.val
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, Nat.cast_mul, Nat.cast_add, Nat.cast_one]; field_simp [NeZero.ne N]

noncomputable def tailC : ℝ := ∑' i : ℕ, ((i+1:ℕ):ℝ)^(-9/8:ℝ)
private lemma tail_sum : Summable (fun i : ℕ => ((i+1:ℕ):ℝ)^(-9/8:ℝ)) :=
  (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr (by norm_num))

theorem split_bound {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hn : χ ≠ 1)
    {s : ℂ} (hs : s ∈ (ball (2+I*t : ℂ) (7/4 : ℝ))) (K : ℕ) {U : ℝ} (hU : ((K+2:ℕ):ℝ)*N ≤ U)
    (h : (1-s.re)*Real.log U ≤ 1) (hK : ((4+|t|)*(N:ℝ)^2)^8 ≤ K) :
    ‖χ.LFunction s‖ ≤ Real.exp 1 * (2*(1+Real.log N) + (1+Real.log K)) + tailC := by
  let f := fun i => ‖characterLBlock χ i s‖
  have hf : Summable f := (characterLBlockMajorant_summable t N).of_nonneg_of_le
    (fun _ => norm_nonneg _) (fun i => norm_characterLBlock_le t χ hn i hs)
  rw [LFunction_eq_characterLBlockSeries t χ hn hs, characterLBlockSeries]
  apply (norm_tsum_le_tsum_norm hf).trans
  change ∑' i, f i ≤ _
  rw [← hf.sum_add_tsum_nat_add (K+1), Finset.sum_range_succ' f K]
  have hfirst := first χ (by rintro rfl; exact hn (Subsingleton.elim _ _)) (show (N:ℝ) ≤ U by apply le_trans _ hU; push_cast; nlinarith [Nat.cast_nonneg (α:=ℝ) K, Nat.cast_nonneg (α:=ℝ) N, mul_nonneg (Nat.cast_nonneg (α:=ℝ) K) (Nat.cast_nonneg (α:=ℝ) N)]) h
  have hmid : ∑ i ∈ Finset.range K, f (i+1) ≤ Real.exp 1 * (1+Real.log K) := by
    calc
      _ ≤ ∑ i ∈ Finset.range K, Real.exp 1 * (((i+1:ℕ):ℝ)⁻¹) := by
        apply Finset.sum_le_sum; intro i hi
        simpa only [div_eq_mul_inv, Nat.cast_add, Nat.cast_one] using middle χ i (s:=s) (U:=U) (by apply le_trans _ hU; gcongr; exact (Finset.mem_range.mp hi).le) h
      _ = Real.exp 1 * (harmonic K : ℝ) := by simp [harmonic, Finset.mul_sum]
      _ ≤ _ := by gcongr; exact harmonic_le_one_add_log K
  have htail : (∑' i : ℕ, f (i+(K+1))) ≤ tailC := by
    apply Summable.tsum_le_tsum _ ((summable_nat_add_iff _).mpr hf) tail_sum
    intro i
    let y : ℝ := ((i+(K+1)+1:ℕ):ℝ)
    have yp : 0 < y := by dsimp [y]; positivity
    have hy : (K:ℝ) ≤ y := by dsimp [y]; exact_mod_cast (by omega : K ≤ i+(K+1)+1)
    have hco : (4+|t|)*(N:ℝ)^2 ≤ y^(1/8:ℝ) := by
      have hh := Real.rpow_le_rpow (show 0 ≤ ((4+|t|)*(N:ℝ)^2)^8 by positivity) (hK.trans hy) (by norm_num : 0 ≤ (1/8:ℝ))
      rwa [← Real.rpow_natCast _ 8, ← Real.rpow_mul (by positivity), show (↑(8:ℕ):ℝ)*(1/8)=1 by norm_num, Real.rpow_one] at hh
    apply (norm_characterLBlock_le t χ hn _ hs).trans
    change (4+|t|)*(N:ℝ)^2*y^(-5/4:ℝ) ≤ _
    calc
      _ ≤ y^(1/8:ℝ)*y^(-5/4:ℝ) := by gcongr
      _ = y^(-9/8:ℝ) := by rw [← Real.rpow_add yp]; norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_nonpos (by positivity) (by dsimp [y]; exact_mod_cast (by omega : i+1 ≤ i+(K+1)+1)) (by norm_num)
  change f 0 ≤ _ at hfirst
  linarith

noncomputable def Q (N : ℕ) (t : ℝ) := 2+(N:ℝ)*(2+|t|)
noncomputable def C := 30*Real.exp 1 + |tailC|
lemma Q_ge {N : ℕ} [NeZero N] : 4+|t| ≤ Q N t := by
  have hn : (1:ℝ) ≤ N := by exact_mod_cast NeZero.pos N
  unfold Q; nlinarith [mul_le_mul_of_nonneg_right hn (show 0 ≤ 2+|t| by positivity)]
lemma logQ_ge {N : ℕ} [NeZero N] : 1 ≤ Real.log (Q N t) := by
  rw [← Real.exp_le_exp, Real.exp_log (by linarith [Q_ge (N:=N) t, abs_nonneg t])]
  linarith [Real.exp_one_lt_d9, Q_ge (N:=N) t, abs_nonneg t]

theorem disk_bound {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hn : χ ≠ 1)
    {s : ℂ} (hs : dist s (1+I*t) ≤ 1/(26*Real.log (Q N t))) :
    ‖χ.LFunction s‖ ≤ C*Real.log (Q N t) := by
  let A := Q N t
  have hA : 4 ≤ A := by linarith [Q_ge (N:=N) t, abs_nonneg t]
  have ha : 1 ≤ Real.log A := logQ_ge t
  have hN : (N:ℝ) ≤ A := by dsimp [A,Q]; nlinarith [mul_nonneg (Nat.cast_nonneg (α:=ℝ) N) (abs_nonneg t)]
  let K := ⌈A^24⌉₊
  have hk : A^24 ≤ (K:ℝ) := Nat.le_ceil _
  have hk' : (K:ℝ) < A^24 + 1 := Nat.ceil_lt_add_one (by positivity)
  have hk2 : (K:ℝ)+2 ≤ A^25 := by
    rw [pow_succ]; nlinarith [show (1:ℝ) ≤ A^24 by exact one_le_pow₀ (by linarith) ]
  have hk0 : (0:ℝ) < K := lt_of_lt_of_le (by positivity) hk
  have hlk := Real.log_le_log hk0 (show (K:ℝ) ≤ A^25 by linarith)
  rw [Real.log_pow] at hlk
  have hln := Real.log_le_log (show (0:ℝ) < N by exact_mod_cast NeZero.pos N) hN
  change dist s _ ≤ 1/(26*Real.log A) at hs
  have hw := (le_div_iff₀ (by positivity : 0 < 26*Real.log A)).mp hs
  have hd : dist s (1+I*t) ≤ 1/26 := by nlinarith [mul_le_mul_of_nonneg_left ha (dist_nonneg (x:=s) (y:=1+I*t))]
  have hD : s ∈ (ball (2+I*t : ℂ) (7/4 : ℝ)) := by
    have H := dist_triangle s (1+I*t) (2+I*t)
    rw [dist_add_right] at H; norm_num [dist_eq_norm] at H hd ⊢; linarith
  apply (split_bound t χ hn hD K (U:=A^26) (by
    push_cast; rw [pow_succ A 25]; gcongr) (by
    rw [Real.log_pow]; have hv := abs_re_le_norm (s-(1+I*t))
    norm_num [sub_re, add_re, mul_re] at hv
    rw [dist_eq_norm] at hw
    norm_num only [Nat.cast_ofNat]
    apply le_trans _ hw
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    linarith [neg_le_abs (s.re-1)]) (by
    apply le_trans _ hk
    calc
      _ ≤ (A*A^2)^8 := by gcongr; exact Q_ge t
      _ = _ := by ring)).trans
  change _ ≤ C*Real.log A
  norm_num only [Nat.cast_ofNat] at hlk
  unfold C; have he := Real.exp_pos 1
  nlinarith [mul_le_mul_of_nonneg_left hln he.le, mul_le_mul_of_nonneg_left hlk he.le,
    mul_le_mul_of_nonneg_left ha (abs_nonneg tailC), le_abs_self tailC,
    mul_le_mul_of_nonneg_left ha he.le]

theorem deriv_bound {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hn : χ ≠ 1)
    {s : ℂ} (hs : dist s (1+I*t) ≤ 1/(52*Real.log (Q N t))) :
    ‖deriv χ.LFunction s‖ ≤ 52*C*(Real.log (Q N t))^2 := by
  have h := logQ_ge (N:=N) t
  let R := 1/(52*Real.log (Q N t))
  have hr : 0 < R := by dsimp [R]; positivity
  have H := norm_deriv_le_of_forall_mem_sphere_norm_le (f:=χ.LFunction) (c:=s) hr
    (DirichletCharacter.differentiable_LFunction hn).diffContOnCl (C:=C*Real.log (Q N t)) (by
      intro z hz; apply disk_bound t χ hn
      apply (dist_triangle z s _).trans
      rw [mem_sphere_iff_norm] at hz
      rw [dist_eq_norm z s, hz]; change R+_ ≤ _
      have hh : R+R = 1/(26*Real.log (Q N t)) := by dsimp [R]; ring
      rw [← hh]; gcongr)
  apply H.trans_eq; dsimp [R]; rw [div_div_eq_mul_div, div_one]; ring

private noncomputable def mean {N : ℕ} (χ : DirichletCharacter ℂ N) [NeZero N] : ℂ :=
  (∑ j : ZMod N, χ j) / N
private lemma mean_le {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : ‖mean χ‖ ≤ 1 := by
  have hn : (0:ℝ) < N := by exact_mod_cast NeZero.pos N
  rw [mean, norm_div, Complex.norm_natCast, div_le_iff₀ hn, one_mul]
  apply (norm_sum_le _ _).trans
  simpa using Finset.sum_le_sum (s:=Finset.univ) (fun (j : ZMod N) _ => χ.norm_le_one j)
private noncomputable def prim (N k : ℕ) (s : ℂ) : ℂ :=
  (((k*N:ℕ):ℂ)^(-s+1))/(-s+1)
private lemma prim_le {N k : ℕ} (hk : 0 < k*N) {s : ℂ} (hs : 1 < s.re) :
    ‖prim N k s‖ ≤ 1/‖-s+1‖ := by
  rw [prim,norm_div]; gcongr
  rw [← ofReal_natCast, norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hk)]
  apply Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hk); simp; linarith

private lemma error_le {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {s : ℂ} (hs : s ∈ (ball (2+I*t : ℂ) (7/4 : ℝ))) (hr : 1 < s.re) {k : ℕ} (hk : 1 ≤ k) :
    ‖characterLBlock χ k s - mean χ * (prim N (k+1) s - prim N k s)‖ ≤
    2*(4+|t|)*(N:ℝ)^2*(k:ℝ)^(-5/4:ℝ) := by
  let a : ℝ := (k*N:ℕ)
  let b : ℝ := ((k+1)*N:ℕ)
  let F := fun x : ℝ => (x:ℂ)^(-s)
  have hka : (k:ℝ) ≤ a := by dsimp [a]; exact_mod_cast (Nat.le_mul_of_pos_right k (NeZero.pos N))
  have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hab : b-a=N := by dsimp [a,b]; push_cast; ring
  have hn : (0:ℝ) < N := by exact_mod_cast NeZero.pos N
  have hab' : a ≤ b := by linarith
  have var (x : ℝ) (hx : x ∈ Icc a b) : ‖F x - F b‖ ≤ (4+|t|)*N*(k:ℝ)^(-5/4:ℝ) := by
    apply (norm_cpow_neg_sub_le t (hk1.trans (hka.trans hx.1)) hx.2 (hre t hs).le (hnorm t hs)).trans
    apply mul_le_mul (mul_le_mul_of_nonneg_left (by linarith [hx.1]) (by positivity))
      (Real.rpow_le_rpow_of_nonpos (by positivity) (hka.trans hx.1) (by norm_num)) (Real.rpow_nonneg (by linarith [hx.1]) _) (by positivity)
  let S := ∑ j : ZMod N, χ j
  have H1 : ‖characterLBlock χ k s-S*F b‖ ≤ N*((4+|t|)*N*(k:ℝ)^(-5/4:ℝ)) := by
    unfold characterLBlock; dsimp only [S]; rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _j : ZMod N, (4+|t|)*N*(k:ℝ)^(-5/4:ℝ) := by
        apply Finset.sum_le_sum; intro j _; rw [← mul_sub,norm_mul]
        apply (mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one j)).trans
        simpa only [F,ofReal_natCast] using var ((k*N+j.val:ℕ):ℝ) (by
          change _ ≤ _ ∧ _ ≤ _; dsimp [a,b]; exact_mod_cast (show k*N ≤ k*N+j.val ∧ k*N+j.val ≤ (k+1)*N by have := j.val_lt; constructor <;> nlinarith))
      _ = _ := by simp
  have intF : IntervalIntegrable F MeasureTheory.volume a b := by
    apply ContinuousOn.intervalIntegrable
    intro x hx; apply (hasDerivAt_ofReal_cpow_const (x:=x) _ _).continuousAt.continuousWithinAt
    · rw [uIcc_of_le hab'] at hx; linarith [hx.1]
    · intro H; have H' := congrArg Complex.re H; simp at H'; linarith
  have H2 := intervalIntegral.norm_integral_le_of_norm_le_const (a:=a) (b:=b) (f:=fun x => F b - F x) (C:=(4+|t|)*N*(k:ℝ)^(-5/4:ℝ)) (by
    intro x hx; rw [uIoc_of_le hab'] at hx; rw [norm_sub_rev]; exact var _ ⟨hx.1.le,hx.2⟩)
  rw [intervalIntegral.integral_sub intervalIntegrable_const intF, intervalIntegral.integral_const, hab,abs_of_pos hn] at H2
  have he : (∫ x in a..b, F x) = prim N (k+1) s - prim N k s := by
    dsimp only [F]; rw [integral_cpow (Or.inr ⟨by intro H; have hh := congrArg Complex.re H; simp at hh; linarith, by rw [uIcc_of_le hab']; intro hh; linarith [hh.1]⟩),sub_div]; simp [prim,a,b]
  rw [he, Complex.real_smul] at H2
  have he' : mean χ*(N:ℂ)=S := by dsimp [mean,S]; field_simp [NeZero.ne N]
  calc
    _ = ‖(characterLBlock χ k s-S*F b)+mean χ*((N:ℂ)*F b-(prim N (k+1) s-prim N k s))‖ := by congr 1; rw [← he']; ring
    _ ≤ _ := by apply (norm_add_le _ _).trans; rw [norm_mul]; have hm := mean_le χ; push_cast at H2; nlinarith [mul_le_of_le_one_left (norm_nonneg ((N:ℂ)*F b-(prim N (k+1) s-prim N k s))) hm]

private lemma sum_tail_bound {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {s : ℂ} (hs : s ∈ (ball (2+I*t : ℂ) (7/4 : ℝ))) (hr : 1 < s.re) (K m : ℕ) (hK : ((4+|t|)*(N:ℝ)^2)^8 ≤ K) :
    ‖∑ i ∈ Finset.range m, characterLBlock χ (K+1+i) s‖ ≤ 2*tailC+2/‖-s+1‖ := by
  let p := fun i => prim N (K+1+i) s
  let f := fun i => characterLBlock χ (K+1+i) s
  let e := fun i => f i-mean χ*(p (i+1)-p i)
  have err (i : ℕ) : ‖e i‖ ≤ 2*((i+1:ℕ):ℝ)^(-9/8:ℝ) := by
    let y : ℝ := ((K+1+i:ℕ):ℝ)
    have yp : 0 < y := by dsimp [y]; positivity
    have hy : (K:ℝ) ≤ y := by dsimp [y]; exact_mod_cast (by omega : K ≤ K+1+i)
    have hco : (4+|t|)*(N:ℝ)^2 ≤ y^(1/8:ℝ) := by
      have hh := Real.rpow_le_rpow (show 0 ≤ ((4+|t|)*(N:ℝ)^2)^8 by positivity) (hK.trans hy) (by norm_num : 0 ≤ (1/8:ℝ))
      rwa [← Real.rpow_natCast _ 8, ← Real.rpow_mul (by positivity), show (↑(8:ℕ):ℝ)*(1/8)=1 by norm_num, Real.rpow_one] at hh
    apply (error_le t χ hs hr (k:=K+1+i) (by omega)).trans
    change 2*(4+|t|)*(N:ℝ)^2*y^(-5/4:ℝ) ≤ _
    calc
      _ = 2*(((4+|t|)*(N:ℝ)^2)*y^(-5/4:ℝ)) := by ring
      _ ≤ 2*(y^(1/8:ℝ)*y^(-5/4:ℝ)) := by gcongr
      _ = 2*y^(-9/8:ℝ) := by rw [← Real.rpow_add yp]; norm_num
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos (by positivity) (by dsimp [y]; exact_mod_cast (by omega : i+1 ≤ K+1+i)) (by norm_num)) (by norm_num)
  have he : ‖∑ i ∈ Finset.range m, e i‖ ≤ 2*tailC := by
    apply (norm_sum_le _ _).trans; apply (Finset.sum_le_sum (fun i _ => err i)).trans
    rw [← Finset.mul_sum]; gcongr; exact tail_sum.sum_le_tsum _ (by intros; positivity)
  have hp (i : ℕ) : ‖p i‖ ≤ 1/‖-s+1‖ := prim_le (Nat.mul_pos (by omega) (NeZero.pos N)) hr
  have H : ‖mean χ*(p m-p 0)‖ ≤ 2/‖-s+1‖ := by
    rw [norm_mul]; apply (mul_le_of_le_one_left (norm_nonneg _) (mean_le χ)).trans
    apply (norm_sub_le _ _).trans
    apply (add_le_add (hp m) (hp 0)).trans_eq; ring
  have eqn : ∑ i ∈ Finset.range m, e i = ∑ i ∈ Finset.range m, f i-mean χ*(p m-p 0) := by
    dsimp only [e]; rw [Finset.sum_sub_distrib,← Finset.mul_sum, Finset.sum_range_sub]
  change ‖∑ i ∈ Finset.range m, f i‖ ≤ _
  rw [← sub_add_cancel (∑ i ∈ Finset.range m, f i) (mean χ*(p m-p 0)), ← eqn]
  exact (norm_add_le _ _).trans (add_le_add he H)

theorem right_bound {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hn1 : N ≠ 1)
    {s : ℂ} (hs : s ∈ (ball (2+I*t : ℂ) (7/4 : ℝ))) (hr : 1 < s.re) :
    ‖χ.LFunction s‖ ≤ 2*C*Real.log (Q N t) + 2/‖-s+1‖ := by
  let A := Q N t
  have hA : 4 ≤ A := by linarith [Q_ge (N:=N) t, abs_nonneg t]
  have ha : 1 ≤ Real.log A := logQ_ge t
  have hN : (N:ℝ) ≤ A := by dsimp [A,Q]; nlinarith [mul_nonneg (Nat.cast_nonneg (α:=ℝ) N) (abs_nonneg t)]
  let K := ⌈A^24⌉₊
  have hk : A^24 ≤ (K:ℝ) := Nat.le_ceil _
  have hk' : (K:ℝ) < A^24 + 1 := Nat.ceil_lt_add_one (by positivity)
  have hk2 : (K:ℝ)+2 ≤ A^25 := by
    rw [pow_succ]; nlinarith [show (1:ℝ) ≤ A^24 by exact one_le_pow₀ (by linarith) ]
  have hk0 : (0:ℝ) < K := lt_of_lt_of_le (by positivity) hk
  have hlk := Real.log_le_log hk0 (show (K:ℝ) ≤ A^25 by linarith)
  rw [Real.log_pow] at hlk
  have hln := Real.log_le_log (show (0:ℝ) < N by exact_mod_cast NeZero.pos N) hN
  let U := A^26
  have hU : ((K+2:ℕ):ℝ)*N ≤ U := by dsimp [U]; push_cast; rw [pow_succ A 25]; gcongr
  have h : (1-s.re)*Real.log U ≤ 1 := by
    apply le_trans (mul_nonpos_of_nonpos_of_nonneg (by linarith) (Real.log_nonneg (one_le_pow₀ (by linarith)))) (by norm_num)
  let f := fun k => ‖characterLBlock χ k s‖
  have hfirst := first χ hn1 (show (N:ℝ) ≤ U by apply le_trans _ hU; push_cast; nlinarith [Nat.cast_nonneg (α:=ℝ) K, Nat.cast_nonneg (α:=ℝ) N, mul_nonneg (Nat.cast_nonneg (α:=ℝ) K) (Nat.cast_nonneg (α:=ℝ) N)]) h
  have hmid : ∑ i ∈ Finset.range K, f (i+1) ≤ Real.exp 1 * (1+Real.log K) := by
    calc
      _ ≤ ∑ i ∈ Finset.range K, Real.exp 1 * (((i+1:ℕ):ℝ)⁻¹) := by
        apply Finset.sum_le_sum; intro i hi
        simpa only [div_eq_mul_inv, Nat.cast_add, Nat.cast_one] using middle χ i (s:=s) (U:=U) (by apply le_trans _ hU; gcongr; exact (Finset.mem_range.mp hi).le) h
      _ = Real.exp 1 * (harmonic K : ℝ) := by simp [harmonic, Finset.mul_sum]
      _ ≤ _ := by gcongr; exact harmonic_le_one_add_log K
  have hK : ((4+|t|)*(N:ℝ)^2)^8 ≤ K := by
    apply le_trans _ hk
    calc
      _ ≤ (A*A^2)^8 := by gcongr; exact Q_ge t
      _ = _ := by ring
  obtain ⟨he,hf⟩ := LFunction_eq_characterLBlockSeries_of_one_lt_re χ hn1 hr
  rw [he,characterLBlockSeries,← hf.sum_add_tsum_nat_add (K+1)]
  apply (norm_add_le _ _).trans
  have hpre := norm_sum_le (Finset.range (K+1)) (fun i => characterLBlock χ i s)
  change _ ≤ ∑ i ∈ Finset.range (K+1), f i at hpre
  rw [Finset.sum_range_succ' f K] at hpre; change f 0 ≤ _ at hfirst
  have H := ((summable_nat_add_iff (K+1)).mpr hf).tendsto_sum_tsum_nat.norm
  have ht := le_of_tendsto H (Eventually.of_forall (fun m => by simpa only [Nat.add_comm _ (K+1)] using sum_tail_bound t χ hs hr K m hK))
  change _ ≤ 2*C*Real.log A + _
  have HC : Real.exp 1 * (2*(1+Real.log N)+(1+Real.log K)) + 2*tailC ≤ 2*C*Real.log A := by
    norm_num only [Nat.cast_ofNat] at hlk
    unfold C; have he := Real.exp_pos 1
    nlinarith [mul_le_mul_of_nonneg_left hln he.le, mul_le_mul_of_nonneg_left hlk he.le,
      mul_le_mul_of_nonneg_left ha (abs_nonneg tailC), le_abs_self tailC,
      mul_le_mul_of_nonneg_left ha he.le]
  linarith

theorem doubled_bound {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hn : χ ≠ 1)
    {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) (ht : t ≠ 0) :
    ‖(χ^2).LFunction (1+x+2*I*t)‖ ≤ 2*C*Real.log (Q N (2*t)) + 1/|t| := by
  let s : ℂ := 1+x+2*I*t
  have hN : N ≠ 1 := by rintro rfl; exact hn (Subsingleton.elim _ _)
  have hr : 1 < s.re := by dsimp [s]; norm_num [add_re,mul_re,mul_im]; linarith
  have hs : s ∈ ball (2+I*(2*t:ℝ):ℂ) (7/4:ℝ) := by
    rw [mem_ball,dist_eq_norm]; have eqn : s-(2+I*(2*t:ℝ)) = ((x-1:ℝ):ℂ) := by dsimp [s]; push_cast; ring
    rw [eqn,norm_real,Real.norm_eq_abs,abs_of_nonpos (by linarith)]; linarith
  apply (right_bound (2*t) (χ^2) hN hs hr).trans; apply add_le_add le_rfl
  have hb := abs_im_le_norm (-s+1)
  have hi : (-s+1).im = -(2*t) := by dsimp [s]; norm_num [add_im,mul_im,mul_re]
  rw [hi, abs_neg,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)] at hb
  have htp := abs_pos.mpr ht
  exact (div_le_div_iff₀ (by linarith : 0 < ‖-s+1‖) htp).mpr (by linarith)

theorem strip_bounds {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hn : χ ≠ 1)
    (s : ℂ) (hs : |s.re-1| ≤ 1/(52*Real.log (Q N s.im))) :
    ‖χ.LFunction s‖ ≤ C*Real.log (Q N s.im) ∧
    ‖deriv χ.LFunction s‖ ≤ 52*C*(Real.log (Q N s.im))^2 := by
  have e : dist s (1+I*s.im) = |s.re-1| := by
    rw [dist_eq_norm]; have hh : s-(1+I*s.im) = ((s.re-1:ℝ):ℂ) := by apply Complex.ext <;> simp [mul_re,mul_im]
    rw [hh,norm_real,Real.norm_eq_abs]
  rw [← e] at hs
  refine ⟨disk_bound s.im χ hn (hs.trans ?_),deriv_bound s.im χ hn hs⟩
  have := logQ_ge (N:=N) s.im
  apply one_div_le_one_div_of_le (by positivity); linarith

end
end BVHeight

end

section
namespace BVShort
open Complex Metric DirichletCharacter BVHeight
private lemma Cnonneg : 0 ≤ C := by unfold C; positivity

theorem uniform_box {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hn : χ ≠ 1)
    {x r T L D M : ℝ} (hx : 0 < x) (hx1 : x ≤ 1/4) (hr : 0 < r) (hr1 : r ≤ 1/2)
    (_hL : 0 < L) (hD : 0 < D) (hM : 2 ≤ M) (hDM : D ≤ M)
    (hlog : ∀ t : ℝ, |t| ≤ 2*|T|+2 → Real.log (Q q t) ≤ L)
    (hnarrow : 3*x ≤ 1/(52*L)) (hsmall : 16*M^8*x < 1)
    (hder : 52*C*L^2 ≤ D) (hdbl : 2*C*L+1/r ≤ M)
    (hp : ‖LFunctionTrivChar q (1+x)‖ ≤ M/x)
    (hreal : χ^2 = 1 → 2*D*(x+r) ≤ ‖χ.LFunction 1‖)
    {s : ℂ} (hs : |s.re-1| ≤ x/2) (ht : |s.im| ≤ T) :
    χ.LFunction s ≠ 0 ∧ ‖deriv χ.LFunction s / χ.LFunction s‖ ≤ 2/x := by
  have hT := (abs_nonneg _).trans ht
  have H {z : ℂ} (a : |z.re-1| ≤ 3*x) (b : |z.im| ≤ 2*|T|+2) :=
    strip_bounds χ hn z (a.trans (hnarrow.trans (one_div_le_one_div_of_le
      (by have := logQ_ge (N:=q) z.im; positivity) (mul_le_mul_of_nonneg_left (hlog _ b) (by norm_num)))))
  have der {z : ℂ} (a : |z.re-1| ≤ 3*x) (b : |z.im| ≤ 2*|T|+2) : ‖deriv χ.LFunction z‖ ≤ D := by
    apply (H a b).2.trans; apply le_trans _ hder; gcongr; exact mul_nonneg (by norm_num) Cnonneg; exact (logQ_ge (N:=q) z.im).trans' (by norm_num); exact hlog _ b
  have b0 : |s.im| ≤ 2*|T|+2 := by rw [abs_of_nonneg hT]; linarith
  have ds := der (by linarith : |s.re-1| ≤ 3*x) b0
  by_cases low : χ^2 = 1 ∧ |s.im| ≤ r
  · let K := {z : ℂ | |z.re-1| ≤ x ∧ |z.im| ≤ r}
    have cv : Convex ℝ K := by
      intro a ha b hb u v hu hv huv
      obtain ⟨ha,ha'⟩ := ha; obtain ⟨hb,hb'⟩ := hb
      change |(u • a + v • b).re-1| ≤ x ∧ |(u • a + v • b).im| ≤ r
      simp only [add_re,add_im,smul_re,smul_im,smul_eq_mul]
      rw [show u*a.re+v*b.re-1=u*(a.re-1)+v*(b.re-1) by linear_combination huv]
      constructor <;> apply (abs_add_le ..).trans <;> rw [abs_mul, abs_mul,abs_of_nonneg hu,abs_of_nonneg hv]
      · calc _ ≤ u*x+v*x := by gcongr
             _ = x := by linear_combination x*huv
      · calc _ ≤ u*r+v*r := by gcongr
             _ = r := by linear_combination r*huv
    have dK : ∀ z ∈ K, ‖deriv χ.LFunction z‖ ≤ D := fun z hz => der (hz.1.trans (by linarith)) (hz.2.trans (by linarith [abs_nonneg T]))
    have oneK : (1:ℂ) ∈ K := by change |(1:ℂ).re-1| ≤ x ∧ |(1:ℂ).im| ≤ r; simpa using And.intro hx.le hr.le
    have sk : s ∈ K := ⟨hs.trans (by linarith),low.2⟩
    have lip := Convex.norm_image_sub_le_of_norm_deriv_le (fun z _ => (differentiable_LFunction hn z)) dK cv sk oneK
    have d : ‖1-s‖ ≤ x+r := by
      apply (norm_le_abs_re_add_abs_im _).trans
      simp only [sub_re,one_re,sub_im,one_im,zero_sub,abs_neg,abs_sub_comm 1 s.re]; linarith [low.2]
    have lo : D*(x+r) ≤ ‖χ.LFunction s‖ := by linarith [norm_sub_norm_le (χ.LFunction 1) (χ.LFunction s),mul_le_mul_of_nonneg_left d hD.le,hreal low.1]
    have pos : 0 < ‖χ.LFunction s‖ := lt_of_lt_of_le (by positivity) lo
    refine ⟨norm_pos_iff.mp pos, ?_⟩
    rw [norm_div,div_le_div_iff₀ pos hx]; nlinarith [mul_le_mul_of_nonneg_right ds hx.le,mul_pos hD hr]
  · let c : ℂ := 1+x+I*s.im
    have cr : c.re = 1+x := by simp [c,mul_re]
    have ci : c.im = s.im := by simp [c,mul_im]
    have dd : ∀ z ∈ closedBall c (3*x/2), ‖deriv χ.LFunction z‖ ≤ M := by
      intro z hz; rw [mem_closedBall,dist_eq_norm] at hz
      have a := (abs_re_le_norm (z-c)).trans hz; have b := (abs_im_le_norm (z-c)).trans hz
      rw [sub_re,cr] at a; rw [sub_im,ci] at b
      apply (der _ _).trans hDM
      · rw [abs_le] at a ⊢; constructor <;> linarith [a.1,a.2]
      · have := abs_add_le (z.im-s.im) s.im; rw [sub_add_cancel] at this; linarith [le_abs_self T]
    have hz : s ∈ closedBall c (3*x/2) := by
      rw [mem_closedBall,dist_eq_norm]; apply (norm_le_abs_re_add_abs_im _).trans; rw [sub_re,sub_im,cr,ci,sub_self,abs_zero,add_zero,abs_le]; rw [abs_le] at hs; constructor <;> linarith [hs.1,hs.2]
    have dbl : ‖(χ^2).LFunction (1+x+2*I*s.im)‖ ≤ M := by
      by_cases sq : χ^2 = 1
      · have rr : r < |s.im| := lt_of_not_ge (fun h => low ⟨sq,h⟩)
        apply (doubled_bound s.im χ hn hx (by linarith) (abs_pos.mp (hr.trans rr))).trans
        apply le_trans _ hdbl; apply add_le_add
        · exact mul_le_mul_of_nonneg_left (hlog _ (by rw [abs_mul]; norm_num; linarith [le_abs_self T])) (by positivity [Cnonneg])
        · exact one_div_le_one_div_of_le hr rr.le
      · let z : ℂ := 1+x+2*I*s.im
        have zr : z.re = 1+x := by simp [z,mul_re,mul_im]
        have zi : z.im = 2*s.im := by simp [z,mul_re,mul_im]
        have B := hlog z.im (by rw [zi,abs_mul]; norm_num; linarith [le_abs_self T])
        have V := (strip_bounds (χ^2) sq z (by rw [zr,add_sub_cancel_left,abs_of_pos hx]; apply le_trans (by linarith : x ≤ 1/(52*L)); apply one_div_le_one_div_of_le (by have := logQ_ge (N:=q) z.im; positivity); gcongr)).1
        apply V.trans; nlinarith [mul_le_mul_of_nonneg_left B Cnonneg, mul_nonneg Cnonneg _hL.le,one_div_pos.mpr hr]
    obtain ⟨a,b⟩ := local_disk χ hn hx (by linarith) hsmall hp dbl dd hz
    exact ⟨norm_pos_iff.mp (lt_trans (by positivity) a), b⟩
end BVShort

end

section
open Filter Real Complex Metric DirichletCharacter BVHeight
open scoped Topology
namespace BVShort
private noncomputable def E (t a : ℝ) := Real.exp (a*t)
private lemma Ep (t a : ℝ) : 0 < E t a := exp_pos _
private lemma Ea (t a b : ℝ) : E t (a+b) = E t a * E t b := by simp [E, add_mul,Real.exp_add]
private lemma En (t a : ℝ) : E t (-a) = (E t a)⁻¹ := by simp [E,Real.exp_neg]
private lemma Epow (t a : ℝ) (n : ℕ) : E t a ^ n = E t (n*a) := by simp [E,mul_assoc,Real.exp_nat_mul]
private lemma Edom (a b K k : ℝ) (hab : a < b) (hk : 0 < k) :
    ∀ᶠ t : ℝ in atTop, K*E t a < k*E t b := by
  have hh := (Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (sub_pos.mpr hab))).eventually (eventually_gt_atTop (K/k))
  filter_upwards [hh] with t ht
  change K/k < E t (b-a) at ht
  have h := mul_lt_mul_of_pos_right ((div_lt_iff₀ hk).mp ht) (Ep t a)
  rwa [mul_right_comm,←Ea,sub_add_cancel,mul_comm (E t b)] at h
private lemma ln_budget (A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    ∀ᶠ t : ℝ in atTop, ∀ (q : ℕ), (q:ℝ) ≤ E t B → ∀ y : ℝ,
    |y| ≤ 2*|E t A|+2 → Real.log (Q q y) ≤ E t (1/256) := by
  have hh := (isLittleO_pow_exp_pos_mul_atTop 1 (by norm_num : (0:ℝ)<1/256)).def (show 0 < 1/(A+B+8) by positivity)
  filter_upwards [hh,eventually_ge_atTop (1:ℝ)] with t ht ht1
  have ha : 1 ≤ E t A := Real.one_le_exp (by positivity)
  have hb : 1 ≤ E t B := Real.one_le_exp (by positivity)
  intro q hq y hy
  rw [abs_of_pos (Ep ..)] at hy
  have H : Q q y ≤ 8 * (E t A*E t B) := by unfold Q; nlinarith [mul_le_mul_of_nonneg_right hq (by positivity : 0 ≤ 2+|y|),mul_le_mul_of_nonneg_right hy (Ep t B).le,mul_le_mul_of_nonneg_right ha (Ep t B).le]
  have H' := Real.log_le_log (by unfold Q; positivity) H
  rw [← Ea, Real.log_mul (by norm_num) (Ep ..).ne', E,Real.log_exp] at H'
  simp only [pow_one] at ht
  change ‖t‖ ≤ (1/(A+B+8))*‖E t (1/256)‖ at ht
  rw [Real.norm_eq_abs,abs_of_pos (by linarith),Real.norm_eq_abs,abs_of_pos (Ep ..),one_div_mul_eq_div] at ht
  have h := (le_div_iff₀ (by positivity)).mp ht
  linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<8)]
private lemma Ep0 (t : ℝ) : E t 0 = 1 := by simp [E]
open BombieriVinogradov.SiegelWalfisz in
private theorem scaled (A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    ∀ᶠ t : ℝ in atTop, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → χ.IsPrimitive →
      (q:ℝ) ≤ E t B → ∀ s : ℂ, |s.re-1| ≤ E t (-1/2) → |s.im| ≤ E t A →
      χ.LFunction s ≠ 0 ∧ ‖deriv χ.LFunction s / χ.LFunction s‖ ≤ E t (1/2) := by
  have he : 0 < 1/(128*B) := by positivity
  obtain ⟨k,hk,hS⟩ := siegelLowerBound _ he
  have p : Tendsto (fun t => 1+E t (-1/3)) atTop (𝓝[>] 1) := by
    apply tendsto_nhdsWithin_iff.mpr; constructor
    · simpa [E] using (Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by norm_num : (-1/3:ℝ)<0))).const_add 1
    · exact Eventually.of_forall (fun t => show 1 < 1+E t (-1/3) by linarith [Ep t (-1/3)])
  filter_upwards [p.eventually principal_uniform,ln_budget A B hA hB,
    Edom (-1/3) 0 1 (1/4) (by norm_num) (by norm_num), Edom (-1/32) 0 1 (1/2) (by norm_num) (by norm_num),
    Edom 0 (1/28) 2 1 (by norm_num) (by norm_num), Edom (1/64) (1/28) 1 1 (by norm_num) (by norm_num),
    Edom (-1/3+1/256) 0 156 1 (by norm_num) (by norm_num),
    Edom (8*(1/28)-1/3) 0 16 1 (by norm_num) (by norm_num),
    Edom (2*(1/256)) (1/64) (52*C) 1 (by norm_num) (by norm_num),
    Edom (1/256) (1/28) (2*C) (1/2) (by norm_num) (by norm_num),
    Edom (1/32) (1/28) 1 (1/2) (by norm_num) (by norm_num),
    Edom (1/64-1/3) (-1/128) 2 (k/2) (by norm_num) (by positivity),
    Edom (1/64-1/32) (-1/128) 2 (k/2) (by norm_num) (by positivity),
    Edom (-1/2) (-1/3) 2 1 (by norm_num) (by norm_num), Edom (1/3) (1/2) 2 1 (by norm_num) (by norm_num)] with t hp hlog hx hr hM hDM hna hsm hd hdb1 hdb2 hs1 hs2 hw hfin
  simp only [Ep0,one_mul,mul_one] at *
  intro q _ χ hn hpr hq s hs ht
  have IX (a : ℝ) : 1 / E t (-a) = E t a := by rw [En,one_div,inv_inv]
  obtain ⟨a,b⟩ := uniform_box χ hn (x:=E t (-1/3)) (r:=E t (-1/32)) (T:=E t A) (L:=E t (1/256)) (D:=E t (1/64)) (M:=E t (1/28)) (Ep ..) hx.le (Ep ..) hr.le (Ep ..) (Ep ..) hM.le hDM.le (hlog _ hq) (by
    apply (le_div_iff₀ (mul_pos (by norm_num) (Ep ..))).mpr; rw [Ea] at hna; linarith) (by
    rw [Epow]; norm_num only [Nat.cast_ofNat]; rw [sub_eq_add_neg,Ea] at hsm; linarith) (by simpa only [Epow,Nat.cast_ofNat] using hd.le) (by
    rw [show (-1/32:ℝ) = -(1/32) by ring,IX]; linarith) (by
    have H := hp q; rw [add_sub_cancel_left] at H; push_cast at H; exact H.trans (div_le_div_of_nonneg_right hM.le (Ep ..).le)) (by
    intro sq; have h := hS q χ (three_le_level_of_ne_one χ hn) hpr sq hn
    have pow := Real.rpow_le_rpow_of_nonpos (show 0 < (q:ℝ) by exact_mod_cast NeZero.pos q) hq (neg_nonpos.mpr he.le)
    have e : (E t B)^(-(1/(128*B))) = E t (-1/128) := by unfold E; rw [← Real.exp_mul]; congr 1; field_simp
    rw [e] at pow
    have z := le_trans (mul_le_mul_of_nonneg_left pow hk.le) (h.trans (re_le_norm _))
    rw [sub_eq_add_neg,Ea] at hs1 hs2
    norm_num only [neg_div] at *; nlinarith) (by linarith) ht
  refine ⟨a,b.trans ?_⟩
  rw [div_eq_mul_one_div, show (-1/3:ℝ) = -(1/3) by ring, IX]; exact hfin.le

theorem log_strip (A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    ∀ᶠ X : ℝ in atTop, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → χ.IsPrimitive →
      (q:ℝ) ≤ (Real.log X)^B → ∀ s : ℂ, |s.re-1| ≤ 1/Real.sqrt (Real.log X) → |s.im| ≤ (Real.log X)^A →
      χ.LFunction s ≠ 0 ∧ ‖deriv χ.LFunction s / χ.LFunction s‖ ≤ Real.sqrt (Real.log X) := by
  filter_upwards [(Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually (scaled A B hA hB),eventually_gt_atTop (1:ℝ)] with X hx hX
  have e (a : ℝ) : E (Real.log (Real.log X)) a = (Real.log X)^a := by rw [Real.rpow_def_of_pos (Real.log_pos hX),mul_comm]; rfl
  change ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), _ at hx
  simp only [Function.comp_apply, e] at hx
  rw [Real.sqrt_eq_rpow]; have en : (-1/2:ℝ) = -(1/2) := by ring
  simpa only [en,Real.rpow_neg (Real.log_pos hX).le,one_div] using hx
end BVShort

end

section

open Complex Set Filter DirichletCharacter
open BombieriVinogradov.SiegelWalfisz
namespace BVRect
lemma shift {n q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hn : 2 < n) (hχ : χ ≠ 1)
    {a b T M : ℝ} (ha : 0 < a) (hab : a ≤ b) (hT : 0 < T) (hM : 0 ≤ M)
    (H : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → |s.im| ≤ T → χ.LFunction s ≠ 0 ∧ ‖deriv χ.LFunction s / χ.LFunction s‖ ≤ M) :
    ‖explicitFormulaVerticalIntegral χ n b T‖ ≤
    2*T*(M*(n:ℝ)^a/a) + 2*(b-a)*(M*(n:ℝ)^b/T) := by
  let f := explicitFormulaIntegrand χ n
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hn0 : (n:ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have ht : -T ≤ T := by linarith
  have hd := differentiable_LFunction hχ
  have E : RectangleIntegral f (a + (-T:ℝ)*I) (b + T*I) = 0 := by
    apply HolomorphicOn.vanishesOnRectangle (U := Rectangle _ _) _ (Subset.rfl)
    intro s hs
    have hs' : s.re ∈ Icc a b ∧ s.im ∈ Icc (-T) T := by
      simp [Rectangle,uIcc_of_le,hab,ht] at hs
      exact hs
    have nz := (H s hs'.1.1 hs'.1.2 (abs_le.mpr hs'.2)).1
    have sz : s ≠ 0 := fun e => by simp [e] at hs'; linarith [hs'.1.1]
    apply ((hd.deriv.differentiableAt.div (hd s) nz).differentiableWithinAt.mul _)
    apply DifferentiableWithinAt.neg
    change DifferentiableWithinAt ℂ (perronKernelIntegrand (n:ℝ)) _ s
    exact (holomorphicOn_perronKernelIntegrand (show 0 < (n:ℝ) by positivity) s
      (ha.trans_le hs'.1.1)).mono (by intro z hz; simp [Rectangle,uIcc_of_le,hab,ht] at hz; exact ha.trans_le hz.1.1)
  simp [RectangleIntegral] at E
  have e : VIntegral f b (-T) T = VIntegral f a (-T) T + HIntegral f a b T - HIntegral f a b (-T) := by linear_combination E
  have normF (s : ℂ) (h1 : a ≤ s.re) (h2 : s.re ≤ b) (h3 : |s.im| ≤ T) :
      ‖f s‖ ≤ M*(n:ℝ)^s.re/‖s‖ := by
    simp only [f, explicitFormulaIntegrand,logDeriv_apply,norm_mul,norm_neg,norm_div,
      Complex.norm_natCast_cpow_of_re_ne_zero n (ne_of_gt (ha.trans_le h1)),mul_div_assoc]
    gcongr
    simpa only [norm_div] using (H s h1 h2 h3).2
  have hor (t : ℝ) (ht' : |t| = T) : ‖HIntegral f a b t‖ ≤ (M*(n:ℝ)^b/T)*(b-a) := by
    apply (intervalIntegral.norm_integral_le_of_norm_le_const _).trans_eq
    · rw [abs_of_nonneg (sub_nonneg.mpr hab)]
    · intro u hu
      rw [uIoc_of_le hab] at hu
      let z : ℂ := u+t*I
      have zr : z.re = u := by simp [z]
      have zi : z.im = t := by simp [z]
      have hz := normF z (zr ▸ hu.1.le) (zr ▸ hu.2) (by rw [zi,ht'])
      have hden : T ≤ ‖z‖ := by simpa [zi,ht'] using abs_im_le_norm z
      apply hz.trans
      rw [zr]; gcongr; exact hu.2
  have ver : ‖VIntegral f a (-T) T‖ ≤ (M*(n:ℝ)^a/a)*(T- -T) := by
    rw [VIntegral,norm_smul,norm_I,one_mul]
    apply (intervalIntegral.norm_integral_le_of_norm_le_const _).trans_eq
    · rw [abs_of_nonneg (sub_nonneg.mpr ht)]
    · intro t ht'
      rw [uIoc_of_le ht] at ht'
      let z : ℂ := a+t*I
      have zr : z.re = a := by simp [z]
      have hz := normF z zr.ge (zr.trans_le hab) (by simpa [z] using abs_le.mpr ⟨ht'.1.le,ht'.2⟩)
      exact hz.trans (by rw [zr]; gcongr; simpa [zr] using re_le_norm z)
  change ‖(1/(2*Real.pi*I):ℂ) • VIntegral f b (-T) T‖ ≤ _
  have hpi : ‖(1/(2*Real.pi*I):ℂ)‖ ≤ 1 := by
    simp [abs_of_pos Real.pi_pos]; apply mul_le_one₀ _ (by positivity) (by norm_num); exact inv_le_one_of_one_le₀ (by linarith [Real.pi_gt_three])
  rw [norm_smul,e]
  apply (mul_le_of_le_one_left (norm_nonneg _) hpi).trans
  calc
    _ ≤ (‖VIntegral f a (-T) T‖ + ‖HIntegral f a b T‖) + ‖HIntegral f a b (-T)‖ :=
      (norm_sub_le ..).trans (by gcongr; exact norm_add_le ..)
    _ ≤ _ := by linarith [ver,hor T (abs_of_pos hT),hor (-T) (by simp [abs_of_pos hT])]
end BVRect
open Filter Real Complex DirichletCharacter
open BombieriVinogradov.SiegelWalfisz
namespace BVRect
lemma power_absorb (k : ℝ) : ∀ᶠ x : ℝ in atTop, x^k ≤ Real.exp x := by
  filter_upwards [(tendsto_exp_div_rpow_atTop k).eventually_ge_atTop 1, eventually_gt_atTop (0:ℝ)] with x hx hx0
  exact (one_mul _).symm.le.trans ((le_div_iff₀ (Real.rpow_pos_of_pos hx0 k)).mp hx)
lemma scalar (A : ℝ) (_hA : 0 < A) : ∀ᶠ n : ℕ in atTop,
    let L := Real.log n
    let a := 1-1/Real.sqrt L
    let T := L^(A+5)
    0 < a ∧ a ≤ optimizedPerronLine n ∧ 0 < T ∧ 0 ≤ L ∧
    2*T*(L*(n:ℝ)^a/a) ≤ 4*n/L^A ∧
    2*(optimizedPerronLine n-a)*(L*(n:ℝ)^(optimizedPerronLine n)/T) ≤ 4*Real.exp 1*n/L^A ∧
    (n:ℝ)*Real.log (2*(n:ℝ))^2/T ≤ 4*n/L^A ∧ L ≤ n/L^A := by
  have lim := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have slim := Real.tendsto_sqrt_atTop.comp lim
  filter_upwards [slim.eventually_ge_atTop 2, lim.eventually_ge_atTop 4,
    slim.eventually (power_absorb (2*(2*A+6))),lim.eventually (power_absorb (A+1)), eventually_gt_atTop 2] with n hs hL hpow hend hn
  let L := Real.log (n:ℝ)
  let r := Real.sqrt L
  change 2 ≤ r at hs
  change 4 ≤ L at hL
  have hL0 : 0 < L := by linarith
  have hr : 0 < r := by linarith
  have hrr : r^2 = L := Real.sq_sqrt hL0.le
  have hn0 : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
  have ha : 1/2 ≤ 1-1/r := by apply sub_le_sub_left (show 1/r ≤ 1/2 by gcongr) 1 |>.trans' (by norm_num)
  have ha0 : 0 < 1-1/r := by linarith
  have hb := optimizedPerronLine_le_two hn
  have he : (n:ℝ)^(1-1/r) = n/Real.exp r := by
    rw [Real.rpow_def_of_pos hn0]; change Real.exp (L*(1-1/r)) = _
    have : L*(1-1/r)=L-r := by field_simp; nlinarith [hrr]
    rw [this,Real.exp_sub,Real.exp_log hn0]
  have p : L^(2*A+6) ≤ Real.exp r := by
    rw [← hrr, ← Real.rpow_natCast, ← Real.rpow_mul hr.le]; exact hpow
  let D := L^A
  have dpos : 0 < D := Real.rpow_pos_of_pos hL0 _
  have te : L^(A+5) = D*L^5 := by simp [D,Real.rpow_add hL0]
  have pe : D^2*L^6 ≤ Real.exp r := by
    convert p using 1
    rw [Real.rpow_add hL0, mul_comm 2 A,Real.rpow_mul hL0.le];simp [D]
  have l1 : 1 ≤ L := by linarith
  have l5 : L ≤ L^5 := by simpa using pow_le_pow_right₀ l1 (show 1 ≤ 5 by decide)
  have l25 : L^2 ≤ L^5 := pow_le_pow_right₀ l1 (by decide)
  have hl2 : Real.log (2*(n:ℝ))^2 ≤ 4*L^2 := by
    rw [Real.log_mul (by norm_num) hn0.ne']; change (Real.log 2+L)^2 ≤ _
    have log2 : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
    nlinarith [log2, Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2), sq_nonneg (L-Real.log 2),mul_nonneg (show 0 ≤ L-Real.log 2 by linarith [log2]) (show 0 ≤ 3*L+Real.log 2 by positivity)]
  dsimp only
  change 0 < 1-1/r ∧ _
  refine ⟨ha0, (show 1-1/r ≤ 1 by linarith [one_div_pos.mpr hr]).trans (optimizedPerronLine_gt_one hn).le, Real.rpow_pos_of_pos hL0 _,hL0.le,?_,?_,?_,?_⟩
  · change 2*L^(A+5)*(L*(n:ℝ)^(1-1/r)/(1-1/r)) ≤ 4*n/D
    rw [te,he]; apply (le_div_iff₀ dpos).mpr
    rw [mul_div_assoc', ← mul_div_right_comm, div_le_iff₀ ha0]
    field_simp [ne_of_gt (Real.exp_pos r)]
    nlinarith only [mul_le_mul_of_nonneg_right pe hr.le,mul_nonneg (sub_nonneg.mpr hs) (Real.exp_pos r).le]
  · change 2*(_-(1-1/r))*(L*_ / L^(A+5)) ≤ _ / D
    rw [te,rpow_optimizedPerronLine_eq hn]; field_simp
    nlinarith only [mul_le_mul_of_nonneg_right hb hr.le,hs,mul_le_mul_of_nonneg_left (show 1 ≤ L^4 from one_le_pow₀ l1) hr.le]
  · change (n:ℝ)*_ / L^(A+5) ≤ _ / D
    rw [te]; field_simp
    rw [mul_comm (n:ℝ) 2]; linarith
  · apply (le_div_iff₀ dpos).mpr
    change L^(A+1) ≤ Real.exp L at hend
    simpa [Real.rpow_add hL0,Real.exp_log hn0,D,mul_comm,L] using hend
end BVRect
open Filter Complex DirichletCharacter
open BombieriVinogradov.SiegelWalfisz
namespace BVRect

def Strip : Prop := ∀ A B : ℝ, 0 < A → 0 < B → ∀ᶠ n : ℕ in atTop,
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → χ ≠ 1 →
  (q:ℝ) ≤ (Real.log n)^B → ∀ s : ℂ, 1-1/Real.sqrt (Real.log n) ≤ s.re →
  s.re ≤ 1+1/Real.log n → |s.im| ≤ (Real.log n)^(A+5) →
  χ.LFunction s ≠ 0 ∧ ‖deriv χ.LFunction s / χ.LFunction s‖ ≤ Real.log n
open Finset in
lemma endpoint {n q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hn : 1 ≤ n) :
  ‖∑ k ∈ Icc 1 n, (ArithmeticFunction.vonMangoldt k:ℂ)*χ k‖ ≤
  ‖characterChebyshevHalfSum n χ‖ + Real.log n := by
  classical
  let f := twistedMangoldtSequence χ
  have e : Finset.Icc 1 n = insert n (Finset.Ico 1 n) := by ext k; simp; omega
  have eq : ∑ k ∈ Icc 1 n, (ArithmeticFunction.vonMangoldt k:ℂ)*χ k = characterChebyshevHalfSum n χ + (1/2:ℂ)*f n := by
    rw [e,sum_insert (by simp),characterChebyshevHalfSum]; simp only [f,twistedMangoldtSequence]; simp_rw [mul_comm (ArithmeticFunction.vonMangoldt _:ℂ)]; ring_nf; rfl
  rw [eq]; apply (norm_add_le ..).trans; gcongr
  rw [norm_mul]; apply (mul_le_of_le_one_left (norm_nonneg _) (by norm_num)).trans
  exact (norm_twistedMangoldtSequence_le_vonMangoldt χ n).trans ArithmeticFunction.vonMangoldt_le_log

end BVRect

end

end

section
namespace TotientPerron
open Real Filter Finset

theorem away_from_one {x n U : ℝ} (hx : 0<x) (hn : 0<n) (hU : 2≤U)
    (far : x/U < |n-x|) : 1/(2*U) ≤ |log (x/n)| := by
  have up : 0<U := by linarith
  by_cases cmp : n≤x
  · rw [abs_of_nonpos (sub_nonpos.mpr cmp)] at far
    have logs := Real.log_le_sub_one_of_pos (div_pos hn hx)
    rw [Real.log_div hx.ne' hn.ne',abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hn cmp))]
    rw [Real.log_div hn.ne' hx.ne'] at logs
    have bound : 1/(2*U) ≤ (x-n)/x := by
      rw [div_le_div_iff₀ (by positivity) hx]
      have room := (div_lt_iff₀ up).mp far
      nlinarith
    rw [sub_div, div_self hx.ne'] at bound
    linarith
  · have cmp' : x≤n := (lt_of_not_ge cmp).le
    rw [abs_of_nonneg (sub_nonneg.mpr cmp')] at far
    have logs := Real.log_le_sub_one_of_pos (div_pos hx hn)
    rw [Real.log_div hx.ne' hn.ne'] at logs ⊢
    rw [abs_of_nonpos (sub_nonpos.mpr (Real.log_le_log hx cmp'))]
    have bound : 1/(2*U) ≤ (n-x)/n := by
      rw [div_le_div_iff₀ (by positivity) hn]
      have room := (div_lt_iff₀ up).mp far
      nlinarith [mul_nonneg (sub_nonneg.mpr cmp') (show 0≤U-1 by linarith)]
    rw [sub_div, div_self hn.ne'] at bound
    linarith

theorem localized_error {x n c U : ℝ} (hx : 0<x) (hn : 0<n)
    (hc : 1<c) (hc' : c≤2) (hU : 2≤U) (close : |n-x| ≤ x/U) :
    (if x/n = 1 then c/(Real.pi*U^2) else
      (x/n)^c * min 1 (1/(Real.pi*U^2*|Real.log (x/n)|))) ≤ 4 := by
  have up : 0<U := by linarith
  have const : x/U ≤ x/2 := div_le_div_of_nonneg_left hx.le (by norm_num) hU
  have left := (abs_le.mp close).1
  have small : x/n ≤ 2 := (div_le_iff₀ hn).mpr (by linarith)
  split_ifs
  · apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [Real.pi_gt_three, mul_le_mul_of_nonneg_right Real.pi_gt_three.le (sq_nonneg U),
      sq_nonneg (U-2)]
  · calc
      _ ≤ (x/n)^c*1 := mul_le_mul_of_nonneg_left (min_le_left ..) (Real.rpow_nonneg (by positivity) _)
      _ ≤ (2:ℝ)^c := by simpa using Real.rpow_le_rpow (by positivity) small (zero_le_one.trans hc.le)
      _ ≤ (2:ℝ)^(2:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hc'
      _ = 4 := by norm_num

theorem away_error {x n c U : ℝ} (hx : 0<x) (hn : 0<n) (hU : 2≤U)
    (far : x/U < |n-x|) :
    (if x/n = 1 then c/(Real.pi*U^2) else
      (x/n)^c * min 1 (1/(Real.pi*U^2*|Real.log (x/n)|))) ≤ (x/n)^c*(2/U) := by
  have up : 0<U := by linarith
  have sep := away_from_one hx hn hU far
  have lg : 0 < |Real.log (x/n)| := (by positivity : 0<(1:ℝ)/(2*U)).trans_le sep
  have ratio : x/n ≠ 1 := by intro e; simp [e] at lg
  rw [if_neg ratio]
  refine mul_le_mul_of_nonneg_left ((min_le_right ..).trans ?_) (Real.rpow_nonneg (by positivity) _)
  apply (div_le_div_iff₀ (by positivity) up).mpr
  have one := (div_le_iff₀ (by positivity : 0<2*U)).mp sep
  calc
    1*U ≤ 2*(U^2*|Real.log (x/n)|) := by nlinarith [mul_le_mul_of_nonneg_right one up.le]
    _ ≤ 2*(Real.pi*U^2*|Real.log (x/n)|) := by
      have aux := mul_le_mul_of_nonneg_right (show (1:ℝ)≤Real.pi by linarith [Real.pi_gt_three])
        (mul_nonneg (sq_nonneg U) lg.le)
      linarith only [show U^2*|Real.log (x/n)| ≤ Real.pi*U^2*|Real.log (x/n)| by simpa [mul_assoc] using aux]
end TotientPerron
end

section
namespace TotientPerron
open Real Filter Finset

theorem near_membership {x n : ℕ} {U : ℝ} (near : |(n:ℝ)-x| ≤ (x:ℝ)/U) :
    n ∈ Icc (x - ⌊(x:ℝ)/U⌋₊) (x + ⌊(x:ℝ)/U⌋₊) := by
  rw [mem_Icc]
  by_cases order : n≤x
  · have d : x-n≤⌊(x:ℝ)/U⌋₊ := by
      apply Nat.le_floor
      rw [Nat.cast_sub order]
      rw [abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast order))] at near
      linarith
    omega
  · have order' : x≤n := by omega
    have d : n-x≤⌊(x:ℝ)/U⌋₊ := by
      apply Nat.le_floor
      rw [Nat.cast_sub order']
      rwa [abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast order'))] at near
    omega

theorem close_of_mem {x n : ℕ} {U : ℝ} (hU : 2≤U)
    (inside : n ∈ Icc (x - ⌊(x:ℝ)/U⌋₊) (x + ⌊(x:ℝ)/U⌋₊)) :
    |(n:ℝ)-x| ≤ (x:ℝ)/U := by
  let d := ⌊(x:ℝ)/U⌋₊
  have df : (d:ℝ) ≤ (x:ℝ)/U := Nat.floor_le (by positivity)
  obtain ⟨lo, hi⟩ := mem_Icc.mp inside
  change x-d ≤ n at lo
  change n≤x+d at hi
  have low : x≤n+d := by omega
  have l : (x:ℝ) ≤ n+d := by exact_mod_cast low
  have h : (n:ℝ) ≤ x+d := by exact_mod_cast hi
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem window_card {x : ℕ} {U : ℝ} (hU : 2≤U) (hx : U≤x) :
    ((Icc (x - ⌊(x:ℝ)/U⌋₊) (x+⌊(x:ℝ)/U⌋₊)).card : ℝ) ≤ 3*((x:ℝ)/U) := by
  have up : 0<U := by linarith
  let d := ⌊(x:ℝ)/U⌋₊
  have dcap : (d:ℝ) ≤ (x:ℝ)/U := Nat.floor_le (by positivity)
  have xd : (x:ℝ)/U ≤ x := div_le_self (Nat.cast_nonneg _) (by linarith)
  have le : d≤x := by exact_mod_cast dcap.trans xd
  have count : (Icc (x-d) (x+d)).card = 2*d+1 := by rw [Nat.card_Icc]; omega
  change ((Icc (x-d) (x+d)).card : ℝ) ≤ _
  rw [count]
  push_cast
  have : 1 ≤ (x:ℝ)/U := (one_le_div up).mpr hx
  linarith

/-- The finitely many terms near the endpoint and a summable majorant elsewhere. -/
theorem tsum_upper {W : Finset ℕ} {f g : ℕ → ℝ} {C : ℝ} (hf : Summable f)
    (hg : Summable g) (gn : ∀ n, 0 ≤ g n)
    (near : ∀ n ∈ W, f n ≤ C) (far : ∀ n ∉ W, f n ≤ g n) :
    ∑' n, f n ≤ W.card*C + ∑' n,g n := by
  let a (n : ℕ) : ℝ := if n ∈ W then C else 0
  have sum : Summable a := summable_of_ne_finset_zero (s:=W) (by intro n nn; simp [a,nn])
  have bound (n : ℕ) : f n ≤ a n + g n := by
    by_cases mem : n∈W
    · simpa only [a,if_pos mem] using (near n mem).trans (le_add_of_nonneg_right (gn n))
    · simpa only [a,if_neg mem,zero_add] using far n mem
  have v := hf.tsum_le_tsum bound (sum.add hg)
  have value : ∑' n, a n = W.card*C := by
    rw [tsum_eq_sum (s:=W) (fun n nn => by simp [a,nn])]
    rw [sum_congr rfl (fun n hn => show a n=C by simp [a,hn]),sum_const,nsmul_eq_mul]
  rwa [sum.tsum_add hg,value] at v
end TotientPerron
end

section
namespace TotientPerron
open Real Finset
open scoped ArithmeticFunction.vonMangoldt
open BombieriVinogradov.SiegelWalfisz

/-- A coarser truncation bound, uniform in the character, suffices when the height
is allowed to be an arbitrarily large fixed power of the logarithm. -/
theorem coarse_truncation : ∃ C : ℝ, 0<C ∧ ∀ {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (x : ℕ) (_hx : 2<x) (U : ℝ), 2≤U → U≤x →
    ‖explicitFormulaVerticalIntegral χ x (optimizedPerronLine x) (U^2) -
      characterChebyshevHalfSum x χ‖ ≤ C*x*Real.log (2*(x:ℝ))/U := by
  obtain ⟨K,hK,lseries⟩ := exists_vonMangoldtLSeriesNormSum_le_div_le_three
  refine ⟨12+2*Real.exp 1*K,by positivity,?_⟩
  intro N _ χ x hx U hU ux
  let c := optimizedPerronLine x
  have cpos : 1<c := optimizedPerronLine_gt_one hx
  have ctwo : c≤2 := optimizedPerronLine_le_two hx
  have up : 0<U := by linarith
  have xn : 0<x := by omega
  have xp : 0<(x:ℝ) := by exact_mod_cast xn
  have ln := one_le_log_natCast hx
  have lc : log (x:ℝ) ≤ log (2*(x:ℝ)) := log_le_log xp (by linarith)
  let W := Icc (x-⌊(x:ℝ)/U⌋₊) (x+⌊(x:ℝ)/U⌋₊)
  let f := sourcePerronErrorMajorantTerm x c (U^2)
  let wt (n : ℕ) : ℝ := Λ n/(n:ℝ)^c
  let g (n : ℕ) : ℝ := ((2/U)*(x:ℝ)^c)*wt n
  have sumwt : Summable wt := by
    have S := (ArithmeticFunction.LSeriesSummable_vonMangoldt (s:=(c:ℂ)) (by simpa using cpos)).norm
    simpa only [wt,norm_LSeriesTerm_vonMangoldt_eq] using S
  have sumg : Summable g := sumwt.mul_left _
  have gpos (n : ℕ) : 0 ≤ g n := by dsimp [g,wt]; positivity [ArithmeticFunction.vonMangoldt_nonneg (n:=n)]
  have near (n : ℕ) (inside : n∈W) : f n ≤ 4*log (2*(x:ℝ)) := by
    have cl := close_of_mem hU inside
    simp only [f,sourcePerronErrorMajorantTerm]
    by_cases nz : n=0
    · rw [if_pos nz]; linarith
    rw [if_neg nz]
    have np : 0 < (n:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero nz
    have nl : (n:ℝ) ≤ 2*(x:ℝ) := by
      have b := (abs_le.mp cl).2
      have d := div_le_self xp.le (show 1≤U by linarith)
      linarith
    have coef := (ArithmeticFunction.vonMangoldt_le_log (n:=n)).trans (log_le_log np nl)
    calc
      _ ≤ Λ n * 4 := mul_le_mul_of_nonneg_left (localized_error xp np cpos ctwo hU cl)
        ArithmeticFunction.vonMangoldt_nonneg
      _ ≤ _ := by linarith
  have far (n : ℕ) (outside : n∉W) : f n ≤ g n := by
    have sep : (x:ℝ)/U < |(n:ℝ)-x| := lt_of_not_ge fun close => outside (near_membership close)
    simp only [f,sourcePerronErrorMajorantTerm]
    by_cases nz : n=0
    · rw [if_pos nz]; exact gpos n
    rw [if_neg nz]
    have np : 0 < (n:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero nz
    calc
      _ ≤ Λ n * (((x:ℝ)/n)^c*(2/U)) :=
        mul_le_mul_of_nonneg_left (away_error xp np hU sep) ArithmeticFunction.vonMangoldt_nonneg
      _ = g n := by dsimp [g,wt]; rw [Real.div_rpow xp.le np.le]; ring
  have split := tsum_upper (W:=W) (summable_sourcePerronErrorMajorantTerm xn cpos (sq_pos_of_pos up))
    sumg gpos near far
  have count := window_card hU ux
  have wt_value : ∑' n,wt n = vonMangoldtLSeriesNormSum c := by
    simp only [vonMangoldtLSeriesNormSum,norm_LSeriesTerm_vonMangoldt_eq,wt]
  have value : ∑' n,g n = ((2/U)*(x:ℝ)^c)*vonMangoldtLSeriesNormSum c := by
    rw [←wt_value,←tsum_mul_left]
  have line : vonMangoldtLSeriesNormSum c ≤ K*log (x:ℝ) := by
    have v := lseries c cpos (ctwo.trans (by norm_num))
    simpa [c,optimizedPerronLine,div_eq_mul_inv] using v
  apply (norm_explicitFormulaVerticalIntegral_sub_halfSum_le_source χ xn cpos (sq_pos_of_pos up)).trans
  apply split.trans
  rw [value]
  calc
    _ ≤ 3*((x:ℝ)/U)*(4*log (2*(x:ℝ))) + ((2/U)*(x:ℝ)^c)*(K*log (2*(x:ℝ))) :=
      add_le_add (mul_le_mul_of_nonneg_right count (by linarith))
        (mul_le_mul_of_nonneg_left (line.trans (mul_le_mul_of_nonneg_left lc hK.le)) (by positivity))
    _ = _ := by rw [show (x:ℝ)^c=x*exp 1 from rpow_optimizedPerronLine_eq hx]; ring
end TotientPerron
end

section
namespace TotientPerron
open Filter Complex DirichletCharacter Finset Real
open BombieriVinogradov.SiegelWalfisz

/-- A larger power of the logarithm in the contour height absorbs the coarse window error. -/
theorem natural_from_strip (strip : BVRect.Strip) : ∀ B A : ℝ, 0<B → 0<A → ∃ K > (0:ℝ),
    ∀ᶠ n : ℕ in atTop, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → χ ≠ 1 → (q:ℝ) ≤ (Real.log n)^B →
      ‖∑ k ∈ Icc 1 n, (ArithmeticFunction.vonMangoldt k:ℂ)*χ k‖ ≤ K*n/(Real.log n)^A := by
  intro B A hB hA
  obtain ⟨C,cpos,truncate⟩ := coarse_truncation
  refine ⟨5+4*Real.exp 1+2*C,by positivity,?_⟩
  let J := 2*A+5
  have jp : 0<J := by dsimp [J]; linarith
  have lim := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [BVRect.scalar J jp,strip J B jp hB,lim.eventually_ge_atTop 2,
    lim.eventually (BVRect.power_absorb (A+5)),eventually_gt_atTop 2] with n S H large room hn
  intro q _ χ hp hχ hq
  let L := Real.log (n:ℝ)
  let U := L^(A+5)
  have lp : 2≤L := large
  have ln : 0<L := by linarith
  have np : 0<(n:ℝ) := by exact_mod_cast (show 0<n by omega)
  have u2 : 2≤U := lp.trans ((Real.rpow_one L).symm.le.trans
    (Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)))
  have ux : U≤(n:ℝ) := by
    change U ≤ Real.exp L at room
    rwa [show Real.exp L=(n:ℝ) from Real.exp_log np] at room
  have t : U^2=L^(J+5) := by
    dsimp [U,J]
    rw [←Real.rpow_natCast,←Real.rpow_mul ln.le]
    congr 1; push_cast; ring
  obtain ⟨ha,hab,hT,hM,hleft,hhor,_,hend⟩ := S
  have shifted := BVRect.shift χ hn hχ ha hab hT hM (H q χ hp hχ hq)
  have per := truncate χ n hn U u2 ux
  rw [t] at per
  have QP : L^A ≤ L^J := Real.rpow_le_rpow_of_exponent_le (by linarith)
    (by dsimp [J]; linarith)
  have divs : (n:ℝ)/L^J ≤ n/L^A := div_le_div_of_nonneg_left np.le (Real.rpow_pos_of_pos ln _) QP
  have small : C*(n:ℝ)*Real.log (2*(n:ℝ))/U ≤ 2*C*((n:ℝ)/L^A) := by
    have log2 : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
    have logbound : Real.log (2*(n:ℝ)) ≤ 2*L := by rw [Real.log_mul (by norm_num) np.ne']; change Real.log 2+L≤_; linarith
    have lepow : L≤L^5 := by simpa using pow_le_pow_right₀ (by linarith : 1≤L) (by decide : 1≤5)
    have dpos : 0<L^A := Real.rpow_pos_of_pos ln _
    have upos : 0<U := by linarith
    apply (div_le_iff₀ upos).mpr
    rw [show U=L^A*(L^5) by simp [U,Real.rpow_add ln]]
    calc
      C*(n:ℝ)*Real.log (2*(n:ℝ)) ≤ C*n*(2*L^5) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = _ := by field_simp
  have ep := BVRect.endpoint χ (show 1≤n by omega)
  have tri := norm_sub_le (explicitFormulaVerticalIntegral χ n (optimizedPerronLine n) (L^(J+5)))
    (explicitFormulaVerticalIntegral χ n (optimizedPerronLine n) (L^(J+5))-characterChebyshevHalfSum n χ)
  rw [sub_sub_cancel] at tri
  have hr : 4*Real.exp 1*n/L^J ≤ 4*Real.exp 1*n/L^A :=
    div_le_div_of_nonneg_left (by positivity) (Real.rpow_pos_of_pos ln _) QP
  change ‖_‖ ≤ (5+4*Real.exp 1+2*C)*n/L^A
  linarith only [ep,tri,per,small,shifted,hleft,hhor,hend,
    show 4*(n:ℝ)/L^J ≤ 4*(n/L^A) by rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left divs (by norm_num),
    divs,hr,show (5+4*Real.exp 1+2*C)*n/L^A = 4*(n/L^A) + 4*Real.exp 1*n/L^A +
      (n/L^A)+2*C*(n/L^A) by ring]
end TotientPerron
end

section
section
open Filter in
theorem BVShort.strip : BVRect.Strip := by
  intro A B hA hB
  filter_upwards [tendsto_natCast_atTop_atTop.eventually (BVShort.log_strip (A+5) B (by linarith) hB),
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_gt_atTop (1:ℝ))] with n H hn
  intro q _ χ hp hc hq s hl hr ht
  change 1 < Real.log (n:ℝ) at hn
  have p : 0 < Real.sqrt (Real.log n) := Real.sqrt_pos.mpr (by linarith)
  have b : Real.sqrt (Real.log n) ≤ Real.log n := by by_contra! hh; nlinarith [Real.sq_sqrt (show 0 ≤ Real.log (n:ℝ) by linarith),mul_lt_mul_of_pos_right hh (by linarith : 0 < Real.sqrt (Real.log n)),mul_le_mul_of_nonneg_right hn.le p.le]
  obtain ⟨nz,v⟩ := H q χ hc hp hq s (abs_le.mpr ⟨by linarith,by linarith [one_div_le_one_div_of_le p b]⟩) ht
  exact ⟨nz,v.trans b⟩
open Filter Finset in
theorem BVShort.natural : ∀ B A : ℝ, 0 < B → 0 < A → ∃ K > (0:ℝ), ∀ᶠ n : ℕ in atTop,
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → χ ≠ 1 → (q:ℝ) ≤ (Real.log n)^B →
  ‖∑ k ∈ Icc 1 n, (ArithmeticFunction.vonMangoldt k:ℂ)*χ k‖ ≤ K*n/(Real.log n)^A := TotientPerron.natural_from_strip BVShort.strip

end

/- # Bounds for character sums on either of two adjacent dyadic intervals -/

open Filter
open scoped Topology
namespace TotientDyadic

lemma power_absorbed_by_log {D E : ℕ} (hDE : D<E) {c : ℝ} (hc : 0<c) :
    ∀ᶠ k : ℕ in atTop, ∀ j ≥ k, (k:ℝ)^D ≤ c * (Real.log ((2:ℝ)^j))^E := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have lim := (tendsto_pow_div_pow_atTop_zero (𝕜 := ℝ) hDE).comp tendsto_natCast_atTop_atTop
  have ev := lim.eventually_lt_const (show 0 < c * (Real.log 2)^E by positivity)
  filter_upwards [ev,eventually_gt_atTop 0] with k hk hpos
  intro j hj
  have kp : (0:ℝ)<k := by exact_mod_cast hpos
  have h := (div_lt_iff₀ (pow_pos kp E)).mp hk
  rw [Real.log_pow,mul_pow]
  have sub : (k:ℝ)^E ≤ (j:ℝ)^E := by gcongr
  calc (k:ℝ)^D ≤ c*(Real.log 2)^E*(k:ℝ)^E := h.le
       _ ≤ c*(Real.log 2)^E*(j:ℝ)^E := by gcongr
       _ = c*((j:ℝ)^E*(Real.log 2)^E) := by ring

lemma modulus_log (D : ℕ) : ∀ᶠ k : ℕ in atTop, ∀ j ≥ k,
    (k:ℝ)^D ≤ (Real.log ((2:ℝ)^j))^(D+2) := by
  simpa only [one_mul] using power_absorbed_by_log (D:=D) (E:=D+2) (by omega) (c:=1) (by norm_num)

lemma modulus_lt_height (D : ℕ) : ∀ᶠ k : ℕ in atTop, k^D ≤ 2^k := by
  have ev := (tendsto_pow_const_div_const_pow_of_one_lt D (r:=2) (by norm_num)).eventually_lt_const (show (0:ℝ)<1 by norm_num)
  filter_upwards [ev] with k hk
  have h := (div_lt_iff₀ (show (0:ℝ)<2^k by positivity)).mp hk
  rw [one_mul] at h
  exact_mod_cast h.le

lemma mass_budget (D : ℕ) {C T ε : ℝ} (hC : 0<C) (hT : 0<T) (hε : 0<ε) :
    ∀ᶠ k : ℕ in atTop, ∀ j : ℕ, (j=k ∨ j=k+1) →
      let a := (2:ℝ)^j
      let b := 2*a
      (k:ℝ)^D * (2*(k:ℝ)^D*Real.log b + (C*a/(Real.log a)^(2*D+4) +
        C*b/(Real.log b)^(2*D+4) + T*Real.sqrt b)) < ε*(2:ℝ)^k := by
  let E := 2*D+4
  have hlog := power_absorbed_by_log (D:=D) (E:=E) (by dsimp [E]; omega) (c:=ε/24/C) (by positivity)
  have hp := (tendsto_pow_const_div_const_pow_of_one_lt (2*D+1) (r:=2) (by norm_num)).eventually_lt_const (show 0 < ε/24 by positivity)
  have hroot : ‖Real.sqrt 2‖ < (2:ℝ) := by
    rw [Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
    linarith [Real.sqrt_two_lt_three_halves]
  have hs := (isLittleO_pow_const_mul_const_pow_const_pow_of_norm_lt D hroot).tendsto_div_nhds_zero.eventually_lt_const (show 0<ε/8/T by positivity)
  filter_upwards [hlog,hp,hs,eventually_ge_atTop 2] with k hk hpk hsk k2
  intro j hj
  let x := (2:ℝ)^k
  let a := (2:ℝ)^j
  let b := 2*a
  change (k:ℝ)^D*(2*(k:ℝ)^D*Real.log b+(C*a/(Real.log a)^E+C*b/(Real.log b)^E+T*Real.sqrt b)) < ε*x
  have xp : 0<x := by dsimp [x]; positivity
  have ap : 0<a := by dsimp [a]; positivity
  have bp : 0<b := by dsimp [b]; positivity
  have jlo : k≤j := by omega
  have jhi : j≤k+1 := by omega
  have kpos : 0<(k:ℝ) := by exact_mod_cast (show 0<k by omega)
  have kTwo : (2:ℝ)≤k := by exact_mod_cast k2
  have jReal : (j:ℝ)≤k+1 := by exact_mod_cast jhi
  have amax : a≤2*x := by
    rcases hj with rfl|rfl
    · dsimp [a,x]; linarith
    · simp [a,x,pow_succ,mul_comm]
  have bmax : b≤4*x := by dsimp [b]; linarith
  have b_eq : b=(2:ℝ)^(j+1) := by simp [b,a,pow_succ,mul_comm]
  have l2 : Real.log 2≤1 := by linarith [Real.log_le_sub_one_of_pos (show (0:ℝ)<2 by norm_num)]
  have logmax : Real.log b ≤ 3*k := by
    rw [b_eq,Real.log_pow,Nat.cast_add_one]
    calc ((j:ℝ)+1)*Real.log 2 ≤ ((j:ℝ)+1)*1 := by gcongr
         _ ≤ 3*k := by linarith
  have oneChar (i : ℕ) (hi : k ≤ i) :
      (k:ℝ)^D*(C*(2:ℝ)^i/(Real.log ((2:ℝ)^i))^E) ≤ (ε/24)*(2:ℝ)^i := by
    have ip : (0:ℝ)< i := by exact_mod_cast (show 0< i by omega)
    have lp : 0<Real.log ((2:ℝ)^i) := by rw [Real.log_pow]; exact mul_pos ip (Real.log_pos (by norm_num))
    have gain := mul_le_mul_of_nonneg_right (hk i hi) hC.le
    have coeff : (k:ℝ)^D*C/(Real.log ((2:ℝ)^i))^E ≤ ε/24 := by
      apply (div_le_iff₀ (pow_pos lp E)).mpr
      calc (k:ℝ)^D*C ≤ ε/24/C*(Real.log ((2:ℝ)^i))^E*C := gain
           _ = ε/24*(Real.log ((2:ℝ)^i))^E := by field_simp
    calc _ = ((k:ℝ)^D*C/(Real.log ((2:ℝ)^i))^E)*(2:ℝ)^i := by ring
         _ ≤ _ := mul_le_mul_of_nonneg_right coeff (by positivity)
  have ca := oneChar j jlo
  change (k:ℝ)^D*(C*a/(Real.log a)^E) ≤ ε/24*a at ca
  have cb := oneChar (j+1) (by omega)
  rw [← b_eq] at cb
  have hpoly : (k:ℝ)^(2*D+1) < ε/24*x := (div_lt_iff₀ xp).mp hpk
  have hcount : (k:ℝ)^D*(2*(k:ℝ)^D*Real.log b) ≤ 6*(k:ℝ)^(2*D+1) := by
    calc _ ≤ (k:ℝ)^D*(2*(k:ℝ)^D*(3*k)) := by gcongr
         _ = _ := by rw [pow_succ,show 2*D=D+D by omega,pow_add]; ring
  have sqrtmax : Real.sqrt b ≤ 2*(Real.sqrt 2)^k := by
    apply (Real.sqrt_le_left (by positivity)).mpr
    calc b ≤ 4*x := bmax
         _ = _ := by rw [mul_pow,← pow_mul,Nat.mul_comm k 2,pow_mul,Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]; dsimp [x]; ring
  have hs' : (k:ℝ)^D*(Real.sqrt 2)^k < ε/8/T*x := (div_lt_iff₀ xp).mp hsk
  have sqerr : (k:ℝ)^D*(T*Real.sqrt b) ≤ (2*T)*((k:ℝ)^D*(Real.sqrt 2)^k) := by
    calc _ ≤ (k:ℝ)^D*(T*(2*(Real.sqrt 2)^k)) := by gcongr
         _ = _ := by ring
  have sqsmall := mul_lt_mul_of_pos_left hs' (show 0<2*T by positivity)
  have sqid : 2*T*(ε/8/T*x) = ε/4*x := by field_simp; ring
  rw [sqid] at sqsmall
  have cmaxA := mul_le_mul_of_nonneg_left amax (show 0≤ε/24 by positivity)
  have cmaxB := mul_le_mul_of_nonneg_left bmax (show 0≤ε/24 by positivity)
  rw [mul_add,mul_add,mul_add]
  linarith only [ca,cb,cmaxA,cmaxB,hpoly,hcount,sqerr,sqsmall,mul_pos hε xp]

end TotientDyadic

open Finset ArithmeticFunction
namespace Erdos694Class

theorem primitive_at_prime {q : ℕ} [NeZero q] (hq : q.Prime)
    {χ : DirichletCharacter ℂ q} (hc : χ ≠ 1) : χ.IsPrimitive := by
  exact (hq.eq_one_or_self_of_dvd χ.conductor χ.conductor_dvd_level).resolve_left
    (fun h => hc (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr h))

theorem split_sum {E : Type*} [AddCommGroup E] (f : ℕ → E) {a b : ℕ} (ab : a≤b) :
    (∑ p ∈ Ioc a b, f p) = (∑ p ∈ Icc 1 b, f p) - ∑ p ∈ Icc 1 a, f p := by
  have hu : Ioc a b ∪ Icc 1 a = Icc 1 b := by
    ext p
    simp only [mem_union, mem_Ioc, mem_Icc]
    omega
  have hd : Disjoint (Ioc a b) (Icc 1 a) := by
    apply Finset.disjoint_left.mpr
    simp only [mem_Ioc, mem_Icc]
    omega
  apply eq_sub_iff_add_eq.mpr
  rw [← sum_union hd,hu]

theorem split_theta {a b : ℕ} (ab : a ≤ b) :
    Chebyshev.theta b - Chebyshev.theta a =
      ∑ p ∈ (Ioc a b).filter Nat.Prime, Real.log p := by
  have h (k : ℕ) : Ioc 0 k = Icc 1 k := by
    ext p
    simp only [mem_Ioc, mem_Icc]
    omega
  simp only [Chebyshev.theta, Nat.floor_natCast, sum_filter, h]
  exact (split_sum (fun p => if p.Prime then Real.log p else 0) ab).symm

theorem prime_twist_bound {a b q : ℕ} [NeZero q] (ab : a≤b) (χ : DirichletCharacter ℂ q)
    {Ea Eb : ℝ}
    (ha : ‖∑ k ∈ Icc 1 a, (vonMangoldt k : ℂ)*χ k‖ ≤ Ea)
    (hb : ‖∑ k ∈ Icc 1 b, (vonMangoldt k : ℂ)*χ k‖ ≤ Eb) :
    ‖∑ p ∈ (Ioc a b).filter Nat.Prime, (Real.log p : ℂ)*χ p‖ ≤
      Ea + Eb + (Chebyshev.psi b - Chebyshev.theta b) := by
  classical
  let w (p : ℕ) : ℂ := (vonMangoldt p : ℂ) * χ p
  have total : ‖∑ p ∈ Ioc a b, w p‖ ≤ Ea + Eb := by
    rw [split_sum w ab]
    exact (norm_sub_le ..).trans (by dsimp [w]; linarith)
  have tail : ‖∑ p ∈ (Ioc a b).filter (fun p => ¬p.Prime), w p‖ ≤ Chebyshev.psi b - Chebyshev.theta b := by
    rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, Nat.floor_natCast]
    calc
      _ ≤ ∑ p ∈ (Ioc a b).filter (fun p => ¬p.Prime), ‖w p‖ := norm_sum_le ..
      _ ≤ ∑ p ∈ (Ioc a b).filter (fun p => ¬p.Prime), vonMangoldt p := by
        apply sum_le_sum
        intro p _
        simpa [w, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (vonMangoldt_nonneg)] using
          mul_le_mul_of_nonneg_left (χ.norm_le_one p) (vonMangoldt_nonneg (n:=p))
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (fun p hp =>
        mem_filter.mpr ⟨mem_Ioc.mpr ⟨by have := (mem_Ioc.mp (mem_filter.mp hp).1).1; omega,
        (mem_Ioc.mp (mem_filter.mp hp).1).2⟩,(mem_filter.mp hp).2⟩)
        (fun _ _ _ => vonMangoldt_nonneg)
  have heq : (∑ p ∈ (Ioc a b).filter Nat.Prime, (Real.log p : ℂ)*χ p) =
      (∑ p ∈ Ioc a b, w p) - ∑ p ∈ (Ioc a b).filter (fun p => ¬p.Prime), w p := by
    rw [eq_sub_iff_add_eq]
    convert sum_filter_add_sum_filter_not (Ioc a b) Nat.Prime w using 2
    apply sum_congr rfl
    intro p hp
    simp only [w, vonMangoldt_apply_prime (mem_filter.mp hp).2]
  rw [heq]
  exact (norm_sub_le ..).trans (add_le_add total tail)

end Erdos694Class

open Finset ArithmeticFunction
namespace Erdos694Class

theorem class_count {a b q : ℕ} (ab : a ≤ b) (hq : q.Prime) (before : q ≤ a) {Ea Eb : ℝ}
    (small₁ : ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
      ‖∑ k ∈ Icc 1 a, (vonMangoldt k : ℂ)*χ k‖ ≤ Ea)
    (small₂ : ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
      ‖∑ k ∈ Icc 1 b, (vonMangoldt k : ℂ)*χ k‖ ≤ Eb)
    (e₀ : 0 ≤ Ea + Eb + (Chebyshev.psi b - Chebyshev.theta b)) :
    Chebyshev.theta b - Chebyshev.theta a ≤
      (q.totient : ℝ) * ((((Ioc a b).filter (fun p => p.Prime ∧ p%q=1%q)).card:ℝ) * Real.log b +
        (Ea + Eb + (Chebyshev.psi b - Chebyshev.theta b))) := by
  classical
  let : NeZero q := ⟨hq.ne_zero⟩
  let P := (Ioc a b).filter Nat.Prime
  let R := P.filter (fun p => p%q=1%q)
  let S (χ : DirichletCharacter ℂ q) : ℂ := ∑ p ∈ P, (Real.log p : ℂ) * χ p
  let E := Ea + Eb + (Chebyshev.psi b - Chebyshev.theta b)
  have entire : S 1 = ((Chebyshev.theta b - Chebyshev.theta a : ℝ) : ℂ) := by
    rw [split_theta ab, Complex.ofReal_sum]
    dsimp [S,P]
    apply sum_congr rfl
    intro p hp
    have pq : q < p := before.trans_lt (mem_Ioc.mp (mem_filter.mp hp).1).1
    have hu : IsUnit (p : ZMod q) := (ZMod.isUnit_iff_coprime ..).mpr
      ((mem_filter.mp hp).2.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hq.pos pq))
    simp [MulChar.one_apply hu]
  have orth : (∑ χ, S χ) = ((q.totient : ℝ) * ∑ p ∈ R, Real.log p : ℝ) := by
    simp only [S, Complex.ofReal_mul, Complex.ofReal_sum, Complex.ofReal_natCast, R, sum_filter,
      mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro p _
    rw [← mul_sum, DirichletCharacter.sum_characters_eq ℂ]
    have iff : (p : ZMod q)=1 ↔ p%q=1%q := by
      simpa using ZMod.natCast_eq_natCast_iff' p 1 q
    by_cases h : p%q=1%q <;> simp [h,iff, mul_comm]
  have m := Finset.sum_erase_add (s:=(Finset.univ : Finset (DirichletCharacter ℂ q))) S (Finset.mem_univ 1)
  have rest : ‖∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).erase 1, S χ‖ ≤ (q.totient:ℝ)*E := by
    calc
      _ ≤ ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).erase 1, ‖S χ‖ := norm_sum_le ..
      _ ≤ ∑ _χ ∈ (univ : Finset (DirichletCharacter ℂ q)).erase 1, E := by
        apply sum_le_sum
        intro χ hχ
        exact prime_twist_bound ab χ (small₁ χ (ne_of_mem_erase hχ)) (small₂ χ (ne_of_mem_erase hχ))
      _ ≤ ∑ _χ : DirichletCharacter ℂ q, E := sum_le_sum_of_subset_of_nonneg
        (erase_subset ..) (fun _ _ _ => e₀)
      _ = _ := by
        simp only [sum_const, card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card,
          DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity]
  have mass : 0 ≤ ∑ p ∈ R, Real.log p := sum_nonneg fun p _ => Real.log_natCast_nonneg p
  have bound : (∑ p ∈ R, Real.log p) ≤ (R.card:ℝ)*Real.log b := by
    calc
      _ ≤ ∑ _p ∈ R, Real.log b := by
        apply sum_le_sum
        intro p hp
        have mem := mem_filter.mp ((mem_filter.mp hp).1)
        exact Real.log_le_log (by exact_mod_cast mem.2.pos) (by exact_mod_cast (mem_Ioc.mp mem.1).2)
      _ = _ := by simp
  have ht : ‖S 1‖ ≤ (q.totient:ℝ)*(∑ p ∈ R, Real.log p) + (q.totient:ℝ)*E := by
    rw [show S 1 = (∑ χ,S χ) - ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).erase 1, S χ by linear_combination m]
    apply (norm_sub_le ..).trans
    rw [orth, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) mass)]
    exact add_le_add le_rfl rest
  have hh : Chebyshev.theta b - Chebyshev.theta a ≤ ‖S 1‖ := by
    rw [entire, Complex.norm_real, Real.norm_eq_abs]
    exact le_abs_self _
  have hr : R = (Ioc a b).filter (fun p => p.Prime ∧ p%q=1%q) := by
    ext p
    simp [R,P,and_assoc]
  calc
    _ ≤ _ := hh.trans ht
    _ ≤ (q.totient:ℝ)*(R.card*Real.log b)+(q.totient:ℝ)*E :=
      add_le_add (mul_le_mul_of_nonneg_left bound (Nat.cast_nonneg q.totient)) le_rfl
    _ = _ := by rw [hr]; dsimp only [E]; ring

end Erdos694Class

open Filter Finset ArithmeticFunction

namespace Erdos694Class

theorem dyadic_supply
    (sw : ∀ B A : ℝ, 0 < B → 0 < A → ∃ C > (0:ℝ), ∀ᶠ n : ℕ in atTop,
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → χ ≠ 1 →
        (q:ℝ) ≤ (Real.log n)^B →
        ‖∑ k ∈ Icc 1 n, (vonMangoldt k:ℂ)*χ k‖ ≤ C*n/(Real.log n)^A)
    (bands : ∀ᶠ k : ℕ in atTop, ∃ j : ℕ, (j=k ∨ j=k+1) ∧
      Real.log 2 / 4 * (2:ℝ)^k ≤ Chebyshev.theta (2*(2:ℝ)^j) - Chebyshev.theta ((2:ℝ)^j))
    (size : ∀ D : ℕ, ∀ᶠ k : ℕ in atTop, k^D ≤ 2^k ∧
      ∀ j ≥ k, (k:ℝ)^D ≤ (Real.log ((2:ℝ)^j))^(D+2))
    (budget : ∀ (D : ℕ) (C T ε : ℝ), 0<C → 0<T → 0<ε → ∀ᶠ k : ℕ in atTop,
      ∀ j : ℕ, (j=k ∨ j=k+1) →
      let a := (2:ℝ)^j
      let b := 2*a
      (k:ℝ)^D * (2*(k:ℝ)^D * Real.log b +
        (C*a/(Real.log a)^(2*D+4) + C*b/(Real.log b)^(2*D+4) + T*Real.sqrt b))
        < ε*(2:ℝ)^k) :
    ∀ D : ℕ, ∀ᶠ k : ℕ in atTop, ∃ j : ℕ, (j=k ∨ j=k+1) ∧ ∀ q : ℕ, q.Prime → q≤k^D →
      2*k^D ≤ ((Ioc (2^j) (2*2^j)).filter (fun p => p.Prime ∧ p%q=1%q)).card := by
  intro D
  obtain ⟨C,hC,uniform⟩ := sw (D+2 : ℕ) (2*D+4 : ℕ) (by positivity) (by positivity)
  obtain ⟨N,hN⟩ := eventually_atTop.mp uniform
  obtain ⟨V,hV⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  let T := max V 1
  have hT : 0 < T := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hε : 0 < Real.log 2 / 4 := by positivity
  filter_upwards [bands, size D, budget D C T _ hC hT hε, eventually_ge_atTop N,
    eventually_ge_atTop 1] with k hkband hkSize hkbudget hkN hkpos
  obtain ⟨j,hj,hmass⟩ := hkband
  refine ⟨j,hj,?_⟩
  have kj : k ≤ j := by rcases hj with h|h <;> omega
  let a : ℕ := 2^j
  let b : ℕ := 2*a
  have ha : (a:ℝ) = (2:ℝ)^j := by simp [a]
  have hb : (b:ℝ) = 2*(2:ℝ)^j := by simp [b,ha]
  have ab : a≤b := by dsimp [b]; omega
  have ka : 2^k ≤ a := Nat.pow_le_pow_right (by decide) kj
  have hNa : N ≤ a := hkN.trans ((show k < 2^k from Nat.lt_two_pow_self).le.trans ka)
  intro q hq hqk
  let : NeZero q := ⟨hq.ne_zero⟩
  have qk' : (q:ℝ) ≤ (k:ℝ)^D := by exact_mod_cast hqk
  have modulusA : (q:ℝ) ≤ Real.log a ^ ((D+2:ℕ):ℝ) := by
    rw [Real.rpow_natCast,ha]
    exact qk'.trans (hkSize.2 _ kj)
  have modulusB : (q:ℝ) ≤ Real.log b ^ ((D+2:ℕ):ℝ) := by
    rw [Real.rpow_natCast, hb, show 2*(2:ℝ)^j = (2:ℝ)^(j+1) by ring]
    exact qk'.trans (hkSize.2 _ (by omega))
  let Ea := C*(a:ℝ) / (Real.log a)^(2*D+4:ℕ)
  let Eb := C*(b:ℝ) / (Real.log b)^(2*D+4:ℕ)
  have small (n : ℕ) (hn : N≤n) (hnq : (q:ℝ) ≤ Real.log n ^ ((D+2:ℕ):ℝ))
      (χ : DirichletCharacter ℂ q) (ne : χ ≠ 1) :
      ‖∑ i ∈ Icc 1 n, (vonMangoldt i:ℂ)*χ i‖ ≤ C*n/(Real.log n)^(2*D+4:ℕ) := by
    simpa only [Real.rpow_natCast] using hN n hn q χ (primitive_at_prime hq ne) ne hnq
  have enon : 0 ≤ Ea + Eb + (Chebyshev.psi b-Chebyshev.theta b) :=
    add_nonneg (add_nonneg (by dsimp [Ea]; positivity) (by dsimp [Eb]; positivity))
      (sub_nonneg.mpr (Chebyshev.theta_le_psi _))
  have h := class_count ab hq (hqk.trans (hkSize.1.trans ka))
    (Ea:=Ea) (Eb:=Eb) (small a hNa modulusA) (small b (hNa.trans ab) modulusB) enon
  let card := ((Ioc a b).filter (fun p => p.Prime ∧ p%q=1%q)).card
  change 2*k^D ≤ card
  by_contra! bad
  have hcard : (card:ℝ) ≤ 2*(k:ℝ)^D := by exact_mod_cast bad.le
  have htot : (q.totient:ℝ) ≤ (k:ℝ)^D := by exact_mod_cast (Nat.totient_le q).trans hqk
  have hpowers : Chebyshev.psi b-Chebyshev.theta b ≤ T*Real.sqrt b :=
    (hV b).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _))
  have final := hkbudget j hj
  dsimp only at final
  rw [← hb, ← ha] at final hmass
  have smaller :
      (q.totient:ℝ)*((card:ℝ)*Real.log b + (Ea+Eb+(Chebyshev.psi b-Chebyshev.theta b))) ≤
      (k:ℝ)^D * (2*(k:ℝ)^D*Real.log b+(Ea+Eb+T*Real.sqrt b)) :=
    mul_le_mul htot (add_le_add (mul_le_mul_of_nonneg_right hcard (Real.log_natCast_nonneg _))
      (add_le_add le_rfl hpowers))
      (add_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)) enon) (by positivity)
  exact (not_lt_of_ge (hmass.trans (h.trans smaller))) final

end Erdos694Class

open Filter
open scoped Topology
namespace TotientDyadic

/-- Chebyshev's elementary estimates give a positive mass in at least one of two
successive dyadic intervals. The interval is chosen before the modulus. -/
theorem principal_band :
    ∀ᶠ k : ℕ in atTop, ∃ j : ℕ, (j = k ∨ j = k + 1) ∧
      (Real.log 2 / 4) * (2 : ℝ)^k ≤
        Chebyshev.theta (2 * (2:ℝ)^j) - Chebyshev.theta ((2:ℝ)^j) := by
  have log2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have small := (isLittleO_log_rpow_atTop (r := 1/2) (by norm_num)).bound
    (show 0 < Real.log 2 / 16 by positivity)
  have height : Tendsto (fun k : ℕ => 4 * (2:ℝ)^k) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < (2:ℝ))).const_mul_atTop (by norm_num)
  filter_upwards [height.eventually small, height.eventually_ge_atTop 16] with k hk hk16
  let x : ℝ := 4 * (2:ℝ)^k
  have x16 : 16 ≤ x := hk16
  have x1 : 1 ≤ x := by linarith
  have hx : 0 ≤ x := by linarith
  have hlog : Real.log x ≤ (Real.log 2 / 16) * Real.sqrt x := by
    change ‖Real.log x‖ ≤ _ * ‖x ^ (1/2:ℝ)‖ at hk
    rw [← Real.sqrt_eq_rpow, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg x1),
      Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] at hk
    exact hk
  have hs : Real.sqrt x ≤ x := Real.sqrt_le_self_iff.mpr (Or.inr x1)
  have hlinear : Real.log x ≤ (Real.log 2 / 16) * x :=
    hlog.trans (mul_le_mul_of_nonneg_left hs (by positivity))
  have hnext : Real.log (x + 1) ≤ Real.log 2 + Real.log x := by
    rw [← Real.log_mul (by positivity) (by linarith : x ≠ 0)]
    apply Real.log_le_log (by positivity)
    linarith
  have hsq : 2 * Real.sqrt x * Real.log x ≤ 2 * (Real.log 2 / 16) * x := by
    calc
      _ ≤ 2 * Real.sqrt x * ((Real.log 2/16) * Real.sqrt x) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
      _ = 2 * (Real.log 2 / 16) * (Real.sqrt x)^2 := by ring
      _ = _ := by rw [Real.sq_sqrt hx]
  have hbound := Chebyshev.theta_ge (4 * 2 ^ k)
  simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow] at hbound
  change x * Real.log 2 - Real.log (x + 1) - 2 * Real.sqrt x * Real.log x ≤
    Chebyshev.theta x at hbound
  have lower : 3/4 * x * Real.log 2 ≤ Chebyshev.theta x := by
    nlinarith [mul_nonneg (sub_nonneg.mpr x16) log2.le]
  have upper := Chebyshev.theta_le_log4_mul_x (x := (2:ℝ)^k) (by positivity)
  have log4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4:ℝ)=2^2 by norm_num, Real.log_pow]
    norm_num
  rw [log4] at upper
  dsimp only [x] at lower
  by_cases h : (Real.log 2 / 4) * (2:ℝ)^k ≤
    Chebyshev.theta (2*(2:ℝ)^k)-Chebyshev.theta ((2:ℝ)^k)
  · exact ⟨k, Or.inl rfl, h⟩
  · refine ⟨k+1, Or.inr rfl, ?_⟩
    rw [pow_succ']
    rw [show (2:ℝ) * (2 * 2^k) = 4*2^k by ring]
    nlinarith only [lower, upper, lt_of_not_ge h,
      mul_nonneg log2.le (show 0 ≤ (2:ℝ)^k by positivity)]
end TotientDyadic

open Filter in
theorem TotientPerron.small_modulus_supply : OMA.R_Erdos694_erdos_694_R2.H2 := by
  apply Erdos694Class.dyadic_supply BVShort.natural TotientDyadic.principal_band
  · intro D
    exact (TotientDyadic.modulus_lt_height D).and (TotientDyadic.modulus_log D)
  · intro D C T ε hC hT hε
    exact TotientDyadic.mass_budget D hC hT hε
end

theorem OMA.solution : type_of% @Erdos694.erdos_694 :=
  OMA.R_Erdos694_erdos_694_R2.main Mertens.qualitative_H1 TotientPerron.small_modulus_supply
