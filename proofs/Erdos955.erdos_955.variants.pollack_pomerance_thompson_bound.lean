import FormalConjectures.ErdosProblems.«955»
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.Primorial
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith

section

/-! Reduction of the Pollack--Pomerance--Thompson density statement to the uniform theorem of
their paper (Divisor-sum fibers, Mathematika 64 (2018)) and an elementary bound for the
sum-of-divisors function. Every n below x has s(n) below x (1 + log x), so only the part of A
below that bound matters, and that part has at most x ^ (1/2 + o(1)) elements. -/

namespace OMA.R_Erdos955_erdos_955_variants_pollack_pomerance_thompson_bound_R1

open Filter Topology

/-- Pollack, Pomerance and Thompson, uniformly in the set: if eps tends to 0 then the number of
n up to x whose sum of proper divisors lies in a set of at most x ^ (1/2 + eps x) positive
integers is o(x), uniformly over such sets. -/
def H1 : Prop :=
  ∀ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) → ∀ δ : ℝ, 0 < δ →
    ∀ᶠ x : ℕ in atTop, ∀ A : Finset ℕ, (∀ a ∈ A, 0 < a) →
      (A.card : ℝ) ≤ (x : ℝ) ^ ((1 / 2 : ℝ) + ε x) →
      (((Finset.Icc 1 x).filter (fun n => Erdos955.s n ∈ A)).card : ℝ) ≤ δ * x

/-- The elementary bound sigma(n) <= n (1 + log n), from sigma(n) / n = sum of 1 / d over the
divisors d of n. -/
def H2 : Prop :=
  ∀ n : ℕ, 1 ≤ n → (ArithmeticFunction.sigma 1 n : ℝ) ≤ n * (1 + Real.log n)

lemma s_pos_of_two_le {n : ℕ} (hn : 2 ≤ n) : 1 ≤ Erdos955.s n := by
  have h1 : ({1, n} : Finset ℕ) ⊆ n.divisors := by
    intro d hd
    rw [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl
    · exact Nat.one_mem_divisors.mpr (by omega)
    · exact Nat.mem_divisors_self _ (by omega)
  have h2 : ∑ d ∈ ({1, n} : Finset ℕ), d = 1 + n := Finset.sum_pair (by omega)
  have h3 : ∑ d ∈ ({1, n} : Finset ℕ), d ≤ ∑ d ∈ n.divisors, d :=
    Finset.sum_le_sum_of_subset h1
  have h4 : ArithmeticFunction.sigma 1 n = ∑ d ∈ n.divisors, d := by
    simp [ArithmeticFunction.sigma_one_apply]
  unfold Erdos955.s
  omega

lemma tendsto_log_ratio :
    Tendsto (fun b : ℕ => Real.log ((b : ℝ) * (2 + Real.log b)) / Real.log b) atTop (𝓝 1) := by
  have hL : Tendsto (fun b : ℕ => 2 + Real.log (b : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_left _ _ (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have h0 : Tendsto (fun b : ℕ => Real.log (2 + Real.log (b : ℝ)) / Real.log b) atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-2) 1 one_ne_zero).comp hL
    refine h.congr (fun b => ?_)
    simp only [Function.comp_apply, pow_one]
    congr 1
    ring
  have h1 : Tendsto (fun b : ℕ => 1 + Real.log (2 + Real.log (b : ℝ)) / Real.log b) atTop
      (𝓝 1) := by
    simpa using h0.const_add 1
  refine h1.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with b hb
  have hb' : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hlog : 0 < Real.log (b : ℝ) := Real.log_pos (by linarith)
  rw [Real.log_mul (ne_of_gt (by linarith)) (ne_of_gt (by linarith)), add_div,
    div_self hlog.ne']

theorem main : H1 → H2 →
    type_of% @Erdos955.erdos_955.variants.pollack_pomerance_thompson_bound := by
  intro h1 h2 A ε hε hA
  classical
  obtain ⟨M, hMdef⟩ : ∃ M : ℕ → ℕ, ∀ b : ℕ, M b = ⌊(b : ℝ) * (1 + Real.log b)⌋₊ + 1 :=
    ⟨_, fun _ => rfl⟩
  have hbM : ∀ b : ℕ, b ≤ M b := by
    intro b
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · exact Nat.zero_le _
    · have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
      have hlog : 0 ≤ Real.log (b : ℝ) := Real.log_nonneg hb1
      have hfl : b ≤ ⌊(b : ℝ) * (1 + Real.log b)⌋₊ := Nat.le_floor (by nlinarith)
      rw [hMdef]
      omega
  have hM : Tendsto M atTop atTop := tendsto_atTop_mono hbM tendsto_id
  obtain ⟨ε', hε'def⟩ : ∃ ε' : ℕ → ℝ, ∀ b : ℕ, ε' b =
      (1 / 2 + ε (M b)) * (Real.log ((b : ℝ) * (2 + Real.log b)) / Real.log b) - 1 / 2 :=
    ⟨_, fun _ => rfl⟩
  have hεM : Tendsto (fun b => ε (M b)) atTop (𝓝 0) := hε.comp hM
  have hε' : Tendsto ε' atTop (𝓝 0) := by
    have h := ((hεM.const_add (1 / 2)).mul tendsto_log_ratio).sub_const (1 / 2)
    have hfun : ε' = fun b : ℕ => (1 / 2 + ε (M b)) *
        (Real.log ((b : ℝ) * (2 + Real.log b)) / Real.log b) - 1 / 2 := funext hε'def
    rw [hfun]
    simpa using h
  rw [Set.HasDensity, Metric.tendsto_nhds]
  intro η hη
  have hE2 := hM.eventually hA
  have hE3 : ∀ᶠ b in atTop, dist (ε (M b)) 0 < 1 / 2 :=
    Metric.tendsto_nhds.mp hεM (1 / 2) (by norm_num)
  have hE4 := h1 ε' hε' (η / 2) (by positivity)
  have hE5 : ∀ᶠ b : ℕ in atTop, 4 / η < (b : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_gt_atTop _
  filter_upwards [eventually_ge_atTop 2, hE2, hE3, hE4, hE5] with b hb2 hcount heps hppt hbig
  have hb1 : (2 : ℝ) ≤ b := by exact_mod_cast hb2
  have hbpos : (0 : ℝ) < b := by linarith
  have hlogb : 0 < Real.log (b : ℝ) := Real.log_pos (by linarith)
  have hAbpos : ∀ a ∈ (Finset.Ico 1 (M b)).filter (· ∈ A), 0 < a := by
    intro a ha
    exact (Finset.mem_Ico.mp (Finset.mem_filter.mp ha).1).1
  have he0 : 0 ≤ 1 / 2 + ε (M b) := by
    rw [Real.dist_eq, sub_zero] at heps
    have := (abs_lt.mp heps).1
    linarith
  have hRpos : 0 < (b : ℝ) * (2 + Real.log b) := mul_pos hbpos (by linarith)
  have hMR : ((M b : ℕ) : ℝ) ≤ (b : ℝ) * (2 + Real.log b) := by
    have hfl : ((⌊(b : ℝ) * (1 + Real.log b)⌋₊ : ℕ) : ℝ) ≤ (b : ℝ) * (1 + Real.log b) :=
      Nat.floor_le (mul_nonneg hbpos.le (by linarith))
    have hring : (b : ℝ) * (2 + Real.log b) = (b : ℝ) * (1 + Real.log b) + b := by ring
    rw [hMdef, hring]
    push_cast
    linarith
  have hpow : ((b : ℝ) * (2 + Real.log b)) ^ (1 / 2 + ε (M b)) =
      (b : ℝ) ^ ((1 / 2 : ℝ) + ε' b) := by
    rw [Real.rpow_def_of_pos hRpos, Real.rpow_def_of_pos hbpos, hε'def]
    congr 1
    field_simp
    ring
  have hcardAb : ((((Finset.Ico 1 (M b)).filter (· ∈ A)).card : ℕ) : ℝ) ≤
      (b : ℝ) ^ ((1 / 2 : ℝ) + ε' b) := by
    rw [← hpow]
    refine le_trans (le_trans (Nat.cast_le.mpr ?_) hcount)
      (Real.rpow_le_rpow (Nat.cast_nonneg _) hMR he0)
    rw [Nat.count_eq_card_filter_range]
    apply Finset.card_le_card
    intro x hx
    rw [Finset.mem_filter] at hx ⊢
    exact ⟨Finset.mem_range.mpr (Finset.mem_Ico.mp hx.1).2, hx.2⟩
  have hres := hppt _ hAbpos hcardAb
  have hsub : (Finset.range b).filter (fun n => Erdos955.s n ∈ A) ⊆
      {0, 1} ∪ (Finset.Icc 1 b).filter
        (fun n => Erdos955.s n ∈ (Finset.Ico 1 (M b)).filter (· ∈ A)) := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_range] at hn
    by_cases hn1 : n ≤ 1
    · apply Finset.mem_union_left
      rw [Finset.mem_insert, Finset.mem_singleton]
      omega
    · apply Finset.mem_union_right
      have hn2 : 2 ≤ n := by omega
      rw [Finset.mem_filter, Finset.mem_Icc, Finset.mem_filter, Finset.mem_Ico]
      refine ⟨⟨by omega, by omega⟩, ⟨s_pos_of_two_le hn2, ?_⟩, hn.2⟩
      have hσ := h2 n (by omega)
      have hnb : (n : ℝ) ≤ b := by exact_mod_cast hn.1.le
      have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
      have hlogn : Real.log (n : ℝ) ≤ Real.log b := Real.log_le_log (by linarith) hnb
      have hlogn0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1'
      have hle : (ArithmeticFunction.sigma 1 n : ℝ) ≤ (b : ℝ) * (1 + Real.log b) :=
        hσ.trans (mul_le_mul hnb (by linarith) (by linarith) (by linarith))
      have hfl : ArithmeticFunction.sigma 1 n ≤ ⌊(b : ℝ) * (1 + Real.log b)⌋₊ :=
        Nat.le_floor hle
      have hs : Erdos955.s n ≤ ArithmeticFunction.sigma 1 n := Nat.sub_le _ _
      rw [hMdef]
      omega
  have hcardC : ((((Finset.range b).filter (fun n => Erdos955.s n ∈ A)).card : ℕ) : ℝ) ≤
      2 + η / 2 * b := by
    have h1' := Finset.card_le_card hsub
    have h2' := Finset.card_union_le ({0, 1} : Finset ℕ) ((Finset.Icc 1 b).filter
      (fun n => Erdos955.s n ∈ (Finset.Ico 1 (M b)).filter (· ∈ A)))
    have h3' : ({0, 1} : Finset ℕ).card ≤ 2 := Finset.card_le_two
    have h4' : ((((Finset.range b).filter (fun n => Erdos955.s n ∈ A)).card : ℕ) : ℝ) ≤
        (2 : ℝ) + (((Finset.Icc 1 b).filter
          (fun n => Erdos955.s n ∈ (Finset.Ico 1 (M b)).filter (· ∈ A))).card : ℕ) := by
      exact_mod_cast (by omega :
        ((Finset.range b).filter (fun n => Erdos955.s n ∈ A)).card ≤
          2 + ((Finset.Icc 1 b).filter
            (fun n => Erdos955.s n ∈ (Finset.Ico 1 (M b)).filter (· ∈ A))).card)
    linarith
  have hset : (((Finset.range b).filter (fun n => Erdos955.s n ∈ A) : Finset ℕ) : Set ℕ) =
      {n | Erdos955.s n ∈ A} ∩ Set.Iio b := by
    ext n
    simp [and_comm]
  have hpd : ({n | Erdos955.s n ∈ A} : Set ℕ).partialDensity Set.univ b =
      ((((Finset.range b).filter (fun n => Erdos955.s n ∈ A)).card : ℕ) : ℝ) / b := by
    simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter, Nat.ncard_Iio, ← hset,
      Set.ncard_coe_finset]
  rw [Real.dist_eq, hpd, sub_zero, abs_of_nonneg (by positivity), div_lt_iff₀ hbpos]
  have h4 : 4 < b * η := (div_lt_iff₀ hη).mp hbig
  linarith

end OMA.R_Erdos955_erdos_955_variants_pollack_pomerance_thompson_bound_R1

end

section

/-! Pollack, Pomerance and Thompson, Divisor-sum fibers (2018), section 2,
arXiv:1706.03120. Split Theorem 1.2 at the four exceptional classes in its proof.
Outside those classes a fixed positive value has few preimages. Summation over the
target set and the two exceptional-set estimates give the uniform conclusion. -/

namespace OMA.R_Erdos955_erdos_955_variants_pollack_pomerance_thompson_bound_R1_H1_R1
open Filter Topology Finset
open scoped Classical

/-- The near-square-root divisor window in condition (b) of Theorem 1.2. -/
def H1 : Prop :=
  ∀ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) → ∀ δ : ℝ, 0 < δ → ∀ᶠ x : ℕ in atTop,
    let η := max (ε x) (1 / Real.log (Real.log x))
    let window := fun n : ℕ => ∃ d ∈ n.divisors,
      (x : ℝ) ^ ((1 / 2 : ℝ) - 10 * η) < d ∧ (d : ℝ) < (x : ℝ) ^ ((1 / 2 : ℝ) + 10 * η)
    (((Icc 1 x).filter window).card : ℝ) ≤ δ * x

/-- The small-prime, squarefull-divisor, and small-integer exceptions (a), (c), (d). -/
def H2 : Prop :=
  ∀ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) → ∀ δ : ℝ, 0 < δ → ∀ᶠ x : ℕ in atTop,
    let η := max (ε x) (1 / Real.log (Real.log x))
    let other := fun n : ℕ => (¬ ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ (p : ℝ) ≤ Real.log x) ∨
      (∃ q ∈ n.divisors, (x : ℝ) ^ (2 * η) < q ∧ ∀ p : ℕ, p.Prime → p ∣ q → p ^ 2 ∣ q) ∨ n ^ 2 ≤ x
    (((Icc 1 x).filter other).card : ℝ) ≤ δ * x

/-- A uniform bound on one positive fiber after deleting the four exceptional classes.
K bounds each individual fiber, including when the value is larger than x. -/
def H3 : Prop :=
  ∀ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) → ∀ δ : ℝ, 0 < δ → ∀ᶠ x : ℕ in atTop,
    let η := max (ε x) (1 / Real.log (Real.log x))
    let window := fun n : ℕ => ∃ d ∈ n.divisors,
      (x : ℝ) ^ ((1 / 2 : ℝ) - 10 * η) < d ∧ (d : ℝ) < (x : ℝ) ^ ((1 / 2 : ℝ) + 10 * η)
    let other := fun n : ℕ => (¬ ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ (p : ℝ) ≤ Real.log x) ∨
      (∃ q ∈ n.divisors, (x : ℝ) ^ (2 * η) < q ∧ ∀ p : ℕ, p.Prime → p ∣ q → p ^ 2 ∣ q) ∨ n ^ 2 ≤ x
    let good := (Icc 1 x).filter (fun n => ¬ window n ∧ ¬ other n)
    ∃ K : ℕ, (x : ℝ) ^ ((1 / 2 : ℝ) + ε x) * K ≤ δ * x ∧
      ∀ a : ℕ, 0 < a → (good.filter (fun n => Erdos955.s n = a)).card ≤ K

lemma finite_fiber_split (S A : Finset ℕ) (s : ℕ → ℕ) (P Q : ℕ → Prop)
    [DecidablePred P] [DecidablePred Q] (K : ℕ)
    (fiber : ∀ a ∈ A, ((S.filter (fun n => ¬ P n ∧ ¬ Q n)).filter
      (fun n => s n = a)).card ≤ K) :
    (S.filter (fun n => s n ∈ A)).card ≤
      (S.filter P).card + (S.filter Q).card + A.card * K := by
  let G := S.filter (fun n => ¬ P n ∧ ¬ Q n)
  have sub : S.filter (fun n => s n ∈ A) ⊆
      (S.filter P ∪ S.filter Q) ∪ G.filter (fun n => s n ∈ A) := by
    intro n hn
    obtain ⟨hnS, hnA⟩ := mem_filter.mp hn
    by_cases hp : P n
    · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hnS, hp⟩))
    by_cases hq : Q n
    · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨hnS, hq⟩))
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_filter.mpr ⟨hnS,hp,hq⟩,hnA⟩)
  have good : (G.filter (fun n => s n ∈ A)).card ≤ A.card * K := by
    rw [← sum_card_fiberwise_eq_card_filter G A s]
    calc
      _ ≤ ∑ _a ∈ A, K := sum_le_sum fiber
      _ = _ := by simp
  exact (card_le_card sub).trans <| (card_union_le ..).trans <|
    Nat.add_le_add (card_union_le ..) good

theorem main : H1 → H2 → H3 → OMA.R_Erdos955_erdos_955_variants_pollack_pomerance_thompson_bound_R1.H1 := by
  classical
  intro h₁ h₂ h₃ ε hε δ hδ
  have hpart : 0 < δ / 3 := by linarith
  filter_upwards [h₁ ε hε (δ / 3) hpart, h₂ ε hε (δ / 3) hpart,
    h₃ ε hε (δ / 3) hpart] with x hwindow hother hsingle
  intro A hpos hsize
  let η := max (ε x) (1 / Real.log (Real.log x))
  let window := fun n : ℕ => ∃ d ∈ n.divisors,
      (x : ℝ) ^ ((1 / 2 : ℝ) - 10 * η) < d ∧ (d : ℝ) < (x : ℝ) ^ ((1 / 2 : ℝ) + 10 * η)
  let other := fun n : ℕ => (¬ ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ (p : ℝ) ≤ Real.log x) ∨
      (∃ q ∈ n.divisors, (x : ℝ) ^ (2 * η) < q ∧ ∀ p : ℕ, p.Prime → p ∣ q → p ^ 2 ∣ q) ∨ n ^ 2 ≤ x
  obtain ⟨K,hK,hfiber⟩ := hsingle
  have htotal := finite_fiber_split (Icc 1 x) A Erdos955.s window other K
    (fun a ha => hfiber a (hpos a ha))
  have hcount : (((Icc 1 x).filter (fun n => Erdos955.s n ∈ A)).card : ℝ) ≤
      (((Icc 1 x).filter window).card : ℝ) + (((Icc 1 x).filter other).card : ℝ) +
      (A.card : ℝ) * K := by exact_mod_cast htotal
  change (((Icc 1 x).filter window).card : ℝ) ≤ δ / 3 * x at hwindow
  change (((Icc 1 x).filter other).card : ℝ) ≤ δ / 3 * x at hother
  have hprod := mul_le_mul_of_nonneg_right hsize (Nat.cast_nonneg (α := ℝ) K)
  linarith

end OMA.R_Erdos955_erdos_955_variants_pollack_pomerance_thompson_bound_R1_H1_R1

end

section

namespace Erdos955.Window
open Filter Topology

theorem clipped_window_tendsto (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun x : ℕ => max (ε x) (1/Real.log (Real.log x))) atTop (𝓝 0) := by
  have c : Tendsto (fun x : ℕ => (x:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have l := Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp c)
  have t := (tendsto_inv_atTop_zero (𝕜:=ℝ)).comp l
  simpa [Function.comp_def,one_div] using hε.max t

end Erdos955.Window

end

section

namespace Erdos955.Window
open Filter Topology

/-- Powers x^t of a natural argument tend to infinity for fixed t>0. -/
theorem window_power_at_top {t : ℝ} (ht : 0<t) :
    Tendsto (fun x : ℕ => (x:ℝ)^t) atTop atTop := by
  have cast : Tendsto (fun x : ℕ => (x:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have lg := Real.tendsto_log_atTop.comp cast
  have lim := Real.tendsto_exp_atTop.comp ((tendsto_mul_const_atTop_of_pos ht).mpr lg)
  apply lim.congr'
  filter_upwards [cast.eventually_gt_atTop (0:ℝ)] with x hx
  exact (Real.rpow_def_of_pos hx t).symm

/-- For fixed cutoffs, all finite-x losses disappear. A collects the smooth-part
and large-factor exceptions, B the strip cost, and w is its limiting width. -/
theorem window_large_x_budget {t A B w δ : ℝ} (ht : 0<t) (gap : A+B*w<δ)
    (h : ℕ → ℝ) (small : Tendsto h atTop (𝓝 0)) :
    ∀ᶠ x : ℕ in atTop, (x:ℝ)^(9/10:ℝ) + A*x + x/(⌊(x:ℝ)^t⌋₊:ℝ)
      + B*x*(1/Real.log x+h x+w) ≤ δ*x := by
  have cast : Tendsto (fun x : ℕ => (x:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have logInv := (tendsto_inv_atTop_zero (𝕜:=ℝ)).comp (Real.tendsto_log_atTop.comp cast)
  have lo := (tendsto_inv_atTop_zero (𝕜:=ℝ)).comp (window_power_at_top (by norm_num : (0:ℝ)<1/10))
  have square := (tendsto_inv_atTop_zero (𝕜:=ℝ)).comp
    (cast.comp (tendsto_nat_floor_atTop.comp (window_power_at_top ht)))
  have tail : Tendsto (fun x : ℕ => ((x:ℝ)^(1/10:ℝ))⁻¹ + A + ((⌊(x:ℝ)^t⌋₊:ℝ))⁻¹ +
    B * (1/Real.log x+h x+w)) atTop (𝓝 (A+B*w)) := by
    simpa [Function.comp_def,one_div] using
      (((lo.add (tendsto_const_nhds (x:=A))).add square).add
        ((tendsto_const_nhds (x:=B)).mul ((logInv.add small).add (tendsto_const_nhds (x:=w)))))
  filter_upwards [tail.eventually_lt_const gap,cast.eventually_gt_atTop (0:ℝ)] with x hx pos
  have scaled := mul_le_mul_of_nonneg_right hx.le pos.le
  have eq : ((x:ℝ)^(1/10:ℝ))⁻¹ * x = (x:ℝ)^(9/10:ℝ) := by
    rw [←Real.rpow_neg pos.le]
    conv_lhs => rhs; rw [←Real.rpow_one (x:ℝ)]
    rw [←Real.rpow_add pos]
    norm_num
  calc _ = (((x:ℝ)^(1/10:ℝ))⁻¹ + A + ((⌊(x:ℝ)^t⌋₊:ℝ))⁻¹ +
      B * (1/Real.log x+h x+w)) * x := by rw [←eq]; ring
       _ ≤ _ := scaled

end Erdos955.Window

end

section

namespace Erdos955.Window
open Finset

/-- Compare prime valuations of factorials without asymptotic constants. -/
lemma factorial_valuation_compare {p Y : ℕ} (hp : p.Prime) (hY : p ≤ Y) (X : ℕ) :
    Y * X.factorial.factorization p ≤ 4 * X * Y.factorial.factorization p := by
  let v := X.factorial.factorization p
  let w := Y.factorial.factorization p
  have lower : Y/p ≤ w := by
    dsimp [w]
    rw [Nat.factorization_factorial hp (show Nat.log p Y < Nat.log p Y + 2 by omega)]
    have hmem : 1 ∈ Ico 1 (Nat.log p Y + 2) := mem_Ico.mpr (by omega)
    simpa using (single_le_sum (f := fun i => Y/p^i) (fun i _ => Nat.zero_le _) hmem)
  have hq : 1 ≤ Y/p := (Nat.le_div_iff_mul_le hp.pos).mpr (by simpa)
  have hmod := Nat.mod_lt Y hp.pos
  have heq := Nat.mod_add_div Y p
  have hmul : p ≤ p * (Y/p) := by simpa using Nat.mul_le_mul_left p hq
  have ybound : Y ≤ 2*w*p := by
    calc
      Y ≤ 2*(Y/p)*p := by rw [Nat.mul_assoc, Nat.mul_comm (Y/p) p]; omega
      _ ≤ 2*w*p := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ lower)
  have ub : v*(p-1) ≤ X :=
    (Nat.mul_le_mul_right _ (Nat.factorization_factorial_le_div_pred hp X)).trans (Nat.div_mul_le_self ..)
  have pbound : p*v ≤ 2*X := by
    have htwo := hp.two_le
    calc
      p*v ≤ (2*(p-1))*v := Nat.mul_le_mul_right _ (by omega)
      _ = 2*(v*(p-1)) := by ring
      _ ≤ _ := Nat.mul_le_mul_left 2 ub
  calc
    Y*v ≤ (2*w*p)*v := Nat.mul_le_mul_right _ ybound
    _ = (2*w)*(p*v) := Nat.mul_assoc .. 
    _ ≤ (2*w)*(2*X) := Nat.mul_le_mul_left _ pbound
    _ = _ := by ring

/-- The logarithmic mass of the prime factors at most Y, counted with multiplicity. -/
noncomputable def smallPrimeLog (Y n : ℕ) : ℝ :=
  ∑ p ∈ (Icc 1 Y).filter Nat.Prime, (n.factorization p : ℝ) * Real.log p

lemma smallPrimeLog_nonneg (Y n : ℕ) : 0 ≤ smallPrimeLog Y n := by
  apply sum_nonneg
  intro p hp
  exact mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by exact_mod_cast (mem_Icc.mp (mem_filter.mp hp).1).1))

lemma smallPrimeLog_le_log (Y n : ℕ) : smallPrimeLog Y n ≤ Real.log n := by
  rw [Real.log_nat_eq_sum_factorization, Finsupp.sum]
  let f := fun p : ℕ => (n.factorization p : ℝ) * Real.log p
  let S := (Icc 1 Y).filter Nat.Prime
  change ∑ p ∈ S, f p ≤ ∑ p ∈ n.factorization.support, f p
  calc
    _ = ∑ p ∈ S ∩ n.factorization.support, f p := by
      symm
      apply sum_subset (inter_subset_left ..)
      intro p hp hout
      have hnot : p ∉ n.factorization.support := fun hm => hout (mem_inter.mpr ⟨hp, hm⟩)
      simp [f, Finsupp.notMem_support_iff.mp hnot]
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (inter_subset_right ..) (by
      intro p hp _
      have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
      exact mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by exact_mod_cast hprime.one_lt.le)))

lemma smallPrimeLog_sum (Y X : ℕ) :
    ∑ n ∈ Icc 1 X, smallPrimeLog Y n = smallPrimeLog Y X.factorial := by
  unfold smallPrimeLog
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro p _
  rw [← sum_mul, ← Nat.cast_sum]
  congr 2
  rw [← Nat.factorization_prod_apply (fun n (hn : n ∈ Icc 1 X) =>
    show n ≠ 0 from Nat.ne_of_gt (mem_Icc.mp hn).1)]
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.prod_Ico_id_eq_factorial]

lemma smallPrimeLog_first_moment {Y : ℕ} (hY : 0 < Y) (X : ℕ) :
    ∑ n ∈ Icc 1 X, smallPrimeLog Y n ≤ 4 * X * Real.log Y := by
  rw [smallPrimeLog_sum]
  apply (mul_le_mul_iff_right₀ (Nat.cast_pos.mpr hY : (0:ℝ) < Y)).mp
  have hfact : Real.log (Y.factorial : ℝ) ≤ Y * Real.log Y := by
    have h := Real.log_le_log (Nat.cast_pos.mpr Y.factorial_pos)
      (show (Y.factorial : ℝ) ≤ (Y : ℝ)^Y by exact_mod_cast Y.factorial_le_pow)
    simpa using h
  calc
    (Y : ℝ) * smallPrimeLog Y X.factorial ≤ (4*X) * smallPrimeLog Y Y.factorial := by
      simp only [smallPrimeLog, mul_sum]
      apply sum_le_sum
      intro p hp
      obtain ⟨hpI, hprime⟩ := mem_filter.mp hp
      have h := factorial_valuation_compare hprime (mem_Icc.mp hpI).2 X
      have hreal : (Y : ℝ) * X.factorial.factorization p ≤ 4*X*(Y.factorial.factorization p : ℝ) := by exact_mod_cast h
      rw [← mul_assoc, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right hreal (Real.log_nonneg (by exact_mod_cast hprime.one_lt.le))
    _ ≤ (4*X) * (Y * Real.log Y) := mul_le_mul_of_nonneg_left
      ((smallPrimeLog_le_log Y _).trans hfact) (by positivity)
    _ = _ := by ring

end Erdos955.Window

end

section

namespace Erdos955.Window
open Finset
open scoped Classical

lemma smooth_divisor_log_le {s n Y : ℕ} (hn : 0 < n) (hdiv : s ∣ n)
    (hsmooth : ∀ p : ℕ, p.Prime → p ∣ s → p ≤ Y) :
    Real.log s ≤ smallPrimeLog Y n := by
  have hs := Nat.pos_of_dvd_of_pos hdiv hn
  have le := (Nat.factorization_le_iff_dvd hs.ne' hn.ne').mpr hdiv
  rw [Real.log_nat_eq_sum_factorization, Finsupp.sum, smallPrimeLog]
  let S := (Icc 1 Y).filter Nat.Prime
  have sub : s.factorization.support ⊆ S := by
    intro p hp
    have prime := Nat.prime_of_mem_primeFactors hp
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨prime.one_lt.le,
      hsmooth p prime (Nat.dvd_of_mem_primeFactors hp)⟩, prime⟩
  calc
    _ ≤ ∑ p ∈ s.factorization.support, (n.factorization p : ℝ) * Real.log p := by
      apply sum_le_sum
      intro p hp
      exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (le p))
        (Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt.le))
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg sub (by
      intro p hp _
      exact mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by exact_mod_cast (mem_Icc.mp (mem_filter.mp hp).1).1)))

lemma smooth_divisor_tail (X Y : ℕ) (L : ℝ) (hY : 0 < Y) (E : Finset ℕ)
    (member : ∀ n ∈ E, n ∈ Icc 1 X ∧ ∃ s : ℕ, s ∣ n ∧ L ≤ Real.log s ∧
        ∀ p : ℕ, p.Prime → p ∣ s → p ≤ Y) :
    (E.card : ℝ)*L ≤ 4*X*Real.log Y := by
  calc
    _ = ∑ _n ∈ E, L := by simp
    _ ≤ ∑ n ∈ E, smallPrimeLog Y n := by
      apply sum_le_sum
      intro n hn
      obtain ⟨hx,s,hdiv,hl,hp⟩ := member n hn
      exact hl.trans (smooth_divisor_log_le (mem_Icc.mp hx).1 hdiv hp)
    _ ≤ ∑ n ∈ Icc 1 X, smallPrimeLog Y n := sum_le_sum_of_subset_of_nonneg
      (fun n hn => (member n hn).1) (fun n _ _ => smallPrimeLog_nonneg Y n)
    _ ≤ _ := smallPrimeLog_first_moment hY X

/-- A form that composes with any exceptional set of integers. Integers admitting a
divisor exceeding X^v, all of whose prime factors are at most X^u, have density ≤4u/v. -/
theorem smooth_divisor_power_tail (X : ℕ) (hx : 1 < X) {u v : ℝ} (hu : 0 ≤ u) (hv : 0 < v)
    (E : Finset ℕ) (member : ∀ n ∈ E, n ∈ Icc 1 X ∧ ∃ s : ℕ, s ∣ n ∧
      (X : ℝ)^v ≤ s ∧ ∀ p : ℕ, p.Prime → p ∣ s → (p : ℝ) ≤ (X : ℝ)^u) :
    (E.card : ℝ) ≤ (4*u/v)*X := by
  have hxR : (1 : ℝ) < X := by exact_mod_cast hx
  let Y := ⌊(X : ℝ)^u⌋₊
  have hY : 0 < Y := Nat.le_floor (by simpa using Real.one_le_rpow hxR.le hu)
  have hxpos : (0 : ℝ) < X := by linarith
  have hlog := Real.log_pos hxR
  have hh : (E.card : ℝ)*(v*Real.log X) ≤ 4*X*Real.log Y := by
    apply smooth_divisor_tail X Y _ hY E
    intro n hn
    obtain ⟨hI,s,hd,hbig,hp⟩ := member n hn
    refine ⟨hI,s,hd,?_,fun p hp' hps => Nat.le_floor (hp p hp' hps)⟩
    have h := Real.log_le_log (Real.rpow_pos_of_pos hxpos _) hbig
    simpa [Real.log_rpow hxpos, mul_comm] using h
  have hylog : Real.log Y ≤ u*Real.log X := by
    have h := Real.log_le_log (Nat.cast_pos.mpr hY) (Nat.floor_le (Real.rpow_nonneg hxpos.le u))
    simpa [Real.log_rpow hxpos, mul_comm] using h
  apply (mul_le_mul_iff_left₀ (mul_pos hv hlog)).mp
  calc
    (E.card : ℝ) * (v*Real.log X) ≤ 4*X*(u*Real.log X) :=
      hh.trans (mul_le_mul_of_nonneg_left hylog (by positivity))
    _ = _ := by field_simp

end Erdos955.Window

end

section

namespace Erdos955.PPT

/-- A positive powerful number has a square divisor whose square root is at
least its cube root. Take half of each prime exponent, rounded down. -/
theorem powerful_square_divisor {q : ℕ} (hq : 0 < q)
    (powerful : ∀ p : ℕ, p.Prime → p ∣ q → p ^ 2 ∣ q) :
    ∃ t : ℕ, t ^ 2 ∣ q ∧ q ≤ t ^ 3 := by
  let t := ∏ p ∈ q.primeFactors, p ^ (q.factorization p / 2)
  have repr := Nat.prod_primeFactors_pow_factorization (Nat.ne_of_gt hq)
  refine ⟨t, ?_, ?_⟩
  · have div : t ^ 2 ∣ ∏ p ∈ q.primeFactors, p ^ q.factorization p := by
      change (∏ p ∈ q.primeFactors, p ^ (q.factorization p / 2)) ^ 2 ∣ _
      rw [← Finset.prod_pow]
      apply Finset.prod_dvd_prod_of_dvd
      intro p _
      rw [← pow_mul]
      apply pow_dvd_pow
      omega
    simpa only [← repr] using div
  · calc
      q = ∏ p ∈ q.primeFactors, p ^ q.factorization p := repr
      _ ≤ ∏ p ∈ q.primeFactors, (p ^ (q.factorization p / 2)) ^ 3 := by
        apply Finset.prod_le_prod'
        intro p hp
        have pp := Nat.prime_of_mem_primeFactors hp
        have he := (pp.pow_dvd_iff_le_factorization (Nat.ne_of_gt hq)).1
          (powerful p pp (Nat.dvd_of_mem_primeFactors hp))
        rw [← pow_mul]
        exact Nat.pow_le_pow_right pp.pos (by omega)
      _ = t ^ 3 := Finset.prod_pow ..

end Erdos955.PPT

end

section

namespace Erdos955.PPT

/-- The square-multiple count at k+1 fits inside the drop between the counts of
multiples of k and k+1. This version works with floors throughout. -/
theorem square_quotient_step (N k : ℕ) (hk : 0 < k) :
    N / (k + 1) ^ 2 + N / (k + 1) ≤ N / k := by
  apply (Nat.le_div_iff_mul_le hk).2
  have small : N / (k + 1) ^ 2 * k ≤ N / (k + 1) := by
    rw [pow_two, ← Nat.div_div_eq_div_mul]
    exact (Nat.mul_le_mul_left _ (Nat.le_succ k)).trans (Nat.div_mul_le_self ..)
  calc
    (N / (k + 1) ^ 2 + N / (k + 1)) * k =
        N / (k + 1) ^ 2 * k + N / (k + 1) * k := Nat.add_mul ..
    _ ≤ N / (k + 1) + N / (k + 1) * k := Nat.add_le_add_right small _
    _ = N / (k + 1) * (k + 1) := by rw [Nat.mul_succ, Nat.add_comm]
    _ ≤ N := Nat.div_mul_le_self ..

/-- Sum the integer majorants over a finite interval of square divisors. -/
theorem square_quotient_sum (N U r : ℕ) (hU : 0 < U) :
    (∑ i ∈ Finset.range r, N / (U + i + 1) ^ 2) + N / (U + r) ≤ N / U := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Finset.sum_range_succ, Nat.add_succ, Nat.add_assoc]
    exact (Nat.add_le_add_left (square_quotient_step N (U+r) (by omega)) _).trans ih

theorem square_divisor_union_bound {N U : ℕ} (hU : 0 < U) (S : Finset ℕ)
    (member : ∀ n ∈ S, 0 < n ∧ n ≤ N ∧ ∃ t, U < t ∧ t ^ 2 ∣ n) :
    S.card ≤ N / U := by
  let A (i : ℕ) := (Finset.Ioc 0 N).filter fun n => (U + i + 1) ^ 2 ∣ n
  have sub : S ⊆ (Finset.range N).biUnion A := by
    intro n hn
    obtain ⟨pos,hi,t,ht,hd⟩ := member n hn
    have htn := (Nat.le_self_pow (by decide : 2 ≠ 0) t).trans (Nat.le_of_dvd pos hd)
    let i := t - (U + 1)
    have hsum : U + i + 1 = t := by dsimp [i]; omega
    apply Finset.mem_biUnion.mpr
    refine ⟨i, Finset.mem_range.mpr (by dsimp [i]; omega), ?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨pos,hi⟩, hsum.symm ▸ hd⟩
  have sizes (i : ℕ) : (A i).card = N / (U + i + 1) ^ 2 :=
    Nat.Ioc_filter_dvd_card_eq_div ..
  calc
    S.card ≤ ((Finset.range N).biUnion A).card := Finset.card_le_card sub
    _ ≤ ∑ i ∈ Finset.range N, (A i).card := Finset.card_biUnion_le
    _ = ∑ i ∈ Finset.range N, N / (U + i + 1) ^ 2 := Finset.sum_congr rfl fun i _ => sizes i
    _ ≤ N / U := (Nat.le_add_right ..).trans (square_quotient_sum N U N hU)

/-- A positive multiple of a powerful divisor q > U³ has a square divisor t²
with t > U, so there are at most floor(N/U) such numbers up to N. -/
theorem powerful_divisor_union_bound {N U : ℕ} (hU : 0 < U) (S : Finset ℕ)
    (member : ∀ n ∈ S, 0 < n ∧ n ≤ N ∧ ∃ q, U ^ 3 < q ∧ q ∣ n ∧
      ∀ p : ℕ, p.Prime → p ∣ q → p ^ 2 ∣ q) :
    S.card ≤ N / U := by
  apply square_divisor_union_bound hU S
  intro n hn
  obtain ⟨pos,hi,q,hq,hd,hpow⟩ := member n hn
  obtain ⟨t,ht,hcube⟩ := powerful_square_divisor (Nat.zero_lt_of_lt hq) hpow
  have large : U < t := by
    by_cases h : U < t
    · exact h
    have rev := Nat.pow_le_pow_left (Nat.le_of_not_gt h) 3
    omega
  exact ⟨pos,hi,t,large,dvd_trans ht hd⟩

open Classical in
theorem count_large_square_divisors (N U : ℕ) (hU : 0 < U) :
    ((Finset.Ioc 0 N).filter (fun n => ∃ t, U < t ∧ t ^ 2 ∣ n)).card ≤ N / U := by
  apply square_divisor_union_bound hU
  intro n hn
  obtain ⟨range,large⟩ := Finset.mem_filter.mp hn
  exact ⟨(Finset.mem_Ioc.mp range).1,(Finset.mem_Ioc.mp range).2,large⟩

open Classical in
theorem count_large_powerful_divisors (N U : ℕ) (hU : 0 < U) :
    ((Finset.Ioc 0 N).filter (fun n => ∃ q, U ^ 3 < q ∧ q ∣ n ∧
      ∀ p : ℕ, p.Prime → p ∣ q → p ^ 2 ∣ q)).card ≤ N / U := by
  apply powerful_divisor_union_bound hU
  intro n hn
  obtain ⟨range,large⟩ := Finset.mem_filter.mp hn
  exact ⟨(Finset.mem_Ioc.mp range).1,(Finset.mem_Ioc.mp range).2,large⟩

end Erdos955.PPT

end

section

namespace Erdos955.Window
open Finset

/-- The product of the full prime-power factors with prime base at most `Y`. -/
noncomputable def primeSmoothPart (n : ℕ) (Y : ℝ) : ℕ :=
  ∏ p ∈ n.primeFactors.filter (fun p : ℕ => (p : ℝ) ≤ Y), p ^ n.factorization p

def isSmoothAt (s : ℕ) (Y : ℝ) : Prop := ∀ p : ℕ, p.Prime → p ∣ s → (p : ℝ) ≤ Y

theorem primeSmoothPart_dvd {n : ℕ} (hn : n ≠ 0) (Y : ℝ) : primeSmoothPart n Y ∣ n := by
  nth_rw 2 [Nat.prod_primeFactors_pow_factorization hn]
  exact prod_dvd_prod_of_subset _ _ _ (filter_subset _ _)

theorem primeSmoothPart_isSmooth (n : ℕ) (Y : ℝ) : isSmoothAt (primeSmoothPart n Y) Y := by
  intro p hp hdiv
  obtain ⟨q, hq, hpow⟩ := (hp.prime.dvd_finsetProd_iff _).mp hdiv
  obtain ⟨hq, hsmall⟩ := mem_filter.mp hq
  exact ((Nat.prime_dvd_prime_iff_eq hp (Nat.prime_of_mem_primeFactors hq)).mp
    (hp.dvd_of_dvd_pow hpow)) ▸ hsmall

/-- The complement of the smooth part is squarefree if the large prime squares
are absent. Its support is precisely the large primes of the integer. -/
theorem smooth_mul_large {r n : ℕ} {T : ℝ} (hn : n ≠ 0) (hr : r ∣ n)
    (hsq : ∀ p : ℕ, p.Prime → T < (p : ℝ) → ¬p ^ 2 ∣ n) :
    r = primeSmoothPart r T * ∏ p ∈ r.primeFactors.filter (fun p : ℕ => T < (p : ℝ)), p := by
  have hr0 := (Nat.pos_of_dvd_of_pos hr (Nat.pos_of_ne_zero hn)).ne'
  calc
    r = ∏ p ∈ r.primeFactors, p ^ r.factorization p := Nat.prod_primeFactors_pow_factorization hr0
    _ = primeSmoothPart r T * ∏ p ∈ r.primeFactors.filter (fun p : ℕ => T < (p : ℝ)), p ^ r.factorization p := by
      simpa only [primeSmoothPart, not_le] using (prod_filter_mul_prod_filter_not r.primeFactors
        (fun p : ℕ => (p : ℝ) ≤ T) (fun p => p ^ r.factorization p)).symm
    _ = _ := by
      congr 1
      apply prod_congr rfl
      intro p hp
      obtain ⟨hp,hbig⟩ := mem_filter.mp hp
      have hprime := Nat.prime_of_mem_primeFactors hp
      have hpos := hprime.factorization_pos_of_dvd hr0 (Nat.dvd_of_mem_primeFactors hp)
      have hlt : ¬2 ≤ r.factorization p := fun h =>
        hsq p hprime hbig (((hprime.pow_dvd_iff_le_factorization hr0).mpr h).trans hr)
      simp [show r.factorization p = 1 by omega]

private theorem TwoPrimeRepresentation_exists_large_prime {r n : ℕ} {C E : ℝ} (hr : r ∣ n) (hlarge : E < (r : ℝ))
    (hsmall : ∀ s : ℕ, s ∣ n → isSmoothAt s C → (s : ℝ) ≤ E) :
    ∃ p : ℕ, p.Prime ∧ p ∣ r ∧ C < (p : ℝ) := by
  by_contra! h
  exact hlarge.not_ge (hsmall r hr (fun p hp hd => h p hp hd))

/-- Encode a divisor in the window using one large prime from each complementary
factor and a subset of the large prime divisors of the remaining integer. -/
theorem two_prime_representation {n d e : ℕ} (hn : 0 < n) (hde : n = d * e)
    {C T E S : ℝ} (hd : E < (d : ℝ)) (he : E < (e : ℝ))
    (hcoarse : ∀ s : ℕ, s ∣ n → isSmoothAt s C → (s : ℝ) ≤ E)
    (hfine : ∀ s : ℕ, s ∣ n → isSmoothAt s T → (s : ℝ) ≤ S)
    (hsq : ∀ p : ℕ, p.Prime → T < (p : ℝ) → ¬p^2 ∣ n) :
    ∃ (m p q s : ℕ) (U : Finset ℕ), n = m * p * q ∧ 0 < m ∧
      p.Prime ∧ C < (p : ℝ) ∧ q.Prime ∧ C < (q : ℝ) ∧
      U ⊆ m.primeFactors.filter (fun r : ℕ => T < (r : ℝ)) ∧
      0 < s ∧ s ∣ n ∧ (s : ℝ) ≤ S ∧ d = p * s * ∏ r ∈ U, r := by
  have hdn : d ∣ n := hde ▸ dvd_mul_right _ _
  have hen : e ∣ n := hde ▸ dvd_mul_left _ _
  obtain ⟨p,hp,⟨u,hu⟩,hCp⟩ := TwoPrimeRepresentation_exists_large_prime hdn hd hcoarse
  obtain ⟨q,hq,⟨v,hv⟩,hCq⟩ := TwoPrimeRepresentation_exists_large_prime hen he hcoarse
  have hun : u ∣ n := (show u ∣ d from hu ▸ dvd_mul_left _ _).trans hdn
  have hu0 : 0 < u := Nat.pos_of_dvd_of_pos hun hn
  have hrepr : n = (u*v)*p*q := by rw [hde, hu, hv]; ac_rfl
  have hm : 0 < u*v := Nat.pos_of_dvd_of_pos
    (show u*v ∣ n by rw [hrepr]; exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _) hn
  let U := u.primeFactors.filter (fun r : ℕ => T < (r : ℝ))
  have hsu := primeSmoothPart_dvd hu0.ne' T
  refine ⟨u*v, p, q, primeSmoothPart u T, U, hrepr, hm, hp, hCp, hq, hCq,
    ?_, Nat.pos_of_dvd_of_pos hsu hu0, hsu.trans hun,
    hfine _ (hsu.trans hun) (primeSmoothPart_isSmooth u T), ?_⟩
  · exact filter_subset_filter _ (Nat.primeFactors_mono (dvd_mul_right _ _) hm.ne')
  · calc d = p*u := hu
         _ = p*(primeSmoothPart u T * ∏ r ∈ U, r) := congrArg (p * ·) (smooth_mul_large hn.ne' hun hsq)
         _ = _ := (mul_assoc ..).symm

end Erdos955.Window

end

section

namespace Erdos955.Window
open scoped Classical

def retained (x : ℕ) (c t : ℝ) (n : ℕ) : Prop :=
  (x : ℝ)^(9/10 : ℝ) < n ∧
  (∀ s : ℕ, s ∣ n → isSmoothAt s ((x : ℝ)^c) → (s : ℝ) ≤ (x : ℝ)^(1/4 : ℝ)) ∧
  (∀ s : ℕ, s ∣ n → isSmoothAt s ((x : ℝ)^t) → (s : ℝ) ≤ (x : ℝ)^(t^(99/100 : ℝ))) ∧
  (∀ p : ℕ, p.Prime → (x : ℝ)^t < p → ¬ p^2 ∣ n) ∧
  ((n.primeFactors.filter (fun p : ℕ => (x : ℝ)^t < (p : ℝ))).card : ℝ) <
    (142/100:ℝ)*Real.log (1/t)

end Erdos955.Window

end

section

namespace Erdos955.Window
open Finset
open scoped Classical

/-- Quantitative decomposition into the five exceptional classes and the retained set. -/
theorem discard_window_exceptions (x : ℕ) (hx : 1 < x) {c t M G : ℝ}
    (hc : 0 ≤ c) (ht : 0 < t) (W : Finset ℕ) (hW : W ⊆ Icc 1 x)
    (hmany : ∀ E : Finset ℕ, (∀ n ∈ E, n ∈ Icc 1 x ∧
        (142/100:ℝ)*Real.log (1/t) ≤ ((n.primeFactors.filter (fun p : ℕ => (x : ℝ)^t < (p : ℝ))).card : ℝ)) →
        (E.card : ℝ) ≤ M)
    (hgood : ∀ E : Finset ℕ, E ⊆ W → (∀ n ∈ E, retained x c t n) → (E.card : ℝ) ≤ G) :
    (W.card : ℝ) ≤ (x : ℝ)^(9/10:ℝ) + (16*c)*x + (4*t/t^(99/100:ℝ))*x +
      x/(⌊(x:ℝ)^t⌋₊ : ℝ) + M + G := by
  classical
  let S := W.filter (fun n : ℕ => (n : ℝ) ≤ (x : ℝ)^(9/10 : ℝ))
  let C := W.filter (fun n : ℕ => ∃ s : ℕ, s∣n ∧ isSmoothAt s ((x:ℝ)^c) ∧ (x:ℝ)^(1/4:ℝ) < s)
  let F := W.filter (fun n : ℕ => ∃ s : ℕ, s∣n ∧ isSmoothAt s ((x:ℝ)^t) ∧ (x:ℝ)^(t^(99/100:ℝ)) < s)
  let Q := W.filter (fun n : ℕ => ∃ p : ℕ, p.Prime ∧ (x:ℝ)^t < p ∧ p^2 ∣ n)
  let H := W.filter (fun n : ℕ => (142/100:ℝ)*Real.log (1/t) ≤
    ((n.primeFactors.filter (fun p : ℕ => (x:ℝ)^t < (p : ℝ))).card : ℝ))
  let R := W.filter (retained x c t)
  have sub : W ⊆ ((((S ∪ C) ∪ F) ∪ Q) ∪ H) ∪ R := by
    intro n hn
    simp only [S,C,F,Q,H,R,mem_union,mem_filter,hn,true_and]
    by_cases hs : (n:ℝ) ≤ (x:ℝ)^(9/10:ℝ)
    · exact (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hs)))))
    by_cases hc' : ∃ s : ℕ, s∣n ∧ isSmoothAt s ((x:ℝ)^c) ∧ (x:ℝ)^(1/4:ℝ) < s
    · exact (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hc')))))
    by_cases hf : ∃ s : ℕ, s∣n ∧ isSmoothAt s ((x:ℝ)^t) ∧ (x:ℝ)^(t^(99/100:ℝ)) < s
    · exact (Or.inl (Or.inl (Or.inl (Or.inr hf))))
    by_cases hq : ∃ p : ℕ, p.Prime ∧ (x:ℝ)^t < p ∧ p^2 ∣ n
    · exact (Or.inl (Or.inl (Or.inr hq)))
    by_cases hh : (142/100:ℝ)*Real.log (1/t) ≤ ((n.primeFactors.filter (fun p : ℕ => (x:ℝ)^t < (p : ℝ))).card : ℝ)
    · exact (Or.inl (Or.inr hh))
    right
    exact ⟨lt_of_not_ge hs,fun s hd hv => le_of_not_gt (fun hg => hc' ⟨s,hd,hv,hg⟩),
      fun s hd hv => le_of_not_gt (fun hg => hf ⟨s,hd,hv,hg⟩),
      fun p hp hpt hp2 => hq ⟨p,hp,hpt,hp2⟩,lt_of_not_ge hh⟩
  have total : W.card ≤ S.card + C.card + F.card + Q.card + H.card + R.card := by
    have h0 := card_le_card sub
    have h1 := card_union_le S C
    have h2 := card_union_le (S ∪ C) F
    have h3 := card_union_le ((S ∪ C) ∪ F) Q
    have h4 := card_union_le (((S ∪ C) ∪ F) ∪ Q) H
    have h5 := card_union_le ((((S ∪ C) ∪ F) ∪ Q) ∪ H) R
    omega
  have hS : (S.card : ℝ) ≤ (x : ℝ)^(9/10:ℝ) := by
    have hs : S ⊆ Icc 1 ⌊(x:ℝ)^(9/10:ℝ)⌋₊ := fun n hn =>
      mem_Icc.mpr ⟨(mem_Icc.mp (hW (mem_filter.mp hn).1)).1, Nat.le_floor (mem_filter.mp hn).2⟩
    have hnat := card_le_card hs
    simp at hnat
    exact (Nat.cast_le.mpr hnat).trans (Nat.floor_le (Real.rpow_nonneg (by positivity) _))
  have hC : (C.card : ℝ) ≤ (16*c)*x := by
    have bound := smooth_divisor_power_tail x hx hc (show 0 < (1/4:ℝ) by norm_num) C
    apply le_trans (bound ?_)
    · apply le_of_eq; ring
    · intro n hn
      obtain ⟨hw,s,hd,sm,hi⟩ := mem_filter.mp hn
      exact ⟨hW hw,s,hd,hi.le,sm⟩
  have hF : (F.card : ℝ) ≤ (4*t/t^(99/100:ℝ))*x := by
    apply smooth_divisor_power_tail x hx ht.le (Real.rpow_pos_of_pos ht _)
    intro n hn
    obtain ⟨hw,s,hd,sm,hi⟩ := mem_filter.mp hn
    exact ⟨hW hw,s,hd,hi.le,sm⟩
  have hX : (1:ℝ) ≤ x := by exact_mod_cast hx.le
  have hy : 0 < ⌊(x:ℝ)^t⌋₊ := Nat.le_floor (by simpa using Real.one_le_rpow hX ht.le)
  have hQ : (Q.card : ℝ) ≤ x/(⌊(x:ℝ)^t⌋₊ : ℝ) := by
    have hsq := Erdos955.PPT.square_divisor_union_bound hy Q (by
      intro n hn
      obtain ⟨hw,p,_,hpt,hpn⟩ := mem_filter.mp hn
      have hpos := (mem_Icc.mp (hW hw))
      refine ⟨hpos.1,hpos.2,p,?_,hpn⟩
      exact Nat.floor_lt (Real.rpow_nonneg (by positivity) _) |>.mpr hpt)
    apply (le_div_iff₀ (Nat.cast_pos.mpr hy)).mpr
    exact_mod_cast ((Nat.le_div_iff_mul_le hy).mp hsq)
  have hH := hmany H (fun n hn => ⟨hW (mem_filter.mp hn).1,(mem_filter.mp hn).2⟩)
  have hR := hgood R (filter_subset _ _) (fun n hn => (mem_filter.mp hn).2)
  have treal : (W.card : ℝ) ≤ S.card+C.card+F.card+Q.card+H.card+R.card := by exact_mod_cast total
  linarith

end Erdos955.Window

end

section

namespace Erdos955.Window
open Filter Topology

/-- The number of large-prime subsets grows more slowly than the reciprocal of
the precision x^(t^0.99) used to truncate small prime factors. -/
theorem parameter_exponent_positive : (0:ℝ) < 99/100 - (142/100)*Real.log 2 := by
  have hsum := Real.sum_le_exp_of_nonneg (x := 139/200) (by norm_num) 6
  norm_num [Finset.sum_range_succ] at hsum
  have h2 : (2:ℝ) < Real.exp (139/200) := by linarith
  have h := Real.log_lt_log (by norm_num : (0:ℝ)<2) h2
  rw [Real.log_exp] at h
  linarith

/-- First choose the coarse cutoff c, then the finer t. All coefficients are
arbitrary and the x-dependent floors and logarithmic terms may be sent to zero afterwards. -/
theorem window_parameter_selection (Kcoarse Kfine Kgood δ : ℝ) (hδ : 0<δ) :
    ∃ c t : ℝ, 0<c ∧ c<1/10 ∧ 0<t ∧ t<c ∧
      Kcoarse*c + Kfine*t^(1-99/100:ℝ) + Real.exp (1/100-Real.log (1/t)/10000)
      + (Kgood/c^2)*(2:ℝ)^((142/100)*Real.log (1/t))*t^(99/100:ℝ) < δ := by
  have dec (h : ℝ) (pos : 0<h) :
      Tendsto (fun L : ℝ => Real.exp (-L*h)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp ((tendsto_mul_const_atBot_of_pos pos).mpr tendsto_neg_atTop_atBot)
  have de : Tendsto (fun v : ℝ => Real.exp (-v)) atTop (𝓝 0) := by simpa using dec 1 zero_lt_one
  have dc : Tendsto (fun v : ℝ => Kcoarse*Real.exp (-v)) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x:=Kcoarse)).mul de
  obtain ⟨j,hcj,hsize⟩ := ((de.eventually_lt_const (by norm_num : (0:ℝ)<1/10)).and
    (dc.eventually_lt_const (show (0:ℝ)<δ/2 by linarith))).exists
  let c := Real.exp (-j)
  have hc : 0<c := Real.exp_pos _
  have limit : Tendsto (fun L : ℝ =>
      Kcoarse*c + Kfine*Real.exp (-L*(1-99/100)) + Real.exp (1/100)*Real.exp (-L*(1/10000)) +
      (Kgood/c^2)*Real.exp (-L*(99/100-(142/100)*Real.log 2))) atTop (𝓝 (Kcoarse*c)) := by
    simpa using (((tendsto_const_nhds (x:=Kcoarse*c)).add
      ((tendsto_const_nhds (x:=Kfine)).mul (dec (1-99/100) (by norm_num)))).add
      ((tendsto_const_nhds (x:=Real.exp (1/100))).mul (dec (1/10000) (by norm_num)))).add
      ((tendsto_const_nhds (x:=Kgood/c^2)).mul (dec _ parameter_exponent_positive))
  have less : Kcoarse*c < δ := by
    change Kcoarse * Real.exp (-j) < δ
    linarith
  obtain ⟨L,ht,hr⟩ := ((de.eventually_lt_const hc).and (limit.eventually_lt_const less)).exists
  let t := Real.exp (-L)
  refine ⟨c,t,hc,hcj,Real.exp_pos _,ht,?_⟩
  have invlog : Real.log (1/t)=L := by simp [one_div,t]
  have fine (z : ℝ) : t^z = Real.exp (-L*z) := (Real.exp_mul _ _).symm
  have relevant : (2:ℝ)^((142/100)*L) * t^(99/100:ℝ)
      = Real.exp (-L*(99/100-(142/100)*Real.log 2)) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ)<2),fine,←Real.exp_add]
    congr 1
    ring
  rw [invlog,mul_assoc (Kgood/c^2),relevant,fine,
    show 1/100-L/10000 = 1/100+(-L)*(1/10000) by ring,Real.exp_add]
  exact hr

end Erdos955.Window

end

section

namespace Erdos955.Window
open Finset
open scoped BigOperators

/-- Counting multiples of squarefree products gives the exponential moment for the
number of distinct prime factors selected from an arbitrary finite set of primes. -/
theorem prime_factor_moment (x : ℕ) (P : Finset ℕ) (prime : ∀ p∈P, p.Prime)
    (s : ℝ) (hs : 0 ≤ s) :
    ∑ n ∈ Ioc 0 x, (1+s)^(P.filter (fun p => p∣n)).card
      ≤ x * ∏ p∈P, (1+s/p) := by
  classical
  let ω (n : ℕ) := (P.filter (fun p => p∣n)).card
  let g (T : Finset ℕ) := ∏ p∈T, p
  have repr (n : ℕ) (hn : n ∈ Ioc 0 x) : (1+s)^ω n =
      ∑ T ∈ P.powerset, (if g T∣n then s^T.card else 0) := by
    let Q := P.filter (fun p => p∣n)
    have hp (T : Finset ℕ) (hT : T⊆P) : g T∣n ↔ T⊆Q := by
      constructor
      · intro h p hp
        exact mem_filter.mpr ⟨hT hp,(dvd_prod_of_mem (fun i => i) hp).trans h⟩
      · intro h
        have hsub : T⊆n.primeFactors :=
          fun p hp => Nat.mem_primeFactors.mpr ⟨prime _ (hT hp),(mem_filter.mp (h hp)).2,
            (mem_Ioc.mp hn).1.ne'⟩
        exact (prod_dvd_prod_of_subset _ _ _ hsub).trans n.prod_primeFactors_dvd
    have powers : P.powerset.filter (fun T => g T∣n) = Q.powerset := by
      ext T
      simp only [mem_filter,mem_powerset]
      constructor
      · exact fun h => (hp T h.1).mp h.2
      · exact fun h => ⟨h.trans (filter_subset ..),(hp T (h.trans (filter_subset ..))).mpr h⟩
    rw [← sum_filter,powers]
    simpa [Q,ω] using (prod_one_add (f:=fun _ : ℕ => s) Q)
  calc
    _ = ∑ n ∈ Ioc 0 x, ∑ T ∈ P.powerset, if g T∣n then s^T.card else 0 :=
      sum_congr rfl repr
    _ = ∑ T ∈ P.powerset, ∑ n ∈ Ioc 0 x, if g T∣n then s^T.card else 0 := sum_comm
    _ ≤ ∑ T ∈ P.powerset, (x : ℝ) * ∏ p∈T, s/p := by
      apply sum_le_sum
      intro T _
      rw [← sum_filter,sum_const,nsmul_eq_mul,Nat.Ioc_filter_dvd_card_eq_div]
      calc
        _ ≤ ((x:ℝ)/(g T)) * s^T.card :=
          mul_le_mul_of_nonneg_right Nat.cast_div_le (pow_nonneg hs _)
        _ = (x:ℝ) * ∏ p∈T, s/p := by
          rw [prod_div_distrib]; simp only [g,Nat.cast_prod,prod_const]; ring
    _ = _ := by rw [prod_one_add,mul_sum]

/-- An exponential-moment tail estimate with no covariance or floor error. -/
theorem prime_factor_tail (x : ℕ) (P : Finset ℕ) (prime : ∀ p∈P, p.Prime)
    (s L : ℝ) (hs : 0 < s) :
    ((Ioc 0 x).filter (fun n => L ≤ ((P.filter (fun p => p∣n)).card : ℝ))).card
        * (1+s)^L ≤ (x:ℝ) * Real.exp (s * ∑ p∈P, 1/(p:ℝ)) := by
  classical
  let A := (Ioc 0 x).filter (fun n => L ≤ ((P.filter (fun p => p∣n)).card : ℝ))
  let f (n : ℕ) := (1+s)^(P.filter (fun p => p∣n)).card
  calc
    _ = ∑ _n ∈ A, (1+s)^L := by simp [A]
    _ ≤ ∑ n ∈ A, f n := by
      apply sum_le_sum
      intro n hn
      simpa [f] using Real.rpow_le_rpow_of_exponent_le (by linarith : 1≤1+s) (mem_filter.mp hn).2
    _ ≤ ∑ n ∈ Ioc 0 x, f n := sum_le_sum_of_subset_of_nonneg (filter_subset ..)
      (fun n _ _ => pow_nonneg (by linarith) _)
    _ ≤ (x:ℝ) * ∏ p∈P, (1+s/p) := prime_factor_moment x P prime s hs.le
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg x)
      rw [mul_sum,Real.exp_sum]
      apply Finset.prod_le_prod
      · exact fun p _ => by positivity
      · intro p _
        simpa [div_eq_mul_inv,add_comm] using Real.add_one_le_exp (s/(p:ℝ))

end Erdos955.Window

end

section

namespace Erdos955.Window
open Finset

/-- With prime mass at most 1.39 times L plus a constant, numbers having at least
1.42 times L selected prime factors have exponentially small relative size. -/
theorem rare_many_prime_factors (x : ℕ) (P : Finset ℕ) (prime : ∀ p∈P, p.Prime)
    (L K : ℝ) (hL : 0≤L) (mass : ∑ p∈P, 1/(p:ℝ) ≤ (139/100)*L+K) :
    (((Ioc 0 x).filter (fun n => (142/100 : ℝ)*L ≤ ((P.filter (fun p => p∣n)).card : ℝ))).card : ℝ)
      ≤ x * Real.exp (K/100-L/10000) := by
  let s : ℝ := 1/100
  have hs : 0<s := by norm_num [s]
  let A := (Ioc 0 x).filter (fun n => (142/100 : ℝ)*L ≤ ((P.filter (fun p => p∣n)).card : ℝ))
  change (A.card:ℝ) ≤ _
  have factor : (1+s)^((142/100 : ℝ)*L)=Real.exp (Real.log (1+s)*((142/100)*L)) :=
    Real.rpow_def_of_pos (by linarith) _
  have h := prime_factor_tail x P prime s ((142/100)*L) hs
  rw [factor] at h
  change (A.card:ℝ)*_≤_ at h
  have log_bound : (1/101:ℝ) ≤ Real.log (1+s) := by
    have e := Real.log_le_sub_one_of_pos (by positivity : (0:ℝ)<(1+s)⁻¹)
    rw [Real.log_inv] at e
    norm_num [s] at e ⊢
    linarith
  have key : s * ∑ p∈P, 1/(p:ℝ) ≤
      (K/100-L/10000) + Real.log (1+s)*((142/100)*L) := by
    have q := mul_le_mul_of_nonneg_right log_bound (show 0≤(142/100:ℝ)*L by positivity)
    dsimp [s] at *
    linarith
  apply le_of_mul_le_mul_right (a := Real.exp (Real.log (1+s)*((142/100)*L)))
  · calc
      _ ≤ _ := h
      _ ≤ x * Real.exp ((K/100-L/10000) + Real.log (1+s)*((142/100)*L)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr key) (Nat.cast_nonneg x)
      _ = _ := by rw [Real.exp_add]; ring
  · exact Real.exp_pos _

end Erdos955.Window

end

section

namespace Erdos955.Window
open Finset

/-- Apply a reciprocal-prime interval bound to the prime factors of n above x^t.
The limiting parameter L is independent of x. -/
theorem large_factor_tail_of_reciprocal
    (Y0 : ℝ) (bound : ∀ Y Z : ℝ, Y0 ≤ Y → Y ≤ Z → ∀ P : Finset ℕ,
      (∀ p∈P, p.Prime ∧ Y<(p:ℝ) ∧ (p:ℝ)≤Z) →
      ∑ p∈P, 1/(p:ℝ) ≤ (139/100:ℝ) *
        (1/Real.log Z + (Real.log (Real.log Z)-Real.log (Real.log Y))))
    (x : ℕ) (t : ℝ) (hx : 1<(x:ℝ)) (hlog : 2≤Real.log (x:ℝ))
    (ht : 0<t) (ht1 : t≤1) (hY : Y0≤(x:ℝ)^t) (S : Finset ℕ)
    (member : ∀ n∈S, n∈Ioc 0 x ∧ (142/100:ℝ)*Real.log (1/t) ≤
       ((n.primeFactors.filter (fun p : ℕ => (x:ℝ)^t<(p:ℝ))).card : ℝ)) :
    (S.card:ℝ) ≤ x * Real.exp (1/100 - Real.log (1/t)/10000) := by
  classical
  let P := (Ioc 0 x).filter (fun p : ℕ => p.Prime ∧ (x:ℝ)^t<(p:ℝ))
  have prime : ∀ p∈P, p.Prime := fun _ hp => (mem_filter.mp hp).2.1
  have hX := (Real.rpow_le_rpow_of_exponent_le hx.le ht1).trans_eq (Real.rpow_one _)
  have hlogx := Real.log_pos hx
  have raw := bound ((x:ℝ)^t) x hY hX P (by
    intro p hp
    obtain ⟨h,hp,lt⟩ := mem_filter.mp hp
    exact ⟨hp,lt,by exact_mod_cast (mem_Ioc.mp h).2⟩)
  have mass : ∑ p∈P, 1/(p:ℝ) ≤ (139/100)*Real.log (1/t)+1 := by
    rw [Real.log_rpow (zero_lt_one.trans hx), Real.log_mul ht.ne' hlogx.ne'] at raw
    rw [one_div,Real.log_inv]
    have h := (div_le_one hlogx).mpr (show (139/100:ℝ)≤Real.log x by linarith)
    simp only [div_eq_mul_inv,one_mul] at raw h ⊢
    linarith
  have hL : 0≤Real.log (1/t) := Real.log_nonneg ((one_le_div ht).mpr ht1)
  have count := rare_many_prime_factors x P prime (Real.log (1/t)) 1 hL mass
  apply le_trans _ count
  apply Nat.cast_le.mpr
  apply card_le_card
  intro n hn
  obtain ⟨hi,large⟩ := member n hn
  apply mem_filter.mpr
  refine ⟨hi,?_⟩
  have hn0 := (mem_Ioc.mp hi).1.ne'
  have eq : (P.filter (fun p => p∣n))=n.primeFactors.filter (fun p : ℕ => (x:ℝ)^t<(p:ℝ)) := by
    ext p
    simp only [P,mem_filter,mem_Ioc,Nat.mem_primeFactors]
    constructor
    · rintro ⟨⟨_,pr,lp⟩,d⟩
      exact ⟨⟨pr,d,hn0⟩,lp⟩
    · rintro ⟨⟨pr,d,_⟩,lp⟩
      exact ⟨⟨⟨pr.pos,(Nat.le_of_dvd (mem_Ioc.mp hi).1 d).trans (mem_Ioc.mp hi).2⟩,pr,lp⟩,d⟩
  rwa [eq]

end Erdos955.Window

end

section

namespace Erdos955.Window
open Finset Filter Topology
open scoped Classical

/-- Assemble the shrinking-window estimate from the prime reciprocal interval
estimate and the census of retained integers. -/
theorem window_endpoint
    (recip : ∃ Y0 : ℝ, ∀ Y Z : ℝ, Y0 ≤ Y → Y ≤ Z → ∀ P : Finset ℕ,
      (∀ p∈P, p.Prime ∧ Y<(p:ℝ) ∧ (p:ℝ)≤Z) →
      ∑ p∈P, 1/(p:ℝ) ≤ (139/100:ℝ) *
        (1/Real.log Z + (Real.log (Real.log Z)-Real.log (Real.log Y))))
    (count : ∀ c t : ℝ, 0 < c → c < 1/10 → 0 < t → t < c →
      ∀ᶠ x : ℕ in atTop, ∀ h : ℝ, 0 ≤ h → h ≤ 1/20 → ∀ E : Finset ℕ,
        E ⊆ (Icc 1 x).filter (fun n : ℕ => ∃ d ∈ n.divisors,
          (x : ℝ)^(1/2-h) < (d : ℝ) ∧ (d : ℝ) < (x : ℝ)^(1/2+h)) →
        (∀ n ∈ E, retained x c t n) →
        (E.card : ℝ) ≤ (4/c^2)*(2:ℝ)^((142/100)*Real.log (1/t))*x*
          (1/Real.log x+2*h+t^(99/100:ℝ))) :
    OMA.R_Erdos955_erdos_955_variants_pollack_pomerance_thompson_bound_R1_H1_R1.H1 := by
  intro ε hε δ hδ
  obtain ⟨c,t,hc,hc1,ht,htc,hgap⟩ := window_parameter_selection 16 4 4 δ hδ
  obtain ⟨Y0,hprime⟩ := recip
  let η := fun x : ℕ => max (ε x) (1/Real.log (Real.log x))
  let A := 16*c+4*t^(1-99/100:ℝ)+Real.exp (1/100-Real.log (1/t)/10000)
  let B := (4/c^2)*(2:ℝ)^((142/100)*Real.log (1/t))
  let w := t^(99/100:ℝ)
  have tend : Tendsto η atTop (𝓝 0) := clipped_window_tendsto ε hε
  have tend20 : Tendsto (fun x => 20*η x) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := (20:ℝ))).mul tend
  have budget := window_large_x_budget (A:=A) (B:=B) (w:=w) ht hgap _ tend20
  have cast : Tendsto (fun x : ℕ => (x:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have logs := Real.tendsto_log_atTop.comp cast
  filter_upwards [budget, count c t hc hc1 ht htc, (window_power_at_top ht).eventually_ge_atTop Y0,
    eventually_gt_atTop (1 : ℕ), logs.eventually_ge_atTop 2,
    (Real.tendsto_log_atTop.comp logs).eventually_gt_atTop 0,
    tend.eventually_lt_const (show (0:ℝ)<1/200 by norm_num)] with x hbudget hcount hY hx hlog hll hcut
  have hη : 0 ≤ η x := (one_div_nonneg.mpr hll.le).trans (le_max_right ..)
  have hh : 10*η x ≤ 1/20 := by linarith
  let W := (Icc 1 x).filter (fun n : ℕ => ∃ d ∈ n.divisors,
    (x:ℝ)^(1/2-10*η x) < (d:ℝ) ∧ (d:ℝ) < (x:ℝ)^(1/2+10*η x))
  have hW : W ⊆ Icc 1 x := filter_subset _ _
  have big (E : Finset ℕ) (he : ∀ n ∈ E, n ∈ Icc 1 x ∧ (142/100:ℝ)*Real.log (1/t) ≤
          ((n.primeFactors.filter (fun p : ℕ => (x:ℝ)^t < (p:ℝ))).card : ℝ)) :
      (E.card:ℝ) ≤ x*Real.exp (1/100-Real.log (1/t)/10000) := by
    apply large_factor_tail_of_reciprocal Y0 hprime x t (by exact_mod_cast hx) hlog ht (by linarith) hY
    intro n hn
    obtain ⟨hi,hu⟩ := he n hn
    exact ⟨mem_Ioc.mpr (mem_Icc.mp hi),hu⟩
  have retainedBound := hcount (10*η x) (by positivity) hh
  have hfinite := discard_window_exceptions x hx hc.le ht W hW big retainedBound
  have hpower : 4*t/t^(99/100:ℝ) = 4*t^(1-99/100:ℝ) := by
    rw [Real.rpow_sub ht, Real.rpow_one]
    ring
  change (W.card:ℝ) ≤ δ*x
  apply hfinite.trans
  rw [hpower]
  change (x:ℝ)^(9/10:ℝ) + 16*c*x + 4*t^(1-99/100:ℝ)*x + x/(⌊(x:ℝ)^t⌋₊:ℝ) +
    x*Real.exp (1/100-Real.log (1/t)/10000) + B*x*(1/Real.log x+2*(10*η x)+w) ≤ δ*x
  convert hbudget using 1 <;> dsimp only [A] <;> ring

end Erdos955.Window

end

section

namespace Erdos955.PPT
open Finset

/-- Transfer the reciprocal-prime interval estimate to a moving interval of
powers, uniformly in both exponents above the fixed positive threshold `t`. -/
theorem prime_reciprocal_power_window_of_bound (Y0 : ℝ)
    (bound : ∀ Y Z : ℝ, Y0 ≤ Y → Y ≤ Z → ∀ P : Finset ℕ,
      (∀ p ∈ P, p.Prime ∧ Y < (p : ℝ) ∧ (p : ℝ) ≤ Z) →
      ∑ p ∈ P, (1 / (p : ℝ)) ≤ (139 / 100 : ℝ) *
        (1 / Real.log Z + (Real.log (Real.log Z) - Real.log (Real.log Y))))
    {x t a b : ℝ} (hx : 1 < x) (ht : 0 < t) (hta : t ≤ a) (hab : a ≤ b)
    (hy : Y0 ≤ x ^ t) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ x ^ a < (p : ℝ) ∧ (p : ℝ) ≤ x ^ b) :
    ∑ p ∈ P, (1 / (p : ℝ)) ≤ (139 / 100 : ℝ) * (1 / (t * Real.log x) + (b - a) / t) := by
  have hx0 := zero_lt_one.trans hx
  have hl := Real.log_pos hx
  have ha := ht.trans_le hta
  have hb := ha.trans_le hab
  have hbound := bound (x ^ a) (x ^ b) (hy.trans (Real.rpow_le_rpow_of_exponent_le hx.le hta))
    (Real.rpow_le_rpow_of_exponent_le hx.le hab) P hP
  rw [Real.log_rpow hx0 a, Real.log_rpow hx0 b, Real.log_mul ha.ne' hl.ne',
    Real.log_mul hb.ne' hl.ne'] at hbound
  apply hbound.trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  have hinv := one_div_le_one_div_of_le (mul_pos ht hl) (mul_le_mul_of_nonneg_right (hta.trans hab) hl.le)
  have hlog := Real.log_le_sub_one_of_pos (div_pos hb ha)
  rw [Real.log_div hb.ne' ha.ne'] at hlog
  have hratio : b/a - 1 = (b-a)/a := by field_simp
  rw [hratio] at hlog
  have hinc := div_le_div_of_nonneg_left (sub_nonneg.mpr hab) ht hta
  linarith

/-- The prime number bound's asymptotic coefficient `log 4` leaves room below 1.39. -/
theorem log_four_lt_prime_constant : Real.log 4 < (139 / 100 : ℝ) := by
  have hsum := Real.sum_le_exp_of_nonneg (x := 139/200) (by norm_num) 6
  norm_num [Finset.sum_range_succ] at hsum
  have h2 : (2 : ℝ) < Real.exp (139 / 200) := by linarith
  have hlog := Real.log_lt_log (by norm_num : (0:ℝ) < 2) h2
  rw [Real.log_exp] at hlog
  rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]
  norm_num at *
  linarith

end Erdos955.PPT

end

section

namespace Erdos955.PPT
open Finset

/-- Replacing a divisor by any positive factor B does not change the logarithmic
width of its prime strip. The endpoints may be truncated by the lower cutoff. -/
theorem prime_reciprocal_strip_of_bound (Y0 : ℝ)
    (bound : ∀ Y Z : ℝ, Y0 ≤ Y → Y ≤ Z → ∀ P : Finset ℕ,
      (∀ p ∈ P, p.Prime ∧ Y < (p : ℝ) ∧ (p : ℝ) ≤ Z) →
      ∑ p ∈ P, (1 / (p : ℝ)) ≤ (139 / 100 : ℝ) *
        (1 / Real.log Z + (Real.log (Real.log Z) - Real.log (Real.log Y))))
    {x c α β B : ℝ} (hx : 1 < x) (hc : 0 < c) (hB : 0 < B) (hαβ : α ≤ β)
    (hY : Y0 ≤ x ^ c) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ x^c < (p : ℝ) ∧ x^α/B < p ∧ (p : ℝ) ≤ x^β/B) :
    ∑ p ∈ P, (1 / (p : ℝ)) ≤ (139 / 100 : ℝ) / c * (1/Real.log x + (β-α)) := by
  let Y := max (x ^ c) (x^α/B)
  let Z := x^β/B
  have hx0 := zero_lt_one.trans hx
  have hlx := Real.log_pos hx
  have hcL := mul_pos hc hlx
  have hy := (Real.rpow_pos_of_pos hx0 c).trans_le (le_max_left _ _ : x^c ≤ Y)
  have hcl : c*Real.log x ≤ Real.log Y := by
    simpa only [Real.log_rpow hx0] using Real.log_le_log (Real.rpow_pos_of_pos hx0 c) (le_max_left _ _ : x^c ≤ Y)
  obtain hnon | hnil := P.eq_empty_or_nonempty
  · rw [hnon, sum_empty]
    exact mul_nonneg (by positivity) (add_nonneg (by positivity) (sub_nonneg.mpr hαβ))
  obtain ⟨r,hr⟩ := hnil
  have hYZ := (max_lt ((hP r hr).2.1) ((hP r hr).2.2.1)).le.trans (hP r hr).2.2.2
  have hlog := Real.log_le_log hy hYZ
  have hlY := hcL.trans_le hcl
  have hlZ := hlY.trans_le hlog
  have hmass := bound Y Z (hY.trans (le_max_left ..)) hYZ P (by
    intro p hp
    obtain ⟨h1,h2,h3,h4⟩ := hP p hp
    exact ⟨h1,max_lt h2 h3,h4⟩)
  have hlen : Real.log Z - Real.log Y ≤ (β-α)*Real.log x := by
    have ha := Real.log_le_log (div_pos (Real.rpow_pos_of_pos hx0 α) hB) (le_max_right _ _ : x^α/B ≤ Y)
    rw [Real.log_div (Real.rpow_pos_of_pos hx0 α).ne' hB.ne', Real.log_rpow hx0] at ha
    dsimp [Z]
    rw [Real.log_div (Real.rpow_pos_of_pos hx0 β).ne' hB.ne', Real.log_rpow hx0]
    linarith only [ha]
  have hg := Real.log_le_sub_one_of_pos (div_pos hlZ hlY)
  rw [Real.log_div hlZ.ne' hlY.ne'] at hg
  have heq : Real.log Z / Real.log Y - 1 = (Real.log Z - Real.log Y)/Real.log Y := by field_simp
  rw [heq] at hg
  have hloglog : Real.log (Real.log Z) - Real.log (Real.log Y) ≤ (β-α)/c := by
    apply hg.trans
    calc _ ≤ (Real.log Z - Real.log Y)/(c*Real.log x) :=
             div_le_div_of_nonneg_left (sub_nonneg.mpr hlog) hcL hcl
         _ ≤ ((β-α)*Real.log x)/(c*Real.log x) := div_le_div_of_nonneg_right hlen hcL.le
         _ = _ := by field_simp
  have hinv := one_div_le_one_div_of_le hcL (hcl.trans hlog)
  calc _ ≤ _ := hmass
       _ ≤ (139/100 : ℝ) * (1/(c*Real.log x) + (β-α)/c) :=
           mul_le_mul_of_nonneg_left (add_le_add hinv hloglog) (by norm_num)
       _ = _ := by ring

end Erdos955.PPT

end

section

namespace Erdos955.Window
open Finset

noncomputable def largePrimes (m : ℕ) (T : ℝ) : Finset ℕ :=
  m.primeFactors.filter (fun r : ℕ => T < (r : ℝ))

noncomputable def residuals (X K : ℕ) (T : ℝ) : Finset ℕ :=
  (Icc 1 X).filter (fun m => (largePrimes m T).card ≤ K)

noncomputable def stripPrimes (X : ℕ) (C lo hi S : ℝ) (U : Finset ℕ) : Finset ℕ :=
  let B : ℝ := (∏ r ∈ U, r : ℕ)
  (Icc 1 X).filter (fun p : ℕ => p.Prime ∧ C < (p : ℝ) ∧
    lo / (S * B) < (p : ℝ) ∧ (p : ℝ) < hi / B)

noncomputable def quotientPrimes (X m p : ℕ) (C : ℝ) : Finset ℕ :=
  (Icc 1 (X / (m * p))).filter (fun q : ℕ => q.Prime ∧ C < (q : ℝ))

/-- Count each eligible integer by one of its representations; the sum may
count it several times. `K` caps the number of large prime factors. -/
theorem two_prime_census (G : Finset ℕ) (X K : ℕ) (C T E S lo hi : ℝ)
    (good : ∀ n ∈ G, 0 < n ∧ n ≤ X ∧ (largePrimes n T).card ≤ K ∧
      (∀ s : ℕ, s ∣ n → isSmoothAt s C → (s : ℝ) ≤ E) ∧
      (∀ s : ℕ, s ∣ n → isSmoothAt s T → (s : ℝ) ≤ S) ∧
      (∀ p : ℕ, p.Prime → T < (p : ℝ) → ¬p^2 ∣ n) ∧
      ∃ d e : ℕ, n = d * e ∧ E < (d : ℝ) ∧ E < (e : ℝ) ∧ lo < (d : ℝ) ∧ (d : ℝ) < hi) :
    G.card ≤ ∑ m ∈ residuals X K T, ∑ U ∈ (largePrimes m T).powerset,
      ∑ p ∈ stripPrimes X C lo hi S U, (quotientPrimes X m p C).card := by
  classical
  let Q (m p : ℕ) := (quotientPrimes X m p C).image (fun q => m*p*q)
  let P (m : ℕ) (U : Finset ℕ) := (stripPrimes X C lo hi S U).biUnion (Q m)
  let W (m : ℕ) := (largePrimes m T).powerset.biUnion (P m)
  have cover : G ⊆ (residuals X K T).biUnion W := by
    intro n hn
    obtain ⟨hn0,hnX,hK,hcoarse,hfine,hsq,d,e,hde,hd,he,hl,hh⟩ := good n hn
    obtain ⟨m,p,q,s,U,hmn,hm,hp,hCp,hq,hCq,hU,hs,_,hsS,hdU⟩ :=
      two_prime_representation hn0 hde hd he hcoarse hfine hsq
    have hmd : m ∣ n := hmn ▸ dvd_mul_of_dvd_left (dvd_mul_right _ _) _
    have hpd : p ∣ n := hmn ▸ dvd_mul_of_dvd_left (dvd_mul_left _ _) _
    have hmK : (largePrimes m T).card ≤ K :=
      (card_le_card (filter_subset_filter _ (Nat.primeFactors_mono hmd hn0.ne'))).trans hK
    have hmM : m ∈ residuals X K T := mem_filter.mpr ⟨mem_Icc.mpr
      ⟨hm, (Nat.le_of_dvd hn0 hmd).trans hnX⟩, hmK⟩
    have hB0 : 0 < ∏ r ∈ U, r := prod_pos (fun r hr => (Nat.prime_of_mem_primeFactors
      (mem_filter.mp (hU hr)).1).pos)
    let B : ℝ := (∏ r ∈ U, r : ℕ)
    have hB : 0 < B := by dsimp [B]; exact_mod_cast hB0
    have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast hs
    have hS : 0 < S := zero_lt_one.trans_le (hs1.trans hsS)
    have hpr : (0 : ℝ) ≤ p := Nat.cast_nonneg _
    have hdR : (d : ℝ) = p * s * B := by dsimp [B]; exact_mod_cast hdU
    have hwinL : lo / (S*B) < p := by
      apply (div_lt_iff₀ (mul_pos hS hB)).mpr
      rw [hdR] at hl
      calc lo < p * s * B := hl
           _ ≤ p*S*B := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsS hpr) hB.le
           _ = _ := mul_assoc ..
    have hwinR : (p : ℝ) < hi / B := by
      apply (lt_div_iff₀ hB).mpr
      rw [hdR] at hh
      exact (mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hpr hs1) hB.le).trans_lt hh
    have hpP : p ∈ stripPrimes X C lo hi S U := mem_filter.mpr ⟨mem_Icc.mpr
      ⟨hp.pos, (Nat.le_of_dvd hn0 hpd).trans hnX⟩, hp, hCp, hwinL, hwinR⟩
    have hqQ : q ∈ quotientPrimes X m p C := by
      refine mem_filter.mpr ⟨mem_Icc.mpr ⟨hq.pos, (Nat.le_div_iff_mul_le (mul_pos hm hp.pos)).mpr ?_⟩,hq,hCq⟩
      simpa only [Nat.mul_comm q (m*p), ← hmn] using hnX
    exact mem_biUnion.mpr ⟨m,hmM,mem_biUnion.mpr ⟨U,mem_powerset.mpr hU,
      mem_biUnion.mpr ⟨p,hpP,mem_image.mpr ⟨q,hqQ,hmn.symm⟩⟩⟩⟩
  calc G.card ≤ ((residuals X K T).biUnion W).card := card_le_card cover
       _ ≤ ∑ m ∈ residuals X K T, (W m).card := card_biUnion_le
       _ ≤ _ := by
         apply sum_le_sum
         intro m _
         apply card_biUnion_le.trans
         apply sum_le_sum
         intro U _
         apply card_biUnion_le.trans
         exact sum_le_sum (fun p _ => card_image_le)

end Erdos955.Window

end

section

namespace Erdos955.Window

/-- In the central divisor window, both complementary factors exceed the
coarse cutoff. The exponent bound on `h` only enters in those comparisons. -/
theorem window_factor_pair {x h : ℝ} {n d : ℕ} (hx : 1 < x) (hh : h ≤ 1/20)
    (hn : x ^ (9/10 : ℝ) < (n : ℝ)) (hd : d ∣ n)
    (hlo : x ^ (1/2 - h) < (d : ℝ)) (hhi : (d : ℝ) < x ^ (1/2 + h)) :
    ∃ e : ℕ, n = d*e ∧ x ^ (1/4 : ℝ) < (d : ℝ) ∧ x ^ (1/4 : ℝ) < (e : ℝ) := by
  obtain ⟨e,rfl⟩ := hd
  have hx0 := zero_lt_one.trans hx
  refine ⟨e,rfl,(Real.rpow_le_rpow_of_exponent_le hx.le (by linarith)).trans_lt hlo,?_⟩
  by_contra! he
  have hp := mul_le_mul hhi.le he (Nat.cast_nonneg e) (Real.rpow_pos_of_pos hx0 _).le
  rw [← Real.rpow_add hx0] at hp
  have comp : x ^ ((1/2+h)+(1/4 : ℝ)) ≤ x ^ (9/10 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hx.le (by linarith)
  exact (not_lt_of_ge (hp.trans comp)) (by simpa only [Nat.cast_mul] using hn)

/-- Moving the smooth part into the exponent yields the multiplicative strip
for `p * B`, in the quotient form used to count the prime witnesses. -/
theorem strip_from_quotients {x h u p B : ℝ} (hx : 0 < x) (hB : 0 < B)
    (lo : x ^ (1/2-h) / (x^u * B) < p) (hi : p < x ^ (1/2+h) / B) :
    x ^ (1/2-h-u) < p*B ∧ p*B < x ^ (1/2+h) := by
  have eq : x ^ (1/2-h-u) / B = x ^ (1/2-h)/(x^u*B) := by
    rw [Real.rpow_sub hx, div_div]
  exact ⟨(div_lt_iff₀ hB).mp (eq ▸ lo), (lt_div_iff₀ hB).mp hi⟩

/-- A smooth factor at most `x^u` widens the divisor window by `u` on the
lower side. In the application `u = t^(99/100 : ℝ)`. -/
theorem strip_of_representation {x h u : ℝ} {d p s B : ℕ} (hx : 0 < x)
    (hlo : x ^ (1/2-h) < (d : ℝ)) (hhi : (d : ℝ) < x ^ (1/2+h))
    (rep : d = p*s*B) (hs : 0 < s) (hsmax : (s : ℝ) ≤ x^u) :
    x ^ (1/2-h-u) < (p : ℝ)*B ∧ (p : ℝ)*B < x ^ (1/2+h) := by
  have eq : (d : ℝ) = (p : ℝ)*B*s := by rw [rep]; push_cast; ring
  have hs1 : 1 ≤ (s : ℝ) := by exact_mod_cast hs
  have hpB : 0 ≤ (p : ℝ)*B := mul_nonneg (Nat.cast_nonneg p) (Nat.cast_nonneg B)
  constructor
  · by_contra! low
    have bound := mul_le_mul low hsmax (Nat.cast_nonneg s) (Real.rpow_pos_of_pos hx _).le
    rw [← eq, ← Real.rpow_add hx, sub_add_cancel] at bound
    exact hlo.not_ge bound
  · rw [eq] at hhi
    exact (le_mul_of_one_le_right hpB hs1).trans_lt hhi

/-- For a positive half-width, the central window strictly straddles `√x`. -/
theorem sqrt_in_window {x h : ℝ} (hx : 1 < x) (hh : 0 < h) :
    x ^ (1/2-h) < Real.sqrt x ∧ Real.sqrt x < x ^ (1/2+h) := by
  rw [Real.sqrt_eq_rpow]
  exact ⟨Real.rpow_lt_rpow_of_exponent_lt hx (by linarith),
    Real.rpow_lt_rpow_of_exponent_lt hx (by linarith)⟩

end Erdos955.Window

end

section

namespace Erdos955.Window
open Finset

/-- Apply reciprocal-prime interval counting directly to the census strip. -/
theorem census_strip_estimate (Y0 : ℝ)
    (bound : ∀ Y Z : ℝ, Y0 ≤ Y → Y ≤ Z → ∀ P : Finset ℕ,
      (∀ p ∈ P, p.Prime ∧ Y < (p : ℝ) ∧ (p : ℝ) ≤ Z) →
      ∑ p ∈ P, 1 / (p : ℝ) ≤ (139/100 : ℝ) *
        (1/Real.log Z + (Real.log (Real.log Z)-Real.log (Real.log Y))))
    {X m : ℕ} {c h u T : ℝ} (hx : 1 < (X:ℝ)) (hc : 0 < c)
    (hh : 0 ≤ h) (hu : 0 ≤ u) (hy : Y0 ≤ (X:ℝ)^c)
    (U : Finset ℕ) (hU : U ⊆ largePrimes m T) :
    (∑ p ∈ stripPrimes X ((X:ℝ)^c) ((X:ℝ)^(1/2-h)) ((X:ℝ)^(1/2+h)) ((X:ℝ)^u) U,
      1/(p:ℝ)) ≤ (139/100:ℝ)/c * (1/Real.log X+2*h+u) := by
  let B : ℝ := (∏ r ∈ U, r : ℕ)
  have pos : 0 < ∏ r ∈ U, r := prod_pos (fun r hr =>
    (Nat.prime_of_mem_primeFactors (mem_filter.mp (hU hr)).1).pos)
  have bpos : 0 < B := Nat.cast_pos.mpr pos
  let P := stripPrimes X ((X:ℝ)^c) ((X:ℝ)^(1/2-h)) ((X:ℝ)^(1/2+h)) ((X:ℝ)^u) U
  have admissible (p : ℕ) (hp : p ∈ P) :
      p.Prime ∧ (X:ℝ)^c < (p:ℝ) ∧ (X:ℝ)^(1/2-h-u)/B < p ∧ (p:ℝ) ≤ (X:ℝ)^(1/2+h)/B := by
    obtain ⟨prime,cut,lo,hi⟩ := (mem_filter.mp hp).2
    have h := strip_from_quotients (zero_lt_one.trans hx) bpos lo hi
    exact ⟨prime,cut,(div_lt_iff₀ bpos).mpr h.1,hi.le⟩
  have est := Erdos955.PPT.prime_reciprocal_strip_of_bound Y0 bound hx hc bpos
    (show (1/2-h-u:ℝ) ≤ 1/2+h by linarith) hy P admissible
  calc _ ≤ _ := est
       _ = _ := by ring

/-- Interpret the integer quotient defining the second prime range in the
real prime-counting estimate. -/
theorem census_quotient_estimate (Y0 : ℝ)
    (bound : ∀ {x c T : ℝ}, 1<x → 0<c → 0≤T → Y0 ≤ x^c → ∀ P : Finset ℕ,
      (∀ p ∈ P, p.Prime ∧ x^c < (p:ℝ) ∧ (p:ℝ) ≤ T) →
        (P.card:ℝ) ≤ (139/100:ℝ)*T/(c*Real.log x))
    {X m p : ℕ} {c : ℝ} (hx : 1 < (X:ℝ)) (hc : 0 < c) (hy : Y0 ≤ (X:ℝ)^c)
    (hm : 0 < m) (hp : 0 < p) :
    ((quotientPrimes X m p ((X:ℝ)^c)).card : ℝ) ≤
      (139/100:ℝ)/c*X/Real.log X*(1/(m:ℝ))*(1/(p:ℝ)) := by
  let Q := quotientPrimes X m p ((X:ℝ)^c)
  have hmp : 0 < (m:ℝ)*p := mul_pos (Nat.cast_pos.mpr hm) (Nat.cast_pos.mpr hp)
  have inc (q : ℕ) (hq : q ∈ Q) : q.Prime ∧ (X:ℝ)^c < (q:ℝ) ∧ (q:ℝ) ≤ X/((m:ℝ)*p) := by
    obtain ⟨range,prime,cut⟩ := mem_filter.mp hq
    refine ⟨prime,cut,(le_div_iff₀ hmp).mpr ?_⟩
    exact_mod_cast (Nat.le_div_iff_mul_le (Nat.mul_pos hm hp)).mp (mem_Icc.mp range).2
  have est := bound hx hc (div_nonneg (Nat.cast_nonneg X) hmp.le) hy Q inc
  calc _ ≤ _ := est
       _ = _ := by simp only [div_eq_mul_inv,mul_inv_rev]; ring

end Erdos955.Window

end

section

namespace Erdos955.Window
open Finset

private theorem CensusSum_harmonic_increment {x : ℝ} (hx : 0 < x) :
    1/(x+1) ≤ Real.log (x+1) - Real.log x := by
  have h := Real.one_sub_inv_le_log_of_pos (div_pos (show 0 < x+1 by linarith) hx)
  rw [Real.log_div (by linarith) hx.ne'] at h
  convert h using 1
  field_simp
  ring

/-- The elementary logarithmic upper bound for the positive harmonic sum. -/
theorem harmonic_Icc_le (X : ℕ) : ∑ m ∈ Icc 1 X, 1/(m:ℝ) ≤ 1 + Real.log X := by
  induction X with
  | zero => simp
  | succ X ih =>
    by_cases hX : X = 0
    · subst X; norm_num
    have hx : (0:ℝ) < X := by exact_mod_cast Nat.pos_of_ne_zero hX
    rw [sum_Icc_succ_top (by omega : 1 ≤ X+1), Nat.cast_succ]
    linarith [CensusSum_harmonic_increment hx]

/-- Sum the two prime estimates over the squarefree support and over the
residual integer. The factor 4 is larger than twice the squared prime constant. -/
theorem census_sum_of_prime_bounds (X K : ℕ) (T : ℝ) (P : Finset ℕ → Finset ℕ)
    (Q : ℕ → ℕ → ℕ) {c W : ℝ} (hlog : 1 ≤ Real.log X) (hc : 0 < c) (hW : 0 ≤ W)
    (hP : ∀ m ∈ residuals X K T, ∀ U ∈ (largePrimes m T).powerset,
      ∑ p ∈ P U, 1/(p:ℝ) ≤ (139/100:ℝ)/c * W)
    (hQ : ∀ m ∈ residuals X K T, ∀ U ∈ (largePrimes m T).powerset, ∀ p ∈ P U,
      (Q m p : ℝ) ≤ (139/100:ℝ)/c * X / Real.log X * (1/(m:ℝ)) * (1/(p:ℝ))) :
    ((∑ m ∈ residuals X K T, ∑ U ∈ (largePrimes m T).powerset, ∑ p ∈ P U, Q m p : ℕ) : ℝ)
      ≤ (4/c^2) * (2:ℝ)^K * X * W := by
  classical
  let D := (139/100:ℝ)/c
  let F := D * X / Real.log X
  let H := F * (D*W) * (2:ℝ)^K
  have hl : 0 < Real.log X := zero_lt_one.trans_le hlog
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hmU (m : ℕ) (hm : m ∈ residuals X K T) (U : Finset ℕ) (hU : U ∈ (largePrimes m T).powerset) :
      ∑ p ∈ P U, (Q m p : ℝ) ≤ F*(1/m)*(D*W) := by
    calc ∑ p ∈ P U, (Q m p : ℝ) ≤ ∑ p ∈ P U, F*(1/m)*(1/p) := sum_le_sum (hQ m hm U hU)
         _ = _ := (mul_sum ..).symm
         _ ≤ _ := mul_le_mul_of_nonneg_left (hP m hm U hU) (by positivity)
  have hm (m : ℕ) (hm : m ∈ residuals X K T) :
      ∑ U ∈ (largePrimes m T).powerset, ∑ p ∈ P U, (Q m p : ℝ) ≤ H * (1/m) := by
    have hK := (mem_filter.mp hm).2
    have hpow : (2:ℝ)^(largePrimes m T).card ≤ (2:ℝ)^K := pow_le_pow_right₀ (by norm_num) hK
    calc ∑ U ∈ (largePrimes m T).powerset, ∑ p ∈ P U, (Q m p : ℝ) ≤
           ∑ _U ∈ (largePrimes m T).powerset, F*(1/m)*(D*W) := sum_le_sum (hmU m hm)
         _ = (2:ℝ)^(largePrimes m T).card * (F*(1/m)*(D*W)) := by simp
         _ ≤ (2:ℝ)^K * (F*(1/m)*(D*W)) := mul_le_mul_of_nonneg_right hpow (by positivity)
         _ = _ := by dsimp [H]; ring
  have hsum : ∑ m ∈ residuals X K T, 1/(m:ℝ) ≤ 2 * Real.log X := by
    calc ∑ m ∈ residuals X K T, 1/(m:ℝ) ≤ ∑ m ∈ Icc 1 X, 1/(m:ℝ) :=
           sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by positivity)
         _ ≤ _ := (harmonic_Icc_le X).trans (by linarith)
  simp only [Nat.cast_sum]
  calc ∑ m ∈ residuals X K T, ∑ U ∈ (largePrimes m T).powerset, ∑ p ∈ P U, (Q m p : ℝ) ≤
          ∑ m ∈ residuals X K T, H*(1/m) := sum_le_sum hm
       _ = _ := (mul_sum ..).symm
       _ ≤ H*(2*Real.log X) := mul_le_mul_of_nonneg_left hsum hH
       _ = (2*(139/100:ℝ)^2)/c^2 * (2:ℝ)^K * X * W := by
         dsimp [H,F,D]
         field_simp
       _ ≤ _ := by gcongr <;> norm_num

end Erdos955.Window

end

section

namespace Erdos955.Window
open Finset
open scoped Classical

/-- Count a retained subset of the near-square-root window by the residual
integer, its set of large primes, and the two selected prime factors. -/
theorem retained_census {x : ℕ} {h c t : ℝ} (hx : 1 < x) (hh : h ≤ 1/20)
    (E : Finset ℕ) (window : E ⊆ (Icc 1 x).filter (fun n : ℕ =>
      ∃ d ∈ n.divisors, (x : ℝ)^(1/2-h) < (d : ℝ) ∧ (d : ℝ) < (x : ℝ)^(1/2+h)))
    (good : ∀ n ∈ E, retained x c t n) :
    E.card ≤ ∑ m ∈ residuals x ⌊(142/100:ℝ)*Real.log (1/t)⌋₊ ((x:ℝ)^t),
      ∑ U ∈ (largePrimes m ((x:ℝ)^t)).powerset,
        ∑ p ∈ stripPrimes x ((x:ℝ)^c) ((x:ℝ)^(1/2-h)) ((x:ℝ)^(1/2+h))
          ((x:ℝ)^(t^(99/100:ℝ))) U, (quotientPrimes x m p ((x:ℝ)^c)).card := by
  apply two_prime_census (E := (x:ℝ)^(1/4:ℝ))
  intro n hn
  obtain ⟨hnum,d,hd,lo,hi⟩ := mem_filter.mp (window hn)
  obtain ⟨pos,cap⟩ := mem_Icc.mp hnum
  obtain ⟨big,coarse,fine,square,count⟩ := good n hn
  obtain ⟨e,prod,db,eb⟩ := window_factor_pair (by exact_mod_cast hx) hh big
    (Nat.dvd_of_mem_divisors hd) lo hi
  exact ⟨pos,cap,Nat.le_floor count.le,coarse,fine,square,d,e,prod,db,eb,lo,hi⟩

end Erdos955.Window

end

section

namespace Erdos955.PPT
open Filter Finset

/-- Sum of prime logarithms bounded by the elementary primorial inequality. -/
theorem prime_log_mass (N : ℕ) :
    ∑ p ∈ Nat.primesLE N, Real.log p ≤ N * Real.log 4 := by
  have hprod : (∏ p ∈ Nat.primesLE N, (p : ℝ)) = (primorial N : ℝ) := by
    simp [primorial_eq_prod_primesLE]
  have hn : (0 : ℝ) < primorial N := by exact_mod_cast primorial_pos N
  have hlog := Real.log_le_log hn (show (primorial N : ℝ) ≤ (4:ℝ)^N by exact_mod_cast primorial_le_four_pow N)
  rw [← hprod, Real.log_prod (fun p hp => by exact_mod_cast (Nat.prime_of_mem_primesLE hp).ne_zero), Real.log_pow] at hlog
  exact hlog

/-- Split prime counting into primes below x^u and the rest, whose logs each cost u log x. -/
theorem prime_count_log_split {x u : ℝ} (hx : 1 < x) (hu : 0 < u) :
    (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ x ^ u + (x * Real.log 4)/(u*Real.log x) := by
  classical
  let S := Nat.primesLE ⌊x⌋₊
  let small := S.filter (fun p : ℕ => (p:ℝ) ≤ x^u)
  let large := S \ small
  have hx0 := zero_lt_one.trans hx
  have hl := mul_pos hu (Real.log_pos hx)
  have hsmall : (small.card : ℝ) ≤ x^u := by
    have hsub : small ⊆ Icc 1 ⌊x^u⌋₊ := by
      intro p hp
      obtain ⟨hs,hsz⟩ := mem_filter.mp hp
      exact mem_Icc.mpr ⟨(Nat.prime_of_mem_primesLE hs).one_le,Nat.le_floor hsz⟩
    have hcard := card_le_card hsub
    rw [Nat.card_Icc] at hcard
    have hnat : small.card ≤ ⌊x^u⌋₊ := by omega
    exact (Nat.cast_le.mpr hnat).trans (Nat.floor_le (Real.rpow_nonneg hx0.le _))
  have hlarge : (large.card : ℝ) * (u * Real.log x) ≤ x*Real.log 4 := by
    calc _ = ∑ _p ∈ large, (u*Real.log x) := by simp
         _ ≤ ∑ p ∈ large, Real.log p := by
           apply sum_le_sum
           intro p hp
           obtain ⟨hS,hsmall⟩ := mem_sdiff.mp hp
           have hbound : x^u < (p:ℝ) := lt_of_not_ge (fun h => hsmall (mem_filter.mpr ⟨hS,h⟩))
           simpa only [Real.log_rpow hx0] using Real.log_le_log (Real.rpow_pos_of_pos hx0 _) hbound.le
         _ ≤ ∑ p ∈ S, Real.log p := sum_le_sum_of_subset_of_nonneg sdiff_subset (fun p hp _ =>
           Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_le))
         _ ≤ ⌊x⌋₊ * Real.log 4 := prime_log_mass _
         _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.floor_le hx0.le) (Real.log_nonneg (by norm_num))
  have hlarge' := (le_div_iff₀ hl).mpr hlarge
  have hnat : large.card + small.card = Nat.primeCounting ⌊x⌋₊ :=
    (card_sdiff_add_card_eq_card (filter_subset ..)).trans (Nat.primesLE_card_eq_primeCounting _)
  have hsz : (large.card:ℝ) + small.card = Nat.primeCounting ⌊x⌋₊ := by exact_mod_cast hnat
  linarith only [hsz,hsmall,hlarge']

/-- A fixed power below one is negligible on the x/log x scale. The elementary
quadratic lower bound for exp suffices. -/
theorem eventually_small_power {u d : ℝ} (hu : u < 1) (hd : 0 < d) :
    ∀ᶠ x : ℝ in atTop, x ^ u ≤ d*x/Real.log x := by
  let v := 1-u
  have hv : 0 < v := sub_pos.mpr hu
  have hcoef : 0 < d*v^2 := by positivity
  filter_upwards [eventually_gt_atTop 1,
    Real.tendsto_log_atTop.eventually_ge_atTop (2/(d*v^2))] with x hx hbig
  have hx0 := zero_lt_one.trans hx
  have ht := Real.log_pos hx
  have h2 := (div_le_iff₀ hcoef).mp hbig
  have hqt : Real.log x ≤ d * (v * Real.log x)^2 / 2 := by
    nlinarith only [mul_le_mul_of_nonneg_right h2 ht.le]
  have hseries := Real.pow_div_factorial_le_exp (x := v * Real.log x) (mul_pos hv ht).le 2
  norm_num at hseries
  have hlog : Real.log x ≤ d * x ^ v := by
    rw [Real.rpow_def_of_pos hx0, mul_comm (Real.log x) v]
    calc _ ≤ d * ((v*Real.log x)^2/2) := by linarith only [hqt]
         _ ≤ _ := mul_le_mul_of_nonneg_left hseries hd.le
  apply (le_div_iff₀ ht).mpr
  calc x^u * Real.log x ≤ x^u * (d*x^v) := mul_le_mul_of_nonneg_left hlog (Real.rpow_nonneg hx0.le _)
       _ = d * (x^u * x^v) := by ring
       _ = _ := by rw [← Real.rpow_add hx0, show u + v = 1 by dsimp [v]; ring, Real.rpow_one]

/-- The exact Chebyshev upper bound, derived directly from the pinned primorial inequality. -/
theorem eventual_prime_count_from_primorial {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ (Real.log 4 + ε) * x / Real.log x := by
  have h4 := Real.log_pos (by norm_num : (1:ℝ) < 4)
  have hD : 0 < Real.log 4 + ε/2 := by linarith
  let u := Real.log 4 / (Real.log 4 + ε/2)
  have hu : 0 < u := div_pos h4 hD
  have hu1 : u < 1 := (div_lt_one hD).mpr (by linarith)
  have hid : u * (Real.log 4 + ε/2) = Real.log 4 := div_mul_cancel₀ _ hD.ne'
  filter_upwards [eventually_gt_atTop 1, eventually_small_power hu1 (show 0 < ε/2 by linarith)] with x hx hsmall
  have hlog := Real.log_pos hx
  calc _ ≤ x ^ u + (x * Real.log 4)/(u*Real.log x) := prime_count_log_split hx hu
       _ ≤ (ε/2)*x/Real.log x + (x * Real.log 4)/(u*Real.log x) := add_le_add_left hsmall _
       _ = _ := by field_simp; nlinarith only [hid]

end Erdos955.PPT

end

section

namespace Erdos955.PPT
open Filter Finset

/-- Chebyshev's asymptotic estimate at a fixed large threshold, also bounding
arbitrary subsets of primes with endpoints above a smaller power. -/
theorem eventual_prime_count_range_of_Chebyshev
    (cheb : ∀ {ε : ℝ}, 0 < ε → ∀ᶠ x : ℝ in atTop,
      (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ (Real.log 4 + ε) * x / Real.log x) :
    ∃ Y0 : ℝ, ∀ {x c T : ℝ}, 1 < x → 0 < c → 0 ≤ T → Y0 ≤ x^c →
      ∀ P : Finset ℕ, (∀ p∈P, p.Prime ∧ x^c < (p:ℝ) ∧ (p:ℝ) ≤ T) →
        (P.card : ℝ) ≤ (139/100 : ℝ) * T / (c * Real.log x) := by
  obtain ⟨Y0,hY0⟩ := Filter.eventually_atTop.mp (cheb (sub_pos.mpr log_four_lt_prime_constant))
  refine ⟨Y0, ?_⟩
  intro x c T hx hc hT hY P hP
  have hl := mul_pos hc (Real.log_pos hx)
  obtain rfl | hn := P.eq_empty_or_nonempty
  · simpa using div_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 139/100) hT) hl.le
  obtain ⟨p,hp⟩ := hn
  have hTlow := (hP p hp).2.1.le.trans (hP p hp).2.2
  have hs : P ⊆ Nat.primesLE ⌊T⌋₊ := by
    intro q hq
    exact Nat.mem_primesLE.mpr ⟨Nat.le_floor (hP q hq).2.2,(hP q hq).1⟩
  have hcard := card_le_card hs
  rw [Nat.primesLE_card_eq_primeCounting] at hcard
  have hπ := hY0 T (hY.trans hTlow)
  rw [show Real.log 4 + (139/100 - Real.log 4) = 139/100 by ring] at hπ
  have hlog := Real.log_le_log (Real.rpow_pos_of_pos (zero_lt_one.trans hx) c) hTlow
  rw [Real.log_rpow (zero_lt_one.trans hx)] at hlog
  exact ((Nat.cast_le.mpr hcard).trans hπ).trans (div_le_div_of_nonneg_left (by positivity) hl hlog)

end Erdos955.PPT

end

section

namespace Erdos955.PPT
open Finset

/-- The logarithmic increment pays for moving one partial-summation endpoint.
This finite-difference inequality replaces integration of the prime counting function. -/
theorem loglog_increment {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hlog : 2 ≤ Real.log a) :
    a / Real.log a * (1/a - 1/b) ≤ Real.log (Real.log b) - Real.log (Real.log a) := by
  have hb := ha.trans_le hab
  have hla : 0 < Real.log a := by linarith
  have hlt := Real.log_le_log ha hab
  have hlb := hla.trans_le hlt
  let d := Real.log b - Real.log a
  let w := 1 - a/b
  have hd : 0 ≤ d := sub_nonneg.mpr hlt
  have hw : 0 ≤ w := sub_nonneg.mpr ((div_le_one hb).mpr hab)
  have hrat : 0 ≤ b/a - 1 := sub_nonneg.mpr ((one_le_div ha).mpr hab)
  have hP := Real.le_log_one_add_of_nonneg hrat
  rw [show 1 + (b/a - 1) = b/a by ring, Real.log_div hb.ne' ha.ne'] at hP
  have hP2 : 2 * (b-a) ≤ d * (b+a) := by
    have hident : 2 * (b/a-1) / (b/a-1+2) = 2 * (b-a) / (b+a) := by
      apply (div_eq_div_iff (by linarith) (by positivity)).mpr
      field_simp
      ring
    rw [hident] at hP
    exact (div_le_iff₀ (by positivity)).mp hP
  have hP3 : 2*w ≤ d * (2-w) := by
    apply (mul_le_mul_iff_of_pos_right hb).mp
    have hwid : w * b = b-a := by dsimp [w]; field_simp
    nlinarith only [hP2, hwid, congrArg (fun z : ℝ => d*z) hwid]
  have hdw : 0 ≤ d-w := by nlinarith [mul_nonneg hd hw]
  have hle : w / Real.log a ≤ d / Real.log b := by
    apply (div_le_div_iff₀ hla hlb).mpr
    have hdiff : Real.log b = Real.log a + d := by dsimp [d]; ring
    rw [hdiff]
    nlinarith [mul_nonneg (sub_nonneg.mpr hlog) hdw]
  have hfinal := Real.one_sub_inv_le_log_of_pos (div_pos hlb hla)
  rw [Real.log_div hlb.ne' hla.ne'] at hfinal
  calc a / Real.log a * (1/a - 1/b) = w / Real.log a := by dsimp [w]; field_simp
       _ ≤ d / Real.log b := hle
       _ = 1 - (Real.log b / Real.log a)⁻¹ := by dsimp [d]; field_simp
       _ ≤ _ := hfinal

/-- Finite partial summation. The counting bound is needed only at right endpoints
of finite subsets under consideration. -/
theorem reciprocal_sum_of_count {Y A : ℝ} (hY : 0 < Y) (hlY : 2 ≤ Real.log Y)
    (hA : 0 ≤ A) (Q : ℕ → Prop)
    (hcount : ∀ T : ℝ, Y ≤ T → ∀ P : Finset ℕ,
      (∀ p ∈ P, Q p ∧ Y < (p : ℝ) ∧ (p : ℝ) ≤ T) → (P.card : ℝ) ≤ A*T/Real.log T)
    (P : Finset ℕ) (Z : ℝ) (hYZ : Y ≤ Z)
    (hP : ∀ p ∈ P, Q p ∧ Y < (p : ℝ) ∧ (p : ℝ) ≤ Z) :
    ∑ p ∈ P, 1 / (p : ℝ) ≤ A*(1/Real.log Z + (Real.log (Real.log Z) - Real.log (Real.log Y))) := by
  classical
  have stronger (S : Finset ℕ) : ∀ z : ℝ, Y ≤ z →
      (∀ p ∈ S, Q p ∧ Y < (p : ℝ) ∧ (p : ℝ) ≤ z) →
      ∑ p ∈ S, 1/(p : ℝ) ≤ S.card / z + A*(Real.log (Real.log z)-Real.log (Real.log Y)) := by
    induction S using Finset.induction_on_max with
    | empty =>
      intro z hz _
      have hl : Real.log (Real.log Y) ≤ Real.log (Real.log z) :=
        Real.log_le_log (by linarith) (Real.log_le_log hY hz)
      simp only [sum_empty, card_empty, Nat.cast_zero, zero_div, zero_add]
      exact mul_nonneg hA (sub_nonneg.mpr hl)
    | insert r S hmax ih =>
      intro z hz hS
      have hr := hS r (mem_insert_self ..)
      have hr0 := hY.trans hr.2.1
      have hrz := hr.2.2
      have hz0 := hr0.trans_le hrz
      have hS' : ∀ p ∈ S, Q p ∧ Y < (p : ℝ) ∧ (p : ℝ) ≤ r := by
        intro p hp
        have h := hS p (mem_insert_of_mem hp)
        exact ⟨h.1, h.2.1, by exact_mod_cast (hmax p hp).le⟩
      have hnot : r ∉ S := fun h => (hmax _ h).false
      have hbefore := ih r hr.2.1.le hS'
      have hcard := hcount r hr.2.1.le (insert r S) (by
        intro p hp
        rcases mem_insert.mp hp with rfl | hp
        · exact ⟨hr.1,hr.2.1,le_rfl⟩
        · exact hS' p hp)
      let m : ℝ := (insert r S).card
      have hpartial : ∑ p ∈ insert r S, 1/(p : ℝ) ≤ m / r + A*(Real.log (Real.log r)-Real.log (Real.log Y)) := by
        rw [sum_insert hnot]
        dsimp [m]
        rw [card_insert_of_notMem hnot, Nat.cast_add_one, add_div]
        linarith only [hbefore]
      have hweight : 0 ≤ 1/(r : ℝ) - 1/z := sub_nonneg.mpr (one_div_le_one_div_of_le hr0 hrz)
      have hincr := loglog_increment hr0 hrz (hlY.trans (Real.log_le_log hY hr.2.1.le))
      have hpartial' : m * (1/(r : ℝ) - 1/z) ≤ A*(Real.log (Real.log z)-Real.log (Real.log r)) :=
        calc _ ≤ (A*r/Real.log r) * (1/(r : ℝ)-1/z) := mul_le_mul_of_nonneg_right hcard hweight
             _ = A*((r/Real.log r)*(1/(r : ℝ)-1/z)) := by ring
             _ ≤ _ := mul_le_mul_of_nonneg_left hincr hA
      change _ ≤ m/z + _
      simp only [div_eq_mul_inv, one_mul] at hpartial hpartial' ⊢
      linarith only [hpartial, hpartial']
  have hmain := stronger P Z hYZ hP
  have hC := hcount Z hYZ P hP
  have hz := hY.trans_le hYZ
  have hCZ : (P.card : ℝ)/Z ≤ A / Real.log Z := by
    apply (div_le_iff₀ hz).mpr
    exact hC.trans_eq (by ring)
  simp only [div_eq_mul_inv, one_mul] at hmain hCZ ⊢
  linarith only [hmain, hCZ]

end Erdos955.PPT

end

section

namespace Erdos955.PPT
open Filter Finset

/-- A reciprocal-prime interval bound with a uniform constant strictly below 1.4. -/
theorem prime_reciprocal_interval_from_Chebyshev
    (cheb : ∀ {ε : ℝ}, 0 < ε → ∀ᶠ x : ℝ in atTop, (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ (Real.log 4 + ε) * x / Real.log x) : ∃ Y0 : ℝ, ∀ Y Z : ℝ, Y0 ≤ Y → Y ≤ Z → ∀ P : Finset ℕ,
    (∀ p ∈ P, p.Prime ∧ Y < (p : ℝ) ∧ (p : ℝ) ≤ Z) →
    ∑ p ∈ P, 1 / (p : ℝ) ≤ (139 / 100 : ℝ) *
      (1 / Real.log Z + (Real.log (Real.log Z) - Real.log (Real.log Y))) := by
  have hπ := cheb
    (sub_pos.mpr log_four_lt_prime_constant)
  rw [Filter.eventually_atTop] at hπ
  obtain ⟨B, hB⟩ := hπ
  refine ⟨max B (Real.exp 2), ?_⟩
  intro Y Z hY hYZ P hP
  have he := (le_max_right B (Real.exp 2)).trans hY
  have hy := (Real.exp_pos 2).trans_le he
  have hl : 2 ≤ Real.log Y := (Real.le_log_iff_exp_le hy).mpr he
  apply reciprocal_sum_of_count hy hl (by norm_num : (0 : ℝ) ≤ 139/100) Nat.Prime _ P Z hYZ hP
  intro T ht S hS
  have hsub : S ⊆ Nat.primesLE ⌊T⌋₊ := by
    intro p hp
    exact Nat.mem_primesLE.mpr ⟨Nat.le_floor (hS p hp).2.2, (hS p hp).1⟩
  have hsize := Finset.card_le_card hsub
  rw [Nat.primesLE_card_eq_primeCounting] at hsize
  have hCT := hB T (((le_max_left ..).trans hY).trans ht)
  rw [show Real.log 4 + (139 / 100 - Real.log 4) = 139 / 100 by ring] at hCT
  exact (Nat.cast_le.mpr hsize).trans hCT

end Erdos955.PPT

end

section

namespace Erdos955.Window
open Finset Filter

/-- The retained near-square-root divisor window, with every prime counting
and harmonic loss included in the constant `4`. -/
theorem eventually_retained_estimate_of_Chebyshev
    (cheb : ∀ {ε : ℝ}, 0 < ε → ∀ᶠ x : ℝ in atTop,
      (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ (Real.log 4 + ε) * x / Real.log x)
    {c t : ℝ} (hc : 0 < c) (ht : 0 < t) (ht1 : t ≤ 1) :
    ∀ᶠ X : ℕ in atTop, ∀ h : ℝ, 0 ≤ h → h ≤ 1/20 → ∀ E : Finset ℕ,
      E ⊆ (Icc 1 X).filter (fun n : ℕ => ∃ d ∈ n.divisors,
        (X : ℝ)^(1/2-h) < (d : ℝ) ∧ (d : ℝ) < (X : ℝ)^(1/2+h)) →
      (∀ n ∈ E, retained X c t n) → (E.card : ℝ) ≤
        (4/c^2)*(2:ℝ)^((142/100:ℝ)*Real.log (1/t))*X*
          (1/Real.log X+2*h+t^(99/100:ℝ)) := by
  classical
  obtain ⟨Y0,recip⟩ := Erdos955.PPT.prime_reciprocal_interval_from_Chebyshev cheb
  obtain ⟨Y1,count⟩ := Erdos955.PPT.eventual_prime_count_range_of_Chebyshev cheb
  have hcast : Tendsto (fun X : ℕ => (X:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [(window_power_at_top hc).eventually_ge_atTop Y0,
    (window_power_at_top hc).eventually_ge_atTop Y1,
    (Real.tendsto_log_atTop.comp hcast).eventually_ge_atTop 1,
    eventually_gt_atTop (1 : ℕ)] with X hcut0 hcut1 hlog hx h hh hh' E hwin hret
  let K := ⌊(142/100:ℝ)*Real.log (1/t)⌋₊
  let u := t^(99/100:ℝ)
  have hxR : 1 < (X:ℝ) := by exact_mod_cast hx
  have hu : 0 ≤ u := Real.rpow_nonneg ht.le _
  have hlogR : 1 ≤ Real.log (X:ℝ) := hlog
  have hW : 0 ≤ 1/Real.log X+2*h+u := by positivity
  let T := (X:ℝ)^t
  let P := stripPrimes X ((X:ℝ)^c) ((X:ℝ)^(1/2-h)) ((X:ℝ)^(1/2+h)) ((X:ℝ)^u)
  let Q := fun m p => (quotientPrimes X m p ((X:ℝ)^c)).card
  have hp (m : ℕ) (_hm : m ∈ residuals X K T) (U : Finset ℕ) (hU : U ∈ (largePrimes m T).powerset) :
      ∑ p ∈ P U, 1/(p:ℝ) ≤ (139/100:ℝ)/c*(1/Real.log X+2*h+u) :=
    census_strip_estimate Y0 recip hxR hc hh hu hcut0 _ (mem_powerset.mp hU)
  have hq (m : ℕ) (hm : m ∈ residuals X K T) (U : Finset ℕ) (_hU : U ∈ (largePrimes m T).powerset)
      (p : ℕ) (hp : p ∈ P U) :
      (Q m p : ℝ) ≤ (139/100:ℝ)/c*X/Real.log X*(1/(m:ℝ))*(1/(p:ℝ)) :=
    census_quotient_estimate Y1 count hxR hc hcut1 (mem_Icc.mp (mem_filter.mp hm).1).1
      (mem_Icc.mp (mem_filter.mp hp).1).1
  have hfinite := census_sum_of_prime_bounds X K T P Q hlogR hc hW hp hq
  have hcount := retained_census hx hh' E hwin hret
  have hK0 : 0 ≤ (142/100:ℝ)*Real.log (1/t) :=
    mul_nonneg (by norm_num) (Real.log_nonneg ((one_le_div ht).mpr ht1))
  have hK : (2:ℝ)^K ≤ (2:ℝ)^((142/100:ℝ)*Real.log (1/t)) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.floor_le hK0)
  apply ((Nat.cast_le.mpr hcount).trans hfinite).trans
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hK (by positivity)) (Nat.cast_nonneg _)) hW

theorem eventually_retained_estimate
    {c t : ℝ} (hc : 0 < c) (ht : 0 < t) (ht1 : t ≤ 1) :
    ∀ᶠ X : ℕ in atTop, ∀ h : ℝ, 0 ≤ h → h ≤ 1/20 → ∀ E : Finset ℕ,
      E ⊆ (Icc 1 X).filter (fun n : ℕ => ∃ d ∈ n.divisors,
        (X : ℝ)^(1/2-h) < (d : ℝ) ∧ (d : ℝ) < (X : ℝ)^(1/2+h)) →
      (∀ n ∈ E, retained X c t n) → (E.card : ℝ) ≤
        (4/c^2)*(2:ℝ)^((142/100:ℝ)*Real.log (1/t))*X*
          (1/Real.log X+2*h+t^(99/100:ℝ)) :=
  eventually_retained_estimate_of_Chebyshev Erdos955.PPT.eventual_prime_count_from_primorial hc ht ht1

end Erdos955.Window

end

section

namespace Erdos955.Window
open Filter

theorem divisor_window_of_prime_counting
    (cheb : ∀ {ε : ℝ}, 0 < ε → ∀ᶠ x : ℝ in atTop,
      (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ (Real.log 4 + ε) * x / Real.log x) :
    OMA.R_Erdos955_erdos_955_variants_pollack_pomerance_thompson_bound_R1_H1_R1.H1 :=
  window_endpoint (Erdos955.PPT.prime_reciprocal_interval_from_Chebyshev cheb)
    (fun _ _ hc hc1 ht htc => eventually_retained_estimate_of_Chebyshev cheb hc ht (by linarith))

end Erdos955.Window

end

section

namespace Erdos955.PPT
open Nat Finset

lemma totient_mul_le_first (a b : ℕ) : (a*b).totient ≤ a * b.totient := by
  induction a using induction_on_primes with
  | zero => simp
  | one => simp
  | prime_mul p a hp ih =>
    rw [Nat.mul_assoc p a b, Nat.mul_assoc p a b.totient]
    by_cases h : p ∣ a * b
    · rw [Nat.totient_mul_of_prime_of_dvd hp h]
      exact Nat.mul_le_mul_left _ ih
    · rw [Nat.totient_mul_of_prime_of_not_dvd hp h]
      exact Nat.mul_le_mul (Nat.sub_le _ _) ih

private lemma TotientRatio_dyadic_weight (F : ℕ → ℕ) (k c : ℕ)
    (h : ∀ j, 1 ≤ j → j ≤ 2 ^ k → c ≤ j * F j) :
    k * c ≤ 2 * ∑ i ∈ range (2 ^ k), F (i+1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    let m := 2 ^ k
    have hm : 0 < m := Nat.pow_pos (by decide)
    have power : 2 ^ (k+1) = m + m := by simp [m,pow_succ,Nat.mul_two]
    rw [power] at h ⊢
    have left := ih (fun j hj hle => h j hj (Nat.le_add_right_of_le hle))
    have each (i : ℕ) (hi : i ∈ range m) : c ≤ 2 * m * F (m+i+1) := by
      have bound := mem_range.mp hi
      have jj : m+i+1 ≤ m+m := by omega
      exact (h (m+i+1) (by omega) jj).trans (Nat.mul_le_mul_right _ (by omega))
    have total : m * c ≤ m * (2 * ∑ i ∈ range m, F (m+i+1)) := by
      calc
        m * c = ∑ _i ∈ range m, c := by simp
        _ ≤ ∑ i ∈ range m, 2 * m * F (m+i+1) := sum_le_sum each
        _ = _ := by rw [← Finset.mul_sum]; ac_rfl
    have right := Nat.le_of_mul_le_mul_left total hm
    change k * c ≤ 2 * ∑ i ∈ range m, F (i+1) at left
    rw [sum_range_add, Nat.mul_add, Nat.succ_mul]
    exact Nat.add_le_add left right

/-- Factorial moduli give explicit arbitrarily small coprime proportions. -/
theorem factorial_totient_ratio (k : ℕ) :
    k * (factorial (2 ^ k)).totient ≤ 2 * factorial (2 ^ k) := by
  let M := 2 ^ k
  let Q := factorial M
  have qpos : Q ≠ 0 := Nat.factorial_ne_zero _
  let F := fun j => (Q/j).totient
  have d (j : ℕ) (hj : 1 ≤ j) (hjM : j ≤ M) : j ∣ Q := Nat.dvd_factorial hj hjM
  have each (j : ℕ) (hj : 1 ≤ j) (hjM : j ≤ M) : Q.totient ≤ j * F j := by
    have H := totient_mul_le_first j (Q / j)
    rwa [Nat.mul_div_cancel' (d j hj hjM)] at H
  have scaled := TotientRatio_dyadic_weight F k Q.totient each
  have sub : (range M).image (fun i => i+1) ⊆ Q.divisors := by
    intro j hj
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hj
    exact Nat.mem_divisors.mpr ⟨d _ (by omega) (mem_range.mp hi),qpos⟩
  have sum_bound : (∑ i ∈ range M, F (i+1)) ≤ Q := by
    calc
      _ = ∑ j ∈ (range M).image (fun i => i+1), F j := by
        rw [sum_image]
        intro i _ j _ he
        exact Nat.add_right_cancel he
      _ ≤ ∑ j ∈ Q.divisors, F j := sum_le_sum_of_subset sub
      _ = Q := (Nat.sum_div_divisors Q Nat.totient).trans (Nat.sum_totient Q)
  exact scaled.trans (Nat.mul_le_mul_left 2 sum_bound)

end Erdos955.PPT

end

section

namespace Erdos955.PPT

/-- Count reduced residues in the complete and partial blocks below `N`. -/
theorem card_coprime_Icc_le (N Q : ℕ) (hQ : 0 < Q) :
    ((Finset.Icc 1 N).filter (fun n => n.Coprime Q)).card ≤ (N / Q + 1) * Q.totient := by
  let blocks := Finset.range (N / Q + 1)
  let residues := (Finset.range Q).filter (fun a => Q.Coprime a)
  have bound : ((Finset.Icc 1 N).filter (fun n => n.Coprime Q)).card ≤
      (blocks ×ˢ residues).card := by
    apply Finset.card_le_card_of_injOn (fun n : ℕ => (n / Q, n % Q))
    · intro n hn
      obtain ⟨hn, cop⟩ := Finset.mem_filter.mp hn
      apply Finset.mem_product.mpr
      constructor
      · exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right (Finset.mem_Icc.mp hn).2))
      · apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_range.mpr (Nat.mod_lt _ hQ), ?_⟩
        change Q.gcd (n % Q) = 1
        rw [Nat.gcd_comm, ← Nat.gcd_rec]
        exact cop.symm
    · intro a _ b _ he
      have hdiv : a / Q = b / Q := congrArg Prod.fst he
      have hmod : a % Q = b % Q := congrArg Prod.snd he
      calc
        a = a % Q + Q * (a / Q) := (Nat.mod_add_div _ _).symm
        _ = b % Q + Q * (b / Q) := by rw [hmod,hdiv]
        _ = b := Nat.mod_add_div _ _
  simpa only [Finset.card_product, blocks, Finset.card_range, residues, Nat.totient_eq_card_coprime] using bound

theorem coprime_factorial_of_rough {n M : ℕ}
    (rough : ∀ p : ℕ, p.Prime → p ≤ M → ¬ p ∣ n) : n.Coprime M.factorial := by
  by_cases hn : n = 1
  · simp [hn]
  · apply (Nat.coprime_factorial_iff hn).mpr
    exact Nat.lt_of_not_ge (fun hp => rough _ (Nat.minFac_prime hn) hp (Nat.minFac_dvd n))

end Erdos955.PPT

end

section

namespace Erdos955.PPT
open Nat Finset

/-- Quantitative finite sieve with a factorial modulus. -/
theorem rough_count_scaled (k N : ℕ) (hN : (2 ^ k).factorial ≤ N) :
    k * ((Icc 1 N).filter (fun n => n.Coprime (2^k).factorial)).card ≤ 4 * N := by
  let Q := (2^k).factorial
  have hp : 0 < Q := factorial_pos _
  calc
    _ ≤ k * ((N/Q + 1) * Q.totient) := Nat.mul_le_mul_left _ (card_coprime_Icc_le N Q hp)
    _ = (N/Q+1) * (k*Q.totient) := by ac_rfl
    _ ≤ (N/Q+1) * (2*Q) := Nat.mul_le_mul_left _ (factorial_totient_ratio k)
    _ = 2 * (N/Q*Q+Q) := by rw [Nat.add_mul,one_mul,Nat.mul_add]; ac_rfl
    _ ≤ 4 * N := by
      have hsum := Nat.add_le_add (Nat.div_mul_le_self N Q) hN
      omega

theorem small_count (k N : ℕ) (hk : 0 < k) (hN : k^2 ≤ N) :
    ((Icc 1 N).filter (fun n => n^2 ≤ N)).card ≤ N/k := by
  have sub : (Icc 1 N).filter (fun n => n^2 ≤ N) ⊆ Icc 1 (N/k) := by
    intro n hn
    obtain ⟨hs,hsq⟩ := mem_filter.mp hn
    refine mem_Icc.mpr ⟨(mem_Icc.mp hs).1, (Nat.le_div_iff_mul_le hk).mpr ?_⟩
    by_cases h : n ≤ k
    · exact (Nat.mul_le_mul_right k h).trans (by simpa [pow_two] using hN)
    · exact (Nat.mul_le_mul_left n (by omega : k ≤ n)).trans (by simpa [pow_two] using hsq)
  simpa using card_le_card sub

/-- For any fixed k, the three elementary exceptional classes together occupy at
most 6N/k integers as soon as the fixed cutoffs have been reached. -/
theorem exceptional_finite_bound (k N : ℕ) (hk : 0 < k)
    (hmod : (2^k).factorial ≤ N) (hsq : k^2 ≤ N) (S : Finset ℕ)
    (member : ∀ n ∈ S, 0 < n ∧ n ≤ N ∧
      ((∀ p : ℕ, p.Prime → p ≤ 2^k → ¬ p ∣ n) ∨
       (∃ q : ℕ, k^3 < q ∧ q ∣ n ∧ ∀ p : ℕ, p.Prime → p ∣ q → p^2 ∣ q) ∨ n^2 ≤ N)) :
    k * S.card ≤ 6 * N := by
  classical
  let R := (Icc 1 N).filter (fun n => n.Coprime (2^k).factorial)
  let P := (Icc 1 N).filter (fun n => ∃ q : ℕ, k^3 < q ∧ q ∣ n ∧ ∀ p : ℕ, p.Prime → p ∣ q → p^2 ∣ q)
  let T := (Icc 1 N).filter (fun n => n^2 ≤ N)
  have sub : S ⊆ (R ∪ P) ∪ T := by
    intro n hn
    obtain ⟨pos,ub,case1|case2|case3⟩ := member n hn
    · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨mem_Icc.mpr ⟨pos,ub⟩,
        coprime_factorial_of_rough case1⟩))
    · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨mem_Icc.mpr ⟨pos,ub⟩,case2⟩))
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_Icc.mpr ⟨pos,ub⟩,case3⟩)
  have pp : P.card ≤ N/k := by
    apply powerful_divisor_union_bound hk
    intro n hn
    obtain ⟨bounds,hq⟩ := mem_filter.mp hn
    exact ⟨(mem_Icc.mp bounds).1,(mem_Icc.mp bounds).2,hq⟩
  have hh : S.card ≤ R.card + P.card + T.card :=
    (card_le_card sub).trans ((card_union_le ..).trans (Nat.add_le_add_right (card_union_le ..) _))
  have hR : k * R.card ≤ 4*N := rough_count_scaled k N hmod
  have hP : k * P.card ≤ N := (Nat.mul_le_mul_left k pp).trans (Nat.mul_div_le N k)
  have hT : k * T.card ≤ N :=
    (Nat.mul_le_mul_left k (small_count k N hk hsq)).trans (Nat.mul_div_le N k)
  have hh' := Nat.mul_le_mul_left k hh
  rw [Nat.mul_add, Nat.mul_add] at hh'
  omega

end Erdos955.PPT

end

section

namespace Erdos955.PPT
open Filter Finset
open scoped Classical

/-- Pass from fixed natural cutoffs to cutoffs that eventually exceed them. -/
theorem elementary_with_cutoffs (L B : ℕ → ℝ)
    (largeL : ∀ k : ℕ, ∀ᶠ x : ℕ in atTop, ((2^k : ℕ) : ℝ) ≤ L x)
    (largeB : ∀ k : ℕ, ∀ᶠ x : ℕ in atTop, (k : ℝ)^3 ≤ B x)
    (δ : ℝ) (hδ : 0 < δ) : ∀ᶠ x : ℕ in atTop,
      let other := fun n : ℕ => (¬ ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ (p : ℝ) ≤ L x) ∨
        (∃ q ∈ n.divisors, B x < q ∧ ∀ p : ℕ, p.Prime → p ∣ q → p^2 ∣ q) ∨ n^2 ≤ x
      (((Icc 1 x).filter other).card : ℝ) ≤ δ*x := by
  classical
  obtain ⟨k, hk⟩ := exists_nat_gt (6 / δ)
  have hkR : 0 < (k : ℝ) := lt_trans (div_pos (by norm_num) hδ) hk
  have hkn : 0 < k := by exact_mod_cast hkR
  have six : (6 : ℝ) ≤ k*δ := ((div_lt_iff₀ hδ).mp hk).le
  filter_upwards [largeL k, largeB k, eventually_ge_atTop ((2^k).factorial),
    eventually_ge_atTop (k^2)] with x hL hB hmod hsq
  let E := fun n : ℕ => (¬ ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ (p : ℝ) ≤ L x) ∨
    (∃ q ∈ n.divisors, B x < q ∧ ∀ p : ℕ, p.Prime → p ∣ q → p^2 ∣ q) ∨ n^2 ≤ x
  let S := (Icc 1 x).filter E
  have hcount : k*S.card ≤ 6*x := by
    apply exceptional_finite_bound k x hkn hmod hsq S
    intro n hn
    obtain ⟨hnS, hcase⟩ := mem_filter.mp hn
    obtain ⟨pos, bounds⟩ := mem_Icc.mp hnS
    refine ⟨pos,bounds,?_⟩
    rcases hcase with noPrime | big | tiny
    · left
      intro p hp hpSmall hdvd
      exact noPrime ⟨p, hp, hdvd, (show (p : ℝ) ≤ ((2^k : ℕ) : ℝ) by exact_mod_cast hpSmall).trans hL⟩
    · right; left
      obtain ⟨q,hdiv,hq,powers⟩ := big
      have hcube : k^3 < q := by exact_mod_cast lt_of_le_of_lt hB hq
      exact ⟨q,hcube,(Nat.mem_divisors.mp hdiv).1,powers⟩
    · exact Or.inr (Or.inr tiny)
  have hreal : (k : ℝ)*S.card ≤ 6*(x : ℝ) := by exact_mod_cast hcount
  change (S.card : ℝ) ≤ δ*x
  apply (mul_le_mul_iff_right₀ hkR).mp
  calc
    (k : ℝ) * S.card ≤ 6*x := hreal
    _ ≤ (k*δ)*x := mul_le_mul_of_nonneg_right six (Nat.cast_nonneg _)
    _ = k*(δ*x) := by ac_rfl

end Erdos955.PPT

end

section

open Filter
namespace Erdos955.PPT

/-- Independent of ε, the logarithmic floor on the exponent eventually makes
this cutoff exceed any fixed cube. -/
theorem eventually_cube_le_cutoff (U : ℕ) (ε : ℕ → ℝ) :
    ∀ᶠ x : ℕ in atTop, (U : ℝ) ^ 3 ≤
      (x : ℝ) ^ (2 * max (ε x) (1 / Real.log (Real.log (x : ℝ)))) := by
  have hcast : Tendsto (fun x : ℕ => (x : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hcast
  have hll : Tendsto (fun x : ℕ => Real.log (Real.log (x : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hlog
  have hratio : Tendsto (fun x : ℕ =>
      Real.exp (Real.log (Real.log (x : ℝ))) / Real.log (Real.log (x : ℝ))) atTop atTop := by
    simpa only [Function.comp_def, pow_one] using (Real.tendsto_exp_div_pow_atTop 1).comp hll
  filter_upwards [hratio.eventually_ge_atTop ((U : ℝ) ^ 3),
    hcast.eventually_gt_atTop 0, hlog.eventually_gt_atTop 0, hll.eventually_gt_atTop 0]
    with x hratio hx hlog hll
  rw [Real.exp_log hlog] at hratio
  rw [Real.rpow_def_of_pos hx]
  let y := max (ε x) (1 / Real.log (Real.log (x : ℝ)))
  have hfloor : 1 / Real.log (Real.log (x : ℝ)) ≤ y := le_max_right _ _
  have hy : 0 ≤ y := (one_div_nonneg.mpr hll.le).trans hfloor
  have hle : 1 / Real.log (Real.log (x : ℝ)) ≤ 2 * y :=
    hfloor.trans (by simpa only [two_mul] using le_add_of_nonneg_right hy)
  calc
    (U : ℝ) ^ 3 ≤ Real.log (x : ℝ) / Real.log (Real.log (x : ℝ)) := hratio
    _ = Real.log (x : ℝ) * (1 / Real.log (Real.log (x : ℝ))) := by simp only [div_eq_mul_inv, one_mul]
    _ ≤ Real.log (x : ℝ) * (2 * y) := mul_le_mul_of_nonneg_left hle hlog.le
    _ ≤ Real.log (x : ℝ) * (2 * y) + 1 := le_add_of_nonneg_right zero_le_one
    _ ≤ Real.exp (Real.log (x : ℝ) * (2 * y)) := Real.add_one_le_exp _


end Erdos955.PPT

end

section

namespace Erdos955.PPT
open Finset Filter Topology
open scoped Classical

/-- The elementary exceptional-set endpoint in Pollack–Pomerance–Thompson, Section 2. -/
theorem elementary_endpoint_of_growth
    (growth : ∀ (U : ℕ) (ε : ℕ → ℝ), ∀ᶠ x : ℕ in atTop, (U : ℝ)^3 ≤
      (x : ℝ) ^ (2 * max (ε x) (1 / Real.log (Real.log (x : ℝ))))) :
    ∀ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) → ∀ δ : ℝ, 0 < δ → ∀ᶠ x : ℕ in atTop,
      let η := max (ε x) (1 / Real.log (Real.log x))
      let other := fun n : ℕ => (¬ ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ (p : ℝ) ≤ Real.log x) ∨
        (∃ q ∈ n.divisors, (x : ℝ) ^ (2 * η) < q ∧ ∀ p : ℕ, p.Prime → p ∣ q → p ^ 2 ∣ q) ∨ n ^ 2 ≤ x
      (((Icc 1 x).filter other).card : ℝ) ≤ δ * x := by
  intro ε _ δ hδ
  have hcast : Tendsto (fun x : ℕ => (x : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hcast
  exact elementary_with_cutoffs (fun x => Real.log (x : ℝ))
    (fun x => (x : ℝ) ^ (2 * max (ε x) (1 / Real.log (Real.log (x : ℝ)))))
    (fun k => hlog.eventually_ge_atTop ((2^k : ℕ) : ℝ)) (fun k => growth k ε) δ hδ

theorem elementary_endpoint :
    ∀ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) → ∀ δ : ℝ, 0 < δ → ∀ᶠ x : ℕ in atTop,
      let η := max (ε x) (1 / Real.log (Real.log x))
      let other := fun n : ℕ => (¬ ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ (p : ℝ) ≤ Real.log x) ∨
        (∃ q ∈ n.divisors, (x : ℝ) ^ (2 * η) < q ∧ ∀ p : ℕ, p.Prime → p ∣ q → p ^ 2 ∣ q) ∨ n ^ 2 ≤ x
      (((Icc 1 x).filter other).card : ℝ) ≤ δ * x :=
  elementary_endpoint_of_growth eventually_cube_le_cutoff

end Erdos955.PPT

end

section

namespace DivisorSumFibers

/-- A finite fiber bound for the linear relation in section 2 of
Pollack, Pomerance and Thompson, Divisor-sum fibers, equation (2.4).
For a fixed divisor d, use k = σ(d), m = s(d) and f = s. -/
theorem linear_fiber_card (k m a B : ℕ) (hm : 0 < m)
    (f : ℕ → ℕ) (E : Finset ℕ) (bound : ∀ e ∈ E, f e ≤ B)
    (relation : ∀ e ∈ E, k * f e + m * e = a) :
    E.card ≤ B / (m / m.gcd k) + 1 := by
  let M := m / m.gcd k
  have residue (e : ℕ) (he : e ∈ E) : k * f e ≡ a [MOD m] := by
    rw [← relation e he]
    simp [Nat.ModEq, Nat.add_mod]
  calc
    E.card ≤ (Finset.range (B / M + 1)).card := by
      apply Finset.card_le_card_of_injOn (fun e => f e / M)
      · intro e he
        exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right (bound e he)))
      · intro u hu v hv hdiv
        change f u / M = f v / M at hdiv
        have hmod : f u % M = f v % M :=
          ((residue u hu).trans (residue v hv).symm).cancel_left_div_gcd hm
        have hval : f u = f v := by
          calc f u = f u % M + M * (f u / M) := (Nat.mod_add_div _ _).symm
               _ = f v % M + M * (f v / M) := by rw [hmod, hdiv]
               _ = f v := Nat.mod_add_div _ _
        have same := (relation u hu).trans (relation v hv).symm
        rw [hval] at same
        exact Nat.eq_of_mul_eq_mul_left hm (Nat.add_left_cancel same)
    _ = _ := Finset.card_range _
end DivisorSumFibers

end

section

namespace Erdos955.PPT

open scoped ArithmeticFunction.sigma

/-- The definition of the proper divisor sum in FormalConjectures.ErdosProblems.955. -/
abbrev properSum (n : ℕ) : ℕ := σ 1 n - n

theorem properSum_add_self (n : ℕ) : properSum n + n = σ 1 n := by
  apply Nat.sub_add_cancel
  rw [ArithmeticFunction.sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]
  exact Nat.le_add_left _ _

/-- Pollack, Pomerance and Thompson, equation (2.4). -/
theorem fiber_identity {d e : ℕ} (h : Nat.Coprime d e) :
    properSum (d * e) = σ 1 d * properSum e + properSum d * e := by
  apply Nat.add_right_cancel (m := d * e)
  rw [properSum_add_self, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime h]
  calc
    σ 1 d * σ 1 e = σ 1 d * (properSum e + e) := by rw [properSum_add_self]
    _ = σ 1 d * properSum e + (properSum d + d) * e := by
      rw [Nat.mul_add, properSum_add_self d]
    _ = σ 1 d * properSum e + properSum d * e + d * e := by rw [Nat.add_mul, Nat.add_assoc]

/-- The common factor divides both the product's proper divisor sum and the fixed factor. -/
theorem fiber_gcd_dvd {d e : ℕ} (h : Nat.Coprime d e) :
    Nat.gcd (σ 1 d) (properSum d) ∣ properSum (d * e) ∧
    Nat.gcd (σ 1 d) (properSum d) ∣ d := by
  have hd := Nat.gcd_dvd_left (σ 1 d) (properSum d)
  have hs := Nat.gcd_dvd_right (σ 1 d) (properSum d)
  constructor
  · rw [fiber_identity h]
    exact dvd_add (dvd_mul_of_dvd_left hd _) (dvd_mul_of_dvd_left hs _)
  · apply (Nat.dvd_add_right hs).1
    rw [properSum_add_self]
    exact hd

end Erdos955.PPT

end

section

namespace Erdos955.PPT
open scoped ArithmeticFunction ArithmeticFunction.sigma

/-- The number of nonexceptional factors e in a single fiber with a fixed d
is controlled by one residue class of s(e), as in PPT, section 2. -/
theorem card_fixed_divisor (d a B : ℕ) (hd : 0 < properSum d) (E : Finset ℕ)
    (cop : ∀ e ∈ E, d.Coprime e) (value : ∀ e ∈ E, properSum (d * e) = a)
    (bound : ∀ e ∈ E, properSum e ≤ B) :
    E.card ≤ B / (properSum d / (properSum d).gcd (σ 1 d)) + 1 := by
  apply DivisorSumFibers.linear_fiber_card (σ 1 d) (properSum d) a B hd properSum E bound
  intro e he
  rw [← fiber_identity (cop e he)]
  exact value e he

end Erdos955.PPT

end

section

namespace Erdos955.PPT

/-- The largest divisor below the cutoff gives the coprime factorization
used in equations (2.1) and (2.2) of Divisor-sum fibers, Section 2. -/
theorem exists_gap_factorization {n r L U T : ℕ} (hr : 0 < r) (hn : r < n)
    (hL : L ≤ r) (hU : r < U) (hsep : L * T < U)
    (hgap : ∀ b : ℕ, b ∣ n → b ≤ L ∨ U ≤ b)
    (hsq : ∀ p : ℕ, p.Prime → p^2 ∣ n → p ≤ T) :
    ∃ d e : ℕ, n = d * e ∧ 0 < d ∧ d ≤ L ∧ 1 < e ∧ d.Coprime e ∧
      (∀ p : ℕ, p.Prime → p ∣ e → U ≤ d * p ∧ T < p) ∧
      (∀ p : ℕ, p.Prime → p ∣ n → p ≤ T → p ∣ d) := by
  let S := n.divisors.filter (· ≤ r)
  have hn0 : n ≠ 0 := by omega
  have h1 : 1 ∈ S := Finset.mem_filter.mpr
    ⟨Nat.mem_divisors.mpr ⟨one_dvd n, hn0⟩, hr⟩
  have hne : S.Nonempty := ⟨1, h1⟩
  let d := S.max' hne
  have hdmem : d ∈ S := S.max'_mem hne
  obtain ⟨hddiv, hdr⟩ := Finset.mem_filter.mp hdmem
  have hdpos : 0 < d := S.le_max' 1 h1
  have hdn := (Nat.mem_divisors.mp hddiv).1
  have hdL : d ≤ L := (hgap d hdn).resolve_right (by omega)
  obtain ⟨e, he⟩ := hdn
  have hepos : 1 < e := by
    by_contra! hc
    have hnd : n ≤ d := he ▸ (by simpa using Nat.mul_le_mul_left d hc)
    omega
  have hlarge (p : ℕ) (hp : p.Prime) (hpe : p ∣ e) : U ≤ d * p ∧ T < p := by
    have hdp : d * p ∣ n := he ▸ Nat.mul_dvd_mul_left d hpe
    have hlt : d < d * p := by simpa using Nat.mul_lt_mul_of_pos_left hp.one_lt hdpos
    have hrp : r < d * p := by
      by_contra! small
      have hm : d * p ∈ S := Finset.mem_filter.mpr
        ⟨Nat.mem_divisors.mpr ⟨hdp, hn0⟩, small⟩
      exact (not_lt_of_ge (S.le_max' _ hm)) hlt
    have hUp : U ≤ d * p := (hgap _ hdp).resolve_left (by omega)
    refine ⟨hUp, ?_⟩
    by_contra! hs
    exact (Nat.not_le_of_lt hsep) (hUp.trans (Nat.mul_le_mul hdL hs))
  refine ⟨d, e, he, hdpos, hdL, hepos, Nat.coprime_of_dvd ?_, hlarge, ?_⟩
  · intro p hp hpd hpe
    have hs : p^2 ∣ n := by rw [he, pow_two]; exact Nat.mul_dvd_mul hpd hpe
    exact (Nat.not_le_of_lt (hlarge p hp hpe).2) (hsq p hp hs)
  · intro p hp hpn hpT
    exact (hp.dvd_or_dvd (he ▸ hpn)).resolve_right
      (fun hpe => (Nat.not_le_of_lt (hlarge p hp hpe).2) hpT)

/-- A small prime factor of d provides the lower bound s(d) ≥ d / p. -/
theorem self_le_prime_mul_properSum {p d : ℕ} (hp : p.Prime) (hd : 0 < d)
    (hpd : p ∣ d) : d ≤ p * properSum d := by
  obtain ⟨k, rfl⟩ := hpd
  have hk : 0 < k := by by_contra! h; simp_all
  have hkmem : k ∈ (p * k).properDivisors := Nat.mem_properDivisors.mpr
    ⟨dvd_mul_left _ _, by simpa using Nat.mul_lt_mul_of_pos_right hp.one_lt hk⟩
  have hsum : properSum (p * k) = ∑ i ∈ (p * k).properDivisors, i := by
    rw [properSum, ArithmeticFunction.sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self, Nat.add_sub_cancel]
  apply Nat.mul_le_mul_left
  rw [hsum]
  exact Finset.single_le_sum (fun i _ => Nat.zero_le i) hkmem


end Erdos955.PPT

end

section

namespace Erdos955.PPT

/-- Each proper divisor of e is at most e divided by the least prime factor.
This gives a direct bound using the divisor count in place of the Euler product. -/
theorem minFac_mul_properSum_le (e : ℕ) (he : e ≠ 0) :
    e.minFac * properSum e ≤ e * e.properDivisors.card := by
  have hs : properSum e = ∑ i ∈ e.properDivisors, i := by
    rw [properSum, ArithmeticFunction.sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self, Nat.add_sub_cancel]
  rw [hs, Finset.mul_sum]
  calc
    ∑ b ∈ e.properDivisors, e.minFac * b ≤ ∑ _b ∈ e.properDivisors, e := by
      apply Finset.sum_le_sum
      intro b hb
      obtain ⟨k, hk, hek⟩ := (Nat.mem_properDivisors_iff_exists he).mp hb
      have hkdiv : k ∣ e := hek ▸ dvd_mul_left _ _
      calc
        e.minFac * b ≤ k * b := Nat.mul_le_mul_right _ (Nat.minFac_le_of_dvd hk hkdiv)
        _ = e := by rw [hek, Nat.mul_comm]
    _ = _ := by simp [Nat.mul_comm]

/-- If all prime factors of e jump across the divisor gap, then U s(e)
is bounded by the original n times the number of proper divisors of e. -/
theorem gap_mul_properSum_le {d e U : ℕ} (he : 1 < e)
    (hgap : ∀ p : ℕ, p.Prime → p ∣ e → U ≤ d * p) :
    U * properSum e ≤ (d * e) * e.properDivisors.card := by
  have h := hgap e.minFac (Nat.minFac_prime (by omega)) (Nat.minFac_dvd _)
  calc
    U * properSum e ≤ (d * e.minFac) * properSum e := Nat.mul_le_mul_right _ h
    _ = d * (e.minFac * properSum e) := Nat.mul_assoc .. 
    _ ≤ d * (e * e.properDivisors.card) := Nat.mul_le_mul_left _ (minFac_mul_properSum_le e (by omega))
    _ = _ := (Nat.mul_assoc ..).symm


end Erdos955.PPT

end

section

namespace Erdos955.PPT

/-- Dyadic blocks give an integral harmonic bound with explicit constants. -/
theorem sum_floor_harmonic (X k : ℕ) :
    ∑ i ∈ Finset.range (2^k), X / (i+1) ≤ X * (k+1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Nat.mul_two, Finset.sum_range_add]
    have hbound : ∑ i ∈ Finset.range (2^k), X / (2^k+i+1) ≤ X := by
      calc
        _ ≤ ∑ _i ∈ Finset.range (2^k), X / (2^k) := by
          apply Finset.sum_le_sum
          intro i _
          exact Nat.div_le_div_left (by omega) (Nat.two_pow_pos k)
        _ = (2^k) * (X / (2^k)) := by simp
        _ ≤ X := Nat.mul_div_le X _
    calc
      _ ≤ X * (k+1) + X := Nat.add_le_add ih hbound
      _ = _ := (Nat.mul_succ X _).symm

/-- After extracting g from d and s(d), the individual fiber is at most
one plus B*T/h, where d=g*h and d has a prime factor at most T. -/
theorem card_fixed_divisor_weight (d a B T g h j : ℕ) (hd : 0 < d)
    (hp : ∃ p : ℕ, p.Prime ∧ p ∣ d ∧ p ≤ T)
    (hg : g = (properSum d).gcd (ArithmeticFunction.sigma 1 d))
    (hdg : d = g*h) (hsj : properSum d = g*j)
    (E : Finset ℕ) (cop : ∀ e ∈ E, d.Coprime e)
    (value : ∀ e ∈ E, properSum (d * e) = a) (bound : ∀ e ∈ E, properSum e ≤ B) :
    E.card ≤ B*T/h + 1 := by
  obtain ⟨p, hprime, hpd, hpT⟩ := hp
  have hsmall := (self_le_prime_mul_properSum hprime hd hpd).trans
    (Nat.mul_le_mul_right _ hpT)
  have hprod : 0 < g*h := hdg ▸ hd
  have hgpos : 0 < g := by by_contra! hg0; simp [Nat.eq_zero_of_le_zero hg0] at hprod
  have hhpos : 0 < h := by by_contra! hh0; simp [Nat.eq_zero_of_le_zero hh0] at hprod
  have hmpos : 0 < properSum d := by
    by_contra! hm0
    simp [Nat.eq_zero_of_le_zero hm0] at hsmall
    omega
  have hT : h ≤ j*T := by
    rw [hsj, hdg, Nat.mul_left_comm T g j, Nat.mul_comm T j] at hsmall
    exact Nat.le_of_mul_le_mul_left hsmall hgpos
  have hm := card_fixed_divisor d a B hmpos E cop value bound
  rw [← hg, hsj, Nat.mul_div_cancel_left _ hgpos] at hm
  refine hm.trans (Nat.add_le_add_right ((Nat.le_div_iff_mul_le hhpos).mpr ?_) _)
  calc
    B/j*h ≤ B/j*(j*T) := Nat.mul_le_mul_left _ hT
    _ = (B/j*j)*T := (Nat.mul_assoc ..).symm
    _ ≤ B*T := Nat.mul_le_mul_right _ (Nat.div_mul_le_self ..)

end Erdos955.PPT

end

section

namespace Erdos955.PPT
open Finset
open scoped ArithmeticFunction.sigma

/-- Finitary summation in the proof of PPT Theorem 1.2.
Grouping first by g | a and then by d = g h costs one harmonic sum. -/
theorem finite_fiber_card {a L k B T N : ℕ} (ha : 0 < a) (hL : L ≤ 2^k)
    (F : Finset ℕ)
    (factors : ∀ n ∈ F, ∃ d e : ℕ, n = d*e ∧ 0 < d ∧ d ≤ L ∧ e ≤ N ∧
      d.Coprime e ∧ properSum n = a ∧ properSum e ≤ B ∧
      ∃ p : ℕ, p.Prime ∧ p ∣ d ∧ p ≤ T) :
    F.card ≤ a.divisors.card * (L + (B*T)*(k+1)) := by
  classical
  let E := fun (g h : ℕ) => (range (N+1)).filter (fun e =>
    let d := g*h
    0 < d ∧ (properSum d).gcd (σ 1 d) = g ∧
      (∃ p : ℕ, p.Prime ∧ p ∣ d ∧ p ≤ T) ∧
      d.Coprime e ∧ properSum (d*e) = a ∧ properSum e ≤ B)
  let A := fun g i => (E g (i+1)).image (fun e => (g*(i+1))*e)
  have cover : F ⊆ a.divisors.biUnion (fun g => (range L).biUnion (A g)) := by
    intro n hn
    obtain ⟨d,e,hde,hd,hdL,heN,hcop,hval,hB,hp⟩ := factors n hn
    let g := (properSum d).gcd (σ 1 d)
    have hgd : g ∣ d := by simpa [g, Nat.gcd_comm] using (fiber_gcd_dvd hcop).2
    have hga : g ∣ a := by
      rw [← hval,hde]
      simpa [g, Nat.gcd_comm] using (fiber_gcd_dvd hcop).1
    obtain ⟨h, hgh⟩ := hgd
    have hhpos : 0 < h := by by_contra! h0; simp [Nat.eq_zero_of_le_zero h0] at hgh; omega
    obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hhpos)
    have hhd : i+1 ≤ d := Nat.le_of_dvd hd (hgh ▸ dvd_mul_left _ _)
    refine mem_biUnion.mpr ⟨g, Nat.mem_divisors.mpr ⟨hga, ha.ne'⟩,
      mem_biUnion.mpr ⟨i,mem_range.mpr (by omega),?_⟩⟩
    apply mem_image.mpr
    refine ⟨e, mem_filter.mpr ⟨mem_range.mpr (by omega), ?_⟩, ?_⟩
    · change 0 < g*(i+1) ∧ _
      rw [← hgh]
      exact ⟨hd,rfl,hp,hcop,hde ▸ hval,hB⟩
    · rw [← hgh, ← hde]
  have bound (g i : ℕ) : (A g i).card ≤ B*T/(i+1) + 1 := by
    refine card_image_le.trans ?_
    by_cases hne : (E g (i+1)).Nonempty
    · obtain ⟨e, he⟩ := hne
      let d := g*(i+1)
      obtain ⟨hd,hg,hp,_⟩ := (mem_filter.mp he).2
      have hgs : g ∣ properSum d := hg ▸ Nat.gcd_dvd_left _ _
      obtain ⟨j, hj⟩ := hgs
      apply card_fixed_divisor_weight d a B T g (i+1) j hd hp hg.symm rfl hj
      · intro e he; exact (mem_filter.mp he).2.2.2.2.1
      · intro e he; exact (mem_filter.mp he).2.2.2.2.2.1
      · intro e he; exact (mem_filter.mp he).2.2.2.2.2.2
    · rw [not_nonempty_iff_eq_empty.mp hne, card_empty]
      exact Nat.zero_le _
  have total (g : ℕ) : ((range L).biUnion (A g)).card ≤ L + (B*T)*(k+1) := by
    have hsum : ∑ i ∈ range L, B*T/(i+1) ≤ B*T*(k+1) := by
      apply le_trans _ (sum_floor_harmonic (B*T) k)
      exact sum_le_sum_of_subset (Finset.range_mono hL)
    calc
      _ ≤ ∑ i ∈ range L, (A g i).card := card_biUnion_le
      _ ≤ ∑ i ∈ range L, (B*T/(i+1) + 1) := sum_le_sum (fun i _ => bound g i)
      _ = L + ∑ i ∈ range L, B*T/(i+1) := by simp [sum_add_distrib, Nat.add_comm]
      _ ≤ _ := Nat.add_le_add_left hsum _
  calc
    _ ≤ _ := card_le_card cover
    _ ≤ ∑ g ∈ a.divisors, ((range L).biUnion (A g)).card := card_biUnion_le
    _ ≤ ∑ _g ∈ a.divisors, (L + (B*T)*(k+1)) := sum_le_sum (fun g _ => total g)
    _ = _ := by simp

end Erdos955.PPT

end

section

namespace Erdos955.PPT

/-- A finite uniform bound on a single divisor-sum fiber, before using the
asymptotic maximal order of the divisor function. The elementary bound on
the proper divisor sum of e uses only its divisor count and least prime factor. -/
theorem good_divisor_fiber_bound {a X r L U T k D : ℕ} (ha : 0 < a) (hr : 0 < r)
    (hL : L ≤ r) (hU : r < U) (hsep : L*T < U) (hdyadic : L ≤ 2^k)
    (hcount : ∀ e : ℕ, e ≤ X → e.properDivisors.card ≤ D)
    (F : Finset ℕ)
    (member : ∀ n ∈ F, r < n ∧ n ≤ X ∧ properSum n = a ∧
      (∀ b : ℕ, b ∣ n → b ≤ L ∨ U ≤ b) ∧
      (∀ p : ℕ, p.Prime → p^2 ∣ n → p ≤ T) ∧
      ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ p ≤ T) :
    F.card ≤ a.divisors.card * (L + (X*D/U*T)*(k+1)) := by
  apply finite_fiber_card (N := X) ha hdyadic
  intro n hn
  obtain ⟨hrn,hnX,hval,hgap,hsq,p,hprime,hpn,hpT⟩ := member n hn
  obtain ⟨d,e,hde,hd,hdL,he,hcop,large,small⟩ :=
    exists_gap_factorization hr hrn hL hU hsep hgap hsq
  have heX : e ≤ X := (Nat.le_of_dvd (hr.trans hrn) (hde ▸ dvd_mul_left _ _)).trans hnX
  refine ⟨d,e,hde,hd,hdL,heX,hcop,hval,?_,p,hprime,small p hprime hpn hpT,hpT⟩
  have hbound := gap_mul_properSum_le he (fun p hp hpe => (large p hp hpe).1)
  apply (Nat.le_div_iff_mul_le (hr.trans hU)).mpr
  rw [Nat.mul_comm (properSum e), ← hde] at *
  exact hbound.trans (Nat.mul_le_mul hnX (hcount e heX))

end Erdos955.PPT

end

section

namespace Erdos955.PPT
open Finset
open scoped Classical

/-- Apply the finite bound directly to the four real cutoff conditions.
The three integer separation inequalities can be checked once for each X. -/
theorem fiber_outside_real_windows (X a D k : ℕ) (A B C J : ℝ) (ha : 0 < a)
    (hr : 0 < X.sqrt) (hl : ⌊A⌋₊ ≤ X.sqrt) (hu : X.sqrt < ⌈B⌉₊)
    (hgap : ⌊A⌋₊ * ⌈max C J⌉₊ < ⌈B⌉₊) (hdyadic : ⌊A⌋₊ ≤ 2^k)
    (hcount : ∀ e : ℕ, e ≤ X → e.properDivisors.card ≤ D) :
    let window := fun n : ℕ => ∃ d ∈ n.divisors, A < d ∧ (d : ℝ) < B
    let other := fun n : ℕ => (¬ ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ (p : ℝ) ≤ J) ∨
      (∃ q ∈ n.divisors, C < q ∧ ∀ p : ℕ, p.Prime → p ∣ q → p^2 ∣ q) ∨ n^2 ≤ X
    let good := (Icc 1 X).filter (fun n => ¬ window n ∧ ¬ other n)
    (good.filter (fun n => properSum n = a)).card ≤
      a.divisors.card * (⌊A⌋₊ + (X*D/⌈B⌉₊*⌈max C J⌉₊)*(k+1)) := by
  classical
  dsimp only
  apply good_divisor_fiber_bound ha hr hl hu hgap hdyadic hcount
  intro n hn
  obtain ⟨hn,hvalue⟩ := mem_filter.mp hn
  obtain ⟨hn,hwin,hother⟩ := mem_filter.mp hn
  obtain ⟨hn1, hnX⟩ := mem_Icc.mp hn
  have hn0 : n ≠ 0 := by omega
  have hroot : X.sqrt < n := by
    by_contra! small
    exact hother (Or.inr (Or.inr ((Nat.pow_le_pow_left small 2).trans (Nat.sqrt_le' X))))
  refine ⟨hroot, hnX, hvalue, ?_, ?_, ?_⟩
  · intro d hdn
    by_cases hlower : (d : ℝ) ≤ A
    · exact Or.inl (Nat.le_floor hlower)
    · apply Or.inr
      apply Nat.ceil_le.mpr
      by_contra! h
      exact hwin ⟨d, Nat.mem_divisors.mpr ⟨hdn, hn0⟩, lt_of_not_ge hlower, h⟩
  · intro p hprime hp2
    have hC : ((p^2 : ℕ) : ℝ) ≤ C := by
      by_contra! large
      refine hother (Or.inr (Or.inl ⟨p^2, Nat.mem_divisors.mpr ⟨hp2,hn0⟩, large, ?_⟩))
      intro q hq hqp
      have eq := (Nat.prime_dvd_prime_iff_eq hq hprime).mp (hq.dvd_of_dvd_pow hqp)
      simp [eq]
    have hself : p ≤ p^2 := by simpa [pow_two] using Nat.le_mul_self p
    have hs : (p : ℝ) ≤ (⌈max C J⌉₊ : ℕ) :=
      ((Nat.cast_le.mpr hself).trans hC).trans ((le_max_left C J).trans (Nat.le_ceil _))
    exact_mod_cast hs
  · have hex : ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ (p : ℝ) ≤ J := by
      by_contra h
      exact hother (Or.inl h)
    obtain ⟨p, hp, hpn, hpJ⟩ := hex
    have hs : (p : ℝ) ≤ (⌈max C J⌉₊ : ℕ) :=
      hpJ.trans ((le_max_right C J).trans (Nat.le_ceil _))
    exact ⟨p,hp,hpn,by exact_mod_cast hs⟩

end Erdos955.PPT

end

section

namespace Erdos955.PPT
open Finset

private theorem DivisorPrimeSplit_prime_exponent_le_log {n p : ℕ} (hn : n ≠ 0) (hp : p ∈ n.primeFactors) :
    (n.factorization p : ℝ) ≤ Real.log n / Real.log 2 := by
  have hnat : 2 ^ n.factorization p ≤ n :=
    (Nat.pow_le_pow_left (Nat.prime_of_mem_primeFactors hp).two_le _).trans (Nat.ordProj_le p hn)
  have hreal : (2 : ℝ) ^ n.factorization p ≤ n := by exact_mod_cast hnat
  have hlog := Real.log_le_log (pow_pos (by norm_num : (0 : ℝ) < 2) _) hreal
  rw [Real.log_pow] at hlog
  exact (le_div_iff₀ (Real.log_pos (by norm_num))).mpr hlog

private theorem DivisorPrimeSplit_prime_product_rpow (s : Finset ℕ) (e : ℕ → ℕ) (a : ℝ) :
    (∏ p ∈ s, ((p : ℝ) ^ e p) ^ a) = (∏ p ∈ s, (p : ℝ) ^ e p) ^ a := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hp ih =>
    rw [prod_insert hp, prod_insert hp, ih, Real.mul_rpow (by positivity)
      (Finset.prod_nonneg fun i _ => pow_nonneg (Nat.cast_nonneg i) _)]

/-- The contribution of primes below `Y` is at most one factor `log n / log 2 + 1`
per prime. Above `Y`, every local divisor count is absorbed into the `a`th power. -/
theorem divisor_prime_split {n : ℕ} (hn : n ≠ 0) {Y a : ℝ} (hY : 1 ≤ Y) (ha : 0 ≤ a)
    (h2 : 2 ≤ Y ^ a) : (n.divisors.card : ℝ) ≤
      (Real.log n / Real.log 2 + 1) ^ (Y + 1) * (n : ℝ) ^ a := by
  classical
  let B := Real.log n / Real.log 2 + 1
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  have hB : 1 ≤ B := le_add_of_nonneg_left
    (div_nonneg (Real.log_nonneg hnR) (Real.log_pos (by norm_num)).le)
  let S := n.primeFactors.filter (fun p : ℕ => (p : ℝ) < Y)
  have hS : S ⊆ range (⌊Y⌋₊ + 1) := by
    intro p hp
    exact mem_range.mpr (Nat.lt_succ_of_le (Nat.le_floor (mem_filter.mp hp).2.le))
  have hcardN : S.card ≤ ⌊Y⌋₊ + 1 := (card_le_card hS).trans_eq (card_range _)
  have hcard : (S.card : ℝ) ≤ Y + 1 := by
    calc (S.card : ℝ) ≤ (⌊Y⌋₊ : ℝ) + 1 := by exact_mod_cast hcardN
         _ ≤ Y + 1 := add_le_add_left (Nat.floor_le (zero_le_one.trans hY)) _
  have hlocal (p : ℕ) (hp : p ∈ n.primeFactors) :
      (n.factorization p : ℝ) + 1 ≤
      (if (p : ℝ) < Y then B else 1) * (((p : ℝ) ^ n.factorization p) ^ a) := by
    have hpone : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_le
    split_ifs with hsmall
    · exact (add_le_add_left (DivisorPrimeSplit_prime_exponent_le_log hn hp) 1).trans
        (le_mul_of_one_le_right (zero_le_one.trans hB) (Real.one_le_rpow (one_le_pow₀ hpone) ha))
    · rw [one_mul, ← Real.rpow_natCast_mul (Nat.cast_nonneg p), mul_comm,
        Real.rpow_mul_natCast (Nat.cast_nonneg p)]
      have hnat : n.factorization p + 1 ≤ 2 ^ n.factorization p := Nat.lt_two_pow_self
      calc (n.factorization p : ℝ) + 1 ≤ (2 : ℝ) ^ n.factorization p := by exact_mod_cast hnat
           _ ≤ _ := pow_le_pow_left₀ (by norm_num)
                     (h2.trans (Real.rpow_le_rpow (zero_le_one.trans hY) (le_of_not_gt hsmall) ha)) _
  have hfactor : (∏ p ∈ n.primeFactors, (p : ℝ) ^ n.factorization p) = (n : ℝ) := by
    exact_mod_cast (Nat.prod_primeFactors_pow_factorization hn).symm
  rw [Nat.card_divisors hn, Nat.cast_prod]
  simp only [Nat.cast_add, Nat.cast_one]
  calc ∏ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1) ≤
          ∏ p ∈ n.primeFactors, ((if (p : ℝ) < Y then B else 1) *
            (((p : ℝ) ^ n.factorization p) ^ a)) :=
        prod_le_prod (fun _ _ => by positivity) hlocal
       _ = B ^ S.card * (n : ℝ) ^ a := by
         rw [prod_mul_distrib, DivisorPrimeSplit_prime_product_rpow, hfactor, ← prod_filter]
         simp [S]
       _ ≤ _ := by
         rw [← Real.rpow_natCast B S.card]
         exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hB hcard)
           (Real.rpow_nonneg (Nat.cast_nonneg _) _)

end Erdos955.PPT

end

section

namespace Erdos955.PPT
open Filter

/-- An explicit eventual threshold at which the logarithmic cost of all small
primes fits inside one half of the available `log x / loglog x`. -/
theorem small_prime_log_budget {t L : ℝ} (ht : 0 < t) (hL : Real.log t = L)
    (htbig : 2 / Real.log 2 + 1 ≤ t) (hLbig : 384 ≤ L) :
    Real.log (2 * t / Real.log 2 + 1) * (Real.exp (L / 2) + 1) ≤ t / (2 * L) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have ht1 : 1 ≤ t := by linarith [show 0 ≤ 2 / Real.log 2 by positivity]
  have hcost : 2 * t / Real.log 2 + 1 ≤ t ^ 2 := by
    have := mul_le_mul_of_nonneg_right htbig ht.le
    rw [add_mul, one_mul, div_mul_eq_mul_div] at this
    nlinarith
  have hlog := Real.log_le_log (by positivity) hcost
  rw [Real.log_pow, hL, Nat.cast_ofNat] at hlog
  have hLpos : 0 < L := by linarith
  have he : 1 ≤ Real.exp (L / 2) := Real.one_le_exp (by positivity)
  have hlarge : 8 * L ^ 2 ≤ Real.exp (L / 2) := by
    have hseries := Real.pow_div_factorial_le_exp (x := L / 2) (by positivity) 3
    norm_num at hseries
    nlinarith [mul_nonneg (sq_nonneg L) (sub_nonneg.mpr hLbig)]
  have he2 := mul_le_mul_of_nonneg_right hlarge (Real.exp_pos (L / 2)).le
  have hsum : Real.exp (L / 2) * Real.exp (L / 2) = t := by
    rw [← Real.exp_add, add_halves, ← hL, Real.exp_log ht]
  rw [hsum] at he2
  apply (le_div_iff₀ (by positivity : 0 < 2 * L)).mpr
  have hbound := mul_le_mul_of_nonneg_right hlog (by positivity : 0 ≤ Real.exp (L / 2) + 1)
  have he1 := mul_le_mul_of_nonneg_left (by linarith : Real.exp (L / 2) + 1 ≤ 2 * Real.exp (L / 2)) (by positivity : 0 ≤ 2 * L)
  exact ((mul_le_mul_of_nonneg_right (hbound.trans he1) (by positivity : 0 ≤ 2 * L)).trans (by nlinarith only [he2]))

theorem prime_split_scale {L : ℝ} (hL : 0 < L) :
    2 ≤ (Real.exp (L / 2)) ^ ((3 / 2 : ℝ) / L) := by
  rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  have h : L / 2 * (3 / 2 / L) = (3 / 4 : ℝ) := by field_simp; ring
  rw [h]
  nlinarith [Real.quadratic_le_exp_of_nonneg (x := (3 / 4 : ℝ)) (by norm_num)]

/-- Uniform divisor bound at both scales used in the good-fiber estimate. -/
theorem eventually_divisor_card_le : ∀ᶠ x : ℕ in atTop,
    ∀ k : ℕ, 1 ≤ k → k ≤ 2 → ∀ n : ℕ, n ≤ x ^ k →
      (n.divisors.card : ℝ) ≤ (x : ℝ) ^ (2 * k / Real.log (Real.log (x : ℝ))) := by
  have hcast : Tendsto (fun x : ℕ => (x : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop := Real.tendsto_log_atTop.comp hcast
  have hll : Tendsto (fun x : ℕ => Real.log (Real.log (x : ℝ))) atTop atTop := Real.tendsto_log_atTop.comp hlog
  filter_upwards [hcast.eventually_gt_atTop 0, hlog.eventually_gt_atTop 0,
    hlog.eventually_ge_atTop (2 / Real.log 2 + 1), hll.eventually_ge_atTop 384]
    with x hx ht htbig hLbig
  let t := Real.log (x : ℝ)
  let L := Real.log t
  have hL : 0 < L := by change 0 < Real.log (Real.log (x : ℝ)); linarith
  intro k hk1 hk2 n hn
  by_cases hnzero : n = 0
  · subst n
    simpa using Real.rpow_nonneg hx.le (2 * k / L)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hnzero
  have hnpos : 0 < (n : ℝ) := zero_lt_one.trans_le hn1
  have hk1r : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hk2r : (k : ℝ) ≤ 2 := by exact_mod_cast hk2
  have hnt : Real.log n ≤ k * t := by
    have hcomp := Real.log_le_log hnpos (show (n : ℝ) ≤ (x : ℝ) ^ k by exact_mod_cast hn)
    simpa [t, Real.log_pow] using hcomp
  let Y := Real.exp (L/2)
  let a := (3/2 : ℝ)/L
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have ht' : 0 < t := ht
  have hY : 1 ≤ Y := Real.one_le_exp (by positivity)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hB : 0 < Real.log n / Real.log 2 + 1 := by
    have hh := Real.log_nonneg hn1
    positivity
  have hcost := small_prime_log_budget ht' rfl htbig hLbig
  have hmajor : Real.log (Real.log n / Real.log 2 + 1) * (Y + 1) ≤ t / (2 * L) := by
    apply le_trans _ hcost
    apply mul_le_mul_of_nonneg_right _ (by dsimp [Y]; positivity)
    apply Real.log_le_log hB
    apply add_le_add_left
    exact div_le_div_of_nonneg_right (hnt.trans (mul_le_mul_of_nonneg_right hk2r ht'.le)) hl2.le
  have h := divisor_prime_split hnzero hY ha (prime_split_scale hL)
  apply h.trans
  rw [Real.rpow_def_of_pos hB, Real.rpow_def_of_pos hnpos, Real.rpow_def_of_pos hx, ← Real.exp_add, Real.exp_le_exp]
  change Real.log (Real.log n / Real.log 2 + 1) * (Y + 1) + Real.log n * a ≤ t * (2 * k / L)
  have hbig := mul_le_mul_of_nonneg_right hnt ha
  calc _ ≤ t / (2 * L) + (k * t) * a := add_le_add hmajor hbig
       _ ≤ _ := by
          dsimp [a]
          field_simp [hL.ne']
          nlinarith [mul_nonneg (sub_nonneg.mpr hk1r) ht'.le]

theorem eventually_divisor_card_linear_and_square : ∀ᶠ x : ℕ in atTop,
    (∀ e ≤ x, (Nat.divisors e).card ≤ ((x : ℝ) ^ (2 / Real.log (Real.log x)))) ∧
    (∀ a ≤ x^2, (Nat.divisors a).card ≤ ((x : ℝ) ^ (4 / Real.log (Real.log x)))) := by
  filter_upwards [eventually_divisor_card_le] with x hx
  constructor
  · simpa only [pow_one, Nat.cast_one, mul_one] using hx 1 (by decide) (by decide)
  · simpa only [Nat.cast_ofNat, show (2 : ℝ) * 2 = 4 by norm_num] using hx 2 (by decide) (by decide)

end Erdos955.PPT

end

section

namespace Erdos955.PPT
open Filter Finset Topology
open scoped Classical

theorem properSum_le_square (n : ℕ) : properSum n ≤ n^2 := by
  rw [properSum, ArithmeticFunction.sigma_one_apply,
      Nat.sum_divisors_eq_sum_properDivisors_add_self, Nat.add_sub_cancel]
  calc
    _ ≤ ∑ _i ∈ n.properDivisors, n := by
      apply sum_le_sum
      intro i hi
      exact (Nat.mem_properDivisors.mp hi).2.le
    _ = n.properDivisors.card*n := by simp
    _ ≤ n^2 := by
      rw [pow_two]
      exact Nat.mul_le_mul_right _ ((card_le_card Nat.properDivisors_subset_divisors).trans
        (Nat.card_divisors_le_self n))

theorem fiber_uniform_K {X a K k : ℕ} {A B C J D V : ℝ} (ha : 0 < a)
    (hr : 0 < X.sqrt) (hl : ⌊A⌋₊ ≤ X.sqrt) (hu : X.sqrt < ⌈B⌉₊)
    (hgap : ⌊A⌋₊ * ⌈max C J⌉₊ < ⌈B⌉₊) (hdyadic : ⌊A⌋₊ ≤ 2^k)
    (dt : ∀ e ≤ X, (e.divisors.card : ℝ) ≤ D)
    (at' : ∀ a ≤ X^2, (a.divisors.card : ℝ) ≤ V)
    (budget : ∀ s : ℕ, (s : ℝ) ≤ V →
      s*(⌊A⌋₊ + (X*⌊D⌋₊/⌈B⌉₊*⌈max C J⌉₊)*(k+1)) ≤ K) :
    let window := fun n : ℕ => ∃ d ∈ n.divisors, A < d ∧ (d : ℝ) < B
    let other := fun n : ℕ => (¬ ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ (p : ℝ) ≤ J) ∨
      (∃ q ∈ n.divisors, C < q ∧ ∀ p : ℕ, p.Prime → p ∣ q → p^2 ∣ q) ∨ n^2 ≤ X
    let good := (Icc 1 X).filter (fun n => ¬ window n ∧ ¬ other n)
    (good.filter (fun n => properSum n = a)).card ≤ K := by
  by_cases small : a ≤ X^2
  · apply (fiber_outside_real_windows X a ⌊D⌋₊ k A B C J ha hr hl hu hgap hdyadic ?_).trans
      (budget a.divisors.card (at' a small))
    intro e he
    exact (card_le_card Nat.properDivisors_subset_divisors).trans (Nat.le_floor (dt e he))
  · dsimp only
    have empty : ∀ n, n ∈ Icc 1 X → properSum n ≠ a := by
      intro n hn eq
      apply small
      rw [← eq]
      exact (properSum_le_square n).trans (Nat.pow_le_pow_left (mem_Icc.mp hn).2 2)
    have hempty : ∀ (S : Finset ℕ), S ⊆ Icc 1 X → (S.filter (fun n => properSum n = a)) = ∅ := by
      intro S hS
      exact eq_empty_iff_forall_notMem.mpr (fun n hn => (empty n (hS (mem_filter.mp hn).1)) (mem_filter.mp hn).2)
    rw [hempty _ (filter_subset _ _), card_empty]
    exact Nat.zero_le _

/-- Apply the divisor estimates to any η at least 1 / log log X. -/
theorem lift_exponent_both (X : ℕ) (hx : 1 ≤ X) (η : ℝ) (hη : 1/Real.log (Real.log X) ≤ η)
    (bounds : (∀ n ≤ X, (n.divisors.card : ℝ) ≤ (X : ℝ)^(2 / Real.log (Real.log X))) ∧
      (∀ n ≤ X^2, (n.divisors.card : ℝ) ≤ (X : ℝ)^(4 / Real.log (Real.log X)))) :
    (∀ n ≤ X, (n.divisors.card : ℝ) ≤ (X : ℝ)^(2*η)) ∧
      (∀ n ≤ X^2, (n.divisors.card : ℝ) ≤ (X : ℝ)^(4*η)) := by
  have hxR : (1 : ℝ) ≤ X := by exact_mod_cast hx
  constructor
  · intro n hn
    apply (bounds.1 n hn).trans (Real.rpow_le_rpow_of_exponent_le hxR ?_)
    linarith only [show 2 / Real.log (Real.log X) = 2*(1/Real.log (Real.log X)) by ring, hη]
  · intro n hn
    apply (bounds.2 n hn).trans (Real.rpow_le_rpow_of_exponent_le hxR ?_)
    linarith only [show 4 / Real.log (Real.log X) = 4*(1/Real.log (Real.log X)) by ring, hη]

end Erdos955.PPT

end

section

namespace Erdos955.PPT
open Filter

/-- A half copy of the exponent floor absorbs a logarithm and any fixed constant. -/
theorem eventually_half_eta_dominates (ε : ℕ → ℝ) (H : ℝ) : ∀ᶠ x : ℕ in atTop,
    let η := max (ε x) (1 / Real.log (Real.log (x : ℝ)))
    1 ≤ (x : ℝ) ∧ 1 ≤ Real.log x ∧ 0 ≤ η ∧
    8 * Real.log x ≤ (x : ℝ) ^ (η/2) ∧ H ≤ (x : ℝ) ^ (η/2) := by
  have hcast : Tendsto (fun x : ℕ => (x : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop := Real.tendsto_log_atTop.comp hcast
  have hll : Tendsto (fun x : ℕ => Real.log (Real.log (x : ℝ))) atTop atTop := Real.tendsto_log_atTop.comp hlog
  filter_upwards [hcast.eventually_ge_atTop 1, hlog.eventually_ge_atTop 8,
    hlog.eventually_ge_atTop H, hll.eventually_ge_atTop 24] with x hx ht8 htH hLbig
  let t := Real.log (x : ℝ)
  let L := Real.log t
  let η := max (ε x) (1/L)
  change 1 ≤ (x : ℝ) ∧ 1 ≤ t ∧ 0 ≤ η ∧ 8 * t ≤ (x : ℝ)^(η/2) ∧ H ≤ (x : ℝ)^(η/2)
  have ht : 0 < t := by change 0 < Real.log (x : ℝ); linarith
  have hL : 0 < L := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 24) hLbig
  have hη : 1/L ≤ η := le_max_right ..
  have hlarge : 4 * L^2 ≤ t := by
    have hseries := Real.pow_div_factorial_le_exp (x := L) hL.le 3
    have he : Real.exp L = t := Real.exp_log ht
    norm_num at hseries
    rw [he] at hseries
    nlinarith [mul_nonneg (sq_nonneg L) (sub_nonneg.mpr hLbig)]
  have hdouble : 2*L ≤ t * (η/2) := by
    have hlow : 2 * L ≤ t / (2 * L) := (le_div_iff₀ (by positivity)).mpr (by nlinarith only [hlarge])
    apply hlow.trans
    calc t / (2 * L) = t * ((1/L) / 2) := by ring
         _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) ht.le
  have hsq : t ^ 2 ≤ (x : ℝ) ^ (η/2) := by
    rw [Real.rpow_def_of_pos (zero_lt_one.trans_le hx)]
    calc t^2 = Real.exp (2 * L) := by rw [two_mul, Real.exp_add, show Real.exp L = t from Real.exp_log ht, pow_two]
         _ ≤ _ := Real.exp_le_exp.mpr hdouble
  have h8t : 8 * t ≤ t ^ 2 := by nlinarith [mul_nonneg ht.le (sub_nonneg.mpr ht8)]
  exact ⟨hx, (by change 1 ≤ Real.log (x : ℝ); linarith),
    (one_div_nonneg.mpr hL.le).trans hη, h8t.trans hsq,
    htH.trans ((by linarith : t ≤ 8 * t).trans (h8t.trans hsq))⟩

end Erdos955.PPT

end

section

namespace Erdos955.PPT
open Filter

/-- Separation of the two integer divisor windows, including the rounding cost
in the permitted multiplier. -/
theorem divisor_cutoff_order {X : ℕ} {η : ℝ} (hX : 1 < (X : ℝ)) (hη : 0 < η)
    (hC : 2 ≤ (X : ℝ) ^ (2 * η)) (hJ : Real.log X ≤ (X : ℝ) ^ (2 * η)) :
    let A := (X : ℝ) ^ ((1:ℝ)/2 - 10 * η)
    let B := (X : ℝ) ^ ((1:ℝ)/2 + 10 * η)
    let C := (X : ℝ) ^ (2 * η)
    let J := Real.log X
    let k := ⌈2 * J⌉₊
    0 < X.sqrt ∧ ⌊A⌋₊ ≤ X.sqrt ∧ X.sqrt < ⌈B⌉₊ ∧
      ⌊A⌋₊ * ⌈max C J⌉₊ < ⌈B⌉₊ ∧ ⌊A⌋₊ ≤ 2 ^ k := by
  dsimp only
  let A := (X : ℝ) ^ ((1 : ℝ)/2 - 10 * η)
  let B := (X : ℝ) ^ ((1 : ℝ)/2 + 10 * η)
  let C := (X : ℝ) ^ (2 * η)
  let k := ⌈2 * Real.log (X : ℝ)⌉₊
  have hX0 : (0 : ℝ) < X := zero_lt_one.trans hX
  have hA : 0 < A := Real.rpow_pos_of_pos hX0 _
  have hC' : 2 ≤ C := hC
  have hlower : A ≤ Real.sqrt (X : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hX.le (by linarith)
  have hupper : Real.sqrt (X : ℝ) < B := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_lt_rpow_of_exponent_lt hX (by linarith)
  have hfloor : ⌊A⌋₊ ≤ X.sqrt := by
    simpa only [Real.nat_floor_real_sqrt_eq_nat_sqrt] using Nat.floor_mono hlower
  have hgap : A * (C * C) < B := by
    dsimp [A,B,C]
    rw [← Real.rpow_add hX0, ← Real.rpow_add hX0]
    apply Real.rpow_lt_rpow_of_exponent_lt hX
    linarith
  have hk : 2 * Real.log X ≤ (k : ℝ) := Nat.le_ceil _
  have hlog2 : (1:ℝ)/2 ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hdyadic : X ≤ 2^k := by
    have hreal : (X : ℝ) ≤ (2 : ℝ)^k := by
      apply (Real.log_le_log_iff hX0 (pow_pos (by norm_num) _)).mp
      rw [Real.log_pow]
      have h := mul_le_mul hk hlog2 (by norm_num) (Nat.cast_nonneg k)
      linarith
    exact_mod_cast hreal
  refine ⟨Nat.sqrt_pos.mpr (by exact_mod_cast hX0), hfloor,
    Nat.lt_ceil.mpr (Real.nat_sqrt_le_real_sqrt.trans_lt hupper), ?_,
    hfloor.trans ((Nat.sqrt_le_self _).trans hdyadic)⟩
  rw [max_eq_left hJ]
  apply Nat.lt_ceil.mpr
  rw [Nat.cast_mul]
  have hround : (⌈C⌉₊ : ℝ) ≤ C * C := by
    have near := Nat.ceil_lt_add_one (by linarith : 0 ≤ C)
    nlinarith [sq_nonneg (C-2)]
  exact (mul_le_mul (Nat.floor_le hA.le) hround (Nat.cast_nonneg _) hA.le).trans_lt hgap

/-- All five numerical hypotheses in `fiber_outside_real_windows` eventually
hold, with the dyadic depth chosen as the ceiling of twice the logarithm. -/
theorem eventually_divisor_cutoff_order (ε : ℕ → ℝ) : ∀ᶠ X : ℕ in atTop,
    let η := max (ε X) (1 / Real.log (Real.log (X : ℝ)))
    let A := (X : ℝ) ^ ((1:ℝ)/2 - 10 * η)
    let B := (X : ℝ) ^ ((1:ℝ)/2 + 10 * η)
    let C := (X : ℝ) ^ (2 * η)
    let J := Real.log X
    let k := ⌈2 * J⌉₊
    0 < X.sqrt ∧ ⌊A⌋₊ ≤ X.sqrt ∧ X.sqrt < ⌈B⌉₊ ∧
      ⌊A⌋₊ * ⌈max C J⌉₊ < ⌈B⌉₊ ∧ ⌊A⌋₊ ≤ 2 ^ k := by
  filter_upwards [eventually_half_eta_dominates ε 2, eventually_gt_atTop (1 : ℕ)] with X h hX
  dsimp only at h ⊢
  let η := max (ε X) (1 / Real.log (Real.log (X : ℝ)))
  obtain ⟨hx, hlog, hη, hwindow, htwo⟩ := h
  have hη' : 0 < η := by
    apply lt_of_le_of_ne hη
    rintro heq
    change 0 = η at heq
    change 2 ≤ (X : ℝ) ^ (η / 2) at htwo
    rw [← heq] at htwo
    norm_num at htwo
  have hmono : (X : ℝ) ^ (η/2) ≤ (X : ℝ) ^ (2 * η) :=
    Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  exact divisor_cutoff_order (by exact_mod_cast hX) hη' (htwo.trans hmono)
    ((show Real.log X ≤ 8 * Real.log X by linarith).trans (hwindow.trans hmono))

end Erdos955.PPT

end

section

namespace Erdos955.PPT
open Filter

/-- The rounded coefficient in the fiber count is uniformly bounded by the given
real power. The two terms correspond to the divisors below the gap and those above. -/
theorem window_coefficient_bound {x s : ℕ} {η : ℝ} (hx : 1 ≤ (x : ℝ))
    (ht : 1 ≤ Real.log (x : ℝ)) (hη : 0 ≤ η)
    (hlog : 8 * Real.log x ≤ (x : ℝ) ^ (η / 2)) (hs : (s : ℝ) ≤ (x : ℝ) ^ (4*η)) :
    let A := (x : ℝ) ^ ((1/2 : ℝ) - 10*η)
    let B := (x : ℝ) ^ ((1/2 : ℝ) + 10*η)
    let C := (x : ℝ) ^ (2*η)
    let J := Real.log (x : ℝ)
    let k := ⌈2*J⌉₊
    s * (⌊A⌋₊ + (x * ⌊C⌋₊ / ⌈B⌉₊ * ⌈max C J⌉₊) * (k+1)) ≤
      ⌊2 * (x : ℝ) ^ ((1/2 : ℝ) - (3/2 : ℝ)*η)⌋₊ := by
  let X := (x : ℝ)
  let P := fun a : ℝ => X ^ a
  let A := P (1/2 - 10*η)
  let B := P (1/2 + 10*η)
  let C := P (2*η)
  let J := Real.log X
  let k := ⌈2*J⌉₊
  let q := x * ⌊C⌋₊ / ⌈B⌉₊
  let Z := P (1/2 - (3/2)*η)
  have hX : 0 < X := zero_lt_one.trans_le hx
  have pos (b : ℝ) : 0 < P b := Real.rpow_pos_of_pos hX _
  have add (a b : ℝ) : P a * P b = P (a+b) := (Real.rpow_add hX ..).symm
  have sub (a b : ℝ) : P a / P b = P (a-b) := (Real.rpow_sub hX ..).symm
  have mono {a b : ℝ} (h : a ≤ b) : P a ≤ P b := Real.rpow_le_rpow_of_exponent_le hx h
  have hC1 : 1 ≤ C := Real.one_le_rpow hx (by linarith)
  have hJC : J ≤ C := (by linarith [show 1 ≤ J from ht] : J ≤ 8*J).trans (hlog.trans (mono (by linarith)))
  have hT : ((⌈max C J⌉₊ : ℕ) : ℝ) ≤ 2*C := by
    rw [max_eq_left hJC]
    exact (Nat.ceil_lt_add_one (pos _).le).le.trans (by linarith)
  have hkj : ((k+1 : ℕ) : ℝ) ≤ 4 * J := by
    rw [Nat.cast_add_one]
    have hc := Nat.ceil_lt_add_one (show 0 ≤ 2*J by linarith [show 1 ≤ J from ht])
    change (⌈2*J⌉₊ : ℝ) + 1 ≤ 4 * J
    linarith [show 1 ≤ J from ht]
  have hraw : (q : ℝ) * (⌈B⌉₊ : ℕ) ≤ X * (⌊C⌋₊ : ℕ) := by
    dsimp only [q, X]
    exact_mod_cast Nat.div_mul_le_self (x * ⌊C⌋₊) ⌈B⌉₊
  have hq : (q : ℝ) ≤ X*C/B := by
    apply (le_div_iff₀ (pos _)).mpr
    exact ((mul_le_mul_of_nonneg_left (Nat.le_ceil B) (Nat.cast_nonneg q)).trans hraw).trans
      (mul_le_mul_of_nonneg_left (Nat.floor_le (pos _).le) hX.le)
  have htc : ((⌈max C J⌉₊ : ℕ) : ℝ) * (k+1 : ℕ) ≤ C * P (η/2) := by
    calc _ ≤ (2*C)*(4*J) := mul_le_mul hT hkj (Nat.cast_nonneg _) (by exact mul_nonneg (by norm_num) (pos _).le)
         _ = C*(8*J) := by ring
         _ ≤ _ := mul_le_mul_of_nonneg_left hlog (pos _).le
  have hA : P (4*η) * A ≤ Z := by
    dsimp only [A, Z]
    rw [add]
    apply mono
    linarith
  have hprod : P (4*η) * ((X*C/B) * (C * P (η/2))) = Z := by
    have hxone : X = P 1 := (Real.rpow_one X).symm
    dsimp only [C, B, Z]
    rw [hxone, add, sub, add, add, add]
    congr 1
    ring
  have hqterm : P (4*η) * ((q : ℝ) * (((⌈max C J⌉₊ : ℕ) : ℝ) * (k+1 : ℕ))) ≤ Z := by
    rw [← hprod]
    apply mul_le_mul_of_nonneg_left _ (pos _).le
    exact mul_le_mul hq htc (by positivity) (div_nonneg (mul_nonneg hX.le (pos _).le) (pos _).le)
  apply Nat.le_floor
  change ((s * (⌊A⌋₊ + q * ⌈max C J⌉₊ * (k+1)) : ℕ) : ℝ) ≤ 2 * Z
  push_cast
  calc (s : ℝ) * ((⌊A⌋₊ : ℝ) + (q : ℝ) * (⌈max C J⌉₊ : ℝ) * ((k : ℝ)+1))
       ≤ P (4*η) * (A + (q : ℝ) * (⌈max C J⌉₊ : ℝ) * ((k : ℝ)+1)) :=
         mul_le_mul hs (add_le_add_left (Nat.floor_le (pos _).le) _) (by positivity) (pos _).le
       _ ≤ _ := by
          rw [mul_add, mul_assoc (q : ℝ)]
          rw [Nat.cast_add_one] at hqterm
          linarith only [hA, hqterm]

/-- The common integer budget covers every small fiber, while multiplying it
by an admissible target-set size gives at most δx. -/
theorem eventually_real_window_budget (ε : ℕ → ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ x : ℕ in atTop,
    let η := max (ε x) (1 / Real.log (Real.log (x : ℝ)))
    let A := (x : ℝ) ^ ((1/2 : ℝ) - 10*η)
    let B := (x : ℝ) ^ ((1/2 : ℝ) + 10*η)
    let C := (x : ℝ) ^ (2*η)
    let J := Real.log (x : ℝ)
    let k := ⌈2*J⌉₊
    let K := ⌊2 * (x : ℝ) ^ ((1/2 : ℝ) - (3/2 : ℝ)*η)⌋₊
    (x : ℝ) ^ ((1/2 : ℝ) + ε x) * K ≤ δ*x ∧
    ∀ s : ℕ, (s : ℝ) ≤ (x : ℝ) ^ (4*η) →
      s * (⌊A⌋₊ + (x * ⌊C⌋₊ / ⌈B⌉₊ * ⌈max C J⌉₊) * (k+1)) ≤ K := by
  filter_upwards [eventually_half_eta_dominates ε (2/δ)] with x h
  obtain ⟨hx, ht, hη, hlog, hδsave⟩ := h
  let X := (x : ℝ)
  let η := max (ε x) (1 / Real.log (Real.log (x : ℝ)))
  let P := fun b : ℝ => X^b
  have hX : 0 < X := zero_lt_one.trans_le hx
  have pos (b : ℝ) : 0 < P b := Real.rpow_pos_of_pos hX _
  constructor
  · have hsum : (1/2 + ε x) + (1/2 - (3/2)*η) ≤ 1 - η/2 := by
      linarith [show ε x ≤ η from le_max_left ..]
    have h2 : 2 ≤ δ * P (η/2) := by
      simpa only [mul_comm δ] using (div_le_iff₀ hδ).mp hδsave
    have hfin : 2 * (X / P (η/2)) ≤ δ * X := by
      rw [mul_div_assoc', div_le_iff₀ (pos _)]
      calc 2 * X ≤ (δ * P (η/2)) * X := mul_le_mul_of_nonneg_right h2 hX.le
           _ = _ := by ring
    calc P (1/2 + ε x) * (⌊2 * P (1/2 - (3/2)*η)⌋₊ : ℝ)
         ≤ P (1/2 + ε x) * (2 * P (1/2 - (3/2)*η)) :=
           mul_le_mul_of_nonneg_left (Nat.floor_le (mul_nonneg (by norm_num) (pos _).le)) (pos _).le
         _ = 2 * P ((1/2 + ε x) + (1/2 - (3/2)*η)) := by dsimp [P]; rw [Real.rpow_add hX (1/2 + ε x) (1/2 - (3/2)*η)]; ring
         _ ≤ 2 * P (1 - η/2) := mul_le_mul_of_nonneg_left
           (Real.rpow_le_rpow_of_exponent_le hx hsum) (by norm_num)
         _ = 2 * (X / P (η/2)) := by dsimp [P]; rw [Real.rpow_sub hX, Real.rpow_one]
         _ ≤ _ := hfin
  · exact fun s hs => window_coefficient_bound hx ht hη hlog hs

end Erdos955.PPT

end

section

theorem Complete955.uniform_fiber : OMA.R_Erdos955_erdos_955_variants_pollack_pomerance_thompson_bound_R1_H1_R1.H3 := by
  classical
  intro ε _ δ hδ
  filter_upwards [Erdos955.PPT.eventually_divisor_card_linear_and_square,
    Erdos955.PPT.eventually_divisor_cutoff_order ε,
    Erdos955.PPT.eventually_real_window_budget ε hδ,
    Filter.eventually_ge_atTop (1 : ℕ)] with x hdiv hcut hbudget hx
  let η := max (ε x) (1 / Real.log (Real.log (x : ℝ)))
  have hdr := Erdos955.PPT.lift_exponent_both x hx η (le_max_right ..) hdiv
  obtain ⟨hr,hl,hu,hgap,hdyadic⟩ := hcut
  obtain ⟨hsize,hcoef⟩ := hbudget
  refine ⟨_, hsize, ?_⟩
  intro a ha
  exact Erdos955.PPT.fiber_uniform_K ha hr hl hu hgap hdyadic hdr.1 hdr.2 hcoef

end

section

-- Step Erdos955.erdos_955.variants.pollack_pomerance_thompson_bound.R1.H2
-- Credit: @caa1982

open Finset

private lemma SigmaBound_sum_inv_le_one_add_log (n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / (k : ℝ) ≤ 1 + Real.log (n : ℝ) := by
  induction n with
  | zero => omega
  | succ m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · have hset : Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
        ext x
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      have hnotmem : m + 1 ∉ Finset.Icc 1 m := by simp
      rw [hset, Finset.sum_insert hnotmem]
      have ihm := ih hm
      have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
      have hm1R : (0 : ℝ) < (m : ℝ) + 1 := by linarith
      have hlog : Real.log ((m : ℝ) / ((m : ℝ) + 1)) ≤ (m : ℝ) / ((m : ℝ) + 1) - 1 :=
        Real.log_le_sub_one_of_pos (div_pos hmR hm1R)
      rw [Real.log_div hmR.ne' hm1R.ne'] at hlog
      have hstep : 1 / ((m : ℝ) + 1) ≤ Real.log ((m : ℝ) + 1) - Real.log (m : ℝ) := by
        have heq : (m : ℝ) / ((m : ℝ) + 1) - 1 = -(1 / ((m : ℝ) + 1)) := by
          field_simp
          ring
        linarith
      push_cast
      linarith

theorem Complete955.sigma_bound : OMA.R_Erdos955_erdos_955_variants_pollack_pomerance_thompson_bound_R1.H2 := by
  intro n hn
  have hn0 : n ≠ 0 := by omega
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hsig : (ArithmeticFunction.sigma 1 n : ℝ) = (n : ℝ) * ∑ d ∈ n.divisors, (1 : ℝ) / (d : ℝ) := by
    rw [ArithmeticFunction.sigma_one_apply, Nat.cast_sum, Finset.mul_sum]
    refine Finset.sum_bij (fun d _ => n / d) ?_ ?_ ?_ ?_
    · intro d hd
      exact Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors hd), hn0⟩
    · intro d₁ hd₁ d₂ hd₂ heq
      have h1 := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd₁)
      have h2 := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd₂)
      have hpos : 0 < n / d₁ := Nat.div_pos (Nat.le_of_dvd hn (Nat.dvd_of_mem_divisors hd₁))
        (Nat.pos_of_mem_divisors hd₁)
      have : d₁ * (n / d₁) = d₂ * (n / d₁) := by rw [h1, heq, h2]
      exact Nat.eq_of_mul_eq_mul_right hpos this
    · intro d hd
      refine ⟨n / d, Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors hd), hn0⟩, ?_⟩
      exact Nat.div_div_self (Nat.dvd_of_mem_divisors hd) hn0
    · intro d hd
      have hdvd : d ∣ n := Nat.dvd_of_mem_divisors hd
      have hdiv_pos : (0 : ℝ) < ((n / d : ℕ) : ℝ) := by
        exact_mod_cast Nat.div_pos (Nat.le_of_dvd hn hdvd) (Nat.pos_of_mem_divisors hd)
      have hmul : (d : ℝ) * ((n / d : ℕ) : ℝ) = (n : ℝ) := by
        exact_mod_cast Nat.mul_div_cancel' hdvd
      field_simp [hdiv_pos.ne']
      linarith
  rw [hsig]
  have hsub : n.divisors ⊆ Finset.Icc 1 n := by
    intro d hd
    exact Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd, Nat.le_of_dvd hn (Nat.dvd_of_mem_divisors hd)⟩
  have hsum_le : ∑ d ∈ n.divisors, (1 : ℝ) / (d : ℝ) ≤ ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / (k : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
  exact mul_le_mul_of_nonneg_left (hsum_le.trans (SigmaBound_sum_inv_le_one_add_log n hn)) hnR.le

end

/-- Pollack, Pomerance and Thompson, *Divisor-sum fibers* (2018). We combine
the reductions of the uniform finite-set theorem with the growth of `σ`.
The outer reduction is @ivillar’s #6331. The divisor-sum bound is @caa1982’s
#7369. The exceptional-set reduction is #9822. -/
theorem OMA.solution : type_of% @Erdos955.erdos_955.variants.pollack_pomerance_thompson_bound :=
  OMA.R_Erdos955_erdos_955_variants_pollack_pomerance_thompson_bound_R1.main
    (OMA.R_Erdos955_erdos_955_variants_pollack_pomerance_thompson_bound_R1_H1_R1.main
      (Erdos955.Window.divisor_window_of_prime_counting Erdos955.PPT.eventual_prime_count_from_primorial)
      Erdos955.PPT.elementary_endpoint Complete955.uniform_fiber)
    Complete955.sigma_bound
