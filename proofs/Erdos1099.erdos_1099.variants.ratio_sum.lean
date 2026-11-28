import FormalConjectures.ErdosProblems.«1099»

/-! The construction and relative-gap estimates are adapted from the Apache-2.0
formalization of Michael Vose’s construction in plby/lean-proofs, commit
8822f7ddef30fadbd92e1c6ab4ed897af356af5e, src/latest/ErdosProblems/Erdos1099.
The final argument bounds the excess over the telescoping logarithm. -/
-- Credit: @marcusbuffett
-- Source copyright © 2026 OpenAI. Licensed under Apache 2.0.
section
/-
# Erdős Problem 1099: definitions and filter-level reduction

This file contains the source-faithful statistic and the elementary passage
from a cofinal bounded subsequence to the literal real-valued liminf.
-/

open Filter Finset
open scoped BigOperators

namespace Vose1099

noncomputable section

/-- The increasing enumeration of the positive divisors of `n`. -/
def orderedDivisor (n : ℕ) : Fin n.divisors.card ↪o ℕ :=
  n.divisors.orderEmbOfFin rfl

lemma orderedDivisor_mem (n : ℕ) (i : Fin n.divisors.card) :
    orderedDivisor n i ∈ n.divisors :=
  Finset.orderEmbOfFin_mem n.divisors rfl i

lemma orderedDivisor_pos (n : ℕ) (i : Fin n.divisors.card) :
    0 < orderedDivisor n i :=
  Nat.pos_of_mem_divisors (orderedDivisor_mem n i)

/-- The power energy of consecutive relative divisor gaps from Problem 1099. -/
def hAlpha (α : ℝ) (n : ℕ) : ℝ :=
  ∑ i : Fin (n.divisors.card - 1),
    Real.rpow
      (((orderedDivisor n ⟨i.1 + 1, by omega⟩ : ℕ) : ℝ) /
          ((orderedDivisor n ⟨i.1, by omega⟩ : ℕ) : ℝ) - 1)
      α

end

end Vose1099

end

section
/-
# The explicit integers used for Erdős Problem 1099

This file contains only the elementary arithmetic part of the construction.
For `k : ℕ`, put

* `triangular k = 1 + ⋯ + k`,
* `generator i = 2 ^ i + 1`,
* `voseNumber k = 2 ^ triangular k * ∏ i ∈ Icc 1 k, generator i`.

If `E ⊆ Icc 1 r` and `triangular r ≤ t ≤ triangular k`, the natural
number

`2 ^ (t - ∑ i ∈ E, i) * ∏ i ∈ E, (2 ^ i + 1)`

is visibly a divisor of `voseNumber k`.  Its logarithm is

`t * log 2 + ∑ i ∈ E, log (1 + (1 / 2) ^ i)`.

None of the divisibility arguments uses coprimality of the generators.
-/

open scoped BigOperators Topology
open Filter Finset

namespace Vose1099

noncomputable section

/-- The triangular number `1 + ⋯ + k`.

The finite-sum definition is definitionally aligned with the index set used
by the generators. -/
def triangular (k : ℕ) : ℕ := ∑ i ∈ Finset.Icc 1 k, i

/-- The `i`-th elementary odd generator in the explicit construction. -/
def generator (i : ℕ) : ℕ := 2 ^ i + 1

/-- Product of the generators with indices from `1` through `k`. -/
def generatorProduct (k : ℕ) : ℕ :=
  ∏ i ∈ Finset.Icc 1 k, generator i

/-- The explicit sequence of integers used in the construction. -/
def voseNumber (k : ℕ) : ℕ :=
  2 ^ triangular k * generatorProduct k

/-- Sum of the integer indices in a selected finite set. -/
def indexSum (E : Finset ℕ) : ℕ :=
  ∑ i ∈ E, i

/-- Product of the generators whose indices are selected by `E`. -/
def selectedProduct (E : Finset ℕ) : ℕ :=
  ∏ i ∈ E, generator i

/-- A selected divisor at integral logarithmic level `t`. -/
def selectedDivisor (t : ℕ) (E : Finset ℕ) : ℕ :=
  2 ^ (t - indexSum E) * selectedProduct E

/-- The small natural-log correction contributed by `generator i`. -/
def logDigit (i : ℕ) : ℝ :=
  Real.log (1 + (1 / 2 : ℝ) ^ i)

@[simp] lemma triangular_zero : triangular 0 = 0 := by
  simp [triangular]

lemma triangular_eq_sum_Icc (k : ℕ) :
    triangular k = ∑ i ∈ Finset.Icc 1 k, i := by
  rfl

lemma indexSum_le_triangular {E : Finset ℕ} {k : ℕ}
    (hE : E ⊆ Finset.Icc 1 k) : indexSum E ≤ triangular k := by
  rw [triangular_eq_sum_Icc, indexSum]
  exact Finset.sum_le_sum_of_subset_of_nonneg hE (fun _ _ _ ↦ Nat.zero_le _)

lemma generator_pos (i : ℕ) : 0 < generator i := by
  simp [generator]

lemma generator_ne_zero (i : ℕ) : generator i ≠ 0 :=
  Nat.ne_of_gt (generator_pos i)

lemma generatorProduct_pos (k : ℕ) : 0 < generatorProduct k := by
  simp [generatorProduct, generator_pos]

lemma voseNumber_pos (k : ℕ) : 0 < voseNumber k := by
  simp [voseNumber, generatorProduct, generator_pos]

lemma voseNumber_ne_zero (k : ℕ) : voseNumber k ≠ 0 :=
  Nat.ne_of_gt (voseNumber_pos k)

lemma pow_two_le_voseNumber (k : ℕ) :
    2 ^ triangular k ≤ voseNumber k := by
  rw [voseNumber]
  exact Nat.le_mul_of_pos_right (2 ^ triangular k) (generatorProduct_pos k)

lemma selectedProduct_dvd_generatorProduct {E : Finset ℕ} {k : ℕ}
    (hE : E ⊆ Finset.Icc 1 k) : selectedProduct E ∣ generatorProduct k := by
  classical
  rw [selectedProduct, generatorProduct]
  exact Finset.prod_dvd_prod_of_subset E (Finset.Icc 1 k) generator hE

/-- The selected number is an actual divisor of the explicit construction.
The more flexible hypotheses through `r` are the ones used by the logarithmic
shell construction. -/
lemma selectedDivisor_dvd {k r t : ℕ} {E : Finset ℕ}
    (hE : E ⊆ Finset.Icc 1 r) (hrk : r ≤ k)
    (hrt : triangular r ≤ t) (htk : t ≤ triangular k) :
    selectedDivisor t E ∣ voseNumber k := by
  have hEk : E ⊆ Finset.Icc 1 k :=
    hE.trans (Finset.Icc_subset_Icc_right hrk)
  have hsum_le_t : indexSum E ≤ t :=
    (indexSum_le_triangular hE).trans hrt
  have hpow : 2 ^ (t - indexSum E) ∣ 2 ^ triangular k := by
    exact pow_dvd_pow 2 (by omega)
  exact Nat.mul_dvd_mul hpow (selectedProduct_dvd_generatorProduct hEk)

lemma selectedDivisor_pos (t : ℕ) (E : Finset ℕ) :
    0 < selectedDivisor t E := by
  simp [selectedDivisor, selectedProduct, generator_pos]

lemma selectedProduct_pos (E : Finset ℕ) : 0 < selectedProduct E := by
  simp [selectedProduct, generator_pos]

lemma selectedProduct_ne_zero (E : Finset ℕ) : selectedProduct E ≠ 0 :=
  Nat.ne_of_gt (selectedProduct_pos E)

lemma generator_cast_eq (i : ℕ) :
    (generator i : ℝ) = (2 : ℝ) ^ i * (1 + (1 / 2 : ℝ) ^ i) := by
  rw [generator, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
  have h2 : (2 : ℝ) ≠ 0 := by norm_num
  rw [mul_add, mul_one]
  have hcancel : (2 : ℝ) ^ i * (1 / 2 : ℝ) ^ i = 1 := by
    rw [← mul_pow]
    norm_num
  rw [hcancel, add_comm]

lemma log_generator (i : ℕ) :
    Real.log (generator i : ℝ) = (i : ℝ) * Real.log 2 + logDigit i := by
  rw [generator_cast_eq, Real.log_mul (by positivity) (by positivity)]
  rw [Real.log_pow]
  rfl

/-- Natural-log formula for every selected divisor. -/
lemma log_selectedDivisor {t : ℕ} {E : Finset ℕ}
    (hEt : indexSum E ≤ t) :
    Real.log (selectedDivisor t E : ℝ) =
      (t : ℝ) * Real.log 2 + ∑ i ∈ E, logDigit i := by
  classical
  rw [selectedDivisor, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [Real.log_mul (by positivity) (by exact_mod_cast selectedProduct_ne_zero E), Real.log_pow]
  rw [show Real.log (2 : ℝ) = Real.log 2 by rfl]
  rw [selectedProduct, Nat.cast_prod,
    Real.log_prod (fun i hi ↦ by exact_mod_cast generator_ne_zero i)]
  simp_rw [log_generator]
  simp only [Finset.sum_add_distrib]
  rw [← Finset.sum_mul]
  have hcast : (∑ i ∈ E, (i : ℝ)) = (indexSum E : ℝ) := by
    simp [indexSum]
  rw [hcast]
  rw [Nat.cast_sub hEt]
  ring

lemma triangular_mono : Monotone triangular := by
  intro a b hab
  rw [triangular_eq_sum_Icc, triangular_eq_sum_Icc]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.Icc_subset_Icc_right hab) (fun _ _ _ ↦ Nat.zero_le _)

lemma triangular_succ (k : ℕ) : triangular (k + 1) = triangular k + (k + 1) := by
  rw [triangular, triangular, Finset.sum_Icc_succ_top (by omega)]

lemma triangular_ge_id (k : ℕ) : k ≤ triangular k := by
  cases k with
  | zero => simp
  | succ k =>
      rw [triangular]
      apply Finset.single_le_sum (fun i _ ↦ Nat.zero_le i)
      simp

lemma triangular_tendsto_atTop : Tendsto triangular atTop atTop := by
  exact tendsto_atTop_mono' atTop
    (Filter.Eventually.of_forall triangular_ge_id) tendsto_id

lemma pow_two_triangular_tendsto_atTop :
    Tendsto (fun k : ℕ ↦ 2 ^ triangular k) atTop atTop := by
  exact (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < (2 : ℕ))).comp
    triangular_tendsto_atTop

lemma voseNumber_tendsto_atTop : Tendsto voseNumber atTop atTop := by
  exact tendsto_atTop_mono' atTop
    (Filter.Eventually.of_forall pow_two_le_voseNumber)
    pow_two_triangular_tendsto_atTop

end

end Vose1099

end

section
/-
# The finite logarithmic subset net for Erdős Problem 1099

This file deliberately uses only finite sums.  The terminal error at depth `r`
is `2⁻ʳ`; no infinite product or infinite tail is needed.
-/

open Finset Set
open scoped BigOperators

namespace Vose1099.Net

noncomputable section

/-- The `i`-th dyadic scale, written without an integer exponent. -/
def dyadic (i : ℕ) : ℝ := (1 / 2 : ℝ) ^ i

/-- The natural-logarithmic digit attached to `2^i + 1`. -/
def delta (i : ℕ) : ℝ := Real.log (1 + dyadic i)

@[simp] lemma dyadic_zero : dyadic 0 = 1 := by simp [dyadic]

lemma dyadic_pos (i : ℕ) : 0 < dyadic i := by
  exact pow_pos (by norm_num) i

lemma dyadic_nonneg (i : ℕ) : 0 ≤ dyadic i := (dyadic_pos i).le

lemma one_add_dyadic_pos (i : ℕ) : 0 < 1 + dyadic i := by
  linarith [dyadic_pos i]

lemma delta_nonneg (i : ℕ) : 0 ≤ delta i := by
  rw [delta, Real.log_nonneg_iff (one_add_dyadic_pos i)]
  linarith [dyadic_nonneg i]

lemma delta_le_dyadic (i : ℕ) : delta i ≤ dyadic i := by
  simpa [delta] using Real.log_le_sub_one_of_pos (one_add_dyadic_pos i)

lemma delta_zero : delta 0 = Real.log 2 := by norm_num [delta, dyadic]

/-- The elementary first-order part of the expansion of a finite product. -/
lemma one_add_sum_le_prod_one_add {ι : Type*}
    (s : Finset ι) (f : ι → ℝ) (hf : ∀ i ∈ s, 0 ≤ f i) :
    1 + ∑ i ∈ s, f i ≤ ∏ i ∈ s, (1 + f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha]
      have hfa : 0 ≤ f a := hf a (by simp)
      have hsum : 0 ≤ ∑ i ∈ s, f i :=
        Finset.sum_nonneg fun i hi ↦ hf i (by simp [hi])
      have hone : 0 ≤ 1 + f a := by linarith
      calc
        1 + (f a + ∑ i ∈ s, f i)
            ≤ (1 + f a) * (1 + ∑ i ∈ s, f i) := by nlinarith
        _ ≤ (1 + f a) * ∏ i ∈ s, (1 + f i) := by
          exact mul_le_mul_of_nonneg_left (ih fun i hi ↦ hf i (by simp [hi])) hone

/-- A finite geometric tail identity.  It is the source of the terminal
`dyadic r` error in the net construction. -/
lemma sum_Icc_dyadic_add_dyadic (i n : ℕ) :
    (∑ j ∈ Finset.Icc (i + 1) (i + n), dyadic j) + dyadic (i + n) = dyadic i := by
  induction n with
  | zero => simp
  | succ n ih =>
      have htop : i + (n + 1) = (i + n) + 1 := by omega
      rw [htop, Finset.sum_Icc_succ_top (by omega)]
      have hdyadic :
          dyadic (i + n + 1) + dyadic (i + n + 1) = dyadic (i + n) := by
        simp only [dyadic, pow_succ]
        ring
      calc
        (∑ j ∈ Finset.Icc (i + 1) (i + n), dyadic j) +
              dyadic (i + n + 1) + dyadic (i + n + 1) =
            (∑ j ∈ Finset.Icc (i + 1) (i + n), dyadic j) +
              dyadic (i + n) := by rw [add_assoc, hdyadic]
        _ = dyadic i := ih

lemma sum_Icc_dyadic_add_dyadic' {i r : ℕ} (hir : i ≤ r) :
    (∑ j ∈ Finset.Icc (i + 1) r, dyadic j) + dyadic r = dyadic i := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hir
  exact sum_Icc_dyadic_add_dyadic i n

/-- The key finite digit inequality.  In paper notation this is
`δᵢ ≤ 2⁻ʳ + ∑_{i<j≤r} δⱼ`. -/
lemma delta_le_terminal_add_sum {i r : ℕ} (hir : i ≤ r) :
    delta i ≤ dyadic r + ∑ j ∈ Finset.Icc (i + 1) r, delta j := by
  let s := Finset.Icc (i + 1) r
  let P : ℝ := ∏ j ∈ s, (1 + dyadic j)
  have hP : 1 + ∑ j ∈ s, dyadic j ≤ P := by
    exact one_add_sum_le_prod_one_add s dyadic fun j _ ↦ dyadic_nonneg j
  have hsum : (∑ j ∈ s, dyadic j) + dyadic r = dyadic i := by
    simpa [s] using sum_Icc_dyadic_add_dyadic' hir
  have hPpos : 0 < P := by
    dsimp [P, s]
    exact Finset.prod_pos fun j _ ↦ one_add_dyadic_pos j
  have hmain : 1 + dyadic i ≤ Real.exp (dyadic r) * P := by
    have hexp : 1 + dyadic r ≤ Real.exp (dyadic r) := by
      simpa [add_comm] using Real.add_one_le_exp (dyadic r)
    have hleft : 0 ≤ 1 + dyadic r := by linarith [dyadic_nonneg r]
    have hright : 0 ≤ 1 + ∑ j ∈ s, dyadic j := by
      have hsnonneg : 0 ≤ ∑ j ∈ s, dyadic j :=
        Finset.sum_nonneg fun j _ ↦ dyadic_nonneg j
      linarith
    calc
      1 + dyadic i = (1 + dyadic r) + ∑ j ∈ s, dyadic j := by linarith
      _ ≤ (1 + dyadic r) * (1 + ∑ j ∈ s, dyadic j) := by
        have hsnonneg : 0 ≤ ∑ j ∈ s, dyadic j :=
          Finset.sum_nonneg fun j _ ↦ dyadic_nonneg j
        nlinarith [mul_nonneg (dyadic_nonneg r) hsnonneg]
      _ ≤ Real.exp (dyadic r) * P := by
        exact mul_le_mul hexp hP hright (Real.exp_pos _).le
  have hlog := Real.log_le_log (one_add_dyadic_pos i) hmain
  rw [Real.log_mul (Real.exp_ne_zero _) hPpos.ne', Real.log_exp] at hlog
  rw [Real.log_prod] at hlog
  · simpa [delta, s, add_comm] using hlog
  · intro j hj
    exact (one_add_dyadic_pos j).ne'

/- ## Concrete finite subset sums -/

/-- Internal interval version of the finite greedy construction. -/
lemma exists_finset_sum_net_aux (i n : ℕ) {x : ℝ}
    (hx0 : 0 ≤ x)
    (hx : x ≤ dyadic (i + n) + ∑ j ∈ Finset.Icc i (i + n), delta j) :
    ∃ S : Finset ℕ, S ⊆ Finset.Icc i (i + n) ∧
      0 ≤ x - ∑ j ∈ S, delta j ∧
      x - ∑ j ∈ S, delta j ≤ dyadic (i + n) := by
  induction n generalizing i x with
  | zero =>
      by_cases hsmall : x ≤ dyadic i
      · refine ⟨∅, by simp, by simpa, by simpa⟩
      · have hdi : delta i ≤ dyadic i := delta_le_dyadic i
        refine ⟨{i}, by simp, ?_, ?_⟩
        · simp only [Finset.sum_singleton]
          linarith
        · simpa using hx
  | succ n ih =>
      let r := i + (n + 1)
      let T := dyadic r + ∑ j ∈ Finset.Icc (i + 1) r, delta j
      have hir : i ≤ r := by simp [r]
      have hdi : delta i ≤ T := by
        simpa [T] using delta_le_terminal_add_sum hir
      have hsplit :
          (∑ j ∈ Finset.Icc i r, delta j) =
            delta i + ∑ j ∈ Finset.Icc (i + 1) r, delta j := by
        have hset : Finset.Icc i r = insert i (Finset.Icc (i + 1) r) := by
          ext j
          simp only [Finset.mem_Icc, Finset.mem_insert]
          omega
        rw [hset, Finset.sum_insert (by simp)]
      by_cases hsmall : x ≤ T
      · have hr : (i + 1) + n = r := by simp [r, Nat.add_assoc, Nat.add_comm n 1]
        obtain ⟨S, hSsub, hS0, hSg⟩ := ih (i := i + 1) (x := x) hx0 (by
          simpa [hr, T] using hsmall)
        refine ⟨S, ?_, hS0, ?_⟩
        · intro j hj
          have hj' := hSsub hj
          simp only [Finset.mem_Icc] at hj' ⊢
          omega
        · simpa [hr] using hSg
      · have hxsub0 : 0 ≤ x - delta i := by linarith
        have hxsubup : x - delta i ≤ T := by
          rw [hsplit] at hx
          dsimp [T]
          dsimp [r] at hx ⊢
          linarith
        have hr : (i + 1) + n = r := by simp [r, Nat.add_assoc, Nat.add_comm n 1]
        obtain ⟨S, hSsub, hS0, hSg⟩ := ih (i := i + 1) (x := x - delta i)
          hxsub0 (by simpa [hr, T] using hxsubup)
        have hiS : i ∉ S := by
          intro hi
          have := hSsub hi
          simp only [Finset.mem_Icc] at this
          omega
        refine ⟨insert i S, ?_, ?_, ?_⟩
        · intro j hj
          simp only [Finset.mem_insert] at hj
          rcases hj with rfl | hj
          · simp
          · have hj' := hSsub hj
            simp only [Finset.mem_Icc] at hj' ⊢
            omega
        · rw [Finset.sum_insert hiS]
          simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hS0
        · rw [Finset.sum_insert hiS]
          convert hSg using 1
          · ring
          · congr 1
            omega

/-- The concrete one-sided subset-sum net on `[0, log 2]`, with terminal
error `2⁻ʳ`. -/
lemma exists_subsetSum_below {r : ℕ} {x : ℝ}
    (hx0 : 0 ≤ x) (hx2 : x ≤ Real.log 2) :
    ∃ S : Finset ℕ, S ⊆ Finset.Icc 1 r ∧
      0 ≤ x - ∑ i ∈ S, delta i ∧
      x - ∑ i ∈ S, delta i ≤ dyadic r := by
  have hbudget : Real.log 2 ≤ dyadic r + ∑ j ∈ Finset.Icc 1 r, delta j := by
    simpa [delta_zero] using (delta_le_terminal_add_sum (i := 0) (r := r) (Nat.zero_le r))
  cases r with
  | zero =>
      refine ⟨∅, by simp, by simpa, ?_⟩
      simpa using hx2.trans hbudget
  | succ n =>
      have hb : x ≤ dyadic (1 + n) + ∑ j ∈ Finset.Icc 1 (1 + n), delta j := by
        simpa [Nat.add_comm] using hx2.trans hbudget
      simpa [Nat.add_comm] using exists_finset_sum_net_aux 1 n hx0 hb

/- ## Two elementary bounds used to locate the logarithmic shells -/

/-- Every finite partial digit sum is strictly below `1`. -/
lemma sum_delta_lt_one (r : ℕ) :
    (∑ i ∈ Finset.Icc 1 r, delta i) < 1 := by
  cases r with
  | zero => simp
  | succ n =>
      have hle : (∑ i ∈ Finset.Icc 1 (n + 1), delta i) ≤
          ∑ i ∈ Finset.Icc 1 (n + 1), dyadic i := by
        exact Finset.sum_le_sum fun i _ ↦ delta_le_dyadic i
      have hgeom := sum_Icc_dyadic_add_dyadic' (i := 0) (r := n + 1) (by omega)
      have hpos := dyadic_pos (n + 1)
      simp only [Nat.zero_add, dyadic_zero] at hgeom
      linarith

end

end Vose1099.Net

end

section
/-
# Finite gap-energy lemmas for Erdős Problem 1099

The estimates here are deliberately independent of divisors. They say that
an increasing finite partition whose gaps are at most `g` has `alpha`-energy
at most `g^(alpha-1)` times its total length, and that subdividing an interval
can only lower this energy when `alpha >= 1`.
-/

open Finset
open scoped BigOperators

namespace Vose1099

noncomputable section

/-- Additive `alpha`-energy of the consecutive gaps of a finite sequence. -/
def gapEnergy (alpha : ℝ) {m : ℕ} (x : Fin (m + 1) → ℝ) : ℝ :=
  ∑ i : Fin m, (x ⟨i.1 + 1, by omega⟩ - x ⟨i.1, by omega⟩) ^ alpha

/-- Consecutive differences telescope. -/
lemma sum_fin_consecutive_sub {m : ℕ} (x : Fin (m + 1) → ℝ) :
    (∑ i : Fin m, (x ⟨i.1 + 1, by omega⟩ - x ⟨i.1, by omega⟩)) =
      x ⟨m, by omega⟩ - x ⟨0, by omega⟩ := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Fin.sum_univ_succ]
      have htail := ih (fun j : Fin (m + 1) ↦ x j.succ)
      have htail' :
          (∑ i : Fin m,
            (x ⟨i.1 + 2, by omega⟩ - x ⟨i.1 + 1, by omega⟩)) =
            x ⟨m + 1, by omega⟩ - x ⟨1, by omega⟩ := by
        simpa only [Fin.succ_mk, Nat.add_assoc] using htail
      change (x ⟨1, by omega⟩ - x ⟨0, by omega⟩) +
          (∑ i : Fin m,
            (x ⟨i.1 + 2, by omega⟩ - x ⟨i.1 + 1, by omega⟩)) =
        x ⟨m + 1, by omega⟩ - x ⟨0, by omega⟩
      rw [htail']
      ring

/-- The standard mesh-times-length estimate for a finite partition. -/
lemma gapEnergy_le_mesh_mul_length {alpha : ℝ} (halpha : 1 ≤ alpha)
    {m : ℕ} (x : Fin (m + 1) → ℝ) (hx : Monotone x) {g : ℝ}
    (hmesh : ∀ i : Fin m,
      x ⟨i.1 + 1, by omega⟩ - x ⟨i.1, by omega⟩ ≤ g) :
    gapEnergy alpha x ≤ g ^ (alpha - 1) *
      (x ⟨m, by omega⟩ - x ⟨0, by omega⟩) := by
  unfold gapEnergy
  calc
    (∑ i : Fin m,
        (x ⟨i.1 + 1, by omega⟩ - x ⟨i.1, by omega⟩) ^ alpha)
        ≤ ∑ i : Fin m, g ^ (alpha - 1) *
            (x ⟨i.1 + 1, by omega⟩ - x ⟨i.1, by omega⟩) := by
          apply Finset.sum_le_sum
          intro i _
          let d := x ⟨i.1 + 1, by omega⟩ - x ⟨i.1, by omega⟩
          have hd : 0 ≤ d := sub_nonneg.mpr (hx (by simp))
          have hexp : 0 ≤ alpha - 1 := sub_nonneg.mpr halpha
          have hpow : d ^ (alpha - 1) ≤ g ^ (alpha - 1) :=
            Real.rpow_le_rpow hd (hmesh i) hexp
          have hfactor : d ^ alpha = d ^ (alpha - 1) * d := by
            calc
              d ^ alpha = d ^ ((alpha - 1) + 1) := by
                congr 1
                ring
              _ = d ^ (alpha - 1) * d := by
                rw [Real.rpow_add' hd (by linarith), Real.rpow_one]
          rw [hfactor]
          exact mul_le_mul_of_nonneg_right hpow hd
    _ = g ^ (alpha - 1) *
        (x ⟨m, by omega⟩ - x ⟨0, by omega⟩) := by
          rw [← Finset.mul_sum, sum_fin_consecutive_sub]

end

end Vose1099

end

section
/-
# Refinement of divisor-chain energy

The complete increasing list of divisors refines every increasing chain of
divisors from `1` to `n`.  This file proves that, for exponent at least one,
such a refinement can only decrease the relative-gap energy.

The chain is represented by a monotone map into the indices of the full
ordered divisor sequence.  Thus every entry is automatically a divisor.
Allowing repeated indices is useful when concatenating chains: repetitions
merely contribute a zero gap.
-/

open Finset
open scoped BigOperators

namespace Vose1099

noncomputable section

/-- Relative-gap energy of a chain selected from the ordered divisors of `n`. -/
def divisorChainEnergy (alpha : ℝ) (n : ℕ) {m : ℕ}
    (c : Fin (m + 1) → Fin n.divisors.card) : ℝ :=
  ∑ j : Fin m,
    Real.rpow
      (((orderedDivisor n (c ⟨j.1 + 1, by omega⟩) : ℕ) : ℝ) /
          ((orderedDivisor n (c ⟨j.1, by omega⟩) : ℕ) : ℝ) - 1)
      alpha

/-- Relative-gap energy of a finite sequence of positive integer values. -/
def valueChainEnergy (alpha : ℝ) {m : ℕ} (d : Fin (m + 1) → ℕ) : ℝ :=
  ∑ j : Fin m,
    Real.rpow
      (((d ⟨j.1 + 1, by omega⟩ : ℕ) : ℝ) /
          ((d ⟨j.1, by omega⟩ : ℕ) : ℝ) - 1)
      alpha

private def relativeGap (x : ℕ → ℝ) (i : ℕ) : ℝ :=
  x (i + 1) / x i - 1

private lemma relativeGap_nonneg_of_monotone (x : ℕ → ℝ)
    (hxpos : ∀ i, 0 < x i) (hxmono : Monotone x) (i : ℕ) :
    0 ≤ relativeGap x i := by
  rw [relativeGap, sub_nonneg, one_le_div (hxpos i)]
  exact hxmono (Nat.le_succ i)

private lemma two_relativeGaps_le {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : a ≤ b) (hbc : b ≤ c) :
    b / a - 1 + (c / b - 1) ≤ c / a - 1 := by
  have hba : 0 ≤ b / a - 1 := by
    rw [sub_nonneg, one_le_div ha]
    exact hab
  have hcb : 0 ≤ c / b - 1 := by
    rw [sub_nonneg, one_le_div hb]
    exact hbc
  have hmul : 0 ≤ (b / a - 1) * (c / b - 1) := mul_nonneg hba hcb
  have hratio : (b / a) * (c / b) = c / a := by
    field_simp
  rw [← hratio]
  nlinarith

/-- On an interval of a positive monotone sequence, the energy of all
successive relative gaps is bounded by the energy of the single endpoint
gap. -/
private lemma sum_Ico_relativeGap_rpow_le {alpha : ℝ} (halpha : 1 ≤ alpha)
    (x : ℕ → ℝ) (hxpos : ∀ i, 0 < x i) (hxmono : Monotone x)
    {p q : ℕ} (hpq : p ≤ q) :
    ∑ i ∈ Ico p q, Real.rpow (relativeGap x i) alpha ≤
      Real.rpow (x q / x p - 1) alpha := by
  induction q generalizing p with
  | zero =>
      have hp : p = 0 := Nat.eq_zero_of_le_zero hpq
      subst p
      simpa [hxpos 0 |>.ne'] using
        (Real.rpow_nonneg (show (0 : ℝ) ≤ 0 by rfl) alpha)
  | succ q ih =>
      by_cases hp : p = q + 1
      · subst p
        simpa [hxpos (q + 1) |>.ne'] using
          (Real.rpow_nonneg (show (0 : ℝ) ≤ 0 by rfl) alpha)
      · have hpq' : p ≤ q := by omega
        have hih := ih hpq'
        have hleft : 0 ≤ x q / x p - 1 := by
          rw [sub_nonneg, one_le_div (hxpos p)]
          exact hxmono hpq'
        have hright : 0 ≤ relativeGap x q :=
          relativeGap_nonneg_of_monotone x hxpos hxmono q
        have hadd :
            x q / x p - 1 + relativeGap x q ≤
              x (q + 1) / x p - 1 := by
          exact two_relativeGaps_le (hxpos p) (hxpos q) (hxmono hpq')
            (hxmono (Nat.le_succ q))
        calc
          (∑ i ∈ Ico p (q + 1), Real.rpow (relativeGap x i) alpha) =
              (∑ i ∈ Ico p q, Real.rpow (relativeGap x i) alpha) +
                Real.rpow (relativeGap x q) alpha := by
                  rw [sum_Ico_succ_top hpq']
          _ ≤ Real.rpow (x q / x p - 1) alpha +
                Real.rpow (relativeGap x q) alpha :=
              add_le_add hih le_rfl
          _ ≤ Real.rpow (x q / x p - 1 + relativeGap x q) alpha :=
              Real.add_rpow_le_rpow_add hleft hright halpha
          _ ≤ Real.rpow (x (q + 1) / x p - 1) alpha :=
              Real.rpow_le_rpow (add_nonneg hleft hright) hadd (by linarith)

private lemma sum_fin_consecutive_sub_refinement {m : ℕ} (x : Fin (m + 1) → ℝ) :
    (∑ i : Fin m, (x ⟨i.1 + 1, by omega⟩ - x ⟨i.1, by omega⟩)) =
      x ⟨m, by omega⟩ - x ⟨0, by omega⟩ := by
  let y : ℕ → ℝ := fun i ↦
    x ⟨min i m, Nat.lt_succ_of_le (min_le_right i m)⟩
  calc
    (∑ i : Fin m, (x ⟨i.1 + 1, by omega⟩ - x ⟨i.1, by omega⟩)) =
        ∑ i : Fin m, (y (i.1 + 1) - y i.1) := by
          apply sum_congr rfl
          intro i _
          have hi : i.1 ≤ m := i.isLt.le
          have his : i.1 + 1 ≤ m := i.isLt
          simp [y, hi, his]
    _ = ∑ i ∈ range m, (y (i + 1) - y i) :=
      Fin.sum_univ_eq_sum_range (fun i ↦ y (i + 1) - y i) m
    _ = y m - y 0 := sum_range_sub y m
    _ = x ⟨m, by omega⟩ - x ⟨0, by omega⟩ := by simp [y]

/-- Consecutive index intervals in an endpoint-normalized monotone chain
partition the full index interval. -/
private lemma sum_chain_Ico {m : ℕ} (c : Fin (m + 1) → ℕ)
    (hc : Monotone c) (hc0 : c ⟨0, by omega⟩ = 0) (f : ℕ → ℝ) :
    (∑ j : Fin m, ∑ i ∈ Ico (c ⟨j.1, by omega⟩) (c ⟨j.1 + 1, by omega⟩), f i) =
      ∑ i ∈ range (c ⟨m, by omega⟩), f i := by
  let s : Fin (m + 1) → ℝ := fun j ↦ ∑ i ∈ range (c j), f i
  calc
    (∑ j : Fin m, ∑ i ∈ Ico (c ⟨j.1, by omega⟩) (c ⟨j.1 + 1, by omega⟩), f i) =
        ∑ j : Fin m, (s ⟨j.1 + 1, by omega⟩ - s ⟨j.1, by omega⟩) := by
          apply sum_congr rfl
          intro j _
          exact sum_Ico_eq_sub f (hc (by simp))
    _ = s ⟨m, by omega⟩ - s ⟨0, by omega⟩ :=
      sum_fin_consecutive_sub_refinement s
    _ = ∑ i ∈ range (c ⟨m, by omega⟩), f i := by
      change (∑ i ∈ range (c ⟨m, by omega⟩), f i) -
          (∑ i ∈ range (c ⟨0, by omega⟩), f i) = _
      rw [hc0]
      simp

private def extendedDivisorValue (n : ℕ) (hn : n ≠ 0) (i : ℕ) : ℝ :=
  ((orderedDivisor n
      ⟨min i (n.divisors.card - 1), by
        have hcard : 0 < n.divisors.card :=
          Finset.card_pos.mpr (Nat.nonempty_divisors.mpr hn)
        omega⟩ : ℕ) : ℝ)

private lemma extendedDivisorValue_eq (n : ℕ) (hn : n ≠ 0) {i : ℕ}
    (hi : i < n.divisors.card) :
    extendedDivisorValue n hn i = ((orderedDivisor n ⟨i, hi⟩ : ℕ) : ℝ) := by
  simp [extendedDivisorValue, Nat.min_eq_left (Nat.le_sub_one_of_lt hi)]

private lemma extendedDivisorValue_pos (n : ℕ) (hn : n ≠ 0) (i : ℕ) :
    0 < extendedDivisorValue n hn i := by
  unfold extendedDivisorValue
  exact_mod_cast orderedDivisor_pos n _

private lemma extendedDivisorValue_monotone (n : ℕ) (hn : n ≠ 0) :
    Monotone (extendedDivisorValue n hn) := by
  intro i j hij
  unfold extendedDivisorValue
  have hmin : min i (n.divisors.card - 1) ≤ min j (n.divisors.card - 1) :=
    min_le_min_right _ hij
  have hfin :
      (⟨min i (n.divisors.card - 1), by
          have hcard : 0 < n.divisors.card :=
            Finset.card_pos.mpr (Nat.nonempty_divisors.mpr hn)
          omega⟩ : Fin n.divisors.card) ≤
        ⟨min j (n.divisors.card - 1), by
          have hcard : 0 < n.divisors.card :=
            Finset.card_pos.mpr (Nat.nonempty_divisors.mpr hn)
          omega⟩ := hmin
  exact_mod_cast (orderedDivisor n).monotone hfin

private lemma hAlpha_eq_sum_range_extended (alpha : ℝ) (n : ℕ) (hn : n ≠ 0) :
    hAlpha alpha n =
      ∑ i ∈ range (n.divisors.card - 1),
        Real.rpow (relativeGap (extendedDivisorValue n hn) i) alpha := by
  calc
    hAlpha alpha n =
        ∑ i : Fin (n.divisors.card - 1),
          Real.rpow (relativeGap (extendedDivisorValue n hn) i.1) alpha := by
            unfold hAlpha
            apply sum_congr rfl
            intro i _
            simp only [relativeGap]
            rw [extendedDivisorValue_eq n hn (by omega),
              extendedDivisorValue_eq n hn (by omega)]
    _ = ∑ i ∈ range (n.divisors.card - 1),
          Real.rpow (relativeGap (extendedDivisorValue n hn) i) alpha :=
      Fin.sum_univ_eq_sum_range
        (fun i ↦ Real.rpow (relativeGap (extendedDivisorValue n hn) i) alpha)
        (n.divisors.card - 1)

/-- The full ordered divisor sequence has no greater relative-gap energy than
any strictly increasing chain of divisors from its first entry to its last.

The monotone map `c` selects the chain.  `hc0` and `hclast` say that its
endpoints are respectively `1` and `n`, expressed as indices in the complete
ordered divisor sequence. -/
theorem hAlpha_le_divisorChainEnergy {alpha : ℝ} (halpha : 1 ≤ alpha)
    {n m : ℕ} (hn : n ≠ 0)
    (c : Fin (m + 1) → Fin n.divisors.card) (hcmono : Monotone c)
    (hc0 : (c ⟨0, by omega⟩).1 = 0)
    (hclast : (c ⟨m, by omega⟩).1 = n.divisors.card - 1) :
    hAlpha alpha n ≤ divisorChainEnergy alpha n c := by
  let x : ℕ → ℝ := extendedDivisorValue n hn
  let cv : Fin (m + 1) → ℕ := fun j ↦ (c j).1
  have hcvmono : Monotone cv := fun _ _ hij ↦ by
    exact_mod_cast hcmono hij
  have hpartition :
      (∑ j : Fin m, ∑ i ∈ Ico (cv ⟨j.1, by omega⟩) (cv ⟨j.1 + 1, by omega⟩),
          Real.rpow (relativeGap x i) alpha) =
        ∑ i ∈ range (n.divisors.card - 1),
          Real.rpow (relativeGap x i) alpha := by
    rw [← hclast]
    exact sum_chain_Ico cv hcvmono hc0 _
  rw [hAlpha_eq_sum_range_extended alpha n hn, ← hpartition]
  unfold divisorChainEnergy
  apply sum_le_sum
  intro j _
  have hpq : cv ⟨j.1, by omega⟩ ≤ cv ⟨j.1 + 1, by omega⟩ :=
    hcvmono (by simp)
  have hblock := sum_Ico_relativeGap_rpow_le halpha x
    (extendedDivisorValue_pos n hn) (extendedDivisorValue_monotone n hn) hpq
  simpa [x, cv, relativeGap, extendedDivisorValue_eq] using hblock

private lemma card_divisors_pos {n : ℕ} (hn : n ≠ 0) : 0 < n.divisors.card :=
  Finset.card_pos.mpr (Nat.nonempty_divisors.mpr hn)

private lemma orderedDivisor_zero {n : ℕ} (hn : n ≠ 0) :
    orderedDivisor n ⟨0, card_divisors_pos hn⟩ = 1 := by
  rw [orderedDivisor, Finset.orderEmbOfFin_zero rfl (card_divisors_pos hn)]
  apply (Finset.min'_eq_iff _ _ _).2
  refine ⟨Nat.one_mem_divisors.mpr hn, ?_⟩
  intro d hd
  exact Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (Nat.pos_of_mem_divisors hd))

private lemma orderedDivisor_last {n : ℕ} (hn : n ≠ 0) :
    orderedDivisor n
      ⟨n.divisors.card - 1,
        Nat.sub_lt (card_divisors_pos hn) Nat.zero_lt_one⟩ = n := by
  rw [orderedDivisor, Finset.orderEmbOfFin_last rfl (card_divisors_pos hn)]
  apply (Finset.max'_eq_iff _ _ _).2
  exact ⟨Nat.mem_divisors_self n hn, fun d hd ↦ Nat.divisor_le hd⟩

/-- Value-level form of the refinement theorem.  A monotone finite sequence
of divisors beginning at `1` and ending at `n` bounds the energy of the full
ordered divisor sequence.  Repeated values are permitted and contribute
zero. -/
theorem hAlpha_le_valueChainEnergy {alpha : ℝ} (halpha : 1 ≤ alpha)
    {n m : ℕ} (hn : n ≠ 0) (d : Fin (m + 1) → ℕ)
    (hdmem : ∀ j, d j ∈ n.divisors) (hdmono : Monotone d)
    (hd0 : d ⟨0, by omega⟩ = 1) (hdlast : d ⟨m, by omega⟩ = n) :
    hAlpha alpha n ≤ valueChainEnergy alpha d := by
  let e : Fin n.divisors.card ≃o n.divisors := n.divisors.orderIsoOfFin rfl
  let c : Fin (m + 1) → Fin n.divisors.card := fun j ↦
    e.symm ⟨d j, hdmem j⟩
  have hc_value (j : Fin (m + 1)) : orderedDivisor n (c j) = d j := by
    exact congrArg Subtype.val (e.apply_symm_apply ⟨d j, hdmem j⟩)
  have hcmono : Monotone c := by
    intro i j hij
    apply e.symm.monotone
    exact hdmono hij
  have hc0 : (c ⟨0, by omega⟩).1 = 0 := by
    have heq : c ⟨0, by omega⟩ = ⟨0, card_divisors_pos hn⟩ := by
      apply (orderedDivisor n).injective
      rw [hc_value, hd0, orderedDivisor_zero hn]
    exact congrArg Fin.val heq
  have hclast : (c ⟨m, by omega⟩).1 = n.divisors.card - 1 := by
    have heq : c ⟨m, by omega⟩ =
        ⟨n.divisors.card - 1,
          Nat.sub_lt (card_divisors_pos hn) Nat.zero_lt_one⟩ := by
      apply (orderedDivisor n).injective
      rw [hc_value, hdlast, orderedDivisor_last hn]
    exact congrArg Fin.val heq
  calc
    hAlpha alpha n ≤ divisorChainEnergy alpha n c :=
      hAlpha_le_divisorChainEnergy halpha hn c hcmono hc0 hclast
    _ = valueChainEnergy alpha d := by
      unfold divisorChainEnergy valueChainEnergy
      apply sum_congr rfl
      intro j _
      rw [hc_value, hc_value]

end

end Vose1099

end

section
/-
# Finite logarithmic shells for Erdős Problem 1099

This file turns the subset-sum net into actual, increasingly ordered divisor
chains.  At integral level `t`, and depth `r`, we retain every selected divisor
whose logarithmic correction is in `[0, log 2]`, and adjoin `2^(t+1)` as the
right endpoint.  Sorting this finite set gives a divisor chain across the
whole dyadic shell.  Its logarithmic mesh is at most `2 * 2⁻ʳ`.
-/

open Finset Set
open scoped BigOperators

namespace Vose1099

noncomputable section

open scoped Classical

/-- The finite family of index sets whose digit sums lie in one dyadic
logarithmic shell. -/
def shellIndexSets (r : ℕ) : Finset (Finset ℕ) :=
  (Finset.Icc 1 r).powerset.filter
    (fun E ↦ (∑ i ∈ E, Net.delta i) ≤ Real.log 2)

/-- The actual selected divisors in the shell `[2^t,2^(t+1)]`, including the
right endpoint. -/
def shellDivisors (t r : ℕ) : Finset ℕ :=
  insert (2 ^ (t + 1))
    ((shellIndexSets r).image (fun E ↦ selectedDivisor t E))

lemma mem_shellIndexSets_iff {r : ℕ} {E : Finset ℕ} :
    E ∈ shellIndexSets r ↔
      E ⊆ Finset.Icc 1 r ∧ (∑ i ∈ E, Net.delta i) ≤ Real.log 2 := by
  simp [shellIndexSets]

lemma empty_mem_shellIndexSets (r : ℕ) : ∅ ∈ shellIndexSets r := by
  simp [shellIndexSets, Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]

lemma pow_mem_shellDivisors_left (t r : ℕ) :
    2 ^ t ∈ shellDivisors t r := by
  apply Finset.mem_insert_of_mem
  apply Finset.mem_image.2
  refine ⟨∅, empty_mem_shellIndexSets r, ?_⟩
  simp [selectedDivisor, indexSum, selectedProduct]

lemma pow_mem_shellDivisors_right (t r : ℕ) :
    2 ^ (t + 1) ∈ shellDivisors t r := by
  simp [shellDivisors]

lemma logDigit_eq_delta (i : ℕ) : logDigit i = Net.delta i := by
  rfl

lemma log_selectedDivisor_eq {t : ℕ} {E : Finset ℕ}
    (hEt : indexSum E ≤ t) :
    Real.log (selectedDivisor t E : ℝ) =
      (t : ℝ) * Real.log 2 + ∑ i ∈ E, Net.delta i := by
  simpa [logDigit_eq_delta] using log_selectedDivisor hEt

lemma indexSum_le_of_mem_shellIndexSets {t r : ℕ} {E : Finset ℕ}
    (hE : E ∈ shellIndexSets r) (hrt : triangular r ≤ t) :
    indexSum E ≤ t := by
  exact (indexSum_le_triangular (mem_shellIndexSets_iff.1 hE).1).trans hrt

lemma log_pow_two (t : ℕ) :
    Real.log ((2 ^ t : ℕ) : ℝ) = (t : ℝ) * Real.log 2 := by
  norm_num [Real.log_pow]

lemma shellDivisors_log_mem {t r d : ℕ} (hrt : triangular r ≤ t)
    (hd : d ∈ shellDivisors t r) :
    Real.log (d : ℝ) ∈
      Set.Icc ((t : ℝ) * Real.log 2) (((t + 1 : ℕ) : ℝ) * Real.log 2) := by
  simp only [shellDivisors, Finset.mem_insert, Finset.mem_image] at hd
  rcases hd with rfl | hd
  · rw [log_pow_two]
    exact ⟨mul_le_mul_of_nonneg_right (by norm_num) (Real.log_nonneg (by norm_num)), le_rfl⟩
  · obtain ⟨E, hE, rfl⟩ := hd
    have hsum0 : 0 ≤ ∑ i ∈ E, Net.delta i :=
      Finset.sum_nonneg fun i _ ↦ Net.delta_nonneg i
    have hsum2 : (∑ i ∈ E, Net.delta i) ≤ Real.log 2 :=
      (mem_shellIndexSets_iff.1 hE).2
    rw [log_selectedDivisor_eq (indexSum_le_of_mem_shellIndexSets hE hrt)]
    constructor
    · linarith
    · push_cast
      ring_nf
      linarith

lemma shellDivisors_pos {t r d : ℕ} (hd : d ∈ shellDivisors t r) : 0 < d := by
  simp only [shellDivisors, Finset.mem_insert, Finset.mem_image] at hd
  rcases hd with rfl | hd
  · positivity
  · obtain ⟨E, _, rfl⟩ := hd
    exact selectedDivisor_pos t E

lemma shellDivisors_dvd {k r t d : ℕ}
    (hrk : r ≤ k) (hrt : triangular r ≤ t)
    (htk : t + 1 ≤ triangular k) (hd : d ∈ shellDivisors t r) :
    d ∣ voseNumber k := by
  simp only [shellDivisors, Finset.mem_insert, Finset.mem_image] at hd
  rcases hd with rfl | hd
  · exact Nat.dvd_mul_right_of_dvd (pow_dvd_pow 2 htk) _
  · obtain ⟨E, hE, rfl⟩ := hd
    exact selectedDivisor_dvd (mem_shellIndexSets_iff.1 hE).1 hrk hrt
      (Nat.le_of_succ_le htk)

/-- Every point of the one-sided logarithmic net is represented by an actual
selected divisor in the shell. -/
lemma exists_shellDivisor_log_below {t r : ℕ} (hrt : triangular r ≤ t)
    {x : ℝ}
    (hx : x ∈ Set.Icc ((t : ℝ) * Real.log 2)
      (((t + 1 : ℕ) : ℝ) * Real.log 2)) :
    ∃ d ∈ shellDivisors t r,
      0 ≤ x - Real.log (d : ℝ) ∧
      x - Real.log (d : ℝ) ≤ Net.dyadic r := by
  let u := x - (t : ℝ) * Real.log 2
  have hu0 : 0 ≤ u := by exact sub_nonneg.mpr hx.1
  have hu2 : u ≤ Real.log 2 := by
    dsimp [u]
    norm_num [Nat.cast_add, Nat.cast_one] at hx
    ring_nf at hx ⊢
    linarith
  obtain ⟨E, hEsub, hE0, hEg⟩ := Net.exists_subsetSum_below hu0 hu2
  let d := selectedDivisor t E
  have hEmem : E ∈ shellIndexSets r := by
    rw [mem_shellIndexSets_iff]
    refine ⟨hEsub, ?_⟩
    linarith
  have hsumt : indexSum E ≤ t :=
    (indexSum_le_triangular hEsub).trans hrt
  refine ⟨d, ?_, ?_, ?_⟩
  · rw [shellDivisors]
    exact Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨E, hEmem, rfl⟩)
  · rw [log_selectedDivisor_eq hsumt]
    dsimp [u] at hE0
    linarith
  · rw [log_selectedDivisor_eq hsumt]
    dsimp [u] at hEg
    linarith

/-- Adjacent elements of the sorted finite divisor shell have logarithmic gap
at most `2 * 2⁻ʳ`. -/
lemma shellDivisors_log_mesh {t r a b : ℕ} (hrt : triangular r ≤ t)
    (ha : a ∈ shellDivisors t r) (hb : b ∈ shellDivisors t r)
    (hadj : ∀ d ∈ shellDivisors t r, ¬ (a < d ∧ d < b)) :
    Real.log (b : ℝ) - Real.log (a : ℝ) ≤ 2 * Net.dyadic r := by
  by_contra hgap
  let x := (Real.log (a : ℝ) + Real.log (b : ℝ)) / 2
  have hxa := shellDivisors_log_mem hrt ha
  have hxb := shellDivisors_log_mem hrt hb
  have hx : x ∈ Set.Icc ((t : ℝ) * Real.log 2)
      (((t + 1 : ℕ) : ℝ) * Real.log 2) := by
    constructor <;> dsimp [x] <;> linarith [hxa.1, hxa.2, hxb.1, hxb.2]
  obtain ⟨d, hd, hd0, hdg⟩ := exists_shellDivisor_log_below hrt hx
  have hloga : Real.log (a : ℝ) < Real.log (d : ℝ) := by
    dsimp [x] at hd0 hdg
    linarith
  have hlogb : Real.log (d : ℝ) < Real.log (b : ℝ) := by
    dsimp [x] at hd0 hdg
    linarith
  have had : a < d := by
    exact_mod_cast (Real.log_lt_log_iff
      (by exact_mod_cast shellDivisors_pos ha)
      (by exact_mod_cast shellDivisors_pos hd)).mp hloga
  have hdb : d < b := by
    exact_mod_cast (Real.log_lt_log_iff
      (by exact_mod_cast shellDivisors_pos hd)
      (by exact_mod_cast shellDivisors_pos hb)).mp hlogb
  exact hadj d hd ⟨had, hdb⟩

/- ## A list model for concatenating finite chains -/

/-- Logarithmic gap energy of a finite list of positive integers. -/
def listLogEnergy (alpha : ℝ) : List ℕ → ℝ
  | a :: b :: l =>
      (Real.log (b : ℝ) - Real.log (a : ℝ)) ^ alpha +
        listLogEnergy alpha (b :: l)
  | _ => 0

/-- The relative-gap energy used in Erdős Problem 1099, evaluated on a finite
divisor chain. -/
def listRelativeEnergy (alpha : ℝ) : List ℕ → ℝ
  | a :: b :: l =>
      (((b : ℝ) / (a : ℝ) - 1) ^ alpha) +
        listRelativeEnergy alpha (b :: l)
  | _ => 0

lemma listLogEnergy_nonneg (alpha : ℝ) (l : List ℕ)
    (hpos : ∀ d ∈ l, 0 < d) (hchain : l.IsChain (· ≤ ·)) :
    0 ≤ listLogEnergy alpha l := by
  induction l with
  | nil => simp [listLogEnergy]
  | cons a l ih =>
      cases l with
      | nil => simp [listLogEnergy]
      | cons b l =>
          simp only [List.isChain_cons_cons] at hchain
          have ha0 : 0 < a := hpos a (by simp)
          have hab : a ≤ b := hchain.1
          have hlog : Real.log (a : ℝ) ≤ Real.log (b : ℝ) :=
            Real.log_le_log (by exact_mod_cast ha0) (by exact_mod_cast hab)
          simp only [listLogEnergy]
          exact add_nonneg (Real.rpow_nonneg (sub_nonneg.mpr hlog) _)
            (ih (fun d hd ↦ hpos d (by simp [hd])) hchain.2)

lemma exp_sub_one_le_exp_mul {x C : ℝ} (hx0 : 0 ≤ x) (hxC : x ≤ C) :
    Real.exp x - 1 ≤ Real.exp C * x := by
  have htan := Real.add_one_le_exp (-x)
  have hmul := mul_le_mul_of_nonneg_left htan (Real.exp_pos x).le
  have hfirst : Real.exp x - 1 ≤ Real.exp x * x := by
    rw [mul_add, mul_one, ← Real.exp_add] at hmul
    simp only [add_neg_cancel, Real.exp_zero] at hmul
    linarith
  exact hfirst.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hxC) hx0)

lemma gap_le_of_rpow_le {alpha x C : ℝ} (halpha : 1 ≤ alpha)
    (hC : 1 ≤ C) (hxpow : x ^ alpha ≤ C) : x ≤ C := by
  by_cases hx1 : x ≤ 1
  · exact hx1.trans hC
  · have hone : 1 ≤ x := le_of_not_ge hx1
    have hxle : x ≤ x ^ alpha := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hone halpha
    exact hxle.trans hxpow

/-- On a positive increasing chain whose logarithmic energy is at most
`C ≥ 1`, relative-gap energy is at most `exp(C)^alpha` times logarithmic
energy.  This deliberately coarse conversion is enough for uniformity and
does not need a separately stored mesh certificate. -/
lemma listRelativeEnergy_le_exp_mul_listLogEnergy {alpha C : ℝ}
    (halpha : 1 ≤ alpha) (hC : 1 ≤ C) (l : List ℕ)
    (hpos : ∀ d ∈ l, 0 < d) (hchain : l.IsChain (· ≤ ·))
    (henergy : listLogEnergy alpha l ≤ C) :
    listRelativeEnergy alpha l ≤
      (Real.exp C) ^ alpha * listLogEnergy alpha l := by
  induction l with
  | nil => simp [listRelativeEnergy, listLogEnergy]
  | cons a l ih =>
      cases l with
      | nil => simp [listRelativeEnergy, listLogEnergy]
      | cons b l =>
          simp only [List.isChain_cons_cons] at hchain
          have hab : a ≤ b := hchain.1
          have hchain' : (b :: l).IsChain (· ≤ ·) := hchain.2
          have ha0 : 0 < a := hpos a (by simp)
          have hb0 : 0 < b := hpos b (by simp)
          let x := Real.log (b : ℝ) - Real.log (a : ℝ)
          have hx0 : 0 ≤ x := sub_nonneg.mpr
            (Real.log_le_log (by exact_mod_cast ha0) (by exact_mod_cast hab))
          have htail0 : 0 ≤ listLogEnergy alpha (b :: l) :=
            listLogEnergy_nonneg alpha _ (fun d hd ↦ hpos d (by simp [hd])) hchain'
          have hxpow : x ^ alpha ≤ C := by
            have he : x ^ alpha + listLogEnergy alpha (b :: l) ≤ C := by
              simpa only [listLogEnergy] using henergy
            linarith
          have hxC : x ≤ C := gap_le_of_rpow_le halpha hC hxpow
          have htailC : listLogEnergy alpha (b :: l) ≤ C := by
            have he : x ^ alpha + listLogEnergy alpha (b :: l) ≤ C := by
              simpa only [listLogEnergy] using henergy
            linarith [Real.rpow_nonneg hx0 alpha]
          have ih' := ih (fun d hd ↦ hpos d (by simp [hd])) hchain' htailC
          have hratio : (b : ℝ) / (a : ℝ) = Real.exp x := by
            dsimp [x]
            rw [Real.exp_sub, Real.exp_log (by exact_mod_cast hb0),
              Real.exp_log (by exact_mod_cast ha0)]
          have hrel0 : 0 ≤ (b : ℝ) / (a : ℝ) - 1 := by
            rw [sub_nonneg, one_le_div (by exact_mod_cast ha0)]
            exact_mod_cast hab
          have hlin : (b : ℝ) / (a : ℝ) - 1 ≤ Real.exp C * x := by
            rw [hratio]
            exact exp_sub_one_le_exp_mul hx0 hxC
          have hterm : (((b : ℝ) / (a : ℝ) - 1) ^ alpha) ≤
              (Real.exp C) ^ alpha * x ^ alpha := by
            calc
              (((b : ℝ) / (a : ℝ) - 1) ^ alpha)
                  ≤ (Real.exp C * x) ^ alpha :=
                    Real.rpow_le_rpow hrel0 hlin (by linarith)
              _ = (Real.exp C) ^ alpha * x ^ alpha := by
                    rw [Real.mul_rpow (Real.exp_pos C).le hx0]
          simp only [listRelativeEnergy, listLogEnergy]
          calc
            ((b : ℝ) / (a : ℝ) - 1) ^ alpha + listRelativeEnergy alpha (b :: l)
                ≤ (Real.exp C) ^ alpha * x ^ alpha +
                    (Real.exp C) ^ alpha * listLogEnergy alpha (b :: l) :=
                  add_le_add hterm ih'
            _ = (Real.exp C) ^ alpha *
                  (x ^ alpha + listLogEnergy alpha (b :: l)) := by ring

lemma listLogEnergy_append (alpha : ℝ) {l₁ l₂ : List ℕ}
    (h₁ : l₁ ≠ []) (h₂ : l₂ ≠ []) :
    listLogEnergy alpha (l₁ ++ l₂) =
      listLogEnergy alpha l₁ +
        (Real.log (l₂.head h₂ : ℝ) - Real.log (l₁.getLast h₁ : ℝ)) ^ alpha +
          listLogEnergy alpha l₂ := by
  induction l₁ with
  | nil => contradiction
  | cons a l ih =>
      cases l with
      | nil =>
          cases l₂ with
          | nil => contradiction
          | cons b l₂ => simp [listLogEnergy]
      | cons b l =>
          rw [List.cons_append]
          simp only [listLogEnergy]
          change (Real.log (b : ℝ) - Real.log (a : ℝ)) ^ alpha +
              listLogEnergy alpha ((b :: l) ++ l₂) = _
          rw [ih (by simp)]
          have hlast : (a :: b :: l).getLast h₁ =
              (b :: l).getLast (by simp) := by simp
          rw [hlast]
          ring

lemma listLogEnergy_append_of_getLast_eq_head
    (alpha : ℝ) (halpha : alpha ≠ 0) {l₁ l₂ : List ℕ}
    (h₁ : l₁ ≠ []) (h₂ : l₂ ≠ [])
    (hconnect : l₁.getLast h₁ = l₂.head h₂) :
    listLogEnergy alpha (l₁ ++ l₂) =
      listLogEnergy alpha l₁ + listLogEnergy alpha l₂ := by
  rw [listLogEnergy_append alpha h₁ h₂, hconnect, sub_self]
  simp [halpha]

lemma log_nat_div_sub_log_nat_div {n a b : ℕ}
    (hn : 0 < n) (ha : a ∣ n) (hb : b ∣ n) (ha0 : 0 < a) (hb0 : 0 < b) :
    Real.log ((n / a : ℕ) : ℝ) - Real.log ((n / b : ℕ) : ℝ) =
      Real.log (b : ℝ) - Real.log (a : ℝ) := by
  rw [Nat.cast_div_charZero ha, Nat.cast_div_charZero hb]
  rw [Real.log_div (by exact_mod_cast hn.ne') (by exact_mod_cast ha0.ne'),
    Real.log_div (by exact_mod_cast hn.ne') (by exact_mod_cast hb0.ne')]
  ring

/-- Reversing a divisor list and replacing `d` by `n/d` preserves its
logarithmic gap energy. -/
lemma listLogEnergy_reverse_div {alpha : ℝ} {n : ℕ} (hn : 0 < n)
    (l : List ℕ) (hdvd : ∀ d ∈ l, d ∣ n) :
    listLogEnergy alpha (l.reverse.map (fun d ↦ n / d)) =
      listLogEnergy alpha l := by
  induction l with
  | nil => simp [listLogEnergy]
  | cons a l ih =>
      cases l with
      | nil => simp [listLogEnergy]
      | cons b l =>
          have ha : a ∣ n := hdvd a (by simp)
          have hb : b ∣ n := hdvd b (by simp)
          have ha0 : 0 < a := Nat.pos_of_dvd_of_pos ha hn
          have hb0 : 0 < b := Nat.pos_of_dvd_of_pos hb hn
          have ih' := ih (fun d hd ↦ hdvd d (by simp [hd]))
          rw [List.reverse_cons, List.map_append]
          have hrev : (List.reverse (b :: l)).map (fun d ↦ n / d) ≠ [] := by simp
          rw [listLogEnergy_append alpha hrev (by simp)]
          simp only [List.map_cons, List.map_nil, List.head_cons, listLogEnergy]
          have hlast :
              ((List.reverse (b :: l)).map (fun d ↦ n / d)).getLast hrev = n / b := by
            simp
          rw [hlast, ih', log_nat_div_sub_log_nat_div hn ha hb ha0 hb0]
          ring

lemma listLogEnergy_ofFn {alpha : ℝ} {m : ℕ} (d : Fin (m + 1) → ℕ) :
    listLogEnergy alpha (List.ofFn d) =
      gapEnergy alpha (fun i ↦ Real.log (d i : ℝ)) := by
  induction m with
  | zero => simp [listLogEnergy, gapEnergy]
  | succ m ih =>
    rw [List.ofFn_succ]
    rw [show List.ofFn (fun i : Fin (m + 1) ↦ d i.succ) =
        d (Fin.succ 0) :: List.ofFn (fun i : Fin m ↦ d i.succ.succ) by
          rw [List.ofFn_succ]]
    simp only [listLogEnergy, gapEnergy, Fin.sum_univ_succ]
    have htail := ih (fun i : Fin (m + 1) ↦ d i.succ)
    rw [List.ofFn_succ] at htail
    rw [htail]
    unfold gapEnergy
    congr 1

lemma listRelativeEnergy_ofFn {alpha : ℝ} {m : ℕ} (d : Fin (m + 1) → ℕ) :
    listRelativeEnergy alpha (List.ofFn d) = valueChainEnergy alpha d := by
  induction m with
  | zero => simp [listRelativeEnergy, valueChainEnergy]
  | succ m ih =>
    rw [List.ofFn_succ]
    rw [show List.ofFn (fun i : Fin (m + 1) ↦ d i.succ) =
        d (Fin.succ 0) :: List.ofFn (fun i : Fin m ↦ d i.succ.succ) by
          rw [List.ofFn_succ]]
    simp only [listRelativeEnergy, valueChainEnergy, Fin.sum_univ_succ]
    have htail := ih (fun i : Fin (m + 1) ↦ d i.succ)
    rw [List.ofFn_succ] at htail
    rw [htail]
    unfold valueChainEnergy
    congr 1

/-- A finite (weakly) increasing chain of divisors of `voseNumber k`, with
specified endpoints.  Weak increase is intentional: concatenation retains
the common endpoint of two pieces, producing a harmless zero-energy edge. -/
structure LogDivisorChain (k a b : ℕ) where
  values : List ℕ
  ne_nil : values ≠ []
  isChain : values.IsChain (· ≤ ·)
  head_eq : values.head ne_nil = a
  last_eq : values.getLast ne_nil = b
  dvd : ∀ d ∈ values, d ∣ voseNumber k

namespace LogDivisorChain

/-- Change only the endpoint indices of a chain along proved equalities. -/
def recast {k a b a' b' : ℕ} (ha : a = a') (hb : b = b')
    (c : LogDivisorChain k a b) : LogDivisorChain k a' b' := by
  subst a'
  subst b'
  exact c

@[simp] lemma values_recast {k a b a' b' : ℕ} (ha : a = a') (hb : b = b')
    (c : LogDivisorChain k a b) : (recast ha hb c).values = c.values := by
  subst a'
  subst b'
  rfl

lemma all_pos {k a b : ℕ} (c : LogDivisorChain k a b) {d : ℕ}
    (hd : d ∈ c.values) : 0 < d := by
  exact Nat.pos_of_dvd_of_pos (c.dvd d hd) (voseNumber_pos k)

lemma left_pos {k a b : ℕ} (c : LogDivisorChain k a b) : 0 < a := by
  rw [← c.head_eq]
  exact c.all_pos (List.head_mem c.ne_nil)

lemma right_pos {k a b : ℕ} (c : LogDivisorChain k a b) : 0 < b := by
  rw [← c.last_eq]
  exact c.all_pos (List.getLast_mem c.ne_nil)

def singleton {k a : ℕ} (ha : a ∣ voseNumber k) : LogDivisorChain k a a where
  values := [a]
  ne_nil := by simp
  isChain := by simp
  head_eq := by simp
  last_eq := by simp
  dvd d hd := by
    simp only [List.mem_singleton] at hd
    subst d
    exact ha

@[simp] lemma energy_singleton {alpha : ℝ} {k a : ℕ} (ha : a ∣ voseNumber k) :
    listLogEnergy alpha (singleton ha).values = 0 := by
  simp [singleton, listLogEnergy]

/-- Concatenation of chains.  The repeated common endpoint contributes
zero logarithmic energy. -/
def append {k a b c : ℕ} (p : LogDivisorChain k a b)
    (q : LogDivisorChain k b c) : LogDivisorChain k a c where
  values := p.values ++ q.values
  ne_nil := by simp [p.ne_nil]
  isChain := p.isChain.append q.isChain (by
    intro x hx y hy
    rw [List.getLast?_eq_getLast_of_ne_nil p.ne_nil] at hx
    rw [List.head?_eq_some_head q.ne_nil] at hy
    simp only [Option.mem_some_iff] at hx hy
    subst x
    subst y
    simp [p.last_eq, q.head_eq])
  head_eq := by
    rw [List.head_append_of_ne_nil p.ne_nil]
    exact p.head_eq
  last_eq := by
    rw [List.getLast_append_of_right_ne_nil _ _ q.ne_nil]
    exact q.last_eq
  dvd d hd := by
    rw [List.mem_append] at hd
    exact hd.elim (p.dvd d) (q.dvd d)

lemma energy_append {alpha : ℝ} (halpha : alpha ≠ 0) {k a b c : ℕ}
    (p : LogDivisorChain k a b) (q : LogDivisorChain k b c) :
    listLogEnergy alpha (p.append q).values =
      listLogEnergy alpha p.values + listLogEnergy alpha q.values := by
  change listLogEnergy alpha (p.values ++ q.values) = _
  exact listLogEnergy_append_of_getLast_eq_head alpha halpha p.ne_nil q.ne_nil
    (p.last_eq.trans q.head_eq.symm)

/-- Totalized divisor complementation.  Its value at zero is chosen so the
function is antitone on all naturals; on every divisor chain it is simply
`d ↦ voseNumber k / d`. -/
def divisorComplement (n d : ℕ) : ℕ := if d = 0 then n else n / d

lemma nat_div_antitone_pos (n : ℕ) {a b : ℕ} (ha : 0 < a) (hab : a ≤ b) :
    n / b ≤ n / a := by
  apply (Nat.le_div_iff_mul_le ha).2
  calc
    (n / b) * a ≤ (n / b) * b := Nat.mul_le_mul_left _ hab
    _ ≤ n := Nat.div_mul_le_self n b

lemma divisorComplement_antitone (n : ℕ) : Antitone (divisorComplement n) := by
  intro a b hab
  by_cases ha : a = 0
  · subst a
    by_cases hb : b = 0
    · simp [divisorComplement, hb]
    · simp [divisorComplement, hb, Nat.div_le_self]
  · have ha0 : 0 < a := Nat.pos_of_ne_zero ha
    have hb : b ≠ 0 := (ha0.trans_le hab).ne'
    simp only [divisorComplement, if_neg ha, if_neg hb]
    exact nat_div_antitone_pos n ha0 hab

/-- Reflection under `d ↦ voseNumber k / d`. -/
def reflect {k a b : ℕ} (c : LogDivisorChain k a b) :
    LogDivisorChain k (voseNumber k / b) (voseNumber k / a) where
  values := c.values.reverse.map (divisorComplement (voseNumber k))
  ne_nil := by simp [c.ne_nil]
  isChain := by
    apply List.isChain_map_of_isChain (divisorComplement (voseNumber k))
      (fun _ _ h ↦ divisorComplement_antitone _ h)
    exact List.isChain_reverse.2 c.isChain
  head_eq := by
    simp only [List.head_map]
    rw [List.head_reverse, c.last_eq]
    simp [divisorComplement, c.right_pos.ne']
  last_eq := by
    simp only [List.getLast_map]
    rw [List.getLast_reverse, c.head_eq]
    simp [divisorComplement, c.left_pos.ne']
  dvd d hd := by
    rw [List.mem_map] at hd
    obtain ⟨x, hx, rfl⟩ := hd
    have hxdvd : x ∣ voseNumber k := c.dvd x (by simpa using hx)
    have hxpos : 0 < x := Nat.pos_of_dvd_of_pos hxdvd (voseNumber_pos k)
    simp only [divisorComplement, if_neg hxpos.ne']
    exact Nat.div_dvd_of_dvd hxdvd

lemma energy_reflect {alpha : ℝ} {k a b : ℕ} (c : LogDivisorChain k a b) :
    listLogEnergy alpha c.reflect.values = listLogEnergy alpha c.values := by
  have hmap : c.values.reverse.map (divisorComplement (voseNumber k)) =
      c.values.reverse.map (fun d ↦ voseNumber k / d) := by
    apply List.map_congr_left
    intro d hd
    have hd' : d ∈ c.values := by simpa using hd
    simp [divisorComplement, (c.all_pos hd').ne']
  change listLogEnergy alpha
    (c.values.reverse.map (divisorComplement (voseNumber k))) = _
  calc
    listLogEnergy alpha (c.values.reverse.map (divisorComplement (voseNumber k))) =
        listLogEnergy alpha (c.values.reverse.map (fun d ↦ voseNumber k / d)) :=
      congrArg (listLogEnergy alpha) hmap
    _ = listLogEnergy alpha c.values :=
      listLogEnergy_reverse_div (voseNumber_pos k) c.values c.dvd

end LogDivisorChain

/-- A `Fin`-indexed increasing chain crossing one dyadic shell. -/
def IsShellChain (k t : ℕ) {m : ℕ} (d : Fin (m + 1) → ℕ) : Prop :=
  StrictMono d ∧ d 0 = 2 ^ t ∧ d ⟨m, by omega⟩ = 2 ^ (t + 1) ∧
    ∀ i, d i ∣ voseNumber k

/-- The sorted shell gives a genuine divisor chain, together with its sharp
finite logarithmic energy estimate. -/
theorem exists_shell_chain {alpha : ℝ} (halpha : 1 ≤ alpha)
    {k r t : ℕ} (hrk : r ≤ k) (hrt : triangular r ≤ t)
    (htk : t + 1 ≤ triangular k) :
    ∃ (m : ℕ) (d : Fin (m + 1) → ℕ),
      IsShellChain k t d ∧
      gapEnergy alpha (fun i ↦ Real.log (d i : ℝ)) ≤
        (2 * Net.dyadic r) ^ (alpha - 1) * Real.log 2 := by
  let s := shellDivisors t r
  have hsne : s.Nonempty := ⟨2 ^ t, pow_mem_shellDivisors_left t r⟩
  let m := s.card - 1
  have hcard : s.card = m + 1 := by
    dsimp [m]
    have : 0 < s.card := Finset.card_pos.mpr hsne
    omega
  let e : Fin (m + 1) ≃o s := s.orderIsoOfFin hcard
  let d : Fin (m + 1) → ℕ := fun i ↦ (e i : ℕ)
  have hdmem (i : Fin (m + 1)) : d i ∈ shellDivisors t r := by
    exact (e i).property
  have hstrict : StrictMono d := by
    intro i j hij
    exact e.lt_iff_lt.2 hij
  have hfirst : d 0 = 2 ^ t := by
    apply le_antisymm
    · have hepow := e.monotone
          (Fin.zero_le (e.symm ⟨2 ^ t, pow_mem_shellDivisors_left t r⟩))
      have hv : (e 0).val ≤
          (e (e.symm ⟨2 ^ t, pow_mem_shellDivisors_left t r⟩)).val := hepow
      change (e 0).val ≤ 2 ^ t
      simpa only [OrderIso.apply_symm_apply] using hv
    · have hm := shellDivisors_log_mem hrt (hdmem 0)
      have hposd : (0 : ℝ) < d 0 := by exact_mod_cast shellDivisors_pos (hdmem 0)
      have hlog : Real.log (((2 ^ t : ℕ) : ℝ)) ≤ Real.log (d 0 : ℝ) := by
        simpa only [log_pow_two] using hm.1
      exact_mod_cast (Real.log_le_log_iff (by positivity) hposd).mp hlog
  have hlast : d ⟨m, by omega⟩ = 2 ^ (t + 1) := by
    apply le_antisymm
    · have hm := shellDivisors_log_mem hrt (hdmem ⟨m, by omega⟩)
      have hposd : (0 : ℝ) < d ⟨m, by omega⟩ := by
        exact_mod_cast shellDivisors_pos (hdmem ⟨m, by omega⟩)
      have hlog : Real.log (d ⟨m, by omega⟩ : ℝ) ≤
          Real.log (((2 ^ (t + 1) : ℕ) : ℝ)) := by
        simpa only [log_pow_two] using hm.2
      exact_mod_cast (Real.log_le_log_iff hposd (by positivity)).mp hlog
    · have hidx : e.symm ⟨2 ^ (t + 1), pow_mem_shellDivisors_right t r⟩ ≤
          (Fin.last m : Fin (m + 1)) := Fin.le_last _
      have := e.monotone hidx
      have hv : (e (e.symm ⟨2 ^ (t + 1), pow_mem_shellDivisors_right t r⟩)).val ≤
          (e (Fin.last m)).val := this
      change 2 ^ (t + 1) ≤ (e (Fin.last m)).val
      simpa only [OrderIso.apply_symm_apply] using hv
  have hmonoLog : Monotone (fun i ↦ Real.log (d i : ℝ)) := by
    intro i j hij
    have hdij : d i ≤ d j := hstrict.monotone hij
    exact Real.log_le_log (by exact_mod_cast shellDivisors_pos (hdmem i))
      (by exact_mod_cast hdij)
  have hmesh : ∀ i : Fin m,
      Real.log (d ⟨i.1 + 1, by omega⟩ : ℝ) -
          Real.log (d ⟨i.1, by omega⟩ : ℝ) ≤ 2 * Net.dyadic r := by
    intro i
    apply shellDivisors_log_mesh hrt (hdmem _) (hdmem _)
    intro z hz hzbetween
    let iz : Fin (m + 1) := e.symm ⟨z, hz⟩
    have hi : (⟨i.1, by omega⟩ : Fin (m + 1)) < iz := by
      apply e.lt_iff_lt.1
      change (e ⟨i.1, by omega⟩).val < (e iz).val
      rw [show e iz = ⟨z, hz⟩ by simp [iz]]
      exact hzbetween.1
    have hiz : iz < (⟨i.1 + 1, by omega⟩ : Fin (m + 1)) := by
      apply e.lt_iff_lt.1
      change (e iz).val < (e ⟨i.1 + 1, by omega⟩).val
      rw [show e iz = ⟨z, hz⟩ by simp [iz]]
      exact hzbetween.2
    change i.1 < iz.1 at hi
    change iz.1 < i.1 + 1 at hiz
    omega
  refine ⟨m, d, ⟨hstrict, hfirst, hlast, fun i ↦
    shellDivisors_dvd hrk hrt htk (hdmem i)⟩, ?_⟩
  have henergy := gapEnergy_le_mesh_mul_length halpha
    (fun i ↦ Real.log (d i : ℝ)) hmonoLog hmesh
  calc
    gapEnergy alpha (fun i ↦ Real.log (d i : ℝ)) ≤
        (2 * Net.dyadic r) ^ (alpha - 1) *
          (Real.log (d ⟨m, by omega⟩ : ℝ) - Real.log (d 0 : ℝ)) := henergy
    _ = (2 * Net.dyadic r) ^ (alpha - 1) * Real.log 2 := by
      rw [hlast, hfirst, log_pow_two, log_pow_two]
      push_cast
      ring

/-- List-valued form of `exists_shell_chain`, ready for concatenation. -/
theorem exists_shell_logDivisorChain {alpha : ℝ} (halpha : 1 ≤ alpha)
    {k r t : ℕ} (hrk : r ≤ k) (hrt : triangular r ≤ t)
    (htk : t + 1 ≤ triangular k) :
    ∃ c : LogDivisorChain k (2 ^ t) (2 ^ (t + 1)),
      listLogEnergy alpha c.values ≤
        (2 * Net.dyadic r) ^ (alpha - 1) * Real.log 2 := by
  obtain ⟨m, d, hd, henergy⟩ := exists_shell_chain halpha hrk hrt htk
  let l := List.ofFn d
  have hlne : l ≠ [] := by simp [l]
  have hlchain : l.IsChain (· ≤ ·) := by
    rw [show l = List.ofFn d by rfl, List.isChain_ofFn]
    intro i hi
    exact hd.1.monotone (Fin.mk_le_mk.mpr (by omega))
  let c : LogDivisorChain k (2 ^ t) (2 ^ (t + 1)) :=
    { values := l
      ne_nil := hlne
      isChain := hlchain
      head_eq := by simpa [l] using hd.2.1
      last_eq := by
        have hlastfn := (List.getLast_ofFn_succ d).trans hd.2.2.1
        simpa only [l] using hlastfn
      dvd := by
        intro x hx
        simp only [l, List.mem_ofFn] at hx
        obtain ⟨i, rfl⟩ := hx
        exact hd.2.2.2 i }
  refine ⟨c, ?_⟩
  rw [show c.values = List.ofFn d by rfl, listLogEnergy_ofFn]
  exact henergy

/-- The geometric-polynomial majorant term for depth `r = n+3`. -/
def shellMajorantTerm (alpha : ℝ) (n : ℕ) : ℝ :=
  ((n : ℝ) + 4) *
    (2 * Net.dyadic (n + 3)) ^ (alpha - 1) * Real.log 2

/-- Concatenate `n` consecutive unit shells, all using the same digit depth
`r`. -/
theorem exists_shell_block {alpha : ℝ} (halpha : 1 ≤ alpha)
    {k r t n : ℕ} (hrk : r ≤ k) (hrt : triangular r ≤ t)
    (htk : t + n ≤ triangular k) :
    ∃ c : LogDivisorChain k (2 ^ t) (2 ^ (t + n)),
      listLogEnergy alpha c.values ≤
        (n : ℝ) * ((2 * Net.dyadic r) ^ (alpha - 1) * Real.log 2) := by
  induction n with
  | zero =>
      have hpow : 2 ^ t ∣ voseNumber k :=
        Nat.dvd_mul_right_of_dvd (pow_dvd_pow 2 (by simpa using htk)) _
      refine ⟨LogDivisorChain.singleton hpow, ?_⟩
      simp
  | succ n ih =>
      have htn : t + n ≤ triangular k := by omega
      obtain ⟨p, hp⟩ := ih htn
      have hrtn : triangular r ≤ t + n := hrt.trans (Nat.le_add_right t n)
      have hsucc : t + n + 1 ≤ triangular k := by omega
      obtain ⟨q, hq⟩ := exists_shell_logDivisorChain halpha hrk hrtn hsucc
      let c := p.append q
      refine ⟨c, ?_⟩
      rw [LogDivisorChain.energy_append (by linarith : alpha ≠ 0)]
      push_cast
      nlinarith

/-- A complete block at depth `r` contains exactly `r+1` dyadic shells. -/
theorem exists_depth_block {alpha : ℝ} (halpha : 1 ≤ alpha)
    {k r : ℕ} (hrk : r + 1 ≤ k) :
    ∃ c : LogDivisorChain k (2 ^ triangular r) (2 ^ triangular (r + 1)),
      listLogEnergy alpha c.values ≤
        ((r : ℝ) + 1) *
          ((2 * Net.dyadic r) ^ (alpha - 1) * Real.log 2) := by
  have hrk' : r ≤ k := by omega
  have htri : triangular r + (r + 1) ≤ triangular k := by
    rw [← triangular_succ]
    exact triangular_mono hrk
  rw [triangular_succ]
  simpa only [Nat.cast_add, Nat.cast_one] using
    (exists_shell_block halpha hrk' le_rfl htri)

/-- The initial six shells, from `1` to `2^triangular 3`, have a fixed
energy cost. -/
theorem exists_initial_block {alpha : ℝ} (halpha : 1 ≤ alpha)
    {k : ℕ} (hk : 3 ≤ k) :
    ∃ c : LogDivisorChain k 1 (2 ^ triangular 3),
      listLogEnergy alpha c.values ≤
        (triangular 3 : ℝ) *
          ((2 * Net.dyadic 0) ^ (alpha - 1) * Real.log 2) := by
  have htri : triangular 0 + triangular 3 ≤ triangular k := by
    simpa using triangular_mono hk
  obtain ⟨c, hc⟩ := exists_shell_block halpha (k := k) (r := 0)
    (t := 0) (n := triangular 3) (Nat.zero_le _) (Nat.zero_le _) htri
  simpa only [triangular_zero, pow_zero, zero_add] using ⟨c, hc⟩

/-- For fixed ambient `k`, concatenate the complete depth blocks
`3,4,...,3+j-1`. -/
theorem exists_tail_blocks {alpha : ℝ} (halpha : 1 ≤ alpha)
    {k j : ℕ} (hjk : 3 + j ≤ k) :
    ∃ c : LogDivisorChain k (2 ^ triangular 3) (2 ^ triangular (3 + j)),
      listLogEnergy alpha c.values ≤
        ∑ n ∈ Finset.range j, shellMajorantTerm alpha n := by
  induction j with
  | zero =>
      have hpow : 2 ^ triangular 3 ∣ voseNumber k :=
        Nat.dvd_mul_right_of_dvd
          (pow_dvd_pow 2 (triangular_mono (by omega : 3 ≤ k))) _
      refine ⟨LogDivisorChain.singleton hpow, ?_⟩
      simp
  | succ j ih =>
      have hjk' : 3 + j ≤ k := by omega
      obtain ⟨p, hp⟩ := ih hjk'
      obtain ⟨q, hq⟩ := exists_depth_block halpha
        (r := 3 + j) (by omega : 3 + j + 1 ≤ k)
      let c := p.append q
      have hidx : 3 + (j + 1) = 3 + j + 1 := by omega
      rw [hidx]
      refine ⟨c, ?_⟩
      rw [LogDivisorChain.energy_append (by linarith : alpha ≠ 0),
        Finset.sum_range_succ]
      · have hq' : listLogEnergy alpha q.values ≤ shellMajorantTerm alpha j := by
          calc
            listLogEnergy alpha q.values ≤
                (((3 + j : ℕ) : ℝ) + 1) *
                  ((2 * Net.dyadic (3 + j)) ^ (alpha - 1) * Real.log 2) := hq
            _ = shellMajorantTerm alpha j := by
              unfold shellMajorantTerm
              rw [Nat.add_comm j 3]
              push_cast
              ring
        exact add_le_add hp hq'

/-- The full lower-half chain, from `1` to `2^triangular k`, has the stated
finite-prefix bound. -/
theorem exists_lower_chain {alpha : ℝ} (halpha : 1 ≤ alpha)
    {k : ℕ} (hk : 3 ≤ k) :
    ∃ c : LogDivisorChain k 1 (2 ^ triangular k),
      listLogEnergy alpha c.values ≤
        (triangular 3 : ℝ) *
            ((2 * Net.dyadic 0) ^ (alpha - 1) * Real.log 2) +
          ∑ n ∈ Finset.range (k - 3), shellMajorantTerm alpha n := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  obtain ⟨p, hp⟩ := exists_initial_block halpha (by omega : 3 ≤ 3 + j)
  obtain ⟨q, hq⟩ := exists_tail_blocks halpha (le_rfl : 3 + j ≤ 3 + j)
  let c := p.append q
  refine ⟨c, ?_⟩
  rw [LogDivisorChain.energy_append (by linarith : alpha ≠ 0)]
  simpa only [Nat.add_sub_cancel_left] using add_le_add hp hq

/- ## The cap and the convergent majorant -/

lemma log_generatorProduct (k : ℕ) :
    Real.log (generatorProduct k : ℝ) =
      (triangular k : ℝ) * Real.log 2 +
        ∑ i ∈ Finset.Icc 1 k, Net.delta i := by
  rw [generatorProduct, Nat.cast_prod, Real.log_prod]
  · simp_rw [log_generator, logDigit_eq_delta]
    rw [Finset.sum_add_distrib]
    change (∑ x ∈ Finset.Icc 1 k, (x : ℝ) * Real.log 2) +
        ∑ x ∈ Finset.Icc 1 k, Net.delta x = _
    rw [← Finset.sum_mul]
    congr 1
    rw [triangular, Nat.cast_sum]
  · intro i hi
    exact_mod_cast generator_ne_zero i

lemma pow_triangular_le_generatorProduct (k : ℕ) :
    2 ^ triangular k ≤ generatorProduct k := by
  calc
    2 ^ triangular k = ∏ i ∈ Finset.Icc 1 k, 2 ^ i := by
      rw [triangular, Finset.prod_pow_eq_pow_sum]
    _ ≤ ∏ i ∈ Finset.Icc 1 k, generator i := by
      exact Finset.prod_le_prod' fun i _ ↦ by simp [generator]
    _ = generatorProduct k := rfl

/-- The single central cap has logarithmic length less than one. -/
lemma cap_log_gap_lt_one (k : ℕ) :
    Real.log (generatorProduct k : ℝ) -
        Real.log ((2 ^ triangular k : ℕ) : ℝ) < 1 := by
  rw [log_generatorProduct, log_pow_two]
  have := Net.sum_delta_lt_one k
  linarith

/-- The cap from the last power of two to the generator product. -/
theorem exists_cap_chain {alpha : ℝ} (halpha : 1 ≤ alpha) (k : ℕ) :
    ∃ c : LogDivisorChain k (2 ^ triangular k) (generatorProduct k),
      listLogEnergy alpha c.values ≤ 1 := by
  have hpowdvd : 2 ^ triangular k ∣ voseNumber k := by
    rw [voseNumber]
    exact dvd_mul_right _ _
  have hprodvd : generatorProduct k ∣ voseNumber k := by
    rw [voseNumber]
    exact dvd_mul_left _ _
  let c : LogDivisorChain k (2 ^ triangular k) (generatorProduct k) :=
    { values := [2 ^ triangular k, generatorProduct k]
      ne_nil := by simp
      isChain := by simpa using pow_triangular_le_generatorProduct k
      head_eq := by simp
      last_eq := by simp
      dvd := by
        intro d hd
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
        rcases hd with rfl | rfl
        · exact hpowdvd
        · exact hprodvd }
  refine ⟨c, ?_⟩
  have hgap0 : 0 ≤ Real.log (generatorProduct k : ℝ) -
      Real.log ((2 ^ triangular k : ℕ) : ℝ) := by
    exact sub_nonneg.mpr (Real.log_le_log
      (by positivity : (0 : ℝ) < ((2 ^ triangular k : ℕ) : ℝ))
      (by exact_mod_cast pow_triangular_le_generatorProduct k))
  have hgap1 : Real.log (generatorProduct k : ℝ) -
      Real.log ((2 ^ triangular k : ℕ) : ℝ) ≤ 1 :=
    (cap_log_gap_lt_one k).le
  change listLogEnergy alpha [2 ^ triangular k, generatorProduct k] ≤ 1
  simp only [listLogEnergy, add_zero]
  simpa using Real.rpow_le_one hgap0 hgap1 (by linarith : 0 ≤ alpha)

def shellMajorant (alpha : ℝ) : ℝ :=
  ∑' n : ℕ, shellMajorantTerm alpha n

lemma shellMajorantTerm_nonneg {alpha : ℝ} (n : ℕ) :
    0 ≤ shellMajorantTerm alpha n := by
  unfold shellMajorantTerm
  exact mul_nonneg
    (mul_nonneg (by positivity)
      (Real.rpow_nonneg (mul_nonneg (by norm_num) (Net.dyadic_nonneg _)) _))
    (Real.log_nonneg (by norm_num))

lemma two_mul_dyadic_add_three (n : ℕ) :
    2 * Net.dyadic (n + 3) = (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ n := by
  rw [Net.dyadic, pow_add]
  norm_num
  ring

lemma shellMajorantTerm_eq_geometric {alpha : ℝ} (n : ℕ) :
    shellMajorantTerm alpha n =
      ((1 / 4 : ℝ) ^ (alpha - 1) * Real.log 2) *
        (((n : ℝ) + 4) * ((1 / 2 : ℝ) ^ (alpha - 1)) ^ n) := by
  rw [shellMajorantTerm, two_mul_dyadic_add_three]
  rw [Real.mul_rpow (by positivity : (0 : ℝ) ≤ 1 / 4)
    (by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ n)]
  have hpow : (((1 / 2 : ℝ) ^ n) ^ (alpha - 1)) =
      (((1 / 2 : ℝ) ^ (alpha - 1)) ^ n) := by
    rw [← Real.rpow_natCast_mul (by positivity : (0 : ℝ) ≤ 1 / 2),
      ← Real.rpow_mul_natCast (by positivity : (0 : ℝ) ≤ 1 / 2)]
    congr 1
    ring
  rw [hpow]
  ring

/-- The shell majorant is a genuinely convergent series for every
`alpha > 1`. -/
lemma summable_shellMajorantTerm {alpha : ℝ} (halpha : 1 < alpha) :
    Summable (shellMajorantTerm alpha) := by
  let q : ℝ := (1 / 2 : ℝ) ^ (alpha - 1)
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hqlt : q < 1 := by
    dsimp [q]
    exact Real.rpow_lt_one (by norm_num) (by norm_num) (sub_pos.mpr halpha)
  have hqnorm : ‖q‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hq0] using hqlt
  have hsumn : Summable (fun n : ℕ ↦ (n : ℝ) * q ^ n) := by
    simpa using (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hqnorm)
  have hsumc : Summable (fun n : ℕ ↦ (4 : ℝ) * q ^ n) :=
    (summable_geometric_of_norm_lt_one hqnorm).mul_left 4
  have hsum : Summable (fun n : ℕ ↦ ((n : ℝ) + 4) * q ^ n) := by
    convert hsumn.add hsumc using 1
    ext n
    ring
  have hmul := hsum.mul_left ((1 / 4 : ℝ) ^ (alpha - 1) * Real.log 2)
  simpa only [q, ← shellMajorantTerm_eq_geometric] using hmul

lemma shellMajorant_nonneg {alpha : ℝ} :
    0 ≤ shellMajorant alpha := by
  unfold shellMajorant
  exact tsum_nonneg fun n ↦ shellMajorantTerm_nonneg n

lemma sum_shellMajorantTerm_le {alpha : ℝ} (halpha : 1 < alpha) (j : ℕ) :
    (∑ n ∈ Finset.range j, shellMajorantTerm alpha n) ≤ shellMajorant alpha := by
  unfold shellMajorant
  exact (summable_shellMajorantTerm halpha).sum_le_tsum (Finset.range j)
    (fun n _ ↦ shellMajorantTerm_nonneg n)

/-- A lower chain followed by the cap, uniformly bounded independently of
`k`. -/
theorem exists_lower_cap_chain {alpha : ℝ} (halpha : 1 < alpha)
    {k : ℕ} (hk : 3 ≤ k) :
    ∃ c : LogDivisorChain k 1 (generatorProduct k),
      listLogEnergy alpha c.values ≤
        (triangular 3 : ℝ) *
            ((2 * Net.dyadic 0) ^ (alpha - 1) * Real.log 2) +
          shellMajorant alpha + 1 := by
  obtain ⟨p, hp⟩ := exists_lower_chain halpha.le hk
  obtain ⟨q, hq⟩ := exists_cap_chain halpha.le k
  let c := p.append q
  refine ⟨c, ?_⟩
  rw [LogDivisorChain.energy_append (by linarith : alpha ≠ 0)]
  have hprefix := sum_shellMajorantTerm_le halpha (k - 3)
  linarith

/-- Complementation turns the lower chain into the upper chain, beginning at
the generator product. -/
theorem reflect_lower_chain {alpha : ℝ} (halpha : 1 ≤ alpha)
    {k : ℕ} (hk : 3 ≤ k) :
    ∃ c : LogDivisorChain k (generatorProduct k) (voseNumber k),
      listLogEnergy alpha c.values ≤
        (triangular 3 : ℝ) *
            ((2 * Net.dyadic 0) ^ (alpha - 1) * Real.log 2) +
          ∑ n ∈ Finset.range (k - 3), shellMajorantTerm alpha n := by
  obtain ⟨p, hp⟩ := exists_lower_chain halpha hk
  have hleft : voseNumber k / 2 ^ triangular k = generatorProduct k := by
    rw [voseNumber]
    calc
      (2 ^ triangular k * generatorProduct k) / 2 ^ triangular k =
          (generatorProduct k * 2 ^ triangular k) / 2 ^ triangular k := by
            rw [Nat.mul_comm]
      _ = generatorProduct k := Nat.mul_div_left _ (H := by positivity)
  have hright : voseNumber k / 1 = voseNumber k := by simp
  let c : LogDivisorChain k (generatorProduct k) (voseNumber k) :=
    LogDivisorChain.recast hleft hright p.reflect
  refine ⟨c, ?_⟩
  simpa only [c, LogDivisorChain.values_recast, LogDivisorChain.energy_reflect] using hp

/-- The promised global finite divisor chain.  Its logarithmic `alpha`-energy
is bounded by a constant depending only on `alpha`, uniformly in `k`. -/
theorem exists_global_logDivisorChain {alpha : ℝ} (halpha : 1 < alpha)
    {k : ℕ} (hk : 3 ≤ k) :
    ∃ c : LogDivisorChain k 1 (voseNumber k),
      listLogEnergy alpha c.values ≤
        2 * ((triangular 3 : ℝ) *
              ((2 * Net.dyadic 0) ^ (alpha - 1) * Real.log 2) +
            shellMajorant alpha) + 1 := by
  obtain ⟨p, hp⟩ := exists_lower_cap_chain halpha hk
  obtain ⟨q, hq⟩ := reflect_lower_chain halpha.le hk
  let c := p.append q
  refine ⟨c, ?_⟩
  rw [LogDivisorChain.energy_append (by linarith : alpha ≠ 0)]
  have hprefix := sum_shellMajorantTerm_le halpha (k - 3)
  linarith

/-- An explicit uniform constant for relative-gap energy of the constructed
chains. -/
def globalLogBound (alpha : ℝ) : ℝ :=
  2 * ((triangular 3 : ℝ) *
        ((2 * Net.dyadic 0) ^ (alpha - 1) * Real.log 2) +
      shellMajorant alpha) + 1

def globalRelativeBound (alpha : ℝ) : ℝ :=
  (Real.exp (globalLogBound alpha)) ^ alpha * globalLogBound alpha

lemma one_le_globalLogBound {alpha : ℝ} :
    1 ≤ globalLogBound alpha := by
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hshell : 0 ≤ shellMajorant alpha := shellMajorant_nonneg
  have hdy : 0 ≤ 2 * Net.dyadic 0 :=
    mul_nonneg (by norm_num) (Net.dyadic_nonneg 0)
  have hpow : 0 ≤ (2 * Net.dyadic 0) ^ (alpha - 1) :=
    Real.rpow_nonneg hdy _
  have hearly : 0 ≤ (triangular 3 : ℝ) *
      ((2 * Net.dyadic 0) ^ (alpha - 1) * Real.log 2) :=
    mul_nonneg (by positivity) (mul_nonneg hpow hlog)
  unfold globalLogBound
  linarith

/-- Final construction-side estimate: for every `k ≥ 3` there is a finite
increasing divisor chain from `1` to `voseNumber k` whose relative-gap
`alpha`-energy is bounded by a constant independent of `k`.

The chain is weakly increasing because concatenation retains common
endpoints.  Deleting repetitions makes it strictly increasing and leaves its
energy unchanged. -/
theorem exists_global_relativeDivisorChain {alpha : ℝ} (halpha : 1 < alpha)
    {k : ℕ} (hk : 3 ≤ k) :
    ∃ c : LogDivisorChain k 1 (voseNumber k),
      listRelativeEnergy alpha c.values ≤ globalRelativeBound alpha := by
  obtain ⟨c, hc⟩ := exists_global_logDivisorChain halpha hk
  refine ⟨c, ?_⟩
  have hconvert := listRelativeEnergy_le_exp_mul_listLogEnergy
    halpha.le one_le_globalLogBound c.values
    (fun d hd ↦ c.all_pos hd) c.isChain (by simpa [globalLogBound] using hc)
  calc
    listRelativeEnergy alpha c.values
        ≤ (Real.exp (globalLogBound alpha)) ^ alpha *
            listLogEnergy alpha c.values := hconvert
    _ ≤ (Real.exp (globalLogBound alpha)) ^ alpha * globalLogBound alpha := by
      exact mul_le_mul_of_nonneg_left
        (by simpa [globalLogBound] using hc)
        (Real.rpow_nonneg (Real.exp_pos _).le _)
    _ = globalRelativeBound alpha := rfl

/-- The complete ordered divisor sequence has no more relative-gap energy
than the uniformly bounded Vose chain. -/
theorem hAlpha_voseNumber_le_globalRelativeBound {alpha : ℝ}
    (halpha : 1 < alpha) {k : ℕ} (hk : 3 ≤ k) :
    hAlpha alpha (voseNumber k) ≤ globalRelativeBound alpha := by
  obtain ⟨c, hc⟩ := exists_global_relativeDivisorChain halpha hk
  let m := c.values.length - 1
  have hlenpos : 0 < c.values.length := List.length_pos_of_ne_nil c.ne_nil
  have hlen : c.values.length = m + 1 := by
    dsimp [m]
    omega
  let e : Fin (m + 1) → Fin c.values.length := fun i ↦ Fin.cast hlen.symm i
  let d : Fin (m + 1) → ℕ := fun i ↦ c.values.get (e i)
  have hdmem : ∀ i, d i ∈ (voseNumber k).divisors := by
    intro i
    apply Nat.mem_divisors.mpr
    exact ⟨c.dvd (d i) (List.get_mem c.values (e i)), (voseNumber_pos k).ne'⟩
  have hdmono : Monotone d := by
    intro i j hij
    exact c.isChain.sortedLE.monotone_get (by
      change i.1 ≤ j.1
      exact hij)
  have hd0 : d ⟨0, by omega⟩ = 1 := by
    have hh := (c.values.head_eq_getElem_zero c.ne_nil).symm.trans c.head_eq
    have he0 : e ⟨0, by omega⟩ = ⟨0, hlenpos⟩ := by
      apply Fin.ext
      rfl
    change c.values.get (e ⟨0, by omega⟩) = 1
    rw [he0]
    exact hh
  have hdlast : d ⟨m, by omega⟩ = voseNumber k := by
    have hh := (List.get_length_sub_one (by omega :
      c.values.length - 1 < c.values.length)).trans c.last_eq
    have helast : e ⟨m, by omega⟩ =
        ⟨c.values.length - 1, by omega⟩ := by
      apply Fin.ext
      simp only [e, Fin.val_cast, m]
    change c.values.get (e ⟨m, by omega⟩) = voseNumber k
    rw [helast]
    exact hh
  have hof : List.ofFn d = c.values := by
    have hcongr := List.ofFn_congr hlen c.values.get
    exact (by simpa only [d, e] using hcongr.symm.trans (List.ofFn_get c.values))
  calc
    hAlpha alpha (voseNumber k) ≤ valueChainEnergy alpha d :=
      hAlpha_le_valueChainEnergy halpha.le (voseNumber_pos k).ne' d hdmem hdmono hd0 hdlast
    _ = listRelativeEnergy alpha c.values := by
      rw [← listRelativeEnergy_ofFn, hof]
    _ ≤ globalRelativeBound alpha := hc

end

end Vose1099

end

namespace Vose1099
open Filter Finset Real

private theorem nth_ordered {n i : ℕ} (hn : n ≠ 0) (hi : i < n.divisors.card) :
    Nat.nth (· ∣ n) i = orderedDivisor n ⟨i,hi⟩ := by
  classical
  have hf : (Set.ofPred (· ∣ n)).Finite := by
    apply (n.divisors.finite_toSet).subset
    intro d hd
    exact Nat.mem_divisors.mpr ⟨hd, hn⟩
  have he : hf.toFinset = n.divisors := by ext d; simp [hn]
  have hfi : i < hf.toFinset.card := he.symm ▸ hi
  rw [Nat.nth_eq_orderEmbOfFin hf hfi]
  unfold orderedDivisor
  have congEmb (A B : Finset ℕ) (heq : A = B) (hiA : i < A.card) (hiB : i < B.card) :
      A.orderEmbOfFin rfl ⟨i,hiA⟩ = B.orderEmbOfFin rfl ⟨i,hiB⟩ := by subst B; rfl
  exact congEmb _ _ he _ _

private theorem ratio_cost (r : ℝ) (hr : 1 ≤ r) : r ≤ 1 + log r + (r-1)^2 := by
  have hp : 0 < r := by linarith
  have h := one_sub_inv_le_log_of_pos hp
  have h2 : r-1-(1-r⁻¹) = (r-1)^2 / r := by field_simp <;> ring
  have h3 : (r-1)^2/r ≤ (r-1)^2 := div_le_self (sq_nonneg _) hr
  linarith

private theorem compare_ratio (n : ℕ) (hn : n ≠ 0) :
    ∑ i : Fin (n.divisors.card-1), ((Nat.nth (· ∣ n) (i+1) : ℝ) / Nat.nth (· ∣ n) i) -
      n.divisors.card - log n ≤ hAlpha 2 n := by
  let k := n.divisors.card-1
  let v := extendedDivisorValue n hn
  let r := fun i : ℕ => v (i+1)/v i
  have pos (i : ℕ) : 0 < v i := extendedDivisorValue_pos n hn i
  have hcard := card_divisors_pos hn
  have hr (i : ℕ) : 1 ≤ r i := (one_le_div (pos i)).mpr
    (extendedDivisorValue_monotone n hn (Nat.le_succ i))
  have nth (i : ℕ) (hi : i < n.divisors.card) : (Nat.nth (· ∣ n) i : ℝ) = v i := by
    rw [nth_ordered hn hi]; exact (extendedDivisorValue_eq n hn hi).symm
  have he : (∑ i : Fin (n.divisors.card-1), ((Nat.nth (· ∣ n) (i+1) : ℝ) / Nat.nth (· ∣ n) i)) =
      ∑ i ∈ range k, r i := by
    rw [← Fin.sum_univ_eq_sum_range r]
    apply sum_congr rfl
    intro i _
    change (Nat.nth (· ∣ n) (i.val+1) : ℝ) / Nat.nth (· ∣ n) i.val = _
    rw [nth _ (by omega),nth _ (by omega)]
  have hz : v 0 = 1 := by
    rw [show v 0 = _ from extendedDivisorValue_eq n hn hcard,orderedDivisor_zero hn]
    norm_num
  have hk : v k = n := by
    rw [show v k = _ from extendedDivisorValue_eq n hn (show k < _ by dsimp [k];omega),orderedDivisor_last hn]
  have htel : (∑ i ∈ range k, log (r i)) = log n := by
    calc _ = ∑ i ∈ range k, (log (v (i+1))-log (v i)) :=
          sum_congr rfl fun i _ => log_div (pos _).ne' (pos _).ne'
      _ = _ := by rw [sum_range_sub (fun j => log (v j)),hk,hz,log_one,sub_zero]
  have hh : hAlpha 2 n = ∑ i ∈ range k, (r i-1)^2 := by
    rw [hAlpha_eq_sum_range_extended _ _ hn]
    simp [k,r,v,relativeGap]
  have hb := sum_le_sum (s := range k) (fun i _ => ratio_cost (r i) (hr i))
  simp only [sum_add_distrib, htel, sum_const, card_range, nsmul_eq_mul, mul_one] at hb
  rw [he,hh]
  have hsmall : (k:ℝ) ≤ n.divisors.card := by exact_mod_cast Nat.sub_le n.divisors.card 1
  linarith
end Vose1099

open Filter Real Vose1099 in
theorem OMA.solution : type_of% @Erdos1099.erdos_1099.variants.ratio_sum := by
  refine ⟨globalRelativeBound 2, ?_⟩
  rw [frequently_atTop]
  intro N
  obtain ⟨K,hK⟩ := (tendsto_atTop_atTop.mp voseNumber_tendsto_atTop) N
  let k := max K 3
  exact ⟨voseNumber k,hK _ (le_max_left ..),
    (compare_ratio _ (voseNumber_ne_zero k)).trans
      (hAlpha_voseNumber_le_globalRelativeBound (by norm_num) (le_max_right ..))⟩
