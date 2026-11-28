import FormalConjectures.ErdosProblems.«912»
import Mathlib

/-!
Reduction of Erdős Problem 912 (the open asymptotic `h n ~ c (n / log n)^(1/2)`) to two
statements purely about primes. Let `D n` be the number of distinct values `n / p` over the
primes `p ≤ n` with `n < p * p`. Large primes have exponent `n / p` in `n!`, so
`D n ≤ h n ≤ D n + π(√n)` and `π(√n) = o((n / log n)^(1/2))` (Chebyshev). The upper bound
`D n = O((n / log n)^(1/2))` is proved here from Chebyshev's bound. Given the lower bound `H1`
(the lower half of the Erdős–Selfridge theorem, phrased for `D`) and the convergence statement
`H2` (liminf = limsup of `D n / (n / log n)^(1/2)`), the ratio converges to a positive limit,
which is the problem.
-/

open Finset Filter Asymptotics
open scoped Topology

namespace OMA.R_Erdos912_erdos_912_R2

/-- `D n` for large primes is the image of `p ↦ n / p`; the lower half of Erdős–Selfridge. -/
def H1 : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
    c * ((n : ℝ) / Real.log n) ^ (1 / 2 : ℝ) ≤
      ((((Finset.range (n + 1)).filter (fun p => p.Prime ∧ n < p * p)).image
        (fun p => n / p)).card : ℝ)

/-- The normalized count of distinct values `n / p` over primes `p ∈ (√n, n]` has no oscillation. -/
def H2 : Prop :=
  Filter.liminf (fun n : ℕ => ((((Finset.range (n + 1)).filter
      (fun p => p.Prime ∧ n < p * p)).image (fun p => n / p)).card : ℝ) /
        ((n : ℝ) / Real.log n) ^ (1 / 2 : ℝ)) atTop =
  Filter.limsup (fun n : ℕ => ((((Finset.range (n + 1)).filter
      (fun p => p.Prime ∧ n < p * p)).image (fun p => n / p)).card : ℝ) /
        ((n : ℝ) / Real.log n) ^ (1 / 2 : ℝ)) atTop

theorem factorization_of_large_prime {p n : ℕ} (hp : p.Prime) (hn : n < p * p) :
    n.factorial.factorization p = n / p := by
  have hl : Nat.log p n < 2 := Nat.log_lt_of_lt_pow' (by decide) (by simpa [pow_two] using hn)
  rw [Nat.factorization_factorial hp hl]
  norm_num

theorem log_le_sqrt {x : ℝ} (hx : 0 < x) : Real.log x ≤ √x := by
  have h : 0 < √x / 2 := by positivity
  have heq : Real.log (√x / 2) = Real.log x / 2 - Real.log 2 := by
    rw [Real.log_div (by positivity) (by norm_num), Real.log_sqrt hx.le]
  linarith only [Real.log_le_sub_one_of_pos h, heq, Real.log_two_lt_d9]

theorem prime_count_upper {x : ℝ} (hx : 1 < x) :
    (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ 5 * x / Real.log x := by
  have hx' : 0 < x := zero_lt_one.trans hx
  have hl : 0 < Real.log x := Real.log_pos hx
  have hroot : √x ≤ x / Real.log x := by
    apply (le_div_iff₀ hl).2
    calc
      _ ≤ √x * √x := mul_le_mul_of_nonneg_left (log_le_sqrt hx') (Real.sqrt_nonneg _)
      _ = x := by rw [← pow_two, Real.sq_sqrt hx'.le]
  have hp := Chebyshev.pi_le_log4_mul_div hx
  rw [Real.log_sqrt hx'.le] at hp
  have hl4 : Real.log 4 ≤ 2 := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num, Real.log_pow]
    norm_num
    linarith only [Real.log_two_lt_d9]
  have he : Real.log 4 * x / (Real.log x / 2) = (2 * Real.log 4) * (x / Real.log x) := by ring
  rw [he] at hp
  have hmul := mul_le_mul_of_nonneg_right (show 2 * Real.log 4 ≤ 4 by linarith only [hl4])
    (div_nonneg hx'.le hl.le)
  rw [mul_div_assoc]
  linarith only [hp, hroot, hmul]

section Transfer

variable {D : ℕ → ℕ}
  (hD : ∀ n, D n = (((Finset.range (n + 1)).filter
    (fun p => p.Prime ∧ n < p * p)).image (fun p => n / p)).card)
include hD

theorem D_le_h (n : ℕ) : D n ≤ Erdos912.h n := by
  rw [hD]
  classical
  unfold Erdos912.h
  apply card_le_card
  intro k hk
  obtain ⟨p, hp, rfl⟩ := mem_image.1 hk
  obtain ⟨hpr, hprime, hpn⟩ := mem_filter.1 hp
  have hle : p ≤ n := Nat.lt_succ_iff.1 (mem_range.1 hpr)
  exact Finsupp.mem_frange.2 ⟨(Nat.div_pos hle hprime.pos).ne', p,
    factorization_of_large_prime hprime hpn⟩

theorem h_le_D_add (n : ℕ) : Erdos912.h n ≤ D n + Nat.primeCounting (Nat.sqrt n) := by
  classical
  let e := n.factorial.factorization
  let S := ((Finset.range (n + 1)).filter (fun p => p.Prime ∧ n < p * p)).image (fun p => n / p)
  have hs : e.frange ⊆ S ∪ (Nat.primesLE (Nat.sqrt n)).image e := by
    intro k hk
    obtain ⟨hk0, p, rfl⟩ := Finsupp.mem_frange.1 hk
    have hpprime : p.Prime := by
      by_contra h
      exact hk0 (Nat.factorization_eq_zero_of_not_prime _ h)
    by_cases hpp : n < p * p
    · have hv : e p = n / p := factorization_of_large_prime hpprime hpp
      have hpn : p ≤ n := by
        by_contra h
        exact hk0 (by rw [hv]; exact Nat.div_eq_of_lt (by omega))
      refine mem_union_left _ (mem_image.2 ⟨p, mem_filter.2 ⟨mem_range.2 (by omega),
        hpprime, hpp⟩, hv.symm⟩)
    · refine mem_union_right _ (mem_image_of_mem e (Nat.mem_primesLE.2 ⟨?_, hpprime⟩))
      exact Nat.le_sqrt.2 (by omega)
  calc
    Erdos912.h n = e.frange.card := rfl
    _ ≤ (S ∪ (Nat.primesLE (Nat.sqrt n)).image e).card := card_le_card hs
    _ ≤ S.card + ((Nat.primesLE (Nat.sqrt n)).image e).card := card_union_le _ _
    _ ≤ S.card + (Nat.primesLE (Nat.sqrt n)).card := Nat.add_le_add_left card_image_le _
    _ = D n + Nat.primeCounting (Nat.sqrt n) := by
      rw [Nat.primesLE_card_eq_primeCounting, hD]

theorem D_upper : ∀ᶠ n : ℕ in atTop,
    (D n : ℝ) ≤ 12 * ((n : ℝ) / Real.log n) ^ (1 / 2 : ℝ) := by
  classical
  filter_upwards [eventually_ge_atTop 3] with n hn
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  set L := Real.log (n : ℝ) with hLdef
  have hL1 : 1 ≤ L := by
    rw [hLdef, Real.le_log_iff_exp_le hn0]
    linarith [Real.exp_one_lt_d9]
  have hL0 : 0 < L := by linarith
  set X := √((n : ℝ) * L) with hXdef
  set Y := √((n : ℝ) / L) with hYdef
  have hY0 : 0 < Y := Real.sqrt_pos.2 (div_pos hn0 hL0)
  have hXY : X = Y * L := by
    rw [hXdef, hYdef, show (n : ℝ) * L = ((n : ℝ) / L) * L ^ 2 by field_simp,
      Real.sqrt_mul (div_nonneg hn0.le hL0.le), Real.sqrt_sq hL0.le]
  have hXYn : X * Y = n := by
    rw [hXdef, hYdef, ← Real.sqrt_mul (by positivity), show (n : ℝ) * L * ((n : ℝ) / L) = n ^ 2 by
      field_simp, Real.sqrt_sq hn0.le]
  have hY1 : 1 ≤ Y := by
    rw [hYdef]
    apply Real.one_le_sqrt.2
    rw [le_div_iff₀ hL0, one_mul]
    linarith [Real.log_le_sub_one_of_pos hn0]
  have hX0 : 0 < X := by rw [hXY]; positivity
  have hX1 : 1 < X := by rw [hXY]; nlinarith
  let S := (Finset.range (n + 1)).filter (fun p => p.Prime ∧ n < p * p)
  have hs : S.image (fun p => n / p) ⊆
      (Nat.primesLE ⌊X⌋₊).image (fun p => n / p) ∪ Finset.range (⌊Y⌋₊ + 1) := by
    intro k hk
    obtain ⟨p, hp, rfl⟩ := mem_image.1 hk
    obtain ⟨-, hprime, -⟩ := mem_filter.1 hp
    by_cases hpX : p ≤ ⌊X⌋₊
    · exact mem_union_left _ (mem_image_of_mem _ (Nat.mem_primesLE.2 ⟨hpX, hprime⟩))
    · have hXp : X < (p : ℝ) := (Nat.floor_lt hX0.le).1 (lt_of_not_ge hpX)
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
      have hval : ((n / p : ℕ) : ℝ) ≤ Y := by
        have h1 : ((n / p : ℕ) : ℝ) * p ≤ n := by exact_mod_cast Nat.div_mul_le_self n p
        have h2 : (n : ℝ) ≤ Y * p := by
          rw [← hXYn, mul_comm X]; exact mul_le_mul_of_nonneg_left hXp.le hY0.le
        exact le_of_mul_le_mul_right (h1.trans h2) hp0
      exact mem_union_right _ (mem_range.2 (Nat.lt_succ_of_le ((Nat.le_floor_iff hY0.le).2 hval)))
  have hcard : D n ≤ Nat.primeCounting ⌊X⌋₊ + (⌊Y⌋₊ + 1) := by
    rw [hD]
    calc
      _ ≤ _ := card_le_card hs
      _ ≤ _ := card_union_le _ _
      _ ≤ (Nat.primesLE ⌊X⌋₊).card + (⌊Y⌋₊ + 1) := by
        rw [card_range]; exact Nat.add_le_add_right card_image_le _
      _ = _ := by rw [Nat.primesLE_card_eq_primeCounting]
  have hcardR : (D n : ℝ) ≤ (Nat.primeCounting ⌊X⌋₊ : ℝ) + (⌊Y⌋₊ : ℝ) + 1 := by
    have := (Nat.cast_le (α := ℝ)).2 hcard
    push_cast at this
    linarith
  have hpi := prime_count_upper hX1
  have hlogX : L / 2 ≤ Real.log X := by
    rw [hXdef, Real.log_sqrt (by positivity), Real.log_mul hn0.ne' hL0.ne']
    have : 0 ≤ Real.log L := Real.log_nonneg hL1
    linarith
  have hpi2 : 5 * X / Real.log X ≤ 10 * Y := by
    rw [div_le_iff₀ (by linarith)]
    have := mul_le_mul_of_nonneg_left hlogX (show (0 : ℝ) ≤ 10 * Y by positivity)
    have hX5 : 5 * X = 10 * Y * (L / 2) := by rw [hXY]; ring
    linarith
  have hg : ((n : ℝ) / L) ^ (1 / 2 : ℝ) = Y := (Real.sqrt_eq_rpow _).symm
  rw [hg]
  linarith [Nat.floor_le hY0.le]

end Transfer

theorem small_isLittleO :
    (fun n : ℕ => (Nat.primeCounting (Nat.sqrt n) : ℝ)) =o[atTop]
      (fun n : ℕ => ((n : ℝ) / Real.log n) ^ (1 / 2 : ℝ)) := by
  rw [isLittleO_iff]
  intro ε hε
  have hLtop : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hLtop.eventually_ge_atTop ((10 / ε) ^ 2 + 1),
    eventually_ge_atTop (2 : ℕ)] with n hL hn
  set L := Real.log (n : ℝ) with hLdef
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hL1 : 1 ≤ L := by nlinarith [sq_nonneg (10 / ε)]
  have hL0 : 0 < L := by linarith
  have hsq : (10 / ε) ^ 2 ≤ L := by linarith
  let Y := √((n : ℝ) / L)
  let Z := √(n : ℝ)
  let E := √L
  have hY0 : 0 < Y := Real.sqrt_pos.2 (div_pos hn0 hL0)
  have hE0 : 0 < E := Real.sqrt_pos.2 hL0
  have hZY : Z = Y * E := by
    dsimp only [Z, Y, E]
    rw [← Real.sqrt_mul (div_nonneg hn0.le hL0.le), div_mul_cancel₀ _ hL0.ne']
  have hE2 : E ^ 2 = L := Real.sq_sqrt hL0.le
  have hEge : 10 / ε ≤ E := Real.le_sqrt_of_sq_le hsq
  have hZ1 : 1 < Z := by
    have : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
    simpa [Z] using Real.sqrt_lt_sqrt (by norm_num) this
  have hfl : ⌊Z⌋₊ = Nat.sqrt n := Real.nat_floor_real_sqrt_eq_nat_sqrt
  have hb := prime_count_upper hZ1
  rw [hfl, show Real.log Z = L / 2 from Real.log_sqrt hn0.le] at hb
  have hg : ((n : ℝ) / L) ^ (1 / 2 : ℝ) = Y := (Real.sqrt_eq_rpow _).symm
  rw [Real.norm_of_nonneg (by positivity), hg, Real.norm_of_nonneg hY0.le]
  refine hb.trans ?_
  rw [hZY]
  apply (div_le_iff₀ (by positivity : 0 < L / 2)).2
  have h10 : 10 ≤ ε * E := by
    have := mul_le_mul_of_nonneg_left hEge hε.le
    rwa [mul_div_cancel₀ _ hε.ne'] at this
  have : 10 * E ≤ ε * L := by
    rw [← hE2]; nlinarith [mul_le_mul_of_nonneg_right h10 hE0.le]
  nlinarith [mul_le_mul_of_nonneg_left this hY0.le]

theorem equiv_iff {D : ℕ → ℕ}
    (hD : ∀ n, D n = (((Finset.range (n + 1)).filter
      (fun p => p.Prime ∧ n < p * p)).image (fun p => n / p)).card) {c : ℝ} (hc : 0 < c) :
    (fun n => (D n : ℝ)) ~[atTop] (fun n => c * ((n : ℝ) / Real.log n) ^ (1 / 2 : ℝ)) →
    (fun n => (Erdos912.h n : ℝ)) ~[atTop]
      (fun n => c * ((n : ℝ) / Real.log n) ^ (1 / 2 : ℝ)) := by
  intro hd
  have ho : (fun n : ℕ => (Erdos912.h n : ℝ) - (D n : ℝ)) =o[atTop]
      (fun n => c * ((n : ℝ) / Real.log n) ^ (1 / 2 : ℝ)) := by
    refine IsBigO.trans_isLittleO (IsBigO.of_bound 1 (Eventually.of_forall fun n => ?_))
      (small_isLittleO.trans_isBigO (isBigO_self_const_mul hc.ne' _ _))
    have h1 : (D n : ℝ) ≤ Erdos912.h n := by exact_mod_cast D_le_h hD n
    have h2 : (Erdos912.h n : ℝ) ≤ D n + Nat.primeCounting (Nat.sqrt n) := by
      exact_mod_cast h_le_D_add hD n
    rw [Real.norm_of_nonneg (by linarith), Real.norm_of_nonneg (by positivity)]
    linarith
  have := hd.add_isLittleO ho
  refine this.congr_left (Eventually.of_forall fun n => ?_)
  simp

theorem main : H1 → H2 → type_of% @Erdos912.erdos_912 := by
  intro hlow hconv
  obtain ⟨c, hc, hlow⟩ := hlow
  set D : ℕ → ℕ := fun n => (((Finset.range (n + 1)).filter
    (fun p => p.Prime ∧ n < p * p)).image (fun p => n / p)).card with hDdef
  have hD : ∀ n, D n = (((Finset.range (n + 1)).filter
      (fun p => p.Prime ∧ n < p * p)).image (fun p => n / p)).card := fun n => rfl
  set g : ℕ → ℝ := fun n => ((n : ℝ) / Real.log n) ^ (1 / 2 : ℝ) with hg
  set r : ℕ → ℝ := fun n => (D n : ℝ) / g n with hr
  have hgpos : ∀ᶠ n : ℕ in atTop, 0 < g n := by
    filter_upwards [eventually_ge_atTop 3] with n hn
    have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
    have hl : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
    exact Real.rpow_pos_of_pos (div_pos (by linarith) hl) _
  have hup : ∀ᶠ n : ℕ in atTop, r n ≤ 12 := by
    filter_upwards [D_upper hD, hgpos] with n h1 h2
    exact (div_le_iff₀ h2).2 h1
  have hlo : ∀ᶠ n : ℕ in atTop, c ≤ r n := by
    filter_upwards [hlow, hgpos] with n h1 h2
    exact (le_div_iff₀ h2).2 h1
  have hT : Tendsto r atTop (𝓝 (Filter.limsup r atTop)) :=
    tendsto_of_liminf_eq_limsup hconv rfl (isBoundedUnder_of_eventually_le hup)
      (isBoundedUnder_of_eventually_ge hlo)
  set L := Filter.limsup r atTop with hL
  have hcL : c ≤ L := ge_of_tendsto hT hlo
  have hL0 : 0 < L := hc.trans_le hcL
  refine ⟨L, hL0, equiv_iff hD hL0 ?_⟩
  apply isEquivalent_of_tendsto_one
  have h1 : Tendsto (fun n => r n / L) atTop (𝓝 1) := by
    simpa [div_self hL0.ne'] using hT.div_const L
  refine h1.congr' ?_
  filter_upwards [hgpos] with n hn
  simp only [Pi.div_apply, hr]
  rw [div_div, mul_comm]

end OMA.R_Erdos912_erdos_912_R2
