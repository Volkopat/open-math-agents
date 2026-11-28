import FormalConjectures.ErdosProblems.«394»
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Tactic

/-!
Disproof of the strong Erdős–Hall average-order conjecture.

The prime-times-squarefree-cofactor construction is from Pickhardt and
the Paratelligent Research Agent, Erdős Problem 394 and the average order
of t_2: a counterexample to the strong form.
https://paratelligent.com/research/papers/erdos-problem-394-and-the-average-order-of-t-2-a-counterexample-6CWZNbA5

This proof uses Chebyshev bounds, a finite Selberg sieve with a bounded
remainder, and a finite product over prime subsets to bound cofactor mass.
-/



/- Local work on the claimed refutation of the strong Erdős–Hall conjecture. -/

open Filter Finset
open scoped Asymptotics Topology Nat

namespace Hall394

theorem least_start_spec {n : ℕ} (hn : 0 < n) :
    0 < Erdos394.t 2 n ∧ n ∣ Erdos394.t 2 n * (Erdos394.t 2 n + 1) := by
  have hne : {m : ℕ | 0 < m ∧ n ∣ ∏ i ∈ range 2, (m + i)}.Nonempty :=
    ⟨n, hn, by simp [Finset.prod_range_succ]⟩
  have h := Nat.sInf_mem hne
  change 0 < Erdos394.t 2 n ∧ n ∣ ∏ i ∈ range 2, (Erdos394.t 2 n + i) at h
  simpa [Finset.prod_range_succ] using h

theorem prime_factor_lower_bound {p n : ℕ} (hp : p.Prime) (hd : p ∣ n)
    (hn : 0 < n) : p - 1 ≤ Erdos394.t 2 n := by
  obtain ⟨hpos, ht⟩ := least_start_spec hn
  rcases hp.dvd_mul.mp (hd.trans ht) with h | h
  · have := Nat.le_of_dvd hpos h
    omega
  · have := Nat.le_of_dvd (by omega) h
    omega

theorem dvd_consecutive_iff_split (n m : ℕ) :
    n ∣ m * (m + 1) ↔ ∃ a b : ℕ, a * b = n ∧ a.Coprime b ∧ a ∣ m ∧ b ∣ m + 1 := by
  have hcop : m.Coprime (m + 1) := Nat.coprime_self_add_right.mpr (by simp)
  constructor
  · intro h
    exact ⟨n.gcd m, n.gcd (m + 1),
      (Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime hcop).mpr h,
      hcop.gcd_both n n, Nat.gcd_dvd_right _ _, Nat.gcd_dvd_right _ _⟩
  · rintro ⟨a, b, hab, _, ha, hb⟩
    rw [← hab]
    exact Nat.mul_dvd_mul ha hb

theorem large_prime_factorization_unique {a b p q cutoff : ℕ}
    (ha : a.Prime) (hp : p.Prime) (hq : 0 < q)
    (ha' : cutoff < a) (hq' : q ≤ cutoff)
    (h : a * b = p * q) : a = p ∧ b = q := by
  have hd : a ∣ p * q := h ▸ Nat.dvd_mul_right a b
  have hap : a ∣ p := (ha.dvd_mul.mp hd).resolve_right fun h =>
    (not_lt_of_ge ((Nat.le_of_dvd hq h).trans hq')) ha'
  have he : a = p := (hp.eq_one_or_self_of_dvd a hap).resolve_left ha.ne_one
  subst p
  exact ⟨rfl, Nat.mul_left_cancel ha.pos h⟩

theorem large_prime_on_one_side {p b m : ℕ} (hp : p.Prime)
    (h : p * b ∣ m * (m + 1)) :
    ∃ d k : ℕ, k * d = b ∧
      ((p * k ∣ m ∧ d ∣ m + 1) ∨ (p * k ∣ m + 1 ∧ d ∣ m)) := by
  obtain ⟨a, c, hac, _, ha, hc⟩ := (dvd_consecutive_iff_split (p * b) m).mp h
  have hd : p ∣ a * c := hac.symm ▸ Nat.dvd_mul_right p b
  rcases hp.dvd_mul.mp hd with hpa | hpc
  · obtain ⟨k, rfl⟩ := hpa
    exact ⟨c, k, Nat.mul_left_cancel hp.pos (by simpa [Nat.mul_assoc] using hac),
      Or.inl ⟨ha, hc⟩⟩
  · obtain ⟨k, rfl⟩ := hpc
    exact ⟨a, k, Nat.mul_left_cancel hp.pos (by
      calc p * (k * a) = a * (p * k) := by ac_rfl
           _ = p * b := hac), Or.inr ⟨hc, ha⟩⟩

noncomputable def total (x : ℝ) : ℝ :=
  ∑ n ∈ Icc 1 ⌊x⌋₊, (Erdos394.t 2 n : ℝ)

noncomputable def scale (x : ℝ) : ℝ :=
  x ^ 2 / (Real.log x) ^ (2 / 3 : ℝ)

theorem refute_of_frequent_lower_bound
    (h : ∃ d : ℝ, 0 < d ∧ ∃ᶠ x in atTop, d * scale x ≤ total x) :
    ¬ (type_of% @Erdos394.erdos_394.variants.hall_conjecture) := by
  intro hc
  have hlog : (2 / 3 : ℝ) < Real.log 2 :=
    lt_trans (by norm_num) Real.log_two_gt_d9
  have hsmall : total =o[atTop] scale := hc _ hlog
  obtain ⟨d, hd, hlarge⟩ := h
  have hbound := Asymptotics.isLittleO_iff.mp hsmall (show 0 < d / 2 by positivity)
  have hx : ∀ᶠ x : ℝ in atTop, 1 < x := eventually_gt_atTop 1
  obtain ⟨x, ⟨hlarge, hbound⟩, hx⟩ := ((hlarge.and_eventually hbound).and_eventually hx).exists
  have hscale : 0 < scale x := by
    unfold scale
    exact div_pos (by positivity) (Real.rpow_pos_of_pos (Real.log_pos hx) _)
  have htotal : |total x| = total x := abs_of_nonneg (by
    unfold total
    exact Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, htotal, abs_of_pos hscale] at hbound
  exact (not_lt_of_ge (hlarge.trans hbound)) (mul_lt_mul_of_pos_right (by linarith) hscale)

theorem card_mul_le_total {x a : ℝ} {S : Finset ℕ}
    (hsub : S ⊆ Icc 1 ⌊x⌋₊)
    (hlower : ∀ n ∈ S, a ≤ (Erdos394.t 2 n : ℝ)) :
    (S.card : ℝ) * a ≤ total x := by
  calc
    (S.card : ℝ) * a = ∑ _n ∈ S, a := by simp
    _ ≤ ∑ n ∈ S, (Erdos394.t 2 n : ℝ) := Finset.sum_le_sum hlower
    _ ≤ total x := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun n _ _ => Nat.cast_nonneg _)

theorem refute_of_frequently_many_large_starts
    (h : ∃ d : ℝ, 0 < d ∧ ∃ᶠ x in atTop,
      ∃ (S : Finset ℕ) (a : ℝ), S ⊆ Icc 1 ⌊x⌋₊ ∧
        (∀ n ∈ S, a ≤ (Erdos394.t 2 n : ℝ)) ∧
        d * scale x ≤ (S.card : ℝ) * a) :
    ¬ (type_of% @Erdos394.erdos_394.variants.hall_conjecture) := by
  obtain ⟨d, hd, hf⟩ := h
  refine refute_of_frequent_lower_bound ⟨d, hd, hf.mono ?_⟩
  rintro x ⟨S, a, hsub, hlower, hcard⟩
  exact hcard.trans (card_mul_le_total hsub hlower)

theorem refute_of_half_exponent
    (h : ∃ d : ℝ, 0 < d ∧ ∃ᶠ x in atTop,
      d * (x ^ 2 / (Real.log x) ^ (1 / 2 : ℝ)) ≤ total x) :
    ¬ (type_of% @Erdos394.erdos_394.variants.hall_conjecture) := by
  obtain ⟨d, hd, h⟩ := h
  refine refute_of_frequent_lower_bound ⟨d, hd, ?_⟩
  have hx : ∀ᶠ x : ℝ in atTop, 1 ≤ Real.log x :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1)
  refine ((h.and_eventually hx).mono ?_)
  rintro x ⟨hbound, hx⟩
  apply le_trans _ hbound
  apply mul_le_mul_of_nonneg_left _ hd.le
  unfold scale
  have hpow : (Real.log x) ^ (1 / 2 : ℝ) ≤ (Real.log x) ^ (2 / 3 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
  exact div_le_div_of_nonneg_left (sq_nonneg x)
    (Real.rpow_pos_of_pos (by linarith) _) hpow

end Hall394








/- Counting lemmas for the Erdős 394 Hall conjecture. -/

open Filter Finset
open scoped Asymptotics Topology Nat

namespace Hall394Counting

theorem card_sdiff_ge_of_cover {α β : Type*} [DecidableEq α]
    (P : Finset α) (classes : Finset β) (bad : β → Finset α)
    {mass density cap : ℝ}
    (hP : mass ≤ (P.card : ℝ))
    (hclasses : (classes.card : ℝ) ≤ density)
    (hbad : ∀ b ∈ classes, ((P ∩ bad b).card : ℝ) ≤ cap)
    (hcap : 0 ≤ cap) :
    mass - density * cap ≤ ((P \ classes.biUnion bad).card : ℝ) := by
  classical
  have hsub : P ∩ classes.biUnion bad ⊆ classes.biUnion (fun b => P ∩ bad b) := by
    intro a ha
    obtain ⟨hp, hbad⟩ := Finset.mem_inter.mp ha
    obtain ⟨b, hb, ha⟩ := Finset.mem_biUnion.mp hbad
    exact Finset.mem_biUnion.mpr ⟨b, hb, Finset.mem_inter.mpr ⟨hp, ha⟩⟩
  have hbound : ((P ∩ classes.biUnion bad).card : ℝ) ≤ density * cap := by
    calc
      _ ≤ ((classes.biUnion fun b => P ∩ bad b).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
      _ ≤ ∑ b ∈ classes, ((P ∩ bad b).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le (s := classes) (t := fun b => P ∩ bad b)
      _ ≤ ∑ _b ∈ classes, cap := Finset.sum_le_sum hbad
      _ = (classes.card : ℝ) * cap := by simp
      _ ≤ density * cap := mul_le_mul_of_nonneg_right hclasses hcap
  have heq : ((P \ classes.biUnion bad).card : ℝ) +
      ((P ∩ classes.biUnion bad).card : ℝ) = P.card := by
    exact_mod_cast Finset.card_sdiff_add_card_inter P (classes.biUnion bad)
  linarith

theorem weighted_sum_le_of_disjoint {α β : Type*} [DecidableEq α]
    (U : Finset α) (B : Finset β) (S : β → Finset α) (f : α → ℝ)
    (weight : β → ℝ) (hdisj : (B : Set β).PairwiseDisjoint S)
    (hsub : ∀ b ∈ B, S b ⊆ U)
    (hf : ∀ a ∈ U, 0 ≤ f a)
    (hweight : ∀ b ∈ B, ∀ a ∈ S b, weight b ≤ f a) :
    ∑ b ∈ B, ((S b).card : ℝ) * weight b ≤ ∑ a ∈ U, f a := by
  classical
  calc
    _ ≤ ∑ b ∈ B, ∑ a ∈ S b, f a := by
      apply Finset.sum_le_sum
      intro b hb
      calc
        _ = ∑ _a ∈ S b, weight b := by simp
        _ ≤ ∑ a ∈ S b, f a := Finset.sum_le_sum (hweight b hb)
    _ = ∑ a ∈ B.biUnion S, f a := (Finset.sum_biUnion hdisj).symm
    _ ≤ ∑ a ∈ U, f a := by
      apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun a ha _ => hf a ha)
      intro a ha
      obtain ⟨b, hb, hab⟩ := Finset.mem_biUnion.mp ha
      exact hsub b hb hab

theorem eventually_loglog_le_log_rpow :
    ∀ᶠ x : ℝ in atTop, Real.log (Real.log x) ≤ (Real.log x) ^ (1 / 6 : ℝ) := by
  have h := Asymptotics.IsLittleO.comp_tendsto (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / 6 by norm_num)) Real.tendsto_log_atTop
  have hbound := Asymptotics.isLittleO_iff.mp h (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [hbound, eventually_gt_atTop (1 : ℝ)] with x hx h1
  change ‖Real.log (Real.log x)‖ ≤ 1 * ‖(Real.log x) ^ (1 / 6 : ℝ)‖ at hx
  rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (Real.log_pos h1) _)] at hx
  exact (le_abs_self _).trans hx

theorem eventually_chebyshev_lower :
    ∀ᶠ x : ℝ in atTop, x / (2 * Real.log x) ≤ (Nat.primeCounting ⌊x⌋₊ : ℝ) := by
  have hlog := Asymptotics.isLittleO_iff.mp Real.isLittleO_log_id_atTop
    (show (0 : ℝ) < 1 / 24 by norm_num)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hlog
  filter_upwards [eventually_ge_atTop (max N 24)] with x hx
  have h24 : 24 ≤ x := (le_max_right _ _).trans hx
  have hx1 : 1 < x := by linarith
  have hlogsmall := hN (x + 2) (by linarith [le_trans (le_max_left N 24) hx])
  change ‖Real.log (x + 2)‖ ≤ 1 / 24 * ‖x + 2‖ at hlogsmall
  simp only [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ x + 2 by linarith)] at hlogsmall
  have hlogsmall' : Real.log (x + 2) ≤ (x + 2) / 24 := by
    linarith [le_abs_self (Real.log (x + 2))]
  have htwo : (2/3 : ℝ) ≤ Real.log 2 := le_trans (by norm_num) Real.log_two_gt_d9.le
  have hmul := mul_le_mul_of_nonneg_left htwo (show 0 ≤ x - 1 by linarith)
  have hnum : x / 2 ≤ (x - 1) * Real.log 2 - Real.log (x + 2) := by linarith
  calc
    x / (2 * Real.log x) = (x / 2) / Real.log x := by ring
    _ ≤ _ := (div_le_div_of_nonneg_right hnum (Real.log_pos hx1).le).trans
      (Chebyshev.pi_ge' hx1)

theorem eventually_chebyshev_interval :
    ∀ᶠ x : ℝ in atTop, x / (4 * Real.log x) ≤
      (Nat.primeCounting ⌊x⌋₊ : ℝ) - Nat.primeCounting ⌊x / 16⌋₊ := by
  have ht : Tendsto (fun x : ℝ => x / 16) atTop atTop := by
    simpa [div_eq_mul_inv, mul_comm] using
      (tendsto_const_mul_atTop_of_pos (show (0 : ℝ) < 16⁻¹ by norm_num)).2 tendsto_id
  have hup := ht.eventually (Chebyshev.eventually_primeCounting_le
    (show (0 : ℝ) < 1 / 2 by norm_num))
  filter_upwards [eventually_chebyshev_lower, hup, eventually_ge_atTop (256 : ℝ)] with x hl hu hx
  have hy : 16 ≤ x / 16 := by linarith
  have hlogy : 0 < Real.log (x / 16) := Real.log_pos (by linarith)
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hlogcmp : Real.log x ≤ 2 * Real.log (x / 16) := by
    calc
      Real.log x = Real.log 16 + Real.log (x / 16) := by
        rw [← Real.log_mul (by norm_num : (16 : ℝ) ≠ 0) (by linarith : x / 16 ≠ 0)]
        congr 1
        ring
      _ ≤ _ := by linarith [Real.log_le_log (by norm_num : 0 < (16 : ℝ)) hy]
  have hlog4 : Real.log 4 + 1 / 2 ≤ 2 := by
    have heq : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
      ring
    linarith [Real.log_two_lt_d9]
  have hu' : (Nat.primeCounting ⌊x / 16⌋₊ : ℝ) ≤ x / (4 * Real.log x) := by
    apply hu.trans
    have hlhs : (Real.log 4 + 1 / 2) * (x / 16) ≤ x / 8 := by
      linarith [mul_le_mul_of_nonneg_right hlog4 (show 0 ≤ x / 16 by linarith)]
    calc
      _ ≤ (x / 8) / Real.log (x / 16) :=
        div_le_div_of_nonneg_right hlhs hlogy.le
      _ ≤ _ := by
        rw [div_le_div_iff₀ hlogy (by positivity : 0 < 4 * Real.log x)]
        linarith [mul_le_mul_of_nonneg_left hlogcmp (show 0 ≤ x by linarith)]
  have heq : x / (2 * Real.log x) = 2 * (x / (4 * Real.log x)) := by ring
  linarith

noncomputable def primeWindow (N : ℕ) : Finset ℕ :=
  Nat.primesLE (N-1) \ Nat.primesLE ⌊(N : ℝ)/16⌋₊

theorem eventually_primeWindow_card :
    ∀ᶠ N : ℕ in atTop,
      (N : ℝ) / (8 * Real.log N) ≤ ((primeWindow N).card : ℝ) := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hinterval := ht.eventually eventually_chebyshev_interval
  have hlog := ht.eventually ((Asymptotics.isLittleO_iff.mp Real.isLittleO_log_id_atTop
    (show (0 : ℝ) < 1/8 by norm_num)))
  filter_upwards [hinterval, hlog, eventually_ge_atTop (16 : ℕ)] with N hi hl hN
  have hsub : Nat.primesLE ⌊(N : ℝ)/16⌋₊ ⊆ Nat.primesLE (N-1) :=
    Nat.primesLE_mono (Nat.floor_le_of_le (by push_cast [Nat.cast_sub (by omega : 1 ≤ N)]; linarith [show (16 : ℝ) ≤ N by exact_mod_cast hN]))
  have hdiff : ((primeWindow N).card : ℝ) =
      (Nat.primeCounting (N-1) : ℝ) - Nat.primeCounting ⌊(N : ℝ)/16⌋₊ := by
    unfold primeWindow
    rw [Finset.card_sdiff_of_subset hsub, Nat.cast_sub (Finset.card_le_card hsub)]
    simp
  have hstep : (Nat.primeCounting N : ℝ) ≤ Nat.primeCounting (N-1) + 1 := by
    have hsubset : Nat.primesLE N ⊆ insert N (Nat.primesLE (N-1)) := by
      intro p hp
      obtain ⟨hle,hp⟩ := Nat.mem_primesLE.mp hp
      rcases eq_or_lt_of_le hle with rfl | hlt
      · simp
      · exact Finset.mem_insert_of_mem (Nat.mem_primesLE.mpr ⟨by omega,hp⟩)
    have hnat := (Finset.card_le_card hsubset).trans (Finset.card_insert_le _ _)
    simp only [Nat.primesLE_card_eq_primeCounting] at hnat
    exact_mod_cast hnat
  have hLN : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hN0 : 0 ≤ (N : ℝ) := Nat.cast_nonneg _
  have hOne : 1 ≤ (N : ℝ) / (8 * Real.log N) := by
    change ‖Real.log (N : ℝ)‖ ≤ 1/8 * ‖(N : ℝ)‖ at hl
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hLN, abs_of_nonneg hN0] at hl
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hi' : (N : ℝ) / (4 * Real.log N) ≤
      (Nat.primeCounting N : ℝ) - Nat.primeCounting ⌊(N : ℝ)/16⌋₊ := by
    simpa only [Nat.floor_natCast] using hi
  rw [hdiff]
  linarith only [hstep, hOne, hi',
    show (N : ℝ) / (4 * Real.log N) = 2 * ((N : ℝ) / (8 * Real.log N)) by ring]

end Hall394Counting










/- Remainder bounds for the Selberg sieve on an arithmetic progression. -/
open Finset

namespace Hall394Progression

def residue (N d r : ℕ) : Finset ℕ :=
  (range N).filter fun n => n % d = r

theorem residue_card_bounds {N d r : ℕ} (hr : r < d) :
    N / d ≤ (residue N d r).card ∧ (residue N d r).card ≤ N / d + 1 := by
  have hd : 0 < d := by omega
  constructor
  · rw [← Finset.card_range (N / d)]
    apply Finset.card_le_card_of_injOn (fun k => d * k + r)
    · intro k hk
      change k ∈ range (N / d) at hk
      change d * k + r ∈ residue N d r
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr ?_, by simp [Nat.mod_eq_of_lt hr]⟩
      have hb := Nat.mul_le_mul_left d (Nat.succ_le_of_lt (Finset.mem_range.mp hk))
      have hN := Nat.mul_div_le N d
      rw [Nat.mul_succ] at hb
      omega
    · intro k _ l _ h
      change d * k + r = d * l + r at h
      exact Nat.mul_left_cancel hd (Nat.add_right_cancel h)
  · rw [← Finset.card_range (N / d + 1)]
    apply Finset.card_le_card_of_injOn (fun n => n / d)
    · intro n hn
      change n ∈ residue N d r at hn
      change n / d ∈ range (N / d + 1)
      have hnN := Finset.mem_range.mp (Finset.mem_filter.mp hn).1
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right hnN.le))
    · intro n hn m hm h
      change n ∈ residue N d r at hn
      change m ∈ residue N d r at hm
      change n / d = m / d at h
      have hnR := (Finset.mem_filter.mp hn).2
      have hmR := (Finset.mem_filter.mp hm).2
      change n % d = r at hnR
      change m % d = r at hmR
      calc
        n = n % d + d * (n / d) := (Nat.mod_add_div n d).symm
        _ = m % d + d * (m / d) := by rw [hnR, hmR, h]
        _ = m := Nat.mod_add_div m d

theorem progression_divisibility_residue (q d a : ℕ) (hq : 0 < q) (hd : 0 < d)
    (hcop : q.Coprime d) :
    ∃ r < q * d, ∀ n : ℕ, n % q = a % q ∧ d ∣ n ↔ n % (q * d) = r := by
  let u := Nat.chineseRemainder hcop a 0
  have hu : (u : ℕ) < q * d := Nat.chineseRemainder_lt_mul hcop a 0 hq.ne' hd.ne'
  refine ⟨u, hu, ?_⟩
  intro n
  change (n ≡ a [MOD q]) ∧ d ∣ n ↔ n % (q * d) = (u : ℕ)
  rw [← Nat.modEq_zero_iff_dvd]
  constructor
  · rintro ⟨ha, hz⟩
    have h := Nat.chineseRemainder_modEq_unique hcop ha hz
    change n % (q * d) = (u : ℕ) % (q * d) at h
    simpa only [Nat.mod_eq_of_lt hu] using h
  · intro h
    have h' : n ≡ (u : ℕ) [MOD q * d] := by
      change n % (q * d) = (u : ℕ) % (q * d)
      rw [Nat.mod_eq_of_lt hu]
      exact h
    exact ⟨(h'.of_dvd (Nat.dvd_mul_right q d)).trans u.2.1,
      (h'.of_dvd (Nat.dvd_mul_left d q)).trans u.2.2⟩

theorem progression_mult_count {N q d a : ℕ} (hq : 0 < q) (hd : 0 < d)
    (hcop : q.Coprime d) :
    N / (q * d) ≤ ((residue N q (a % q)).filter (fun n => d ∣ n)).card ∧
      ((residue N q (a % q)).filter (fun n => d ∣ n)).card ≤ N / (q * d) + 1 := by
  obtain ⟨r, hr, hCRT⟩ := progression_divisibility_residue q d a hq hd hcop
  have heq : (residue N q (a % q)).filter (fun n => d ∣ n) = residue N (q * d) r := by
    ext n
    simp only [residue, Finset.mem_filter, and_assoc, hCRT n]
  rw [heq]
  exact residue_card_bounds hr

theorem abs_progression_error {N q d a : ℕ} (hq : 0 < q) (hd : 0 < d)
    (hcop : q.Coprime d) :
    |(((residue N q (a % q)).filter (fun n => d ∣ n)).card : ℝ) -
      (N : ℝ) / (q * d)| ≤ 1 := by
  let M := q * d
  have hM : 0 < M := Nat.mul_pos hq hd
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have heq : (N : ℝ) = (N % M : ℕ) + (M : ℝ) * (N / M : ℕ) := by
    exact_mod_cast (Nat.mod_add_div N M).symm
  have hmod : (N % M : ℕ) < M := Nat.mod_lt _ hM
  have hmod' : ((N % M : ℕ) : ℝ) < M := by exact_mod_cast hmod
  obtain ⟨hlo, hhi⟩ := progression_mult_count (N := N) (a := a) hq hd hcop
  let C := ((residue N q (a % q)).filter (fun n => d ∣ n)).card
  have hlo' : ((N / M : ℕ) : ℝ) ≤ C := by exact_mod_cast hlo
  have hhi' : (C : ℝ) ≤ ((N / M : ℕ) : ℝ) + 1 := by exact_mod_cast hhi
  have hdivlo : ((N / M : ℕ) : ℝ) ≤ (N : ℝ) / M := by
    rw [le_div_iff₀ hM']
    linarith [Nat.cast_nonneg (α := ℝ) (N % M)]
  have hdivhi : (N : ℝ) / M ≤ ((N / M : ℕ) : ℝ) + 1 := by
    rw [div_le_iff₀ hM']
    nlinarith
  rw [← Nat.cast_mul]
  change |(C : ℝ) - (N : ℝ) / M| ≤ 1
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end Hall394Progression





/- Finite Selberg majorant for primes larger than the weight support. -/

open Finset

namespace Hall394Sieve

noncomputable def countMultiples (A : Finset ℕ) (d : ℕ) : ℝ :=
  (A.filter fun n => d ∣ n).card

theorem prime_count_le_weighted (A : Finset ℕ) (z : ℕ) (hz : 1 ≤ z)
    (w : ℕ → ℝ) (hw : w 1 = 1) :
    ((A.filter fun n => n.Prime ∧ z < n).card : ℝ) ≤
      ∑ d ∈ Icc 1 z, ∑ e ∈ Icc 1 z, w d * w e * countMultiples A (d.lcm e) := by
  let D := Icc 1 z
  let f := fun n : ℕ => ∑ d ∈ D, if d ∣ n then w d else 0
  have hmajor : ((A.filter fun n => n.Prime ∧ z < n).card : ℝ) ≤ ∑ n ∈ A, (f n)^2 := by
    calc
      _ = ∑ n ∈ A, if n.Prime ∧ z < n then (1 : ℝ) else 0 := by
        rw [← Finset.sum_filter]
        simp
      _ ≤ _ := ?_
    apply Finset.sum_le_sum
    intro n _
    split_ifs with h
    · have hf : f n = 1 := by
        dsimp only [f]
        rw [Finset.sum_eq_single 1]
        · simp [hw]
        · intro b hb hne
          have hbz := (Finset.mem_Icc.mp hb).2
          have hn : ¬ b ∣ n := fun hd =>
            ((Nat.dvd_prime h.1).mp hd).elim hne (fun he => (not_lt_of_ge (he ▸ hbz)) h.2)
          simp [hn]
        · simp [D, hz]
      simp [hf]
    · exact sq_nonneg _
  refine hmajor.trans_eq ?_
  calc
    ∑ n ∈ A, (f n)^2 =
        ∑ n ∈ A, ∑ d ∈ D, ∑ e ∈ D,
          if d.lcm e ∣ n then w d * w e else 0 := by
      apply Finset.sum_congr rfl
      intro n _
      rw [pow_two]
      dsimp only [f]
      rw [Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      apply Finset.sum_congr rfl
      intro e _
      by_cases hd : d ∣ n <;> by_cases he : e ∣ n <;> simp [Nat.lcm_dvd_iff, hd, he]
    _ = ∑ d ∈ D, ∑ e ∈ D, ∑ n ∈ A,
          if d.lcm e ∣ n then w d * w e else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d _
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d _
      apply Finset.sum_congr rfl
      intro e _
      rw [← Finset.sum_filter]
      simp [countMultiples, mul_comm]

end Hall394Sieve



/- Uniform control of the error in a finite sieve quadratic form. -/
open Finset

namespace Hall394SieveError

theorem quadratic_le_model {ι : Type*} (D : Finset ι)
    (w : ι → ℝ) (count model : ι → ι → ℝ) (E : ℝ)
    (_hE : 0 ≤ E)
    (herr : ∀ d ∈ D, ∀ e ∈ D, w d ≠ 0 → w e ≠ 0 →
      |count d e - model d e| ≤ E) :
    (∑ d ∈ D, ∑ e ∈ D, w d * w e * count d e) ≤
      (∑ d ∈ D, ∑ e ∈ D, w d * w e * model d e) +
        E * (∑ d ∈ D, |w d|)^2 := by
  have hpoint : ∀ d ∈ D, ∀ e ∈ D,
      w d * w e * count d e ≤ w d * w e * model d e + E * (|w d| * |w e|) := by
    intro d hd e he
    by_cases hwd : w d = 0
    · simp [hwd]
    by_cases hwe : w e = 0
    · simp [hwe]
    have h := calc
      (w d * w e) * (count d e - model d e) ≤
          |(w d * w e) * (count d e - model d e)| := le_abs_self _
      _ = (|w d| * |w e|) * |count d e - model d e| := by simp only [abs_mul]
      _ ≤ (|w d| * |w e|) * E :=
        mul_le_mul_of_nonneg_left (herr d hd e he hwd hwe) (by positivity)
    linarith only [h]
  calc
    _ ≤ ∑ d ∈ D, ∑ e ∈ D,
        (w d * w e * model d e + E * (|w d| * |w e|)) :=
      Finset.sum_le_sum fun d hd => Finset.sum_le_sum (hpoint d hd)
    _ = _ := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, pow_two, Finset.sum_mul_sum]

end Hall394SieveError



/- Diagonalization of the main term for the dimension-one sieve. -/

open Finset

namespace Hall394Weights

theorem sum_totient_gcd {d e z : ℕ} (hd : d ∈ Icc 1 z) :
    ∑ k ∈ Icc 1 z, (if k ∣ d ∧ k ∣ e then (k.totient : ℝ) else 0) =
      (d.gcd e : ℝ) := by
  have hdpos : 0 < d := (mem_Icc.mp hd).1
  have hgpos : 0 < d.gcd e := Nat.gcd_pos_of_pos_left e hdpos
  have hset : (Icc 1 z).filter (fun k => k ∣ d ∧ k ∣ e) = (d.gcd e).divisors := by
    ext k
    simp only [mem_filter, mem_Icc, Nat.mem_divisors]
    refine ⟨fun h => ⟨Nat.dvd_gcd h.2.1 h.2.2, hgpos.ne'⟩, ?_⟩
    rintro ⟨hk, _⟩
    have hkd := hk.trans (Nat.gcd_dvd_left d e)
    have hke := hk.trans (Nat.gcd_dvd_right d e)
    have hkpos := Nat.pos_of_dvd_of_pos hkd hdpos
    exact ⟨⟨hkpos, (Nat.le_of_dvd hdpos hkd).trans (mem_Icc.mp hd).2⟩, hkd, hke⟩
  rw [← Finset.sum_filter, hset]
  exact_mod_cast Nat.sum_totient (d.gcd e)

theorem div_lcm_eq_div_mul_gcd {d e : ℕ} (hd : 0 < d) (he : 0 < e)
    (a b : ℝ) :
    a * b / (d.lcm e : ℝ) = (a / d) * (b / e) * (d.gcd e : ℝ) := by
  have hl : (d.lcm e : ℝ) ≠ 0 := by
    exact_mod_cast Nat.lcm_ne_zero hd.ne' he.ne'
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have he' : (e : ℝ) ≠ 0 := by exact_mod_cast he.ne'
  have h : (d.gcd e : ℝ) * (d.lcm e : ℝ) = d * e := by
    exact_mod_cast Nat.gcd_mul_lcm d e
  field_simp
  calc
    a * b * d * e = (a * b) * (d * e) := by ring
    _ = (a * b) * ((d.gcd e : ℝ) * (d.lcm e : ℝ)) := by rw [h]
    _ = _ := by ring

theorem diagonal_main_term (z : ℕ) (w : ℕ → ℝ) :
    ∑ d ∈ Icc 1 z, ∑ e ∈ Icc 1 z, w d * w e / (d.lcm e : ℝ) =
      ∑ k ∈ Icc 1 z, (k.totient : ℝ) *
        (∑ d ∈ Icc 1 z, if k ∣ d then w d / d else 0)^2 := by
  let D := Icc 1 z
  change ∑ d ∈ D, ∑ e ∈ D, w d * w e / (d.lcm e : ℝ) = _
  calc
    _ = ∑ d ∈ D, ∑ e ∈ D, ∑ k ∈ D,
        if k ∣ d ∧ k ∣ e then (w d / d) * (w e / e) * (k.totient : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      apply Finset.sum_congr rfl
      intro e he
      rw [div_lcm_eq_div_mul_gcd (mem_Icc.mp hd).1 (mem_Icc.mp he).1]
      rw [← sum_totient_gcd hd, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      split_ifs <;> simp
    _ = ∑ k ∈ D, ∑ d ∈ D, ∑ e ∈ D,
        if k ∣ d ∧ k ∣ e then (w d / d) * (w e / e) * (k.totient : ℝ) else 0 := by
      conv_lhs =>
        enter [2, d]
        rw [Finset.sum_comm]
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      rw [pow_two, Finset.sum_mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e _
      by_cases hd : k ∣ d <;> by_cases he : k ∣ e <;>
        simp [hd, he, mul_comm]

theorem moebius_sum_divisors (n : ℕ) :
    ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ) =
      if n = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℝ => f n)
    (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℝ))
  simpa only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.intCoe_apply,
    ArithmeticFunction.one_apply] using h

theorem moebius_sum_divisors_interval {z k l : ℕ} (hk : k ∈ Icc 1 z)
    (hl : 0 < l) :
    ∑ d ∈ Icc 1 z, (if l ∣ d ∧ d ∣ k then
        (ArithmeticFunction.moebius (k / d) : ℝ) else 0) =
      if l = k then 1 else 0 := by
  have hkpos : 0 < k := (mem_Icc.mp hk).1
  by_cases hd : l ∣ k
  · obtain ⟨n, hn⟩ := hd
    have hnpos : 0 < n := by
      by_contra! hz
      have hz' : n = 0 := by omega
      simp [hz'] at hn
      omega
    have hfilter :
        (Icc 1 z).filter (fun d => l ∣ d ∧ d ∣ k) =
          (n.divisors).image (fun a => l * a) := by
      ext d
      simp only [mem_filter, mem_Icc, mem_image, Nat.mem_divisors]
      constructor
      · rintro ⟨_, ⟨a, rfl⟩, h⟩
        exact ⟨a, ⟨(Nat.mul_dvd_mul_iff_left hl).mp (hn ▸ h), hnpos.ne'⟩, rfl⟩
      · rintro ⟨a, ⟨ha, _⟩, rfl⟩
        have had : l * a ∣ k := hn.symm ▸ Nat.mul_dvd_mul_left l ha
        exact ⟨⟨Nat.pos_of_dvd_of_pos had hkpos,
          (Nat.le_of_dvd hkpos had).trans (mem_Icc.mp hk).2⟩,
          Nat.dvd_mul_right l a, had⟩
    have heq : (l = k) ↔ n = 1 := by
      constructor
      · intro h
        exact (Nat.mul_left_cancel hl (show l * 1 = l * n by simpa [← hn] using h)).symm
      · intro h
        simp [hn, h]
    rw [← Finset.sum_filter, hfilter, Finset.sum_image (fun a _ b _ h => Nat.mul_left_cancel hl h)]
    simp_rw [hn, Nat.mul_div_mul_left _ _ hl]
    rw [Nat.sum_div_divisors n (fun d => (ArithmeticFunction.moebius d : ℝ)), moebius_sum_divisors]
    have heq' : l = l * n ↔ n = 1 := by simpa only [hn] using heq
    simp only [heq']
  · have hne : l ≠ k := fun h => hd (h ▸ dvd_rfl)
    rw [if_neg hne]
    apply Finset.sum_eq_zero
    intro d _
    exact if_neg fun h => hd (h.1.trans h.2)

noncomputable def invertMultiples (z : ℕ) (y : ℕ → ℝ) (d : ℕ) : ℝ :=
  ∑ k ∈ Icc 1 z, if d ∣ k then (ArithmeticFunction.moebius (k / d) : ℝ) * y k else 0

theorem sum_invertMultiples {z l : ℕ} (hl : l ∈ Icc 1 z) (y : ℕ → ℝ) :
    ∑ d ∈ Icc 1 z, (if l ∣ d then invertMultiples z y d else 0) = y l := by
  classical
  let D := Icc 1 z
  let mu := fun n : ℕ => (ArithmeticFunction.moebius n : ℝ)
  change ∑ d ∈ D, (if l ∣ d then (∑ k ∈ D, if d ∣ k then mu (k / d) * y k else 0)
    else 0) = y l
  calc
    _ = ∑ d ∈ D, ∑ k ∈ D, if l ∣ d ∧ d ∣ k then mu (k / d) * y k else 0 := by
      apply Finset.sum_congr rfl
      intro d _
      by_cases hd : l ∣ d <;> simp [hd]
    _ = ∑ k ∈ D, ∑ d ∈ D, if l ∣ d ∧ d ∣ k then mu (k / d) * y k else 0 :=
      Finset.sum_comm
    _ = ∑ k ∈ D, (if l = k then 1 else (0 : ℝ)) * y k := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [← moebius_sum_divisors_interval hk (mem_Icc.mp hl).1, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro d _
      split_ifs <;> simp [mu]
    _ = y l := by
      rw [Finset.sum_eq_single l]
      · simp
      · intro b _ hb
        simp [Ne.symm hb]
      · exact fun h => (h hl).elim

noncomputable def sieveMass (z q : ℕ) : ℝ :=
  ∑ k ∈ Icc 1 z, if Squarefree k ∧ k.Coprime q then (k.totient : ℝ)⁻¹ else 0

theorem sieveMass_pos {z : ℕ} (hz : 1 ≤ z) (q : ℕ) : 0 < sieveMass z q := by
  classical
  have hmem : 1 ∈ Icc 1 z := by simp [hz]
  have hnonneg : ∀ k ∈ Icc 1 z,
      0 ≤ (if Squarefree k ∧ k.Coprime q then (k.totient : ℝ)⁻¹ else 0) := by
    intro k _
    split_ifs <;> positivity
  have h := Finset.single_le_sum hnonneg hmem
  simp at h
  exact lt_of_lt_of_le (by norm_num) h

noncomputable def targetWeights (z q k : ℕ) : ℝ :=
  if Squarefree k ∧ k.Coprime q then
    (ArithmeticFunction.moebius k : ℝ) * (k.totient : ℝ)⁻¹ / sieveMass z q else 0

noncomputable def selbergWeights (z q d : ℕ) : ℝ :=
  d * invertMultiples z (targetWeights z q) d

theorem selberg_diagonal {z : ℕ} (hz : 1 ≤ z) (q : ℕ) :
    (∑ d ∈ Icc 1 z, ∑ e ∈ Icc 1 z,
      selbergWeights z q d * selbergWeights z q e / (d.lcm e : ℝ)) = (sieveMass z q)⁻¹ := by
  classical
  have hmass := sieveMass_pos hz q
  have hrow : ∀ k ∈ Icc 1 z,
      (∑ d ∈ Icc 1 z, if k ∣ d then selbergWeights z q d / d else 0) =
        targetWeights z q k := by
    intro k hk
    rw [← sum_invertMultiples hk (targetWeights z q)]
    apply Finset.sum_congr rfl
    intro d hd
    have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast (show 0 < d from (mem_Icc.mp hd).1).ne'
    split_ifs <;> simp [selbergWeights, hd']
  rw [diagonal_main_term]
  calc
    _ = ∑ k ∈ Icc 1 z, (k.totient : ℝ) * (targetWeights z q k)^2 :=
      Finset.sum_congr rfl fun k hk => by rw [hrow k hk]
    _ = ∑ k ∈ Icc 1 z,
        (if Squarefree k ∧ k.Coprime q then (k.totient : ℝ)⁻¹ else 0) /
          (sieveMass z q)^2 := by
      apply Finset.sum_congr rfl
      intro k hk
      by_cases hg : Squarefree k ∧ k.Coprime q
      · have hphi : (k.totient : ℝ) ≠ 0 := by
          exact_mod_cast (Nat.totient_pos.mpr (mem_Icc.mp hk).1).ne'
        have hmu : (ArithmeticFunction.moebius k : ℝ)^2 = 1 := by
          exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hg.1
        simp only [targetWeights, if_pos hg, div_pow, mul_pow, hmu, one_mul]
        field_simp
      · simp [targetWeights, hg]
    _ = _ := by
      simp_rw [div_eq_mul_inv, ← Finset.sum_mul]
      change sieveMass z q / sieveMass z q ^ 2 = _
      field_simp

theorem selbergWeights_one {z : ℕ} (hz : 1 ≤ z) (q : ℕ) :
    selbergWeights z q 1 = 1 := by
  classical
  have hp := sieveMass_pos hz q
  simp only [selbergWeights, Nat.cast_one, one_mul, invertMultiples, one_dvd,
    if_true, Nat.div_one]
  calc
    _ = ∑ k ∈ Icc 1 z,
        (if Squarefree k ∧ k.Coprime q then (k.totient : ℝ)⁻¹ else 0) /
          sieveMass z q := by
      apply Finset.sum_congr rfl
      intro k _
      by_cases hg : Squarefree k ∧ k.Coprime q
      · have hmu : (ArithmeticFunction.moebius k : ℝ)^2 = 1 := by
          exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hg.1
        simp only [targetWeights, if_pos hg, ← mul_div_assoc, ← mul_assoc,
          ← pow_two, hmu, one_mul]
      · simp [targetWeights, hg]
    _ = 1 := by
      simp_rw [div_eq_mul_inv, ← Finset.sum_mul]
      exact div_self hp.ne'

theorem selbergWeights_eq_zero_of_not_coprime {z q d : ℕ} (h : ¬ d.Coprime q) :
    selbergWeights z q d = 0 := by
  classical
  unfold selbergWeights invertMultiples
  suffices heq : (∑ k ∈ Icc 1 z, if d ∣ k then
      (ArithmeticFunction.moebius (k / d) : ℝ) * targetWeights z q k else 0) = 0 by simp [heq]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hd : d ∣ k
  · have hk : ¬ k.Coprime q := fun hc => h (hc.of_dvd_left hd)
    simp [hd, targetWeights, hk]
  · simp [hd]

theorem abs_selbergWeights_le {z : ℕ} (hz : 1 ≤ z) (q d : ℕ) :
    |selbergWeights z q d| ≤ d := by
  classical
  have hp := sieveMass_pos hz q
  have hsum : |invertMultiples z (targetWeights z q) d| ≤ 1 := by
    unfold invertMultiples
    calc
      _ ≤ ∑ k ∈ Icc 1 z, |if d ∣ k then
          (ArithmeticFunction.moebius (k / d) : ℝ) * targetWeights z q k else 0| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Icc 1 z,
          (if Squarefree k ∧ k.Coprime q then (k.totient : ℝ)⁻¹ else 0) /
            sieveMass z q := by
        apply Finset.sum_le_sum
        intro k hk
        by_cases hg : Squarefree k ∧ k.Coprime q
        · have hg' : 0 ≤ (k.totient : ℝ)⁻¹ / sieveMass z q := by positivity
          by_cases hd : d ∣ k
          · have hmu : |(ArithmeticFunction.moebius k : ℝ)| = 1 := by
              exact_mod_cast ArithmeticFunction.abs_moebius_eq_one_of_squarefree hg.1
            have hmu' : |(ArithmeticFunction.moebius (k / d) : ℝ)| ≤ 1 := by
              exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := k / d)
            simp only [if_pos hd, if_pos hg, targetWeights, abs_mul, abs_div, hmu, one_mul,
              abs_of_nonneg (show 0 ≤ (k.totient : ℝ)⁻¹ by positivity), abs_of_pos hp]
            simpa using mul_le_mul_of_nonneg_right hmu' hg'
          · simp only [if_neg hd, if_pos hg, abs_zero]
            exact hg'
        · simp [targetWeights, hg]
      _ = 1 := by
        simp_rw [div_eq_mul_inv, ← Finset.sum_mul]
        change sieveMass z q * (sieveMass z q)⁻¹ = 1
        exact mul_inv_cancel₀ hp.ne'
  rw [selbergWeights, abs_mul, abs_of_nonneg (Nat.cast_nonneg d)]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg (α := ℝ) d)

end Hall394Weights











open Finset Hall394Progression Hall394Sieve Hall394SieveError Hall394Weights

namespace Hall394PrimeProgression

theorem count_prime_progression {N q a z : ℕ} (hq : 0 < q) (hz : 1 ≤ z) :
    (((residue N q (a % q)).filter (fun n => n.Prime ∧ z < n)).card : ℝ) ≤
      (N : ℝ) / q / sieveMass z q + (z : ℝ)^4 := by
  let w := selbergWeights z q
  let A := residue N q (a % q)
  have hmodel :
      (∑ d ∈ Icc 1 z, ∑ e ∈ Icc 1 z, w d * w e *
        ((N : ℝ) / q / (d.lcm e : ℝ))) = (N : ℝ) / q / sieveMass z q := by
    calc
      _ = (N : ℝ) / q *
          (∑ d ∈ Icc 1 z, ∑ e ∈ Icc 1 z, w d * w e / (d.lcm e : ℝ)) := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d _
        apply Finset.sum_congr rfl
        intro e _
        ring
      _ = _ := by rw [show w = selbergWeights z q from rfl, selberg_diagonal hz q]; rfl
  have hg : (∑ d ∈ Icc 1 z, |w d|) ≤ (z : ℝ)^2 := by
    calc
      _ ≤ ∑ _d ∈ Icc 1 z, (z : ℝ) := by
        apply Finset.sum_le_sum
        intro d hd
        exact (abs_selbergWeights_le hz q d).trans (by exact_mod_cast (mem_Icc.mp hd).2)
      _ = _ := by simp [Nat.card_Icc, pow_two]
  have hg0 : 0 ≤ ∑ d ∈ Icc 1 z, |w d| :=
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  have herr :
      ∀ d ∈ Icc 1 z, ∀ e ∈ Icc 1 z, w d ≠ 0 → w e ≠ 0 →
        |countMultiples A (d.lcm e) - (N : ℝ) / q / (d.lcm e : ℝ)| ≤ 1 := by
    intro d hd e he hwd hwe
    have hdq : d.Coprime q := by
      by_contra h
      exact hwd (selbergWeights_eq_zero_of_not_coprime h)
    have heq : e.Coprime q := by
      by_contra h
      exact hwe (selbergWeights_eq_zero_of_not_coprime h)
    have hcop : q.Coprime (d.lcm e) :=
      ((Nat.coprime_mul_iff_left.mpr ⟨hdq, heq⟩).of_dvd_left (Nat.lcm_dvd_mul d e)).symm
    have hpos : 0 < d.lcm e :=
      Nat.pos_of_ne_zero (Nat.lcm_ne_zero
        (show 0 < d from (mem_Icc.mp hd).1).ne'
        (show 0 < e from (mem_Icc.mp he).1).ne')
    rw [div_div]
    exact abs_progression_error (N := N) (a := a) hq hpos hcop
  have h := (prime_count_le_weighted A z hz w (selbergWeights_one hz q)).trans
    (quadratic_le_model (Icc 1 z) w (fun d e => countMultiples A (d.lcm e))
      (fun d e => (N : ℝ) / q / (d.lcm e : ℝ)) 1 (by norm_num) herr)
  rw [hmodel, one_mul] at h
  have hg' : (∑ d ∈ Icc 1 z, |w d|)^2 ≤ (z : ℝ)^4 := by
    calc
      _ ≤ ((z : ℝ)^2)^2 := pow_le_pow_left₀ hg0 hg 2
      _ = _ := by ring
  exact h.trans (add_le_add_right hg' _)

end Hall394PrimeProgression




/- Harmonic mass of multiples used to bound the sieve denominator. -/
open Finset

namespace Hall394Harmonic

noncomputable def weight (n : ℕ) : ℝ := (n : ℝ)⁻¹

theorem sum_multiples_weight_le (z d : ℕ) (hd : 0 < d) :
    (∑ n ∈ (Icc 1 z).filter (fun n => d ∣ n), weight n) ≤
      weight d * ∑ n ∈ Icc 1 z, weight n := by
  have hset : (Icc 1 z).filter (fun n => d ∣ n) =
      (Icc 1 (z / d)).image (fun n => d * n) := by
    ext n
    simp only [mem_filter, mem_Icc, mem_image]
    constructor
    · rintro ⟨⟨hn, hnz⟩, ⟨k, rfl⟩⟩
      refine ⟨k, ⟨?_, (Nat.le_div_iff_mul_le hd).2 ?_⟩, rfl⟩
      · by_contra! hk
        have hk0 : k = 0 := by omega
        simp [hk0] at hn
      · simpa [Nat.mul_comm] using hnz
    · rintro ⟨k, ⟨hk, hkz⟩, rfl⟩
      exact ⟨⟨Nat.mul_pos hd hk, by
        simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hd).1 hkz⟩,
        Nat.dvd_mul_right d k⟩
  rw [hset, Finset.sum_image (fun _ _ _ _ h => Nat.mul_left_cancel hd h)]
  simp only [weight, Nat.cast_mul, mul_inv, ← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => by positivity)
  intro n hn
  exact mem_Icc.mpr ⟨(mem_Icc.mp hn).1, (mem_Icc.mp hn).2.trans (Nat.div_le_self _ _)⟩

theorem sum_reciprocal_squares_le (z : ℕ) :
    ∑ n ∈ Icc 2 z, ((n : ℝ)^2)⁻¹ ≤ 3 / 4 := by
  induction z with
  | zero => norm_num
  | succ z ih =>
    by_cases h : 2 ≤ z
    · have hstrong : ∀ k : ℕ, 2 ≤ k →
          ∑ n ∈ Icc 2 k, ((n : ℝ)^2)⁻¹ ≤ 3 / 4 - (k : ℝ)⁻¹ := by
        intro k
        induction k with
        | zero => omega
        | succ k ihk =>
          intro hk
          by_cases hk2 : 2 ≤ k
          · have hset : Icc 2 (k + 1) = insert (k + 1) (Icc 2 k) := by
              ext n
              simp only [mem_Icc, mem_insert]
              omega
            rw [hset, Finset.sum_insert (by simp)]
            have hpos : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
            have hpos' : 0 < (k : ℝ) + 1 := by positivity
            have hstep : (((k : ℝ) + 1)^2)⁻¹ ≤ (k : ℝ)⁻¹ - ((k : ℝ) + 1)⁻¹ := by
              field_simp [hpos.ne', hpos'.ne']
              nlinarith
            push_cast
            linarith [ihk hk2]
          · have he : k = 1 := by omega
            subst k
            norm_num
      exact (hstrong (z + 1) (by omega)).trans (by
        have : 0 ≤ ((z + 1 : ℕ) : ℝ)⁻¹ := by positivity
        linarith)
    · interval_cases z <;> norm_num

theorem weighted_cover_le {ι α : Type*} (U : Finset α) (J : Finset ι)
    (f : α → ℝ) (hf : ∀ n ∈ U, 0 ≤ f n)
    (bad : α → Prop) [DecidablePred bad]
    (covers : ι → α → Prop) [∀ j, DecidablePred (covers j)]
    (hcover : ∀ n ∈ U, bad n → ∃ j ∈ J, covers j n) :
    (∑ n ∈ U.filter bad, f n) ≤
      ∑ j ∈ J, ∑ n ∈ U.filter (covers j), f n := by
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm (s := J) (t := U)]
  refine Finset.sum_le_sum fun n hn => ?_
  by_cases h : bad n
  · obtain ⟨j, hj, hc⟩ := hcover n hn h
    have h := Finset.single_le_sum (f := fun j => if covers j n then f n else 0)
      (fun i _ => by split_ifs <;> simp [hf n hn]) hj
    simpa only [if_pos ‹bad n›, if_pos hc] using h
  · rw [if_neg h]
    exact Finset.sum_nonneg fun _ _ => by split_ifs <;> simp [hf n hn]

theorem nonsquarefree_weight_le (z : ℕ) :
    (∑ n ∈ (Icc 1 z).filter (fun n => ¬ Squarefree n), weight n) ≤
      (3 / 4 : ℝ) * ∑ n ∈ Icc 1 z, weight n := by
  classical
  let H := ∑ n ∈ Icc 1 z, weight n
  have hH : 0 ≤ H := Finset.sum_nonneg fun n _ => by unfold weight; positivity
  calc
    _ ≤ ∑ j ∈ Icc 2 z, ∑ n ∈ (Icc 1 z).filter (fun n => j * j ∣ n), weight n := by
      apply weighted_cover_le (hf := fun n _ => by unfold weight; positivity)
      intro n hn hbad
      rw [Nat.squarefree_iff_prime_squarefree] at hbad
      push Not at hbad
      obtain ⟨p, hp, hd⟩ := hbad
      have hpn : p ∣ n := (Nat.dvd_mul_right p p).trans hd
      exact ⟨p, mem_Icc.mpr ⟨hp.two_le,
        (Nat.le_of_dvd (mem_Icc.mp hn).1 hpn).trans (mem_Icc.mp hn).2⟩, hd⟩
    _ ≤ ∑ j ∈ Icc 2 z, weight (j * j) * H := by
      apply Finset.sum_le_sum
      intro j hj
      have hj' : 0 < j := lt_of_lt_of_le (by decide : 0 < 2) (mem_Icc.mp hj).1
      exact sum_multiples_weight_le z _ (Nat.mul_pos hj' hj')
    _ ≤ _ := by
      rw [← Finset.sum_mul]
      apply mul_le_mul_of_nonneg_right _ hH
      simpa only [weight, Nat.cast_mul, pow_two] using sum_reciprocal_squares_le z

theorem noncoprime_weight_le (z q : ℕ) (hq : q ≠ 0) :
    (∑ n ∈ (Icc 1 z).filter (fun n => ¬ n.Coprime q), weight n) ≤
      (∑ p ∈ q.primeFactors, weight p) * ∑ n ∈ Icc 1 z, weight n := by
  classical
  calc
    _ ≤ ∑ p ∈ q.primeFactors, ∑ n ∈ (Icc 1 z).filter (fun n => p ∣ n), weight n := by
      apply weighted_cover_le (hf := fun n _ => by unfold weight; positivity)
      intro n _ hbad
      by_contra h
      apply hbad
      apply Nat.coprime_of_dvd
      intro p hp hpn hpq
      exact h ⟨p, Nat.mem_primeFactors.mpr ⟨hp, hpq, hq⟩, hpn⟩
    _ ≤ _ := by
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro p hp
      exact sum_multiples_weight_le z p (Nat.prime_of_mem_primeFactors hp).pos

theorem good_weight_ge (z q : ℕ) (hq : q ≠ 0)
    (hsmall : ∑ p ∈ q.primeFactors, weight p ≤ 1 / 8) :
    (1 / 8 : ℝ) * (∑ n ∈ Icc 1 z, weight n) ≤
      ∑ n ∈ Icc 1 z, if Squarefree n ∧ n.Coprime q then weight n else 0 := by
  classical
  let H := ∑ n ∈ Icc 1 z, weight n
  have hH : 0 ≤ H := sum_nonneg fun n _ => inv_nonneg.mpr (Nat.cast_nonneg n)
  have hs := nonsquarefree_weight_le z
  have hc := (noncoprime_weight_le z q hq).trans
    (mul_le_mul_of_nonneg_right hsmall hH)
  have hsplit : H ≤
      (∑ n ∈ Icc 1 z, if Squarefree n ∧ n.Coprime q then weight n else 0) +
        (∑ n ∈ (Icc 1 z).filter (fun n => ¬ Squarefree n), weight n) +
        (∑ n ∈ (Icc 1 z).filter (fun n => ¬ n.Coprime q), weight n) := by
    simp only [Finset.sum_filter, ← Finset.sum_add_distrib]
    apply sum_le_sum
    intro n _
    have hw : 0 ≤ weight n := inv_nonneg.mpr (Nat.cast_nonneg n)
    split_ifs <;> first | linarith | exfalso; tauto
  dsimp only [H] at hsplit
  linarith

theorem log_le_sum_weights (z : ℕ) :
    Real.log (z : ℝ) ≤ ∑ n ∈ Icc 1 z, weight n := by
  simpa [weight, harmonic_eq_sum_Icc] using
    log_le_harmonic_floor (z : ℝ) (Nat.cast_nonneg z)

end Hall394Harmonic






open Finset

namespace Hall394UniformProgression

theorem sieveMass_ge_log_div_eight (z q : ℕ) (hq : q ≠ 0)
    (hsmall : ∑ p ∈ q.primeFactors, Hall394Harmonic.weight p ≤ 1 / 8) :
    Real.log (z : ℝ) / 8 ≤ Hall394Weights.sieveMass z q := by
  classical
  calc
    _ = (1 / 8 : ℝ) * Real.log (z : ℝ) := by ring
    _ ≤ (1 / 8 : ℝ) * ∑ n ∈ Icc 1 z, Hall394Harmonic.weight n :=
      mul_le_mul_of_nonneg_left (Hall394Harmonic.log_le_sum_weights z) (by norm_num)
    _ ≤ ∑ n ∈ Icc 1 z, if Squarefree n ∧ n.Coprime q then Hall394Harmonic.weight n else 0 :=
      Hall394Harmonic.good_weight_ge z q hq hsmall
    _ ≤ _ := by
      unfold Hall394Weights.sieveMass
      apply Finset.sum_le_sum
      intro n hn
      by_cases hg : Squarefree n ∧ n.Coprime q
      · simp only [if_pos hg, Hall394Harmonic.weight]
        have hp : (0 : ℝ) < n.totient := by
          exact_mod_cast (Nat.totient_pos.mpr (Finset.mem_Icc.mp hn).1)
        exact inv_anti₀ hp (by exact_mod_cast Nat.totient_le n)
      · simp only [if_neg hg, le_refl]

theorem count_prime_progression_log {N q a z : ℕ} (hq : 0 < q) (hz : 1 < z)
    (hsmall : ∑ p ∈ q.primeFactors, Hall394Harmonic.weight p ≤ 1 / 8) :
    (((Hall394Progression.residue N q (a % q)).filter
      (fun n => n.Prime ∧ z < n)).card : ℝ) ≤
        8 * N / q / Real.log (z : ℝ) + (z : ℝ)^4 := by
  have h := Hall394PrimeProgression.count_prime_progression
    (N := N) (a := a) hq (by omega : 1 ≤ z)
  refine h.trans (add_le_add_left ?_ _)
  have hzlog : 0 < Real.log (z : ℝ) := Real.log_pos (by exact_mod_cast hz)
  calc
    _ ≤ (N : ℝ) / q / (Real.log (z : ℝ) / 8) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity)
        (sieveMass_ge_log_div_eight z q hq.ne' hsmall)
    _ = _ := by ring

theorem count_le_257 {N q a z : ℕ} (hq : 0 < q) (hz : 1 < z)
    (hsmall : ∑ p ∈ q.primeFactors, Hall394Harmonic.weight p ≤ 1 / 8)
    (hlog : Real.log (N : ℝ) / 32 ≤ Real.log (z : ℝ)) (hN : 1 < N)
    (herr : (q : ℝ) * Real.log (N : ℝ) * (z : ℝ)^4 ≤ N) :
    (((Hall394Progression.residue N q (a % q)).filter
      (fun n => n.Prime ∧ z < n)).card : ℝ) ≤
        257 * N / q / Real.log (N : ℝ) := by
  have hLN : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
  have hq' : 0 < (q : ℝ) := by exact_mod_cast hq
  have hmain : 8 * (N : ℝ) / q / Real.log (z : ℝ) ≤
      256 * (N : ℝ) / q / Real.log (N : ℝ) := by
    calc
      _ ≤ 8 * (N : ℝ) / q / (Real.log (N : ℝ) / 32) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hlog
      _ = _ := by ring
  have he : (z : ℝ)^4 ≤ (N : ℝ) / q / Real.log (N : ℝ) := by
    rw [div_div, le_div_iff₀ (mul_pos hq' hLN)]
    simpa [mul_comm] using herr
  have h := count_prime_progression_log (N := N) (a := a) hq hz hsmall
  linarith only [h, hmain, he,
    show (257 : ℝ) * N / q / Real.log (N : ℝ) =
      256 * N / q / Real.log (N : ℝ) + N / q / Real.log (N : ℝ) by ring]

end Hall394UniformProgression




/- Bounds for excluded residue classes arising from small quotients. -/
open Finset

namespace Hall394BadClasses

theorem unique_residue {d c x y : ℕ} (hx : x < d) (hy : y < d)
    (sign : ZMod d) (hs : IsUnit sign)
    (h₁ : (x : ZMod d) * (c : ZMod d) = sign)
    (h₂ : (y : ZMod d) * (c : ZMod d) = sign) : x = y := by
  have h : (x : ZMod d) * sign = (y : ZMod d) * sign := by
    calc
      _ = (x : ZMod d) * ((y : ZMod d) * (c : ZMod d)) := by rw [h₂]
      _ = (y : ZMod d) * ((x : ZMod d) * (c : ZMod d)) := by ring
      _ = _ := by rw [h₁]
  have hxy := (ZMod.natCast_eq_natCast_iff' x y d).mp (hs.mul_right_cancel h)
  simpa [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] using hxy

noncomputable def smallResidues (d k Q : ℕ) (sign : ZMod d) : Finset ℕ := by
  classical
  exact (range d).filter fun a : ℕ => ∃ u ∈ Icc 1 Q,
    ((a : ℕ) : ZMod d) * ((k * u : ℕ) : ZMod d) = sign

theorem mem_smallResidues (d k Q a : ℕ) (sign : ZMod d) :
    a ∈ smallResidues d k Q sign ↔ a < d ∧ ∃ u ∈ Icc 1 Q,
      (a : ZMod d) * ((k * u : ℕ) : ZMod d) = sign := by
  classical
  simp only [smallResidues, mem_filter, mem_range]

theorem residues_with_small_quotient {d k Q : ℕ} (sign : ZMod d) (hs : IsUnit sign) :
    (smallResidues d k Q sign).card ≤ Q := by
  classical
  let S := smallResidues d k Q sign
  have pick : ∀ a ∈ S, ∃ u ∈ Icc 1 Q,
      (a : ZMod d) * ((k * u : ℕ) : ZMod d) = sign :=
    fun a ha => ((mem_smallResidues d k Q a sign).mp ha).2
  choose u hu hsign using pick
  let f := fun a => if h : a ∈ S then u a h else 0
  have hcard : S.card ≤ (Icc 1 Q).card := by
    apply Finset.card_le_card_of_injOn f
    · intro a ha
      change a ∈ S at ha
      change f a ∈ Icc 1 Q
      simpa [f, ha] using hu a ha
    · intro a ha b hb hab
      change a ∈ S at ha
      change b ∈ S at hb
      change f a = f b at hab
      simp only [f, dif_pos ha, dif_pos hb] at hab
      have ha' : a < d := ((mem_smallResidues d k Q a sign).mp ha).1
      have hb' : b < d := ((mem_smallResidues d k Q b sign).mp hb).1
      apply unique_residue ha' hb' sign hs (hsign a ha)
      simpa only [hab] using hsign b hb
  simpa [Nat.card_Icc] using hcard

theorem lift_residue_card_le (d k : ℕ) (hd : 0 < d) (S : Finset ℕ) :
    ((range (d * k)).filter fun n => n % d ∈ S).card ≤ S.card * k := by
  have hcard : ((range (d * k)).filter fun n => n % d ∈ S).card ≤
      (S.product (range k)).card := by
    apply Finset.card_le_card_of_injOn (fun n => (n % d, n / d))
    · intro n hn
      obtain ⟨hlt, hmem⟩ := mem_filter.mp (show n ∈ (range (d * k)).filter _ from hn)
      apply Finset.mem_product.mpr
      refine ⟨hmem, mem_range.mpr ?_⟩
      exact (Nat.div_lt_iff_lt_mul hd).mpr (by simpa [Nat.mul_comm] using mem_range.mp hlt)
    · intro n _ m _ hm
      have hm₁ : n % d = m % d := congrArg Prod.fst hm
      have hm₂ : n / d = m / d := congrArg Prod.snd hm
      rw [← Nat.mod_add_div n d, ← Nat.mod_add_div m d, hm₁, hm₂]
  simpa using hcard

noncomputable def excluded (d k Q : ℕ) : Finset ℕ :=
  smallResidues d k Q 1 ∪ smallResidues d k Q (-1)

theorem excluded_card_le (d k Q : ℕ) : (excluded d k Q).card ≤ 2 * Q := by
  unfold excluded
  calc
    _ ≤ (smallResidues d k Q 1).card + (smallResidues d k Q (-1)).card :=
      Finset.card_union_le _ _
    _ ≤ Q + Q := Nat.add_le_add
      (residues_with_small_quotient _ isUnit_one)
      (residues_with_small_quotient _ isUnit_one.neg)
    _ = _ := by omega

noncomputable def badClasses (b : ℕ) (rate : ℝ) : Finset ℕ :=
  b.divisors.biUnion fun d =>
    (range b).filter fun r => r % d ∈ excluded d (b / d) ⌊rate * d⌋₊

theorem badClasses_card_le {b : ℕ} (hb : 0 < b) {rate : ℝ} (hrate : 0 ≤ rate) :
    ((badClasses b rate).card : ℝ) ≤ 2 * rate * b * (b.divisors.card : ℝ) := by
  classical
  unfold badClasses
  calc
    _ ≤ ∑ d ∈ b.divisors,
        (((range b).filter fun r => r % d ∈ excluded d (b / d) ⌊rate * d⌋₊).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _d ∈ b.divisors, (2 * rate * b : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      have hdvd := Nat.dvd_of_mem_divisors hd
      have hdpos := Nat.pos_of_dvd_of_pos hdvd hb
      have heq : d * (b / d) = b := Nat.mul_div_cancel' hdvd
      have hcount := lift_residue_card_le d (b / d) hdpos (excluded d (b / d) ⌊rate * d⌋₊)
      rw [heq] at hcount
      have hreal :
          (((range b).filter fun r => r % d ∈ excluded d (b / d) ⌊rate * d⌋₊).card : ℝ) ≤
            (2 : ℝ) * (⌊rate * d⌋₊ : ℕ) * (b / d : ℕ) := by
        exact_mod_cast hcount.trans (Nat.mul_le_mul_right _ (excluded_card_le _ _ _))
      calc
        _ ≤ _ := hreal
        _ ≤ 2 * (rate * d) * (b / d : ℕ) := by
          gcongr
          exact Nat.floor_le (by positivity)
        _ = _ := by
          have heq' : (d : ℝ) * (b / d : ℕ) = b := by exact_mod_cast heq
          calc _ = 2 * rate * ((d : ℝ) * (b / d : ℕ)) := by ring
               _ = _ := by rw [heq']
    _ = _ := by simp [mul_comm]

theorem mem_badClasses_of_excluded {p b d : ℕ} (hb : 0 < b) (hd : d ∈ b.divisors)
    {rate : ℝ} (h : p % d ∈ excluded d (b / d) ⌊rate * d⌋₊) :
    p % b ∈ badClasses b rate := by
  apply Finset.mem_biUnion.mpr
  refine ⟨d, hd, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt _ hb), ?_⟩⟩
  simpa only [Nat.mod_mod_of_dvd _ (Nat.dvd_of_mem_divisors hd)] using h

end Hall394BadClasses







open Finset

namespace Hall394ExcludedStarts

theorem enters_excluded {p b m : ℕ} {rate : ℝ} (hp : p.Prime) (hb : 0 < b)
    (hm : 0 < m) (hdiv : p * b ∣ m * (m + 1))
    (hsmall : ((m + 1 : ℕ) : ℝ) ≤ rate * (p * b : ℕ)) :
    ∃ d ∈ b.divisors,
      p % d ∈ Hall394BadClasses.excluded d (b / d) ⌊rate * d⌋₊ := by
  obtain ⟨d, k, hkd, hs⟩ := Hall394.large_prime_on_one_side hp hdiv
  have hd : 0 < d := by
    by_contra! h
    have : d = 0 := by omega
    simp [this] at hkd
    omega
  have hk : 0 < k := by
    by_contra! h
    have : k = 0 := by omega
    simp [this] at hkd
    omega
  have hbd : d ∣ b := hkd ▸ Nat.dvd_mul_left d k
  have hquot : b / d = k := Nat.div_eq_of_eq_mul_right hd (by simpa only [Nat.mul_comm] using hkd.symm)
  refine ⟨d, Nat.mem_divisors.mpr ⟨hbd, hb.ne'⟩, ?_⟩
  rw [hquot]
  have hpmod : ((p % d : ℕ) : ZMod d) = (p : ZMod d) :=
    (ZMod.natCast_eq_natCast_iff' _ _ _).mpr (by simp)
  have hpk : (0 : ℝ) < (p : ℝ) * k := by exact_mod_cast Nat.mul_pos hp.pos hk
  have hu (u N : ℕ) (hNu : N = p * k * u) (hN : N ≤ m + 1) (hNpos : 0 < N) :
      u ∈ Icc 1 ⌊rate * d⌋₊ := by
    have hupos : 0 < u := by
      by_contra! h
      have : u = 0 := by omega
      simp [this] at hNu
      omega
    refine mem_Icc.mpr ⟨hupos, ?_⟩
    have hN' : (N : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast hN
    have heq : (N : ℝ) = (p : ℝ) * k * u := by exact_mod_cast hNu
    have hbd' : (b : ℝ) = (k : ℝ) * d := by exact_mod_cast hkd.symm
    have h : (u : ℝ) ≤ rate * d := by
      apply le_of_mul_le_mul_left _ hpk
      calc
        (p : ℝ) * k * u = N := heq.symm
        _ ≤ rate * (p * b : ℕ) := hN'.trans hsmall
        _ = _ := by rw [Nat.cast_mul, hbd']; ring
    exact Nat.le_floor h
  unfold Hall394BadClasses.excluded
  rcases hs with ⟨hmul, hdvd⟩ | ⟨hmul, hdvd⟩
  · obtain ⟨u, hmu⟩ := hmul
    have hz : ((m + 1 : ℕ) : ZMod d) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
    have hz' : (p : ZMod d) * ((k * u : ℕ) : ZMod d) = -1 := by
      push_cast at hz ⊢
      have he : (m : ZMod d) = (p : ZMod d) * k * u := by simpa only [Nat.cast_mul] using congrArg (fun n : ℕ => (n : ZMod d)) hmu
      rw [he] at hz
      linear_combination hz
    exact mem_union.mpr (Or.inr ((Hall394BadClasses.mem_smallResidues _ _ _ _ _).mpr
      ⟨Nat.mod_lt _ hd, u, hu u m hmu (by omega) hm, hpmod ▸ hz'⟩))
  · obtain ⟨u, hmu⟩ := hmul
    have hz : (m : ZMod d) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
    have hz' : (p : ZMod d) * ((k * u : ℕ) : ZMod d) = 1 := by
      have he : ((m + 1 : ℕ) : ZMod d) = (p : ZMod d) * k * u := by simpa only [Nat.cast_mul] using congrArg (fun n : ℕ => (n : ZMod d)) hmu
      push_cast at he ⊢
      rw [hz, zero_add] at he
      linear_combination -he
    exact mem_union.mpr (Or.inl ((Hall394BadClasses.mem_smallResidues _ _ _ _ _).mpr
      ⟨Nat.mod_lt _ hd, u, hu u (m + 1) hmu le_rfl (by omega), hpmod ▸ hz'⟩))

end Hall394ExcludedStarts




open Finset
namespace Hall394GoodPrimes

noncomputable def good (P : Finset ℕ) (b : ℕ) (rate : ℝ) : Finset ℕ := by
  classical
  exact P.filter fun p => p % b ∉ Hall394BadClasses.badClasses b rate

theorem good_card {P : Finset ℕ} {N b z : ℕ}
    (hb : 0 < b) (hz : 1 < z)
    (hsmall : ∑ p ∈ b.primeFactors, Hall394Harmonic.weight p ≤ 1 / 8)
    (hlog : Real.log (N : ℝ) / 32 ≤ Real.log (z : ℝ)) (hN : 1 < N)
    (herr : (b : ℝ) * Real.log (N : ℝ) * (z : ℝ)^4 ≤ N)
    (hP : ∀ p ∈ P, p < N ∧ p.Prime ∧ z < p)
    (hmass : (N : ℝ) / (8 * Real.log N) ≤ (P.card : ℝ)) :
    let rate := (16384 * (b.divisors.card : ℝ))⁻¹
    (N : ℝ) / (16 * Real.log N) ≤ ((good P b rate).card : ℝ) := by
  classical
  let rate : ℝ := (16384 * (b.divisors.card : ℝ))⁻¹
  let bad := Hall394BadClasses.badClasses b rate
  let S := fun a => Hall394Progression.residue N b (a % b)
  have hbad : ∀ a ∈ bad, a < b := by
    intro a ha
    obtain ⟨d, _, hd⟩ := Finset.mem_biUnion.mp ha
    exact mem_range.mp (mem_filter.mp hd).1
  have hcard : (bad.card : ℝ) ≤ (b : ℝ) / 8192 := by
    have hd : 0 < b.divisors.card :=
      Finset.card_pos.mpr ⟨1, Nat.mem_divisors.mpr ⟨one_dvd _, hb.ne'⟩⟩
    have hd' : 0 < (b.divisors.card : ℝ) := by exact_mod_cast hd
    have hc := Hall394BadClasses.badClasses_card_le (b := b) (rate := rate) hb (by positivity)
    apply hc.trans_eq
    dsimp only [rate]
    field_simp
    <;> ring
  have hcap : ∀ a ∈ bad,
      ((P ∩ S a).card : ℝ) ≤ 257 * (N : ℝ) / b / Real.log N := by
    intro a _
    refine le_trans ?_ (Hall394UniformProgression.count_le_257 (a := a) hb hz hsmall hlog hN herr)
    exact_mod_cast Finset.card_le_card (fun p hp => by
      obtain ⟨hpP, hpS⟩ := Finset.mem_inter.mp hp
      exact Finset.mem_filter.mpr ⟨hpS, (hP p hpP).2⟩)
  have hcover := Hall394Counting.card_sdiff_ge_of_cover P bad S hmass hcard hcap
    (by have : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN); positivity)
  have heq : P \ bad.biUnion S = good P b rate := by
    ext p
    rw [Finset.mem_sdiff, good, Finset.mem_filter]
    simp only [Finset.mem_biUnion]
    refine and_congr_right fun hp => not_congr ?_
    constructor
    · rintro ⟨a, ha, hs⟩
      have hh := (mem_filter.mp hs).2
      rw [Nat.mod_eq_of_lt (hbad a ha)] at hh
      exact hh.symm ▸ ha
    · intro hpbad
      exact ⟨p % b, hpbad, mem_filter.mpr ⟨mem_range.mpr (hP p hp).1, by simp⟩⟩
  rw [heq] at hcover
  refine le_trans ?_ hcover
  have hlog' : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  field_simp
  <;> nlinarith

theorem t_lower_of_good {P : Finset ℕ} {p b : ℕ} {rate : ℝ}
    (hp : p.Prime) (hb : 0 < b) (hg : p ∈ good P b rate) :
    rate * ((p * b : ℕ) : ℝ) - 1 < (Erdos394.t 2 (p * b) : ℝ) := by
  classical
  have hgood : p % b ∉ Hall394BadClasses.badClasses b rate := (mem_filter.mp hg).2
  obtain ⟨hpos, hdiv⟩ := Hall394.least_start_spec (Nat.mul_pos hp.pos hb)
  by_contra! h
  have hsmall : ((Erdos394.t 2 (p * b) + 1 : ℕ) : ℝ) ≤ rate * (p * b : ℕ) := by
    rw [Nat.cast_add, Nat.cast_one]
    linarith only [h]
  obtain ⟨d, hd, hx⟩ := Hall394ExcludedStarts.enters_excluded hp hb hpos hdiv hsmall
  exact hgood (Hall394BadClasses.mem_badClasses_of_excluded hb hd hx)

end Hall394GoodPrimes





/- Finite product and first moment identities for the cofactor weights. -/

open Finset

namespace Hall394Cofactors

theorem subset_first_moment {α : Type*} [DecidableEq α] (P : Finset α)
    (w f : α → ℝ) (hw : ∀ p ∈ P, 0 ≤ w p) (hf : ∀ p ∈ P, 0 ≤ f p) :
    (∑ S ∈ P.powerset, (∏ p ∈ S, w p) * ∑ p ∈ S, f p) ≤
      (∏ p ∈ P, (1 + w p)) * ∑ p ∈ P, w p * f p := by
  induction P using Finset.induction_on with
  | empty => simp
  | @insert a P ha ih =>
    have hsub : ∀ S ∈ P.powerset, a ∉ S := fun S hS hm => ha (mem_powerset.mp hS hm)
    have hinj : Set.InjOn (insert a) (P.powerset : Set (Finset α)) := by
      intro S hS T hT h
      have hS' := hsub S hS
      have hT' := hsub T hT
      ext p
      have hh : p ∈ insert a S ↔ p ∈ insert a T := by rw [h]
      by_cases hp : p = a
      · subst p
        simp [hS', hT']
      · simpa [hp] using hh
    have hdisj : Disjoint P.powerset (P.powerset.image (insert a)) := by
      apply Finset.disjoint_left.mpr
      intro S hS him
      obtain ⟨T, _, rfl⟩ := mem_image.mp him
      exact hsub _ hS (mem_insert_self _ _)
    rw [powerset_insert, Finset.sum_union hdisj]
    rw [Finset.sum_image hinj, Finset.prod_insert ha, Finset.sum_insert ha]
    have hnew : (∑ S ∈ P.powerset, (∏ p ∈ insert a S, w p) * ∑ p ∈ insert a S, f p) =
        ∑ S ∈ P.powerset, (w a * ∏ p ∈ S, w p) * (f a + ∑ p ∈ S, f p) := by
      apply Finset.sum_congr rfl
      intro S hS
      rw [Finset.prod_insert (hsub S hS), Finset.sum_insert (hsub S hS)]
    rw [hnew]
    -- Separate the contribution of the new element from the old first moment.
    have hm := ih (fun p hp => hw p (mem_insert_of_mem hp)) (fun p hp => hf p (mem_insert_of_mem hp))
    have hweight := hw a (mem_insert_self _ _)
    have hfa := hf a (mem_insert_self _ _)
    have hprod : (∑ S ∈ P.powerset, ∏ p ∈ S, w p) = ∏ p ∈ P, (1 + w p) :=
      (Finset.prod_one_add P).symm
    have hprod0 : 0 ≤ ∏ p ∈ P, (1 + w p) :=
      Finset.prod_nonneg fun p hp => by linarith [hw p (mem_insert_of_mem hp)]
    simp only [mul_add, Finset.sum_add_distrib, ← mul_assoc, ← Finset.sum_mul, ← Finset.mul_sum]
    rw [hprod]
    have hlinear :
        (∑ S ∈ P.powerset, (w a * ∏ p ∈ S, w p) * ∑ p ∈ S, f p) =
          w a * (∑ S ∈ P.powerset, (∏ p ∈ S, w p) * ∑ p ∈ S, f p) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [hlinear]
    nlinarith only [mul_le_mul_of_nonneg_left hm (show 0 ≤ 1 + w a by linarith),
      mul_nonneg (mul_nonneg hweight hweight) (mul_nonneg hfa hprod0)]

theorem weight_of_large_cost {α : Type*} (U : Finset α) (w c : α → ℝ)
    {t cap : ℝ} (ht : 0 < t) (hw : ∀ s ∈ U, 0 ≤ w s)
    (hc : ∀ s ∈ U, 0 ≤ c s)
    (hcap : (∑ s ∈ U, w s * c s) ≤ cap) :
    ∑ s ∈ U.filter (fun s => t < c s), w s ≤ cap / t := by
  rw [le_div_iff₀ ht, Finset.sum_mul]
  calc
    _ ≤ ∑ s ∈ U.filter (fun s => t < c s), w s * c s := by
      apply Finset.sum_le_sum
      intro s hs
      exact mul_le_mul_of_nonneg_left (mem_filter.mp hs).2.le (hw s (mem_filter.mp hs).1)
    _ ≤ ∑ s ∈ U, w s * c s :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun s hs _ => mul_nonneg (hw s hs) (hc s hs))
    _ ≤ _ := hcap

theorem product_square_ge {α : Type*} (P : Finset α) (w : α → ℝ)
    (hw : ∀ p ∈ P, 0 ≤ w p) :
    (∏ p ∈ P, (1 + w p)) ≤ (∏ p ∈ P, (1 + w p / 2))^2 := by
  rw [← Finset.prod_pow]
  apply Finset.prod_le_prod
  · intro p hp
    linarith [hw p hp]
  · intro p _
    nlinarith [sq_nonneg (w p)]

theorem squarefree_harmonic_le_product (z : ℕ) :
    ∑ n ∈ (Icc 1 z).filter Squarefree, (n : ℝ)⁻¹ ≤
      ∏ p ∈ Nat.primesLE z, (1 + (p : ℝ)⁻¹) := by
  classical
  let U := (Icc 1 z).filter Squarefree
  let P := Nat.primesLE z
  let F := fun s : Finset ℕ => ∏ p ∈ s, (p : ℝ)⁻¹
  have hinj : Set.InjOn Nat.primeFactors (U : Set ℕ) := by
    intro a ha b hb he
    have ha' := Nat.prod_primeFactors_of_squarefree ((mem_filter.mp ha).2)
    have hb' := Nat.prod_primeFactors_of_squarefree ((mem_filter.mp hb).2)
    exact ha'.symm.trans (by rw [he, hb'])
  have hsub : U.image Nat.primeFactors ⊆ P.powerset := by
    intro S hS
    obtain ⟨n, hn, rfl⟩ := mem_image.mp hS
    apply mem_powerset.mpr
    intro p hp
    exact Nat.mem_primesLE.mpr ⟨
      (Nat.le_of_dvd (mem_Icc.mp (mem_filter.mp hn).1).1
        (Nat.dvd_of_mem_primeFactors hp)).trans (mem_Icc.mp (mem_filter.mp hn).1).2,
      Nat.prime_of_mem_primeFactors hp⟩
  calc
    _ = ∑ n ∈ U, F n.primeFactors := by
      apply Finset.sum_congr rfl
      intro n hn
      dsimp only [F]
      rw [Finset.prod_inv_distrib, ← Nat.cast_prod,
        Nat.prod_primeFactors_of_squarefree (mem_filter.mp hn).2]
    _ = ∑ S ∈ U.image Nat.primeFactors, F S := (Finset.sum_image hinj).symm
    _ ≤ ∑ S ∈ P.powerset, F S := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun S _ _ => Finset.prod_nonneg fun p _ => by positivity)
    _ = _ := (Finset.prod_one_add P).symm

theorem sum_log_primeFactors_le (n : ℕ) (hn : 0 < n) :
    ∑ p ∈ n.primeFactors, Real.log (p : ℝ) ≤ Real.log n := by
  have hp : ∀ p ∈ n.primeFactors, (0 : ℝ) < p :=
    fun p hp => by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
  rw [← Real.log_prod (fun p hp' => (hp p hp').ne')]
  exact Real.log_le_log (Finset.prod_pos hp) (by
    rw [← Nat.cast_prod]
    exact_mod_cast Nat.le_of_dvd hn (Nat.prod_primeFactors_dvd n))

theorem count_positive_multiples (z p : ℕ) (hp : 0 < p) :
    ((Icc 1 z).filter fun n => p ∣ n).card = z / p := by
  have h : (Icc 1 z).filter (fun n => p ∣ n) =
      (Icc 1 (z / p)).image (fun k => p * k) := by
    ext n
    simp only [mem_filter, mem_Icc, mem_image]
    constructor
    · rintro ⟨⟨hn, hnz⟩, ⟨k, rfl⟩⟩
      refine ⟨k, ⟨?_, (Nat.le_div_iff_mul_le hp).2 ?_⟩, rfl⟩
      · exact Nat.pos_of_ne_zero (fun h => by simp [h] at hn)
      · simpa only [Nat.mul_comm] using hnz
    · rintro ⟨k, ⟨hk, hkz⟩, rfl⟩
      exact ⟨⟨Nat.mul_pos hp hk, by
        simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hp).1 hkz⟩,
        Nat.dvd_mul_right p k⟩
  rw [h, Finset.card_image_of_injOn (fun a _ b _ h => Nat.mul_left_cancel hp h)]
  simp [Nat.card_Icc]

theorem sum_floor_log_prime_le (z : ℕ) :
    ∑ p ∈ Nat.primesLE z, ((z / p : ℕ) : ℝ) * Real.log (p : ℝ) ≤
      (z : ℝ) * Real.log z := by
  classical
  calc
    _ = ∑ p ∈ Nat.primesLE z, ∑ n ∈ Icc 1 z,
          if p ∣ n then Real.log (p : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul,
        count_positive_multiples z p (Nat.prime_of_mem_primesLE hp).pos]
    _ = ∑ n ∈ Icc 1 z, ∑ p ∈ Nat.primesLE z,
          if p ∣ n then Real.log (p : ℝ) else 0 := Finset.sum_comm
    _ ≤ ∑ _n ∈ Icc 1 z, Real.log (z : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      obtain ⟨hn0, hnz⟩ := mem_Icc.mp hn
      have hset : (Nat.primesLE z).filter (fun p => p ∣ n) = n.primeFactors := by
        ext p
        simp only [mem_filter, Nat.mem_primesLE, Nat.mem_primeFactors]
        exact ⟨fun h => ⟨h.1.2, h.2, (show 0 < n from hn0).ne'⟩,
          fun h => ⟨⟨(Nat.le_of_dvd hn0 h.2.1).trans hnz, h.1⟩, h.2.1⟩⟩
      rw [← Finset.sum_filter, hset]
      exact (sum_log_primeFactors_le n hn0).trans (Real.log_le_log (by exact_mod_cast hn0)
        (by exact_mod_cast hnz))
    _ = _ := by simp [Nat.card_Icc]

theorem divisor_card_of_squarefree {b : ℕ} (hb : Squarefree b) :
    b.divisors.card = 2 ^ b.primeFactors.card := by
  rw [Nat.card_divisors hb.ne_zero]
  calc
    _ = ∏ p ∈ b.primeFactors, (2 : ℕ) := by
      apply Finset.prod_congr rfl
      intro p hp
      rw [Nat.factorization_eq_one_of_squarefree hb (Nat.prime_of_mem_primeFactors hp)
        (Nat.dvd_of_mem_primeFactors hp)]
    _ = _ := by simp

theorem prime_subset_product_data (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    let b := ∏ p ∈ S, p
    Squarefree b ∧ b.primeFactors = S ∧ b.divisors.card = 2 ^ S.card ∧
      (∏ p ∈ S, (2 * (p : ℝ))⁻¹) = (2 ^ S.card * (b : ℝ))⁻¹ := by
  let b := ∏ p ∈ S, p
  have hsq : Squarefree b := by
    apply Finset.squarefree_prod_of_pairwise_isCoprime
    · intro p hp q hq hne
      exact Nat.coprime_iff_isRelPrime.mp
        ((Nat.coprime_primes (hS p hp) (hS q hq)).mpr hne)
    · exact fun p hp => (hS p hp).squarefree
  have hf : b.primeFactors = S := Nat.primeFactors_prod hS
  refine ⟨hsq, hf, by rw [divisor_card_of_squarefree hsq, hf], ?_⟩
  rw [Finset.prod_inv_distrib, Finset.prod_mul_distrib, Finset.prod_const]
  simp [b]

theorem sum_log_div_prime_le (z : ℕ) (hz : 0 < z) :
    ∑ p ∈ Nat.primesLE z, Real.log (p : ℝ) / (2 * p) ≤ Real.log z := by
  have hzR : 0 < (z : ℝ) := by exact_mod_cast hz
  have hpoint : ∀ p ∈ Nat.primesLE z,
      (z : ℝ) * (Real.log (p : ℝ) / (2 * p)) ≤
        ((z / p : ℕ) : ℝ) * Real.log (p : ℝ) := by
    intro p hp
    have hp0 := (Nat.prime_of_mem_primesLE hp).pos
    have hpR : 0 < (p : ℝ) := by exact_mod_cast hp0
    have hqp : 0 < z / p := Nat.div_pos (Nat.le_of_mem_primesLE hp) hp0
    have hzle : z ≤ 2 * p * (z / p) := by
      have hr := Nat.mod_lt z hp0
      have he := Nat.mod_add_div z p
      have hprod : p ≤ p * (z / p) := by simpa using Nat.mul_le_mul_left p (show 1 ≤ z / p from hqp)
      rw [two_mul, Nat.add_mul]
      omega
    have hR : (z : ℝ) / (2 * p) ≤ (z / p : ℕ) := by
      rw [div_le_iff₀ (show 0 < (2 : ℝ) * p by positivity)] <;> exact_mod_cast (show z ≤ (z / p) * (2 * p) by simpa [Nat.mul_comm] using hzle)
    calc
      _ = ((z : ℝ) / (2 * p)) * Real.log p := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hR (Real.log_nonneg (by exact_mod_cast hp0))

  have hsum := (Finset.sum_le_sum hpoint).trans (sum_floor_log_prime_le z)
  rw [← Finset.mul_sum] at hsum
  exact le_of_mul_le_mul_left hsum hzR

theorem retain_two_costs {α : Type*} [DecidableEq α] (P : Finset α)
    (w f g : α → ℝ) {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (hw : ∀ p ∈ P, 0 ≤ w p) (hf : ∀ p ∈ P, 0 ≤ f p) (hg : ∀ p ∈ P, 0 ≤ g p)
    (hfs : ∑ p ∈ P, w p * f p ≤ s / 4)
    (hgt : ∑ p ∈ P, w p * g p ≤ t / 4) :
    (1 / 2 : ℝ) * (∏ p ∈ P, (1 + w p)) ≤
      ∑ S ∈ P.powerset.filter (fun S => (∑ p ∈ S, f p) ≤ s ∧ (∑ p ∈ S, g p) ≤ t),
        ∏ p ∈ S, w p := by
  let M := ∏ p ∈ P, (1 + w p)
  let W := fun S : Finset α => ∏ p ∈ S, w p
  let F := fun S : Finset α => ∑ p ∈ S, f p
  let G := fun S : Finset α => ∑ p ∈ S, g p
  have hM : 0 ≤ M := Finset.prod_nonneg fun p hp => by linarith [hw p hp]
  have hW : ∀ S ∈ P.powerset, 0 ≤ W S := fun S hS =>
    Finset.prod_nonneg fun p hp => hw p (mem_powerset.mp hS hp)
  have hsum : ∑ S ∈ P.powerset, W S = M := (Finset.prod_one_add P).symm
  have hF : ∑ S ∈ P.powerset.filter (fun S => s < F S), W S ≤ M / 4 := by
    have h := weight_of_large_cost P.powerset W F hs hW
      (fun S hS => Finset.sum_nonneg fun p hp => hf p (mem_powerset.mp hS hp))
      ((subset_first_moment P w f hw hf).trans (mul_le_mul_of_nonneg_left hfs hM))
    refine h.trans_eq ?_
    change M * (_ / 4) / _ = M / 4
    field_simp
  have hG : ∑ S ∈ P.powerset.filter (fun S => t < G S), W S ≤ M / 4 := by
    have h := weight_of_large_cost P.powerset W G ht hW
      (fun S hS => Finset.sum_nonneg fun p hp => hg p (mem_powerset.mp hS hp))
      ((subset_first_moment P w g hw hg).trans (mul_le_mul_of_nonneg_left hgt hM))
    refine h.trans_eq ?_
    change M * (_ / 4) / _ = M / 4
    field_simp
  have hcover : (∑ S ∈ P.powerset, W S) ≤
      (∑ S ∈ P.powerset.filter (fun S => F S ≤ s ∧ G S ≤ t), W S) +
        (∑ S ∈ P.powerset.filter (fun S => s < F S), W S) +
        (∑ S ∈ P.powerset.filter (fun S => t < G S), W S) := by
    simp only [Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro S hS
    by_cases hf' : F S ≤ s <;> by_cases hg' : G S ≤ t <;>
      simp only [hf', hg', and_self, and_false, false_and, not_le.mpr, not_lt_of_ge, if_true, if_false, add_zero, zero_add] <;> try linarith [hW S hS]
    all_goals simp [hf', hg', lt_of_not_ge, hW S hS]
  change (1 / 2 : ℝ) * M ≤
    ∑ S ∈ P.powerset.filter (fun S => F S ≤ s ∧ G S ≤ t), W S
  linarith

end Hall394Cofactors




















open Filter Finset
open scoped Asymptotics Topology Nat

namespace Hall394Assembly

theorem sum_over_prime_cofactors {x : ℝ} (cutoff : ℕ) (B : Finset ℕ)
    (P : ℕ → Finset ℕ) (W : ℕ → ℝ)
    (hB : ∀ b ∈ B, 0 < b ∧ b ≤ cutoff)
    (hP : ∀ b ∈ B, ∀ p ∈ P b, p.Prime ∧ cutoff < p ∧ p * b ≤ ⌊x⌋₊)
    (hW : ∀ b ∈ B, ∀ p ∈ P b, W b ≤ (Erdos394.t 2 (p * b) : ℝ)) :
    ∑ b ∈ B, ((P b).card : ℝ) * W b ≤ Hall394.total x := by
  classical
  let S := fun b => (P b).image (fun p => p * b)
  have hcard : ∀ b ∈ B, (S b).card = (P b).card := by
    intro b hb
    apply Finset.card_image_of_injOn
    intro p _ q _ h
    change p * b = q * b at h
    exact Nat.mul_right_cancel (hB b hb).1 h
  have hd : (B : Set ℕ).PairwiseDisjoint S := by
    intro a ha b hb hab
    apply Finset.disjoint_left.mpr
    intro n hn hm
    obtain ⟨p, hp, rfl⟩ := mem_image.mp (show n ∈ S a from hn)
    obtain ⟨q, hq, he⟩ := mem_image.mp (show p * a ∈ S b from hm)
    exact hab ((Hall394.large_prime_factorization_unique (hP a ha p hp).1
      (hP b hb q hq).1 (hB b hb).1 (hP a ha p hp).2.1 (hB b hb).2 he.symm).2)
  have hsub : ∀ b ∈ B, S b ⊆ Icc 1 ⌊x⌋₊ := by
    intro b hb n hn
    obtain ⟨p, hp, rfl⟩ := mem_image.mp (show n ∈ S b from hn)
    exact mem_Icc.mpr ⟨Nat.mul_pos (hP b hb p hp).1.pos (hB b hb).1,
      (hP b hb p hp).2.2⟩
  have hlower : ∀ b ∈ B, ∀ n ∈ S b, W b ≤ (Erdos394.t 2 n : ℝ) := by
    intro b hb n hn
    obtain ⟨p, hp, rfl⟩ := mem_image.mp (show n ∈ S b from hn)
    exact hW b hb p hp
  have h := Hall394Counting.weighted_sum_le_of_disjoint (Icc 1 ⌊x⌋₊) B S
    (fun n => (Erdos394.t 2 n : ℝ)) W hd hsub (fun n _ => Nat.cast_nonneg _) hlower
  unfold Hall394.total
  convert h using 1
  exact Finset.sum_congr rfl fun b hb => by rw [hcard b hb]

end Hall394Assembly



/- Choice of a small sieve level with a negligible remainder. -/
open Filter
open scoped Asymptotics Topology Nat

namespace Hall394SieveLevel

theorem eventually_level :
    ∀ᶠ x : ℝ in atTop, ∃ z : ℕ, 1 < z ∧
      Real.log x / 32 ≤ Real.log (z : ℝ) ∧
      (∀ q : ℝ, 0 ≤ q → q ≤ x ^ (1 / 2 : ℝ) →
        q * Real.log x * (z : ℝ)^4 ≤ x) ∧ (z : ℝ) ≤ x ^ (1 / 16 : ℝ) := by
  have hroot := (tendsto_rpow_atTop (show (0 : ℝ) < 1 / 32 by norm_num)).eventually
    (eventually_ge_atTop (2 : ℝ))
  have hlog0 := Asymptotics.isLittleO_iff.mp
    (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / 4 by norm_num))
    (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [hroot, hlog0, eventually_gt_atTop (1 : ℝ)] with x hr hl hx
  let y := x ^ (1 / 16 : ℝ)
  let z := ⌊y⌋₊
  have hx0 : 0 < x := by linarith
  have hy : 0 ≤ y := Real.rpow_nonneg hx0.le _
  have hzup : (z : ℝ) ≤ y := Nat.floor_le hy
  have hzlow : x ^ (1 / 32 : ℝ) ≤ (z : ℝ) := by
    have hsq : y = (x ^ (1 / 32 : ℝ)) ^ (2 : ℕ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
      norm_num [y]
    have hf := Nat.lt_floor_add_one y
    change y < (z : ℝ) + 1 at hf
    nlinarith
  have hz : 1 < z := by
    exact_mod_cast (show (1 : ℝ) < z by linarith)
  have hl' : Real.log x ≤ x ^ (1 / 4 : ℝ) := by
    change ‖Real.log x‖ ≤ 1 * ‖x ^ (1 / 4 : ℝ)‖ at hl
    rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hx0.le _)] at hl
    exact (le_abs_self _).trans hl
  refine ⟨z, hz, ?_, ?_, hzup⟩
  · have hh := Real.log_le_log (Real.rpow_pos_of_pos hx0 _) hzlow
    rw [Real.log_rpow hx0] at hh
    linarith
  · intro q hq hqx
    have hzp : (z : ℝ)^4 ≤ x ^ (1 / 4 : ℝ) := by
      calc
        _ ≤ y^4 := pow_le_pow_left₀ (Nat.cast_nonneg _) hzup 4
        _ = _ := by rw [show y = x ^ (1 / 16 : ℝ) from rfl, ← Real.rpow_natCast,
            ← Real.rpow_mul hx0.le]; norm_num
    have hxlog : 0 ≤ Real.log x := (Real.log_pos hx).le
    calc
      _ ≤ (x ^ (1 / 2 : ℝ) * x ^ (1 / 4 : ℝ)) * x ^ (1 / 4 : ℝ) :=
        mul_le_mul (mul_le_mul hqx hl' hxlog (Real.rpow_nonneg hx0.le _))
          hzp (by positivity) (by positivity)
      _ = x := by
        rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]
        norm_num

end Hall394SieveLevel

open Filter Finset
open scoped Asymptotics Topology Nat

namespace Hall394FinalAssembly

theorem weighted_lower_bound {x : ℝ} (hx : 1 < x) (cutoff : ℕ) (B : Finset ℕ)
    (P : ℕ → Finset ℕ) {a c : ℝ} (ha : 0 < a) (hc : 0 < c)
    (hB : ∀ b ∈ B, 0 < b ∧ b ≤ cutoff)
    (hP : ∀ b ∈ B, ∀ p ∈ P b, p.Prime ∧ cutoff < p ∧ p * b ≤ ⌊x⌋₊)
    (hcount : ∀ b ∈ B, a * (x / (b * Real.log x)) ≤ ((P b).card : ℝ))
    (hstart : ∀ b ∈ B, ∀ p ∈ P b,
      c * (x / (b.divisors.card : ℝ)) ≤ (Erdos394.t 2 (p * b) : ℝ)) :
    (a * c) * (x ^ 2 / Real.log x) *
      (∑ b ∈ B, ((b : ℝ) * b.divisors.card)⁻¹) ≤ Hall394.total x := by
  have hL := Real.log_pos hx
  have hx0 : 0 < x := by linarith
  have hsum := Hall394Assembly.sum_over_prime_cofactors cutoff B P
    (fun b => c * (x / (b.divisors.card : ℝ))) hB hP hstart
  refine le_trans ?_ hsum
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro b hb
  have hdiv : 0 < b.divisors.card := Finset.card_pos.mpr
    ⟨1, Nat.mem_divisors.mpr ⟨one_dvd _, (hB b hb).1.ne'⟩⟩
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (hB b hb).1
  have hd0 : (0 : ℝ) < b.divisors.card := by exact_mod_cast hdiv
  calc
    _ = (a * (x / (b * Real.log x))) * (c * (x / (b.divisors.card : ℝ))) := by
      field_simp
      <;> ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (hcount b hb) (by positivity)

theorem half_exponent_of_assembled_data
    {a c d : ℝ} (ha : 0 < a) (hc : 0 < c) (hd : 0 < d)
    (h : ∀ᶠ x : ℝ in atTop, ∃ (cutoff : ℕ) (B : Finset ℕ) (P : ℕ → Finset ℕ),
      (∀ b ∈ B, 0 < b ∧ b ≤ cutoff) ∧
      (∀ b ∈ B, ∀ p ∈ P b, p.Prime ∧ cutoff < p ∧ p * b ≤ ⌊x⌋₊) ∧
      (∀ b ∈ B, a * (x / (b * Real.log x)) ≤ ((P b).card : ℝ)) ∧
      (∀ b ∈ B, ∀ p ∈ P b, c * (x / (b.divisors.card : ℝ)) ≤
        (Erdos394.t 2 (p * b) : ℝ)) ∧
      d * (Real.log x) ^ (1 / 2 : ℝ) ≤
        ∑ b ∈ B, ((b : ℝ) * b.divisors.card)⁻¹) :
    ¬ (type_of% @Erdos394.erdos_394.variants.hall_conjecture) := by
  apply Hall394.refute_of_half_exponent
  refine ⟨a * c * d, by positivity, ?_⟩
  apply Filter.Eventually.frequently
  filter_upwards [h, eventually_gt_atTop (1 : ℝ)] with x hx hx1
  obtain ⟨cutoff, B, P, hB, hP, hcount, hstart, hmass⟩ := hx
  have hL := Real.log_pos hx1
  refine (le_trans ?_ (weighted_lower_bound hx1 cutoff B P ha hc hB hP hcount hstart))
  refine le_trans ?_ (mul_le_mul_of_nonneg_left hmass (show 0 ≤ (a*c) * (x^2 / Real.log x) by positivity))
  have heq : (Real.log x) ^ (1 / 2 : ℝ) * (Real.log x) ^ (1 / 2 : ℝ) = Real.log x := by
    rw [← Real.rpow_add hL]
    norm_num
  apply le_of_eq
  have hhalf : 0 < (Real.log x) ^ (1/2 : ℝ) := Real.rpow_pos_of_pos hL _
  field_simp [hL.ne', hhalf.ne']
  <;> nlinarith only [heq, congrArg (fun r : ℝ => (a*c*d*x^2)*r) heq]

end Hall394FinalAssembly


open Filter Finset
open scoped Asymptotics Topology Nat

namespace Hall394CofactorMass

noncomputable def primeMass (P : Finset ℕ) : ℝ :=
  ∏ p ∈ P, (1 + (p : ℝ)⁻¹)

noncomputable def halfMass (P : Finset ℕ) : ℝ :=
  ∏ p ∈ P, (1 + (p : ℝ)⁻¹ / 2)

theorem primeMass_ge {z : ℕ} : Real.log (z : ℝ) / 8 ≤ primeMass (Nat.primesLE z) := by
  classical
  have hn : ∑ p ∈ (1 : ℕ).primeFactors, Hall394Harmonic.weight p ≤ 1 / 8 := by norm_num
  have h := Hall394Harmonic.good_weight_ge z 1 (by decide) hn
  have hlog := Hall394Harmonic.log_le_sum_weights z
  have h1 : Real.log (z : ℝ) / 8 ≤
      (1 / 8 : ℝ) * ∑ n ∈ Icc 1 z, Hall394Harmonic.weight n := by linarith
  refine (h1.trans ?_).trans (Hall394Cofactors.squarefree_harmonic_le_product z)
  simpa only [Nat.coprime_one_right_iff, and_true, ← Finset.sum_filter, Hall394Harmonic.weight] using h

theorem mass_above_fixed_lower {z : ℕ} (hz : 64 ≤ z) :
    Real.log (z : ℝ) / (8 * primeMass (Nat.primesLE 64)) ≤
      (halfMass (Nat.primesLE z \ Nat.primesLE 64))^2 := by
  let P := Nat.primesLE z \ Nat.primesLE 64
  let C := primeMass (Nat.primesLE 64)
  have hC : 0 < C := Finset.prod_pos fun _ _ => by positivity
  have hfac : primeMass P * C = primeMass (Nat.primesLE z) := by
    unfold C P primeMass
    exact Finset.prod_sdiff (Nat.primesLE_mono hz)
  calc
    _ = (Real.log (z : ℝ) / 8) / C := by ring
    _ ≤ primeMass (Nat.primesLE z) / C := div_le_div_of_nonneg_right primeMass_ge hC.le
    _ = primeMass P := by rw [← hfac, mul_div_cancel_right₀ _ hC.ne']
    _ ≤ _ := Hall394Cofactors.product_square_ge P _ (fun _ _ => by positivity)

theorem tail_squares (z : ℕ) :
    ∑ n ∈ Ioc 64 z, ((n : ℝ)^2)⁻¹ ≤ 1 / 64 := by
  suffices h : ∀ z : ℕ, 64 ≤ z →
      ∑ n ∈ Ioc 64 z, ((n : ℝ)^2)⁻¹ ≤ 1 / 64 - (z : ℝ)⁻¹ by
    by_cases hz : 64 ≤ z
    · exact (h z hz).trans (sub_le_self _ (by positivity))
    · have he : Ioc 64 z = (∅ : Finset ℕ) := by
        ext n
        simp only [mem_Ioc, notMem_empty, iff_false]
        omega
      rw [he, sum_empty]
      norm_num
  intro z
  induction z with
  | zero => omega
  | succ z ih =>
    intro hz
    by_cases h : 64 ≤ z
    · have he : Ioc 64 (z+1) = insert (z+1) (Ioc 64 z) := by
        ext n
        simp only [mem_Ioc, mem_insert]
        omega
      rw [he, Finset.sum_insert (by simp)]
      have hz0 : (0 : ℝ) < z := by exact_mod_cast (show 0 < z by omega)
      have hz1 : (0 : ℝ) < (z : ℝ)+1 := by positivity
      have hstep : (((z : ℝ)+1)^2)⁻¹ ≤ (z : ℝ)⁻¹ - ((z : ℝ)+1)⁻¹ := by
        field_simp [hz0, hz1]
        nlinarith
      push_cast
      linarith [ih h]
    · have he : z+1 = 64 := by omega
      rw [he]
      norm_num

theorem reciprocal_cost_le (z : ℕ) :
    ∑ p ∈ Nat.primesLE z \ Nat.primesLE 64,
      ((p : ℝ)⁻¹ / 2) * (p : ℝ)⁻¹ ≤ (1 / 8 : ℝ) / 4 := by
  have hsub : Nat.primesLE z \ Nat.primesLE 64 ⊆ Ioc 64 z := by
    intro p hp
    obtain ⟨hlarge, hsmall⟩ := Finset.mem_sdiff.mp hp
    obtain ⟨hle,hpr⟩ := Nat.mem_primesLE.mp hlarge
    refine Finset.mem_Ioc.mpr ⟨?_,hle⟩
    exact lt_of_not_ge fun h => hsmall (Nat.mem_primesLE.mpr ⟨h,hpr⟩)
  have h := Finset.sum_le_sum_of_subset_of_nonneg (f := fun n : ℕ => ((n : ℝ)^2)⁻¹) hsub (fun n _ _ => by positivity)
  have heq : ∀ p : ℕ, ((p : ℝ)⁻¹ / 2) * (p : ℝ)⁻¹ =
      ((p : ℝ)^2)⁻¹ / 2 := by
    intro p
    rw [← inv_pow]
    ring
  simp_rw [heq, div_eq_mul_inv, ← Finset.sum_mul]
  norm_num
  linarith [h.trans (tail_squares z)]

theorem log_cost_le (z : ℕ) (hz : 0 < z) :
    ∑ p ∈ Nat.primesLE z \ Nat.primesLE 64,
      ((p : ℝ)⁻¹ / 2) * Real.log (p : ℝ) ≤ Real.log z := by
  calc
    _ ≤ ∑ p ∈ Nat.primesLE z, ((p : ℝ)⁻¹ / 2) * Real.log (p : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset (fun p hp _ => by
        have hp' : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primesLE hp).pos
        exact mul_nonneg (by positivity) (Real.log_nonneg hp'))
    _ = ∑ p ∈ Nat.primesLE z, Real.log (p : ℝ) / (2 * p) := by
      exact Finset.sum_congr rfl fun p _ => by ring
    _ ≤ _ := Hall394Cofactors.sum_log_div_prime_le z hz

noncomputable def goodSubsets (x : ℝ) (z : ℕ) : Finset (Finset ℕ) :=
  ((Nat.primesLE z \ Nat.primesLE 64).powerset).filter fun S =>
    (∑ p ∈ S, Real.log (p : ℝ)) ≤ Real.log x / 3 ∧
      (∑ p ∈ S, (p : ℝ)⁻¹) ≤ 1 / 8

theorem goodSubsets_weight {x : ℝ} {z : ℕ} (hx : 1 < x) (hz : 64 ≤ z)
    (hlog : Real.log (z : ℝ) ≤ Real.log x / 12) :
    (1 / 2 : ℝ) * halfMass (Nat.primesLE z \ Nat.primesLE 64) ≤
      ∑ S ∈ goodSubsets x z, ∏ p ∈ S, ((p : ℝ)⁻¹ / 2) := by
  classical
  have hL := Real.log_pos hx
  apply Hall394Cofactors.retain_two_costs _ _ _ _ (by positivity) (by norm_num)
  · intro p _
    positivity
  · intro p hp
    have hp1 := (Nat.prime_of_mem_primesLE (Finset.mem_sdiff.mp hp).1).pos
    exact Real.log_nonneg (by exact_mod_cast hp1)
  · intro p _
    positivity
  · linarith [log_cost_le z (by omega)]
  · exact reciprocal_cost_le z

def cofactor (S : Finset ℕ) : ℕ := ∏ p ∈ S, p

noncomputable def cofactors (x : ℝ) (z : ℕ) : Finset ℕ :=
  (goodSubsets x z).image cofactor

theorem subset_primes {x : ℝ} {z : ℕ} {S : Finset ℕ} (hS : S ∈ goodSubsets x z) :
    ∀ p ∈ S, p.Prime := by
  classical
  intro p hp
  have hsub := Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1
  exact Nat.prime_of_mem_primesLE (Finset.mem_sdiff.mp (hsub hp)).1

theorem cofactors_spec {x : ℝ} {z : ℕ} {b : ℕ} (hx : 0 < x)
    (hb : b ∈ cofactors x z) :
    0 < b ∧ (b : ℝ) ≤ x ^ (1 / 3 : ℝ) ∧
      ∑ p ∈ b.primeFactors, Hall394Harmonic.weight p ≤ 1 / 8 := by
  classical
  obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hb
  have hprime := subset_primes hS
  obtain ⟨hsq, hf, _, _⟩ := Hall394Cofactors.prime_subset_product_data S hprime
  have hpos : 0 < cofactor S := Nat.pos_of_ne_zero hsq.ne_zero
  have hbpos : (0 : ℝ) < cofactor S := by exact_mod_cast hpos
  have hcost := (Finset.mem_filter.mp hS).2
  refine ⟨hpos, (Real.log_le_log_iff hbpos (Real.rpow_pos_of_pos hx _)).mp ?_, ?_⟩
  · rw [Real.log_rpow hx]
    unfold cofactor
    rw [Nat.cast_prod, Real.log_prod (fun p hp => by exact_mod_cast (hprime p hp).ne_zero)]
    linarith [hcost.1]
  · simpa only [cofactor, hf, Hall394Harmonic.weight] using hcost.2

theorem cofactors_weight {x : ℝ} {z : ℕ} (hx : 1 < x) (hz : 64 ≤ z)
    (hlog : Real.log (z : ℝ) ≤ Real.log x / 12) :
    (1 / 2 : ℝ) * halfMass (Nat.primesLE z \ Nat.primesLE 64) ≤
      ∑ b ∈ cofactors x z, ((b : ℝ) * b.divisors.card)⁻¹ := by
  classical
  have hinj : Set.InjOn cofactor (goodSubsets x z : Set (Finset ℕ)) := by
    intro S hS T hT h
    exact (Nat.primeFactors_prod (subset_primes hS)).symm.trans
      ((congrArg Nat.primeFactors h).trans (Nat.primeFactors_prod (subset_primes hT)))
  refine (goodSubsets_weight hx hz hlog).trans_eq ?_
  unfold cofactors
  rw [Finset.sum_image hinj]
  apply Finset.sum_congr rfl
  intro S hS
  obtain ⟨_,_, hd,hprod⟩ := Hall394Cofactors.prime_subset_product_data S (subset_primes hS)
  simp_rw [show ∀ p : ℕ, (p : ℝ)⁻¹ / 2 = (2 * (p : ℝ))⁻¹ by intro p; rw [mul_inv]; ring]
  rw [hprod]
  dsimp only [cofactor]
  simp only [hd, Nat.cast_pow, Nat.cast_ofNat, mul_comm]

theorem eventually_cofactor_data :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ x : ℝ in atTop, ∃ B : Finset ℕ,
      (∀ b ∈ B, 0 < b ∧ (b : ℝ) ≤ x ^ (1 / 3 : ℝ) ∧
        ∑ p ∈ b.primeFactors, Hall394Harmonic.weight p ≤ 1/8) ∧
      D * (Real.log x) ^ (1 / 2 : ℝ) ≤
        ∑ b ∈ B, ((b : ℝ) * b.divisors.card)⁻¹ := by
  let C := 2048 * primeMass (Nat.primesLE 64)
  have hC : 0 < C := mul_pos (by norm_num) (Finset.prod_pos fun _ _ => by positivity)
  refine ⟨(C⁻¹) ^ (1 / 2 : ℝ) / 2, by positivity, ?_⟩
  let y := fun x : ℝ => x ^ (1 / 8 : ℝ)
  have hy : Tendsto y atTop atTop := tendsto_rpow_atTop (by norm_num)
  have hy' : ∀ᶠ x : ℝ in atTop, Real.log (y x) ≥ 32 * Real.log 64 :=
    (Real.tendsto_log_atTop.comp hy).eventually (eventually_ge_atTop _)
  filter_upwards [hy.eventually Hall394SieveLevel.eventually_level, hy',
    eventually_gt_atTop (1 : ℝ)] with x hz hy' hx
  obtain ⟨z, hz, hzlog, _, hzupper⟩ := hz
  have hx0 : 0 < x := by linarith
  have hz64 : 64 ≤ z := by
    have hl : Real.log 64 ≤ Real.log (z : ℝ) := by linarith
    exact_mod_cast (Real.log_le_log_iff (by norm_num) (by exact_mod_cast (show 0 < z by omega))).mp hl
  rw [show Real.log (y x) = (1 / 8 : ℝ) * Real.log x from Real.log_rpow hx0 _] at hzlog
  have hzbig : Real.log x / 256 ≤ Real.log (z : ℝ) := by linarith
  have hzsmall : Real.log (z : ℝ) ≤ Real.log x / 12 := by
    have h := Real.log_le_log (by exact_mod_cast (show 0 < z by omega)) hzupper
    rw [Real.log_rpow (Real.rpow_pos_of_pos hx0 _), Real.log_rpow hx0] at h
    linarith [(Real.log_pos hx).le]
  refine ⟨cofactors x z, fun b hb => cofactors_spec hx0 hb, ?_⟩
  refine le_trans ?_ (cofactors_weight hx hz64 hzsmall)
  have hp := mass_above_fixed_lower hz64
  have hM : 0 ≤ halfMass (Nat.primesLE z \ Nat.primesLE 64) :=
    Finset.prod_nonneg fun _ _ => by positivity
  have ht : Real.log x * C⁻¹ ≤ (halfMass (Nat.primesLE z \ Nat.primesLE 64))^2 := by
    refine le_trans ?_ hp
    calc
      _ = (Real.log x / 256) / (8 * primeMass (Nat.primesLE 64)) := by
        unfold C
        ring
      _ ≤ _ := div_le_div_of_nonneg_right hzbig (mul_nonneg (by norm_num) (Finset.prod_nonneg fun _ _ => by positivity))
  have ht' := Real.rpow_le_rpow (mul_nonneg (Real.log_pos hx).le (inv_nonneg.mpr hC.le)) ht
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [Real.mul_rpow (Real.log_pos hx).le (inv_nonneg.mpr hC.le),
    ← Real.rpow_natCast, ← Real.rpow_mul hM] at ht'
  norm_num at ht'
  nlinarith only [ht']

end Hall394CofactorMass









open Filter Finset
open scoped Asymptotics Topology Nat

namespace Hall394Sample

noncomputable def endPoint (x : ℝ) (b : ℕ) : ℕ := ⌊x / b⌋₊ + 1

noncomputable def primes (x : ℝ) (b : ℕ) : Finset ℕ :=
  Hall394GoodPrimes.good (Hall394Counting.primeWindow (endPoint x b)) b
    (16384 * (b.divisors.card : ℝ))⁻¹

theorem sample_bounds {x : ℝ} {b z cutoff : ℕ} (hx : 2 ≤ x) (hb : 0 < b)
    (hbsmall : ∑ p ∈ b.primeFactors, Hall394Harmonic.weight p ≤ 1/8)
    (hz : 1 < z)
    (hlog : Real.log (endPoint x b : ℝ) / 32 ≤ Real.log (z : ℝ))
    (hN : 1 < endPoint x b)
    (herr : (b : ℝ) * Real.log (endPoint x b : ℝ) * (z : ℝ)^4 ≤ endPoint x b)
    (hwindow : (endPoint x b : ℝ) / (8 * Real.log (endPoint x b)) ≤
      ((Hall394Counting.primeWindow (endPoint x b)).card : ℝ))
    (hcut : (16 : ℝ) * max (cutoff : ℝ) z ≤ endPoint x b)
    (hbig : (524288 : ℝ) * (b.divisors.card : ℝ) ≤ x) :
    (∀ p ∈ primes x b, p.Prime ∧ cutoff < p ∧ p * b ≤ ⌊x⌋₊) ∧
    (1 / 32 : ℝ) * (x / (b * Real.log x)) ≤ ((primes x b).card : ℝ) ∧
    (∀ p ∈ primes x b,
      (1 / 524288 : ℝ) * (x / (b.divisors.card : ℝ)) ≤
        (Erdos394.t 2 (p*b) : ℝ)) := by
  classical
  let N := endPoint x b
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hx0 : 0 < x := by linarith
  have hNlo : x / (b : ℝ) < N := by
    simpa only [N, endPoint, Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one (x / (b : ℝ))
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast (show 1 ≤ b from hb)
  have hNup : (N : ℝ) ≤ 2*x := by
    have hf : (⌊x / (b : ℝ)⌋₊ : ℝ) ≤ x / b := Nat.floor_le (by positivity)
    have hdiv : x / (b : ℝ) ≤ x := (div_le_iff₀ hbR).mpr (by nlinarith)
    simp only [N, endPoint, Nat.cast_add, Nat.cast_one]
    linarith
  have hP : ∀ p ∈ Hall394Counting.primeWindow N,
      p < N ∧ p.Prime ∧ z < p ∧ cutoff < p ∧ (N : ℝ) / 16 < p := by
    intro p hp
    have hh := Finset.mem_sdiff.mp hp
    obtain ⟨hle,hpr⟩ := Nat.mem_primesLE.mp hh.1
    have hgt : (N : ℝ) / 16 < p := by
      by_contra! hh'
      exact hh.2 (Nat.mem_primesLE.mpr ⟨Nat.le_floor hh',hpr⟩)
    have hcu : (cutoff : ℝ) < p := by linarith [le_max_left (cutoff : ℝ) (z : ℝ)]
    have hzu : (z : ℝ) < p := by linarith [le_max_right (cutoff : ℝ) (z : ℝ)]
    exact ⟨by omega,hpr,by exact_mod_cast hzu,by exact_mod_cast hcu,hgt⟩
  have hmem : ∀ p ∈ primes x b, p ∈ Hall394Counting.primeWindow N :=
    fun p hp => (Finset.mem_filter.mp hp).1
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨hpN,hpr,_,hpc,_⟩ := hP p (hmem p hp)
    refine ⟨hpr,hpc,Nat.le_floor ?_⟩
    have hpf : p ≤ ⌊x / (b : ℝ)⌋₊ := by
      change p < ⌊x / (b : ℝ)⌋₊ + 1 at hpN
      omega
    have hh : (p : ℝ) ≤ x / b := (Nat.cast_le.mpr hpf).trans (Nat.floor_le (by positivity))
    simpa only [Nat.cast_mul] using (le_div_iff₀ hbR).mp hh
  · have hcount := Hall394GoodPrimes.good_card hb hz hbsmall hlog hN herr
      (fun p hp => let h := hP p hp; ⟨h.1,h.2.1,h.2.2.1⟩) hwindow
    refine le_trans ?_ hcount
    have hL := Real.log_pos (show 1 < x by linarith)
    have hLN : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
    have hlogN : Real.log (N : ℝ) ≤ 2 * Real.log x := by
      have h2 : (N : ℝ) ≤ x^2 := by nlinarith [hNup]
      exact (Real.log_le_log (by positivity : 0 < (N : ℝ)) h2).trans_eq (by rw [Real.log_pow]; norm_num)
    have hxb := (div_lt_iff₀ hbR).mp hNlo
    rw [show (1 / 32 : ℝ) * (x / (b * Real.log x)) = x / (32 * (b * Real.log x)) by ring]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith only [mul_le_mul_of_nonneg_left hlogN hx0.le,
      mul_le_mul_of_nonneg_right hxb.le hL.le]
  · intro p hp
    have ht := Hall394GoodPrimes.t_lower_of_good (hP p (hmem p hp)).2.1 hb hp
    have hpr := (hP p (hmem p hp)).2.2.2.2
    have hpx : x / 16 < (p : ℝ) * b := by
      have h1 := mul_lt_mul_of_pos_right hpr hbR
      have h2 := (div_lt_iff₀ hbR).mp hNlo
      linarith
    have hd : 0 < b.divisors.card := Finset.card_pos.mpr
      ⟨1, Nat.mem_divisors.mpr ⟨one_dvd _,hb.ne'⟩⟩
    have hdR : (0 : ℝ) < b.divisors.card := by exact_mod_cast hd
    change (16384 * (b.divisors.card : ℝ))⁻¹ * ((p*b : ℕ) : ℝ) - 1 <
      (Erdos394.t 2 (p*b) : ℝ) at ht
    push_cast at ht
    have hi := mul_lt_mul_of_pos_left hpx
      (show 0 < (16384 * (b.divisors.card : ℝ))⁻¹ by positivity)
    have hbig' : 1 ≤ x / (524288 * (b.divisors.card : ℝ)) :=
      (le_div_iff₀ (by positivity)).mpr (by simpa using hbig)
    rw [show (1 / 524288 : ℝ) * (x / (b.divisors.card : ℝ)) =
      x / (524288 * (b.divisors.card : ℝ)) by ring]
    linarith only [ht, hi, hbig',
      show (16384 * (b.divisors.card : ℝ))⁻¹ * (x / 16) =
        2 * (x / (524288 * (b.divisors.card : ℝ))) by ring]

theorem eventually_sample :
    ∀ᶠ x : ℝ in atTop, ∀ b : ℕ, 0 < b → (b : ℝ) ≤ x ^ (1/3 : ℝ) →
      (∑ p ∈ b.primeFactors, Hall394Harmonic.weight p ≤ 1/8) →
      (∀ p ∈ primes x b, p.Prime ∧ ⌊x ^ (1/3 : ℝ)⌋₊ < p ∧ p * b ≤ ⌊x⌋₊) ∧
      (1 / 32 : ℝ) * (x / (b * Real.log x)) ≤ ((primes x b).card : ℝ) ∧
      (∀ p ∈ primes x b, (1 / 524288 : ℝ) * (x / (b.divisors.card : ℝ)) ≤
        (Erdos394.t 2 (p*b) : ℝ)) := by
  obtain ⟨K, hK⟩ := eventually_atTop.mp Hall394Counting.eventually_primeWindow_card
  obtain ⟨L, hL⟩ := eventually_atTop.mp Hall394SieveLevel.eventually_level
  let C : ℝ := max (max K L) 1024
  have hroot := (tendsto_rpow_atTop (show (0 : ℝ) < 1/3 by norm_num)).eventually
    (eventually_ge_atTop C)
  filter_upwards [hroot, eventually_ge_atTop (2 : ℝ)] with x hx hx2
  intro b hb hbup hbs
  let u := x ^ (1/3 : ℝ)
  let N := endPoint x b
  have hu : C ≤ u := hx
  have hu0 : 1024 ≤ u := (le_max_right _ _).trans hu
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hxb : x / (b : ℝ) < N := by
    simpa only [N, endPoint, Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one (x / (b : ℝ))
  have hucube : u^3 = x := by
    dsimp only [u]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith : 0 ≤ x)]
    norm_num
  have hN2 : u^2 < (N : ℝ) := by
    have hdiv : u^2 ≤ x / (b : ℝ) := by
      rw [le_div_iff₀ hbR, ← hucube]
      nlinarith only [mul_le_mul_of_nonneg_left hbup (sq_nonneg u)]
    exact hdiv.trans_lt hxb
  have huN : u ≤ (N : ℝ) := by nlinarith [hN2,hu0]
  have hKN : K ≤ N := by
    exact_mod_cast (((le_max_left (K : ℝ) L).trans (le_max_left _ (1024 : ℝ))).trans
      (hu.trans huN))
  have hLN : L ≤ (N : ℝ) := ((le_max_right (K : ℝ) L).trans (le_max_left _ (1024 : ℝ))).trans
    (hu.trans huN)
  obtain ⟨z,hz,hlog,herror,hzup⟩ := hL N hLN
  have hN1 : 1 < N := by exact_mod_cast (show (1 : ℝ) < N by linarith)
  have hhalf : ((N : ℝ) ^ (1/2 : ℝ))^2 = N := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : 0 ≤ (N : ℝ))]
    norm_num
  have hhalf0 : 0 ≤ (N : ℝ) ^ (1/2 : ℝ) := by positivity
  have huhalf : u ≤ (N : ℝ) ^ (1/2 : ℝ) := by
    by_contra! h
    have hsq := pow_lt_pow_left₀ h hhalf0 (by decide : 2 ≠ 0)
    linarith
  have hcut1 : 16 * (⌊u⌋₊ : ℝ) ≤ N := by
    have hfloor : (⌊u⌋₊ : ℝ) ≤ u := Nat.floor_le (by linarith)
    nlinarith only [hN2, hfloor, mul_nonneg (show 0 ≤ u by linarith)
      (show 0 ≤ u - 16 by linarith)]
  have hcut2 : 16 * (z : ℝ) ≤ N := by
    have hzhalf := hzup.trans (Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast hN1.le : (1 : ℝ) ≤ N) (by norm_num : (1/16 : ℝ) ≤ 1/2))
    nlinarith only [hzhalf, hhalf, mul_nonneg hhalf0
      (show 0 ≤ (N : ℝ) ^ (1/2 : ℝ) - 16 by linarith)]
  have hcut : (16 : ℝ) * max (⌊u⌋₊ : ℝ) z ≤ N := by
    rcases le_total (⌊u⌋₊ : ℝ) z with h | h
    · rwa [max_eq_right h]
    · rwa [max_eq_left h]
  have hbig : (524288 : ℝ) * (b.divisors.card : ℝ) ≤ x := by
    have hd : (b.divisors.card : ℝ) ≤ u := (by exact_mod_cast Nat.card_divisors_le_self b :
      (b.divisors.card : ℝ) ≤ b).trans hbup
    rw [← hucube]
    have hx := mul_nonneg (show 0 ≤ u by linarith)
      (show 0 ≤ u^2 - 524288 by nlinarith [sq_nonneg (u - 1024)])
    linarith [mul_le_mul_of_nonneg_left hd (show (0 : ℝ) ≤ 524288 by norm_num)]
  exact sample_bounds hx2 hb hbs hz hlog hN1 (herror b hbR.le (hbup.trans huhalf))
    (hK N hKN) hcut hbig

end Hall394Sample



open Filter Finset
open scoped Asymptotics Topology Nat

theorem OMA.disproof : ¬ (type_of% @Erdos394.erdos_394.variants.hall_conjecture) := by
  obtain ⟨d, hd, hcofactors⟩ := Hall394CofactorMass.eventually_cofactor_data
  apply Hall394FinalAssembly.half_exponent_of_assembled_data
    (a := 1/32) (c := 1/524288) (d := d) (by norm_num) (by norm_num) hd
  filter_upwards [hcofactors, Hall394Sample.eventually_sample] with x hx hs
  obtain ⟨B, hB, hm⟩ := hx
  refine ⟨⌊x ^ (1/3 : ℝ)⌋₊, B, Hall394Sample.primes x, ?_, ?_, ?_, ?_, hm⟩
  · exact fun b hb => ⟨(hB b hb).1, Nat.le_floor (hB b hb).2.1⟩
  · exact fun b hb => (hs b (hB b hb).1 (hB b hb).2.1 (hB b hb).2.2).1
  · exact fun b hb => (hs b (hB b hb).1 (hB b hb).2.1 (hB b hb).2.2).2.1
  · exact fun b hb => (hs b (hB b hb).1 (hB b hb).2.1 (hB b hb).2.2).2.2
