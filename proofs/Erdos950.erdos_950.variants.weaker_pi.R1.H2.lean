import OMAReductions.R_Erdos950_erdos_950_variants_weaker_pi_R1
import Mathlib

/-! Mertens lower bound with `C = 1`. The Euler product over the primes up to `x` is a sum of
`1 / m` over smooth `m` (`EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric`),
hence at least the harmonic number `H_x ≥ log (x + 1)`. Taking logarithms and using
`-log (1 - 1/p) ≤ 1/p + 1/(p (p - 1))` with `∑ 1/(n (n - 1)) ≤ 1` gives the bound. -/

namespace OMA.Step_Erdos950_erdos_950_variants_weaker_pi_R1_H2

open Finset

/-- `m ↦ 1 / m` as a multiplicative map. -/
noncomputable def invHom : ℕ →* ℝ where
  toFun m := (m : ℝ)⁻¹
  map_one' := by simp
  map_mul' a b := by push_cast; rw [mul_inv]

theorem harm_eq (x : ℕ) : ∑ m ∈ Finset.Icc 1 x, (m : ℝ)⁻¹ = (harmonic x : ℝ) := by
  induction x with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, harmonic_succ]
    push_cast
    ring

theorem euler_lower (x : ℕ) :
    Real.log ((x : ℝ) + 1) ≤
      (∏ p ∈ (Finset.range (x + 1)).filter Nat.Prime, (1 - (p : ℝ)⁻¹))⁻¹ := by
  have hp : ∀ {p : ℕ}, p.Prime → ‖invHom p‖ < 1 := by
    intro p hp
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    simp only [invHom, MonoidHom.coe_mk, OneHom.coe_mk, norm_inv, Real.norm_natCast]
    exact inv_lt_one_of_one_lt₀ (by linarith)
  obtain ⟨-, hsum⟩ :=
    EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric hp (x + 1)
  rw [← Finset.prod_inv_distrib]
  have hprod : ∏ p ∈ (x + 1).primesBelow, (1 - invHom p)⁻¹ =
      ∏ p ∈ (Finset.range (x + 1)).filter Nat.Prime, (1 - (p : ℝ)⁻¹)⁻¹ := rfl
  rw [hprod] at hsum
  let s : Finset (Nat.smoothNumbers (x + 1)) :=
    (Finset.Icc 1 x).subtype (fun m => m ∈ Nat.smoothNumbers (x + 1))
  have hle := sum_le_hasSum s (fun i _ => by
    simp only [invHom, MonoidHom.coe_mk, OneHom.coe_mk]; positivity) hsum
  have hs : ∑ i ∈ s, invHom i = ∑ m ∈ Finset.Icc 1 x, (m : ℝ)⁻¹ := by
    rw [Finset.sum_subtype_eq_sum_filter, Finset.filter_true_of_mem]
    · rfl
    · intro m hm
      obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hm
      rw [Nat.mem_smoothNumbers']
      intro p _ hpm
      have := Nat.le_of_dvd (by omega) hpm
      omega
  have hharm := harm_eq x
  have hlog := log_add_one_le_harmonic x
  push_cast at hlog
  linarith [hs ▸ hle, hharm]

/-- `∑_{n=2}^{x} 1 / (n (n - 1)) = 1 - 1 / x` for `x ≥ 1`. -/
theorem tele (x : ℕ) (hx : 1 ≤ x) :
    ∑ n ∈ Finset.Icc 2 x, (1 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) = 1 - 1 / (x : ℝ) := by
  induction x, hx using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hm0 : (m : ℝ) ≠ 0 := by linarith
    have hm1 : (m : ℝ) + 1 ≠ 0 := by linarith
    have hc : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
    rw [hc, show (m : ℝ) + 1 - 1 = m by ring]
    field_simp
    ring

theorem mertens_lower : ∃ C : ℝ, ∀ x : ℕ, 2 ≤ x →
    Real.log (Real.log x) - C ≤ ∑ p ∈ (range (x + 1)).filter Nat.Prime, (1 : ℝ) / p := by
  refine ⟨1, fun x hx => ?_⟩
  set S := (range (x + 1)).filter Nat.Prime with hS
  have hx2 : (2 : ℝ) ≤ x := by exact_mod_cast hx
  have hprime : ∀ p ∈ S, Nat.Prime p := fun p hp => (Finset.mem_filter.mp hp).2
  have hp2 : ∀ p ∈ S, (2 : ℝ) ≤ p := fun p hp => by exact_mod_cast (hprime p hp).two_le
  -- the Euler product bound
  have he := euler_lower x
  rw [← Finset.prod_inv_distrib] at he
  have hfac : ∀ p ∈ S, 0 < (1 - (p : ℝ)⁻¹)⁻¹ := fun p hp => by
    have := hp2 p hp
    have : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
    positivity
  have hlogx1 : 0 < Real.log ((x : ℝ) + 1) := Real.log_pos (by linarith)
  have hll : Real.log (Real.log ((x : ℝ) + 1)) ≤ ∑ p ∈ S, Real.log ((1 - (p : ℝ)⁻¹)⁻¹) := by
    rw [← Real.log_prod (fun p hp => (hfac p hp).ne')]
    exact Real.log_le_log hlogx1 he
  -- each term is at most 1/p + 1/(p (p - 1))
  have hterm : ∀ p ∈ S, Real.log ((1 - (p : ℝ)⁻¹)⁻¹) ≤
      (1 : ℝ) / p + 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
    intro p hp
    have h2 := hp2 p hp
    have hpos : 0 < (1 - (p : ℝ)⁻¹)⁻¹ := hfac p hp
    have hl := Real.log_le_sub_one_of_pos hpos
    have e : (1 - (p : ℝ)⁻¹)⁻¹ - 1 = (1 : ℝ) / p + 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
      have : (p : ℝ) - 1 ≠ 0 := by linarith
      have : (p : ℝ) ≠ 0 := by linarith
      field_simp
      ring
    linarith
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_add_distrib] at hsum
  -- the correction sum is at most 1
  have hsub : S ⊆ Finset.Icc 2 x := by
    intro p hp
    have := (Finset.mem_filter.mp hp).1
    rw [Finset.mem_range] at this
    exact Finset.mem_Icc.mpr ⟨(hprime p hp).two_le, by omega⟩
  have hcorr : ∑ p ∈ S, (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) ≤ 1 := by
    calc ∑ p ∈ S, (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))
        ≤ ∑ n ∈ Finset.Icc 2 x, (1 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hsub
          intro n hn _
          have : (2 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
          have : 0 < (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
          positivity
      _ = 1 - 1 / (x : ℝ) := tele x (by omega)
      _ ≤ 1 := by have : 0 < (x : ℝ) := by linarith
                  have : 0 < 1 / (x : ℝ) := by positivity
                  linarith
  -- monotonicity of log log
  have hmono : Real.log (Real.log x) ≤ Real.log (Real.log ((x : ℝ) + 1)) := by
    have hlx : 0 < Real.log (x : ℝ) := Real.log_pos (by linarith)
    exact Real.log_le_log hlx (Real.log_le_log (by linarith) (by linarith))
  linarith

end OMA.Step_Erdos950_erdos_950_variants_weaker_pi_R1_H2

theorem OMA.solution : OMA.R_Erdos950_erdos_950_variants_weaker_pi_R1.H2 :=
  OMA.Step_Erdos950_erdos_950_variants_weaker_pi_R1_H2.mertens_lower
