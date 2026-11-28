import OMAReductions.R_Erdos687_erdos_687_variants_iwaniec_R1_H1_R2
import Mathlib

/-! The Euler product over the primes up to `x` is the sum of `1 / m` over the `(x + 1)`-smooth
`m` (`EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric`), which
contains `1, ..., x`; so it is at least the harmonic number `H_x ≥ log (x + 1)`. -/

namespace OMA.Step_Erdos687_erdos_687_variants_iwaniec_R1_H1_R2_H2

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

end OMA.Step_Erdos687_erdos_687_variants_iwaniec_R1_H1_R2_H2

theorem OMA.solution : OMA.R_Erdos687_erdos_687_variants_iwaniec_R1_H1_R2.H2 :=
  OMA.Step_Erdos687_erdos_687_variants_iwaniec_R1_H1_R2_H2.euler_lower
