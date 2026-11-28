import OMAReductions.R_RegularPrimes_isRegularPrime_iff_Bernoulli_R3_H2_R1_H2_R1
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.FieldTheory.Finite.Basic

namespace OMA.RPVander

theorem sq_inj (p : ℕ) [Fact p.Prime] (c d : ℕ) (h1 : c + d < p) (h2 : 0 < c + d)
    (h : (c : ZMod p) ^ 2 = (d : ZMod p) ^ 2) : c = d := by
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with h | h
  · rw [ZMod.natCast_eq_natCast_iff'] at h
    rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h
  · have h0 : ((c + d : ℕ) : ZMod p) = 0 := by push_cast; rw [h]; ring
    rw [ZMod.natCast_eq_zero_iff] at h0
    have := Nat.le_of_dvd h2 h0
    omega

theorem target : ∀ (p : ℕ) [Fact p.Prime], 3 ≤ p →
    (Matrix.det (fun j a : Fin ((p - 3) / 2) =>
      ((a.val + 2 : ℕ) : ZMod p) ^ (2 * (j.val + 1)) - 1)) ≠ 0 := by
  intro p _ hp3 hdet
  set m := (p - 3) / 2 with hm
  obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  let x : Fin m → ZMod p := fun a => ((a.val + 2 : ℕ) : ZMod p) ^ 2
  let w : Fin (m + 1) → ZMod p := Fin.cons 1 x
  let c' : Fin (m + 1) → ZMod p := Fin.cons (-∑ a, c a) c
  have hw : Function.Injective w := by
    refine Fin.cons_injective_iff.mpr ⟨?_, ?_⟩
    · rintro ⟨a, ha⟩
      have h1 : ((a.val + 2 : ℕ) : ZMod p) ^ 2 = ((1 : ℕ) : ZMod p) ^ 2 := by
        simpa [x] using ha
      have := sq_inj p _ _ (by have := a.isLt; omega) (by omega) h1
      omega
    · intro a b hab
      have := sq_inj p _ _ (by have := a.isLt; have := b.isLt; omega) (by omega) hab
      exact Fin.ext (by omega)
  have hsum : ∀ i : Fin (m + 1), (∑ k : Fin (m + 1), c' k * w k ^ (i : ℕ)) = 0 := by
    intro i
    rw [Fin.sum_univ_succ]
    simp only [c', w, Fin.cons_zero, Fin.cons_succ, one_pow, mul_one]
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · have hj := congr_fun hc j
      simp only [Matrix.mulVec, dotProduct, Pi.zero_apply, sub_mul, Finset.sum_sub_distrib,
        one_mul, pow_mul] at hj
      simp only [Fin.val_succ, x]
      rw [← hj]
      simp only [mul_comm (c _)]
      ring
  have h0 := Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hw hsum
  apply hc0
  funext a
  have := congr_fun h0 a.succ
  simpa [c'] using this

end OMA.RPVander

theorem OMA.solution : OMA.R_RegularPrimes_isRegularPrime_iff_Bernoulli_R3_H2_R1_H2_R1.H2 :=
  OMA.RPVander.target
