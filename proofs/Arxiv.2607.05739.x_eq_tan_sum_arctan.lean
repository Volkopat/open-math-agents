import FormalConjectures.Arxiv.«2607.05739».TanArctanSum

open Real
/-! The tangent of a sum of arctangents via the coordinates of a Gaussian integer product. -/

open Arxiv.«2607.05739» Finset

namespace OMA

-- The cosine and sine are the two integer coordinates times the same positive factor.
lemma scaled_coordinates (n : ℕ) :
    ∃ c : ℝ, 0 < c ∧
      cos (∑ k ∈ Icc 1 n, arctan k) = c * (A n : ℝ) ∧
      sin (∑ k ∈ Icc 1 n, arctan k) = c * (B n : ℝ) := by
  induction n with
  | zero =>
    exact ⟨1, zero_lt_one, by norm_num [A, gaussProd], by norm_num [B, gaussProd]⟩
  | succ n ih =>
    obtain ⟨c, hc, hcos, hsin⟩ := ih
    let t : ℝ := (n + 1 : ℕ)
    have ht := cos_arctan_pos t
    have hs : sin (arctan t) = t * cos (arctan t) := by
      apply (div_eq_iff ht.ne').mp
      rw [← tan_eq_sin_div_cos, tan_arctan]
    have hp : gaussProd (n + 1) = gaussProd n * (⟨1, (n + 1 : ℕ)⟩ : GaussianInt) := by
      unfold gaussProd
      rw [prod_Icc_succ_top (by omega)]
    refine ⟨c * cos (arctan t), mul_pos hc ht, ?_, ?_⟩
    · rw [sum_Icc_succ_top (by omega), cos_add, hcos, hsin]
      change _ - _ * sin (arctan t) = _
      rw [hs]
      simp [A, B, hp, t]
      ring
    · rw [sum_Icc_succ_top (by omega), sin_add, hcos, hsin]
      change _ + _ * sin (arctan t) = _
      rw [hs]
      simp [A, B, hp, t]
      ring

end OMA

theorem OMA.solution : type_of% @Arxiv.«2607.05739».x_eq_tan_sum_arctan := by
  intro n _
  obtain ⟨c, hc, hcos, hsin⟩ := OMA.scaled_coordinates n
  rw [tan_eq_sin_div_cos, hsin, hcos, x]
  push_cast
  rw [mul_div_mul_left _ _ hc.ne']
