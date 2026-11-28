import OMAStatements.S_mo_189061
import Mathlib

/-!
An exact counterexample to Ludwig's constant-perturbation question.
Cherng-tiao Perng previously gave a numerical counterexample.
Source: https://mathoverflow.net/questions/189061
Credit: @zarnab222-dev
-/

open Polynomial OMA.S_mo_189061

namespace MO189061

noncomputable def q : Polynomial ℝ := C 2 * X ^ 2 + X + C 15

lemma evalQ (z : ℂ) : q.eval₂ Complex.ofRealHom z = 2 * z ^ 2 + z + 15 := by
  simp [q]

lemma nonzeroQ {z : ℂ} (hz : 0 < z.re) : 2 * z ^ 2 + z + 15 ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  have hr := congrArg Complex.re h
  norm_num [pow_two, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im] at hi hr
  have hy : z.im = 0 := by
    by_contra hn
    rcases lt_or_gt_of_ne hn with hy | hy
    · nlinarith [mul_neg_of_pos_of_neg hz hy]
    · nlinarith [mul_pos hz hy]
  rw [hy] at hr
  nlinarith [sq_nonneg z.re]

end MO189061

open MO189061

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_189061.main) := by
  intro claim
  let p := q ^ 4 - C ((15 : ℝ) ^ 4)
  have h0 : p.eval 0 = 0 := by simp [p, q]
  let w : ℂ := ⟨1, 3⟩
  have hw : 2 * w ^ 2 + w + 15 = 15 * Complex.I := by
    apply Complex.ext <;> norm_num [w, pow_two, Complex.mul_re, Complex.mul_im]
  have hp : hasRightRoot p := by
    refine ⟨w, by norm_num [w], ?_⟩
    simp only [p, eval₂_sub, eval₂_pow, evalQ, eval₂_C, map_pow, hw]
    rw [mul_pow]
    norm_num [show Complex.I ^ 4 = 1 by norm_num [show (4 : ℕ) = 2 * 2 by decide, pow_mul]]
  obtain ⟨z, hz, h⟩ := claim p h0 hp (15 ^ 4)
  simp only [p, sub_add_cancel, eval₂_pow, evalQ, pow_eq_zero_iff (by decide : 4 ≠ 0)] at h
  exact nonzeroQ hz h
