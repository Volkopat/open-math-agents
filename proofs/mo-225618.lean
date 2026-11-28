import OMAStatements.S_mo_225618
import Mathlib.Tactic
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Disproof of `mo-225618`

We refute the affirmative uniform approximate-stationarity assertion using a multiscale
involution counterexample on the finite state space `State K = Σ j : Fin K, Fin 3 × Fin (2 ^ j.val)`
for `K ≥ 5`, with probability distribution `dist K ⟨j, _⟩ = 1 / (3 * K * 2 ^ j.val)` and a
uniform mixture of three involutions `perm K t` (`t : Fin 3`). Each involution doubles `dist K`
on its matched color for `j > 0` and halves `dist K` on the two unmatched colors for `j + 1 < K`,
causing exact cancellation of `dist K - mix (weights K) (dist K)` on all interior scales
`0 < j < K - 1` so that `tv (dist K) (mix (weights K) (dist K)) = 1 / (3 * K) ≤ δ`, whereas
each individual involution satisfies `tv (dist K) (push (perm K t) (dist K)) ≥ 1 / 3 - 2 / (3 * K) > 1 / 6`.
-/

namespace MO225618Disproof

open OMA.S_mo_225618

private abbrev State (K : ℕ) : Type :=
  Σ j : Fin K, Fin 3 × Fin (2 ^ j.val)

private lemma state_ext {K : ℕ} {x y : State K}
    (h1 : x.1 = y.1) (h2 : x.2.1 = y.2.1) (h3 : x.2.2.val = y.2.2.val) : x = y := by
  rcases x with ⟨j1, c1, m1⟩
  rcases y with ⟨j2, c2, m2⟩
  dsimp at h1 h2 h3
  subst h1
  subst h2
  have hm : m1 = m2 := Fin.ext h3
  subst hm
  rfl

private noncomputable def dist (K : ℕ) (x : State K) : ℝ :=
  1 / (3 * (K : ℝ) * (2 : ℝ) ^ x.1.val)

private lemma dist_nonneg (K : ℕ) (x : State K) : 0 ≤ dist K x := by
  unfold dist
  positivity

private lemma sum_dist_fiber (K : ℕ) (j : Fin K) (c : Fin 3) :
    ∑ m : Fin (2 ^ j.val), dist K ⟨j, (c, m)⟩ = 1 / (3 * (K : ℝ)) := by
  have hK : (K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := j.isLt; omega)
  have h2 : (2 : ℝ) ^ j.val ≠ 0 := by positivity
  simp only [dist, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_pow, Nat.cast_ofNat]
  field_simp

private lemma sum_dist_layer (K : ℕ) (j : Fin K) :
    ∑ cm : Fin 3 × Fin (2 ^ j.val), dist K ⟨j, cm⟩ = 1 / (K : ℝ) := by
  rw [Fintype.sum_prod_type]
  simp only [sum_dist_fiber, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_ofNat]
  have hK : (K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := j.isLt; omega)
  field_simp

private lemma isProb_dist {K : ℕ} (hK : 0 < K) : IsProb (dist K) := by
  refine ⟨dist_nonneg K, ?_⟩
  rw [Fintype.sum_sigma]
  simp only [sum_dist_layer, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hK0 : (K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp

private lemma fin3_add_one_ne (t : Fin 3) : t + 1 ≠ t := by
  fin_cases t <;> decide

private lemma fin3_add_two_ne (t : Fin 3) : t + 2 ≠ t := by
  fin_cases t <;> decide

private lemma fin3_add_two_ne_add_one (t : Fin 3) : t + 2 ≠ t + 1 := by
  fin_cases t <;> decide

private lemma fin3_eq_add_two {c t : Fin 3} (h0 : c ≠ t) (h1 : c ≠ t + 1) : c = t + 2 := by
  fin_cases c <;> fin_cases t <;> simp_all

private lemma sum_fin3_shift (c : Fin 3) (g : Fin 3 → ℝ) :
    ∑ t : Fin 3, g t = g c + g (c + 1) + g (c + 2) := by
  rw [Fin.sum_univ_three]
  fin_cases c <;> dsimp <;> ring

private def step (K : ℕ) (t : Fin 3) (x : State K) : State K :=
  if x.2.1 = t then
    if hj : 0 < x.1.val then
      ⟨⟨x.1.val - 1, by have := x.1.isLt; omega⟩,
       (t + if x.2.2.val % 2 = 0 then 1 else 2,
        ⟨x.2.2.val / 2, by
          have hpow : 2 ^ x.1.val = 2 * 2 ^ (x.1.val - 1) := by
            conv_lhs => rw [← Nat.sub_add_cancel hj, pow_succ']
          have hm := x.2.2.isLt
          dsimp
          omega⟩)⟩
    else
      x
  else
    if hj : x.1.val + 1 < K then
      ⟨⟨x.1.val + 1, hj⟩,
       (t,
        ⟨2 * x.2.2.val + if x.2.1 = t + 1 then 0 else 1, by
          have hpow : 2 ^ (x.1.val + 1) = 2 * 2 ^ x.1.val := pow_succ' 2 x.1.val
          have hm := x.2.2.isLt
          dsimp
          split_ifs <;> omega⟩)⟩
    else
      x

private lemma step_involutive (K : ℕ) (t : Fin 3) : Function.Involutive (step K t) := by
  intro x
  rcases x with ⟨j, c, m⟩
  by_cases hct : c = t
  · by_cases hj : 0 < j.val
    · have hstep : step K t ⟨j, (c, m)⟩ =
          ⟨⟨j.val - 1, by have := j.isLt; omega⟩,
           (t + if m.val % 2 = 0 then 1 else 2,
            ⟨m.val / 2, by
              have hpow : 2 ^ j.val = 2 * 2 ^ (j.val - 1) := by
                conv_lhs => rw [← Nat.sub_add_cancel hj, pow_succ']
              have hm := m.isLt
              dsimp
              omega⟩)⟩ := by
        simp [step, hct, hj]
      rw [hstep]
      by_cases hm2 : m.val % 2 = 0
      · have hne : t + 1 ≠ t := fin3_add_one_ne t
        have hlt : j.val - 1 + 1 < K := by have := j.isLt; omega
        simp only [step, hm2, hne, hlt, ↓reduceIte, ↓reduceDIte]
        exact state_ext (Fin.ext (by dsimp; omega)) hct.symm (by dsimp; omega)
      · have hne : t + 2 ≠ t := fin3_add_two_ne t
        have hne1 : t + 2 ≠ t + 1 := fin3_add_two_ne_add_one t
        have hlt : j.val - 1 + 1 < K := by have := j.isLt; omega
        simp only [step, hm2, hne, hne1, hlt, ↓reduceIte, ↓reduceDIte]
        exact state_ext (Fin.ext (by dsimp; omega)) hct.symm (by dsimp; omega)
    · have hstep : step K t ⟨j, (c, m)⟩ = ⟨j, (c, m)⟩ := by simp [step, hct, hj]
      rw [hstep, hstep]
  · by_cases hj : j.val + 1 < K
    · have hstep : step K t ⟨j, (c, m)⟩ =
          ⟨⟨j.val + 1, hj⟩,
           (t,
            ⟨2 * m.val + if c = t + 1 then 0 else 1, by
              have hpow : 2 ^ (j.val + 1) = 2 * 2 ^ j.val := pow_succ' 2 j.val
              have hm := m.isLt
              dsimp
              split_ifs <;> omega⟩)⟩ := by
        simp [step, hct, hj]
      rw [hstep]
      have hpos : 0 < j.val + 1 := Nat.succ_pos _
      by_cases h1 : c = t + 1
      · have hmod : (2 * m.val + 0) % 2 = 0 := by omega
        simp only [step, hpos, h1, hmod, ↓reduceIte, ↓reduceDIte]
        exact state_ext (Fin.ext rfl) rfl (by dsimp; omega)
      · have hc2 : c = t + 2 := fin3_eq_add_two hct h1
        have hmod : (2 * m.val + 1) % 2 ≠ 0 := by omega
        simp only [step, hpos, h1, hmod, ↓reduceIte, ↓reduceDIte]
        exact state_ext (Fin.ext rfl) hc2.symm (by dsimp; omega)
    · have hstep : step K t ⟨j, (c, m)⟩ = ⟨j, (c, m)⟩ := by simp [step, hct, hj]
      rw [hstep, hstep]

private def perm (K : ℕ) (t : Fin 3) : Equiv.Perm (State K) :=
  (step_involutive K t).toPerm (step K t)

private lemma push_perm (K : ℕ) (t : Fin 3) (x : State K) :
    push (perm K t) (dist K) x = dist K (step K t x) := rfl

private lemma dist_step_eq_mul_two {K : ℕ} {t : Fin 3} {x : State K}
    (hc : x.2.1 = t) (hj : 0 < x.1.val) :
    dist K (step K t x) = 2 * dist K x := by
  have h1 : (step K t x).1.val = x.1.val - 1 := by simp [step, hc, hj]
  have hK : (K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := x.1.isLt; omega)
  have hpow : (2 : ℝ) ^ x.1.val = 2 * (2 : ℝ) ^ (x.1.val - 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel hj, pow_succ']
  have h2 : (2 : ℝ) ^ (x.1.val - 1) ≠ 0 := by positivity
  unfold dist
  rw [h1, hpow]
  field_simp

private lemma dist_step_eq_self_of_eq {K : ℕ} {t : Fin 3} {x : State K}
    (hc : x.2.1 = t) (hj : x.1.val = 0) :
    dist K (step K t x) = dist K x := by
  have hnot : ¬ 0 < x.1.val := by omega
  simp [step, hc, hnot]

private lemma dist_step_eq_div_two {K : ℕ} {t : Fin 3} {x : State K}
    (hc : x.2.1 ≠ t) (hj : x.1.val + 1 < K) :
    dist K (step K t x) = dist K x / 2 := by
  have h1 : (step K t x).1.val = x.1.val + 1 := by simp [step, hc, hj]
  have hK : (K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := x.1.isLt; omega)
  have h2 : (2 : ℝ) ^ x.1.val ≠ 0 := by positivity
  unfold dist
  rw [h1, pow_succ']
  field_simp

private lemma dist_step_eq_self_of_ne {K : ℕ} {t : Fin 3} {x : State K}
    (hc : x.2.1 ≠ t) (hj : ¬ x.1.val + 1 < K) :
    dist K (step K t x) = dist K x := by
  simp [step, hc, hj]

private noncomputable def weights (K : ℕ) (p : Equiv.Perm (State K)) : ℝ :=
  ∑ t : Fin 3, if p = perm K t then (1 / 3 : ℝ) else 0

private lemma sum_weights_mul (K : ℕ) (g : Equiv.Perm (State K) → ℝ) :
    ∑ p : Equiv.Perm (State K), weights K p * g p = (1 / 3 : ℝ) * ∑ t : Fin 3, g (perm K t) := by
  simp only [weights, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, ← Finset.mul_sum]

private lemma isProb_weights (K : ℕ) : IsProb (weights K) := by
  refine ⟨fun p => Finset.sum_nonneg fun t _ => ?_, ?_⟩
  · split_ifs <;> norm_num
  · have h := sum_weights_mul K (fun _ => (1 : ℝ))
    simp only [mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_ofNat] at h
    linarith

private lemma mix_eq (K : ℕ) (x : State K) :
    mix (weights K) (dist K) x = (1 / 3 : ℝ) * ∑ t : Fin 3, dist K (step K t x) := by
  unfold mix
  rw [sum_weights_mul]
  simp only [push_perm]

private lemma abs_sub_mix_interior {K : ℕ} {x : State K}
    (hlo : 0 < x.1.val) (hhi : x.1.val + 1 < K) :
    |dist K x - mix (weights K) (dist K) x| = 0 := by
  rw [mix_eq, sum_fin3_shift x.2.1,
    dist_step_eq_mul_two rfl hlo,
    dist_step_eq_div_two (fin3_add_one_ne x.2.1).symm hhi,
    dist_step_eq_div_two (fin3_add_two_ne x.2.1).symm hhi]
  have hval : dist K x - 1 / 3 * (2 * dist K x + dist K x / 2 + dist K x / 2) = 0 := by ring
  rw [hval, abs_zero]

private lemma abs_sub_mix_bot {K : ℕ} (hK : 2 ≤ K) {x : State K} (h0 : x.1.val = 0) :
    |dist K x - mix (weights K) (dist K) x| = (1 / 3 : ℝ) * dist K x := by
  have hhi : x.1.val + 1 < K := by omega
  rw [mix_eq, sum_fin3_shift x.2.1,
    dist_step_eq_self_of_eq rfl h0,
    dist_step_eq_div_two (fin3_add_one_ne x.2.1).symm hhi,
    dist_step_eq_div_two (fin3_add_two_ne x.2.1).symm hhi]
  have hval : dist K x - 1 / 3 * (dist K x + dist K x / 2 + dist K x / 2) =
      (1 / 3 : ℝ) * dist K x := by ring
  rw [hval, abs_of_nonneg (mul_nonneg (by norm_num) (dist_nonneg K x))]

private lemma abs_sub_mix_top {K : ℕ} (hK : 2 ≤ K) {x : State K} (htop : x.1.val + 1 = K) :
    |dist K x - mix (weights K) (dist K) x| = (1 / 3 : ℝ) * dist K x := by
  have hlo : 0 < x.1.val := by omega
  have hnot : ¬ x.1.val + 1 < K := by omega
  rw [mix_eq, sum_fin3_shift x.2.1,
    dist_step_eq_mul_two rfl hlo,
    dist_step_eq_self_of_ne (fin3_add_one_ne x.2.1).symm hnot,
    dist_step_eq_self_of_ne (fin3_add_two_ne x.2.1).symm hnot]
  have hval : dist K x - 1 / 3 * (2 * dist K x + dist K x + dist K x) =
      -((1 / 3 : ℝ) * dist K x) := by ring
  rw [hval, abs_neg, abs_of_nonneg (mul_nonneg (by norm_num) (dist_nonneg K x))]

private lemma tv_mix {K : ℕ} (hK : 2 ≤ K) :
    tv (dist K) (mix (weights K) (dist K)) = 1 / (3 * (K : ℝ)) := by
  unfold tv
  rw [Fintype.sum_sigma]
  let j0 : Fin K := ⟨0, by omega⟩
  let jlast : Fin K := ⟨K - 1, by omega⟩
  have hj_ne : j0 ≠ jlast := by
    intro h
    have := congrArg Fin.val h
    dsimp [j0, jlast] at this
    omega
  have hlayer : ∀ j : Fin K,
      ∑ cm : Fin 3 × Fin (2 ^ j.val), |dist K ⟨j, cm⟩ - mix (weights K) (dist K) ⟨j, cm⟩| =
        (if j = j0 then (1 / (3 * (K : ℝ))) else 0) +
        (if j = jlast then (1 / (3 * (K : ℝ))) else 0) := by
    intro j
    by_cases h0 : j = j0
    · subst h0
      simp only [↓reduceIte, hj_ne, add_zero]
      have hsum : ∀ cm : Fin 3 × Fin (2 ^ j0.val),
          |dist K ⟨j0, cm⟩ - mix (weights K) (dist K) ⟨j0, cm⟩| =
            (1 / 3 : ℝ) * dist K ⟨j0, cm⟩ :=
        fun cm => abs_sub_mix_bot hK rfl
      simp_rw [hsum, ← Finset.mul_sum, sum_dist_layer, one_div_mul_one_div]
    · by_cases hlast : j = jlast
      · subst hlast
        simp only [↓reduceIte, hj_ne.symm, zero_add]
        have hsum : ∀ cm : Fin 3 × Fin (2 ^ jlast.val),
            |dist K ⟨jlast, cm⟩ - mix (weights K) (dist K) ⟨jlast, cm⟩| =
              (1 / 3 : ℝ) * dist K ⟨jlast, cm⟩ :=
          fun cm => abs_sub_mix_top hK (by dsimp [jlast]; omega)
        simp_rw [hsum, ← Finset.mul_sum, sum_dist_layer, one_div_mul_one_div]
      · simp only [h0, hlast, ↓reduceIte, add_zero]
        have hlo : 0 < j.val := by
          by_contra h
          apply h0
          exact Fin.ext (by dsimp [j0]; omega)
        have hhi : j.val + 1 < K := by
          by_contra h
          apply hlast
          have := j.isLt
          exact Fin.ext (by dsimp [jlast]; omega)
        exact Finset.sum_eq_zero fun cm _ => abs_sub_mix_interior hlo hhi
  simp_rw [hlayer]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  ring

private lemma sum_abs_step_interior {K : ℕ} (t : Fin 3) {j : Fin K}
    (hlo : 0 < j.val) (hhi : j.val + 1 < K) :
    ∑ cm : Fin 3 × Fin (2 ^ j.val), |dist K ⟨j, cm⟩ - dist K (step K t ⟨j, cm⟩)| =
      2 / (3 * (K : ℝ)) := by
  rw [Fintype.sum_prod_type, sum_fin3_shift t]
  have h0 : ∑ m : Fin (2 ^ j.val), |dist K ⟨j, (t, m)⟩ - dist K (step K t ⟨j, (t, m)⟩)| =
      1 / (3 * (K : ℝ)) := by
    have hterm : ∀ m : Fin (2 ^ j.val),
        |dist K ⟨j, (t, m)⟩ - dist K (step K t ⟨j, (t, m)⟩)| = dist K ⟨j, (t, m)⟩ := by
      intro m
      rw [dist_step_eq_mul_two (x := ⟨j, (t, m)⟩) rfl hlo]
      have : dist K ⟨j, (t, m)⟩ - 2 * dist K ⟨j, (t, m)⟩ = -dist K ⟨j, (t, m)⟩ := by ring
      rw [this, abs_neg, abs_of_nonneg (dist_nonneg K _)]
    simp_rw [hterm]
    exact sum_dist_fiber K j t
  have h1 : ∑ m : Fin (2 ^ j.val),
      |dist K ⟨j, (t + 1, m)⟩ - dist K (step K t ⟨j, (t + 1, m)⟩)| =
      (1 / 2 : ℝ) * (1 / (3 * (K : ℝ))) := by
    have hterm : ∀ m : Fin (2 ^ j.val),
        |dist K ⟨j, (t + 1, m)⟩ - dist K (step K t ⟨j, (t + 1, m)⟩)| =
          (1 / 2 : ℝ) * dist K ⟨j, (t + 1, m)⟩ := by
      intro m
      rw [dist_step_eq_div_two (fin3_add_one_ne t) hhi]
      have : dist K ⟨j, (t + 1, m)⟩ - dist K ⟨j, (t + 1, m)⟩ / 2 =
          (1 / 2 : ℝ) * dist K ⟨j, (t + 1, m)⟩ := by ring
      rw [this, abs_of_nonneg (mul_nonneg (by norm_num) (dist_nonneg K _))]
    simp_rw [hterm, ← Finset.mul_sum, sum_dist_fiber]
  have h2 : ∑ m : Fin (2 ^ j.val),
      |dist K ⟨j, (t + 2, m)⟩ - dist K (step K t ⟨j, (t + 2, m)⟩)| =
      (1 / 2 : ℝ) * (1 / (3 * (K : ℝ))) := by
    have hterm : ∀ m : Fin (2 ^ j.val),
        |dist K ⟨j, (t + 2, m)⟩ - dist K (step K t ⟨j, (t + 2, m)⟩)| =
          (1 / 2 : ℝ) * dist K ⟨j, (t + 2, m)⟩ := by
      intro m
      rw [dist_step_eq_div_two (fin3_add_two_ne t) hhi]
      have : dist K ⟨j, (t + 2, m)⟩ - dist K ⟨j, (t + 2, m)⟩ / 2 =
          (1 / 2 : ℝ) * dist K ⟨j, (t + 2, m)⟩ := by ring
      rw [this, abs_of_nonneg (mul_nonneg (by norm_num) (dist_nonneg K _))]
    simp_rw [hterm, ← Finset.mul_sum, sum_dist_fiber]
  rw [h0, h1, h2]
  ring

private lemma tv_push_ge {K : ℕ} (hK : 2 ≤ K) (t : Fin 3) :
    1 / 3 - 2 / (3 * (K : ℝ)) ≤ tv (dist K) (push (perm K t) (dist K)) := by
  unfold tv
  simp only [push_perm]
  rw [Fintype.sum_sigma]
  let j0 : Fin K := ⟨0, by omega⟩
  let jlast : Fin K := ⟨K - 1, by omega⟩
  have hj_ne : j0 ≠ jlast := by
    intro h
    have := congrArg Fin.val h
    dsimp [j0, jlast] at this
    omega
  have hle : ∑ j : Fin K,
      ((2 / (3 * (K : ℝ))) -
        (if j = j0 then (2 / (3 * (K : ℝ))) else 0) -
        (if j = jlast then (2 / (3 * (K : ℝ))) else 0)) ≤
      ∑ j : Fin K, ∑ cm : Fin 3 × Fin (2 ^ j.val),
        |dist K ⟨j, cm⟩ - dist K (step K t ⟨j, cm⟩)| := by
    refine Finset.sum_le_sum fun j _ => ?_
    by_cases h0 : j = j0
    · subst h0
      simp only [↓reduceIte, hj_ne, sub_self]
      exact Finset.sum_nonneg fun cm _ => abs_nonneg _
    · by_cases hlast : j = jlast
      · subst hlast
        simp only [↓reduceIte, hj_ne.symm, sub_zero, sub_self]
        exact Finset.sum_nonneg fun cm _ => abs_nonneg _
      · simp only [h0, hlast, ↓reduceIte, sub_zero]
        have hlo : 0 < j.val := by
          by_contra h
          apply h0
          exact Fin.ext (by dsimp [j0]; omega)
        have hhi : j.val + 1 < K := by
          by_contra h
          apply hlast
          have := j.isLt
          exact Fin.ext (by dsimp [jlast]; omega)
        rw [sum_abs_step_interior t hlo hhi]
  have hsum : ∑ j : Fin K,
      ((2 / (3 * (K : ℝ))) -
        (if j = j0 then (2 / (3 * (K : ℝ))) else 0) -
        (if j = jlast then (2 / (3 * (K : ℝ))) else 0)) =
      2 / 3 - 4 / (3 * (K : ℝ)) := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    have hK0 : (K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    field_simp
    ring
  have hhalf : 1 / 3 - 2 / (3 * (K : ℝ)) = (2 / 3 - 4 / (3 * (K : ℝ))) / 2 := by ring
  linarith

end MO225618Disproof

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_225618.main) := by
  intro hmain
  obtain ⟨δ, hδ, hbound⟩ := hmain (1 / 6 : ℝ) (by norm_num)
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / (3 * δ))
  let K : ℕ := n + 5
  have hK5 : 5 ≤ K := by omega
  have hK2 : 2 ≤ K := by omega
  have hK0 : 0 < K := by omega
  have hKpos : (0 : ℝ) < (K : ℝ) := Nat.cast_pos.mpr hK0
  have htv_le : OMA.S_mo_225618.tv (MO225618Disproof.dist K)
      (OMA.S_mo_225618.mix (MO225618Disproof.weights K) (MO225618Disproof.dist K)) ≤ δ := by
    rw [MO225618Disproof.tv_mix hK2]
    have hK_gt : 1 / (3 * δ) < (K : ℝ) := by
      have hle : (n : ℝ) ≤ (K : ℝ) := by exact_mod_cast (by omega : n ≤ K)
      linarith
    have h1 : 1 < 3 * (K : ℝ) * δ := by
      have h3δ : 0 < 3 * δ := by linarith
      have := (div_lt_iff₀ h3δ).mp hK_gt
      linarith
    have h3K : 0 < 3 * (K : ℝ) := by positivity
    exact le_of_lt ((div_lt_iff₀ h3K).mpr (by linarith))
  have hle_eta := hbound (MO225618Disproof.State K)
    (MO225618Disproof.weights K) (MO225618Disproof.dist K)
    (MO225618Disproof.isProb_weights K) (MO225618Disproof.isProb_dist hK0) htv_le
  have hexp_ge : 1 / 3 - 2 / (3 * (K : ℝ)) ≤
      ∑ p : Equiv.Perm (MO225618Disproof.State K),
        MO225618Disproof.weights K p *
          OMA.S_mo_225618.tv (MO225618Disproof.dist K)
            (OMA.S_mo_225618.push p (MO225618Disproof.dist K)) := by
    rw [MO225618Disproof.sum_weights_mul]
    have hsum_ge : ∑ _t : Fin 3, (1 / 3 - 2 / (3 * (K : ℝ))) ≤
        ∑ t : Fin 3, OMA.S_mo_225618.tv (MO225618Disproof.dist K)
          (OMA.S_mo_225618.push (MO225618Disproof.perm K t) (MO225618Disproof.dist K)) :=
      Finset.sum_le_sum fun t _ => MO225618Disproof.tv_push_ge hK2 t
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_ofNat] at hsum_ge
    linarith
  have hgt_eta : (1 / 6 : ℝ) < 1 / 3 - 2 / (3 * (K : ℝ)) := by
    have hK5_real : (5 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK5
    have h3K : 0 < 3 * (K : ℝ) := by positivity
    have h2div : 2 / (3 * (K : ℝ)) < 1 / 6 := by
      rw [div_lt_div_iff₀ h3K (by norm_num)]
      linarith
    linarith
  linarith
