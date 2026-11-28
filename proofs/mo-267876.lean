import OMAStatements.S_mo_267876
import Mathlib

/-!
Proof of MathOverflow 267876:
For centered vectors `f, g : Fin n → ℝ` with `0 ≤ ∑ i, f i * g i`,
`∑ i, (f i - g i) ^ 2 ≤ ∑_{i < j} (|f i - f j| - |g i - g j|) ^ 2`.

Setting `p = f + g` and `q = f - g`, the inequality reduces to
`∑ i, q i ^ 2 ≤ ∑_{i < j} min ((p i - p j) ^ 2) ((q i - q j) ^ 2)`
under `∑ p = ∑ q = 0` and `∑ q ^ 2 ≤ ∑ p ^ 2`.
Partitioning edges of `K_n` into `G` (`(p_i - p_j)^2 ≤ (q_i - q_j)^2`) and `Gᶜ`,
this follows from `μ₂(G) + μ₂(Gᶜ) ≥ 1` (Einollahzadeh and Karkhaneei, arXiv:1901.02047).
The finite cases `n ≤ 11` are verified algebraically via block-mean variance decomposition
and exact rational Schur complements, avoiding floating-point eigenvalue computations.
-/

namespace OMA.MO267876

open Finset

section BasicPairs

def pairs (n : ℕ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun e : Fin n × Fin n => e.1 < e.2)

lemma two_mul_sum_pairs {n : ℕ} (F : Fin n → Fin n → ℝ)
    (hsym : ∀ i j, F i j = F j i) (hdiag : ∀ i, F i i = 0) :
    2 * ∑ e ∈ pairs n, F e.1 e.2 = ∑ i : Fin n, ∑ j : Fin n, F i j := by
  have h1 : ∑ i : Fin n, ∑ j : Fin n, F i j =
      ∑ e : Fin n × Fin n, F e.1 e.2 :=
    (Fintype.sum_prod_type (fun e : Fin n × Fin n => F e.1 e.2)).symm
  rw [h1]
  have hsplit := Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset (Fin n × Fin n)))
    (p := fun e => e.1 < e.2) (f := fun e => F e.1 e.2)
  have hrest : ∑ e ∈ Finset.univ.filter (fun e : Fin n × Fin n => ¬ e.1 < e.2), F e.1 e.2 =
      ∑ e ∈ Finset.univ.filter (fun e : Fin n × Fin n => e.2 < e.1), F e.1 e.2 := by
    have hsub := Finset.sum_filter_add_sum_filter_not
      (s := Finset.univ.filter (fun e : Fin n × Fin n => ¬ e.1 < e.2))
      (p := fun e => e.2 < e.1) (f := fun e => F e.1 e.2)
    have hzero : ∑ e ∈ (Finset.univ.filter (fun e : Fin n × Fin n => ¬ e.1 < e.2)).filter
        (fun e => ¬ e.2 < e.1), F e.1 e.2 = 0 := by
      apply Finset.sum_eq_zero
      intro e he
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
      have heq : e.1 = e.2 := le_antisymm (not_lt.mp he.2) (not_lt.mp he.1)
      rw [heq, hdiag]
    have hfilt : (Finset.univ.filter (fun e : Fin n × Fin n => ¬ e.1 < e.2)).filter
        (fun e => e.2 < e.1) = Finset.univ.filter (fun e : Fin n × Fin n => e.2 < e.1) := by
      ext e
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_iff_right_iff_imp]
      intro hlt
      exact not_lt.mpr hlt.le
    rw [hfilt, hzero, add_zero] at hsub
    exact hsub.symm
  have hswap : ∑ e ∈ Finset.univ.filter (fun e : Fin n × Fin n => e.2 < e.1), F e.1 e.2 =
      ∑ e ∈ pairs n, F e.1 e.2 := by
    refine Finset.sum_nbij Prod.swap ?_ ?_ ?_ ?_
    · intro e he
      simp only [pairs, Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
      exact he
    · intro a _ b _ hab
      exact Prod.swap_injective hab
    · intro e he
      refine ⟨e.swap, ?_, Prod.swap_swap e⟩
      simp only [Finset.mem_coe, pairs, Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
      exact he
    · intro e _
      exact hsym e.1 e.2
  rw [← hsplit, hrest, hswap]
  change 2 * ∑ e ∈ pairs n, F e.1 e.2 = (∑ e ∈ pairs n, F e.1 e.2) + ∑ e ∈ pairs n, F e.1 e.2
  ring

def quad {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : Fin n → ℝ) : ℝ :=
  ∑ e ∈ (pairs n).filter (fun e => G.Adj e.1 e.2), (x e.1 - x e.2) ^ 2

lemma two_mul_quad {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : Fin n → ℝ) :
    2 * quad G x = ∑ i : Fin n, ∑ j : Fin n, if G.Adj i j then (x i - x j) ^ 2 else 0 := by
  have hq : quad G x = ∑ e ∈ pairs n, if G.Adj e.1 e.2 then (x e.1 - x e.2) ^ 2 else 0 := by
    unfold quad
    rw [Finset.sum_filter]
  rw [hq]
  exact two_mul_sum_pairs (fun i j => if G.Adj i j then (x i - x j) ^ 2 else 0)
    (fun i j => by
      by_cases h : G.Adj i j
      · rw [if_pos h, if_pos h.symm]; ring
      · rw [if_neg h, if_neg (fun h' => h h'.symm)])
    (fun i => by rw [if_neg (G.loopless.irrefl i)])

lemma quad_nonneg {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : Fin n → ℝ) :
    0 ≤ quad G x :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

lemma quad_shift {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : Fin n → ℝ) (c : ℝ) :
    quad G (fun i => x i - c) = quad G x := by
  unfold quad
  exact Finset.sum_congr rfl (fun _ _ => by ring)

lemma quad_smul {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : Fin n → ℝ) (c : ℝ) :
    quad G (fun i => c * x i) = c ^ 2 * quad G x := by
  unfold quad
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

lemma sum_pairs_sq_eq {n : ℕ} (x : Fin n → ℝ) (hx : ∑ i, x i = 0) :
    ∑ e ∈ pairs n, (x e.1 - x e.2) ^ 2 = (n : ℝ) * ∑ i, x i ^ 2 := by
  have h2 := two_mul_sum_pairs (fun i j : Fin n => (x i - x j) ^ 2)
    (fun _ _ => by ring) (fun _ => by ring)
  have hstep : ∀ i : Fin n, ∑ j : Fin n, (x i - x j) ^ 2 =
      (n : ℝ) * x i ^ 2 + (∑ j, x j ^ 2) := by
    intro i
    have hpt : ∀ j : Fin n, (x i - x j) ^ 2 = x i ^ 2 + x j ^ 2 - 2 * x i * x j := fun _ => by ring
    simp_rw [hpt, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, hx, mul_zero, sub_zero]
  simp_rw [hstep, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h2
  linarith

lemma pair_sq_prod_bound {n : ℕ} (x y : Fin n → ℝ) (hx : ∑ i, x i = 0) (hy : ∑ i, y i = 0) :
    (∑ i, x i ^ 2) * (∑ i, y i ^ 2) ≤
      ∑ e ∈ pairs n, (x e.1 - x e.2) ^ 2 * (y e.1 - y e.2) ^ 2 := by
  have h2 := two_mul_sum_pairs (fun i j : Fin n => (x i - x j) ^ 2 * (y i - y j) ^ 2)
    (fun _ _ => by ring) (fun _ => by ring)
  have hinner : ∀ i : Fin n, ∑ j : Fin n, (x i - x j) ^ 2 * (y i - y j) ^ 2 =
      (n : ℝ) * (x i ^ 2 * y i ^ 2) + (∑ j, x j ^ 2 * y j ^ 2) +
      x i ^ 2 * (∑ j, y j ^ 2) + y i ^ 2 * (∑ j, x j ^ 2) +
      4 * (x i * y i) * (∑ j, x j * y j) -
      2 * y i * (∑ j, x j ^ 2 * y j) - 2 * x i * (∑ j, y j ^ 2 * x j) := by
    intro i
    have hpt : ∀ j : Fin n, (x i - x j) ^ 2 * (y i - y j) ^ 2 =
        x i ^ 2 * y i ^ 2 + x j ^ 2 * y j ^ 2 + x i ^ 2 * y j ^ 2 + y i ^ 2 * x j ^ 2 +
        4 * (x i * y i) * (x j * y j) -
        2 * (x i ^ 2 * y i) * y j - 2 * y i * (x j ^ 2 * y j) -
        2 * (y i ^ 2 * x i) * x j - 2 * x i * (y j ^ 2 * x j) := fun _ => by ring
    simp_rw [hpt, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, hx, hy]
    ring
  have hexp : ∑ i : Fin n, ∑ j : Fin n, (x i - x j) ^ 2 * (y i - y j) ^ 2 =
      2 * (n : ℝ) * (∑ i, x i ^ 2 * y i ^ 2) +
      2 * (∑ i, x i ^ 2) * (∑ j, y j ^ 2) +
      4 * (∑ i, x i * y i) ^ 2 := by
    simp_rw [hinner, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, ← Finset.sum_mul]
    rw [show ∑ i : Fin n, 2 * y i = 2 * ∑ i : Fin n, y i from (Finset.mul_sum ..).symm, hy,
      show ∑ i : Fin n, 2 * x i = 2 * ∑ i : Fin n, x i from (Finset.mul_sum ..).symm, hx,
      show ∑ i : Fin n, 4 * (x i * y i) = 4 * ∑ i : Fin n, x i * y i from (Finset.mul_sum ..).symm]
    ring
  have hnn1 : 0 ≤ 2 * (n : ℝ) * (∑ i, x i ^ 2 * y i ^ 2) :=
    mul_nonneg (by positivity) (Finset.sum_nonneg (fun _ _ => by positivity))
  have hnn2 : 0 ≤ 4 * (∑ i, x i * y i) ^ 2 := by positivity
  linarith

end BasicPairs

section Spectral

lemma exists_minimizer {n : ℕ} (hn : 2 ≤ n) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    ∃ (μ : ℝ) (x : Fin n → ℝ),
      0 ≤ μ ∧ (∑ i, x i = 0) ∧ (∑ i, x i ^ 2 = 1) ∧ quad G x = μ ∧
      (∀ z : Fin n → ℝ, (∑ i, z i = 0) → μ * (∑ i, z i ^ 2) ≤ quad G z) ∧
      (∀ i : Fin n, ∑ j ∈ Finset.univ.filter (G.Adj i), (x i - x j) = μ * x i) := by
  let S : Set (Fin n → ℝ) := {z | (∑ i, z i = 0) ∧ (∑ i, z i ^ 2 = 1)}
  have hne : S.Nonempty := by
    let i0 : Fin n := ⟨0, by omega⟩
    let i1 : Fin n := ⟨1, by omega⟩
    have h01 : i0 ≠ i1 := by
      intro h; have := congrArg Fin.val h; simp [i0, i1] at this
    let r : ℝ := 1 / Real.sqrt 2
    let z : Fin n → ℝ := fun i => if i = i0 then r else if i = i1 then -r else 0
    have hsum_two : ∀ f : ℝ → ℝ, f 0 = 0 → ∑ i : Fin n, f (z i) = f r + f (-r) := by
      intro f hf0
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i0)]
      have hi1 : i1 ∈ Finset.univ.erase i0 := Finset.mem_erase.mpr ⟨h01.symm, Finset.mem_univ _⟩
      rw [← Finset.add_sum_erase _ _ hi1]
      have hrest : ∑ i ∈ (Finset.univ.erase i0).erase i1, f (z i) = 0 := by
        apply Finset.sum_eq_zero; intro i hi
        have h1 := (Finset.mem_erase.mp hi).1
        have h0 := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
        simp [z, h0, h1, hf0]
      rw [hrest, add_zero]
      simp [z, h01.symm]
    refine ⟨z, ?_, ?_⟩
    · have := hsum_two id rfl; dsimp at this; linarith
    · have := hsum_two (fun t => t ^ 2) (by ring)
      have hsq : r ^ 2 = (1 : ℝ) / 2 := by
        dsimp [r]; rw [div_pow, one_pow, Real.sq_sqrt (by norm_num)]
      rw [this]; nlinarith
  have hclosed : IsClosed S := by
    have hc1 : Continuous (fun z : Fin n → ℝ => ∑ i, z i) :=
      continuous_finsetSum _ (fun i _ => continuous_apply i)
    have hc2 : Continuous (fun z : Fin n → ℝ => ∑ i, z i ^ 2) :=
      continuous_finsetSum _ (fun i _ => (continuous_apply i).pow 2)
    exact (isClosed_eq hc1 continuous_const).inter (isClosed_eq hc2 continuous_const)
  have hsub : S ⊆ Metric.closedBall (0 : Fin n → ℝ) 1 := by
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    rw [Real.norm_eq_abs]
    have hle : z i ^ 2 ≤ 1 := by
      calc z i ^ 2 ≤ ∑ j, z j ^ 2 :=
            Finset.single_le_sum (fun j _ => sq_nonneg (z j)) (Finset.mem_univ i)
        _ = 1 := hz.2
    nlinarith [sq_abs (z i), abs_nonneg (z i)]
  have hcomp : IsCompact S := (isCompact_closedBall (0 : Fin n → ℝ) 1).of_isClosed_subset hclosed hsub
  have hcont : Continuous (quad G) := by
    unfold quad
    exact continuous_finsetSum _ (fun e _ => ((continuous_apply e.1).sub (continuous_apply e.2)).pow 2)
  obtain ⟨x, hxS, hmin⟩ := hcomp.exists_isMinOn hne hcont.continuousOn
  let μ := quad G x
  have hbound : ∀ z : Fin n → ℝ, (∑ i, z i = 0) → μ * (∑ i, z i ^ 2) ≤ quad G z := by
    intro z hz
    by_cases hzn : ∑ i, z i ^ 2 = 0
    · rw [hzn, mul_zero]; exact quad_nonneg G z
    · have hpos : 0 < ∑ i, z i ^ 2 :=
        lt_of_le_of_ne (Finset.sum_nonneg (fun i _ => sq_nonneg (z i))) (Ne.symm hzn)
      let r := Real.sqrt (∑ i, z i ^ 2)
      have hr2 : r ^ 2 = ∑ i, z i ^ 2 := Real.sq_sqrt hpos.le
      let w : Fin n → ℝ := fun i => r⁻¹ * z i
      have hwS : w ∈ S := by
        refine ⟨?_, ?_⟩
        · simp only [w, ← Finset.mul_sum, hz, mul_zero]
        · have : ∑ i, (r⁻¹ * z i) ^ 2 = (r ^ 2)⁻¹ * ∑ i, z i ^ 2 := by
            simp_rw [mul_pow, inv_pow, ← Finset.mul_sum]
          rw [this, hr2, inv_mul_cancel₀ hpos.ne']
      have hle : μ ≤ (∑ i, z i ^ 2)⁻¹ * quad G z := by
        have h1 : μ ≤ quad G w := hmin hwS
        have hqw : quad G w = (r ^ 2)⁻¹ * quad G z := by
          simpa [w, inv_pow] using quad_smul G z r⁻¹
        rwa [hqw, hr2] at h1
      have hmul := mul_le_mul_of_nonneg_right hle hpos.le
      have hcancel : (∑ i, z i ^ 2)⁻¹ * quad G z * ∑ i, z i ^ 2 = quad G z := by
        field_simp [hpos.ne']
      linarith
  have heig : ∀ i : Fin n, ∑ j ∈ Finset.univ.filter (G.Adj i), (x i - x j) = μ * x i := by
    let Lx : Fin n → ℝ := fun i => ∑ j ∈ Finset.univ.filter (G.Adj i), (x i - x j)
    have hsumLx : ∑ i : Fin n, Lx i = 0 := by
      have h1 : ∑ i : Fin n, Lx i = ∑ i : Fin n, ∑ j : Fin n, if G.Adj i j then x i - x j else 0 :=
        Finset.sum_congr rfl (fun i _ => Finset.sum_filter (fun j => G.Adj i j) (fun j => x i - x j))
      have h2 : ∑ i : Fin n, ∑ j : Fin n, (if G.Adj i j then x i - x j else 0) =
          -(∑ i : Fin n, ∑ j : Fin n, if G.Adj i j then x i - x j else 0) := by
        conv_lhs => rw [Finset.sum_comm]
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl; intro i _
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl; intro j _
        by_cases h : G.Adj i j
        · rw [if_pos h.symm, if_pos h]; ring
        · have h' : ¬ G.Adj j i := fun hadj => h hadj.symm
          rw [if_neg h', if_neg h]; ring
      linarith
    have hvar : ∀ (v : Fin n → ℝ) (t : ℝ),
        quad G (fun i => x i + t * v i) =
        quad G x + 2 * t * (∑ i, Lx i * v i) + t ^ 2 * quad G v := by
      intro v t
      have h2 := two_mul_quad G (fun i => x i + t * v i)
      have h2x := two_mul_quad G x
      have h2v := two_mul_quad G v
      have hcross : ∑ i : Fin n, ∑ j : Fin n,
          (if G.Adj i j then (x i - x j) * (v i - v j) else 0) =
          2 * ∑ i : Fin n, Lx i * v i := by
        have hsplit : ∀ i j : Fin n,
            (if G.Adj i j then (x i - x j) * (v i - v j) else 0) =
            (if G.Adj i j then (x i - x j) * v i else 0) +
            (if G.Adj i j then (x j - x i) * v j else 0) := by
          intro i j; by_cases h : G.Adj i j <;> simp [h]; ring
        simp_rw [hsplit, Finset.sum_add_distrib]
        have hsym : ∑ i : Fin n, ∑ j : Fin n, (if G.Adj i j then (x j - x i) * v j else 0) =
            ∑ i : Fin n, ∑ j : Fin n, (if G.Adj i j then (x i - x j) * v i else 0) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro i _
          apply Finset.sum_congr rfl; intro j _
          by_cases h : G.Adj i j
          · simp [h, h.symm]
          · have h' : ¬ G.Adj j i := fun hadj => h hadj.symm
            simp [h, h']
        rw [hsym]
        have hfold : ∑ i : Fin n, ∑ j : Fin n, (if G.Adj i j then (x i - x j) * v i else 0) =
            ∑ i : Fin n, Lx i * v i := by
          apply Finset.sum_congr rfl; intro i _
          rw [← Finset.sum_filter, ← Finset.sum_mul]
        rw [hfold]; ring
      have hexp : ∑ i : Fin n, ∑ j : Fin n,
          (if G.Adj i j then (x i + t * v i - (x j + t * v j)) ^ 2 else 0) =
          (∑ i : Fin n, ∑ j : Fin n, if G.Adj i j then (x i - x j) ^ 2 else 0) +
          2 * t * (∑ i : Fin n, ∑ j : Fin n, if G.Adj i j then (x i - x j) * (v i - v j) else 0) +
          t ^ 2 * (∑ i : Fin n, ∑ j : Fin n, if G.Adj i j then (v i - v j) ^ 2 else 0) := by
        have hpt : ∀ i j : Fin n,
            (if G.Adj i j then (x i + t * v i - (x j + t * v j)) ^ 2 else 0) =
            (if G.Adj i j then (x i - x j) ^ 2 else 0) +
            2 * t * (if G.Adj i j then (x i - x j) * (v i - v j) else 0) +
            t ^ 2 * (if G.Adj i j then (v i - v j) ^ 2 else 0) := by
          intro i j; by_cases h : G.Adj i j <;> simp [h]; ring
        simp_rw [hpt, Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [hexp, hcross, ← h2x, ← h2v] at h2
      linarith
    let v : Fin n → ℝ := fun i => Lx i - μ * x i
    have hvsum : ∑ i, v i = 0 := by
      simp only [v, Finset.sum_sub_distrib, ← Finset.mul_sum, hsumLx, hxS.1, mul_zero, sub_zero]
    let A : ℝ := ∑ i, v i ^ 2
    let B : ℝ := quad G v - μ * A
    have hpoly : ∀ t : ℝ, 0 ≤ 2 * t * A + t ^ 2 * B := by
      intro t
      have hzt : ∑ i, (x i + t * v i) = 0 := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hxS.1, hvsum, mul_zero, add_zero]
      have hle := hbound (fun i => x i + t * v i) hzt
      rw [hvar v t] at hle
      have hnorm : ∑ i, (x i + t * v i) ^ 2 =
          (∑ i, x i ^ 2) + 2 * t * (∑ i, x i * v i) + t ^ 2 * A := by
        have : ∀ i, (x i + t * v i) ^ 2 = x i ^ 2 + 2 * t * (x i * v i) + t ^ 2 * v i ^ 2 :=
          fun _ => by ring
        simp_rw [this, Finset.sum_add_distrib, ← Finset.mul_sum]
        rfl
      rw [hnorm, hxS.2] at hle
      have hv2 : A = (∑ i, Lx i * v i) - μ * (∑ i, x i * v i) := by
        have : ∀ i, v i ^ 2 = Lx i * v i - μ * (x i * v i) := fun i => by dsimp [v]; ring
        simp_rw [A, this, Finset.sum_sub_distrib, ← Finset.mul_sum]
      have hmu : quad G x = μ := rfl
      have hdiff : 2 * t * (∑ i, Lx i * v i) - μ * (2 * t * (∑ i, x i * v i)) = 2 * t * A := by
        rw [hv2]; ring
      dsimp only [B]
      nlinarith
    have hA0 : A = 0 := by
      by_contra hne0
      have hApos : 0 < A :=
        lt_of_le_of_ne (Finset.sum_nonneg (fun i _ => sq_nonneg (v i))) (Ne.symm hne0)
      have hBnn : 0 ≤ B := sub_nonneg.mpr (hbound v hvsum)
      let t := -A / (B + 1)
      have ht := hpoly t
      have hden : 0 < B + 1 := by linarith
      have hcalc : 2 * t * A + t ^ 2 * B = -(A ^ 2 * (B + 2)) / (B + 1) ^ 2 := by
        dsimp [t]; field_simp [hden.ne']; ring
      have hneg : -(A ^ 2 * (B + 2)) / (B + 1) ^ 2 < 0 :=
        div_neg_of_neg_of_pos (by nlinarith) (by positivity)
      linarith
    intro i
    have hi0 : v i ^ 2 = 0 := by
      have hle := Finset.single_le_sum (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i)
      nlinarith [sq_nonneg (v i)]
    have hvi : v i = 0 := sq_eq_zero_iff.mp hi0
    dsimp [v, Lx] at hvi
    linarith
  exact ⟨μ, x, quad_nonneg G x, hxS.1, hxS.2, rfl, hbound, heig⟩

lemma eigen_neighbor_bounds {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {μ : ℝ} {x : Fin n → ℝ} (hx0 : ∑ i, x i = 0) (hx1 : ∑ i, x i ^ 2 = 1)
    (heig : ∀ i, ∑ j ∈ Finset.univ.filter (G.Adj i), (x i - x j) = μ * x i)
    (hmu : μ < 1) {v1 v2 : Fin n} (hmax : ∀ i, x i ≤ x v1) (hmin : ∀ i, x v2 ≤ x i) :
    x v2 < 0 ∧ 0 < x v1 ∧
    (∀ u, G.Adj v1 u → 0 < x u) ∧ (∀ w, G.Adj v2 w → x w < 0) ∧
    ¬ G.Adj v1 v2 ∧ (∀ z, ¬ (G.Adj v1 z ∧ G.Adj v2 z)) := by
  have hx1pos : 0 < x v1 := by
    by_contra hle; push Not at hle
    have hall : ∀ i, x i = 0 := by
      have hneg : ∀ i, x i ≤ 0 := fun i => (hmax i).trans hle
      intro i; by_contra hi
      have hlt : x i < 0 := lt_of_le_of_ne (hneg i) hi
      have hsumlt : ∑ j : Fin n, x j < 0 := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
        linarith [Finset.sum_nonpos (s := Finset.univ.erase i) (fun j _ => hneg j)]
      linarith
    have : ∑ i, x i ^ 2 = 0 := Finset.sum_eq_zero (fun i _ => by rw [hall i]; ring)
    linarith
  have hx2neg : x v2 < 0 := by
    by_contra hge; push Not at hge
    have hall : ∀ i, x i = 0 := by
      have hpos : ∀ i, 0 ≤ x i := fun i => hge.trans (hmin i)
      intro i; by_contra hi
      have hgt : 0 < x i := lt_of_le_of_ne (hpos i) (Ne.symm hi)
      have hsumgt : 0 < ∑ j : Fin n, x j := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
        linarith [Finset.sum_nonneg (s := Finset.univ.erase i) (fun j _ => hpos j)]
      linarith
    have : ∑ i, x i ^ 2 = 0 := Finset.sum_eq_zero (fun i _ => by rw [hall i]; ring)
    linarith
  have hN1 : ∀ u, G.Adj v1 u → 0 < x u := by
    intro u hu
    have hle : x v1 - x u ≤ ∑ j ∈ Finset.univ.filter (G.Adj v1), (x v1 - x j) :=
      Finset.single_le_sum (fun j _ => sub_nonneg.mpr (hmax j))
        (Finset.mem_filter.mpr ⟨Finset.mem_univ u, hu⟩)
    rw [heig v1] at hle; nlinarith
  have hN2 : ∀ w, G.Adj v2 w → x w < 0 := by
    intro w hw
    have hge : ∑ j ∈ Finset.univ.filter (G.Adj v2), (x v2 - x j) ≤ x v2 - x w := by
      have hle : x w - x v2 ≤ ∑ j ∈ Finset.univ.filter (G.Adj v2), (x j - x v2) :=
        Finset.single_le_sum (fun j _ => sub_nonneg.mpr (hmin j))
          (Finset.mem_filter.mpr ⟨Finset.mem_univ w, hw⟩)
      have hneg : ∑ j ∈ Finset.univ.filter (G.Adj v2), (x j - x v2) =
          -(∑ j ∈ Finset.univ.filter (G.Adj v2), (x v2 - x j)) := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl (fun _ _ => by ring)
      linarith
    rw [heig v2] at hge; nlinarith
  exact ⟨hx2neg, hx1pos, hN1, hN2, fun h => by linarith [hN1 v2 h],
    fun z ⟨h1, h2⟩ => by linarith [hN1 z h1, hN2 z h2]⟩

lemma no_len3_path_contradiction {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    [DecidableRel Gᶜ.Adj] {v1 v2 : Fin n} (hv12 : v1 ≠ v2)
    (hna : ¬ G.Adj v1 v2) (hnc : ∀ z, ¬ (G.Adj v1 z ∧ G.Adj v2 z))
    (hn3 : ∀ u w, ¬ (G.Adj v1 u ∧ G.Adj u w ∧ G.Adj w v2))
    {p q : Fin n} (hpq : p ≠ q)
    (hcpq : ¬ Gᶜ.Adj p q) (hcc : ∀ z, ¬ (Gᶜ.Adj p z ∧ Gᶜ.Adj q z)) : False := by
  have hGpq : G.Adj p q := by
    by_contra hna'; exact hcpq ((SimpleGraph.compl_adj _ _ _).mpr ⟨hpq, hna'⟩)
  by_cases hp1 : p = v1
  · subst hp1
    exact hcc v2 ⟨(SimpleGraph.compl_adj _ _ _).mpr ⟨hv12, hna⟩,
      (SimpleGraph.compl_adj _ _ _).mpr ⟨fun h => hna (h ▸ hGpq), fun h => hnc q ⟨hGpq, h.symm⟩⟩⟩
  · by_cases hq1 : q = v1
    · subst hq1
      exact hcc v2 ⟨(SimpleGraph.compl_adj _ _ _).mpr ⟨fun h => hna (h ▸ hGpq.symm),
          fun h => hnc p ⟨hGpq.symm, h.symm⟩⟩,
        (SimpleGraph.compl_adj _ _ _).mpr ⟨hv12, hna⟩⟩
    · by_cases hpv1 : G.Adj p v1
      · exact hcc v2 ⟨(SimpleGraph.compl_adj _ _ _).mpr ⟨fun h => hna (h ▸ hpv1.symm),
            fun h => hnc p ⟨hpv1.symm, h.symm⟩⟩,
          (SimpleGraph.compl_adj _ _ _).mpr ⟨fun h => hnc p ⟨hpv1.symm, h ▸ hGpq.symm⟩,
            fun h => hn3 p q ⟨hpv1.symm, hGpq, h⟩⟩⟩
      · by_cases hqv1 : G.Adj q v1
        · exact hcc v2 ⟨(SimpleGraph.compl_adj _ _ _).mpr ⟨fun h => hnc q ⟨hqv1.symm, h ▸ hGpq⟩,
              fun h => hn3 q p ⟨hqv1.symm, hGpq.symm, h⟩⟩,
            (SimpleGraph.compl_adj _ _ _).mpr ⟨fun h => hna (h ▸ hqv1.symm),
              fun h => hnc q ⟨hqv1.symm, h.symm⟩⟩⟩
        · exact hcc v1 ⟨(SimpleGraph.compl_adj _ _ _).mpr ⟨hp1, hpv1⟩,
            (SimpleGraph.compl_adj _ _ _).mpr ⟨hq1, hqv1⟩⟩

lemma step1_small_spread {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    [DecidableRel Gᶜ.Adj] {x y : Fin n → ℝ}
    (hx0 : ∑ i, x i = 0) (hy0 : ∑ i, y i = 0)
    (hx1 : ∑ i, x i ^ 2 = 1) (hy1 : ∑ i, y i ^ 2 = 1)
    (hMx : ∀ i j, (x i - x j) ^ 2 ≤ 1) (hMy : ∀ i j, (y i - y j) ^ 2 ≤ 1) :
    1 ≤ quad G x + quad Gᶜ y := by
  have h1 : ∑ e ∈ pairs n, min ((x e.1 - x e.2) ^ 2) ((y e.1 - y e.2) ^ 2) ≤
      quad G x + quad Gᶜ y := by
    unfold quad
    have hfc : (pairs n).filter (fun e => Gᶜ.Adj e.1 e.2) =
        (pairs n).filter (fun e => ¬ G.Adj e.1 e.2) := by
      ext e
      simp only [Finset.mem_filter, pairs, Finset.mem_univ, true_and, SimpleGraph.compl_adj]
      exact ⟨fun ⟨h, _, hna⟩ => ⟨h, hna⟩, fun ⟨h, hna⟩ => ⟨h, ne_of_lt h, hna⟩⟩
    rw [hfc, ← Finset.sum_filter_add_sum_filter_not (pairs n) (fun e => G.Adj e.1 e.2)
      (fun e => min ((x e.1 - x e.2) ^ 2) ((y e.1 - y e.2) ^ 2))]
    exact add_le_add (Finset.sum_le_sum (fun _ _ => min_le_left _ _))
      (Finset.sum_le_sum (fun _ _ => min_le_right _ _))
  have h2 : ∑ e ∈ pairs n, (x e.1 - x e.2) ^ 2 * (y e.1 - y e.2) ^ 2 ≤
      ∑ e ∈ pairs n, min ((x e.1 - x e.2) ^ 2) ((y e.1 - y e.2) ^ 2) := by
    apply Finset.sum_le_sum; intro e _
    have ha := hMx e.1 e.2; have hb := hMy e.1 e.2
    rcases le_total ((x e.1 - x e.2) ^ 2) ((y e.1 - y e.2) ^ 2) with h | h
    · rw [min_eq_left h]; nlinarith [sq_nonneg (x e.1 - x e.2)]
    · rw [min_eq_right h]; nlinarith [sq_nonneg (y e.1 - y e.2)]
  have h3 := pair_sq_prod_bound x y hx0 hy0
  rw [hx1, hy1, mul_one] at h3
  linarith

end Spectral

section PartitionAndGeneralBounds

lemma star_sum_bound {n : ℕ} (U : Finset (Fin n)) (c : Fin n) (hc : c ∈ U) (y : Fin n → ℝ) :
    ∑ i ∈ U, ∑ j ∈ U, (y i - y j) ^ 2 ≤
      2 * (U.card : ℝ) * ∑ u ∈ U.erase c, (y c - y u) ^ 2 := by
  have hexp : ∑ i ∈ U, ∑ j ∈ U, (y i - y j) ^ 2 =
      2 * (U.card : ℝ) * (∑ i ∈ U, (y i - y c) ^ 2) - 2 * (∑ i ∈ U, (y i - y c)) ^ 2 := by
    have hinner : ∀ i ∈ U, ∑ j ∈ U, (y i - y j) ^ 2 =
        (U.card : ℝ) * (y i - y c) ^ 2 + (∑ j ∈ U, (y j - y c) ^ 2) -
        2 * (y i - y c) * (∑ j ∈ U, (y j - y c)) := by
      intro i _
      have hpt : ∀ j ∈ U, (y i - y j) ^ 2 =
          ((y i - y c) ^ 2 + (y j - y c) ^ 2) - (2 * (y i - y c)) * (y j - y c) := fun _ _ => by ring
      rw [Finset.sum_congr rfl hpt, Finset.sum_sub_distrib, Finset.sum_add_distrib,
        Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
    rw [Finset.sum_congr rfl hinner, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, ← Finset.sum_mul,
      show ∑ i ∈ U, 2 * (y i - y c) = 2 * ∑ i ∈ U, (y i - y c) from (Finset.mul_sum ..).symm]
    ring
  have herase : ∑ i ∈ U, (y i - y c) ^ 2 = ∑ u ∈ U.erase c, (y c - y u) ^ 2 := by
    rw [← Finset.add_sum_erase U (fun i => (y i - y c) ^ 2) hc]
    have h0 : (y c - y c) ^ 2 = 0 := by ring
    rw [h0, zero_add]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  rw [hexp, herase]
  nlinarith [sq_nonneg (∑ i ∈ U, (y i - y c))]

structure PathPartition {n : ℕ} (G : SimpleGraph (Fin n)) where
  v1 : Fin n
  v2 : Fin n
  hv12 : v1 ≠ v2
  hna : ¬ G.Adj v1 v2
  hnc : ∀ z, ¬ (G.Adj v1 z ∧ G.Adj v2 z)
  P : Finset (Fin n × Fin n)
  hPne : P.Nonempty
  hPedge : ∀ e ∈ P, G.Adj v1 e.1 ∧ G.Adj e.1 e.2 ∧ G.Adj e.2 v2
  hPdisj : ∀ e1 ∈ P, ∀ e2 ∈ P, e1 ≠ e2 → e1.1 ≠ e2.1 ∧ e1.2 ≠ e2.2
  S1 : Finset (Fin n)
  S2 : Finset (Fin n)
  A : Finset (Fin n)
  B : Finset (Fin n)
  C : Finset (Fin n)
  hS2 : S2 = P.image Prod.fst
  hS1 : S1 = P.image Prod.snd
  hA : ∀ u, u ∈ A ↔ G.Adj v1 u ∧ u ∉ S2
  hB : ∀ w, w ∈ B ↔ G.Adj v2 w ∧ w ∉ S1
  hC : ∀ z, z ∈ C ↔ z ≠ v1 ∧ z ≠ v2 ∧ ¬ G.Adj v1 z ∧ ¬ G.Adj v2 z
  hAB : ∀ u ∈ A, ∀ w ∈ B, ¬ G.Adj u w

lemma exists_path_partition {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {v1 v2 : Fin n} (hv12 : v1 ≠ v2) (hna : ¬ G.Adj v1 v2)
    (hnc : ∀ z, ¬ (G.Adj v1 z ∧ G.Adj v2 z))
    (hex : ∃ u w, G.Adj v1 u ∧ G.Adj u w ∧ G.Adj w v2) :
    ∃ pp : PathPartition G, pp.v1 = v1 ∧ pp.v2 = v2 := by
  classical
  let valid (P : Finset (Fin n × Fin n)) : Prop :=
    (∀ e ∈ P, G.Adj v1 e.1 ∧ G.Adj e.1 e.2 ∧ G.Adj e.2 v2) ∧
    (∀ e1 ∈ P, ∀ e2 ∈ P, e1 ≠ e2 → e1.1 ≠ e2.1 ∧ e1.2 ≠ e2.2)
  let F : Finset (Finset (Fin n × Fin n)) := Finset.univ.filter valid
  obtain ⟨u0, w0, hu0, huw0, hw0⟩ := hex
  have hmem0 : ({(u0, w0)} : Finset (Fin n × Fin n)) ∈ F := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
    · intro e he; rw [Finset.mem_singleton.mp he]; exact ⟨hu0, huw0, hw0⟩
    · intro e1 h1 e2 h2 hne
      rw [Finset.mem_singleton.mp h1, Finset.mem_singleton.mp h2] at hne
      exact False.elim (hne rfl)
  obtain ⟨P, hPF, hPmax⟩ := Finset.exists_max_image F Finset.card ⟨{(u0, w0)}, hmem0⟩
  have hPval : valid P := (Finset.mem_filter.mp hPF).2
  have hPne : P.Nonempty := by
    have hle := hPmax {(u0, w0)} hmem0
    rw [Finset.card_singleton] at hle
    exact Finset.card_pos.mp (by omega)
  let S2 := P.image Prod.fst
  let S1 := P.image Prod.snd
  let A := (Finset.univ.filter (G.Adj v1)) \ S2
  let B := (Finset.univ.filter (G.Adj v2)) \ S1
  let C := Finset.univ.filter (fun z => z ≠ v1 ∧ z ≠ v2 ∧ ¬ G.Adj v1 z ∧ ¬ G.Adj v2 z)
  have hAB : ∀ u ∈ A, ∀ w ∈ B, ¬ G.Adj u w := by
    intro u hu w hw hadj
    have hu' := Finset.mem_sdiff.mp hu
    have hw' := Finset.mem_sdiff.mp hw
    have hu1 : G.Adj v1 u := (Finset.mem_filter.mp hu'.1).2
    have hw2 : G.Adj w v2 := (Finset.mem_filter.mp hw'.1).2.symm
    have hnotmem : (u, w) ∉ P := fun hm => hu'.2 (Finset.mem_image.mpr ⟨(u, w), hm, rfl⟩)
    have hins : insert (u, w) P ∈ F := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
      · intro e he
        rcases Finset.mem_insert.mp he with rfl | heP
        · exact ⟨hu1, hadj, hw2⟩
        · exact hPval.1 e heP
      · intro e1 h1 e2 h2 hne
        rcases Finset.mem_insert.mp h1 with rfl | h1P <;>
        rcases Finset.mem_insert.mp h2 with rfl | h2P
        · exact False.elim (hne rfl)
        · exact ⟨fun heq => hu'.2 (Finset.mem_image.mpr ⟨e2, h2P, heq.symm⟩),
                 fun heq => hw'.2 (Finset.mem_image.mpr ⟨e2, h2P, heq.symm⟩)⟩
        · exact ⟨fun heq => hu'.2 (Finset.mem_image.mpr ⟨e1, h1P, heq⟩),
                 fun heq => hw'.2 (Finset.mem_image.mpr ⟨e1, h1P, heq⟩)⟩
        · exact hPval.2 e1 h1P e2 h2P hne
    have hle := hPmax (insert (u, w) P) hins
    rw [Finset.card_insert_of_notMem hnotmem] at hle
    omega
  exact ⟨{
    v1 := v1, v2 := v2, hv12 := hv12, hna := hna, hnc := hnc,
    P := P, hPne := hPne, hPedge := hPval.1, hPdisj := hPval.2,
    S1 := S1, S2 := S2, A := A, B := B, C := C,
    hS2 := rfl, hS1 := rfl,
    hA := fun u => by simp only [A, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and],
    hB := fun w => by simp only [B, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and],
    hC := fun z => by simp only [C, Finset.mem_filter, Finset.mem_univ, true_and],
    hAB := hAB
  }, rfl, rfl⟩

namespace PathPartition

variable {n : ℕ} {G : SimpleGraph (Fin n)} (pp : PathPartition G)

lemma S2_adj {u : Fin n} (hu : u ∈ pp.S2) : G.Adj pp.v1 u := by
  rw [pp.hS2] at hu
  obtain ⟨e, heP, rfl⟩ := Finset.mem_image.mp hu
  exact (pp.hPedge e heP).1

lemma S1_adj {w : Fin n} (hw : w ∈ pp.S1) : G.Adj pp.v2 w := by
  rw [pp.hS1] at hw
  obtain ⟨e, heP, rfl⟩ := Finset.mem_image.mp hw
  exact (pp.hPedge e heP).2.2.symm

lemma card_S1 : pp.S1.card = pp.P.card := by
  rw [pp.hS1]
  apply Finset.card_image_of_injOn
  intro e1 h1 e2 h2 heq
  by_contra hne
  exact (pp.hPdisj e1 h1 e2 h2 hne).2 heq

lemma card_S2 : pp.S2.card = pp.P.card := by
  rw [pp.hS2]
  apply Finset.card_image_of_injOn
  intro e1 h1 e2 h2 heq
  by_contra hne
  exact (pp.hPdisj e1 h1 e2 h2 hne).1 heq

lemma v1_not_S1 : pp.v1 ∉ pp.S1 := fun h => pp.hna (pp.S1_adj h).symm
lemma v1_not_S2 : pp.v1 ∉ pp.S2 := fun h => G.loopless.irrefl pp.v1 (pp.S2_adj h)
lemma v1_not_A : pp.v1 ∉ pp.A := fun h => G.loopless.irrefl pp.v1 ((pp.hA pp.v1).mp h).1
lemma v1_not_B : pp.v1 ∉ pp.B := fun h => pp.hna ((pp.hB pp.v1).mp h).1.symm
lemma v1_not_C : pp.v1 ∉ pp.C := fun h => ((pp.hC pp.v1).mp h).1 rfl

lemma v2_not_S1 : pp.v2 ∉ pp.S1 := fun h => G.loopless.irrefl pp.v2 (pp.S1_adj h)
lemma v2_not_S2 : pp.v2 ∉ pp.S2 := fun h => pp.hna (pp.S2_adj h)
lemma v2_not_A : pp.v2 ∉ pp.A := fun h => pp.hna ((pp.hA pp.v2).mp h).1
lemma v2_not_B : pp.v2 ∉ pp.B := fun h => G.loopless.irrefl pp.v2 ((pp.hB pp.v2).mp h).1
lemma v2_not_C : pp.v2 ∉ pp.C := fun h => ((pp.hC pp.v2).mp h).2.1 rfl

lemma disj_S1_S2 : Disjoint pp.S1 pp.S2 := Finset.disjoint_left.mpr fun z h1 h2 =>
  pp.hnc z ⟨pp.S2_adj h2, pp.S1_adj h1⟩
lemma disj_S1_A : Disjoint pp.S1 pp.A := Finset.disjoint_left.mpr fun z h1 hA =>
  pp.hnc z ⟨((pp.hA z).mp hA).1, pp.S1_adj h1⟩
lemma disj_S1_B : Disjoint pp.S1 pp.B := Finset.disjoint_left.mpr fun z h1 hB =>
  ((pp.hB z).mp hB).2 h1
lemma disj_S1_C : Disjoint pp.S1 pp.C := Finset.disjoint_left.mpr fun z h1 hC =>
  ((pp.hC z).mp hC).2.2.2 (pp.S1_adj h1)
lemma disj_S2_A : Disjoint pp.S2 pp.A := Finset.disjoint_left.mpr fun z h2 hA =>
  ((pp.hA z).mp hA).2 h2
lemma disj_S2_B : Disjoint pp.S2 pp.B := Finset.disjoint_left.mpr fun z h2 hB =>
  pp.hnc z ⟨pp.S2_adj h2, ((pp.hB z).mp hB).1⟩
lemma disj_S2_C : Disjoint pp.S2 pp.C := Finset.disjoint_left.mpr fun z h2 hC =>
  ((pp.hC z).mp hC).2.2.1 (pp.S2_adj h2)
lemma disj_A_B : Disjoint pp.A pp.B := Finset.disjoint_left.mpr fun z hA hB =>
  pp.hnc z ⟨((pp.hA z).mp hA).1, ((pp.hB z).mp hB).1⟩
lemma disj_A_C : Disjoint pp.A pp.C := Finset.disjoint_left.mpr fun z hA hC =>
  ((pp.hC z).mp hC).2.2.1 ((pp.hA z).mp hA).1
lemma disj_B_C : Disjoint pp.B pp.C := Finset.disjoint_left.mpr fun z hB hC =>
  ((pp.hC z).mp hC).2.2.2 ((pp.hB z).mp hB).1

lemma cover (z : Fin n) :
    z = pp.v1 ∨ z = pp.v2 ∨ z ∈ pp.S1 ∨ z ∈ pp.S2 ∨ z ∈ pp.A ∨ z ∈ pp.B ∨ z ∈ pp.C := by
  by_cases h1 : z = pp.v1
  · exact Or.inl h1
  by_cases h2 : z = pp.v2
  · exact Or.inr (Or.inl h2)
  by_cases ha1 : G.Adj pp.v1 z
  · by_cases hs2 : z ∈ pp.S2
    · exact Or.inr (Or.inr (Or.inr (Or.inl hs2)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ((pp.hA z).mpr ⟨ha1, hs2⟩)))))
  by_cases ha2 : G.Adj pp.v2 z
  · by_cases hs1 : z ∈ pp.S1
    · exact Or.inr (Or.inr (Or.inl hs1))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ((pp.hB z).mpr ⟨ha2, hs1⟩))))))
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ((pp.hC z).mpr ⟨h1, h2, ha1, ha2⟩))))))

-- Clean 7-block partition API
def blk : Fin 7 → Finset (Fin n)
  | 0 => {pp.v1}
  | 1 => {pp.v2}
  | 2 => pp.S1
  | 3 => pp.S2
  | 4 => pp.A
  | 5 => pp.B
  | 6 => pp.C

lemma blk_disjoint {a b : Fin 7} (hab : a ≠ b) : Disjoint (pp.blk a) (pp.blk b) := by
  fin_cases a <;> fin_cases b <;> try (exact False.elim (hab rfl))
  all_goals
    dsimp [blk]
    first
    | exact Finset.disjoint_singleton.mpr pp.hv12
    | exact Finset.disjoint_singleton.mpr pp.hv12.symm
    | exact Finset.disjoint_singleton_left.mpr pp.v1_not_S1
    | exact Finset.disjoint_singleton_right.mpr pp.v1_not_S1
    | exact Finset.disjoint_singleton_left.mpr pp.v1_not_S2
    | exact Finset.disjoint_singleton_right.mpr pp.v1_not_S2
    | exact Finset.disjoint_singleton_left.mpr pp.v1_not_A
    | exact Finset.disjoint_singleton_right.mpr pp.v1_not_A
    | exact Finset.disjoint_singleton_left.mpr pp.v1_not_B
    | exact Finset.disjoint_singleton_right.mpr pp.v1_not_B
    | exact Finset.disjoint_singleton_left.mpr pp.v1_not_C
    | exact Finset.disjoint_singleton_right.mpr pp.v1_not_C
    | exact Finset.disjoint_singleton_left.mpr pp.v2_not_S1
    | exact Finset.disjoint_singleton_right.mpr pp.v2_not_S1
    | exact Finset.disjoint_singleton_left.mpr pp.v2_not_S2
    | exact Finset.disjoint_singleton_right.mpr pp.v2_not_S2
    | exact Finset.disjoint_singleton_left.mpr pp.v2_not_A
    | exact Finset.disjoint_singleton_right.mpr pp.v2_not_A
    | exact Finset.disjoint_singleton_left.mpr pp.v2_not_B
    | exact Finset.disjoint_singleton_right.mpr pp.v2_not_B
    | exact Finset.disjoint_singleton_left.mpr pp.v2_not_C
    | exact Finset.disjoint_singleton_right.mpr pp.v2_not_C
    | exact pp.disj_S1_S2 | exact pp.disj_S1_S2.symm
    | exact pp.disj_S1_A | exact pp.disj_S1_A.symm
    | exact pp.disj_S1_B | exact pp.disj_S1_B.symm
    | exact pp.disj_S1_C | exact pp.disj_S1_C.symm
    | exact pp.disj_S2_A | exact pp.disj_S2_A.symm
    | exact pp.disj_S2_B | exact pp.disj_S2_B.symm
    | exact pp.disj_S2_C | exact pp.disj_S2_C.symm
    | exact pp.disj_A_B | exact pp.disj_A_B.symm
    | exact pp.disj_A_C | exact pp.disj_A_C.symm
    | exact pp.disj_B_C | exact pp.disj_B_C.symm

lemma biUnion_blk : (Finset.univ : Finset (Fin 7)).biUnion pp.blk = Finset.univ := by
  ext z
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, iff_true]
  rcases pp.cover z with rfl | rfl | h | h | h | h | h
  · exact ⟨0, by simp [blk]⟩
  · exact ⟨1, by simp [blk]⟩
  · exact ⟨2, h⟩
  · exact ⟨3, h⟩
  · exact ⟨4, h⟩
  · exact ⟨5, h⟩
  · exact ⟨6, h⟩

lemma sum_univ_blk (f : Fin n → ℝ) :
    ∑ z : Fin n, f z = ∑ k : Fin 7, ∑ z ∈ pp.blk k, f z := by
  have hpw : ((Finset.univ : Finset (Fin 7)) : Set (Fin 7)).PairwiseDisjoint pp.blk :=
    fun _ _ _ _ hab => pp.blk_disjoint hab
  rw [← pp.biUnion_blk, Finset.sum_biUnion hpw]

lemma sum_univ_split (f : Fin n → ℝ) :
    ∑ z : Fin n, f z =
      f pp.v1 + f pp.v2 + (∑ z ∈ pp.S1, f z) + (∑ z ∈ pp.S2, f z) +
      (∑ z ∈ pp.A, f z) + (∑ z ∈ pp.B, f z) + (∑ z ∈ pp.C, f z) := by
  rw [pp.sum_univ_blk, Fin.sum_univ_seven]
  simp only [blk, Finset.sum_singleton]

lemma sum_double_blk (F : Fin n → Fin n → ℝ) :
    ∑ i : Fin n, ∑ j : Fin n, F i j =
      ∑ a : Fin 7, ∑ b : Fin 7, ∑ i ∈ pp.blk a, ∑ j ∈ pp.blk b, F i j := by
  rw [pp.sum_univ_blk]
  apply Finset.sum_congr rfl; intro a _
  simp_rw [pp.sum_univ_blk]
  exact Finset.sum_comm

lemma card_eq : n = pp.A.card + pp.B.card + pp.C.card + 2 * pp.P.card + 2 := by
  have h := pp.sum_univ_split (fun _ => (1 : ℝ))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
    pp.card_S1, pp.card_S2] at h
  have hnat : (n : ℝ) = ((pp.A.card + pp.B.card + pp.C.card + 2 * pp.P.card + 2 : ℕ) : ℝ) := by
    push_cast; linarith
  exact_mod_cast hnat

def swap : PathPartition G where
  v1 := pp.v2
  v2 := pp.v1
  hv12 := pp.hv12.symm
  hna := fun h => pp.hna h.symm
  hnc := fun z ⟨h1, h2⟩ => pp.hnc z ⟨h2, h1⟩
  P := pp.P.image Prod.swap
  hPne := pp.hPne.image Prod.swap
  hPedge := by
    intro e he
    obtain ⟨e0, h0, rfl⟩ := Finset.mem_image.mp he
    have h := pp.hPedge e0 h0
    exact ⟨h.2.2.symm, h.2.1.symm, h.1.symm⟩
  hPdisj := by
    intro e1 h1 e2 h2 hne
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp h1
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp h2
    have hab : a ≠ b := fun h => hne (h ▸ rfl)
    have h := pp.hPdisj a ha b hb hab
    exact ⟨h.2, h.1⟩
  S1 := pp.S2
  S2 := pp.S1
  A := pp.B
  B := pp.A
  C := pp.C
  hS2 := by rw [pp.hS1, Finset.image_image]; rfl
  hS1 := by rw [pp.hS2, Finset.image_image]; rfl
  hA := pp.hB
  hB := pp.hA
  hC := fun z => by rw [pp.hC]; tauto
  hAB := fun u hu w hw hadj => pp.hAB w hw u hu hadj.symm

lemma compl_adj_v1_v2 : Gᶜ.Adj pp.v1 pp.v2 :=
  (SimpleGraph.compl_adj _ _ _).mpr ⟨pp.hv12, pp.hna⟩

lemma compl_adj_v1_S1 {w : Fin n} (hw : w ∈ pp.S1) : Gᶜ.Adj pp.v1 w :=
  (SimpleGraph.compl_adj _ _ _).mpr ⟨fun h => pp.v1_not_S1 (h ▸ hw),
    fun hadj => pp.hnc w ⟨hadj, pp.S1_adj hw⟩⟩

lemma compl_adj_v1_B {w : Fin n} (hw : w ∈ pp.B) : Gᶜ.Adj pp.v1 w :=
  (SimpleGraph.compl_adj _ _ _).mpr ⟨fun h => pp.v1_not_B (h ▸ hw),
    fun hadj => pp.hnc w ⟨hadj, ((pp.hB w).mp hw).1⟩⟩

lemma compl_adj_v1_C {z : Fin n} (hz : z ∈ pp.C) : Gᶜ.Adj pp.v1 z :=
  (SimpleGraph.compl_adj _ _ _).mpr ⟨((pp.hC z).mp hz).1.symm, ((pp.hC z).mp hz).2.2.1⟩

lemma compl_adj_v2_S2 {u : Fin n} (hu : u ∈ pp.S2) : Gᶜ.Adj pp.v2 u :=
  (SimpleGraph.compl_adj _ _ _).mpr ⟨fun h => pp.v2_not_S2 (h ▸ hu),
    fun hadj => pp.hnc u ⟨pp.S2_adj hu, hadj⟩⟩

lemma compl_adj_v2_A {u : Fin n} (hu : u ∈ pp.A) : Gᶜ.Adj pp.v2 u :=
  (SimpleGraph.compl_adj _ _ _).mpr ⟨fun h => pp.v2_not_A (h ▸ hu),
    fun hadj => pp.hnc u ⟨((pp.hA u).mp hu).1, hadj⟩⟩

lemma compl_adj_v2_C {z : Fin n} (hz : z ∈ pp.C) : Gᶜ.Adj pp.v2 z :=
  (SimpleGraph.compl_adj _ _ _).mpr ⟨((pp.hC z).mp hz).2.1.symm, ((pp.hC z).mp hz).2.2.2⟩

lemma compl_adj_A_B {u w : Fin n} (hu : u ∈ pp.A) (hw : w ∈ pp.B) : Gᶜ.Adj u w :=
  (SimpleGraph.compl_adj _ _ _).mpr ⟨fun h => Finset.disjoint_left.mp pp.disj_A_B hu (h ▸ hw),
    pp.hAB u hu w hw⟩

-- Super-clean block-based lower bound for quad G x using sum_double_blk!
set_option maxHeartbeats 400000 in
lemma mu_lower_from_star [DecidableRel G.Adj] {x : Fin n → ℝ}
    (hx : 1 ≤ |x pp.v1 - x pp.v2|)
    (e0 : Fin n × Fin n) (he0 : e0 ∈ pp.P)
    (T : Finset (Fin n)) (hTA : T ⊆ pp.A) (hTadj : ∀ t ∈ T, G.Adj t e0.2) :
    ((pp.P.card : ℝ) - 1) / 3 + ((T.card : ℝ) + 1) / ((T.card : ℝ) + 3) ≤ quad G x := by
  classical
  have hsq : 1 ≤ (x pp.v1 - x pp.v2) ^ 2 := by
    have : (1 : ℝ) ^ 2 ≤ |x pp.v1 - x pp.v2| ^ 2 := by nlinarith
    rwa [one_pow, sq_abs] at this
  let F : Fin n → Fin n → ℝ := fun i j => if G.Adj i j then (x i - x j) ^ 2 else 0
  have hFnn : ∀ i j, 0 ≤ F i j := fun i j => by dsimp [F]; split_ifs <;> positivity
  have hFsym : ∀ i j, F i j = F j i := fun i j => by
    dsimp [F]; by_cases h : G.Adj i j
    · simp [h, h.symm]; ring
    · have h' : ¬ G.Adj j i := fun ha => h ha.symm
      simp [h, h']
  let Bsum (a b : Fin 7) : ℝ := ∑ i ∈ pp.blk a, ∑ j ∈ pp.blk b, F i j
  have hBnn : ∀ a b, 0 ≤ Bsum a b := fun a b =>
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => hFnn _ _))
  have hBsym : ∀ a b, Bsum a b = Bsum b a := fun a b => by
    dsimp [Bsum]; rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hFsym j i))
  -- From 2 * quad G x = ∑ a, ∑ b, Bsum a b, keep the 5 distinct unordered block pairs:
  -- (0, 3), (0, 4), (3, 2), (4, 2), (2, 1) and their swaps!
  have hkeep : Bsum 0 3 + Bsum 0 4 + Bsum 3 2 + Bsum 4 2 + Bsum 2 1 ≤ quad G x := by
    have h2 := two_mul_quad G x
    have hsum : 2 * quad G x = ∑ a : Fin 7, ∑ b : Fin 7, Bsum a b := by
      rw [h2]; exact pp.sum_double_blk F
    let keep : Finset (Fin 7 × Fin 7) :=
      Finset.univ.filter (fun p : Fin 7 × Fin 7 =>
        p = (0, 3) ∨ p = (3, 0) ∨ p = (0, 4) ∨ p = (4, 0) ∨
        p = (3, 2) ∨ p = (2, 3) ∨ p = (4, 2) ∨ p = (2, 4) ∨
        p = (2, 1) ∨ p = (1, 2))
    have hle : ∑ p ∈ keep, Bsum p.1 p.2 ≤ ∑ p : Fin 7 × Fin 7, Bsum p.1 p.2 :=
      Finset.sum_le_univ_sum_of_nonneg (fun p => hBnn p.1 p.2)
    rw [Fintype.sum_prod_type] at hle
    have hke : ∑ p ∈ keep, Bsum p.1 p.2 =
        2 * (Bsum 0 3 + Bsum 0 4 + Bsum 3 2 + Bsum 4 2 + Bsum 2 1) := by
      rw [Finset.sum_filter, Fintype.sum_prod_type]
      simp only [Fin.sum_univ_seven, Prod.mk.injEq, Fin.reduceEq, and_self, and_false, false_and,
        or_false, false_or, or_true, ite_true, ite_false, add_zero, zero_add]
      rw [hBsym 3 0, hBsym 4 0, hBsym 2 3, hBsym 2 4, hBsym 1 2]
      ring
    linarith
  -- Evaluate / lower-bound each of the 5 block sums
  have hB03 : Bsum 0 3 = ∑ e ∈ pp.P, (x pp.v1 - x e.1) ^ 2 := by
    dsimp [Bsum, blk]; rw [Finset.sum_singleton, pp.hS2]
    rw [Finset.sum_image (fun e1 h1 e2 h2 heq => by
      by_contra hne; exact (pp.hPdisj e1 h1 e2 h2 hne).1 heq)]
    exact Finset.sum_congr rfl (fun e he => by dsimp [F]; rw [if_pos (pp.hPedge e he).1])
  have hB21 : Bsum 2 1 = ∑ e ∈ pp.P, (x e.2 - x pp.v2) ^ 2 := by
    dsimp [Bsum, blk]; simp_rw [Finset.sum_singleton]; rw [pp.hS1]
    rw [Finset.sum_image (fun e1 h1 e2 h2 heq => by
      by_contra hne; exact (pp.hPdisj e1 h1 e2 h2 hne).2 heq)]
    exact Finset.sum_congr rfl (fun e he => by dsimp [F]; rw [if_pos (pp.hPedge e he).2.2])
  have hB32 : ∑ e ∈ pp.P, (x e.1 - x e.2) ^ 2 ≤ Bsum 3 2 := by
    dsimp [Bsum, blk]; rw [pp.hS2]
    rw [Finset.sum_image (fun e1 h1 e2 h2 heq => by
      by_contra hne; exact (pp.hPdisj e1 h1 e2 h2 hne).1 heq)]
    apply Finset.sum_le_sum; intro e he
    have he2 : e.2 ∈ pp.S1 := by rw [pp.hS1]; exact Finset.mem_image.mpr ⟨e, he, rfl⟩
    calc (x e.1 - x e.2) ^ 2 = F e.1 e.2 := by dsimp [F]; rw [if_pos (pp.hPedge e he).2.1]
      _ ≤ ∑ j ∈ pp.S1, F e.1 j := Finset.single_le_sum (fun j _ => hFnn e.1 j) he2
  have hB04 : ∑ t ∈ T, (x pp.v1 - x t) ^ 2 ≤ Bsum 0 4 := by
    dsimp [Bsum, blk]; rw [Finset.sum_singleton]
    calc ∑ t ∈ T, (x pp.v1 - x t) ^ 2
        = ∑ t ∈ T, F pp.v1 t := Finset.sum_congr rfl (fun t ht => by
            dsimp [F]; rw [if_pos ((pp.hA t).mp (hTA ht)).1])
      _ ≤ ∑ t ∈ pp.A, F pp.v1 t := Finset.sum_le_sum_of_subset_of_nonneg hTA (fun _ _ _ => hFnn _ _)
  have hB42 : ∑ t ∈ T, (x t - x e0.2) ^ 2 ≤ Bsum 4 2 := by
    dsimp [Bsum, blk]
    have he02 : e0.2 ∈ pp.S1 := by rw [pp.hS1]; exact Finset.mem_image.mpr ⟨e0, he0, rfl⟩
    calc ∑ t ∈ T, (x t - x e0.2) ^ 2
        = ∑ t ∈ T, F t e0.2 := Finset.sum_congr rfl (fun t ht => by
            dsimp [F]; rw [if_pos (hTadj t ht)])
      _ ≤ ∑ t ∈ T, ∑ j ∈ pp.S1, F t j :=
            Finset.sum_le_sum (fun t _ => Finset.single_le_sum (fun j _ => hFnn t j) he02)
      _ ≤ ∑ t ∈ pp.A, ∑ j ∈ pp.S1, F t j :=
            Finset.sum_le_sum_of_subset_of_nonneg hTA
              (fun _ _ _ => Finset.sum_nonneg (fun _ _ => hFnn _ _))
  -- Split the P sums at e0 into e0 + P.erase e0
  let P' := pp.P.erase e0
  have hsumP : ∑ e ∈ pp.P, ((x pp.v1 - x e.1) ^ 2 + (x e.1 - x e.2) ^ 2 + (x e.2 - x pp.v2) ^ 2) =
      ((x pp.v1 - x e0.1) ^ 2 + (x e0.1 - x e0.2) ^ 2 + (x e0.2 - x pp.v2) ^ 2) +
      ∑ e ∈ P', ((x pp.v1 - x e.1) ^ 2 + (x e.1 - x e.2) ^ 2 + (x e.2 - x pp.v2) ^ 2) :=
    (Finset.add_sum_erase pp.P _ he0).symm
  have hP'_lb : ((pp.P.card : ℝ) - 1) / 3 ≤
      ∑ e ∈ P', ((x pp.v1 - x e.1) ^ 2 + (x e.1 - x e.2) ^ 2 + (x e.2 - x pp.v2) ^ 2) := by
    have hterm : ∀ e ∈ P', (1 / 3 : ℝ) ≤
        (x pp.v1 - x e.1) ^ 2 + (x e.1 - x e.2) ^ 2 + (x e.2 - x pp.v2) ^ 2 := fun e _ => by
      nlinarith [sq_nonneg ((x pp.v1 - x e.1) - (x e.1 - x e.2)),
        sq_nonneg ((x e.1 - x e.2) - (x e.2 - x pp.v2)),
        sq_nonneg ((x pp.v1 - x e.1) - (x e.2 - x pp.v2))]
    have hP'c : (P'.card : ℝ) = (pp.P.card : ℝ) - 1 := by
      have : (P'.card : ℝ) + 1 = (pp.P.card : ℝ) := by exact_mod_cast Finset.card_erase_add_one he0
      linarith
    calc ((pp.P.card : ℝ) - 1) / 3 = (P'.card : ℝ) * (1 / 3) := by rw [hP'c]; ring
      _ = ∑ _e ∈ P', (1 / 3 : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum hterm
  have hstar_lb : ((T.card : ℝ) + 1) / ((T.card : ℝ) + 3) ≤
      (x pp.v1 - x e0.1) ^ 2 + (x e0.1 - x e0.2) ^ 2 +
      (∑ t ∈ T, ((x pp.v1 - x t) ^ 2 + (x t - x e0.2) ^ 2)) + (x e0.2 - x pp.v2) ^ 2 := by
    have h1 : (1 / 2 : ℝ) * (x pp.v1 - x e0.2) ^ 2 ≤ (x pp.v1 - x e0.1) ^ 2 + (x e0.1 - x e0.2) ^ 2 := by
      nlinarith [sq_nonneg (x pp.v1 + x e0.2 - 2 * x e0.1)]
    have h2 : ((T.card : ℝ) / 2) * (x pp.v1 - x e0.2) ^ 2 ≤
        ∑ t ∈ T, ((x pp.v1 - x t) ^ 2 + (x t - x e0.2) ^ 2) := by
      calc ((T.card : ℝ) / 2) * (x pp.v1 - x e0.2) ^ 2
          = ∑ _t ∈ T, (1 / 2 : ℝ) * (x pp.v1 - x e0.2) ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]; ring
        _ ≤ _ := Finset.sum_le_sum (fun t _ => by nlinarith [sq_nonneg (x pp.v1 + x e0.2 - 2 * x t)])
    have hden : (0 : ℝ) < (T.card : ℝ) + 3 := by positivity
    have hser : ((T.card : ℝ) + 1) / ((T.card : ℝ) + 3) * (x pp.v1 - x pp.v2) ^ 2 ≤
        (((T.card : ℝ) + 1) / 2) * (x pp.v1 - x e0.2) ^ 2 + (x e0.2 - x pp.v2) ^ 2 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hden]
      have hid : (((T.card : ℝ) + 1) / 2 * (x pp.v1 - x e0.2) ^ 2 + (x e0.2 - x pp.v2) ^ 2) *
          ((T.card : ℝ) + 3) - ((T.card : ℝ) + 1) * (x pp.v1 - x pp.v2) ^ 2 =
          (1 / 2 : ℝ) * (((T.card : ℝ) + 1) * (x pp.v1 - x e0.2) - 2 * (x e0.2 - x pp.v2)) ^ 2 := by
        ring
      nlinarith [sq_nonneg (((T.card : ℝ) + 1) * (x pp.v1 - x e0.2) - 2 * (x e0.2 - x pp.v2))]
    have hTnn : (0 : ℝ) ≤ (T.card : ℝ) := Nat.cast_nonneg T.card
    have hpos : (0 : ℝ) ≤ ((T.card : ℝ) + 1) / ((T.card : ℝ) + 3) :=
      div_nonneg (by linarith) (by linarith)
    nlinarith
  have hsumP_dist : ∑ e ∈ pp.P, ((x pp.v1 - x e.1) ^ 2 + (x e.1 - x e.2) ^ 2 + (x e.2 - x pp.v2) ^ 2) =
      (∑ e ∈ pp.P, (x pp.v1 - x e.1) ^ 2) + (∑ e ∈ pp.P, (x e.1 - x e.2) ^ 2) +
      (∑ e ∈ pp.P, (x e.2 - x pp.v2) ^ 2) := by
    simp only [Finset.sum_add_distrib]
  have hT_dist : ∑ t ∈ T, ((x pp.v1 - x t) ^ 2 + (x t - x e0.2) ^ 2) =
      (∑ t ∈ T, (x pp.v1 - x t) ^ 2) + (∑ t ∈ T, (x t - x e0.2) ^ 2) :=
    Finset.sum_add_distrib
  linarith

-- Clean block-based lower bound on quad Gᶜ y for BOTH general bound and G2/G3!
lemma compl_block_sum_le [DecidableRel G.Adj] [DecidableRel Gᶜ.Adj] (y : Fin n → ℝ) :
    (y pp.v1 - y pp.v2) ^ 2 +
    (∑ w ∈ pp.S1, (y pp.v1 - y w) ^ 2) +
    (∑ w ∈ pp.B, (y pp.v1 - y w) ^ 2) +
    (∑ z ∈ pp.C, (y pp.v1 - y z) ^ 2) +
    (∑ u ∈ pp.S2, (y pp.v2 - y u) ^ 2) +
    (∑ u ∈ pp.A, (y pp.v2 - y u) ^ 2) +
    (∑ z ∈ pp.C, (y pp.v2 - y z) ^ 2) +
    (∑ u ∈ pp.A, ∑ w ∈ pp.B, (y u - y w) ^ 2) +
    (∑ w ∈ pp.S1, ∑ u ∈ pp.A.filter (fun u => ¬ G.Adj w u), (y w - y u) ^ 2) +
    (∑ u ∈ pp.S2, ∑ w ∈ pp.B.filter (fun w => ¬ G.Adj u w), (y u - y w) ^ 2) ≤ quad Gᶜ y := by
  classical
  let F : Fin n → Fin n → ℝ := fun i j => if Gᶜ.Adj i j then (y i - y j) ^ 2 else 0
  have hFnn : ∀ i j, 0 ≤ F i j := fun i j => by dsimp [F]; split_ifs <;> positivity
  have hFsym : ∀ i j, F i j = F j i := fun i j => by
    dsimp [F]; by_cases h : Gᶜ.Adj i j
    · simp [h, h.symm]; ring
    · have h' : ¬ Gᶜ.Adj j i := fun ha => h ha.symm
      simp [h, h']
  let Bsum (a b : Fin 7) : ℝ := ∑ i ∈ pp.blk a, ∑ j ∈ pp.blk b, F i j
  have hBnn : ∀ a b, 0 ≤ Bsum a b := fun a b =>
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => hFnn _ _))
  have hBsym : ∀ a b, Bsum a b = Bsum b a := fun a b => by
    dsimp [Bsum]; rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hFsym j i))
  -- 10 distinct unordered pairs of Fin 7:
  -- (0,1), (0,2), (0,5), (0,6), (1,3), (1,4), (1,6), (4,5), (2,4), (3,5)
  let keep : Finset (Fin 7 × Fin 7) :=
    Finset.univ.filter (fun p : Fin 7 × Fin 7 =>
      p = (0, 1) ∨ p = (1, 0) ∨ p = (0, 2) ∨ p = (2, 0) ∨
      p = (0, 5) ∨ p = (5, 0) ∨ p = (0, 6) ∨ p = (6, 0) ∨
      p = (1, 3) ∨ p = (3, 1) ∨ p = (1, 4) ∨ p = (4, 1) ∨
      p = (1, 6) ∨ p = (6, 1) ∨ p = (4, 5) ∨ p = (5, 4) ∨
      p = (2, 4) ∨ p = (4, 2) ∨ p = (3, 5) ∨ p = (5, 3))
  have hsum_all : 2 * quad Gᶜ y = ∑ p : Fin 7 × Fin 7, Bsum p.1 p.2 := by
    rw [two_mul_quad, pp.sum_double_blk F, Fintype.sum_prod_type]
  have hle : ∑ p ∈ keep, Bsum p.1 p.2 ≤ 2 * quad Gᶜ y := by
    rw [hsum_all]
    exact Finset.sum_le_univ_sum_of_nonneg (fun p => hBnn p.1 p.2)
  -- Expand ∑ p ∈ keep using explicit Fin.sum_univ_seven × Fin.sum_univ_seven via filter
  have hkeep_eq : ∑ p ∈ keep, Bsum p.1 p.2 =
      2 * (Bsum 0 1 + Bsum 0 2 + Bsum 0 5 + Bsum 0 6 +
           Bsum 1 3 + Bsum 1 4 + Bsum 1 6 + Bsum 4 5 + Bsum 2 4 + Bsum 3 5) := by
    rw [Finset.sum_filter, Fintype.sum_prod_type]
    simp only [Fin.sum_univ_seven, Prod.mk.injEq, Fin.reduceEq, and_self, and_false, false_and,
      or_false, false_or, or_true, ite_true, ite_false, add_zero, zero_add]
    rw [hBsym 1 0, hBsym 2 0, hBsym 5 0, hBsym 6 0, hBsym 3 1, hBsym 4 1,
      hBsym 6 1, hBsym 5 4, hBsym 4 2, hBsym 5 3]
    ring
  -- Evaluate each of the 10 Bsum terms
  have h01 : Bsum 0 1 = (y pp.v1 - y pp.v2) ^ 2 := by
    dsimp [Bsum, blk, F]; rw [Finset.sum_singleton, Finset.sum_singleton, if_pos pp.compl_adj_v1_v2]
  have h02 : Bsum 0 2 = ∑ w ∈ pp.S1, (y pp.v1 - y w) ^ 2 := by
    dsimp [Bsum, blk, F]; rw [Finset.sum_singleton]
    exact Finset.sum_congr rfl (fun w hw => if_pos (pp.compl_adj_v1_S1 hw))
  have h05 : Bsum 0 5 = ∑ w ∈ pp.B, (y pp.v1 - y w) ^ 2 := by
    dsimp [Bsum, blk, F]; rw [Finset.sum_singleton]
    exact Finset.sum_congr rfl (fun w hw => if_pos (pp.compl_adj_v1_B hw))
  have h06 : Bsum 0 6 = ∑ z ∈ pp.C, (y pp.v1 - y z) ^ 2 := by
    dsimp [Bsum, blk, F]; rw [Finset.sum_singleton]
    exact Finset.sum_congr rfl (fun z hz => if_pos (pp.compl_adj_v1_C hz))
  have h13 : Bsum 1 3 = ∑ u ∈ pp.S2, (y pp.v2 - y u) ^ 2 := by
    dsimp [Bsum, blk, F]; rw [Finset.sum_singleton]
    exact Finset.sum_congr rfl (fun u hu => if_pos (pp.compl_adj_v2_S2 hu))
  have h14 : Bsum 1 4 = ∑ u ∈ pp.A, (y pp.v2 - y u) ^ 2 := by
    dsimp [Bsum, blk, F]; rw [Finset.sum_singleton]
    exact Finset.sum_congr rfl (fun u hu => if_pos (pp.compl_adj_v2_A hu))
  have h16 : Bsum 1 6 = ∑ z ∈ pp.C, (y pp.v2 - y z) ^ 2 := by
    dsimp [Bsum, blk, F]; rw [Finset.sum_singleton]
    exact Finset.sum_congr rfl (fun z hz => if_pos (pp.compl_adj_v2_C hz))
  have h45 : Bsum 4 5 = ∑ u ∈ pp.A, ∑ w ∈ pp.B, (y u - y w) ^ 2 := by
    dsimp [Bsum, blk, F]
    exact Finset.sum_congr rfl (fun u hu => Finset.sum_congr rfl (fun w hw =>
      if_pos (pp.compl_adj_A_B hu hw)))
  have h24 : Bsum 2 4 = ∑ w ∈ pp.S1, ∑ u ∈ pp.A.filter (fun u => ¬ G.Adj w u), (y w - y u) ^ 2 := by
    dsimp [Bsum, blk, F]
    apply Finset.sum_congr rfl; intro w hw
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl; intro u hu
    have hne : w ≠ u := fun h => Finset.disjoint_left.mp pp.disj_S1_A hw (h ▸ hu)
    by_cases hadj : G.Adj w u
    · simp [SimpleGraph.compl_adj, hadj]
    · simp [SimpleGraph.compl_adj, hne, hadj]
  have h35 : Bsum 3 5 = ∑ u ∈ pp.S2, ∑ w ∈ pp.B.filter (fun w => ¬ G.Adj u w), (y u - y w) ^ 2 := by
    dsimp [Bsum, blk, F]
    apply Finset.sum_congr rfl; intro u hu
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl; intro w hw
    have hne : u ≠ w := fun h => Finset.disjoint_left.mp pp.disj_S2_B hu (h ▸ hw)
    by_cases hadj : G.Adj u w
    · simp [SimpleGraph.compl_adj, hadj]
    · simp [SimpleGraph.compl_adj, hne, hadj]
  rw [hkeep_eq, h01, h02, h05, h06, h13, h14, h16, h45, h24, h35] at hle
  linarith

set_option maxHeartbeats 600000 in
lemma mu_compl_general_bound [DecidableRel G.Adj] [DecidableRel Gᶜ.Adj]
    (hab : pp.A.card ≤ pp.B.card) (l : ℕ)
    (hl1 : ∀ w ∈ pp.S1, (pp.A.filter (G.Adj w)).card ≤ l)
    (hl2 : ∀ u ∈ pp.S2, (pp.B.filter (G.Adj u)).card ≤ l)
    {y : Fin n → ℝ} (hy0 : ∑ i, y i = 0) :
    (n : ℝ) * (∑ i, y i ^ 2) ≤
      ((n : ℝ) + 2 + 3 * (pp.P.card : ℝ) ^ 2 + 6 * (pp.P.card : ℝ) * (l : ℝ)) * quad Gᶜ y := by
  classical
  let s : ℕ := pp.P.card
  let a : ℕ := pp.A.card
  let b : ℕ := pp.B.card
  let c : ℕ := pp.C.card
  have hn_eq : n = a + b + c + 2 * s + 2 := pp.card_eq
  have hs1 : 1 ≤ s := pp.hPne.card_pos
  have hS1c : pp.S1.card = s := pp.card_S1
  have hS2c : pp.S2.card = s := pp.card_S2
  -- Define U1, U2, U3 as unions of blk k
  let U1 : Finset (Fin n) := ({0, 1, 2, 5, 6} : Finset (Fin 7)).biUnion pp.blk
  let U2 : Finset (Fin n) := ({1, 3, 4, 6} : Finset (Fin 7)).biUnion pp.blk
  let U3 : Finset (Fin n) := ({0, 1, 3, 4} : Finset (Fin 7)).biUnion pp.blk
  have hpw : ∀ S : Finset (Fin 7), (S : Set (Fin 7)).PairwiseDisjoint pp.blk :=
    fun _ _ _ _ _ hab => pp.blk_disjoint hab
  -- Shorthand sums of edges in Gᶜ
  let E12 : ℝ := (y pp.v1 - y pp.v2) ^ 2
  let E1S1 : ℝ := ∑ w ∈ pp.S1, (y pp.v1 - y w) ^ 2
  let E1B : ℝ := ∑ w ∈ pp.B, (y pp.v1 - y w) ^ 2
  let E1C : ℝ := ∑ z ∈ pp.C, (y pp.v1 - y z) ^ 2
  let E2S2 : ℝ := ∑ u ∈ pp.S2, (y pp.v2 - y u) ^ 2
  let E2A : ℝ := ∑ u ∈ pp.A, (y pp.v2 - y u) ^ 2
  let E2C : ℝ := ∑ z ∈ pp.C, (y pp.v2 - y z) ^ 2
  let EAB : ℝ := ∑ u ∈ pp.A, ∑ w ∈ pp.B, (y u - y w) ^ 2
  let ES1A_c : ℝ := ∑ w ∈ pp.S1, ∑ u ∈ pp.A.filter (fun u => ¬ G.Adj w u), (y w - y u) ^ 2
  let ES2B_c : ℝ := ∑ u ∈ pp.S2, ∑ w ∈ pp.B.filter (fun w => ¬ G.Adj u w), (y u - y w) ^ 2
  -- Helper: compute card & sum of biUnion over a subset of Fin 7
  have hU1_card : U1.card = b + c + s + 2 := by
    dsimp [U1]; rw [Finset.card_biUnion (hpw _)]
    have : ∑ k ∈ ({0, 1, 2, 5, 6} : Finset (Fin 7)), (pp.blk k).card =
        (pp.blk 0).card + (pp.blk 1).card + (pp.blk 2).card + (pp.blk 5).card + (pp.blk 6).card := by
      simp [Finset.sum_insert, add_assoc]
    rw [this]; simp only [blk, Finset.card_singleton, hS1c]; omega
  have hU2_card : U2.card = a + c + s + 1 := by
    dsimp [U2]; rw [Finset.card_biUnion (hpw _)]
    have : ∑ k ∈ ({1, 3, 4, 6} : Finset (Fin 7)), (pp.blk k).card =
        (pp.blk 1).card + (pp.blk 3).card + (pp.blk 4).card + (pp.blk 6).card := by
      simp [Finset.sum_insert, add_assoc]
    rw [this]; simp only [blk, Finset.card_singleton, hS2c]; omega
  have hU3_card : U3.card = a + s + 2 := by
    dsimp [U3]; rw [Finset.card_biUnion (hpw _)]
    have : ∑ k ∈ ({0, 1, 3, 4} : Finset (Fin 7)), (pp.blk k).card =
        (pp.blk 0).card + (pp.blk 1).card + (pp.blk 3).card + (pp.blk 4).card := by
      simp [Finset.sum_insert, add_assoc]
    rw [this]; simp only [blk, Finset.card_singleton, hS2c]; omega
  have hS_U1 : ∑ i ∈ U1, ∑ j ∈ U1, (y i - y j) ^ 2 ≤
      2 * ((b : ℝ) + c + s + 2) * (E12 + E1B + E1C + E1S1) := by
    have hmem : pp.v1 ∈ U1 := Finset.mem_biUnion.mpr ⟨0, by decide, by simp [blk]⟩
    have hst := star_sum_bound U1 pp.v1 hmem y
    have hsum : ∑ u ∈ U1.erase pp.v1, (y pp.v1 - y u) ^ 2 = E12 + E1S1 + E1B + E1C := by
      have hfull : ∑ u ∈ U1, (y pp.v1 - y u) ^ 2 = E12 + E1S1 + E1B + E1C := by
        dsimp [U1]; rw [Finset.sum_biUnion (hpw _)]
        simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Fin.reduceEq,
          or_self, not_false_eq_true, Finset.sum_singleton, blk, sub_self, zero_pow (by decide : 2 ≠ 0),
          zero_add]
        dsimp [E12, E1S1, E1B, E1C]; ring
      rw [← Finset.add_sum_erase U1 (fun u => (y pp.v1 - y u) ^ 2) hmem] at hfull
      have h0 : (y pp.v1 - y pp.v1) ^ 2 = 0 := by ring
      linarith
    rw [hU1_card, hsum] at hst; push_cast at hst; linarith
  have hS_U2 : ∑ i ∈ U2, ∑ j ∈ U2, (y i - y j) ^ 2 ≤
      2 * ((a : ℝ) + c + s + 1) * (E2A + E2C + E2S2) := by
    have hmem : pp.v2 ∈ U2 := Finset.mem_biUnion.mpr ⟨1, by decide, by simp [blk]⟩
    have hst := star_sum_bound U2 pp.v2 hmem y
    have hsum : ∑ u ∈ U2.erase pp.v2, (y pp.v2 - y u) ^ 2 = E2S2 + E2A + E2C := by
      have hfull : ∑ u ∈ U2, (y pp.v2 - y u) ^ 2 = E2S2 + E2A + E2C := by
        dsimp [U2]; rw [Finset.sum_biUnion (hpw _)]
        simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Fin.reduceEq,
          or_self, not_false_eq_true, Finset.sum_singleton, blk, sub_self, zero_pow (by decide : 2 ≠ 0),
          zero_add]
        dsimp [E2S2, E2A, E2C]; ring
      rw [← Finset.add_sum_erase U2 (fun u => (y pp.v2 - y u) ^ 2) hmem] at hfull
      have h0 : (y pp.v2 - y pp.v2) ^ 2 = 0 := by ring
      linarith
    rw [hU2_card, hsum] at hst; push_cast at hst; linarith
  have hS_U3 : ∑ i ∈ U3, ∑ j ∈ U3, (y i - y j) ^ 2 ≤
      2 * ((a : ℝ) + s + 2) * (E12 + E2A + E2S2) := by
    have hmem : pp.v2 ∈ U3 := Finset.mem_biUnion.mpr ⟨1, by decide, by simp [blk]⟩
    have hst := star_sum_bound U3 pp.v2 hmem y
    have hsum : ∑ u ∈ U3.erase pp.v2, (y pp.v2 - y u) ^ 2 = E12 + E2S2 + E2A := by
      have hfull : ∑ u ∈ U3, (y pp.v2 - y u) ^ 2 = E12 + E2S2 + E2A := by
        dsimp [U3]; rw [Finset.sum_biUnion (hpw _)]
        simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Fin.reduceEq,
          or_self, not_false_eq_true, Finset.sum_singleton, blk, sub_self, zero_pow (by decide : 2 ≠ 0),
          zero_add]
        dsimp [E12, E2S2, E2A]; ring
      rw [← Finset.add_sum_erase U3 (fun u => (y pp.v2 - y u) ^ 2) hmem] at hfull
      have h0 : (y pp.v2 - y pp.v2) ^ 2 = 0 := by ring
      linarith
    rw [hU3_card, hsum] at hst; push_cast at hst; linarith
  -- Expand U1², U2², U3² via blk
  let D (i j : Fin 7) : ℝ := ∑ x ∈ pp.blk i, ∑ z ∈ pp.blk j, (y x - y z) ^ 2
  have hDnn : ∀ i j, 0 ≤ D i j := fun i j =>
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hDsym : ∀ i j, D i j = D j i := fun i j => by
    dsimp [D]; rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun z _ => by ring))
  have hU_sq : ∀ S : Finset (Fin 7),
      ∑ i ∈ S.biUnion pp.blk, ∑ j ∈ S.biUnion pp.blk, (y i - y j) ^ 2 =
      ∑ a ∈ S, ∑ b ∈ S, D a b := by
    intro S
    rw [Finset.sum_biUnion (hpw S)]
    apply Finset.sum_congr rfl; intro a _
    simp_rw [Finset.sum_biUnion (hpw S)]
    exact Finset.sum_comm
  have hcover_all : ∑ i : Fin n, ∑ j : Fin n, (y i - y j) ^ 2 ≤
      (∑ i ∈ U1, ∑ j ∈ U1, (y i - y j) ^ 2) +
      (∑ i ∈ U2, ∑ j ∈ U2, (y i - y j) ^ 2) +
      (∑ i ∈ U3, ∑ j ∈ U3, (y i - y j) ^ 2) +
      2 * D 2 3 + 2 * D 2 4 + 2 * D 3 5 + 2 * D 4 5 := by
    rw [pp.sum_double_blk (fun i j => (y i - y j) ^ 2), hU_sq, hU_sq, hU_sq]
    have hcov7 : ∀ a b : Fin 7,
        (a ∈ ({0, 1, 2, 5, 6} : Finset (Fin 7)) ∧ b ∈ ({0, 1, 2, 5, 6} : Finset (Fin 7))) ∨
        (a ∈ ({1, 3, 4, 6} : Finset (Fin 7)) ∧ b ∈ ({1, 3, 4, 6} : Finset (Fin 7))) ∨
        (a ∈ ({0, 1, 3, 4} : Finset (Fin 7)) ∧ b ∈ ({0, 1, 3, 4} : Finset (Fin 7))) ∨
        ((a = 2 ∧ b = 3) ∨ (a = 3 ∧ b = 2) ∨ (a = 2 ∧ b = 4) ∨ (a = 4 ∧ b = 2) ∨
         (a = 3 ∧ b = 5) ∨ (a = 5 ∧ b = 3) ∨ (a = 4 ∧ b = 5) ∨ (a = 5 ∧ b = 4)) := by decide
    have hpt : ∀ a b : Fin 7, D a b ≤
        (if a ∈ ({0, 1, 2, 5, 6} : Finset (Fin 7)) ∧ b ∈ ({0, 1, 2, 5, 6} : Finset (Fin 7)) then D a b else 0) +
        (if a ∈ ({1, 3, 4, 6} : Finset (Fin 7)) ∧ b ∈ ({1, 3, 4, 6} : Finset (Fin 7)) then D a b else 0) +
        (if a ∈ ({0, 1, 3, 4} : Finset (Fin 7)) ∧ b ∈ ({0, 1, 3, 4} : Finset (Fin 7)) then D a b else 0) +
        (if (a = 2 ∧ b = 3) ∨ (a = 3 ∧ b = 2) ∨ (a = 2 ∧ b = 4) ∨ (a = 4 ∧ b = 2) ∨
            (a = 3 ∧ b = 5) ∨ (a = 5 ∧ b = 3) ∨ (a = 4 ∧ b = 5) ∨ (a = 5 ∧ b = 4) then D a b else 0) := by
      intro a b
      have hd := hDnn a b
      have hite : ∀ (P : Prop) [Decidable P], 0 ≤ if P then D a b else 0 := fun P _ => by
        split_ifs <;> linarith
      rcases hcov7 a b with h | h | h | h
      · rw [if_pos h]; linarith [hite (a ∈ ({1, 3, 4, 6} : Finset (Fin 7)) ∧ b ∈ ({1, 3, 4, 6} : Finset (Fin 7))),
          hite (a ∈ ({0, 1, 3, 4} : Finset (Fin 7)) ∧ b ∈ ({0, 1, 3, 4} : Finset (Fin 7))),
          hite ((a = 2 ∧ b = 3) ∨ (a = 3 ∧ b = 2) ∨ (a = 2 ∧ b = 4) ∨ (a = 4 ∧ b = 2) ∨
                (a = 3 ∧ b = 5) ∨ (a = 5 ∧ b = 3) ∨ (a = 4 ∧ b = 5) ∨ (a = 5 ∧ b = 4))]
      · rw [if_pos h]; linarith [hite (a ∈ ({0, 1, 2, 5, 6} : Finset (Fin 7)) ∧ b ∈ ({0, 1, 2, 5, 6} : Finset (Fin 7))),
          hite (a ∈ ({0, 1, 3, 4} : Finset (Fin 7)) ∧ b ∈ ({0, 1, 3, 4} : Finset (Fin 7))),
          hite ((a = 2 ∧ b = 3) ∨ (a = 3 ∧ b = 2) ∨ (a = 2 ∧ b = 4) ∨ (a = 4 ∧ b = 2) ∨
                (a = 3 ∧ b = 5) ∨ (a = 5 ∧ b = 3) ∨ (a = 4 ∧ b = 5) ∨ (a = 5 ∧ b = 4))]
      · rw [if_pos h]; linarith [hite (a ∈ ({0, 1, 2, 5, 6} : Finset (Fin 7)) ∧ b ∈ ({0, 1, 2, 5, 6} : Finset (Fin 7))),
          hite (a ∈ ({1, 3, 4, 6} : Finset (Fin 7)) ∧ b ∈ ({1, 3, 4, 6} : Finset (Fin 7))),
          hite ((a = 2 ∧ b = 3) ∨ (a = 3 ∧ b = 2) ∨ (a = 2 ∧ b = 4) ∨ (a = 4 ∧ b = 2) ∨
                (a = 3 ∧ b = 5) ∨ (a = 5 ∧ b = 3) ∨ (a = 4 ∧ b = 5) ∨ (a = 5 ∧ b = 4))]
      · rw [if_pos h]; linarith [hite (a ∈ ({0, 1, 2, 5, 6} : Finset (Fin 7)) ∧ b ∈ ({0, 1, 2, 5, 6} : Finset (Fin 7))),
          hite (a ∈ ({1, 3, 4, 6} : Finset (Fin 7)) ∧ b ∈ ({1, 3, 4, 6} : Finset (Fin 7))),
          hite (a ∈ ({0, 1, 3, 4} : Finset (Fin 7)) ∧ b ∈ ({0, 1, 3, 4} : Finset (Fin 7)))]
    have hsum := Finset.sum_le_sum (fun a (_ : a ∈ Finset.univ) =>
      Finset.sum_le_sum (fun b (_ : b ∈ Finset.univ) => hpt a b))
    have hbox : ∀ S : Finset (Fin 7),
        ∑ a : Fin 7, ∑ b : Fin 7, (if a ∈ S ∧ b ∈ S then D a b else 0) = ∑ a ∈ S, ∑ b ∈ S, D a b := by
      intro S
      have h1 : ∀ a : Fin 7, ∑ b : Fin 7, (if a ∈ S ∧ b ∈ S then D a b else 0) =
          if a ∈ S then ∑ b ∈ S, D a b else 0 := by
        intro a
        by_cases ha : a ∈ S
        · simp only [ha, true_and, Finset.sum_ite_mem, Finset.univ_inter, ite_true]
        · simp [ha]
      simp_rw [h1, Finset.sum_ite_mem, Finset.univ_inter]
    have hrem : ∑ a : Fin 7, ∑ b : Fin 7,
        (if (a = 2 ∧ b = 3) ∨ (a = 3 ∧ b = 2) ∨ (a = 2 ∧ b = 4) ∨ (a = 4 ∧ b = 2) ∨
            (a = 3 ∧ b = 5) ∨ (a = 5 ∧ b = 3) ∨ (a = 4 ∧ b = 5) ∨ (a = 5 ∧ b = 4) then D a b else 0) =
        2 * D 2 3 + 2 * D 2 4 + 2 * D 3 5 + 2 * D 4 5 := by
      simp only [Fin.sum_univ_seven, Fin.reduceEq, and_self, and_false, false_and,
        or_false, false_or, or_true, ite_true, ite_false, add_zero, zero_add]
      rw [hDsym 3 2, hDsym 4 2, hDsym 5 3, hDsym 5 4]; ring
    simp_rw [Finset.sum_add_distrib, hbox, hrem] at hsum
    linarith
  -- Length-3 path bounds for D 2 3, D 2 4, D 3 5
  have h3sq : ∀ a' b' c' : ℝ, (a' + b' + c') ^ 2 ≤ 3 * (a' ^ 2 + b' ^ 2 + c' ^ 2) :=
    fun a' b' c' => by nlinarith [sq_nonneg (a' - b'), sq_nonneg (b' - c'), sq_nonneg (a' - c')]
  have hS1S2 : D 2 3 ≤ 3 * (s : ℝ) * E1S1 + 3 * (s : ℝ) * E2S2 + 3 * (s : ℝ) ^ 2 * E12 := by
    dsimp [D, blk]
    have hpt : ∀ w ∈ pp.S1, ∀ u ∈ pp.S2, (y w - y u) ^ 2 ≤
        3 * ((y pp.v1 - y w) ^ 2 + (y pp.v1 - y pp.v2) ^ 2 + (y pp.v2 - y u) ^ 2) := by
      intro w _ u _
      have := h3sq (y w - y pp.v1) (y pp.v1 - y pp.v2) (y pp.v2 - y u)
      have h1 : (y w - y pp.v1) + (y pp.v1 - y pp.v2) + (y pp.v2 - y u) = y w - y u := by ring
      have h2 : (y w - y pp.v1) ^ 2 = (y pp.v1 - y w) ^ 2 := by ring
      rw [h1, h2] at this; exact this
    calc ∑ w ∈ pp.S1, ∑ u ∈ pp.S2, (y w - y u) ^ 2
        ≤ ∑ w ∈ pp.S1, ∑ u ∈ pp.S2,
            3 * ((y pp.v1 - y w) ^ 2 + (y pp.v1 - y pp.v2) ^ 2 + (y pp.v2 - y u) ^ 2) :=
          Finset.sum_le_sum (fun w hw => Finset.sum_le_sum (fun u hu => hpt w hw u hu))
      _ = 3 * (s : ℝ) * E1S1 + 3 * (s : ℝ) * E2S2 + 3 * (s : ℝ) ^ 2 * E12 := by
          simp_rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, hS1c, hS2c,
            nsmul_eq_mul, ← Finset.mul_sum]
          dsimp [E1S1, E2S2, E12]; ring
  have hS1A : D 2 4 ≤ 3 * (l : ℝ) * E1S1 + 3 * (s : ℝ) * (l : ℝ) * E12 +
      3 * (s : ℝ) * (l : ℝ) * E2A + ES1A_c := by
    have hsp : D 2 4 = (∑ w ∈ pp.S1, ∑ u ∈ pp.A.filter (G.Adj w), (y w - y u) ^ 2) + ES1A_c := by
      dsimp [D, blk, ES1A_c]; rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun w _ => (Finset.sum_filter_add_sum_filter_not pp.A (G.Adj w) _).symm)
    rw [hsp]
    have hg : ∑ w ∈ pp.S1, ∑ u ∈ pp.A.filter (G.Adj w), (y w - y u) ^ 2 ≤
        3 * (l : ℝ) * E1S1 + 3 * (s : ℝ) * (l : ℝ) * E12 + 3 * (s : ℝ) * (l : ℝ) * E2A := by
      by_cases hl0 : l = 0
      · have hempty : ∀ w ∈ pp.S1, pp.A.filter (G.Adj w) = ∅ := fun w hw =>
          Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero (hl0 ▸ hl1 w hw))
        rw [Finset.sum_eq_zero (fun w hw => by rw [hempty w hw, Finset.sum_empty]), hl0]; norm_num
      · have hlpos : (1 : ℝ) ≤ (l : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hl0
        have hle1 : ∑ w ∈ pp.S1, ∑ u ∈ pp.A.filter (G.Adj w), (y w - y u) ^ 2 ≤
            3 * (∑ w ∈ pp.S1, ((pp.A.filter (G.Adj w)).card : ℝ) * (y pp.v1 - y w) ^ 2) +
            3 * (∑ w ∈ pp.S1, ((pp.A.filter (G.Adj w)).card : ℝ)) * E12 +
            3 * (∑ w ∈ pp.S1, ∑ u ∈ pp.A.filter (G.Adj w), (y pp.v2 - y u) ^ 2) := by
          have hpt : ∀ w ∈ pp.S1, ∀ u ∈ pp.A.filter (G.Adj w), (y w - y u) ^ 2 ≤
              3 * ((y pp.v1 - y w) ^ 2 + (y pp.v1 - y pp.v2) ^ 2 + (y pp.v2 - y u) ^ 2) := by
            intro w _ u _
            have := h3sq (y w - y pp.v1) (y pp.v1 - y pp.v2) (y pp.v2 - y u)
            have h1 : (y w - y pp.v1) + (y pp.v1 - y pp.v2) + (y pp.v2 - y u) = y w - y u := by ring
            have h2 : (y w - y pp.v1) ^ 2 = (y pp.v1 - y w) ^ 2 := by ring
            rw [h1, h2] at this; exact this
          calc _ ≤ ∑ w ∈ pp.S1, ∑ u ∈ pp.A.filter (G.Adj w),
                3 * ((y pp.v1 - y w) ^ 2 + (y pp.v1 - y pp.v2) ^ 2 + (y pp.v2 - y u) ^ 2) :=
                Finset.sum_le_sum (fun w hw => Finset.sum_le_sum (fun u hu => hpt w hw u hu))
            _ = _ := by
                simp_rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
                  ← Finset.sum_mul]
                dsimp [E12]; ring
        have hb1 : ∑ w ∈ pp.S1, ((pp.A.filter (G.Adj w)).card : ℝ) * (y pp.v1 - y w) ^ 2 ≤ (l : ℝ) * E1S1 := by
          rw [Finset.mul_sum]
          exact Finset.sum_le_sum (fun w hw => mul_le_mul_of_nonneg_right (by exact_mod_cast hl1 w hw) (sq_nonneg _))
        have hb2 : ∑ w ∈ pp.S1, ((pp.A.filter (G.Adj w)).card : ℝ) ≤ (s : ℝ) * (l : ℝ) := by
          calc _ ≤ ∑ _w ∈ pp.S1, (l : ℝ) := Finset.sum_le_sum (fun w hw => by exact_mod_cast hl1 w hw)
            _ = (s : ℝ) * (l : ℝ) := by rw [Finset.sum_const, hS1c, nsmul_eq_mul]
        have hb3 : ∑ w ∈ pp.S1, ∑ u ∈ pp.A.filter (G.Adj w), (y pp.v2 - y u) ^ 2 ≤ (s : ℝ) * E2A := by
          calc _ ≤ ∑ _w ∈ pp.S1, E2A := Finset.sum_le_sum (fun w _ =>
                Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => sq_nonneg _))
            _ = (s : ℝ) * E2A := by rw [Finset.sum_const, hS1c, nsmul_eq_mul]
        have hE2Ann : 0 ≤ E2A := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
        have hE12nn : 0 ≤ E12 := sq_nonneg _
        have hsnn : (0 : ℝ) ≤ (s : ℝ) := Nat.cast_nonneg s
        have h3_sE2A : (s : ℝ) * E2A ≤ (s : ℝ) * (l : ℝ) * E2A :=
          mul_le_mul_of_nonneg_right (by nlinarith) hE2Ann
        have h3_E12 : (∑ w ∈ pp.S1, ((pp.A.filter (G.Adj w)).card : ℝ)) * E12 ≤ (s : ℝ) * (l : ℝ) * E12 :=
          mul_le_mul_of_nonneg_right hb2 hE12nn
        linarith
    linarith
  have hS2B : D 3 5 ≤ 3 * (l : ℝ) * E2S2 + 3 * (s : ℝ) * (l : ℝ) * E12 +
      3 * (s : ℝ) * (l : ℝ) * E1B + ES2B_c := by
    have hsp : D 3 5 = (∑ u ∈ pp.S2, ∑ w ∈ pp.B.filter (G.Adj u), (y u - y w) ^ 2) + ES2B_c := by
      dsimp [D, blk, ES2B_c]; rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun u _ => (Finset.sum_filter_add_sum_filter_not pp.B (G.Adj u) _).symm)
    rw [hsp]
    have hg : ∑ u ∈ pp.S2, ∑ w ∈ pp.B.filter (G.Adj u), (y u - y w) ^ 2 ≤
        3 * (l : ℝ) * E2S2 + 3 * (s : ℝ) * (l : ℝ) * E12 + 3 * (s : ℝ) * (l : ℝ) * E1B := by
      by_cases hl0 : l = 0
      · have hempty : ∀ u ∈ pp.S2, pp.B.filter (G.Adj u) = ∅ := fun u hu =>
          Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero (hl0 ▸ hl2 u hu))
        rw [Finset.sum_eq_zero (fun u hu => by rw [hempty u hu, Finset.sum_empty]), hl0]; norm_num
      · have hlpos : (1 : ℝ) ≤ (l : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hl0
        have hle1 : ∑ u ∈ pp.S2, ∑ w ∈ pp.B.filter (G.Adj u), (y u - y w) ^ 2 ≤
            3 * (∑ u ∈ pp.S2, ((pp.B.filter (G.Adj u)).card : ℝ) * (y pp.v2 - y u) ^ 2) +
            3 * (∑ u ∈ pp.S2, ((pp.B.filter (G.Adj u)).card : ℝ)) * E12 +
            3 * (∑ u ∈ pp.S2, ∑ w ∈ pp.B.filter (G.Adj u), (y pp.v1 - y w) ^ 2) := by
          have hpt : ∀ u ∈ pp.S2, ∀ w ∈ pp.B.filter (G.Adj u), (y u - y w) ^ 2 ≤
              3 * ((y pp.v2 - y u) ^ 2 + (y pp.v1 - y pp.v2) ^ 2 + (y pp.v1 - y w) ^ 2) := by
            intro u _ w _
            have := h3sq (y u - y pp.v2) (y pp.v2 - y pp.v1) (y pp.v1 - y w)
            have h1 : (y u - y pp.v2) + (y pp.v2 - y pp.v1) + (y pp.v1 - y w) = y u - y w := by ring
            have h2 : (y u - y pp.v2) ^ 2 = (y pp.v2 - y u) ^ 2 := by ring
            have h3 : (y pp.v2 - y pp.v1) ^ 2 = (y pp.v1 - y pp.v2) ^ 2 := by ring
            rw [h1, h2, h3] at this; exact this
          calc _ ≤ ∑ u ∈ pp.S2, ∑ w ∈ pp.B.filter (G.Adj u),
                3 * ((y pp.v2 - y u) ^ 2 + (y pp.v1 - y pp.v2) ^ 2 + (y pp.v1 - y w) ^ 2) :=
                Finset.sum_le_sum (fun u hu => Finset.sum_le_sum (fun w hw => hpt u hu w hw))
            _ = _ := by
                simp_rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
                  ← Finset.sum_mul]
                dsimp [E12]; ring
        have hb1 : ∑ u ∈ pp.S2, ((pp.B.filter (G.Adj u)).card : ℝ) * (y pp.v2 - y u) ^ 2 ≤ (l : ℝ) * E2S2 := by
          rw [Finset.mul_sum]
          exact Finset.sum_le_sum (fun u hu => mul_le_mul_of_nonneg_right (by exact_mod_cast hl2 u hu) (sq_nonneg _))
        have hb2 : ∑ u ∈ pp.S2, ((pp.B.filter (G.Adj u)).card : ℝ) ≤ (s : ℝ) * (l : ℝ) := by
          calc _ ≤ ∑ _u ∈ pp.S2, (l : ℝ) := Finset.sum_le_sum (fun u hu => by exact_mod_cast hl2 u hu)
            _ = (s : ℝ) * (l : ℝ) := by rw [Finset.sum_const, hS2c, nsmul_eq_mul]
        have hb3 : ∑ u ∈ pp.S2, ∑ w ∈ pp.B.filter (G.Adj u), (y pp.v1 - y w) ^ 2 ≤ (s : ℝ) * E1B := by
          calc _ ≤ ∑ _u ∈ pp.S2, E1B := Finset.sum_le_sum (fun u _ =>
                Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => sq_nonneg _))
            _ = (s : ℝ) * E1B := by rw [Finset.sum_const, hS2c, nsmul_eq_mul]
        have hE1Bnn : 0 ≤ E1B := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
        have hE12nn : 0 ≤ E12 := sq_nonneg _
        have hsnn : (0 : ℝ) ≤ (s : ℝ) := Nat.cast_nonneg s
        have h3_sE1B : (s : ℝ) * E1B ≤ (s : ℝ) * (l : ℝ) * E1B :=
          mul_le_mul_of_nonneg_right (by nlinarith) hE1Bnn
        have h3_E12 : (∑ u ∈ pp.S2, ((pp.B.filter (G.Adj u)).card : ℝ)) * E12 ≤ (s : ℝ) * (l : ℝ) * E12 :=
          mul_le_mul_of_nonneg_right hb2 hE12nn
        linarith
    linarith
  have hD45 : D 4 5 = EAB := rfl
  have hedge_sum := pp.compl_block_sum_le y
  have h2tot : ∑ i : Fin n, ∑ j : Fin n, (y i - y j) ^ 2 = 2 * ((n : ℝ) * ∑ i, y i ^ 2) := by
    rw [← two_mul_sum_pairs (fun i j => (y i - y j) ^ 2) (fun _ _ => by ring) (fun _ => by ring),
      sum_pairs_sq_eq y hy0]
  let K : ℝ := (n : ℝ) + 2 + 3 * (s : ℝ) ^ 2 + 6 * (s : ℝ) * (l : ℝ)
  have hnr : (n : ℝ) = (a : ℝ) + b + c + 2 * s + 2 := by exact_mod_cast hn_eq
  have habr : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
  have hsr : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs1
  have hlr : (0 : ℝ) ≤ (l : ℝ) := Nat.cast_nonneg l
  have hE12nn : 0 ≤ E12 := sq_nonneg _
  have hE1S1nn : 0 ≤ E1S1 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hE1Bnn : 0 ≤ E1B := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hE1Cnn : 0 ≤ E1C := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hE2S2nn : 0 ≤ E2S2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hE2Ann : 0 ≤ E2A := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hE2Cnn : 0 ≤ E2C := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hEABnn : 0 ≤ EAB := Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hES1Ann : 0 ≤ ES1A_c := Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hES2Bnn : 0 ≤ ES2B_c := Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have har : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
  have hbr : (0 : ℝ) ≤ (b : ℝ) := Nat.cast_nonneg b
  have hcr : (0 : ℝ) ≤ (c : ℝ) := Nat.cast_nonneg c
  have hs2 : (s : ℝ) ≤ (s : ℝ) ^ 2 := by nlinarith only [hsr]
  have hsl : (l : ℝ) ≤ (s : ℝ) * (l : ℝ) := by nlinarith only [hsr, hlr]
  have hsl0 : 0 ≤ (s : ℝ) * (l : ℝ) := mul_nonneg (by linarith) hlr
  have hc12 : ((b : ℝ) + c + s + 2) + ((a : ℝ) + s + 2) + 3 * (s : ℝ) ^ 2 +
      3 * (s : ℝ) * (l : ℝ) + 3 * (s : ℝ) * (l : ℝ) ≤ K := by dsimp [K]; linarith
  have hc1S1 : ((b : ℝ) + c + s + 2) + 3 * (s : ℝ) + 3 * (l : ℝ) ≤ K := by dsimp [K]; linarith
  have hc1B : ((b : ℝ) + c + s + 2) + 3 * (s : ℝ) * (l : ℝ) ≤ K := by dsimp [K]; linarith
  have hc1C : ((b : ℝ) + c + s + 2) ≤ K := by dsimp [K]; linarith
  have hc2S2 : ((a : ℝ) + c + s + 1) + ((a : ℝ) + s + 2) + 3 * (s : ℝ) + 3 * (l : ℝ) ≤ K := by
    dsimp [K]; linarith
  have hc2A : ((a : ℝ) + c + s + 1) + ((a : ℝ) + s + 2) + 3 * (s : ℝ) * (l : ℝ) ≤ K := by
    dsimp [K]; linarith
  have hc2C : ((a : ℝ) + c + s + 1) ≤ K := by dsimp [K]; linarith
  have hc1 : (1 : ℝ) ≤ K := by dsimp [K]; linarith
  have hKnn : 0 ≤ K := by linarith
  have hm12 := mul_le_mul_of_nonneg_right hc12 hE12nn
  have hm1S1 := mul_le_mul_of_nonneg_right hc1S1 hE1S1nn
  have hm1B := mul_le_mul_of_nonneg_right hc1B hE1Bnn
  have hm1C := mul_le_mul_of_nonneg_right hc1C hE1Cnn
  have hm2S2 := mul_le_mul_of_nonneg_right hc2S2 hE2S2nn
  have hm2A := mul_le_mul_of_nonneg_right hc2A hE2Ann
  have hm2C := mul_le_mul_of_nonneg_right hc2C hE2Cnn
  have hmAB := mul_le_mul_of_nonneg_right hc1 hEABnn
  have hmS1A := mul_le_mul_of_nonneg_right hc1 hES1Ann
  have hmS2B := mul_le_mul_of_nonneg_right hc1 hES2Bnn
  have hcomb : 2 * ((n : ℝ) * ∑ i, y i ^ 2) ≤
      2 * K * (E12 + E1S1 + E1B + E1C + E2S2 + E2A + E2C + EAB + ES1A_c + ES2B_c) := by
    linarith
  have hfinal := mul_le_mul_of_nonneg_left hedge_sum (by linarith : (0 : ℝ) ≤ 2 * K)
  linarith

end PathPartition

end PartitionAndGeneralBounds

section SmallCases

private noncomputable def bmean {n : ℕ} (U : Finset (Fin n)) (z : Fin n → ℝ) : ℝ :=
  if U.card = 0 then 0 else (∑ u ∈ U, z u) / (U.card : ℝ)

private noncomputable def bvar {n : ℕ} (U : Finset (Fin n)) (z : Fin n → ℝ) : ℝ :=
  ∑ u ∈ U, (z u - bmean U z) ^ 2

private lemma bvar_nonneg {n : ℕ} (U : Finset (Fin n)) (z : Fin n → ℝ) : 0 ≤ bvar U z :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

private lemma sum_sub_bmean {n : ℕ} (U : Finset (Fin n)) (z : Fin n → ℝ) :
    ∑ u ∈ U, (z u - bmean U z) = 0 := by
  by_cases hU : U.card = 0
  · rw [Finset.card_eq_zero.mp hU]; simp
  · have hpos : (U.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hU
    simp only [bmean, if_neg hU, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    field_simp [hpos]; ring

private lemma block_norm_sq {n : ℕ} (U : Finset (Fin n)) (z : Fin n → ℝ) :
    ∑ u ∈ U, z u ^ 2 = bvar U z + (U.card : ℝ) * bmean U z ^ 2 := by
  have h : ∀ u ∈ U, z u ^ 2 = (z u - bmean U z) ^ 2 + 2 * bmean U z * (z u - bmean U z) +
      bmean U z ^ 2 := fun _ _ => by ring
  rw [Finset.sum_congr rfl h, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, sum_sub_bmean, mul_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  rfl

private lemma block_star_sq {n : ℕ} (U : Finset (Fin n)) (z : Fin n → ℝ) (c : ℝ) :
    ∑ u ∈ U, (z u - c) ^ 2 = bvar U z + (U.card : ℝ) * (bmean U z - c) ^ 2 := by
  have h : ∀ u ∈ U, (z u - c) ^ 2 = (z u - bmean U z) ^ 2 +
      2 * (bmean U z - c) * (z u - bmean U z) + (bmean U z - c) ^ 2 := fun _ _ => by ring
  rw [Finset.sum_congr rfl h, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, sum_sub_bmean, mul_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  rfl

private lemma block_bip_sq {n : ℕ} (U W : Finset (Fin n)) (z : Fin n → ℝ) :
    ∑ u ∈ U, ∑ w ∈ W, (z u - z w) ^ 2 =
      (W.card : ℝ) * bvar U z + (U.card : ℝ) * bvar W z +
      (U.card : ℝ) * (W.card : ℝ) * (bmean U z - bmean W z) ^ 2 := by
  have hinner : ∀ u ∈ U, ∑ w ∈ W, (z u - z w) ^ 2 =
      bvar W z + (W.card : ℝ) * (z u - bmean W z) ^ 2 := by
    intro u _
    have h := block_star_sq W z (z u)
    have hsw : ∑ w ∈ W, (z u - z w) ^ 2 = ∑ w ∈ W, (z w - z u) ^ 2 :=
      Finset.sum_congr rfl (fun _ _ => by ring)
    rw [hsw, h]; ring
  rw [Finset.sum_congr rfl hinner, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
    ← Finset.mul_sum, block_star_sq]
  ring

private lemma leaf_elim (w lam x m : ℝ) (hw : 0 ≤ w) (hlam : lam < 1) :
    -(w * lam / (1 - lam)) * x ^ 2 ≤ w * ((m - x) ^ 2 - lam * m ^ 2) := by
  have hpos : 0 < 1 - lam := by linarith
  have h1 : w * ((m - x) ^ 2 - lam * m ^ 2) + (w * lam / (1 - lam)) * x ^ 2 =
      w * (1 - lam) * (m - x / (1 - lam)) ^ 2 := by
    field_simp [hpos.ne']; ring
  have hnn : 0 ≤ w * (1 - lam) * (m - x / (1 - lam)) ^ 2 := by positivity
  linarith

private lemma center_elim (c lam p q m : ℝ) (hc : 0 ≤ c) (hlam : lam < 2) :
    c * ((1 - lam) * (p ^ 2 + q ^ 2) - 2 * p * q) / (2 - lam) ≤
      c * ((m - p) ^ 2 + (m - q) ^ 2 - lam * m ^ 2) := by
  have hpos : 0 < 2 - lam := by linarith
  have h1 : c * ((m - p) ^ 2 + (m - q) ^ 2 - lam * m ^ 2) -
      c * ((1 - lam) * (p ^ 2 + q ^ 2) - 2 * p * q) / (2 - lam) =
      c * (2 - lam) * (m - (p + q) / (2 - lam)) ^ 2 := by
    field_simp [hpos.ne']; ring
  have hnn : 0 ≤ c * (2 - lam) * (m - (p + q) / (2 - lam)) ^ 2 := by positivity
  linarith

private lemma bridge_elim (a lam p mA mS : ℝ) (hpos : 0 < 1 + a - lam) :
    p ^ 2 + a * mA ^ 2 - (p + a * mA) ^ 2 / (1 + a - lam) ≤
      (mS - p) ^ 2 + a * (mS - mA) ^ 2 - lam * mS ^ 2 := by
  have h1 : (mS - p) ^ 2 + a * (mS - mA) ^ 2 - lam * mS ^ 2 -
      (p ^ 2 + a * mA ^ 2 - (p + a * mA) ^ 2 / (1 + a - lam)) =
      (1 + a - lam) * (mS - (p + a * mA) / (1 + a - lam)) ^ 2 := by
    field_simp [hpos.ne']; ring
  have hnn : 0 ≤ (1 + a - lam) * (mS - (p + a * mA) / (1 + a - lam)) ^ 2 := by positivity
  linarith

private lemma bip2_elim (a b lam p q mA mB : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hlam : lam < 1) :
    a * q ^ 2 + b * p ^ 2 -
      (a * (1 - lam + a) * q ^ 2 + b * (1 - lam + b) * p ^ 2 + 2 * a * b * p * q) /
        ((1 - lam) * (1 - lam + a + b)) ≤
      a * ((mA - q) ^ 2 - lam * mA ^ 2) + b * ((mB - p) ^ 2 - lam * mB ^ 2) +
      a * b * (mA - mB) ^ 2 := by
  have hd1 : 0 < 1 - lam := by linarith
  have hd2 : 0 < 1 - lam + a + b := by linarith
  by_cases ha0 : a = 0
  · subst ha0
    have h1 := leaf_elim b lam p mB hb hlam
    have heq : 0 * q ^ 2 + b * p ^ 2 -
        (0 * (1 - lam + 0) * q ^ 2 + b * (1 - lam + b) * p ^ 2 + 2 * 0 * b * p * q) /
          ((1 - lam) * (1 - lam + 0 + b)) = -(b * lam / (1 - lam)) * p ^ 2 := by
      have hdb : 0 < 1 - lam + b := by linarith
      field_simp [hd1.ne', hdb.ne']; ring
    rw [heq]; linarith
  · by_cases hb0 : b = 0
    · subst hb0
      have h1 := leaf_elim a lam q mA ha hlam
      have heq : a * q ^ 2 + 0 * p ^ 2 -
          (a * (1 - lam + a) * q ^ 2 + 0 * (1 - lam + 0) * p ^ 2 + 2 * a * 0 * p * q) /
            ((1 - lam) * (1 - lam + a + 0)) = -(a * lam / (1 - lam)) * q ^ 2 := by
        have hda : 0 < 1 - lam + a := by linarith
        field_simp [hd1.ne', hda.ne']; ring
      rw [heq]; linarith
    · have h1lb : 0 < 1 - lam + b := by linarith
      have hsq :
          a * ((mA - q) ^ 2 - lam * mA ^ 2) + b * ((mB - p) ^ 2 - lam * mB ^ 2) +
            a * b * (mA - mB) ^ 2 -
          (a * q ^ 2 + b * p ^ 2 -
            (a * (1 - lam + a) * q ^ 2 + b * (1 - lam + b) * p ^ 2 + 2 * a * b * p * q) /
              ((1 - lam) * (1 - lam + a + b))) =
          a * (1 - lam + b) * (mA - (b * mB + q) / (1 - lam + b)) ^ 2 +
          (b * (1 - lam) * (1 - lam + a + b) / (1 - lam + b)) *
            (mB - ((1 - lam + b) * p + a * q) / ((1 - lam) * (1 - lam + a + b))) ^ 2 := by
        field_simp [hd1.ne', hd2.ne', h1lb.ne']; ring
      have ht1 : 0 ≤ a * (1 - lam + b) * (mA - (b * mB + q) / (1 - lam + b)) ^ 2 := by positivity
      have ht2 : 0 ≤ (b * (1 - lam) * (1 - lam + a + b) / (1 - lam + b)) *
          (mB - ((1 - lam + b) * p + a * q) / ((1 - lam) * (1 - lam + a + b))) ^ 2 := by positivity
      linarith

private lemma quad2_elim (HAA HBB HAB vA vB x y : ℝ)
    (hAA : 0 < HAA) (hdet : 0 < HAA * HBB - HAB ^ 2) :
    -((HBB * vA ^ 2 + HAA * vB ^ 2 - 2 * HAB * vA * vB) / (HAA * HBB - HAB ^ 2)) ≤
      HAA * x ^ 2 + 2 * HAB * x * y + HBB * y ^ 2 - 2 * vA * x - 2 * vB * y := by
  have h1 :
      HAA * x ^ 2 + 2 * HAB * x * y + HBB * y ^ 2 - 2 * vA * x - 2 * vB * y +
      (HBB * vA ^ 2 + HAA * vB ^ 2 - 2 * HAB * vA * vB) / (HAA * HBB - HAB ^ 2) =
      HAA * (x + (HAB * y - vA) / HAA) ^ 2 +
      ((HAA * HBB - HAB ^ 2) / HAA) *
        (y - (HAA * vB - HAB * vA) / (HAA * HBB - HAB ^ 2)) ^ 2 := by
    field_simp [hAA.ne', hdet.ne']; ring
  have ht1 : 0 ≤ HAA * (x + (HAB * y - vA) / HAA) ^ 2 := by positivity
  have ht2 : 0 ≤ ((HAA * HBB - HAB ^ 2) / HAA) *
      (y - (HAA * vB - HAB * vA) / (HAA * HBB - HAB ^ 2)) ^ 2 := by positivity
  linarith

private lemma quad1_elim (H v x : ℝ) (hH : 0 < H) :
    -(v ^ 2 / H) ≤ H * x ^ 2 - 2 * v * x := by
  have h1 : H * x ^ 2 - 2 * v * x + v ^ 2 / H = H * (x - v / H) ^ 2 := by
    field_simp [hH.ne']; ring
  have ht : 0 ≤ H * (x - v / H) ^ 2 := by positivity
  linarith

-- Clean P4 case without Finset.sum_insert timeout
lemma quad_P4_ge_half {n : ℕ} {H : SimpleGraph (Fin n)} [DecidableRel H.Adj]
    {a b c d : Fin n} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hcov : ∀ z : Fin n, z = a ∨ z = b ∨ z = c ∨ z = d)
    (e1 : H.Adj a b) (e2 : H.Adj b c) (e3 : H.Adj c d)
    {z : Fin n → ℝ} (hz : ∑ i, z i = 0) :
    (1 / 2 : ℝ) * ∑ i, z i ^ 2 ≤ quad H z := by
  let p4 : Fin 4 → Fin n := ![a, b, c, d]
  have hp4_inj : Function.Injective p4 := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [p4] at hij ⊢ <;> exfalso
    · exact hab hij
    · exact hac hij
    · exact had hij
    · exact hab.symm hij
    · exact hbc hij
    · exact hbd hij
    · exact hac.symm hij
    · exact hbc.symm hij
    · exact hcd hij
    · exact had.symm hij
    · exact hbd.symm hij
    · exact hcd.symm hij
  have hp4_surj : Function.Surjective p4 := by
    intro x
    rcases hcov x with rfl | rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
  let eqv : Fin 4 ≃ Fin n := Equiv.ofBijective p4 ⟨hp4_inj, hp4_surj⟩
  have hsum : ∀ f : Fin n → ℝ, ∑ i : Fin n, f i = f a + f b + f c + f d := by
    intro f
    rw [← Equiv.sum_comp eqv f, Fin.sum_univ_four]
    have h0 : eqv 0 = a := rfl
    have h1 : eqv 1 = b := rfl
    have h2 : eqv 2 = c := rfl
    have h3 : eqv 3 = d := rfl
    rw [h0, h1, h2, h3]
  have hz4 : z a + z b + z c + z d = 0 := by rw [← hsum]; exact hz
  have hq : (z a - z b) ^ 2 + (z b - z c) ^ 2 + (z c - z d) ^ 2 ≤ quad H z := by
    have h2 := two_mul_quad H z
    rw [hsum (fun i => ∑ j : Fin n, if H.Adj i j then (z i - z j) ^ 2 else 0),
      hsum (fun j => if H.Adj a j then (z a - z j) ^ 2 else 0),
      hsum (fun j => if H.Adj b j then (z b - z j) ^ 2 else 0),
      hsum (fun j => if H.Adj c j then (z c - z j) ^ 2 else 0),
      hsum (fun j => if H.Adj d j then (z d - z j) ^ 2 else 0)] at h2
    have hnn : ∀ i j : Fin n, 0 ≤ if H.Adj i j then (z i - z j) ^ 2 else 0 :=
      fun _ _ => by split_ifs <;> positivity
    have he1 : (if H.Adj a b then (z a - z b) ^ 2 else 0) = (z a - z b) ^ 2 := if_pos e1
    have he1' : (if H.Adj b a then (z b - z a) ^ 2 else 0) = (z a - z b) ^ 2 := by rw [if_pos e1.symm]; ring
    have he2 : (if H.Adj b c then (z b - z c) ^ 2 else 0) = (z b - z c) ^ 2 := if_pos e2
    have he2' : (if H.Adj c b then (z c - z b) ^ 2 else 0) = (z b - z c) ^ 2 := by rw [if_pos e2.symm]; ring
    have he3 : (if H.Adj c d then (z c - z d) ^ 2 else 0) = (z c - z d) ^ 2 := if_pos e3
    have he3' : (if H.Adj d c then (z d - z c) ^ 2 else 0) = (z c - z d) ^ 2 := by rw [if_pos e3.symm]; ring
    linarith [hnn a a, hnn a c, hnn a d, hnn b b, hnn b d, hnn c a, hnn c c, hnn d a, hnn d b, hnn d d]
  rw [hsum (fun i => z i ^ 2)]
  have hzd : z d = -(z a + z b + z c) := by linarith
  rw [hzd] at hq ⊢
  have hsos : 2 * ((z a - z b) ^ 2 + (z b - z c) ^ 2 + (z c - -(z a + z b + z c)) ^ 2) -
      (z a ^ 2 + z b ^ 2 + z c ^ 2 + (-(z a + z b + z c)) ^ 2) =
      2 * (z a - z b / 2 + 3 * z c / 2) ^ 2 +
      (7 / 2 : ℝ) * (z b + 5 * z c / 7) ^ 2 + (12 / 7 : ℝ) * z c ^ 2 := by ring
  nlinarith [sq_nonneg (z a - z b / 2 + 3 * z c / 2),
    sq_nonneg (z b + 5 * z c / 7), sq_nonneg (z c)]

set_option maxHeartbeats 400000 in
private lemma g2_small_bound {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    [DecidableRel Gᶜ.Adj] (pp : PathPartition G) {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam < 1)
    {y : Fin n → ℝ} (hy0 : ∑ i, y i = 0)
    (hpoly :
      let s : ℝ := pp.P.card
      let a : ℝ := pp.A.card
      let b : ℝ := pp.B.card
      let p : ℝ := 1 + s + a
      let q : ℝ := -(1 + s + b)
      0 ≤ (p - q) ^ 2 - (lam + s * lam / (1 - lam)) * (p ^ 2 + q ^ 2) +
          a * q ^ 2 + b * p ^ 2 -
          (a * (1 - lam + a) * q ^ 2 + b * (1 - lam + b) * p ^ 2 + 2 * a * b * p * q) /
            ((1 - lam) * (1 - lam + a + b))) :
    lam * ∑ i, y i ^ 2 ≤ quad Gᶜ y := by
  let s : ℝ := pp.P.card
  let a : ℝ := pp.A.card
  let b : ℝ := pp.B.card
  let c : ℝ := pp.C.card
  have hden : 0 < 2 + 2 * s + a + b := by positivity
  let k0 : ℝ := ((1 + s + b) * y pp.v1 + (1 + s + a) * y pp.v2) / (2 + 2 * s + a + b)
  let t : ℝ := (y pp.v1 - y pp.v2) / (2 + 2 * s + a + b)
  let z : Fin n → ℝ := fun i => y i - k0
  have hz1 : z pp.v1 = (1 + s + a) * t := by
    dsimp [z, k0, t]
    rw [sub_eq_iff_eq_add, mul_div_assoc', ← add_div, eq_div_iff hden.ne']; ring
  have hz2 : z pp.v2 = -(1 + s + b) * t := by
    dsimp [z, k0, t]
    rw [sub_eq_iff_eq_add, mul_div_assoc', ← add_div, eq_div_iff hden.ne']; ring
  have hnorm_le : ∑ i, y i ^ 2 ≤ ∑ i, z i ^ 2 := by
    have hexp : ∑ i, z i ^ 2 = (∑ i, y i ^ 2) - 2 * k0 * (∑ i, y i) + (n : ℝ) * k0 ^ 2 := by
      have : ∀ i, (y i - k0) ^ 2 = y i ^ 2 - 2 * k0 * y i + k0 ^ 2 := fun _ => by ring
      simp_rw [z, this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [hexp, hy0, mul_zero, sub_zero]
    nlinarith [sq_nonneg k0]
  rw [← quad_shift Gᶜ y k0]
  have hblk0 := pp.compl_block_sum_le z
  have hnn_f1 : 0 ≤ ∑ w ∈ pp.S1, ∑ u ∈ pp.A.filter (fun u => ¬ G.Adj w u), (z w - z u) ^ 2 :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hnn_f2 : 0 ≤ ∑ u ∈ pp.S2, ∑ w ∈ pp.B.filter (fun w => ¬ G.Adj u w), (z u - z w) ^ 2 :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hblk :
      (z pp.v1 - z pp.v2) ^ 2 +
      (∑ w ∈ pp.S1, (z pp.v1 - z w) ^ 2) + (∑ u ∈ pp.S2, (z pp.v2 - z u) ^ 2) +
      (∑ u ∈ pp.A, (z pp.v2 - z u) ^ 2) + (∑ w ∈ pp.B, (z pp.v1 - z w) ^ 2) +
      (∑ x ∈ pp.C, (z pp.v1 - z x) ^ 2) + (∑ x ∈ pp.C, (z pp.v2 - z x) ^ 2) +
      (∑ u ∈ pp.A, ∑ w ∈ pp.B, (z u - z w) ^ 2) ≤ quad Gᶜ z := by linarith
  have hsw : ∀ (v : Fin n) (U : Finset (Fin n)),
      ∑ u ∈ U, (z v - z u) ^ 2 = bvar U z + (U.card : ℝ) * (bmean U z - z v) ^ 2 := by
    intro v U; rw [← block_star_sq U z (z v)]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  rw [hsw pp.v1 pp.S1, hsw pp.v2 pp.S2, hsw pp.v2 pp.A, hsw pp.v1 pp.B,
    hsw pp.v1 pp.C, hsw pp.v2 pp.C, block_bip_sq pp.A pp.B z] at hblk
  have hnormz : ∑ i, z i ^ 2 =
      z pp.v1 ^ 2 + z pp.v2 ^ 2 +
      (bvar pp.S1 z + s * bmean pp.S1 z ^ 2) +
      (bvar pp.S2 z + s * bmean pp.S2 z ^ 2) +
      (bvar pp.A z + a * bmean pp.A z ^ 2) +
      (bvar pp.B z + b * bmean pp.B z ^ 2) +
      (bvar pp.C z + c * bmean pp.C z ^ 2) := by
    rw [pp.sum_univ_split (fun i => z i ^ 2),
      block_norm_sq pp.S1 z, block_norm_sq pp.S2 z, block_norm_sq pp.A z,
      block_norm_sq pp.B z, block_norm_sq pp.C z]
    simp only [s, a, b, c, pp.card_S1, pp.card_S2]
  have hS1c : (pp.S1.card : ℝ) = s := by dsimp [s]; exact_mod_cast pp.card_S1
  have hS2c : (pp.S2.card : ℝ) = s := by dsimp [s]; exact_mod_cast pp.card_S2
  rw [hS1c, hS2c] at hblk
  have heS1 := leaf_elim s lam (z pp.v1) (bmean pp.S1 z) (by positivity) hlam1
  have heS2 := leaf_elim s lam (z pp.v2) (bmean pp.S2 z) (by positivity) hlam1
  have heC := center_elim c lam (z pp.v1) (z pp.v2) (bmean pp.C z) (by positivity) (by linarith)
  have heAB := bip2_elim a b lam (z pp.v1) (z pp.v2) (bmean pp.A z) (bmean pp.B z)
    (by positivity) (by positivity) hlam1
  have hCnn : 0 ≤ c * ((1 - lam) * (z pp.v1 ^ 2 + z pp.v2 ^ 2) - 2 * z pp.v1 * z pp.v2) / (2 - lam) := by
    rw [hz1, hz2]
    have hnum : (1 - lam) * (((1 + s + a) * t) ^ 2 + (-(1 + s + b) * t) ^ 2) -
        2 * ((1 + s + a) * t) * (-(1 + s + b) * t) =
        ((1 - lam) * ((1 + s + a) ^ 2 + (1 + s + b) ^ 2) +
          2 * (1 + s + a) * (1 + s + b)) * t ^ 2 := by ring
    rw [hnum]
    have h2l : 0 < 2 - lam := by linarith
    have h1l : 0 < 1 - lam := by linarith
    have hc0 : 0 ≤ c := by positivity
    have hcoef : 0 ≤ (1 - lam) * ((1 + s + a) ^ 2 + (1 + s + b) ^ 2) +
        2 * (1 + s + a) * (1 + s + b) := by positivity
    exact div_nonneg (mul_nonneg hc0 (mul_nonneg hcoef (sq_nonneg t))) h2l.le
  have hmain : 0 ≤ (z pp.v1 - z pp.v2) ^ 2 - (lam + s * lam / (1 - lam)) * (z pp.v1 ^ 2 + z pp.v2 ^ 2) +
      a * z pp.v2 ^ 2 + b * z pp.v1 ^ 2 -
      (a * (1 - lam + a) * z pp.v2 ^ 2 + b * (1 - lam + b) * z pp.v1 ^ 2 +
        2 * a * b * z pp.v1 * z pp.v2) / ((1 - lam) * (1 - lam + a + b)) := by
    rw [hz1, hz2]
    have hfac :
        ((1 + s + a) * t - -(1 + s + b) * t) ^ 2 -
        (lam + s * lam / (1 - lam)) * (((1 + s + a) * t) ^ 2 + (-(1 + s + b) * t) ^ 2) +
        a * (-(1 + s + b) * t) ^ 2 + b * ((1 + s + a) * t) ^ 2 -
        (a * (1 - lam + a) * (-(1 + s + b) * t) ^ 2 + b * (1 - lam + b) * ((1 + s + a) * t) ^ 2 +
          2 * a * b * ((1 + s + a) * t) * (-(1 + s + b) * t)) / ((1 - lam) * (1 - lam + a + b)) =
        t ^ 2 * (((1 + s + a) - -(1 + s + b)) ^ 2 -
          (lam + s * lam / (1 - lam)) * ((1 + s + a) ^ 2 + (-(1 + s + b)) ^ 2) +
          a * (-(1 + s + b)) ^ 2 + b * (1 + s + a) ^ 2 -
          (a * (1 - lam + a) * (-(1 + s + b)) ^ 2 + b * (1 - lam + b) * (1 + s + a) ^ 2 +
            2 * a * b * (1 + s + a) * (-(1 + s + b))) / ((1 - lam) * (1 - lam + a + b))) := by
      ring
    rw [hfac]
    exact mul_nonneg (sq_nonneg t) hpoly
  have hvS1 := bvar_nonneg pp.S1 z
  have hvS2 := bvar_nonneg pp.S2 z
  have hvA := bvar_nonneg pp.A z
  have hvB := bvar_nonneg pp.B z
  have hvC := bvar_nonneg pp.C z
  have hba : 0 ≤ b * bvar pp.A z := mul_nonneg (Nat.cast_nonneg _) hvA
  have hab' : 0 ≤ a * bvar pp.B z := mul_nonneg (Nat.cast_nonneg _) hvB
  have h1S1 : 0 ≤ (1 - lam) * bvar pp.S1 z := mul_nonneg (by linarith) hvS1
  have h1S2 : 0 ≤ (1 - lam) * bvar pp.S2 z := mul_nonneg (by linarith) hvS2
  have h1A : 0 ≤ (1 - lam) * bvar pp.A z := mul_nonneg (by linarith) hvA
  have h1B : 0 ≤ (1 - lam) * bvar pp.B z := mul_nonneg (by linarith) hvB
  have h2C : 0 ≤ (2 - lam) * bvar pp.C z := mul_nonneg (by linarith) hvC
  have hstep : lam * ∑ i, z i ^ 2 ≤ quad Gᶜ z := by
    rw [hnormz]
    linarith
  exact (mul_le_mul_of_nonneg_left hnorm_le hlam0).trans hstep

lemma small_s2_bound {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    [DecidableRel Gᶜ.Adj] (pp : PathPartition G) (hs : pp.P.card = 2)
    (hab : pp.A.card ≤ pp.B.card) (hsum : pp.A.card + pp.B.card ≤ 3)
    {y : Fin n → ℝ} (hy0 : ∑ i, y i = 0) :
    (1 / 3 : ℝ) * ∑ i, y i ^ 2 ≤ quad Gᶜ y := by
  apply g2_small_bound pp (by norm_num) (by norm_num) hy0
  dsimp only; rw [hs]
  generalize ha : pp.A.card = a at hab hsum ⊢
  generalize hb : pp.B.card = b at hab hsum ⊢
  have ha1 : a ≤ 1 := by omega
  have hb3 : b ≤ 3 := by omega
  interval_cases a <;> interval_cases b <;> try omega
  all_goals norm_num

lemma small_s1_l2_bound {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    [DecidableRel Gᶜ.Adj] (pp : PathPartition G) (hs : pp.P.card = 1)
    (hab : pp.A.card ≤ pp.B.card) (hsum : pp.A.card + pp.B.card ≤ 7)
    {y : Fin n → ℝ} (hy0 : ∑ i, y i = 0) :
    (2 / 5 : ℝ) * ∑ i, y i ^ 2 ≤ quad Gᶜ y := by
  apply g2_small_bound pp (by norm_num) (by norm_num) hy0
  dsimp only; rw [hs]
  generalize ha : pp.A.card = a at hab hsum ⊢
  generalize hb : pp.B.card = b at hab hsum ⊢
  have ha3 : a ≤ 3 := by omega
  have hb7 : b ≤ 7 := by omega
  interval_cases a <;> interval_cases b <;> try omega
  all_goals norm_num

private lemma g3_alg_id (a0 b0 lam p q da db c_z ab1_z mA mB : ℝ)
    (hda : da ≠ 0) (hdb : db ≠ 0) :
    ((p - q) ^ 2 - lam * (p ^ 2 + q ^ 2) + c_z + ab1_z +
      p ^ 2 - p ^ 2 / da + q ^ 2 - q ^ 2 / db + a0 * q ^ 2 + b0 * p ^ 2) +
    (a0 * (2 - lam + b0 - a0 / da)) * mA ^ 2 +
    2 * (-(a0 * b0)) * mA * mB +
    (b0 * (2 - lam + a0 - b0 / db)) * mB ^ 2 -
    2 * (a0 * (q + p / da)) * mA -
    2 * (b0 * (p + q / db)) * mB =
    (p - q) ^ 2 - lam * (p ^ 2 + q ^ 2) + c_z + ab1_z +
    (p ^ 2 + a0 * mA ^ 2 - (p + a0 * mA) ^ 2 / da) +
    (q ^ 2 + b0 * mB ^ 2 - (q + b0 * mB) ^ 2 / db) +
    a0 * ((mA - q) ^ 2 - lam * mA ^ 2) +
    b0 * ((mB - p) ^ 2 - lam * mB ^ 2) +
    a0 * b0 * (mA - mB) ^ 2 := by
  field_simp [hda, hdb]; ring

-- G3 algebraic reduction directly from compl_block_sum_le!
set_option maxHeartbeats 400000 in
private lemma g3_small_bound {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    [DecidableRel Gᶜ.Adj] (pp : PathPartition G) {u1 u2 : Fin n}
    (hS1 : pp.S1 = {u1}) (hS2 : pp.S2 = {u2})
    (A0 A1 B0 B1 : Finset (Fin n))
    (hA_union : A0 ∪ A1 = pp.A) (hA_disj : Disjoint A0 A1)
    (hB_union : B0 ∪ B1 = pp.B) (hB_disj : Disjoint B0 B1)
    (h1A0 : ∀ x ∈ A0, ¬ G.Adj u1 x) (h2B0 : ∀ x ∈ B0, ¬ G.Adj u2 x)
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam < 1)
    {y : Fin n → ℝ} (hy0 : ∑ i, y i = 0)
    (hpoly :
      let a : ℝ := pp.A.card
      let b : ℝ := pp.B.card
      let c : ℝ := pp.C.card
      let a0 : ℝ := A0.card
      let a1 : ℝ := A1.card
      let b0 : ℝ := B0.card
      let b1 : ℝ := B1.card
      let p : ℝ := 2 + a
      let q : ℝ := -(2 + b)
      let da : ℝ := 1 + a0 - lam
      let db : ℝ := 1 + b0 - lam
      let c_term : ℝ := c * ((1 - lam) * (p ^ 2 + q ^ 2) - 2 * p * q) / (2 - lam)
      let ab1_term : ℝ := a1 * q ^ 2 + b1 * p ^ 2 -
          (a1 * (1 - lam + a1) * q ^ 2 + b1 * (1 - lam + b1) * p ^ 2 + 2 * a1 * b1 * p * q) /
            ((1 - lam) * (1 - lam + a1 + b1))
      let const : ℝ := (p - q) ^ 2 - lam * (p ^ 2 + q ^ 2) + c_term + ab1_term +
          p ^ 2 - p ^ 2 / da + q ^ 2 - q ^ 2 / db + a0 * q ^ 2 + b0 * p ^ 2
      (a0 = 0 ∧ b0 = 0 → 0 ≤ const) ∧
      (a0 = 0 ∧ b0 ≠ 0 →
        let HBB := b0 * (2 - lam - b0 / db)
        let vB := b0 * (p + q / db)
        0 < HBB ∧ 0 ≤ const - vB ^ 2 / HBB) ∧
      (a0 ≠ 0 ∧ b0 = 0 →
        let HAA := a0 * (2 - lam - a0 / da)
        let vA := a0 * (q + p / da)
        0 < HAA ∧ 0 ≤ const - vA ^ 2 / HAA) ∧
      (a0 ≠ 0 ∧ b0 ≠ 0 →
        let HAA := a0 * (2 - lam + b0 - a0 / da)
        let HBB := b0 * (2 - lam + a0 - b0 / db)
        let HAB := -(a0 * b0)
        let det := HAA * HBB - HAB ^ 2
        let vA := a0 * (q + p / da)
        let vB := b0 * (p + q / db)
        0 < HAA ∧ 0 < det ∧
        0 ≤ const - (HBB * vA ^ 2 + HAA * vB ^ 2 - 2 * HAB * vA * vB) / det)) :
    lam * ∑ i, y i ^ 2 ≤ quad Gᶜ y := by
  let a : ℝ := pp.A.card
  let b : ℝ := pp.B.card
  let c : ℝ := pp.C.card
  let a0 : ℝ := A0.card
  let a1 : ℝ := A1.card
  let b0 : ℝ := B0.card
  let b1 : ℝ := B1.card
  have hden : 0 < 4 + a + b := by positivity
  let k0 : ℝ := ((2 + b) * y pp.v1 + (2 + a) * y pp.v2) / (4 + a + b)
  let t : ℝ := (y pp.v1 - y pp.v2) / (4 + a + b)
  let z : Fin n → ℝ := fun i => y i - k0
  have hz1 : z pp.v1 = (2 + a) * t := by
    dsimp [z, k0, t]; rw [sub_eq_iff_eq_add, mul_div_assoc', ← add_div, eq_div_iff hden.ne']; ring
  have hz2 : z pp.v2 = -(2 + b) * t := by
    dsimp [z, k0, t]; rw [sub_eq_iff_eq_add, mul_div_assoc', ← add_div, eq_div_iff hden.ne']; ring
  have hnorm_le : ∑ i, y i ^ 2 ≤ ∑ i, z i ^ 2 := by
    have hexp : ∑ i, z i ^ 2 = (∑ i, y i ^ 2) - 2 * k0 * (∑ i, y i) + (n : ℝ) * k0 ^ 2 := by
      have : ∀ i, (y i - k0) ^ 2 = y i ^ 2 - 2 * k0 * y i + k0 ^ 2 := fun _ => by ring
      simp_rw [z, this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [hexp, hy0, mul_zero, sub_zero]
    nlinarith [sq_nonneg k0]
  rw [← quad_shift Gᶜ y k0]
  -- Derive the G3 block sum inequality directly from compl_block_sum_le!
  have hblk0 := pp.compl_block_sum_le z
  rw [hS1, hS2, Finset.sum_singleton, Finset.sum_singleton, Finset.sum_singleton,
    Finset.sum_singleton] at hblk0
  have hA0_sub : A0 ⊆ pp.A.filter (fun u => ¬ G.Adj u1 u) := fun x hx =>
    Finset.mem_filter.mpr ⟨hA_union ▸ Finset.mem_union_left A1 hx, h1A0 x hx⟩
  have hB0_sub : B0 ⊆ pp.B.filter (fun w => ¬ G.Adj u2 w) := fun x hx =>
    Finset.mem_filter.mpr ⟨hB_union ▸ Finset.mem_union_left B1 hx, h2B0 x hx⟩
  have hf1 : ∑ x ∈ A0, (z u1 - z x) ^ 2 ≤
      ∑ u ∈ pp.A.filter (fun u => ¬ G.Adj u1 u), (z u1 - z u) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hA0_sub (fun _ _ _ => sq_nonneg _)
  have hf2 : ∑ x ∈ B0, (z u2 - z x) ^ 2 ≤
      ∑ w ∈ pp.B.filter (fun w => ¬ G.Adj u2 w), (z u2 - z w) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hB0_sub (fun _ _ _ => sq_nonneg _)
  have hA_sum : ∑ u ∈ pp.A, (z pp.v2 - z u) ^ 2 =
      (∑ x ∈ A0, (z pp.v2 - z x) ^ 2) + (∑ x ∈ A1, (z pp.v2 - z x) ^ 2) := by
    rw [← hA_union, Finset.sum_union hA_disj]
  have hB_sum : ∑ w ∈ pp.B, (z pp.v1 - z w) ^ 2 =
      (∑ x ∈ B0, (z pp.v1 - z x) ^ 2) + (∑ x ∈ B1, (z pp.v1 - z x) ^ 2) := by
    rw [← hB_union, Finset.sum_union hB_disj]
  have hAB_split : (∑ x ∈ A0, ∑ w ∈ B0, (z x - z w) ^ 2) + (∑ x ∈ A1, ∑ w ∈ B1, (z x - z w) ^ 2) ≤
      ∑ u ∈ pp.A, ∑ w ∈ pp.B, (z u - z w) ^ 2 := by
    rw [← hA_union, ← hB_union, Finset.sum_union hA_disj]
    have h1 : ∑ u ∈ A0, ∑ w ∈ B0 ∪ B1, (z u - z w) ^ 2 =
        (∑ u ∈ A0, ∑ w ∈ B0, (z u - z w) ^ 2) + (∑ u ∈ A0, ∑ w ∈ B1, (z u - z w) ^ 2) := by
      simp_rw [Finset.sum_union hB_disj, Finset.sum_add_distrib]
    have h2 : ∑ u ∈ A1, ∑ w ∈ B0 ∪ B1, (z u - z w) ^ 2 =
        (∑ u ∈ A1, ∑ w ∈ B0, (z u - z w) ^ 2) + (∑ u ∈ A1, ∑ w ∈ B1, (z u - z w) ^ 2) := by
      simp_rw [Finset.sum_union hB_disj, Finset.sum_add_distrib]
    have hnn1 : 0 ≤ ∑ u ∈ A0, ∑ w ∈ B1, (z u - z w) ^ 2 :=
      Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    have hnn2 : 0 ≤ ∑ u ∈ A1, ∑ w ∈ B0, (z u - z w) ^ 2 :=
      Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    linarith
  have hblk :
      (z pp.v1 - z pp.v2) ^ 2 + (z pp.v1 - z u1) ^ 2 + (z pp.v2 - z u2) ^ 2 +
      (∑ x ∈ A0, (z pp.v2 - z x) ^ 2) + (∑ x ∈ A1, (z pp.v2 - z x) ^ 2) +
      (∑ x ∈ B0, (z pp.v1 - z x) ^ 2) + (∑ x ∈ B1, (z pp.v1 - z x) ^ 2) +
      (∑ x ∈ pp.C, (z pp.v1 - z x) ^ 2) + (∑ x ∈ pp.C, (z pp.v2 - z x) ^ 2) +
      (∑ x ∈ A0, ∑ w ∈ B0, (z x - z w) ^ 2) + (∑ x ∈ A1, ∑ w ∈ B1, (z x - z w) ^ 2) +
      (∑ x ∈ A0, (z u1 - z x) ^ 2) + (∑ x ∈ B0, (z u2 - z x) ^ 2) ≤ quad Gᶜ z := by
    linarith
  have hsw : ∀ (v : Fin n) (U : Finset (Fin n)),
      ∑ x ∈ U, (z v - z x) ^ 2 = bvar U z + (U.card : ℝ) * (bmean U z - z v) ^ 2 := by
    intro v U; rw [← block_star_sq U z (z v)]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  rw [hsw pp.v2 A0, hsw pp.v2 A1, hsw pp.v1 B0, hsw pp.v1 B1,
    hsw pp.v1 pp.C, hsw pp.v2 pp.C, hsw u1 A0, hsw u2 B0,
    block_bip_sq A0 B0 z, block_bip_sq A1 B1 z] at hblk
  have hnormz : ∑ i, z i ^ 2 =
      z pp.v1 ^ 2 + z pp.v2 ^ 2 + z u1 ^ 2 + z u2 ^ 2 +
      (bvar A0 z + a0 * bmean A0 z ^ 2) + (bvar A1 z + a1 * bmean A1 z ^ 2) +
      (bvar B0 z + b0 * bmean B0 z ^ 2) + (bvar B1 z + b1 * bmean B1 z ^ 2) +
      (bvar pp.C z + c * bmean pp.C z ^ 2) := by
    rw [pp.sum_univ_split (fun i => z i ^ 2), hS1, hS2, Finset.sum_singleton, Finset.sum_singleton,
      ← hA_union, ← hB_union, Finset.sum_union hA_disj, Finset.sum_union hB_disj,
      block_norm_sq A0 z, block_norm_sq A1 z, block_norm_sq B0 z, block_norm_sq B1 z,
      block_norm_sq pp.C z]
    dsimp [a0, a1, b0, b1, c]; ring
  have hda : 0 < 1 + a0 - lam := by have : (0 : ℝ) ≤ a0 := by positivity
                                    linarith
  have hdb : 0 < 1 + b0 - lam := by have : (0 : ℝ) ≤ b0 := by positivity
                                    linarith
  have heC := center_elim c lam (z pp.v1) (z pp.v2) (bmean pp.C z) (by positivity) (by linarith)
  have heAB1 := bip2_elim a1 b1 lam (z pp.v1) (z pp.v2) (bmean A1 z) (bmean B1 z)
    (by positivity) (by positivity) hlam1
  have heS1 := bridge_elim a0 lam (z pp.v1) (bmean A0 z) (z u1) hda
  have heS2 := bridge_elim b0 lam (z pp.v2) (bmean B0 z) (z u2) hdb
  have h1S1 : (z pp.v1 - z u1) ^ 2 = (z u1 - z pp.v1) ^ 2 := by ring
  have h2S2 : (z pp.v2 - z u2) ^ 2 = (z u2 - z pp.v2) ^ 2 := by ring
  have hA0u1 : (bmean A0 z - z u1) ^ 2 = (z u1 - bmean A0 z) ^ 2 := by ring
  have hB0u2 : (bmean B0 z - z u2) ^ 2 = (z u2 - bmean B0 z) ^ 2 := by ring
  let da : ℝ := 1 + a0 - lam
  let db : ℝ := 1 + b0 - lam
  let c_z : ℝ := c * ((1 - lam) * (z pp.v1 ^ 2 + z pp.v2 ^ 2) - 2 * z pp.v1 * z pp.v2) / (2 - lam)
  let ab1_z : ℝ := a1 * z pp.v2 ^ 2 + b1 * z pp.v1 ^ 2 -
      (a1 * (1 - lam + a1) * z pp.v2 ^ 2 + b1 * (1 - lam + b1) * z pp.v1 ^ 2 +
        2 * a1 * b1 * z pp.v1 * z pp.v2) / ((1 - lam) * (1 - lam + a1 + b1))
  let const_z : ℝ := (z pp.v1 - z pp.v2) ^ 2 - lam * (z pp.v1 ^ 2 + z pp.v2 ^ 2) +
      c_z + ab1_z + z pp.v1 ^ 2 - z pp.v1 ^ 2 / da + z pp.v2 ^ 2 - z pp.v2 ^ 2 / db +
      a0 * z pp.v2 ^ 2 + b0 * z pp.v1 ^ 2
  let mA := bmean A0 z
  let mB := bmean B0 z
  have hred :
      const_z +
      (a0 * (2 - lam + b0 - a0 / da)) * mA ^ 2 +
      2 * (-(a0 * b0)) * mA * mB +
      (b0 * (2 - lam + a0 - b0 / db)) * mB ^ 2 -
      2 * (a0 * (z pp.v2 + z pp.v1 / da)) * mA -
      2 * (b0 * (z pp.v1 + z pp.v2 / db)) * mB ≤
      quad Gᶜ z - lam * ∑ i, z i ^ 2 := by
    have hvA0 := bvar_nonneg A0 z
    have hvA1 := bvar_nonneg A1 z
    have hvB0 := bvar_nonneg B0 z
    have hvB1 := bvar_nonneg B1 z
    have hvC := bvar_nonneg pp.C z
    have h1l : 0 ≤ 1 - lam := by linarith
    have h2l : 0 ≤ 2 - lam := by linarith
    have hnn1 : 0 ≤ b0 * bvar A0 z := mul_nonneg (Nat.cast_nonneg _) hvA0
    have hnn2 : 0 ≤ a0 * bvar B0 z := mul_nonneg (Nat.cast_nonneg _) hvB0
    have hnn3 : 0 ≤ b1 * bvar A1 z := mul_nonneg (Nat.cast_nonneg _) hvA1
    have hnn4 : 0 ≤ a1 * bvar B1 z := mul_nonneg (Nat.cast_nonneg _) hvB1
    have h2A0 : 0 ≤ (2 - lam) * bvar A0 z := mul_nonneg (by linarith) hvA0
    have h1A1 : 0 ≤ (1 - lam) * bvar A1 z := mul_nonneg (by linarith) hvA1
    have h2B0 : 0 ≤ (2 - lam) * bvar B0 z := mul_nonneg (by linarith) hvB0
    have h1B1 : 0 ≤ (1 - lam) * bvar B1 z := mul_nonneg (by linarith) hvB1
    have h2C : 0 ≤ (2 - lam) * bvar pp.C z := mul_nonneg (by linarith) hvC
    have halg := g3_alg_id a0 b0 lam (z pp.v1) (z pp.v2) da db c_z ab1_z mA mB hda.ne' hdb.ne'
    dsimp only [const_z]
    rw [halg, hnormz]
    linarith
  have hnonneg : 0 ≤
      const_z +
      (a0 * (2 - lam + b0 - a0 / da)) * mA ^ 2 +
      2 * (-(a0 * b0)) * mA * mB +
      (b0 * (2 - lam + a0 - b0 / db)) * mB ^ 2 -
      2 * (a0 * (z pp.v2 + z pp.v1 / da)) * mA -
      2 * (b0 * (z pp.v1 + z pp.v2 / db)) * mB := by
    let p0 : ℝ := 2 + a
    let q0 : ℝ := -(2 + b)
    let c_0 : ℝ := c * ((1 - lam) * (p0 ^ 2 + q0 ^ 2) - 2 * p0 * q0) / (2 - lam)
    let ab1_0 : ℝ := a1 * q0 ^ 2 + b1 * p0 ^ 2 -
        (a1 * (1 - lam + a1) * q0 ^ 2 + b1 * (1 - lam + b1) * p0 ^ 2 + 2 * a1 * b1 * p0 * q0) /
          ((1 - lam) * (1 - lam + a1 + b1))
    let const_0 : ℝ := (p0 - q0) ^ 2 - lam * (p0 ^ 2 + q0 ^ 2) +
        c_0 + ab1_0 + p0 ^ 2 - p0 ^ 2 / da + q0 ^ 2 - q0 ^ 2 / db +
        a0 * q0 ^ 2 + b0 * p0 ^ 2
    have hconst_hom : const_z = t ^ 2 * const_0 := by
      dsimp [const_z, const_0, c_z, c_0, ab1_z, ab1_0, p0, q0]; rw [hz1, hz2]; ring
    have hvA_hom : a0 * (z pp.v2 + z pp.v1 / da) = t * (a0 * (q0 + p0 / da)) := by
      rw [hz1, hz2]; dsimp [p0, q0]; ring
    have hvB_hom : b0 * (z pp.v1 + z pp.v2 / db) = t * (b0 * (p0 + q0 / db)) := by
      rw [hz1, hz2]; dsimp [p0, q0]; ring
    by_cases ha0 : a0 = 0
    · by_cases hb0 : b0 = 0
      · have h0 := hpoly.1 ⟨ha0, hb0⟩
        rw [ha0, hb0, hconst_hom]
        have : t ^ 2 * const_0 + 0 * (2 - lam + 0 - 0 / da) * mA ^ 2 +
            2 * -(0 * 0) * mA * mB + 0 * (2 - lam + 0 - 0 / db) * mB ^ 2 -
            2 * (0 * (z pp.v2 + z pp.v1 / da)) * mA -
            2 * (0 * (z pp.v1 + z pp.v2 / db)) * mB = t ^ 2 * const_0 := by ring
        rw [this]; exact mul_nonneg (sq_nonneg t) h0
      · obtain ⟨hHBB, hval⟩ := hpoly.2.1 ⟨ha0, hb0⟩
        have h1 := quad1_elim (b0 * (2 - lam - b0 / db)) (b0 * (z pp.v1 + z pp.v2 / db)) mB hHBB
        rw [hvB_hom] at h1
        have hrem : 0 ≤ const_z - (t * (b0 * (p0 + q0 / db))) ^ 2 / (b0 * (2 - lam - b0 / db)) := by
          rw [hconst_hom]
          have : t ^ 2 * const_0 - (t * (b0 * (p0 + q0 / db))) ^ 2 / (b0 * (2 - lam - b0 / db)) =
              t ^ 2 * (const_0 - (b0 * (p0 + q0 / db)) ^ 2 / (b0 * (2 - lam - b0 / db))) := by ring
          rw [this]; exact mul_nonneg (sq_nonneg t) hval
        rw [ha0]
        have hsim : const_z + 0 * (2 - lam + b0 - 0 / da) * mA ^ 2 +
            2 * -(0 * b0) * mA * mB + b0 * (2 - lam + 0 - b0 / db) * mB ^ 2 -
            2 * (0 * (z pp.v2 + z pp.v1 / da)) * mA -
            2 * (b0 * (z pp.v1 + z pp.v2 / db)) * mB =
            const_z + (b0 * (2 - lam - b0 / db) * mB ^ 2 - 2 * (b0 * (z pp.v1 + z pp.v2 / db)) * mB) := by
          ring
        rw [hsim, hvB_hom]; linarith
    · by_cases hb0 : b0 = 0
      · obtain ⟨hHAA, hval⟩ := hpoly.2.2.1 ⟨ha0, hb0⟩
        have h1 := quad1_elim (a0 * (2 - lam - a0 / da)) (a0 * (z pp.v2 + z pp.v1 / da)) mA hHAA
        rw [hvA_hom] at h1
        have hrem : 0 ≤ const_z - (t * (a0 * (q0 + p0 / da))) ^ 2 / (a0 * (2 - lam - a0 / da)) := by
          rw [hconst_hom]
          have : t ^ 2 * const_0 - (t * (a0 * (q0 + p0 / da))) ^ 2 / (a0 * (2 - lam - a0 / da)) =
              t ^ 2 * (const_0 - (a0 * (q0 + p0 / da)) ^ 2 / (a0 * (2 - lam - a0 / da))) := by ring
          rw [this]; exact mul_nonneg (sq_nonneg t) hval
        rw [hb0]
        have hsim : const_z + a0 * (2 - lam + 0 - a0 / da) * mA ^ 2 +
            2 * -(a0 * 0) * mA * mB + 0 * (2 - lam + a0 - 0 / db) * mB ^ 2 -
            2 * (a0 * (z pp.v2 + z pp.v1 / da)) * mA -
            2 * (0 * (z pp.v1 + z pp.v2 / db)) * mB =
            const_z + (a0 * (2 - lam - a0 / da) * mA ^ 2 - 2 * (a0 * (z pp.v2 + z pp.v1 / da)) * mA) := by
          ring
        rw [hsim, hvA_hom]; linarith
      · obtain ⟨hHAA, hdet, hval⟩ := hpoly.2.2.2 ⟨ha0, hb0⟩
        have h2 := quad2_elim
          (a0 * (2 - lam + b0 - a0 / da))
          (b0 * (2 - lam + a0 - b0 / db))
          (-(a0 * b0))
          (a0 * (z pp.v2 + z pp.v1 / da))
          (b0 * (z pp.v1 + z pp.v2 / db)) mA mB hHAA hdet
        rw [hvA_hom, hvB_hom] at h2
        have hrem : 0 ≤ const_z -
            ((b0 * (2 - lam + a0 - b0 / db)) * (t * (a0 * (q0 + p0 / da))) ^ 2 +
             (a0 * (2 - lam + b0 - a0 / da)) * (t * (b0 * (p0 + q0 / db))) ^ 2 -
             2 * (-(a0 * b0)) * (t * (a0 * (q0 + p0 / da))) * (t * (b0 * (p0 + q0 / db)))) /
              ((a0 * (2 - lam + b0 - a0 / da)) * (b0 * (2 - lam + a0 - b0 / db)) -
                (-(a0 * b0)) ^ 2) := by
          rw [hconst_hom]
          have hfac :
              t ^ 2 * const_0 -
              ((b0 * (2 - lam + a0 - b0 / db)) * (t * (a0 * (q0 + p0 / da))) ^ 2 +
               (a0 * (2 - lam + b0 - a0 / da)) * (t * (b0 * (p0 + q0 / db))) ^ 2 -
               2 * (-(a0 * b0)) * (t * (a0 * (q0 + p0 / da))) * (t * (b0 * (p0 + q0 / db)))) /
                ((a0 * (2 - lam + b0 - a0 / da)) * (b0 * (2 - lam + a0 - b0 / db)) -
                  (-(a0 * b0)) ^ 2) =
              t ^ 2 * (const_0 -
                ((b0 * (2 - lam + a0 - b0 / db)) * (a0 * (q0 + p0 / da)) ^ 2 +
                 (a0 * (2 - lam + b0 - a0 / da)) * (b0 * (p0 + q0 / db)) ^ 2 -
                 2 * (-(a0 * b0)) * (a0 * (q0 + p0 / da)) * (b0 * (p0 + q0 / db))) /
                  ((a0 * (2 - lam + b0 - a0 / da)) * (b0 * (2 - lam + a0 - b0 / db)) -
                    (-(a0 * b0)) ^ 2)) := by ring
          rw [hfac]; exact mul_nonneg (sq_nonneg t) hval
        rw [hvA_hom, hvB_hom]; linarith
  have hstep : lam * ∑ i, z i ^ 2 ≤ quad Gᶜ z := by linarith
  exact (mul_le_mul_of_nonneg_left hnorm_le hlam0).trans hstep

lemma small_s1_l0_bound {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    [DecidableRel Gᶜ.Adj] (pp : PathPartition G) (hs : pp.P.card = 1)
    (hab : pp.A.card ≤ pp.B.card)
    (hlo : 1 ≤ pp.A.card + pp.B.card + pp.C.card)
    (hhi : pp.A.card + pp.B.card ≤ 7)
    (hl1 : ∀ w ∈ pp.S1, (pp.A.filter (G.Adj w)).card ≤ 0)
    (hl2 : ∀ u ∈ pp.S2, (pp.B.filter (G.Adj u)).card ≤ 0)
    {y : Fin n → ℝ} (hy0 : ∑ i, y i = 0) :
    (2 / 3 : ℝ) * ∑ i, y i ^ 2 ≤ quad Gᶜ y := by
  obtain ⟨u1, hS1⟩ := Finset.card_eq_one.mp (pp.card_S1.trans hs)
  obtain ⟨u2, hS2⟩ := Finset.card_eq_one.mp (pp.card_S2.trans hs)
  have hu1_S1 : u1 ∈ pp.S1 := by rw [hS1]; simp
  have hu2_S2 : u2 ∈ pp.S2 := by rw [hS2]; simp
  have h1A : ∀ x ∈ pp.A, ¬ G.Adj u1 x := fun x hx hadj => by
    have := Finset.card_pos.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, hadj⟩⟩
    have := hl1 u1 hu1_S1; omega
  have h2B : ∀ x ∈ pp.B, ¬ G.Adj u2 x := fun x hx hadj => by
    have := Finset.card_pos.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, hadj⟩⟩
    have := hl2 u2 hu2_S2; omega
  apply g3_small_bound pp hS1 hS2 pp.A ∅ pp.B ∅ (Finset.union_empty _)
    (Finset.disjoint_empty_right _) (Finset.union_empty _)
    (Finset.disjoint_empty_right _) h1A h2B (by norm_num) (by norm_num) hy0
  dsimp only
  simp only [Finset.card_empty, Nat.cast_zero]
  generalize ha : pp.A.card = a at hab hlo hhi ⊢
  generalize hb : pp.B.card = b at hab hlo hhi ⊢
  generalize hc : pp.C.card = c at hlo ⊢
  have hcnn : (0 : ℝ) ≤ (c : ℝ) := Nat.cast_nonneg c
  have hcterm_nn : ∀ p q : ℝ, 0 ≤ p → q ≤ 0 →
      0 ≤ (c : ℝ) * ((1 - (2 / 3 : ℝ)) * (p ^ 2 + q ^ 2) - 2 * p * q) / (2 - (2 / 3 : ℝ)) := by
    intro p q hp hq
    apply div_nonneg (mul_nonneg hcnn _) (by norm_num)
    nlinarith [sq_nonneg p, sq_nonneg q]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro ⟨ha0, hb0⟩
    have ha' : a = 0 := Nat.cast_eq_zero.mp ha0
    have hb' : b = 0 := Nat.cast_eq_zero.mp hb0
    subst ha'; subst hb'
    have hc1 : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast (show 1 ≤ c by omega)
    norm_num; linarith
  · rintro ⟨ha0, hb0⟩
    have ha' : a = 0 := Nat.cast_eq_zero.mp ha0
    have hbpos : 1 ≤ b := Nat.pos_of_ne_zero (fun h => hb0 (by simp [h]))
    subst ha'
    have hct := hcterm_nn (2 + (0 : ℝ)) (-(2 + (b : ℝ))) (by positivity)
      (by have : (0 : ℝ) ≤ (b : ℝ) := Nat.cast_nonneg b; linarith)
    have hb7 : b ≤ 7 := by omega
    interval_cases b <;> refine ⟨by norm_num, ?_⟩ <;> (norm_num at hct ⊢; linarith)
  · rintro ⟨ha0, hb0⟩
    have ha' : a ≠ 0 := fun h => ha0 (by simp [h])
    have hb' : b = 0 := Nat.cast_eq_zero.mp hb0
    omega
  · rintro ⟨ha0, hb0⟩
    have hapos : 1 ≤ a := Nat.pos_of_ne_zero (fun h => ha0 (by simp [h]))
    have hbpos : 1 ≤ b := Nat.pos_of_ne_zero (fun h => hb0 (by simp [h]))
    have hct := hcterm_nn (2 + (a : ℝ)) (-(2 + (b : ℝ))) (by positivity)
      (by have : (0 : ℝ) ≤ (b : ℝ) := Nat.cast_nonneg b; linarith)
    have ha3 : a ≤ 3 := by omega
    have hb6 : b ≤ 6 := by omega
    interval_cases a <;> interval_cases b <;> try omega
    all_goals
      refine ⟨by norm_num, by norm_num, ?_⟩
      norm_num at hct ⊢; linarith

lemma small_s1_l1_bound {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    [DecidableRel Gᶜ.Adj] (pp : PathPartition G) (hs : pp.P.card = 1)
    (hab : pp.A.card ≤ pp.B.card)
    (hlo : 1 ≤ pp.A.card + pp.B.card + pp.C.card)
    (hhi : pp.A.card + pp.B.card ≤ 7)
    (hl1 : ∀ w ∈ pp.S1, (pp.A.filter (G.Adj w)).card ≤ 1)
    (hl2 : ∀ u ∈ pp.S2, (pp.B.filter (G.Adj u)).card ≤ 1)
    {y : Fin n → ℝ} (hy0 : ∑ i, y i = 0) :
    (1 / 2 : ℝ) * ∑ i, y i ^ 2 ≤ quad Gᶜ y := by
  classical
  obtain ⟨u1, hS1⟩ := Finset.card_eq_one.mp (pp.card_S1.trans hs)
  obtain ⟨u2, hS2⟩ := Finset.card_eq_one.mp (pp.card_S2.trans hs)
  have hu1_S1 : u1 ∈ pp.S1 := by rw [hS1]; simp
  have hu2_S2 : u2 ∈ pp.S2 := by rw [hS2]; simp
  have hex_split : ∀ (X : Finset (Fin n)) (v : Fin n),
      (X.filter (G.Adj v)).card ≤ 1 →
      ∃ X0 X1 : Finset (Fin n), X0 ∪ X1 = X ∧ Disjoint X0 X1 ∧
        X1.card = min X.card 1 ∧ (∀ x ∈ X0, ¬ G.Adj v x) := by
    intro X v hv
    by_cases hXe : X = ∅
    · subst hXe; exact ⟨∅, ∅, by simp, by simp, by simp, by simp⟩
    · have hXne : X.Nonempty := Finset.nonempty_iff_ne_empty.mpr hXe
      by_cases hf : (X.filter (G.Adj v)).Nonempty
      · obtain ⟨x0, hx0⟩ := Finset.card_eq_one.mp (le_antisymm hv (Finset.card_pos.mpr hf))
        have hx0X : x0 ∈ X := (Finset.mem_filter.mp (by rw [hx0]; simp)).1
        refine ⟨X.erase x0, {x0}, ?_, by simp, ?_, ?_⟩
        · rw [Finset.union_comm, Finset.singleton_union, Finset.insert_erase hx0X]
        · simp [Nat.min_eq_right (Nat.succ_le_of_lt hXne.card_pos)]
        · intro x hx hadj
          have hm : x ∈ X.filter (G.Adj v) :=
            Finset.mem_filter.mpr ⟨Finset.mem_of_mem_erase hx, hadj⟩
          rw [hx0, Finset.mem_singleton] at hm
          exact (Finset.mem_erase.mp hx).1 hm
      · obtain ⟨x0, hx0X⟩ := hXne
        refine ⟨X.erase x0, {x0}, ?_, by simp, ?_, ?_⟩
        · rw [Finset.union_comm, Finset.singleton_union, Finset.insert_erase hx0X]
        · simp [Nat.min_eq_right (Nat.succ_le_of_lt (Finset.card_pos.mpr ⟨x0, hx0X⟩))]
        · intro x hx hadj
          exact hf ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_of_mem_erase hx, hadj⟩⟩
  obtain ⟨A0, A1, hAu, hAd, hA1c, hA0na⟩ := hex_split pp.A u1 (hl1 u1 hu1_S1)
  obtain ⟨B0, B1, hBu, hBd, hB1c, hB0na⟩ := hex_split pp.B u2 (hl2 u2 hu2_S2)
  have hA0c : A0.card + A1.card = pp.A.card := by rw [← Finset.card_union_of_disjoint hAd, hAu]
  have hB0c : B0.card + B1.card = pp.B.card := by rw [← Finset.card_union_of_disjoint hBd, hBu]
  apply g3_small_bound pp hS1 hS2 A0 A1 B0 B1 hAu hAd hBu hBd hA0na hB0na
    (by norm_num) (by norm_num) hy0
  dsimp only
  generalize ha : pp.A.card = a at hab hlo hhi hA1c hA0c ⊢
  generalize hb : pp.B.card = b at hab hlo hhi hB1c hB0c ⊢
  generalize hc : pp.C.card = c at hlo ⊢
  generalize ha0 : A0.card = a0 at hA0c ⊢
  generalize ha1 : A1.card = a1 at hA1c hA0c ⊢
  generalize hb0 : B0.card = b0 at hB0c ⊢
  generalize hb1 : B1.card = b1 at hB1c hB0c ⊢
  have hcnn : (0 : ℝ) ≤ (c : ℝ) := Nat.cast_nonneg c
  have hcterm_nn : ∀ p q : ℝ, 0 ≤ p → q ≤ 0 →
      0 ≤ (c : ℝ) * ((1 - (1 / 2 : ℝ)) * (p ^ 2 + q ^ 2) - 2 * p * q) / (2 - (1 / 2 : ℝ)) := by
    intro p q hp hq
    apply div_nonneg (mul_nonneg hcnn _) (by norm_num)
    nlinarith [sq_nonneg p, sq_nonneg q]
  have ha3 : a ≤ 3 := by omega
  have hb7 : b ≤ 7 := by omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro ⟨h0a, h0b⟩
    have ha0' : a0 = 0 := Nat.cast_eq_zero.mp h0a
    have hb0' : b0 = 0 := Nat.cast_eq_zero.mp h0b
    have hct := hcterm_nn (2 + (a : ℝ)) (-(2 + (b : ℝ))) (by positivity)
      (by have : (0 : ℝ) ≤ (b : ℝ) := Nat.cast_nonneg b; linarith)
    have ha1_le : a ≤ 1 := by omega
    have hb1_le : b ≤ 1 := by omega
    interval_cases a <;> interval_cases b <;> try omega
    · have ha1v : a1 = 0 := by omega
      have hb1v : b1 = 0 := by omega
      have hc1 : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast (show 1 ≤ c by omega)
      subst ha0'; subst hb0'; subst ha1v; subst hb1v
      norm_num; linarith
    · have ha1v : a1 = 0 := by omega
      have hb1v : b1 = 1 := by omega
      subst ha0'; subst hb0'; subst ha1v; subst hb1v
      norm_num at hct ⊢; linarith
    · have ha1v : a1 = 1 := by omega
      have hb1v : b1 = 1 := by omega
      subst ha0'; subst hb0'; subst ha1v; subst hb1v
      norm_num at hct ⊢; linarith
  · rintro ⟨h0a, h0b⟩
    have ha0' : a0 = 0 := Nat.cast_eq_zero.mp h0a
    have hb0p : 1 ≤ b0 := Nat.pos_of_ne_zero (fun h => h0b (by simp [h]))
    have hct := hcterm_nn (2 + (a : ℝ)) (-(2 + (b : ℝ))) (by positivity)
      (by have : (0 : ℝ) ≤ (b : ℝ) := Nat.cast_nonneg b; linarith)
    have ha1_le : a ≤ 1 := by omega
    have hb1v : b1 = 1 := by omega
    have hb0v : b0 = b - 1 := by omega
    subst ha0'; subst hb1v; subst hb0v
    interval_cases a <;> interval_cases b <;> try omega
    all_goals
      have ha1v : a1 = min _ 1 := hA1c
      subst ha1v
      refine ⟨by norm_num, ?_⟩
      norm_num at hct ⊢; linarith
  · rintro ⟨h0a, h0b⟩
    have ha0p : 1 ≤ a0 := Nat.pos_of_ne_zero (fun h => h0a (by simp [h]))
    have hb0' : b0 = 0 := Nat.cast_eq_zero.mp h0b
    omega
  · rintro ⟨h0a, h0b⟩
    have ha0p : 1 ≤ a0 := Nat.pos_of_ne_zero (fun h => h0a (by simp [h]))
    have hb0p : 1 ≤ b0 := Nat.pos_of_ne_zero (fun h => h0b (by simp [h]))
    have hct := hcterm_nn (2 + (a : ℝ)) (-(2 + (b : ℝ))) (by positivity)
      (by have : (0 : ℝ) ≤ (b : ℝ) := Nat.cast_nonneg b; linarith)
    have ha1v : a1 = 1 := by omega
    have hb1v : b1 = 1 := by omega
    have ha0v : a0 = a - 1 := by omega
    have hb0v : b0 = b - 1 := by omega
    subst ha1v; subst hb1v; subst ha0v; subst hb0v
    interval_cases a <;> interval_cases b <;> try omega
    all_goals
      refine ⟨by norm_num, by norm_num, ?_⟩
      norm_num at hct ⊢; linarith

end SmallCases

section MainTheorem

set_option maxHeartbeats 600000 in
theorem algebraic_connectivity_sum_ge_one {n : ℕ} (hn : 2 ≤ n)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] [DecidableRel Gᶜ.Adj]
    {μ μc : ℝ} {x y : Fin n → ℝ}
    (hx0 : ∑ i, x i = 0) (hx1 : ∑ i, x i ^ 2 = 1) (hqx : quad G x = μ)
    (heigG : ∀ i, ∑ j ∈ Finset.univ.filter (G.Adj i), (x i - x j) = μ * x i)
    (hy0 : ∑ i, y i = 0) (hy1 : ∑ i, y i ^ 2 = 1) (hqy : quad Gᶜ y = μc)
    (heigGc : ∀ i, ∑ j ∈ Finset.univ.filter (Gᶜ.Adj i), (y i - y j) = μc * y i) :
    1 ≤ μ + μc := by
  classical
  have hmu0 : 0 ≤ μ := hqx ▸ quad_nonneg G x
  have hmuc0 : 0 ≤ μc := hqy ▸ quad_nonneg Gᶜ y
  by_contra hlt
  push Not at hlt
  have hmu1 : μ < 1 := by linarith
  have hmuc1 : μc < 1 := by linarith
  have hdir : ∀ (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] [DecidableRel Hᶜ.Adj]
      (μH μHc : ℝ) (u v : Fin n → ℝ),
      0 ≤ μH → μH < 1 → 0 ≤ μHc → μHc < 1 → μH + μHc < 1 →
      (∑ i, u i = 0) → (∑ i, u i ^ 2 = 1) → quad H u = μH →
      (∀ i, ∑ j ∈ Finset.univ.filter (H.Adj i), (u i - u j) = μH * u i) →
      (∑ i, v i = 0) → (∑ i, v i ^ 2 = 1) → quad Hᶜ v = μHc →
      (∀ i, ∑ j ∈ Finset.univ.filter (Hᶜ.Adj i), (v i - v j) = μHc * v i) →
      (∃ i j, 1 < (u i - u j) ^ 2) → False := by
    intro H _ _ μH μHc u v hμH0 hμH1 hμHc0 hμHc1 hsumlt
      hu0 hu1 hqu heigH hv0 hv1 hqv heigHc ⟨i0, j0, hbig⟩
    have hne_univ : (Finset.univ : Finset (Fin n)).Nonempty :=
      ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
    obtain ⟨v1, _, hv1max⟩ := Finset.exists_max_image Finset.univ u hne_univ
    obtain ⟨v2, _, hv2min⟩ := Finset.exists_min_image Finset.univ u hne_univ
    have hv1max' : ∀ i, u i ≤ u v1 := fun i => hv1max i (Finset.mem_univ i)
    have hv2min' : ∀ i, u v2 ≤ u i := fun i => hv2min i (Finset.mem_univ i)
    obtain ⟨hu2neg, hu1pos, _, _, hna, hnc⟩ :=
      eigen_neighbor_bounds hu0 hu1 heigH hμH1 hv1max' hv2min'
    have hv12 : v1 ≠ v2 := fun h => by linarith [h ▸ hu1pos]
    have hspread : 1 ≤ |u v1 - u v2| := by
      have hle : |u i0 - u j0| ≤ u v1 - u v2 := by
        rw [abs_le]
        exact ⟨by linarith [hv1max' j0, hv2min' i0], by linarith [hv1max' i0, hv2min' j0]⟩
      have hgt1 : 1 < |u i0 - u j0| := by
        have h1 : (1 : ℝ) ^ 2 < |u i0 - u j0| ^ 2 := by rw [one_pow, sq_abs]; exact hbig
        nlinarith [abs_nonneg (u i0 - u j0)]
      have hpos : 0 ≤ u v1 - u v2 := by linarith
      rw [abs_of_nonneg hpos]; linarith
    have hex3 : ∃ a b, H.Adj v1 a ∧ H.Adj a b ∧ H.Adj b v2 := by
      by_contra hno3; push Not at hno3
      obtain ⟨w1, _, hw1max⟩ := Finset.exists_max_image Finset.univ v hne_univ
      obtain ⟨w2, _, hw2min⟩ := Finset.exists_min_image Finset.univ v hne_univ
      obtain ⟨hv2neg, hv1pos, _, _, hcna, hcnc⟩ :=
        eigen_neighbor_bounds hv0 hv1 heigHc hμHc1 (fun i => hw1max i (Finset.mem_univ i))
          (fun i => hw2min i (Finset.mem_univ i))
      have hw12 : w1 ≠ w2 := fun h => by linarith [h ▸ hv1pos]
      exact no_len3_path_contradiction hv12 hna hnc (fun a b ⟨h1, h2, h3⟩ => hno3 a b h1 h2 h3)
        hw12 hcna hcnc
    obtain ⟨pp0, hpv1, hpv2⟩ := exists_path_partition H hv12 hna hnc hex3
    let pp : PathPartition H := if pp0.A.card ≤ pp0.B.card then pp0 else pp0.swap
    have hab : pp.A.card ≤ pp.B.card := by
      dsimp [pp]; split_ifs with h
      · exact h
      · dsimp [PathPartition.swap]; omega
    have hspread_pp : 1 ≤ |u pp.v1 - u pp.v2| := by
      dsimp [pp]; split_ifs
      · rwa [hpv1, hpv2]
      · dsimp [PathPartition.swap]; rw [hpv1, hpv2, abs_sub_comm]; exact hspread
    let s : ℕ := pp.P.card
    have hs1 : 1 ≤ s := pp.hPne.card_pos
    let l1 : ℕ := pp.S1.sup (fun w => (pp.A.filter (H.Adj w)).card)
    let l2 : ℕ := pp.S2.sup (fun a => (pp.B.filter (H.Adj a)).card)
    let l : ℕ := max l1 l2
    have hl1 : ∀ w ∈ pp.S1, (pp.A.filter (H.Adj w)).card ≤ l := fun w hw =>
      (Finset.le_sup (f := fun w => (pp.A.filter (H.Adj w)).card) hw).trans (le_max_left _ _)
    have hl2 : ∀ a ∈ pp.S2, (pp.B.filter (H.Adj a)).card ≤ l := fun a ha =>
      (Finset.le_sup (f := fun a => (pp.B.filter (H.Adj a)).card) ha).trans (le_max_right _ _)
    have hmuH_lb : ((s : ℝ) - 1) / 3 + ((l : ℝ) + 1) / ((l : ℝ) + 3) ≤ μH := by
      rw [← hqu]
      have hS1ne : pp.S1.Nonempty := by rw [pp.hS1]; exact pp.hPne.image _
      have hS2ne : pp.S2.Nonempty := by rw [pp.hS2]; exact pp.hPne.image _
      rcases le_total l2 l1 with h12 | h21
      · have hl_eq : l = l1 := max_eq_left h12
        obtain ⟨w0, hw0S1, hw0max⟩ :=
          Finset.exists_max_image pp.S1 (fun w => (pp.A.filter (H.Adj w)).card) hS1ne
        have hcard_eq : (pp.A.filter (H.Adj w0)).card = l := by
          rw [hl_eq]
          exact le_antisymm (Finset.le_sup (f := fun w => (pp.A.filter (H.Adj w)).card) hw0S1)
            (Finset.sup_le (fun w hw => hw0max w hw))
        rw [pp.hS1] at hw0S1
        obtain ⟨e0, he0P, he0w⟩ := Finset.mem_image.mp hw0S1
        have hlb := pp.mu_lower_from_star hspread_pp e0 he0P (pp.A.filter (H.Adj e0.2))
          (Finset.filter_subset _ _) (fun t ht => (Finset.mem_filter.mp ht).2.symm)
        rw [he0w, hcard_eq] at hlb; exact hlb
      · have hl_eq : l = l2 := max_eq_right h21
        obtain ⟨u0, hu0S2, hu0max⟩ :=
          Finset.exists_max_image pp.S2 (fun a => (pp.B.filter (H.Adj a)).card) hS2ne
        have hcard_eq : (pp.B.filter (H.Adj u0)).card = l := by
          rw [hl_eq]
          exact le_antisymm (Finset.le_sup (f := fun a => (pp.B.filter (H.Adj a)).card) hu0S2)
            (Finset.sup_le (fun a ha => hu0max a ha))
        rw [pp.hS2] at hu0S2
        obtain ⟨e0, he0P, he0u⟩ := Finset.mem_image.mp hu0S2
        have he0sw : e0.swap ∈ pp.swap.P := Finset.mem_image.mpr ⟨e0, he0P, rfl⟩
        have hsp_sw : 1 ≤ |u pp.swap.v1 - u pp.swap.v2| := by
          dsimp [PathPartition.swap]; rwa [abs_sub_comm]
        have hlb := pp.swap.mu_lower_from_star hsp_sw e0.swap he0sw
          (pp.B.filter (H.Adj e0.1)) (Finset.filter_subset _ _)
          (fun t ht => (Finset.mem_filter.mp ht).2.symm)
        have hswPcard : pp.swap.P.card = s :=
          Finset.card_image_of_injective pp.P Prod.swap_injective
        rw [hswPcard, he0u, hcard_eq] at hlb; exact hlb
    have hmuHc_gen : (n : ℝ) / ((n : ℝ) + 2 + 3 * (s : ℝ) ^ 2 + 6 * (s : ℝ) * (l : ℝ)) ≤ μHc := by
      have hgen := pp.mu_compl_general_bound hab l hl1 hl2 hv0
      rw [hv1, mul_one, hqv] at hgen
      have hden : (0 : ℝ) < (n : ℝ) + 2 + 3 * (s : ℝ) ^ 2 + 6 * (s : ℝ) * (l : ℝ) := by
        have h1 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        have h2 : (0 : ℝ) ≤ (s : ℝ) := Nat.cast_nonneg s
        have h3 : (0 : ℝ) ≤ (l : ℝ) := Nat.cast_nonneg l
        nlinarith
      exact (div_le_iff₀ hden).mpr (by linarith)
    by_cases hs3 : 3 ≤ s
    · have hs3r : (3 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs3
      have hlpos : (1 / 3 : ℝ) ≤ ((l : ℝ) + 1) / ((l : ℝ) + 3) := by
        have hlr : (0 : ℝ) ≤ (l : ℝ) := Nat.cast_nonneg l
        rw [div_le_div_iff₀ (by norm_num) (by linarith)]; linarith
      linarith
    have hs12 : s = 1 ∨ s = 2 := by omega
    rcases hs12 with hs1_eq | hs2_eq
    · by_cases hn12 : 12 ≤ n
      · have hnr : (12 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn12
        have hsr : (s : ℝ) = 1 := by exact_mod_cast hs1_eq
        have hlr : (0 : ℝ) ≤ (l : ℝ) := Nat.cast_nonneg l
        rw [hsr] at hmuH_lb hmuHc_gen
        have h1 : (12 : ℝ) / (17 + 6 * (l : ℝ)) ≤ (n : ℝ) / ((n : ℝ) + 2 + 3 * 1 ^ 2 + 6 * 1 * (l : ℝ)) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
        have h2 : (1 : ℝ) < ((l : ℝ) + 1) / ((l : ℝ) + 3) + 12 / (17 + 6 * (l : ℝ)) := by
          have hd1 : (0 : ℝ) < (l : ℝ) + 3 := by positivity
          have hd2 : (0 : ℝ) < 17 + 6 * (l : ℝ) := by positivity
          have hmul : ((l : ℝ) + 3) * (17 + 6 * (l : ℝ)) <
              ((l : ℝ) + 1) * (17 + 6 * (l : ℝ)) + 12 * ((l : ℝ) + 3) := by nlinarith
          have hdiv := div_lt_div_of_pos_right hmul (mul_pos hd1 hd2)
          have hlhs : ((l : ℝ) + 3) * (17 + 6 * (l : ℝ)) / (((l : ℝ) + 3) * (17 + 6 * (l : ℝ))) = 1 :=
            div_self (mul_pos hd1 hd2).ne'
          have hrhs : (((l : ℝ) + 1) * (17 + 6 * (l : ℝ)) + 12 * ((l : ℝ) + 3)) /
              (((l : ℝ) + 3) * (17 + 6 * (l : ℝ))) =
              ((l : ℝ) + 1) / ((l : ℝ) + 3) + 12 / (17 + 6 * (l : ℝ)) := by
            field_simp [hd1.ne', hd2.ne']
          linarith
        linarith
      · have hncard := pp.card_eq
        have habc_le : pp.A.card + pp.B.card + pp.C.card ≤ 7 := by dsimp [s] at hs1_eq; omega
        by_cases habc0 : pp.A.card + pp.B.card + pp.C.card = 0
        · obtain ⟨e0, hPe0⟩ := Finset.card_eq_one.mp hs1_eq
          have hS1e : pp.S1 = {e0.2} := by rw [pp.hS1, hPe0]; simp
          have hS2e : pp.S2 = {e0.1} := by rw [pp.hS2, hPe0]; simp
          have hAe : pp.A = ∅ := Finset.card_eq_zero.mp (by omega)
          have hBe : pp.B = ∅ := Finset.card_eq_zero.mp (by omega)
          have hCe : pp.C = ∅ := Finset.card_eq_zero.mp (by omega)
          have hcov4 : ∀ z : Fin n, z = pp.v1 ∨ z = e0.1 ∨ z = e0.2 ∨ z = pp.v2 := by
            intro z; have hz := pp.cover z
            rw [hS1e, hS2e, hAe, hBe, hCe] at hz
            simp only [Finset.mem_singleton, Finset.notMem_empty, or_false] at hz; tauto
          have he0P : e0 ∈ pp.P := by rw [hPe0]; simp
          have hed := pp.hPedge e0 he0P
          have hu1_S1 : e0.2 ∈ pp.S1 := by rw [hS1e]; simp
          have hu2_S2 : e0.1 ∈ pp.S2 := by rw [hS2e]; simp
          have h1e1 : pp.v1 ≠ e0.1 := fun h => pp.v1_not_S2 (h ▸ hu2_S2)
          have h1e2 : pp.v1 ≠ e0.2 := fun h => pp.v1_not_S1 (h ▸ hu1_S1)
          have he1e2 : e0.1 ≠ e0.2 := fun h => Finset.disjoint_left.mp pp.disj_S1_S2 hu1_S1 (h ▸ hu2_S2)
          have he12 : e0.1 ≠ pp.v2 := fun h => pp.v2_not_S2 (h ▸ hu2_S2)
          have he22 : e0.2 ≠ pp.v2 := fun h => pp.v2_not_S1 (h ▸ hu1_S1)
          have hG4 := quad_P4_ge_half h1e1 h1e2 pp.hv12 he1e2 he12 he22 hcov4
            hed.1 hed.2.1 hed.2.2 hu0
          have hGc4 := quad_P4_ge_half h1e2.symm he22 he1e2.symm pp.hv12 h1e1 he12.symm
            (fun z => by have := hcov4 z; tauto)
            (pp.compl_adj_v1_S1 hu1_S1).symm pp.compl_adj_v1_v2 (pp.compl_adj_v2_S2 hu2_S2) hv0
          rw [hu1, mul_one, hqu] at hG4
          rw [hv1, mul_one, hqv] at hGc4
          linarith
        · have hlo : 1 ≤ pp.A.card + pp.B.card + pp.C.card := by omega
          have hab_le : pp.A.card + pp.B.card ≤ 7 := by omega
          by_cases hl2ge : 2 ≤ l
          · have hmuH2 : (3 / 5 : ℝ) ≤ μH := by
              have hsr : (s : ℝ) = 1 := by exact_mod_cast hs1_eq
              have hl2r : (2 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl2ge
              rw [hsr] at hmuH_lb
              have : (3 / 5 : ℝ) ≤ ((l : ℝ) + 1) / ((l : ℝ) + 3) := by
                rw [div_le_div_iff₀ (by norm_num) (by positivity)]; linarith
              linarith
            have hmuHc2 := small_s1_l2_bound pp hs1_eq hab hab_le hv0
            rw [hv1, mul_one, hqv] at hmuHc2; linarith
          · have hl01 : l = 0 ∨ l = 1 := by omega
            rcases hl01 with hl0 | hl1_eq
            · have hmuH0 : (1 / 3 : ℝ) ≤ μH := by
                have hsr : (s : ℝ) = 1 := by exact_mod_cast hs1_eq
                have hlr : (l : ℝ) = 0 := by exact_mod_cast hl0
                rw [hsr, hlr] at hmuH_lb; norm_num at hmuH_lb; linarith
              have hmuHc0 := small_s1_l0_bound pp hs1_eq hab hlo hab_le
                (fun w hw => hl0 ▸ hl1 w hw) (fun a ha => hl0 ▸ hl2 a ha) hv0
              rw [hv1, mul_one, hqv] at hmuHc0; linarith
            · have hmuH1 : (1 / 2 : ℝ) ≤ μH := by
                have hsr : (s : ℝ) = 1 := by exact_mod_cast hs1_eq
                have hlr : (l : ℝ) = 1 := by exact_mod_cast hl1_eq
                rw [hsr, hlr] at hmuH_lb; norm_num at hmuH_lb; linarith
              have hmuHc1 := small_s1_l1_bound pp hs1_eq hab hlo hab_le
                (fun w hw => hl1_eq ▸ hl1 w hw) (fun a ha => hl1_eq ▸ hl2 a ha) hv0
              rw [hv1, mul_one, hqv] at hmuHc1; linarith
    · by_cases hl3 : 3 ≤ l
      · have hsr : (s : ℝ) = 2 := by exact_mod_cast hs2_eq
        have hl3r : (3 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl3
        rw [hsr] at hmuH_lb
        have : (2 / 3 : ℝ) ≤ ((l : ℝ) + 1) / ((l : ℝ) + 3) := by
          rw [div_le_div_iff₀ (by norm_num) (by positivity)]; linarith
        linarith
      · by_cases hn10 : 10 ≤ n
        · have hnr : (10 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn10
          have hsr : (s : ℝ) = 2 := by exact_mod_cast hs2_eq
          rw [hsr] at hmuH_lb hmuHc_gen
          have hmono : (10 : ℝ) / (24 + 12 * (l : ℝ)) ≤
              (n : ℝ) / ((n : ℝ) + 2 + 3 * 2 ^ 2 + 6 * 2 * (l : ℝ)) := by
            have hlr : (0 : ℝ) ≤ (l : ℝ) := Nat.cast_nonneg l
            rw [div_le_div_iff₀ (by linarith) (by linarith)]
            nlinarith
          have hl2le : l ≤ 2 := by omega
          interval_cases l
          · norm_num at hmuH_lb hmono hmuHc_gen; linarith
          · norm_num at hmuH_lb hmono hmuHc_gen; linarith
          · norm_num at hmuH_lb hmono hmuHc_gen; linarith
        · have hncard := pp.card_eq
          have hab_le : pp.A.card + pp.B.card ≤ 3 := by dsimp [s] at hs2_eq; omega
          have hmuH2 : (2 / 3 : ℝ) ≤ μH := by
            have hsr : (s : ℝ) = 2 := by exact_mod_cast hs2_eq
            rw [hsr] at hmuH_lb
            have : (1 / 3 : ℝ) ≤ ((l : ℝ) + 1) / ((l : ℝ) + 3) := by
              have hlr : (0 : ℝ) ≤ (l : ℝ) := Nat.cast_nonneg l
              rw [div_le_div_iff₀ (by norm_num) (by linarith)]; linarith
            linarith
          have hmuHc2 := small_s2_bound pp hs2_eq hab hab_le hv0
          rw [hv1, mul_one, hqv] at hmuHc2; linarith
  by_cases hMx : ∀ i j, (x i - x j) ^ 2 ≤ 1
  · by_cases hMy : ∀ i j, (y i - y j) ^ 2 ≤ 1
    · have h1 := step1_small_spread (G := G) hx0 hy0 hx1 hy1 hMx hMy
      linarith
    · push Not at hMy
      have hcc_adj : ∀ i j : Fin n, Gᶜᶜ.Adj i j ↔ G.Adj i j := by
        intro i j
        simp only [SimpleGraph.compl_adj]
        constructor
        · rintro ⟨hne, hna⟩; by_contra ha; exact hna ⟨hne, ha⟩
        · intro ha; exact ⟨G.ne_of_adj ha, fun ⟨_, hna⟩ => hna ha⟩
      have hqcc : quad Gᶜᶜ x = μ := by
        rw [← hqx]; unfold quad; congr 1; ext e
        simp only [Finset.mem_filter, hcc_adj]
      have heigcc : ∀ i, ∑ j ∈ Finset.univ.filter (Gᶜᶜ.Adj i), (x i - x j) = μ * x i := by
        intro i; rw [← heigG i]; congr 1; ext j
        simp only [Finset.mem_filter, hcc_adj]
      exact hdir Gᶜ μc μ y x hmuc0 hmuc1 hmu0 hmu1 (by linarith)
        hy0 hy1 hqy heigGc hx0 hx1 hqcc heigcc hMy
  · push Not at hMx
    exact hdir G μ μc x y hmu0 hmu1 hmuc0 hmuc1 hlt
      hx0 hx1 hqx heigG hy0 hy1 hqy heigGc hMx

private lemma abs_sub_abs_sq (u v : ℝ) :
    (|u + v| - |u - v|) ^ 2 = 4 * min (u ^ 2) (v ^ 2) := by
  have h1 : (|u + v| - |u - v|) ^ 2 = (u + v) ^ 2 + (u - v) ^ 2 - 2 * |u ^ 2 - v ^ 2| := by
    have hmul : |u + v| * |u - v| = |u ^ 2 - v ^ 2| := by
      rw [← abs_mul]; congr 1; ring
    nlinarith [sq_abs (u + v), sq_abs (u - v)]
  rw [h1]
  rcases le_total (u ^ 2) (v ^ 2) with h | h
  · rw [min_eq_left h, abs_of_nonpos (by linarith)]; ring
  · rw [min_eq_right h, abs_of_nonneg (by linarith)]; ring

end MainTheorem

end OMA.MO267876

open Finset OMA.MO267876 in
theorem OMA.solution : type_of% @OMA.S_mo_267876.main := by
  classical
  intro n f g hf hg hfg
  by_cases hn : n ≤ 1
  · have hfn : n = 0 ∨ n = 1 := by omega
    rcases hfn with rfl | rfl
    · simp
    · have hf0 : f 0 = 0 := by simpa using hf
      have hg0 : g 0 = 0 := by simpa using hg
      simp only [Fin.sum_univ_one, hf0, hg0, sub_zero, zero_pow (by decide : 2 ≠ 0)]
      exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  · have hn2 : 2 ≤ n := by omega
    let p : Fin n → ℝ := fun i => f i + g i
    let q : Fin n → ℝ := fun i => f i - g i
    have hp0 : ∑ i, p i = 0 := by
      simp only [p, Finset.sum_add_distrib, hf, hg, add_zero]
    have hq0 : ∑ i, q i = 0 := by
      simp only [q, Finset.sum_sub_distrib, hf, hg, sub_zero]
    have hpq_norm : ∑ i, q i ^ 2 ≤ ∑ i, p i ^ 2 := by
      have hdiff : ∑ i, p i ^ 2 - ∑ i, q i ^ 2 = 4 * ∑ i, f i * g i := by
        rw [← Finset.sum_sub_distrib, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun _ _ => by dsimp [p, q]; ring)
      linarith
    let G : SimpleGraph (Fin n) := {
      Adj := fun i j => i ≠ j ∧ (p i - p j) ^ 2 ≤ (q i - q j) ^ 2
      symm := ⟨fun i j ⟨hne, hle⟩ => ⟨hne.symm, by
        linarith [show (p i - p j) ^ 2 = (p j - p i) ^ 2 by ring,
          show (q i - q j) ^ 2 = (q j - q i) ^ 2 by ring]⟩⟩
      loopless := ⟨fun i ⟨hne, _⟩ => hne rfl⟩
    }
    obtain ⟨μ, x, hμ0, hx0, hx1, hqx, hminG, heigG⟩ := exists_minimizer hn2 G
    obtain ⟨μc, y, hμc0, hy0, hy1, hqy, hminGc, heigGc⟩ := exists_minimizer hn2 Gᶜ
    have hsum1 : 1 ≤ μ + μc :=
      algebraic_connectivity_sum_ge_one hn2 G hx0 hx1 hqx heigG hy0 hy1 hqy heigGc
    have hrhs_eq :
        ∑ e ∈ (Finset.univ.filter (fun e : Fin n × Fin n => e.1 < e.2)),
          (|f e.1 - f e.2| - |g e.1 - g e.2|) ^ 2 =
        quad G p + quad Gᶜ q := by
      have hpt : ∀ e ∈ pairs n, (|f e.1 - f e.2| - |g e.1 - g e.2|) ^ 2 =
          min ((p e.1 - p e.2) ^ 2) ((q e.1 - q e.2) ^ 2) := by
        intro e _
        have h1 : f e.1 - f e.2 = (p e.1 - p e.2) / 2 + (q e.1 - q e.2) / 2 := by dsimp [p, q]; ring
        have h2 : g e.1 - g e.2 = (p e.1 - p e.2) / 2 - (q e.1 - q e.2) / 2 := by dsimp [p, q]; ring
        rw [h1, h2, abs_sub_abs_sq]
        rcases le_total (((p e.1 - p e.2) / 2) ^ 2) (((q e.1 - q e.2) / 2) ^ 2) with h | h
        · rw [min_eq_left h, min_eq_left (by linarith)]; ring
        · rw [min_eq_right h, min_eq_right (by linarith)]; ring
      change ∑ e ∈ pairs n, (|f e.1 - f e.2| - |g e.1 - g e.2|) ^ 2 = _
      rw [Finset.sum_congr rfl hpt]
      rw [← Finset.sum_filter_add_sum_filter_not (pairs n) (fun e => G.Adj e.1 e.2)]
      unfold quad
      congr 1
      · exact Finset.sum_congr rfl (fun e he => min_eq_left (Finset.mem_filter.mp he).2.2)
      · have hfc : (pairs n).filter (fun e => Gᶜ.Adj e.1 e.2) =
            (pairs n).filter (fun e => ¬ G.Adj e.1 e.2) := by
          ext e
          simp only [Finset.mem_filter, pairs, Finset.mem_univ, true_and, SimpleGraph.compl_adj]
          exact ⟨fun ⟨h, _, hna⟩ => ⟨h, hna⟩, fun ⟨h, hna⟩ => ⟨h, ne_of_lt h, hna⟩⟩
        rw [hfc]
        apply Finset.sum_congr rfl; intro e he
        have he' := Finset.mem_filter.mp he
        have hlt : e.1 < e.2 := (Finset.mem_filter.mp he'.1).2
        have hna : ¬ (p e.1 - p e.2) ^ 2 ≤ (q e.1 - q e.2) ^ 2 := fun hle =>
          he'.2 ⟨ne_of_lt hlt, hle⟩
        exact min_eq_right (le_of_lt (not_le.mp hna))
    rw [hrhs_eq]
    have hGp : μ * ∑ i, q i ^ 2 ≤ quad G p :=
      (mul_le_mul_of_nonneg_left hpq_norm hμ0).trans (hminG p hp0)
    have hGcq : μc * ∑ i, q i ^ 2 ≤ quad Gᶜ q := hminGc q hq0
    have hqnn : 0 ≤ ∑ i, q i ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    change ∑ i, q i ^ 2 ≤ quad G p + quad Gᶜ q
    nlinarith
