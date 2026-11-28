import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R1_H1_R1_H1_R2
import Mathlib

namespace E142W
open Finset

variable {p : ℕ} [NeZero p]

lemma e_eq (a : ZMod p) :
    Complex.exp (2 * Real.pi * Complex.I * ((a.val : ℕ) : ℂ) / (p : ℂ)) =
      (ZMod.stdAddChar a : ℂ) := by
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]

lemma sq_norm_eq (z : ℂ) : ((‖z‖ ^ 2 : ℝ) : ℂ) = z * (starRingEnd ℂ) z := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

lemma parseval (u : ZMod p → ℝ) :
    ∑ ξ : ZMod p, ‖∑ t : ZMod p, (u t : ℂ) * ZMod.stdAddChar (t * ξ)‖ ^ 2 =
      (p : ℝ) * ∑ t : ZMod p, (u t) ^ 2 := by
  classical
  apply Complex.ofReal_injective
  rw [Complex.ofReal_sum]
  simp_rw [sq_norm_eq]
  push_cast
  simp_rw [map_sum, map_mul, Complex.conj_ofReal, ← AddChar.map_neg_eq_conj,
    Finset.sum_mul_sum]
  have key : ∀ x i j : ZMod p, (u i : ℂ) * ZMod.stdAddChar (i * x) *
      ((u j : ℂ) * ZMod.stdAddChar (-(j * x))) =
      (u i : ℂ) * (u j : ℂ) * ZMod.stdAddChar (x * (i - j)) := by
    intro x i j
    rw [mul_mul_mul_comm, ← AddChar.map_add_eq_mul]
    congr 2
    ring
  simp_rw [key]
  rw [Finset.sum_comm]
  refine (Finset.sum_congr rfl fun i _ => (Finset.sum_comm)).trans ?_
  have h2 : ∀ i y : ZMod p, ∑ x : ZMod p, (u i : ℂ) * (u y : ℂ) * ZMod.stdAddChar (x * (i - y))
      = if i = y then (u i : ℂ) * (u y : ℂ) * p else 0 := by
    intro i y
    rw [← Finset.mul_sum, AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar p), ZMod.card]
    by_cases h : i = y
    · simp [h]
    · simp [h, sub_eq_zero]
  simp_rw [h2, Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

noncomputable def G (g : ZMod p → ℝ) (ξ : ZMod p) : ℂ :=
  ∑ x : ZMod p, (g x : ℂ) * ZMod.stdAddChar (x * ξ)

noncomputable def corr (g : ZMod p → ℝ) (t : ZMod p) : ℝ := ∑ y : ZMod p, g y * g (y + t)

noncomputable def U2 (g : ZMod p → ℝ) : ℝ :=
  ∑ x : ZMod p, ∑ h₁ : ZMod p, ∑ h₂ : ZMod p, g x * g (x + h₁) * g (x + h₂) * g (x + h₁ + h₂)

lemma sq_norm_G (g : ZMod p → ℝ) (ξ : ZMod p) :
    ((‖G g ξ‖ ^ 2 : ℝ) : ℂ) = ∑ t : ZMod p, (corr g t : ℂ) * ZMod.stdAddChar (t * ξ) := by
  rw [sq_norm_eq, G, map_sum, Finset.sum_mul_sum]
  simp_rw [map_mul, Complex.conj_ofReal, ← AddChar.map_neg_eq_conj]
  rw [Finset.sum_comm]
  have hy : ∀ y : ZMod p, ∑ x : ZMod p, (g x : ℂ) * ZMod.stdAddChar (x * ξ) *
      ((g y : ℂ) * ZMod.stdAddChar (-(y * ξ))) =
      ∑ t : ZMod p, (g y : ℂ) * (g (y + t) : ℂ) * ZMod.stdAddChar (t * ξ) := by
    intro y
    rw [← Equiv.sum_comp (Equiv.addLeft y)]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [Equiv.coe_addLeft]
    rw [mul_mul_mul_comm, ← AddChar.map_add_eq_mul]
    have e1 : (y + t) * ξ + -(y * ξ) = t * ξ := by ring
    rw [e1]
    ring
  simp_rw [hy]
  rw [Finset.sum_comm]
  simp_rw [corr, Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_mul]

lemma sum_corr_sq (g : ZMod p → ℝ) : ∑ t : ZMod p, corr g t ^ 2 = U2 g := by
  simp_rw [U2, corr, sq, Finset.sum_mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun i _ => ?_
  rw [← Equiv.sum_comp (Equiv.addLeft i)]
  refine Finset.sum_congr rfl fun h _ => ?_
  simp only [Equiv.coe_addLeft]
  rw [add_right_comm i t h]
  ring

lemma key (g : ZMod p → ℝ) (hg : ∀ x, |g x| ≤ 1) : ∃ ξ0 : ZMod p, U2 g ≤ (p : ℝ) * ‖G g ξ0‖ ^ 2 := by
  obtain ⟨ξ0, -, hmax⟩ := Finset.exists_max_image Finset.univ (fun ξ => ‖G g ξ‖ ^ 2)
    Finset.univ_nonempty
  refine ⟨ξ0, ?_⟩
  have h4 : ∑ ξ : ZMod p, (‖G g ξ‖ ^ 2) ^ 2 = p * U2 g := by
    rw [← sum_corr_sq, ← parseval]
    refine Finset.sum_congr rfl fun ξ _ => ?_
    rw [← sq_norm_G, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have h2 : ∑ ξ : ZMod p, ‖G g ξ‖ ^ 2 = p * ∑ x : ZMod p, g x ^ 2 := parseval g
  have hsq : ∑ x : ZMod p, g x ^ 2 ≤ p := by
    calc ∑ x : ZMod p, g x ^ 2 ≤ ∑ x : ZMod p, (1 : ℝ) := Finset.sum_le_sum fun x _ => by
          rw [← sq_abs]; exact pow_le_one₀ (abs_nonneg _) (hg x)
      _ = p := by simp [ZMod.card]
  have hp : (0 : ℝ) < p := by exact_mod_cast NeZero.pos p
  have hM : 0 ≤ ‖G g ξ0‖ ^ 2 := by positivity
  have hle : (p : ℝ) * U2 g ≤ p * (p * ‖G g ξ0‖ ^ 2) := by
    rw [← h4]
    calc ∑ ξ : ZMod p, (‖G g ξ‖ ^ 2) ^ 2 ≤ ∑ ξ : ZMod p, ‖G g ξ0‖ ^ 2 * ‖G g ξ‖ ^ 2 :=
          Finset.sum_le_sum fun ξ _ => by
            rw [sq (‖G g ξ‖ ^ 2)]
            exact mul_le_mul_of_nonneg_right (hmax ξ (Finset.mem_univ _)) (by positivity)
      _ = ‖G g ξ0‖ ^ 2 * (p * ∑ x : ZMod p, g x ^ 2) := by rw [← Finset.mul_sum, h2]
      _ ≤ ‖G g ξ0‖ ^ 2 * (p * p) := by gcongr
      _ = p * (p * ‖G g ξ0‖ ^ 2) := by ring
  exact le_of_mul_le_mul_left hle hp

end E142W

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R1_H1_R1_H1_R2.H1 := by
  intro p _ f hf
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hb : ∀ h x : ZMod p, |f x * f (x + h)| ≤ 1 := fun h x => by
    rw [abs_mul]; exact mul_le_one₀ (hf x) (abs_nonneg _) (hf _)
  choose ξ hξ using fun h => E142W.key (fun x => f x * f (x + h)) (hb h)
  refine ⟨ξ, ?_⟩
  simp_rw [E142W.e_eq]
  calc _ = ∑ h₃ : ZMod p, E142W.U2 (fun x => f x * f (x + h₃)) := by
        simp only [E142W.U2]
        refine (Finset.sum_congr rfl fun x _ =>
          (Finset.sum_congr rfl fun h1 _ => Finset.sum_comm).trans Finset.sum_comm).trans ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun h3 _ => Finset.sum_congr rfl fun x _ =>
          Finset.sum_congr rfl fun h1 _ => Finset.sum_congr rfl fun h2 _ => ?_
        ring
    _ ≤ ∑ h : ZMod p, (p : ℝ) * ‖E142W.G (fun x => f x * f (x + h)) (ξ h)‖ ^ 2 :=
        Finset.sum_le_sum fun h _ => hξ h
    _ = _ := by rw [← Finset.mul_sum]; rfl
