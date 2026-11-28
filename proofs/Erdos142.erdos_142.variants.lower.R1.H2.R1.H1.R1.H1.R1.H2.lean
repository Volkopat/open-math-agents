import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R1_H1_R1_H1_R1
import Mathlib

namespace E142W

variable {p : ℕ} [Fact p.Prime]

lemma cs_weight (g S : ZMod p → ℝ) (hg : ∀ x, |g x| ≤ 1) :
    (∑ x, g x * S x) ^ 2 ≤ (p : ℝ) * ∑ x, S x ^ 2 := by
  refine (Finset.sum_mul_sq_le_sq_mul_sq _ g S).trans ?_
  have h1 : ∑ x, g x ^ 2 ≤ (p : ℝ) := by
    calc ∑ x, g x ^ 2 ≤ ∑ _x : ZMod p, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro x _
          have := hg x
          nlinarith [abs_nonneg (g x), sq_abs (g x)]
      _ = p := by simp [Finset.card_univ, ZMod.card]
  exact mul_le_mul_of_nonneg_right h1 (Finset.sum_nonneg fun x _ => sq_nonneg _)

lemma sq_expand (F : ZMod p → ℝ) : (∑ d, F d) ^ 2 = ∑ h, ∑ d, F d * F (d + h) := by
  rw [sq, Finset.sum_mul_sum]
  rw [Finset.sum_comm (f := fun h d => F d * F (d + h))]
  refine Finset.sum_congr rfl fun d _ => ?_
  exact (Equiv.sum_comp (Equiv.addLeft d) (fun d' => F d * F d')).symm

lemma shift_id (g : ZMod p → ℝ) (a : ZMod p) (R : ZMod p → ZMod p → ℝ) :
    ∑ x, ∑ d, g (x + a * d) * R x d = ∑ x, g x * ∑ d, R (x - a * d) d := by
  calc ∑ x, ∑ d, g (x + a * d) * R x d = ∑ d, ∑ x, g (x + a * d) * R x d := Finset.sum_comm
    _ = ∑ d, ∑ x, g x * R (x - a * d) d := Finset.sum_congr rfl fun d _ => by
        rw [← Equiv.sum_comp (Equiv.addRight (a * d)) (fun x => g x * R (x - a * d) d)]
        simp
    _ = ∑ x, ∑ d, g x * R (x - a * d) d := Finset.sum_comm
    _ = ∑ x, g x * ∑ d, R (x - a * d) d := by simp_rw [Finset.mul_sum]

lemma expand_id (a : ZMod p) (R : ZMod p → ZMod p → ℝ) :
    ∑ x, (∑ d, R (x - a * d) d) ^ 2 = ∑ h, ∑ x, ∑ d, R x d * R (x - a * h) (d + h) := by
  simp_rw [sq_expand]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [Finset.sum_comm, Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
    (f := fun x d => R x d * R (x - a * h) (d + h))]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [← Equiv.sum_comp (Equiv.addRight (a * d))]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [Equiv.coe_addRight]
  congr 2 <;> ring

lemma step {ι : Type*} [Fintype ι] (g : ι → ZMod p → ℝ) (hg : ∀ i x, |g i x| ≤ 1)
    (a : ZMod p) (R : ι → ZMod p → ZMod p → ℝ) :
    (∑ i, ∑ x, ∑ d, g i (x + a * d) * R i x d) ^ 2 ≤
      (Fintype.card ι : ℝ) * p * ∑ i, ∑ h, ∑ x, ∑ d, R i x d * R i (x - a * h) (d + h) := by
  refine (sq_sum_le_card_mul_sum_sq (s := Finset.univ)
    (f := fun i => ∑ x, ∑ d, g i (x + a * d) * R i x d)).trans ?_
  rw [Finset.card_univ, mul_assoc]
  gcongr
  rw [Finset.mul_sum]
  gcongr with i
  rw [shift_id, ← expand_id]
  exact cs_weight _ _ (hg i)

lemma shift_eq (x a h b d : ZMod p) : x - a * h + b * (d + h) = x + b * d + (b - a) * h := by
  ring

lemma abs_mul_le_one' {u v : ℝ} (hu : |u| ≤ 1) (hv : |v| ≤ 1) : |u * v| ≤ 1 := by
  rw [abs_mul]
  exact mul_le_one₀ hu (abs_nonneg _) hv

def Cube (f : ZMod p → ℝ) (y a b c : ZMod p) : ℝ :=
  f y * f (y + a) * f (y + b) * f (y + a + b) *
    f (y + c) * f (y + a + c) * f (y + b + c) * f (y + a + b + c)

lemma cube_alt (f : ZMod p → ℝ) (y a b c : ZMod p) : Cube f y a b c =
    f y * f (y + a) * f (y + b) * f (y + b + a) *
      (f (y + c) * f (y + c + a) * f (y + c + b) * f (y + c + b + a)) := by
  unfold Cube
  rw [show y + c + b + a = y + a + b + c by ring, show y + b + a = y + a + b by ring,
    show y + c + a = y + a + c by ring, show y + c + b = y + b + c by ring]
  ring

lemma sum3_congr {ι : Type*} [Fintype ι] {F G : ι → ZMod p → ZMod p → ℝ}
    (H : ∀ i x d, F i x d = G i x d) :
    ∑ i, ∑ x, ∑ d, F i x d = ∑ i, ∑ x, ∑ d, G i x d :=
  Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun x _ =>
    Finset.sum_congr rfl fun d _ => H i x d

lemma sum_lin (Φ : ZMod p → ℝ) (c : ZMod p) : ∑ x, ∑ d, Φ (x + c * d) = p * ∑ x, Φ x := by
  rw [Finset.sum_comm]
  have : ∀ d, ∑ x, Φ (x + c * d) = ∑ x, Φ x := fun d => Equiv.sum_comp (Equiv.addRight (c * d)) Φ
  simp only [this, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]

lemma rescale (u : ZMod p) (hu : u ≠ 0) (F : ZMod p → ℝ) : ∑ h, F (u * h) = ∑ h, F h :=
  Equiv.sum_comp (Equiv.mulLeft₀ u hu) F

theorem gvn (c₀ c₁ c₂ c₃ : ZMod p) (hu0 : c₃ - c₀ ≠ 0) (hu1 : c₃ - c₁ ≠ 0) (hu2 : c₃ - c₂ ≠ 0)
    (f₀ f₁ f₂ f₃ : ZMod p → ℝ) (hf₀ : ∀ x, |f₀ x| ≤ 1) (hf₁ : ∀ x, |f₁ x| ≤ 1)
    (hf₂ : ∀ x, |f₂ x| ≤ 1) :
    (∑ x, ∑ d, f₀ (x + c₀ * d) * f₁ (x + c₁ * d) * f₂ (x + c₂ * d) * f₃ (x + c₃ * d)) ^ 8 ≤
      (p : ℝ) ^ 12 * ∑ x, ∑ h₁, ∑ h₂, ∑ h₃, Cube f₃ x h₁ h₂ h₃ := by
  have e1 : (∑ x, ∑ d, f₀ (x + c₀ * d) * f₁ (x + c₁ * d) * f₂ (x + c₂ * d) * f₃ (x + c₃ * d)) ^ 2
      ≤ p * ∑ h, ∑ x, ∑ d, (f₁ (x + c₁ * d) * f₁ (x + c₁ * d + (c₁ - c₀) * h)) *
        ((f₂ (x + c₂ * d) * f₂ (x + c₂ * d + (c₂ - c₀) * h)) *
          (f₃ (x + c₃ * d) * f₃ (x + c₃ * d + (c₃ - c₀) * h))) := by
    have e := step (ι := Unit) (fun _ => f₀) (fun _ => hf₀) c₀
      (fun _ x d => f₁ (x + c₁ * d) * f₂ (x + c₂ * d) * f₃ (x + c₃ * d))
    simp only [Fintype.sum_unique, Fintype.card_unit, Nat.cast_one, one_mul, shift_eq] at e
    refine Eq.trans_le ?_ (e.trans_eq ?_)
    · congr 1
      exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun d _ => by ring
    · congr 1
      exact sum3_congr fun h x d => by ring
  have e2 : (∑ h, ∑ x, ∑ d, (f₁ (x + c₁ * d) * f₁ (x + c₁ * d + (c₁ - c₀) * h)) *
        ((f₂ (x + c₂ * d) * f₂ (x + c₂ * d + (c₂ - c₀) * h)) *
          (f₃ (x + c₃ * d) * f₃ (x + c₃ * d + (c₃ - c₀) * h)))) ^ 2 ≤
      p * p * ∑ hh : ZMod p × ZMod p, ∑ x, ∑ d,
        (f₂ (x + c₂ * d) * f₂ (x + c₂ * d + (c₂ - c₀) * hh.1) *
          (f₂ (x + c₂ * d + (c₂ - c₁) * hh.2) *
            f₂ (x + c₂ * d + (c₂ - c₁) * hh.2 + (c₂ - c₀) * hh.1))) *
        (f₃ (x + c₃ * d) * f₃ (x + c₃ * d + (c₃ - c₀) * hh.1) *
          (f₃ (x + c₃ * d + (c₃ - c₁) * hh.2) *
            f₃ (x + c₃ * d + (c₃ - c₁) * hh.2 + (c₃ - c₀) * hh.1))) := by
    have e := step (fun h y => f₁ y * f₁ (y + (c₁ - c₀) * h))
      (fun h y => abs_mul_le_one' (hf₁ _) (hf₁ _)) c₁
      (fun h x d => (f₂ (x + c₂ * d) * f₂ (x + c₂ * d + (c₂ - c₀) * h)) *
          (f₃ (x + c₃ * d) * f₃ (x + c₃ * d + (c₃ - c₀) * h)))
    simp only [ZMod.card, shift_eq] at e
    refine e.trans_eq ?_
    simp only [Fintype.sum_prod_type]
    congr 1
    exact Finset.sum_congr rfl fun h _ => sum3_congr fun h' x d => by ring
  have e3 : (∑ hh : ZMod p × ZMod p, ∑ x, ∑ d,
        (f₂ (x + c₂ * d) * f₂ (x + c₂ * d + (c₂ - c₀) * hh.1) *
          (f₂ (x + c₂ * d + (c₂ - c₁) * hh.2) *
            f₂ (x + c₂ * d + (c₂ - c₁) * hh.2 + (c₂ - c₀) * hh.1))) *
        (f₃ (x + c₃ * d) * f₃ (x + c₃ * d + (c₃ - c₀) * hh.1) *
          (f₃ (x + c₃ * d + (c₃ - c₁) * hh.2) *
            f₃ (x + c₃ * d + (c₃ - c₁) * hh.2 + (c₃ - c₀) * hh.1)))) ^ 2 ≤
      p * p * p * ∑ hh : ZMod p × ZMod p, ∑ h₃, ∑ x, ∑ d,
        Cube f₃ (x + c₃ * d) ((c₃ - c₀) * hh.1) ((c₃ - c₁) * hh.2) ((c₃ - c₂) * h₃) := by
    have e := step (fun (hh : ZMod p × ZMod p) y => f₂ y * f₂ (y + (c₂ - c₀) * hh.1) *
          (f₂ (y + (c₂ - c₁) * hh.2) * f₂ (y + (c₂ - c₁) * hh.2 + (c₂ - c₀) * hh.1)))
      (fun hh y => abs_mul_le_one' (abs_mul_le_one' (hf₂ _) (hf₂ _))
        (abs_mul_le_one' (hf₂ _) (hf₂ _))) c₂
      (fun hh x d => f₃ (x + c₃ * d) * f₃ (x + c₃ * d + (c₃ - c₀) * hh.1) *
          (f₃ (x + c₃ * d + (c₃ - c₁) * hh.2) *
            f₃ (x + c₃ * d + (c₃ - c₁) * hh.2 + (c₃ - c₀) * hh.1)))
    simp only [Fintype.card_prod, ZMod.card, Nat.cast_mul, shift_eq] at e
    refine e.trans_eq ?_
    congr 1
    exact Finset.sum_congr rfl fun hh _ => sum3_congr fun h x d => by rw [cube_alt]; ring
  have q4 : ∑ hh : ZMod p × ZMod p, ∑ h₃, ∑ x, ∑ d,
        Cube f₃ (x + c₃ * d) ((c₃ - c₀) * hh.1) ((c₃ - c₁) * hh.2) ((c₃ - c₂) * h₃) =
      p * ∑ x, ∑ h₁, ∑ h₂, ∑ h₃, Cube f₃ x h₁ h₂ h₃ := by
    simp only [Fintype.sum_prod_type]
    calc _ = ∑ h₁, ∑ h₂, ∑ h₃, (p : ℝ) *
          ∑ x, Cube f₃ x ((c₃ - c₀) * h₁) ((c₃ - c₁) * h₂) ((c₃ - c₂) * h₃) :=
          Finset.sum_congr rfl fun h₁ _ => Finset.sum_congr rfl fun h₂ _ =>
            Finset.sum_congr rfl fun h₃ _ => sum_lin
              (fun y => Cube f₃ y ((c₃ - c₀) * h₁) ((c₃ - c₁) * h₂) ((c₃ - c₂) * h₃)) c₃
      _ = p * ∑ h₁, ∑ h₂, ∑ h₃,
          ∑ x, Cube f₃ x ((c₃ - c₀) * h₁) ((c₃ - c₁) * h₂) ((c₃ - c₂) * h₃) := by
          simp only [Finset.mul_sum]
      _ = p * ∑ h₁, ∑ h₂, ∑ h₃, ∑ x, Cube f₃ x h₁ h₂ h₃ := by
          congr 1
          rw [rescale _ hu0 (fun a => ∑ h₂, ∑ h₃,
            ∑ x, Cube f₃ x a ((c₃ - c₁) * h₂) ((c₃ - c₂) * h₃))]
          refine Finset.sum_congr rfl fun h₁ _ => ?_
          rw [rescale _ hu1 (fun b => ∑ h₃, ∑ x, Cube f₃ x h₁ b ((c₃ - c₂) * h₃))]
          refine Finset.sum_congr rfl fun h₂ _ => ?_
          exact rescale _ hu2 (fun c => ∑ x, Cube f₃ x h₁ h₂ c)
      _ = p * ∑ x, ∑ h₁, ∑ h₂, ∑ h₃, Cube f₃ x h₁ h₂ h₃ := by
          congr 1
          calc _ = ∑ h₁ : ZMod p, ∑ h₂ : ZMod p, ∑ x : ZMod p, ∑ h₃ : ZMod p,
                Cube f₃ x h₁ h₂ h₃ :=
                Finset.sum_congr rfl fun h₁ _ => Finset.sum_congr rfl fun h₂ _ => Finset.sum_comm
            _ = ∑ h₁ : ZMod p, ∑ x : ZMod p, ∑ h₂ : ZMod p, ∑ h₃ : ZMod p,
                Cube f₃ x h₁ h₂ h₃ :=
                Finset.sum_congr rfl fun h₁ _ => Finset.sum_comm
            _ = _ := Finset.sum_comm
  set L := ∑ x, ∑ d, f₀ (x + c₀ * d) * f₁ (x + c₁ * d) * f₂ (x + c₂ * d) * f₃ (x + c₃ * d)
  set S1 := ∑ h, ∑ x, ∑ d, (f₁ (x + c₁ * d) * f₁ (x + c₁ * d + (c₁ - c₀) * h)) *
        ((f₂ (x + c₂ * d) * f₂ (x + c₂ * d + (c₂ - c₀) * h)) *
          (f₃ (x + c₃ * d) * f₃ (x + c₃ * d + (c₃ - c₀) * h)))
  set S2 := ∑ hh : ZMod p × ZMod p, ∑ x, ∑ d,
        (f₂ (x + c₂ * d) * f₂ (x + c₂ * d + (c₂ - c₀) * hh.1) *
          (f₂ (x + c₂ * d + (c₂ - c₁) * hh.2) *
            f₂ (x + c₂ * d + (c₂ - c₁) * hh.2 + (c₂ - c₀) * hh.1))) *
        (f₃ (x + c₃ * d) * f₃ (x + c₃ * d + (c₃ - c₀) * hh.1) *
          (f₃ (x + c₃ * d + (c₃ - c₁) * hh.2) *
            f₃ (x + c₃ * d + (c₃ - c₁) * hh.2 + (c₃ - c₀) * hh.1)))
  set T := ∑ x, ∑ h₁, ∑ h₂, ∑ h₃, Cube f₃ x h₁ h₂ h₃
  rw [q4] at e3
  have hp : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have a1 : L ^ 4 ≤ (p : ℝ) ^ 4 * S2 := by
    calc L ^ 4 = (L ^ 2) ^ 2 := by ring
      _ ≤ (p * S1) ^ 2 := pow_le_pow_left₀ (sq_nonneg L) e1 2
      _ = (p : ℝ) ^ 2 * S1 ^ 2 := by ring
      _ ≤ (p : ℝ) ^ 2 * (p * p * S2) := mul_le_mul_of_nonneg_left e2 (by positivity)
      _ = (p : ℝ) ^ 4 * S2 := by ring
  calc L ^ 8 = (L ^ 4) ^ 2 := by ring
    _ ≤ ((p : ℝ) ^ 4 * S2) ^ 2 := pow_le_pow_left₀ (by positivity) a1 2
    _ = (p : ℝ) ^ 8 * S2 ^ 2 := by ring
    _ ≤ (p : ℝ) ^ 8 * (p * p * p * (p * T)) := mul_le_mul_of_nonneg_left e3 (by positivity)
    _ = (p : ℝ) ^ 12 * T := by ring

end E142W

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R1_H1_R1_H1_R1.H2 := by
  intro p _ c₀ c₁ c₂ c₃ _ _ h03 _ h13 h23 f₀ f₁ f₂ f₃ hf₀ hf₁ hf₂
  exact E142W.gvn c₀ c₁ c₂ c₃ (sub_ne_zero.mpr h03.symm) (sub_ne_zero.mpr h13.symm)
    (sub_ne_zero.mpr h23.symm) f₀ f₁ f₂ f₃ hf₀ hf₁ hf₂
