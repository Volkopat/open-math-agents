import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R1_H1_R1_H2_R2
import Mathlib

-- your proof below (helpers in a namespace of your own)

namespace E142W

open Finset

variable {p : ℕ} [Fact p.Prime]

noncomputable def cube (s : ℕ) (g : ZMod p → ℝ) : ℝ :=
  ∑ x : ZMod p, ∑ h : Fin s → ZMod p, ∏ ω : Fin s → Bool,
    g (x + ∑ j : Fin s, if ω j then h j else 0)

lemma sum_cons {s : ℕ} {M : Type*} [AddCommMonoid M] (F : (Fin (s + 1) → ZMod p) → M) :
    ∑ hh, F hh = ∑ u, ∑ k : Fin s → ZMod p, F (Fin.cons u k) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Fin.consEquiv fun _ => ZMod p) _ _ (fun _ => rfl)).symm

lemma prod_cons {s : ℕ} (F : (Fin (s + 1) → Bool) → ℝ) :
    ∏ ω, F ω = ∏ ω : Fin s → Bool, (F (Fin.cons false ω) * F (Fin.cons true ω)) := by
  rw [← Fintype.prod_equiv (Fin.consEquiv fun _ => Bool) _ _ (fun _ => rfl),
    Fintype.prod_prod_type, Finset.prod_comm]
  simp only [Fintype.prod_bool]
  exact Finset.prod_congr rfl fun _ _ => mul_comm _ _

lemma cube_succ (s : ℕ) (G : ZMod p → ℝ) (t : ZMod p) (ht : t ≠ 0) :
    ∑ h, cube s (fun y => G y * G (y + t * h)) = cube (s + 1) G := by
  unfold cube
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [sum_cons]
  conv_rhs => rw [← Equiv.sum_comp (Equiv.mulLeft₀ t ht)]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun k _ => ?_
  rw [prod_cons]
  refine Finset.prod_congr rfl fun ω _ => ?_
  simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
  show _ = _ * G (_ + (t * u + _))
  simp only [Bool.false_eq_true, if_false, zero_add]
  congr 2
  ring

lemma pm (n : ℕ) {ι : Type*} [Fintype ι] (a : ι → ℝ) :
    (Fintype.card ι : ℝ) * (∑ i, a i) ^ (2 ^ n) ≤
      (Fintype.card ι : ℝ) ^ (2 ^ n) * ∑ i, a i ^ (2 ^ n) := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    have h1 : (∑ i, a i) ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ i, a i ^ 2 := by
      simpa using sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := a)
    have h2 := ih (fun i => a i ^ 2)
    have hc : (0:ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
    have e : ∀ x : ℝ, x ^ (2 ^ (n + 1)) = (x ^ 2) ^ (2 ^ n) := fun x => by
      rw [← pow_mul, pow_succ, mul_comm]
    calc (Fintype.card ι : ℝ) * (∑ i, a i) ^ (2 ^ (n + 1))
        = (Fintype.card ι : ℝ) * ((∑ i, a i) ^ 2) ^ (2 ^ n) := by rw [e]
      _ ≤ (Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) * ∑ i, a i ^ 2) ^ (2 ^ n) := by
          gcongr
      _ = (Fintype.card ι : ℝ) ^ (2 ^ n) * ((Fintype.card ι : ℝ) * (∑ i, a i ^ 2) ^ (2 ^ n)) := by
          rw [mul_pow]; ring
      _ ≤ (Fintype.card ι : ℝ) ^ (2 ^ n) *
            ((Fintype.card ι : ℝ) ^ (2 ^ n) * ∑ i, (a i ^ 2) ^ (2 ^ n)) := by gcongr
      _ = (Fintype.card ι : ℝ) ^ (2 ^ (n + 1)) * ∑ i, a i ^ (2 ^ (n + 1)) := by
          simp only [e]; rw [sq]; ring

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

lemma sum_lin (Φ : ZMod p → ℝ) (c : ZMod p) : ∑ x, ∑ d, Φ (x + c * d) = p * ∑ x, Φ x := by
  rw [Finset.sum_comm]
  have : ∀ d, ∑ x, Φ (x + c * d) = ∑ x, Φ x := fun d => Equiv.sum_comp (Equiv.addRight (c * d)) Φ
  simp only [this, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]

lemma expand_prod {s : ℕ} (g : Fin (s + 1) → ZMod p → ℝ) (a : Fin (s + 1) → ZMod p) :
    ∑ y, (∑ d, ∏ i, g i (y + a i * d)) ^ 2 =
      ∑ h, ∑ y, ∑ d, ∏ i, (g i (y + a i * d) * g i (y + a i * d + a i * h)) := by
  simp_rw [sq_expand]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun y _ =>
    Finset.sum_congr rfl fun d _ => ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  congr 2
  ring

lemma step_sq (s : ℕ) (c : Fin (s + 2) → ZMod p) (f : Fin (s + 2) → ZMod p → ℝ)
    (h0 : ∀ x, |f 0 x| ≤ 1) :
    (∑ x, ∑ d, ∏ i, f i (x + c i * d)) ^ 2 ≤ (p : ℝ) * ∑ h, ∑ y, ∑ d,
      ∏ i : Fin (s + 1), (f i.succ (y + (c i.succ - c 0) * d) *
        f i.succ (y + (c i.succ - c 0) * d + (c i.succ - c 0) * h)) := by
  have e : ∑ x, ∑ d, ∏ i, f i (x + c i * d) =
      ∑ y, f 0 y * ∑ d, ∏ i : Fin (s + 1), f i.succ (y + (c i.succ - c 0) * d) := by
    calc ∑ x, ∑ d, ∏ i, f i (x + c i * d)
        = ∑ x, ∑ d, f 0 (x + c 0 * d) * ∏ i : Fin (s + 1), f i.succ (x + c i.succ * d) :=
          Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun d _ => Fin.prod_univ_succ _
      _ = ∑ y, f 0 y * ∑ d, ∏ i : Fin (s + 1), f i.succ (y - c 0 * d + c i.succ * d) :=
          shift_id _ _ _
      _ = _ := by
          refine Finset.sum_congr rfl fun y _ => ?_
          congr 1
          refine Finset.sum_congr rfl fun d _ => Finset.prod_congr rfl fun i _ => ?_
          congr 1
          ring
  rw [e]
  refine (cs_weight _ _ h0).trans_eq ?_
  congr 1
  exact expand_prod (fun i => f i.succ) (fun i => c i.succ - c 0)

lemma pow_two_pow (x : ℝ) (n : ℕ) : x ^ (2 ^ (n + 1)) = (x ^ 2) ^ (2 ^ n) := by
  rw [← pow_mul, pow_succ, mul_comm]

theorem gvn (s : ℕ) : ∀ (c : Fin (s + 1) → ZMod p), Function.Injective c →
    ∀ (f : Fin (s + 1) → ZMod p → ℝ), (∀ i : Fin s, ∀ x, |f i.castSucc x| ≤ 1) →
    (p : ℝ) ^ (s + 1) * (∑ x, ∑ d, ∏ i, f i (x + c i * d)) ^ (2 ^ s) ≤
      (p : ℝ) ^ (2 ^ (s + 1)) * cube s (f (Fin.last s)) := by
  induction s with
  | zero =>
    intro c _ f _
    have h1 : ∑ x, ∑ d, ∏ i : Fin 1, f i (x + c i * d) = p * ∑ x, f 0 x := by
      simp only [Fin.prod_univ_one]
      exact sum_lin _ _
    have h2 : cube 0 (f (Fin.last 0)) = ∑ x, f 0 x := by
      simp [cube]
    rw [h1, h2]
    apply le_of_eq
    ring
  | succ s ih =>
    intro c hc f hf
    let c' : Fin (s + 1) → ZMod p := fun i => c i.succ - c 0
    have hinj : Function.Injective c' := by
      intro i j hij
      exact Fin.succ_injective _ (hc (sub_left_inj.mp hij))
    let D : ZMod p → Fin (s + 1) → ZMod p → ℝ := fun h i z => f i.succ z * f i.succ (z + c' i * h)
    have hD : ∀ h, ∀ i : Fin s, ∀ x, |D h i.castSucc x| ≤ 1 := by
      intro h i x
      have hb : ∀ z, |f i.castSucc.succ z| ≤ 1 := fun z => by
        rw [Fin.succ_castSucc]
        exact hf _ _
      show |f i.castSucc.succ x * f i.castSucc.succ (x + c' i.castSucc * h)| ≤ 1
      rw [abs_mul]
      exact mul_le_one₀ (hb _) (abs_nonneg _) (hb _)
    have IH := fun h => ih c' hinj (D h) (hD h)
    have h0 : ∀ x, |f 0 x| ≤ 1 := fun x => by simpa using hf 0 x
    have hsq := step_sq s c f h0
    have ht : c' (Fin.last s) ≠ 0 := sub_ne_zero.mpr (fun h => Fin.succ_ne_zero _ (hc h))
    have hcube : ∑ h, cube s (D h (Fin.last s)) = cube (s + 1) (f (Fin.last (s + 1))) := by
      have := cube_succ s (f (Fin.last (s + 1))) (c' (Fin.last s)) ht
      rw [← this]
      simp only [D, Fin.succ_last]
    let X : ZMod p → ℝ := fun h => ∑ y, ∑ d, ∏ i, D h i (y + c' i * d)
    have hpow : 2 ^ (s + 1) = 2 ^ s + 2 ^ s := by rw [pow_succ]; ring
    have hpow2 : 2 ^ (s + 1 + 1) = 2 ^ (s + 1) + 2 ^ (s + 1) := by rw [pow_succ 2 (s + 1)]; ring
    have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg _
    have hpm : (p : ℝ) * (∑ h, X h) ^ (2 ^ s) ≤ (p : ℝ) ^ (2 ^ s) * ∑ h, X h ^ (2 ^ s) := by
      have := pm s X
      simpa [ZMod.card] using this
    calc (p : ℝ) ^ (s + 1 + 1) * (∑ x, ∑ d, ∏ i, f i (x + c i * d)) ^ (2 ^ (s + 1))
        = (p : ℝ) ^ (s + 1 + 1) * ((∑ x, ∑ d, ∏ i, f i (x + c i * d)) ^ 2) ^ (2 ^ s) := by
          rw [pow_two_pow]
      _ ≤ (p : ℝ) ^ (s + 1 + 1) * ((p : ℝ) * ∑ h, X h) ^ (2 ^ s) := by
          gcongr
      _ = (p : ℝ) ^ (2 ^ s) * (p : ℝ) ^ (s + 1) * ((p : ℝ) * (∑ h, X h) ^ (2 ^ s)) := by
          rw [mul_pow]; ring
      _ ≤ (p : ℝ) ^ (2 ^ s) * (p : ℝ) ^ (s + 1) * ((p : ℝ) ^ (2 ^ s) * ∑ h, X h ^ (2 ^ s)) := by
          gcongr
      _ = (p : ℝ) ^ (2 ^ (s + 1)) * ∑ h, ((p : ℝ) ^ (s + 1) * X h ^ (2 ^ s)) := by
          rw [← Finset.mul_sum, hpow, pow_add (p : ℝ) (2 ^ s) (2 ^ s)]
          ring
      _ ≤ (p : ℝ) ^ (2 ^ (s + 1)) * ∑ h, ((p : ℝ) ^ (2 ^ (s + 1)) * cube s (D h (Fin.last s))) := by
          exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun h _ => IH h) (by positivity)
      _ = (p : ℝ) ^ (2 ^ (s + 1 + 1)) * cube (s + 1) (f (Fin.last (s + 1))) := by
          rw [← Finset.mul_sum, hcube, hpow2, pow_add (p : ℝ) (2 ^ (s + 1)) (2 ^ (s + 1))]
          ring

end E142W

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R1_H1_R1_H2_R2.H2 := by
  intro s p _ hs c hc f hf
  have g := E142W.gvn s c hc f hf
  have hle : s + 1 < 2 ^ (s + 1) := Nat.lt_two_pow_self
  have hp : (0 : ℝ) < (p : ℝ) ^ (s + 1) :=
    pow_pos (Nat.cast_pos.mpr (Fact.out : p.Prime).pos) _
  have e : (p : ℝ) ^ (2 ^ (s + 1)) = (p : ℝ) ^ (s + 1) * (p : ℝ) ^ (2 ^ (s + 1) - s - 1) := by
    rw [← pow_add]
    congr 1
    omega
  rw [e, mul_assoc] at g
  exact le_of_mul_le_mul_left g hp
