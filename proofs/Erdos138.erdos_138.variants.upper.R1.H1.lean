import OMAReductions.R_Erdos138_erdos_138_variants_upper_R1
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
Gowers' generalized von Neumann theorem over `ZMod P` (`Erdos138.erdos_138.variants.upper.R1.H1`).
-/

namespace OMA.Erdos138GvN

open Finset

private lemma equiv_addRight_apply {G : Type*} [AddGroup G] (a x : G) :
    Equiv.addRight a x = x + a := rfl

private lemma equiv_addLeft_apply {G : Type*} [AddGroup G] (a x : G) :
    Equiv.addLeft a x = a + x := rfl

private lemma equiv_mulLeft0_apply {F : Type*} [GroupWithZero F] (a : F) (ha : a ≠ 0) (x : F) :
    Equiv.mulLeft₀ a ha x = a * x := rfl

private lemma avg_sq_le {ι : Type*} [Fintype ι] (hcard : 0 < (Fintype.card ι : ℝ))
    (a : ι → ℝ) :
    ((Fintype.card ι : ℝ)⁻¹ * ∑ i : ι, a i) ^ 2 ≤
      (Fintype.card ι : ℝ)⁻¹ * ∑ i : ι, (a i) ^ 2 := by
  set N : ℝ := (Fintype.card ι : ℝ)
  set μ : ℝ := N⁻¹ * ∑ i : ι, a i
  have hN : N ≠ 0 := hcard.ne'
  have hsum_a : ∑ i : ι, a i = N * μ := by
    dsimp only [μ]
    rw [← mul_assoc, mul_inv_cancel₀ hN, one_mul]
  have hvar : 0 ≤ ∑ i : ι, (a i - μ) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hexp : ∑ i : ι, (a i - μ) ^ 2 = (∑ i : ι, (a i) ^ 2) - N * μ ^ 2 := by
    have h1 : ∀ i : ι, (a i - μ) ^ 2 = (a i) ^ 2 - 2 * μ * a i + μ ^ 2 := fun i => by ring
    simp_rw [h1, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hsum_a]
    dsimp only [N]
    ring
  have hle : N * μ ^ 2 ≤ ∑ i : ι, (a i) ^ 2 := by linarith
  calc
    μ ^ 2 = N⁻¹ * (N * μ ^ 2) := by rw [← mul_assoc, inv_mul_cancel₀ hN, one_mul]
    _ ≤ N⁻¹ * ∑ i : ι, (a i) ^ 2 := mul_le_mul_of_nonneg_left hle (inv_nonneg.mpr hcard.le)

private lemma avg_pow_two_le {ι : Type*} [Fintype ι] (hcard : 0 < (Fintype.card ι : ℝ)) :
    ∀ (n : ℕ) (a : ι → ℝ), (∀ i, 0 ≤ a i) →
      ((Fintype.card ι : ℝ)⁻¹ * ∑ i : ι, a i) ^ (2 ^ n) ≤
        (Fintype.card ι : ℝ)⁻¹ * ∑ i : ι, (a i) ^ (2 ^ n)
  | 0, _, _ => by simp
  | n + 1, a, ha => by
    have hnonneg : 0 ≤ (Fintype.card ι : ℝ)⁻¹ * ∑ i : ι, a i :=
      mul_nonneg (inv_nonneg.mpr hcard.le) (Finset.sum_nonneg fun i _ => ha i)
    have ih := avg_pow_two_le hcard n a ha
    have hstep := pow_le_pow_left₀ (pow_nonneg hnonneg _) ih 2
    have hfin := hstep.trans (avg_sq_le hcard (fun i => (a i) ^ (2 ^ n)))
    simpa only [pow_succ, pow_mul] using hfin

private def piSuccEquiv {m : ℕ} (α : Type*) :
    (Fin (m + 1) → α) ≃ (Fin m → α) × α where
  toFun f := (fun i => f i.castSucc, f (Fin.last m))
  invFun p := Fin.snoc p.1 p.2
  left_inv f := by
    ext i
    refine Fin.lastCases ?_ ?_ i <;> simp
  right_inv p := by
    rcases p with ⟨f, x⟩
    apply Prod.ext
    · ext i; simp
    · simp

private lemma gowers_succ_eq {P : ℕ} [NeZero P] {m : ℕ} (u : ZMod P → ℝ) :
    ∑ h' : Fin (m + 1) → ZMod P, ∑ x : ZMod P,
        ∏ ω' : Fin (m + 1) → Bool,
          u (x + ∑ i : Fin (m + 1), if ω' i then h' i else 0) =
      ∑ h_last : ZMod P, ∑ x : ZMod P, ∑ h : Fin m → ZMod P,
        ∏ ω : Fin m → Bool,
          (u (x + ∑ i : Fin m, if ω i then h i else 0) *
            u ((x + ∑ i : Fin m, if ω i then h i else 0) + h_last)) := by
  rw [Fintype.sum_equiv (piSuccEquiv (ZMod P)) _
      (fun p => ∑ x : ZMod P, ∏ ω' : Fin (m + 1) → Bool,
        u (x + ∑ i : Fin (m + 1), if ω' i then Fin.snoc p.1 p.2 i else 0)) (fun h' => by
    have hs : Fin.snoc (piSuccEquiv (ZMod P) h').1 (piSuccEquiv (ZMod P) h').2 = h' :=
      (piSuccEquiv (ZMod P)).left_inv h'
    simp_rw [hs])]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun h_last _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [Fintype.prod_equiv (piSuccEquiv Bool) _
      (fun p : (Fin m → Bool) × Bool => u (x + ∑ i : Fin (m + 1),
        if Fin.snoc (α := fun _ => Bool) p.1 p.2 i then
          Fin.snoc (α := fun _ => ZMod P) h h_last i
        else 0)) (fun ω' =>
    congrArg (fun φ : Fin (m + 1) → Bool =>
      u (x + ∑ i : Fin (m + 1),
        if φ i then Fin.snoc (α := fun _ => ZMod P) h h_last i else 0))
      ((piSuccEquiv Bool).left_inv ω').symm)]
  rw [Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun ω _ => ?_
  simp only [Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last, Fintype.prod_bool,
    if_true, Bool.false_eq_true, if_false, add_zero]
  rw [mul_comm, ← add_assoc]

private theorem gvN_general {P : ℕ} [NeZero P] [Fact P.Prime] :
    ∀ (n : ℕ) (u : ZMod P → ℝ)
      (g : Fin (n + 1) → ZMod P → ℝ), (∀ i z, |g i z| ≤ 1) →
      ∀ (c : Fin (n + 1) → ZMod P), (∀ i, c i ≠ 0) →
        |((P : ℝ) ^ 2)⁻¹ * ∑ y : ZMod P, ∑ r : ZMod P,
            u y * ∏ i : Fin (n + 1), g i (y + c i * r)| ^ (2 ^ (n + 1)) ≤
          ((P : ℝ) ^ (n + 2))⁻¹ * ∑ x : ZMod P, ∑ h : Fin (n + 1) → ZMod P,
            ∏ ω : Fin (n + 1) → Bool,
              u (x + ∑ i : Fin (n + 1), if ω i then h i else 0)
  | 0, u, g, hg, c, hc => by
    have hP_pos : 0 < (P : ℝ) := Nat.cast_pos.mpr (NeZero.pos P)
    have hP_nonneg : 0 ≤ (P : ℝ) := hP_pos.le
    have hP_ne : (P : ℝ) ≠ 0 := hP_pos.ne'
    have hinner : ∀ y : ZMod P,
        ∑ r : ZMod P, u y * ∏ i : Fin 1, g i (y + c i * r) = u y * ∑ z : ZMod P, g 0 z := by
      intro y
      simp_rw [Fin.prod_univ_one, ← Finset.mul_sum]
      congr 1
      exact Fintype.sum_equiv ((Equiv.mulLeft₀ (c 0) (hc 0)).trans (Equiv.addLeft y))
        (fun r => g 0 (y + c 0 * r)) (g 0) fun _ => rfl
    have hfact : ((P : ℝ) ^ 2)⁻¹ * ∑ y : ZMod P, ∑ r : ZMod P,
          u y * ∏ i : Fin 1, g i (y + c i * r) =
        ((P : ℝ)⁻¹ * ∑ y : ZMod P, u y) * ((P : ℝ)⁻¹ * ∑ z : ZMod P, g 0 z) := by
      simp_rw [hinner, ← Finset.sum_mul]
      ring
    have hg_avg : |(P : ℝ)⁻¹ * ∑ z : ZMod P, g 0 z| ≤ 1 := by
      rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr hP_nonneg)]
      calc
        (P : ℝ)⁻¹ * |∑ z : ZMod P, g 0 z|
          ≤ (P : ℝ)⁻¹ * ∑ z : ZMod P, |g 0 z| :=
            mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (inv_nonneg.mpr hP_nonneg)
        _ ≤ (P : ℝ)⁻¹ * ∑ _z : ZMod P, (1 : ℝ) :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun z _ => hg 0 z)
              (inv_nonneg.mpr hP_nonneg)
        _ = (P : ℝ)⁻¹ * (P : ℝ) := by
            rw [Finset.sum_const, Finset.card_univ, ZMod.card P, nsmul_eq_mul, mul_one]
        _ = 1 := inv_mul_cancel₀ hP_ne
    have hle : |((P : ℝ) ^ 2)⁻¹ * ∑ y : ZMod P, ∑ r : ZMod P,
          u y * ∏ i : Fin 1, g i (y + c i * r)| ≤
        |(P : ℝ)⁻¹ * ∑ y : ZMod P, u y| := by
      rw [hfact, abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) hg_avg
    have hsq : |((P : ℝ) ^ 2)⁻¹ * ∑ y : ZMod P, ∑ r : ZMod P,
          u y * ∏ i : Fin 1, g i (y + c i * r)| ^ (2 ^ 1) ≤
        ((P : ℝ)⁻¹ * ∑ y : ZMod P, u y) ^ 2 := by
      simpa only [pow_one, sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hle 2
    refine hsq.trans_eq ?_
    have hrhs : ∑ x : ZMod P, ∑ h : Fin 1 → ZMod P,
          ∏ ω : Fin 1 → Bool, u (x + ∑ i : Fin 1, if ω i then h i else 0) =
        ∑ x : ZMod P, ∑ y : ZMod P, u x * u y := by
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Fintype.sum_equiv (Equiv.funUnique (Fin 1) (ZMod P)) _
          (fun h0 => ∏ ω : Fin 1 → Bool, u (x + ∑ i : Fin 1, if ω i then h0 else 0)) (fun h => by
        simp only [Fin.sum_univ_one]; rfl)]
      refine Fintype.sum_equiv (Equiv.addLeft x) _ (fun y => u x * u y) fun h0 => ?_
      rw [Fintype.prod_equiv (Equiv.funUnique (Fin 1) Bool) _
          (fun b => u (x + ∑ _i : Fin 1, if b then h0 else 0)) (fun ω => by
        simp only [Fin.sum_univ_one]; rfl)]
      rw [equiv_addLeft_apply]
      simp only [Fin.sum_univ_one, Fintype.prod_bool, if_true, Bool.false_eq_true, if_false,
        add_zero]
      rw [mul_comm]
    rw [hrhs, ← Finset.sum_mul_sum]
    ring
  | n + 1, u, g, hg, c, hc => by
    have hP_pos : 0 < (P : ℝ) := Nat.cast_pos.mpr (NeZero.pos P)
    have hP_nonneg : 0 ≤ (P : ℝ) := hP_pos.le
    have hcard : 0 < (Fintype.card (ZMod P) : ℝ) := by rwa [ZMod.card P]
    let cL : ZMod P := c (Fin.last (n + 1))
    have hcL : cL ≠ 0 := hc (Fin.last (n + 1))
    let gL : ZMod P → ℝ := g (Fin.last (n + 1))
    let G (z r : ZMod P) : ℝ :=
      u (z - cL * r) * ∏ i : Fin (n + 1), g i.castSucc (z + (c i.castSucc - cL) * r)
    let A (z : ZMod P) : ℝ := (P : ℝ)⁻¹ * ∑ r : ZMod P, G z r
    let S : ℝ :=
      ((P : ℝ) ^ 2)⁻¹ * ∑ y : ZMod P, ∑ r : ZMod P,
        u y * ∏ i : Fin (n + 2), g i (y + c i * r)
    have hre : ∀ r : ZMod P,
        ∑ y : ZMod P, u y * ∏ i : Fin (n + 2), g i (y + c i * r) =
          ∑ z : ZMod P, gL z * G z r := by
      intro r
      refine Fintype.sum_equiv (Equiv.addRight (cL * r)) _ _ fun y => ?_
      rw [equiv_addRight_apply, Fin.prod_univ_castSucc]
      have hsub : (y + cL * r) - cL * r = y := add_sub_cancel_right y (cL * r)
      have hprod : ∏ i : Fin (n + 1), g i.castSucc (y + c i.castSucc * r) =
          ∏ i : Fin (n + 1), g i.castSucc ((y + cL * r) + (c i.castSucc - cL) * r) := by
        refine Finset.prod_congr rfl fun i _ => ?_
        congr 1; ring
      have hlast : g (Fin.last (n + 1)) (y + c (Fin.last (n + 1)) * r) = gL (y + cL * r) := rfl
      dsimp only [G]
      rw [hsub, ← hprod, hlast]
      ring
    have hS_eq : S = (P : ℝ)⁻¹ * ∑ z : ZMod P, gL z * A z := by
      dsimp only [S, A]
      rw [Finset.sum_comm]
      simp_rw [hre]
      rw [Finset.sum_comm]
      have hpull : ∀ z : ZMod P, gL z * ((P : ℝ)⁻¹ * ∑ r : ZMod P, G z r) =
          (P : ℝ)⁻¹ * (gL z * ∑ r : ZMod P, G z r) := fun z => by ring
      simp_rw [hpull, ← Finset.mul_sum, ← mul_assoc]
      congr 1
      ring
    have hS_abs : |S| ≤ (P : ℝ)⁻¹ * ∑ z : ZMod P, |A z| := by
      rw [hS_eq, abs_mul, abs_of_nonneg (inv_nonneg.mpr hP_nonneg)]
      refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hP_nonneg)
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun z _ => ?_)
      rw [abs_mul]
      exact mul_le_of_le_one_left (abs_nonneg _) (hg (Fin.last (n + 1)) z)
    have havg : ((P : ℝ)⁻¹ * ∑ z : ZMod P, |A z|) ^ 2 ≤ (P : ℝ)⁻¹ * ∑ z : ZMod P, (A z) ^ 2 := by
      have h0 := avg_sq_le hcard (fun z => |A z|)
      simpa only [ZMod.card P, sq_abs] using h0
    have hS_sq : |S| ^ 2 ≤ (P : ℝ)⁻¹ * ∑ z : ZMod P, (A z) ^ 2 :=
      (pow_le_pow_left₀ (abs_nonneg S) hS_abs 2).trans havg
    let ut (t y : ZMod P) : ℝ := u y * u (y + (-cL * t))
    let gt (t : ZMod P) (i : Fin (n + 1)) (w : ZMod P) : ℝ :=
      g i.castSucc w * g i.castSucc (w + (c i.castSucc - cL) * t)
    let Xt (t : ZMod P) : ℝ :=
      ((P : ℝ) ^ 2)⁻¹ * ∑ y : ZMod P, ∑ r : ZMod P,
        ut t y * ∏ i : Fin (n + 1), gt t i (y + c i.castSucc * r)
    have hAz_sq : ∀ z : ZMod P,
        (A z) ^ 2 = ((P : ℝ) ^ 2)⁻¹ * ∑ r : ZMod P, ∑ t : ZMod P, G z r * G z (r + t) := by
      intro z
      dsimp only [A]
      rw [mul_pow, ← inv_pow]
      congr 1
      rw [sq, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      exact (Fintype.sum_equiv (Equiv.addLeft r)
        (fun t => G z r * G z (r + t)) (fun r' => G z r * G z r') fun _ => rfl).symm
    have hsum_eq : (P : ℝ)⁻¹ * ∑ z : ZMod P, (A z) ^ 2 = (P : ℝ)⁻¹ * ∑ t : ZMod P, Xt t := by
      congr 1
      have hpull : ∑ z : ZMod P, (A z) ^ 2 =
          ((P : ℝ) ^ 2)⁻¹ * ∑ z : ZMod P, ∑ r : ZMod P, ∑ t : ZMod P, G z r * G z (r + t) := by
        simp only [hAz_sq]
        rw [← Finset.mul_sum]
      have hmid : ∀ t : ZMod P,
          ∑ z : ZMod P, ∑ r : ZMod P, G z r * G z (r + t) =
            ∑ y : ZMod P, ∑ r : ZMod P,
              ut t y * ∏ i : Fin (n + 1), gt t i (y + c i.castSucc * r) := by
        intro t
        rw [Finset.sum_comm]
        rw [Finset.sum_comm (f := fun y r => ut t y * ∏ i : Fin (n + 1), gt t i (y + c i.castSucc * r))]
        refine Finset.sum_congr rfl fun r _ => ?_
        refine (Fintype.sum_equiv (Equiv.addRight (cL * r))
          (fun y => ut t y * ∏ i : Fin (n + 1), gt t i (y + c i.castSucc * r))
          (fun z => G z r * G z (r + t)) fun y => ?_).symm
        rw [equiv_addRight_apply]
        dsimp only [G, ut, gt]
        rw [Finset.prod_mul_distrib]
        have hu1 : (y + cL * r) - cL * r = y := add_sub_cancel_right y (cL * r)
        have hu2 : (y + cL * r) - cL * (r + t) = y + (-cL * t) := by ring
        have hp1 : ∏ i : Fin (n + 1), g i.castSucc ((y + cL * r) + (c i.castSucc - cL) * r) =
            ∏ i : Fin (n + 1), g i.castSucc (y + c i.castSucc * r) := by
          refine Finset.prod_congr rfl fun i _ => ?_
          congr 1; ring
        have hp2 :
            ∏ i : Fin (n + 1), g i.castSucc ((y + cL * r) + (c i.castSucc - cL) * (r + t)) =
              ∏ i : Fin (n + 1),
                g i.castSucc ((y + c i.castSucc * r) + (c i.castSucc - cL) * t) := by
          refine Finset.prod_congr rfl fun i _ => ?_
          congr 1; ring
        rw [hu1, hu2, hp1, hp2]
        ring
      have hcomm :
          ∑ z : ZMod P, ∑ r : ZMod P, ∑ t : ZMod P, G z r * G z (r + t) =
            ∑ t : ZMod P, ∑ z : ZMod P, ∑ r : ZMod P, G z r * G z (r + t) := by
        simp_rw [Finset.sum_comm (s := Finset.univ) (f := fun r t => G _ r * G _ (r + t))]
        exact Finset.sum_comm
      rw [hpull, hcomm]
      simp_rw [hmid]
      dsimp only [Xt]
      rw [Finset.mul_sum]
    have hS_sq' : |S| ^ 2 ≤ (P : ℝ)⁻¹ * ∑ t : ZMod P, Xt t := hS_sq.trans_eq hsum_eq
    have hS_abs_sum : |S| ^ 2 ≤ (P : ℝ)⁻¹ * ∑ t : ZMod P, |Xt t| := by
      refine hS_sq'.trans (mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hP_nonneg))
      exact Finset.sum_le_sum fun t _ => le_abs_self (Xt t)
    have hpow_lift : |S| ^ (2 ^ (n + 2)) ≤ ((P : ℝ)⁻¹ * ∑ t : ZMod P, |Xt t|) ^ (2 ^ (n + 1)) := by
      rw [pow_succ', pow_mul]
      exact pow_le_pow_left₀ (sq_nonneg |S|) hS_abs_sum (2 ^ (n + 1))
    have hjensen :
        ((P : ℝ)⁻¹ * ∑ t : ZMod P, |Xt t|) ^ (2 ^ (n + 1)) ≤
          (P : ℝ)⁻¹ * ∑ t : ZMod P, |Xt t| ^ (2 ^ (n + 1)) := by
      have h0 := avg_pow_two_le hcard (n + 1) (fun t => |Xt t|) (fun t => abs_nonneg _)
      simpa only [ZMod.card P] using h0
    have hih :
        (P : ℝ)⁻¹ * ∑ t : ZMod P, |Xt t| ^ (2 ^ (n + 1)) ≤
          (P : ℝ)⁻¹ * ∑ t : ZMod P,
            ((P : ℝ) ^ (n + 2))⁻¹ * ∑ x : ZMod P, ∑ h : Fin (n + 1) → ZMod P,
              ∏ ω : Fin (n + 1) → Bool,
                ut t (x + ∑ i : Fin (n + 1), if ω i then h i else 0) := by
      refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun t _ => ?_) (inv_nonneg.mpr hP_nonneg)
      have hgt : ∀ i z, |gt t i z| ≤ 1 := fun i z => by
        dsimp only [gt]
        rw [abs_mul]
        exact mul_le_one₀ (hg i.castSucc z) (abs_nonneg _) (hg i.castSucc _)
      have hc' : ∀ i : Fin (n + 1), c i.castSucc ≠ 0 := fun i => hc i.castSucc
      exact gvN_general n (ut t) (gt t) hgt (fun i => c i.castSucc) hc'
    refine (hpow_lift.trans hjensen).trans (hih.trans_eq ?_)
    rw [← Finset.mul_sum, ← mul_assoc, show (P : ℝ)⁻¹ * ((P : ℝ) ^ (n + 2))⁻¹ =
        ((P : ℝ) ^ (n + 3))⁻¹ by rw [pow_succ, mul_inv]; ring]
    congr 1
    dsimp only [ut]
    rw [Fintype.sum_equiv (Equiv.mulLeft₀ (-cL) (neg_ne_zero.mpr hcL)) _
        (fun h_last => ∑ x : ZMod P, ∑ h : Fin (n + 1) → ZMod P,
          ∏ ω : Fin (n + 1) → Bool,
            u (x + ∑ i : Fin (n + 1), if ω i then h i else 0) *
              u ((x + ∑ i : Fin (n + 1), if ω i then h i else 0) + h_last))
        (fun _ => by simp only [equiv_mulLeft0_apply])]
    rw [← gowers_succ_eq u, Finset.sum_comm]

end OMA.Erdos138GvN

theorem OMA.solution : OMA.R_Erdos138_erdos_138_variants_upper_R1.H1 := by
  intro k _ P _ hP hkP f hf j₀
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 2 := ⟨k - 2, by omega⟩
  let u : ZMod P → ℝ := f j₀
  let g : Fin (n + 1) → ZMod P → ℝ := fun i => f (j₀.succAbove i)
  let c : Fin (n + 1) → ZMod P := fun i => ((j₀.succAbove i).1 : ZMod P) - (j₀.1 : ZMod P)
  have hg : ∀ i z, |g i z| ≤ 1 := fun i z => hf (j₀.succAbove i) z
  have hc : ∀ i, c i ≠ 0 := by
    intro i h0
    have heq : ((j₀.succAbove i).1 : ZMod P) = (j₀.1 : ZMod P) := sub_eq_zero.mp h0
    have hval := congrArg ZMod.val heq
    rw [ZMod.val_natCast_of_lt (lt_of_lt_of_le (j₀.succAbove i).2 hkP),
      ZMod.val_natCast_of_lt (lt_of_lt_of_le j₀.2 hkP)] at hval
    exact Fin.succAbove_ne j₀ i (Fin.ext hval)
  have hbound := @OMA.Erdos138GvN.gvN_general P _ ⟨hP⟩ n u g hg c hc
  have hsum :
      ∑ x : ZMod P, ∑ r : ZMod P, ∏ j : Fin (n + 2), f j (x + (j.1 : ZMod P) * r) =
        ∑ y : ZMod P, ∑ r : ZMod P, u y * ∏ i : Fin (n + 1), g i (y + c i * r) := by
    rw [Finset.sum_comm]
    rw [Finset.sum_comm (f := fun y r => u y * ∏ i : Fin (n + 1), g i (y + c i * r))]
    refine Finset.sum_congr rfl fun r _ => ?_
    refine Fintype.sum_equiv (Equiv.addRight ((j₀.1 : ZMod P) * r)) _ _ fun x => ?_
    rw [OMA.Erdos138GvN.equiv_addRight_apply, Fin.prod_univ_succAbove _ j₀]
    dsimp only [u, g, c]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    congr 1; ring
  rw [show n + 2 - 1 = n + 1 by omega]
  simpa only [hsum] using hbound
