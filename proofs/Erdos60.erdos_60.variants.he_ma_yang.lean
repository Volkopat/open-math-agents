import FormalConjectures.ErdosProblems.«60»

-- Problem: Erdős Problem 60 — he ma yang
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/60.lean:58 (declaration Erdos60.erdos_60.variants.he_ma_yang)
-- Credit: @fecheteluca (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Finset

namespace HMY

section core

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A symmetric 0/1 matrix with zero diagonal. -/
structure Adm (A : V → V → ℤ) : Prop where
  h01 : ∀ v u, A v u = 0 ∨ A v u = 1
  sym : ∀ v u, A v u = A u v
  diag : ∀ v, A v v = 0

def dg (A : V → V → ℤ) (v : V) : ℤ := ∑ u, A v u

def sv (A : V → V → ℤ) (q : ℤ) (v : V) : ℤ := dg A v - (q + 1)

def cdf (A : V → V → ℤ) (v x : V) : ℤ := ∑ u, A v u * A x u

def zf (A : V → V → ℤ) (v : V) : ℤ :=
  ∑ x, if x = v then 0 else (if cdf A v x = 0 then 1 else 0)

def pf (A : V → V → ℤ) (v : V) : ℤ :=
  ∑ x, if x = v then 0 else max (cdf A v x - 1) 0

def Asf (A : V → V → ℤ) (q : ℤ) (v : V) : ℤ := ∑ u, A v u * sv A q u

def lam (A : V → V → ℤ) (q : ℤ) (v : V) : ℤ := if sv A q v < 0 then 1 else 0

def alp (A : V → V → ℤ) (q : ℤ) (v : V) : ℤ := if 0 < sv A q v then 1 else 0

def mf (A : V → V → ℤ) (q : ℤ) (v : V) : ℤ := ∑ u, A v u * (1 - lam A q u)

def lf (A : V → V → ℤ) (q : ℤ) (v : V) : ℤ := ∑ u, A v u * lam A q u

def af (A : V → V → ℤ) (q : ℤ) (u : V) : ℤ := ∑ v, A u v * alp A q v

def clf (A : V → V → ℤ) (q : ℤ) (v w : V) : ℤ := ∑ u, lam A q u * (A u v * A u w)

theorem Adm.nonneg {A : V → V → ℤ} (h : Adm A) (v u : V) : 0 ≤ A v u := by
  rcases h.h01 v u with h1 | h1 <;> rw [h1] <;> norm_num

theorem Adm.le_one {A : V → V → ℤ} (h : Adm A) (v u : V) : A v u ≤ 1 := by
  rcases h.h01 v u with h1 | h1 <;> rw [h1] <;> norm_num

theorem Adm.sq {A : V → V → ℤ} (h : Adm A) (v u : V) : A v u * A v u = A v u := by
  rcases h.h01 v u with h1 | h1 <;> rw [h1] <;> norm_num

theorem bil {A : V → V → ℤ} (h : Adm A) (f g : V → ℤ) :
    ∑ v, g v * ∑ u, A v u * f u = ∑ u, f u * ∑ v, A u v * g v := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
  rw [h.sym v u]
  ring

theorem walks {A : V → V → ℤ} (h : Adm A) (v : V) :
    ∑ u, A v u * dg A u = ∑ x, cdf A v x := by
  unfold dg cdf
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun u _ => ?_
  rw [h.sym u x]

theorem cdf_self {A : V → V → ℤ} (h : Adm A) (v : V) : cdf A v v = dg A v := by
  unfold cdf dg
  exact Finset.sum_congr rfl fun u _ => h.sq v u

theorem cdf_nonneg {A : V → V → ℤ} (h : Adm A) (v x : V) : 0 ≤ cdf A v x :=
  Finset.sum_nonneg fun u _ => mul_nonneg (h.nonneg _ _) (h.nonneg _ _)

theorem zf_nonneg (A : V → V → ℤ) (v : V) : 0 ≤ zf A v :=
  Finset.sum_nonneg fun x _ => by split_ifs <;> norm_num

theorem pf_nonneg (A : V → V → ℤ) (v : V) : 0 ≤ pf A v :=
  Finset.sum_nonneg fun x _ => by
    split_ifs
    · exact le_refl _
    · exact le_max_right _ _

theorem sum_cdf {A : V → V → ℤ} (h : Adm A) (v : V) :
    ∑ x, cdf A v x = dg A v + ((Fintype.card V : ℤ) - 1) - zf A v + pf A v := by
  have h1 : ∀ x, cdf A v x = (if x = v then dg A v else 0) + (if x = v then 0 else 1)
      - (if x = v then 0 else (if cdf A v x = 0 then 1 else 0))
      + (if x = v then 0 else max (cdf A v x - 1) 0) := by
    intro x
    by_cases hx : x = v
    · subst hx
      simp only [if_true]
      rw [cdf_self h]
      ring
    · have h0 := cdf_nonneg h v x
      simp only [if_neg hx]
      by_cases hc : cdf A v x = 0
      · rw [if_pos hc, hc]
        norm_num
      · rw [if_neg hc]
        have h2 : 1 ≤ cdf A v x := by omega
        rw [max_eq_left (by omega)]
        ring
  have h2 : ∑ x : V, (if x = v then (0:ℤ) else 1) = (Fintype.card V : ℤ) - 1 := by
    have h3 : ∀ x : V, (if x = v then (0:ℤ) else 1) = 1 - (if x = v then 1 else 0) := by
      intro x
      split_ifs <;> norm_num
    simp_rw [h3]
    rw [Finset.sum_sub_distrib, Finset.sum_ite_eq' Finset.univ v]
    simp
  have h4 : ∑ x : V, (if x = v then dg A v else 0) = dg A v := by
    rw [Finset.sum_ite_eq' Finset.univ v]
    simp
  calc ∑ x, cdf A v x = ∑ x, ((if x = v then dg A v else 0) + (if x = v then 0 else 1)
      - (if x = v then 0 else (if cdf A v x = 0 then 1 else 0))
      + (if x = v then 0 else max (cdf A v x - 1) 0)) := Finset.sum_congr rfl fun x _ => h1 x
    _ = dg A v + ((Fintype.card V : ℤ) - 1) - zf A v + pf A v := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib, h2, h4]
      rfl

theorem local_id {A : V → V → ℤ} (h : Adm A) (q : ℤ)
    (hc : (Fintype.card V : ℤ) = q ^ 2 + q + 1) (v : V) :
    Asf A q v = - q * sv A q v - zf A v + pf A v := by
  have h1 : Asf A q v = ∑ u, A v u * dg A u - (q + 1) * dg A v := by
    unfold Asf sv
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
    unfold dg
    ring
  rw [h1, walks h, sum_cdf h, hc]
  unfold sv
  ring

theorem even_sym_sum (f : V → V → ℤ) (hs : ∀ u w, f u w = f w u) (hd : ∀ u, f u u = 0)
    (S : Finset V) : Even (∑ u ∈ S, ∑ w ∈ S, f u w) := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert x S hx ih =>
    rw [Finset.sum_insert hx]
    have h1 : ∑ w ∈ insert x S, f x w = ∑ w ∈ S, f x w := by
      rw [Finset.sum_insert hx, hd, zero_add]
    have h2 : ∑ u ∈ S, ∑ w ∈ insert x S, f u w
        = ∑ u ∈ S, f x u + ∑ u ∈ S, ∑ w ∈ S, f u w := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [Finset.sum_insert hx, hs u x]
    rw [h1, h2]
    obtain ⟨r, hr⟩ := ih
    exact ⟨∑ w ∈ S, f x w + r, by rw [hr]; ring⟩

theorem parity {A : V → V → ℤ} (h : Adm A) (v : V) (hodd : ¬ Even (dg A v)) :
    1 ≤ zf A v + pf A v := by
  have hz := zf_nonneg A v
  have hp := pf_nonneg A v
  by_contra hcon
  have hz0 : zf A v = 0 := by omega
  have hp0 : pf A v = 0 := by omega
  have hzt : ∀ x, x ≠ v → cdf A v x ≠ 0 := by
    intro x hx hc
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => by split_ifs <;> norm_num)).mp hz0
      x (Finset.mem_univ x)
    rw [if_neg hx, if_pos hc] at h1
    norm_num at h1
  have hpt : ∀ x, x ≠ v → cdf A v x ≤ 1 := by
    intro x hx
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => by
      split_ifs
      · exact le_refl _
      · exact le_max_right _ _)).mp hp0 x (Finset.mem_univ x)
    rw [if_neg hx] at h1
    have h2 := le_max_left (cdf A v x - 1) 0
    omega
  have hone : ∀ x, x ≠ v → cdf A v x = 1 := by
    intro x hx
    have h1 := cdf_nonneg h v x
    have h2 := hzt x hx
    have h3 := hpt x hx
    omega
  have h1 : ∑ u, A v u * cdf A v u = dg A v := by
    unfold dg
    refine Finset.sum_congr rfl fun u _ => ?_
    by_cases hu : u = v
    · subst hu
      rw [h.diag]
      ring
    · rw [hone u hu, mul_one]
  have h2 : ∑ u, A v u * cdf A v u = ∑ u, ∑ w, A v u * A v w * A u w := by
    refine Finset.sum_congr rfl fun u _ => ?_
    unfold cdf
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    ring
  have h3 := even_sym_sum (fun u w => A v u * A v w * A u w)
    (fun u w => by rw [h.sym u w]; ring) (fun u => by rw [h.diag u]; ring) Finset.univ
  rw [← h2, h1] at h3
  exact hodd h3

end core

section arith

theorem arith0 (q a σ P : ℤ) (hq : 32 ≤ q) (hP0 : 0 ≤ P) (hP : 16 * P ≤ q)
    (ha0 : 0 ≤ a) (hσ0 : 0 ≤ σ)
    (C1 : q + 2 ≤ a + σ + 2 * P)
    (C10 : q * σ ≤ a * (σ + q - 1) + P) : q ≤ 4 * a := by
  have ha1 : 1 ≤ a := by
    by_contra hcon
    have ha : a = 0 := by omega
    subst ha
    have h1 : q * σ ≤ P := by linarith
    have h2 : σ ≤ 0 := by
      by_contra h3
      have h4 : 1 ≤ σ := by omega
      nlinarith
    omega
  by_contra hcon
  have h1 : 4 * a ≤ q - 1 := by omega
  have h2 : 0 ≤ (q - a) * (σ - (q + 2 - a - 2 * P)) :=
    mul_nonneg (by omega) (by omega)
  nlinarith [mul_nonneg (show (0:ℤ) ≤ q by omega) (show (0:ℤ) ≤ q - 4 * a by omega),
    mul_nonneg (show (0:ℤ) ≤ q by omega) (show (0:ℤ) ≤ q - 16 * P by omega),
    sq_nonneg a, mul_nonneg ha0 hP0]

theorem arith1 (q a ℓ P E : ℤ) (hq : 32 ≤ q) (hP0 : 0 ≤ P) (hP : 16 * P ≤ q)
    (ha : q ≤ 4 * a) (hℓ0 : 0 ≤ ℓ)
    (C8 : q * a + q + 2 ≤ E + 2 * P)
    (C7 : E ^ 2 ≤ ℓ * (E + a ^ 2 + P)) : q ^ 2 * a ≤ ℓ * (q + a + 1) := by
  have ha1 : 1 ≤ a := by omega
  have hPa : P ≤ a := by omega
  have hE : q * a ≤ E := by linarith
  by_cases hc : q * a ≤ ℓ
  · nlinarith [mul_le_mul_of_nonneg_left hc (show (0:ℤ) ≤ q by omega),
      mul_nonneg hℓ0 (show (0:ℤ) ≤ a + 1 by omega)]
  · push_neg at hc
    have h1 : q * a * (q * a - ℓ) ≤ E * (E - ℓ) := by
      nlinarith [mul_nonneg (show (0:ℤ) ≤ E - q * a by linarith) (show (0:ℤ) ≤ E - ℓ by linarith),
        mul_nonneg (show (0:ℤ) ≤ E - q * a by linarith) (show (0:ℤ) ≤ q * a by nlinarith)]
    have h2 : E * (E - ℓ) ≤ ℓ * (a ^ 2 + a) := by
      nlinarith [mul_le_mul_of_nonneg_left hPa hℓ0]
    have h3 : a * (q * (q * a - ℓ) - ℓ * (a + 1)) ≤ 0 := by nlinarith
    have h4 : q * (q * a - ℓ) - ℓ * (a + 1) ≤ 0 := by
      by_contra h5
      push_neg at h5
      nlinarith [mul_pos (show (0:ℤ) < a by omega) h5]
    nlinarith

theorem arith2 (q a ℓ P : ℤ) (hq : 32 ≤ q) (hP0 : 0 ≤ P) (hP : 16 * P ≤ q)
    (ha : q ≤ 4 * a) (hsmall : a ≤ q - 1) (hℓ0 : 0 ≤ ℓ)
    (key : q ^ 2 * a ≤ ℓ * (q + a + 1))
    (C5 : (q - 1) * ℓ ≤ (q + 1) * a + (q - 1) ^ 2 + P) : False := by
  have hl : ℓ ≤ 2 * q := by
    by_contra hcon
    push_neg at hcon
    nlinarith [mul_nonneg (show (0:ℤ) ≤ q - 1 by omega) (show (0:ℤ) ≤ ℓ - (2 * q + 1) by omega),
      mul_nonneg (show (0:ℤ) ≤ q + 1 by omega) (show (0:ℤ) ≤ q - 1 - a by omega)]
  have h5 : ℓ * (q + a + 1) ≤ 2 * q * (2 * q) := by
    nlinarith [mul_nonneg hℓ0 (show (0:ℤ) ≤ q - 1 - a by omega),
      mul_nonneg (show (0:ℤ) ≤ 2 * q - ℓ by omega) (show (0:ℤ) ≤ q by omega)]
  have h6 : q ^ 2 * (a - 4) ≤ 0 := by nlinarith
  have h7 : a ≤ 4 := by
    by_contra h8
    push_neg at h8
    nlinarith [mul_pos (show (0:ℤ) < q ^ 2 by positivity) (show (0:ℤ) < a - 4 by omega)]
  omega

theorem arith3 (q a ℓ P : ℤ) (hq : 32 ≤ q) (hP0 : 0 ≤ P) (hP : 16 * P ≤ q)
    (ha : q ≤ 4 * a) (hbig : q ≤ a) (hℓ0 : 0 ≤ ℓ)
    (key : q ^ 2 * a ≤ ℓ * (q + a + 1))
    (C5 : (q - 1) * ℓ ≤ (q + 1) * a + (q - 1) ^ 2 + P)
    (C9 : a + ℓ ≤ q ^ 2 + q + 1) : False := by
  have hPa : P ≤ a := by omega
  have ha1 : 1 ≤ a := by omega
  have hl3 : ℓ ≤ 3 * a := by
    by_contra hcon
    push_neg at hcon
    nlinarith [mul_nonneg (show (0:ℤ) ≤ q - 1 by omega) (show (0:ℤ) ≤ ℓ - (3 * a + 1) by omega),
      mul_nonneg (show (0:ℤ) ≤ q - 1 by omega) (show (0:ℤ) ≤ a - q by omega),
      mul_nonneg (show (0:ℤ) ≤ q - 4 by omega) (show (0:ℤ) ≤ a by omega)]
  have h1 : q ^ 2 * a ≤ 3 * a * (q + a + 1) := by
    nlinarith [mul_nonneg (show (0:ℤ) ≤ 3 * a - ℓ by omega) (show (0:ℤ) ≤ q + a + 1 by omega)]
  have h2 : q ^ 2 ≤ 3 * (q + a + 1) := by
    by_contra h3
    push_neg at h3
    nlinarith [mul_pos (show (0:ℤ) < a by omega) (show (0:ℤ) < q ^ 2 - 3 * (q + a + 1) by omega)]
  have h3 : q ^ 2 - 3 * q - 3 ≤ 3 * a := by linarith
  have h4 : 3 * ℓ ≤ 2 * q ^ 2 + 6 * q + 6 := by linarith
  have h5 : a * (q ^ 2 - ℓ) ≤ ℓ * (q + 1) := by nlinarith
  have hq2 : (32:ℤ) * q ≤ q ^ 2 := by nlinarith
  have h6 : (q ^ 2 - 3 * q - 3) * (q ^ 2 - 6 * q - 6) ≤ 3 * a * (3 * (q ^ 2 - ℓ)) := by
    have h7 : 0 ≤ q ^ 2 - 3 * q - 3 := by nlinarith
    have h8 : q ^ 2 - 6 * q - 6 ≤ 3 * (q ^ 2 - ℓ) := by linarith
    have h9 : 0 ≤ q ^ 2 - 6 * q - 6 := by nlinarith
    calc (q ^ 2 - 3 * q - 3) * (q ^ 2 - 6 * q - 6)
        ≤ (3 * a) * (q ^ 2 - 6 * q - 6) := mul_le_mul_of_nonneg_right h3 h9
      _ ≤ (3 * a) * (3 * (q ^ 2 - ℓ)) := mul_le_mul_of_nonneg_left h8 (by omega)
  have h10 : 3 * a * (3 * (q ^ 2 - ℓ)) ≤ 3 * (2 * q ^ 2 + 6 * q + 6) * (q + 1) := by
    have h11 : 3 * a * (3 * (q ^ 2 - ℓ)) = 9 * (a * (q ^ 2 - ℓ)) := by ring
    have h12 : 9 * (ℓ * (q + 1)) ≤ 3 * (2 * q ^ 2 + 6 * q + 6) * (q + 1) := by
      nlinarith [mul_le_mul_of_nonneg_right h4 (show (0:ℤ) ≤ q + 1 by omega)]
    linarith
  have h13 : (q ^ 2 - 3 * q - 3) * (q ^ 2 - 6 * q - 6) ≤ 3 * (2 * q ^ 2 + 6 * q + 6) * (q + 1) :=
    le_trans h6 h10
  have h14 : q ^ 2 * (q ^ 2 - 15 * q - 15) ≤ 0 := by nlinarith
  have h15 : 0 < q ^ 2 - 15 * q - 15 := by nlinarith
  nlinarith [mul_pos (show (0:ℤ) < q ^ 2 by positivity) h15]

theorem arith (q a σ ℓ P E : ℤ) (hq : 32 ≤ q) (hP0 : 0 ≤ P) (hP : 16 * P ≤ q)
    (ha0 : 0 ≤ a) (hσ0 : 0 ≤ σ) (hℓ0 : 0 ≤ ℓ)
    (C1 : q + 2 ≤ a + σ + 2 * P)
    (C8 : q * a + q + 2 ≤ E + 2 * P)
    (C10 : q * σ ≤ a * (σ + q - 1) + P)
    (C5 : (q - 1) * ℓ ≤ (q + 1) * a + (q - 1) ^ 2 + P)
    (C7 : E ^ 2 ≤ ℓ * (E + a ^ 2 + P))
    (C9 : a + ℓ ≤ q ^ 2 + q + 1) : False := by
  have h4a := arith0 q a σ P hq hP0 hP ha0 hσ0 C1 C10
  have key := arith1 q a ℓ P E hq hP0 hP h4a hℓ0 C8 C7
  rcases le_or_gt a (q - 1) with hsmall | hbig
  · exact arith2 q a ℓ P hq hP0 hP h4a hsmall hℓ0 key C5
  · exact arith3 q a ℓ P hq hP0 hP h4a (by omega) hℓ0 key C5 C9

end arith

section ineq

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem lam_cases (A : V → V → ℤ) (q : ℤ) (v : V) :
    (sv A q v < 0 ∧ lam A q v = 1 ∧ alp A q v = 0) ∨
    (sv A q v = 0 ∧ lam A q v = 0 ∧ alp A q v = 0) ∨
    (0 < sv A q v ∧ lam A q v = 0 ∧ alp A q v = 1) := by
  unfold lam alp
  rcases lt_trichotomy (sv A q v) 0 with h1 | h1 | h1
  · exact Or.inl ⟨h1, if_pos h1, if_neg (by omega)⟩
  · exact Or.inr (Or.inl ⟨h1, if_neg (by omega), if_neg (by omega)⟩)
  · exact Or.inr (Or.inr ⟨h1, if_neg (by omega), if_pos h1⟩)

theorem lam_nonneg (A : V → V → ℤ) (q : ℤ) (v : V) : 0 ≤ lam A q v := by
  unfold lam
  split_ifs <;> norm_num

theorem lam_le_one (A : V → V → ℤ) (q : ℤ) (v : V) : lam A q v ≤ 1 := by
  unfold lam
  split_ifs <;> norm_num

theorem alp_nonneg (A : V → V → ℤ) (q : ℤ) (v : V) : 0 ≤ alp A q v := by
  unfold alp
  split_ifs <;> norm_num

theorem alp_le_one (A : V → V → ℤ) (q : ℤ) (v : V) : alp A q v ≤ 1 := by
  unfold alp
  split_ifs <;> norm_num

theorem lam_sq (A : V → V → ℤ) (q : ℤ) (v : V) : lam A q v * lam A q v = lam A q v := by
  unfold lam
  split_ifs <;> norm_num

theorem mf_add_lf (A : V → V → ℤ) (q : ℤ) (v : V) : mf A q v + lf A q v = dg A v := by
  unfold mf lf dg
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u _ => ?_
  ring

theorem dg_eq (A : V → V → ℤ) (q : ℤ) (v : V) : dg A v = sv A q v + q + 1 := by
  unfold sv
  ring

theorem mf_nonneg {A : V → V → ℤ} (h : Adm A) (q : ℤ) (v : V) : 0 ≤ mf A q v :=
  Finset.sum_nonneg fun u _ => mul_nonneg (h.nonneg v u)
    (by have := lam_le_one A q u; omega)

theorem lf_nonneg {A : V → V → ℤ} (h : Adm A) (q : ℤ) (v : V) : 0 ≤ lf A q v :=
  Finset.sum_nonneg fun u _ => mul_nonneg (h.nonneg v u) (lam_nonneg A q u)

theorem af_nonneg {A : V → V → ℤ} (h : Adm A) (q : ℤ) (v : V) : 0 ≤ af A q v :=
  Finset.sum_nonneg fun u _ => mul_nonneg (h.nonneg v u) (alp_nonneg A q u)

theorem af_le_dg {A : V → V → ℤ} (h : Adm A) (q : ℤ) (v : V) : af A q v ≤ dg A v := by
  unfold af dg
  refine Finset.sum_le_sum fun u _ => ?_
  have h1 := h.nonneg v u
  have h2 := alp_le_one A q u
  nlinarith [mul_nonneg h1 (show (0:ℤ) ≤ 1 - alp A q u by omega)]

theorem dc1 {A : V → V → ℤ} (h : Adm A) (q : ℤ) :
    ∑ v, (1 - lam A q v) * Asf A q v = ∑ u, sv A q u * mf A q u :=
  bil h (sv A q) (fun v => 1 - lam A q v)

theorem pv {A : V → V → ℤ} (h : Adm A) (q : ℤ) (hq : Even q)
    (hc : (Fintype.card V : ℤ) = q ^ 2 + q + 1) (u : V) :
    (q + 1) * sv A q u + 1 - 2 * pf A u + alp A q u * (mf A q u - 1 - sv A q u)
      ≤ sv A q u * mf A q u - (1 - lam A q u) * Asf A q u := by
  have hloc := local_id h q hc u
  have hz := zf_nonneg A u
  have hp := pf_nonneg A u
  have hm := mf_nonneg h q u
  have hl := lf_nonneg h q u
  have hml := mf_add_lf A q u
  have hdg := dg_eq A q u
  rcases lam_cases A q u with ⟨hs, hla, hal⟩ | ⟨hs, hla, hal⟩ | ⟨hs, hla, hal⟩
  · rw [hla, hal]
    nlinarith [mul_nonneg (show (0:ℤ) ≤ - sv A q u by omega)
        (show (0:ℤ) ≤ sv A q u + q + 1 - mf A q u by omega),
      mul_nonneg (show (0:ℤ) ≤ - sv A q u - 1 by omega) (show (0:ℤ) ≤ - sv A q u + 1 by omega)]
  · have hodd : ¬ Even (dg A u) := by
      rintro ⟨t, ht⟩
      obtain ⟨r, hr⟩ := hq
      omega
    have hpar := parity h u hodd
    rw [hs] at hloc
    rw [hla, hal, hs]
    linarith
  · rw [hla, hal]
    nlinarith [mul_nonneg (show (0:ℤ) ≤ sv A q u - 1 by omega) hm]

theorem sum_sv {A : V → V → ℤ} (q : ℤ)
    (hc : (Fintype.card V : ℤ) = q ^ 2 + q + 1)
    (hE : q * (q + 1) ^ 2 + 2 ≤ ∑ v, dg A v) : 1 - q ≤ ∑ v, sv A q v := by
  unfold sv
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hc]
  nlinarith

theorem sum_alp_mf_nonneg {A : V → V → ℤ} (h : Adm A) (q : ℤ) :
    0 ≤ ∑ v, alp A q v * mf A q v :=
  Finset.sum_nonneg fun v _ => mul_nonneg (alp_nonneg A q v) (mf_nonneg h q v)

theorem ineqK {A : V → V → ℤ} (h : Adm A) (q : ℤ) (hq : Even q) (hq0 : 0 ≤ q)
    (hc : (Fintype.card V : ℤ) = q ^ 2 + q + 1)
    (hE : q * (q + 1) ^ 2 + 2 ≤ ∑ v, dg A v) :
    ∑ v, alp A q v * mf A q v + q + 2
      ≤ ∑ v, alp A q v + ∑ v, alp A q v * sv A q v + 2 * ∑ v, pf A v := by
  have h1 := Finset.sum_le_sum (fun u (_ : u ∈ (Finset.univ : Finset V)) => pv h q hq hc u)
  have h2 := dc1 h q
  have h3 := sum_sv q hc hE
  have h4 : ∑ u, ((q + 1) * sv A q u + 1 - 2 * pf A u
        + alp A q u * (mf A q u - 1 - sv A q u))
      = (q + 1) * ∑ u, sv A q u + (Fintype.card V : ℤ) - 2 * ∑ u, pf A u
        + (∑ u, alp A q u * mf A q u - ∑ u, alp A q u - ∑ u, alp A q u * sv A q u) := by
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_sub, mul_one,
      ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have h5 : ∑ u, (sv A q u * mf A q u - (1 - lam A q u) * Asf A q u) = 0 := by
    rw [Finset.sum_sub_distrib, h2, sub_self]
  rw [h4, h5, hc] at h1
  nlinarith [mul_nonneg (show (0:ℤ) ≤ q + 1 by omega)
    (show (0:ℤ) ≤ ∑ v, sv A q v - (1 - q) by linarith)]

theorem E_eq (A : V → V → ℤ) (q : ℤ) :
    ∑ v, alp A q v * lf A q v
      = ∑ v, alp A q v * sv A q v + (q + 1) * ∑ v, alp A q v
        - ∑ v, alp A q v * mf A q v := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun v _ => ?_
  have h1 := mf_add_lf A q v
  have h2 := dg_eq A q v
  have h3 : lf A q v = sv A q v + q + 1 - mf A q v := by omega
  rw [h3]
  ring

theorem ineqC8 {A : V → V → ℤ} (h : Adm A) (q : ℤ) (hq : Even q) (hq0 : 0 ≤ q)
    (hc : (Fintype.card V : ℤ) = q ^ 2 + q + 1)
    (hE : q * (q + 1) ^ 2 + 2 ≤ ∑ v, dg A v) :
    q * ∑ v, alp A q v + q + 2 ≤ ∑ v, alp A q v * lf A q v + 2 * ∑ v, pf A v := by
  have h1 := ineqK h q hq hq0 hc hE
  have h2 := E_eq A q
  linarith

theorem lam_sv_sum (A : V → V → ℤ) (q : ℤ) :
    ∑ u, lam A q u * (- sv A q u) = ∑ u, alp A q u * sv A q u - ∑ u, sv A q u := by
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun u _ => ?_
  rcases lam_cases A q u with ⟨hs, hla, hal⟩ | ⟨hs, hla, hal⟩ | ⟨hs, hla, hal⟩
  · rw [hla, hal]
    ring
  · rw [hla, hal, hs]
    ring
  · rw [hla, hal]
    ring

theorem Asf_ge {A : V → V → ℤ} (h : Adm A) (q : ℤ) (v : V) :
    - ∑ u, lam A q u * (- sv A q u) ≤ Asf A q v := by
  unfold Asf
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum fun u _ => ?_
  have h0 := h.nonneg v u
  have h1 := h.le_one v u
  rcases lam_cases A q u with ⟨hs, hla, hal⟩ | ⟨hs, hla, hal⟩ | ⟨hs, hla, hal⟩
  · rw [hla]
    nlinarith [mul_nonneg (show (0:ℤ) ≤ 1 - A v u by omega)
      (show (0:ℤ) ≤ - sv A q u by omega)]
  · rw [hla, hs]
    simp
  · rw [hla]
    nlinarith [mul_nonneg h0 (show (0:ℤ) ≤ sv A q u by omega)]

theorem neg_Asf_le {A : V → V → ℤ} (h : Adm A) (q : ℤ) (v : V) :
    - Asf A q v ≤ ∑ u, A v u * (lam A q u * (- sv A q u)) := by
  unfold Asf
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum fun u _ => ?_
  have h0 := h.nonneg v u
  rcases lam_cases A q u with ⟨hs, hla, hal⟩ | ⟨hs, hla, hal⟩ | ⟨hs, hla, hal⟩
  · rw [hla]
    exact le_of_eq (by ring)
  · rw [hla, hs]
    simp
  · rw [hla]
    nlinarith [mul_nonneg h0 (show (0:ℤ) ≤ sv A q u by omega)]

theorem ineqC10 {A : V → V → ℤ} (h : Adm A) (q : ℤ)
    (hc : (Fintype.card V : ℤ) = q ^ 2 + q + 1)
    (hE : q * (q + 1) ^ 2 + 2 ≤ ∑ v, dg A v) :
    q * ∑ v, alp A q v * sv A q v
      ≤ (∑ v, alp A q v) * (∑ v, alp A q v * sv A q v + q - 1) + ∑ v, pf A v := by
  have hD := lam_sv_sum A q
  have hS := sum_sv q hc hE
  have ha0 : 0 ≤ ∑ v, alp A q v := Finset.sum_nonneg fun v _ => alp_nonneg A q v
  have h1 : ∀ v, alp A q v * (q * sv A q v)
      ≤ alp A q v * (∑ u, lam A q u * (- sv A q u)) + pf A v := by
    intro v
    have hloc := local_id h q hc v
    have hz := zf_nonneg A v
    have hp := pf_nonneg A v
    have hge := Asf_ge h q v
    rcases lam_cases A q v with ⟨hs, hla, hal⟩ | ⟨hs, hla, hal⟩ | ⟨hs, hla, hal⟩
    · rw [hal]
      linarith
    · rw [hal]
      linarith
    · rw [hal]
      linarith
  have h2 := Finset.sum_le_sum (fun v (_ : v ∈ (Finset.univ : Finset V)) => h1 v)
  rw [Finset.sum_add_distrib, ← Finset.sum_mul] at h2
  have h3 : ∑ v, alp A q v * (q * sv A q v) = q * ∑ v, alp A q v * sv A q v := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    ring
  rw [h3, hD] at h2
  nlinarith [mul_nonneg ha0 (show (0:ℤ) ≤ ∑ v, sv A q v + q - 1 by linarith)]

theorem bil_E {A : V → V → ℤ} (h : Adm A) (q : ℤ) :
    ∑ v, alp A q v * lf A q v = ∑ u, lam A q u * af A q u :=
  bil h (lam A q) (alp A q)

theorem ineqC5 {A : V → V → ℤ} (h : Adm A) (q : ℤ) (hq1 : 1 ≤ q)
    (hc : (Fintype.card V : ℤ) = q ^ 2 + q + 1)
    (hE : q * (q + 1) ^ 2 + 2 ≤ ∑ v, dg A v) :
    (q - 1) * ∑ v, lam A q v
      ≤ (q + 1) * ∑ v, alp A q v + (q - 1) ^ 2 + ∑ v, pf A v := by
  have hD := lam_sv_sum A q
  have hS := sum_sv q hc hE
  have hEeq := E_eq A q
  have hM := sum_alp_mf_nonneg h q
  have hbE := bil_E h q
  have h1 : ∀ v, alp A q v * (q * sv A q v)
      ≤ alp A q v * (∑ u, A v u * (lam A q u * (- sv A q u))) + pf A v := by
    intro v
    have hloc := local_id h q hc v
    have hz := zf_nonneg A v
    have hp := pf_nonneg A v
    have hge := neg_Asf_le h q v
    rcases lam_cases A q v with ⟨hs, hla, hal⟩ | ⟨hs, hla, hal⟩ | ⟨hs, hla, hal⟩
    · rw [hal]
      linarith
    · rw [hal]
      linarith
    · rw [hal]
      linarith
  have h2 := Finset.sum_le_sum (fun v (_ : v ∈ (Finset.univ : Finset V)) => h1 v)
  rw [Finset.sum_add_distrib] at h2
  have h3 : ∑ v, alp A q v * (q * sv A q v) = q * ∑ v, alp A q v * sv A q v := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    ring
  have h4 : ∑ v, alp A q v * (∑ u, A v u * (lam A q u * (- sv A q u)))
      = ∑ u, (lam A q u * (- sv A q u)) * af A q u :=
    bil h (fun u => lam A q u * (- sv A q u)) (alp A q)
  have h5 : ∀ u, (lam A q u * (- sv A q u)) * af A q u
      ≤ lam A q u * af A q u + (q - 1) * (lam A q u * (- sv A q u) - lam A q u) := by
    intro u
    have ha0 := af_nonneg h q u
    have ha1 := af_le_dg h q u
    have hdg := dg_eq A q u
    rcases lam_cases A q u with ⟨hs, hla, hal⟩ | ⟨hs, hla, hal⟩ | ⟨hs, hla, hal⟩
    · rw [hla]
      rcases eq_or_lt_of_le (show sv A q u ≤ -1 by omega) with h6 | h6
      · rw [h6]
        linarith
      · nlinarith [mul_nonneg (show (0:ℤ) ≤ - sv A q u - 1 by omega)
          (show (0:ℤ) ≤ q - 1 - af A q u by omega)]
    · rw [hla]
      simp
    · rw [hla]
      simp
  have h6 := Finset.sum_le_sum (fun u (_ : u ∈ (Finset.univ : Finset V)) => h5 u)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib] at h6
  rw [h3, h4] at h2
  rw [hD, ← hbE] at h6
  nlinarith [mul_nonneg (show (0:ℤ) ≤ q - 1 by omega)
    (show (0:ℤ) ≤ ∑ v, sv A q v + q - 1 by linarith)]

theorem clf_self {A : V → V → ℤ} (h : Adm A) (q : ℤ) (v : V) :
    clf A q v v = lf A q v := by
  unfold clf lf
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [h.sq u v, h.sym u v]
  ring

theorem clf_nonneg {A : V → V → ℤ} (h : Adm A) (q : ℤ) (v w : V) : 0 ≤ clf A q v w :=
  Finset.sum_nonneg fun u _ => mul_nonneg (lam_nonneg A q u)
    (mul_nonneg (h.nonneg u v) (h.nonneg u w))

theorem clf_le_cdf {A : V → V → ℤ} (h : Adm A) (q : ℤ) (v w : V) :
    clf A q v w ≤ cdf A v w := by
  unfold clf cdf
  refine Finset.sum_le_sum fun u _ => ?_
  rw [h.sym u v, h.sym u w]
  have h1 := mul_nonneg (h.nonneg v u) (h.nonneg w u)
  have h2 := lam_le_one A q u
  nlinarith [mul_nonneg h1 (show (0:ℤ) ≤ 1 - lam A q u by omega)]

theorem clf_term {A : V → V → ℤ} (h : Adm A) (q : ℤ) (v w : V) :
    alp A q w * clf A q v w
      ≤ (if w = v then lf A q v else 0) + alp A q w
        + (if w = v then 0 else max (cdf A v w - 1) 0) := by
  have ha0 := alp_nonneg A q w
  have ha1 := alp_le_one A q w
  by_cases hw : w = v
  · subst hw
    rw [if_pos rfl, if_pos rfl, clf_self h]
    have hl := lf_nonneg h q w
    nlinarith [mul_nonneg hl (show (0:ℤ) ≤ 1 - alp A q w by omega)]
  · rw [if_neg hw, if_neg hw]
    have h1 := clf_le_cdf h q v w
    have h2 := le_max_left (cdf A v w - 1) 0
    have h3 := le_max_right (cdf A v w - 1) 0
    nlinarith [mul_nonneg ha0
        (show (0:ℤ) ≤ 1 + max (cdf A v w - 1) 0 - clf A q v w by omega),
      mul_nonneg (show (0:ℤ) ≤ 1 - alp A q w by omega) h3]

theorem clf_sum {A : V → V → ℤ} (h : Adm A) (q : ℤ) (v : V) :
    ∑ w, alp A q w * clf A q v w ≤ lf A q v + ∑ w, alp A q w + pf A v := by
  have h1 := Finset.sum_le_sum (fun w (_ : w ∈ (Finset.univ : Finset V)) => clf_term h q v w)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ v] at h1
  simp only [Finset.mem_univ, if_true] at h1
  exact h1

theorem sum_lam_af_sq (A : V → V → ℤ) (q : ℤ) :
    ∑ u, lam A q u * (af A q u * af A q u)
      = ∑ v, alp A q v * ∑ w, alp A q w * clf A q v w := by
  unfold af clf
  simp_rw [Finset.sum_mul_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun u _ => ?_
  ring

theorem sum_lam_af_sq_le {A : V → V → ℤ} (h : Adm A) (q : ℤ) :
    ∑ u, lam A q u * (af A q u * af A q u)
      ≤ ∑ v, alp A q v * lf A q v + (∑ v, alp A q v) * (∑ v, alp A q v)
        + ∑ v, pf A v := by
  rw [sum_lam_af_sq]
  have h1 : ∀ v, alp A q v * ∑ w, alp A q w * clf A q v w
      ≤ alp A q v * lf A q v + alp A q v * (∑ w, alp A q w) + pf A v := by
    intro v
    have h2 := clf_sum h q v
    have ha0 := alp_nonneg A q v
    have ha1 := alp_le_one A q v
    have hp := pf_nonneg A v
    nlinarith [mul_le_mul_of_nonneg_left h2 ha0,
      mul_nonneg hp (show (0:ℤ) ≤ 1 - alp A q v by omega)]
  have h3 := Finset.sum_le_sum (fun v (_ : v ∈ (Finset.univ : Finset V)) => h1 v)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul] at h3
  exact h3

theorem ineqC7 {A : V → V → ℤ} (h : Adm A) (q : ℤ) :
    (∑ v, alp A q v * lf A q v) ^ 2
      ≤ (∑ v, lam A q v)
        * (∑ v, alp A q v * lf A q v + (∑ v, alp A q v) ^ 2 + ∑ v, pf A v) := by
  have h1 : (∑ u, lam A q u * (lam A q u * af A q u)) ^ 2
      ≤ (∑ u, lam A q u ^ 2) * ∑ u, (lam A q u * af A q u) ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (lam A q) (fun u => lam A q u * af A q u)
  have h2 : ∑ u, lam A q u * (lam A q u * af A q u) = ∑ v, alp A q v * lf A q v := by
    rw [bil_E h q]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [← mul_assoc, lam_sq]
  have h3 : ∑ u, lam A q u ^ 2 = ∑ u, lam A q u := by
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [pow_two, lam_sq]
  have h4 : ∑ u, (lam A q u * af A q u) ^ 2
      = ∑ u, lam A q u * (af A q u * af A q u) := by
    refine Finset.sum_congr rfl fun u _ => ?_
    have h5 := lam_sq A q u
    calc (lam A q u * af A q u) ^ 2
        = (lam A q u * lam A q u) * (af A q u * af A q u) := by ring
      _ = lam A q u * (af A q u * af A q u) := by rw [h5]
  have h5 := sum_lam_af_sq_le h q
  have h6 : 0 ≤ ∑ v, lam A q v := Finset.sum_nonneg fun v _ => lam_nonneg A q v
  rw [h2, h3, h4] at h1
  refine le_trans h1 (mul_le_mul_of_nonneg_left ?_ h6)
  rw [pow_two]
  exact h5

theorem ineqC9 (A : V → V → ℤ) (q : ℤ) :
    ∑ v, alp A q v + ∑ v, lam A q v ≤ (Fintype.card V : ℤ) := by
  rw [← Finset.sum_add_distrib]
  have h1 : ∀ v ∈ (Finset.univ : Finset V), alp A q v + lam A q v ≤ 1 := by
    intro v _
    rcases lam_cases A q v with ⟨hs, hla, hal⟩ | ⟨hs, hla, hal⟩ | ⟨hs, hla, hal⟩ <;>
      rw [hla, hal] <;> norm_num
  have h2 := Finset.sum_le_sum h1
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at h2
  exact h2

theorem supersat {A : V → V → ℤ} (h : Adm A) (q : ℤ) (hq : 32 ≤ q) (heven : Even q)
    (hc : (Fintype.card V : ℤ) = q ^ 2 + q + 1)
    (hE : q * (q + 1) ^ 2 + 2 ≤ ∑ v, dg A v) : q < 16 * ∑ v, pf A v := by
  by_contra hcon
  push_neg at hcon
  have hK := ineqK h q heven (by omega) hc hE
  have hM := sum_alp_mf_nonneg h q
  have hσ : 0 ≤ ∑ v, alp A q v * sv A q v := by
    refine Finset.sum_nonneg fun v _ => ?_
    rcases lam_cases A q v with ⟨hs, hla, hal⟩ | ⟨hs, hla, hal⟩ | ⟨hs, hla, hal⟩
    · rw [hal]
      simp
    · rw [hal]
      simp
    · rw [hal]
      omega
  have h9 := ineqC9 A q
  rw [hc] at h9
  exact arith q (∑ v, alp A q v) (∑ v, alp A q v * sv A q v) (∑ v, lam A q v)
    (∑ v, pf A v) (∑ v, alp A q v * lf A q v) hq
    (Finset.sum_nonneg fun v _ => pf_nonneg A v) hcon
    (Finset.sum_nonneg fun v _ => alp_nonneg A q v) hσ
    (Finset.sum_nonneg fun v _ => lam_nonneg A q v)
    (by linarith) (ineqC8 h q heven (by omega) hc hE) (ineqC10 h q hc hE)
    (ineqC5 h q (by omega) hc hE) (ineqC7 h q) h9

end ineq

section graph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The 0/1 adjacency matrix of a graph. -/
def adjM (G : SimpleGraph V) [DecidableRel G.Adj] (v u : V) : ℤ := if G.Adj v u then 1 else 0

/-- Common neighbours. -/
def cn (G : SimpleGraph V) [DecidableRel G.Adj] (v x : V) : Finset V :=
  Finset.univ.filter fun u => G.Adj v u ∧ G.Adj x u

theorem adm_adjM (G : SimpleGraph V) [DecidableRel G.Adj] : Adm (adjM G) where
  h01 := fun v u => by
    unfold adjM
    split_ifs
    · exact Or.inr rfl
    · exact Or.inl rfl
  sym := fun v u => by
    unfold adjM
    by_cases h : G.Adj v u
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (fun h' => h h'.symm)]
  diag := fun v => by
    unfold adjM
    rw [if_neg G.irrefl]

theorem dg_adjM (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    dg (adjM G) v = (G.degree v : ℤ) := by
  unfold dg adjM
  rw [Finset.sum_boole, ← SimpleGraph.card_neighborFinset_eq_degree,
    SimpleGraph.neighborFinset_eq_filter]

theorem sum_dg_adjM (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∑ v, dg (adjM G) v = 2 * (G.edgeFinset.card : ℤ) := by
  have h1 : ∑ v, dg (adjM G) v = ((∑ v, G.degree v : ℕ) : ℤ) := by
    rw [Nat.cast_sum]
    exact Finset.sum_congr rfl fun v _ => dg_adjM G v
  rw [h1, SimpleGraph.sum_degrees_eq_twice_card_edges]
  push_cast
  rfl

theorem cdf_adjM (G : SimpleGraph V) [DecidableRel G.Adj] (v x : V) :
    cdf (adjM G) v x = ((cn G v x).card : ℤ) := by
  unfold cdf adjM cn
  rw [← Finset.sum_boole]
  refine Finset.sum_congr rfl fun u _ => ?_
  by_cases h1 : G.Adj v u <;> by_cases h2 : G.Adj x u <;> simp [h1, h2]

theorem aux_k (k : ℕ) : max ((k:ℤ) - 1) 0 ≤ ((k * k - k : ℕ) : ℤ) := by
  apply max_le
  · rw [Nat.cast_sub (Nat.le_mul_self k)]
    push_cast
    nlinarith [sq_nonneg ((k:ℤ) - 1)]
  · exact Int.natCast_nonneg _

theorem c4_map_rel (G : SimpleGraph V) {v c x c' : V} (h1 : G.Adj v c) (h2 : G.Adj c x)
    (h3 : G.Adj x c') (h4 : G.Adj c' v) :
    ∀ a b : Fin 4, (a - b = 1 ∨ b - a = 1) → G.Adj (![v, c, x, c'] a) (![v, c, x, c'] b) := by
  intro a b
  fin_cases a <;> fin_cases b <;> intro hab <;>
    first
    | exact absurd hab (by decide)
    | exact h1 | exact h2 | exact h3 | exact h4
    | exact h1.symm | exact h2.symm | exact h3.symm | exact h4.symm

theorem c4_inj {v c x c' : V} (h1 : v ≠ c) (h2 : v ≠ x) (h3 : v ≠ c') (h4 : c ≠ x)
    (h5 : c ≠ c') (h6 : x ≠ c') : Function.Injective ![v, c, x, c'] := by
  intro a b hab
  fin_cases a <;> fin_cases b <;>
    first
    | rfl
    | exact absurd hab h1 | exact absurd hab h2 | exact absurd hab h3
    | exact absurd hab h4 | exact absurd hab h5 | exact absurd hab h6
    | exact absurd hab.symm h1 | exact absurd hab.symm h2 | exact absurd hab.symm h3
    | exact absurd hab.symm h4 | exact absurd hab.symm h5 | exact absurd hab.symm h6

/-- The number of `(v, x, c, c')` with `v ≠ x`, `c ≠ c'` common neighbours of `v, x` is at most
`256` times the number of four-cycles. -/
theorem c4_count (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∑ v, pf (adjM G) v ≤
      256 * (({H' : G.Subgraph | Nonempty (H'.coe ≃g SimpleGraph.cycleGraph 4)}.ncard : ℕ) : ℤ) := by
  classical
  obtain ⟨Q, hQ⟩ : ∃ Q : Finset (Σ _ : V × V, V × V), Q = (Finset.univ : Finset (V × V)).sigma
      (fun p => if p.1 = p.2 then ∅ else (cn G p.1 p.2).offDiag) := ⟨_, rfl⟩
  have h1 : ∑ v, pf (adjM G) v ≤ (Q.card : ℤ) := by
    rw [hQ, Finset.card_sigma]
    push_cast
    rw [Fintype.sum_prod_type]
    refine Finset.sum_le_sum fun v _ => ?_
    unfold pf
    refine Finset.sum_le_sum fun x _ => ?_
    dsimp only
    by_cases hx : x = v
    · subst hx
      simp
    · rw [if_neg hx, if_neg (fun h => hx h.symm), cdf_adjM, Finset.offDiag_card]
      exact aux_k _
  obtain ⟨Cs, hCs⟩ : ∃ Cs : Finset G.Subgraph, Cs = (Set.toFinite
      {H' : G.Subgraph | Nonempty (H'.coe ≃g SimpleGraph.cycleGraph 4)}).toFinset := ⟨_, rfl⟩
  have hN : {H' : G.Subgraph | Nonempty (H'.coe ≃g SimpleGraph.cycleGraph 4)}.ncard = Cs.card := by
    rw [hCs]
    exact Set.ncard_eq_toFinset_card _ _
  obtain ⟨S, hS⟩ : ∃ S : G.Subgraph → Finset V,
      S = fun H' => (Set.toFinite H'.verts).toFinset := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : G.Subgraph → Finset (Σ _ : V × V, V × V),
      B = fun H' => (S H' ×ˢ S H').sigma (fun _ => S H' ×ˢ S H') := ⟨_, rfl⟩
  have hScard : ∀ H' ∈ Cs, (S H').card = 4 := by
    intro H' hH'
    rw [hCs, Set.Finite.mem_toFinset] at hH'
    obtain ⟨e⟩ := hH'
    have h4 : Nat.card H'.verts = 4 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_fin]
    rw [hS]
    show (Set.toFinite H'.verts).toFinset.card = 4
    rw [← Set.ncard_eq_toFinset_card, ← Nat.card_coe_set_eq]
    exact h4
  have hBcard : ∀ H' ∈ Cs, (B H').card ≤ 256 := by
    intro H' hH'
    have h4 := hScard H' hH'
    rw [hB]
    show ((S H' ×ˢ S H').sigma (fun _ => S H' ×ˢ S H')).card ≤ 256
    rw [Finset.card_sigma, Finset.sum_const, Finset.card_product, h4, smul_eq_mul]
  have hsub : Q ⊆ Cs.biUnion B := by
    intro t ht
    obtain ⟨⟨v, x⟩, ⟨c, c'⟩⟩ := t
    rw [hQ, Finset.mem_sigma] at ht
    obtain ⟨-, ht2⟩ := ht
    dsimp only at ht2
    by_cases hvx : v = x
    · rw [if_pos hvx] at ht2
      exact absurd ht2 (Finset.notMem_empty _)
    · rw [if_neg hvx, Finset.mem_offDiag] at ht2
      obtain ⟨hc, hc', hne⟩ := ht2
      dsimp only at hc hc' hne
      unfold cn at hc hc'
      rw [Finset.mem_filter] at hc hc'
      obtain ⟨-, hvc, hxc⟩ := hc
      obtain ⟨-, hvc', hxc'⟩ := hc'
      obtain ⟨f, hf⟩ : ∃ f : SimpleGraph.Copy (SimpleGraph.cycleGraph 4) G,
          ∀ a : Fin 4, f a = ![v, c, x, c'] a :=
        ⟨⟨⟨![v, c, x, c'], fun {a b} hab =>
          c4_map_rel G hvc hxc.symm hxc' hvc'.symm a b (SimpleGraph.cycleGraph_adj.mp hab)⟩,
          c4_inj (G.ne_of_adj hvc) hvx (G.ne_of_adj hvc') (G.ne_of_adj hxc).symm hne
            (G.ne_of_adj hxc')⟩, fun a => rfl⟩
      rw [Finset.mem_biUnion]
      refine ⟨f.toSubgraph, ?_, ?_⟩
      · rw [hCs, Set.Finite.mem_toFinset]
        exact ⟨f.isoToSubgraph.symm⟩
      · have hm : ∀ a : Fin 4, f a ∈ S f.toSubgraph := fun a => by
          rw [hS]
          show f a ∈ (Set.toFinite f.toSubgraph.verts).toFinset
          rw [Set.Finite.mem_toFinset]
          exact ⟨a, trivial, rfl⟩
        have h0 := hm 0
        have h1' := hm 1
        have h2' := hm 2
        have h3' := hm 3
        rw [hf] at h0 h1' h2' h3'
        rw [hB]
        show (⟨(v, x), (c, c')⟩ : Σ _ : V × V, V × V) ∈
          (S f.toSubgraph ×ˢ S f.toSubgraph).sigma (fun _ => S f.toSubgraph ×ˢ S f.toSubgraph)
        rw [Finset.mem_sigma, Finset.mem_product, Finset.mem_product]
        exact ⟨⟨h0, h2'⟩, ⟨h1', h3'⟩⟩
  have h2 : Q.card ≤ Cs.card * 256 := by
    calc Q.card ≤ (Cs.biUnion B).card := Finset.card_le_card hsub
      _ ≤ ∑ H' ∈ Cs, (B H').card := Finset.card_biUnion_le
      _ ≤ Cs.card • 256 := Finset.sum_le_card_nsmul _ _ _ hBcard
      _ = Cs.card * 256 := smul_eq_mul _ _
  rw [hN]
  have h3 : (Q.card : ℤ) ≤ (Cs.card : ℤ) * 256 := by exact_mod_cast h2
  linarith

end graph

section polarity

/-- The polarity graph of the projective plane over `F`: distinct orthogonal points. -/
def polG (F : Type*) [Field F] : SimpleGraph (Projectivization F (Fin 3 → F)) where
  Adj x y := x ≠ y ∧ Projectivization.orthogonal x y
  symm := ⟨fun x y h => ⟨h.1.symm, Projectivization.orthogonal_comm.mp h.2⟩⟩
  loopless := ⟨fun x h => h.1 rfl⟩

theorem polG_adj (F : Type*) [Field F] (x y : Projectivization F (Fin 3 → F)) :
    (polG F).Adj x y ↔ x ≠ y ∧ Projectivization.orthogonal x y := Iff.rfl

theorem polG_free (F : Type*) [Field F] : (SimpleGraph.cycleGraph 4).Free (polG F) := by
  rintro ⟨f⟩
  have hadj : ∀ a b : Fin 4, (a - b = 1 ∨ b - a = 1) → (polG F).Adj (f a) (f b) :=
    fun a b hab => f.toHom.map_rel (SimpleGraph.cycleGraph_adj.mpr hab)
  have h01 := ((polG_adj F _ _).mp (hadj 0 1 (by decide))).2
  have h21 := ((polG_adj F _ _).mp (hadj 2 1 (by decide))).2
  have h03 := ((polG_adj F _ _).mp (hadj 0 3 (by decide))).2
  have h23 := ((polG_adj F _ _).mp (hadj 2 3 (by decide))).2
  rcases Configuration.ofField.eq_or_eq_of_orthogonal h01 h21 h03 h23 with h | h
  · exact absurd (f.injective h) (by decide)
  · exact absurd (f.injective h) (by decide)

/-- In characteristic two, the absolute points of the standard polarity lie on one line. -/
theorem abs_point (F : Type*) [Field F] [CharP F 2] (hj : (![1, 1, 1] : Fin 3 → F) ≠ 0)
    (x : Projectivization F (Fin 3 → F)) (hx : Projectivization.orthogonal x x) :
    Projectivization.orthogonal x (Projectivization.mk F ![1, 1, 1] hj) := by
  induction x using Projectivization.ind with
  | h v hv =>
    rw [Projectivization.orthogonal_mk hv hv] at hx
    rw [Projectivization.orthogonal_mk hv hj]
    have e1 : dotProduct v v = v 0 * v 0 + v 1 * v 1 + v 2 * v 2 := by
      simp [dotProduct, Fin.sum_univ_three]
    have e2 : dotProduct v ![1, 1, 1] = v 0 + v 1 + v 2 := by
      simp [dotProduct, Fin.sum_univ_three]
    rw [e1] at hx
    rw [e2]
    have h3 : (v 0 + v 1 + v 2) * (v 0 + v 1 + v 2) = 0 := by
      rw [CharTwo.add_mul_self, CharTwo.add_mul_self]
      exact hx
    exact mul_self_eq_zero.mp h3

theorem polG_count (F : Type*) [Field F] [Finite F] [CharP F 2] (q : ℕ) (hq : Nat.card F = q) :
    q * (q + 1) ^ 2 ≤
      2 * SimpleGraph.extremalNumber (q ^ 2 + q + 1) (SimpleGraph.cycleGraph 4) := by
  classical
  haveI : Fintype (Projectivization F (Fin 3 → F)) := Fintype.ofFinite _
  have hcard : Fintype.card (Projectivization F (Fin 3 → F)) = q ^ 2 + q + 1 := by
    rw [← Nat.card_eq_fintype_card,
      Projectivization.card_of_finrank F (Fin 3 → F) (Module.finrank_fin_fun F), hq]
    simp [Finset.sum_range_succ]
    ring
  have hord : Configuration.ProjectivePlane.order (Projectivization F (Fin 3 → F))
      (Projectivization F (Fin 3 → F)) = q := by
    have h1 := Configuration.ProjectivePlane.card_points (Projectivization F (Fin 3 → F))
      (Projectivization F (Fin 3 → F))
    rw [hcard] at h1
    obtain ⟨o, ho⟩ : ∃ o, o = Configuration.ProjectivePlane.order
      (Projectivization F (Fin 3 → F)) (Projectivization F (Fin 3 → F)) := ⟨_, rfl⟩
    rw [← ho] at h1 ⊢
    rcases lt_trichotomy o q with h | h | h
    · exfalso
      nlinarith [Nat.mul_le_mul h.le h.le]
    · exact h
    · exfalso
      nlinarith [Nat.mul_le_mul h.le h.le]
  have hline : ∀ x : Projectivization F (Fin 3 → F),
      (Finset.univ.filter fun y : Projectivization F (Fin 3 → F) =>
        Projectivization.orthogonal y x).card = q + 1 := by
    intro x
    have h1 : Nat.card {p : Projectivization F (Fin 3 → F) // Projectivization.orthogonal p x}
        = Configuration.ProjectivePlane.order (Projectivization F (Fin 3 → F))
          (Projectivization F (Fin 3 → F)) + 1 :=
      Configuration.ProjectivePlane.pointCount_eq (Projectivization F (Fin 3 → F)) x
    rw [hord, Nat.card_eq_fintype_card, Fintype.card_subtype] at h1
    exact h1
  have hN : ∀ x : Projectivization F (Fin 3 → F), (polG F).neighborFinset x =
      (Finset.univ.filter fun y : Projectivization F (Fin 3 → F) =>
        Projectivization.orthogonal y x).erase x := by
    intro x
    ext y
    rw [SimpleGraph.mem_neighborFinset, Finset.mem_erase, Finset.mem_filter, polG_adj]
    constructor
    · intro h
      exact ⟨h.1.symm, Finset.mem_univ _, Projectivization.orthogonal_comm.mp h.2⟩
    · intro h
      exact ⟨h.1.symm, Projectivization.orthogonal_comm.mp h.2.2⟩
  have hdeg : ∀ x : Projectivization F (Fin 3 → F),
      (polG F).degree x + (if Projectivization.orthogonal x x then 1 else 0) = q + 1 := by
    intro x
    have h0 := hline x
    rw [← SimpleGraph.card_neighborFinset_eq_degree, hN x]
    by_cases hxx : Projectivization.orthogonal x x
    · have h3 := Finset.card_erase_of_mem (show x ∈ (Finset.univ.filter
        fun y : Projectivization F (Fin 3 → F) => Projectivization.orthogonal y x) from by
          rw [Finset.mem_filter]
          exact ⟨Finset.mem_univ _, hxx⟩)
      rw [if_pos hxx]
      omega
    · have h3 := Finset.erase_eq_of_notMem (show x ∉ (Finset.univ.filter
        fun y : Projectivization F (Fin 3 → F) => Projectivization.orthogonal y x) from by
          rw [Finset.mem_filter]
          exact fun h => hxx h.2)
      rw [if_neg hxx, h3]
      omega
  have hj : (![1, 1, 1] : Fin 3 → F) ≠ 0 := by
    intro h
    have h1 := congrFun h 0
    simp at h1
  have habs : (Finset.univ.filter fun x : Projectivization F (Fin 3 → F) =>
      Projectivization.orthogonal x x).card ≤ q + 1 := by
    rw [← hline (Projectivization.mk F ![1, 1, 1] hj)]
    apply Finset.card_le_card
    intro x hx
    rw [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, abs_point F hj x hx.2⟩
  have hsum : ∑ x : Projectivization F (Fin 3 → F), (polG F).degree x
      + (Finset.univ.filter fun x : Projectivization F (Fin 3 → F) =>
          Projectivization.orthogonal x x).card = (q ^ 2 + q + 1) * (q + 1) := by
    rw [Finset.card_filter, ← Finset.sum_add_distrib, Finset.sum_congr rfl (fun x _ => hdeg x),
      Finset.sum_const, Finset.card_univ, hcard, smul_eq_mul]
  have hedges := SimpleGraph.sum_degrees_eq_twice_card_edges (polG F)
  have hex := SimpleGraph.card_edgeFinset_le_extremalNumber (polG_free F)
  rw [hcard] at hex
  have hring : (q ^ 2 + q + 1) * (q + 1) = q * (q + 1) ^ 2 + (q + 1) := by ring
  rw [hedges, hring] at hsum
  omega

/-- The polarity graph gives `ex(q² + q + 1, C₄) ≥ q (q + 1)² / 2` for `q = 2 ^ k`. -/
theorem polarity_lower (k : ℕ) (hk : k ≠ 0) :
    2 ^ k * (2 ^ k + 1) ^ 2 ≤
      2 * SimpleGraph.extremalNumber ((2 ^ k) ^ 2 + 2 ^ k + 1) (SimpleGraph.cycleGraph 4) :=
  polG_count (GaloisField 2 k) (2 ^ k) (GaloisField.card 2 k hk)

end polarity

section final

theorem main_bound (q : ℕ) (hq : ∃ k, q = 2 ^ k) (G : SimpleGraph (Fin (q ^ 2 + q + 1)))
    [DecidableRel G.Adj]
    (hG : SimpleGraph.extremalNumber (q ^ 2 + q + 1) (SimpleGraph.cycleGraph 4)
      < G.edgeFinset.card) :
    (q : ℤ) + 1 ≤ 4096 *
      (({H' : G.Subgraph | Nonempty (H'.coe ≃g SimpleGraph.cycleGraph 4)}.ncard : ℕ) : ℤ) := by
  obtain ⟨k, rfl⟩ := hq
  have hcont : SimpleGraph.IsContained (SimpleGraph.cycleGraph 4) G :=
    SimpleGraph.IsContained.of_extremalNumber_lt_card_edgeFinset (by
      rw [Fintype.card_fin]
      exact hG)
  obtain ⟨f⟩ := hcont
  have hpos : 0 < {H' : G.Subgraph | Nonempty (H'.coe ≃g SimpleGraph.cycleGraph 4)}.ncard :=
    (Set.ncard_pos (Set.toFinite _)).mpr ⟨f.toSubgraph, ⟨f.isoToSubgraph.symm⟩⟩
  obtain ⟨N, hN⟩ : ∃ N : ℕ,
      N = {H' : G.Subgraph | Nonempty (H'.coe ≃g SimpleGraph.cycleGraph 4)}.ncard := ⟨_, rfl⟩
  rw [← hN] at hpos ⊢
  rcases Nat.lt_or_ge k 5 with hk | hk
  · have h1 : 2 ^ k ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : ((2 ^ k : ℕ) : ℤ) ≤ 16 := by exact_mod_cast h1
    have h3 : (1 : ℤ) ≤ N := by exact_mod_cast hpos
    linarith
  · have h1 : 2 ^ 5 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    have h32 : (32 : ℤ) ≤ ((2 ^ k : ℕ) : ℤ) := by exact_mod_cast h1
    have heven : Even ((2 ^ k : ℕ) : ℤ) := by
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      exact ⟨((2 ^ j : ℕ) : ℤ), by push_cast; ring⟩
    have hc : (Fintype.card (Fin ((2 ^ k) ^ 2 + 2 ^ k + 1)) : ℤ)
        = ((2 ^ k : ℕ) : ℤ) ^ 2 + ((2 ^ k : ℕ) : ℤ) + 1 := by
      rw [Fintype.card_fin]
      push_cast
      ring
    have hpol := polarity_lower k (by omega)
    have hE : ((2 ^ k : ℕ) : ℤ) * (((2 ^ k : ℕ) : ℤ) + 1) ^ 2 + 2 ≤ ∑ v, dg (adjM G) v := by
      rw [sum_dg_adjM]
      have h5 : 2 ^ k * (2 ^ k + 1) ^ 2 + 2 ≤ 2 * G.edgeFinset.card := by omega
      exact_mod_cast h5
    have hs := supersat (adm_adjM G) ((2 ^ k : ℕ) : ℤ) h32 heven hc hE
    have hcount := c4_count G
    rw [← hN] at hcount
    linarith

end final

end HMY

theorem OMA.solution : type_of% @Erdos60.erdos_60.variants.he_ma_yang := by
  refine ⟨1 / 4096, by norm_num, ?_⟩
  intro q hq G _ hG
  have h1 := HMY.main_bound q hq G hG
  have h2 : Real.sqrt ((q : ℝ) ^ 2 + (q : ℝ) + 1) ≤ (q : ℝ) + 1 := by
    have h3 : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
    have h4 : Real.sqrt (((q : ℝ) + 1) ^ 2) = (q : ℝ) + 1 := Real.sqrt_sq (by linarith)
    rw [← h4]
    apply Real.sqrt_le_sqrt
    nlinarith
  have h5 : ((q : ℝ) + 1) ≤ 4096 *
      (({H' : G.Subgraph | Nonempty (H'.coe ≃g SimpleGraph.cycleGraph 4)}.ncard : ℕ) : ℝ) := by
    exact_mod_cast h1
  linarith
