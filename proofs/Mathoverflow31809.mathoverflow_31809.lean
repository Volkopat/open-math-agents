import FormalConjectures.Mathoverflow.«31809»
import Mathlib

-- Problem: Mathoverflow 31809
-- Upstream: formal-conjectures FormalConjectures/Mathoverflow/31809.lean:44 (declaration Mathoverflow31809.mathoverflow_31809)
-- Credit: @ppleskov (the owner of the agent is credited as the solver)
-- Based on X.-W. Chen, J. Liu, X.-S. Lu, and C. Zhang,
-- A pre-triangulated category which is not triangulated, arXiv:2608.09777 (2026).

/-!
# A pretriangulated category that is not triangulated

We construct the 35-dimensional preprojective algebra $\Lambda = \Pi(A_5)$ over $\mathbb{F}_2$,
its Frobenius structure and Nakayama involution $\nu$, its 3-term bimodule resolution with an
explicit right-$\Lambda$-linear contracting homotopy, the 7-dimensional 2-periodic module $M$
and its twisted Heller parameter $\theta_\varepsilon$, and prove that the resulting
pretriangulated category $(\mathcal{P}(\Lambda), (-)_\nu, \Delta_{\theta_\varepsilon})$
fails Verdier's octahedral axiom (TR4).
-/

namespace OMA.MO31809

open CategoryTheory Limits

section Algebra

/-- Basis elements of $\Lambda = \Pi(A_5)$ over $\mathbb{F}_2$:
triples `(i, j, s)` with `0 ≤ i, j < 5` and `j - i ≤ s < min(j + 1, 5 - i)`. -/
def isValidBasis (t : Fin 5 × Fin 5 × Fin 5) : Bool :=
  let i := t.1.val
  let j := t.2.1.val
  let s := t.2.2.val
  (j ≤ i + s) && (s < j + 1) && (s + i < 5)

abbrev B := { t : Fin 5 × Fin 5 × Fin 5 // isValidBasis t = true }

lemma valid_iff (t : Fin 5 × Fin 5 × Fin 5) :
    isValidBasis t = true ↔
      t.2.1.val ≤ t.1.val + t.2.2.val ∧ t.2.2.val < t.2.1.val + 1 ∧ t.2.2.val + t.1.val < 5 := by
  simp [isValidBasis, Bool.and_eq_true, and_assoc]

lemma B_bounds (u : B) :
    u.val.2.1.val ≤ u.val.1.val + u.val.2.2.val ∧
    u.val.2.2.val < u.val.2.1.val + 1 ∧
    u.val.2.2.val + u.val.1.val < 5 :=
  (valid_iff u.val).mp u.property

/-- Basis multiplication `u * v` (composition `u ∘ v`): if `u : i₁ → j₁` and `v : i₂ → j₂`
with `j₂ = i₁`, produces `(i₂, j₁, s₁ + s₂)` when valid. -/
def mulB (u v : B) : Option B :=
  if v.val.2.1 = u.val.1 then
    let s := u.val.2.2.val + v.val.2.2.val
    if hs : s < 5 then
      let t : Fin 5 × Fin 5 × Fin 5 := (v.val.1, u.val.2.1, ⟨s, hs⟩)
      if hv : isValidBasis t = true then some ⟨t, hv⟩ else none
    else none
  else none

/-- Vertex idempotent `e_i = (i, i, 0)`. -/
def idempB (i : Fin 5) : B :=
  ⟨(i, i, ⟨0, by omega⟩), by rw [valid_iff]; dsimp; omega⟩

/-- Nakayama involution `ν(i, j, s) = (4 - i, 4 - j, s + i - j)`. -/
def nuB (u : B) : B :=
  ⟨(⟨4 - u.val.1.val, by omega⟩, ⟨4 - u.val.2.1.val, by omega⟩,
    ⟨u.val.2.2.val + u.val.1.val - u.val.2.1.val, by have := B_bounds u; omega⟩), by
    rw [valid_iff]; dsimp; have := B_bounds u; omega⟩

/-- Dual basis permutation `dualB u` such that `phiOpt (mulB u v) = true ↔ v = dualB u`. -/
def dualB (u : B) : B :=
  ⟨(⟨4 - u.val.2.1.val, by omega⟩, u.val.1,
    ⟨u.val.2.1.val - u.val.2.2.val, by have := B_bounds u; omega⟩), by
    rw [valid_iff]; dsimp; have := B_bounds u; omega⟩

/-- Socle predicate for the Frobenius trace form: `i + j = 4` and `s = j`. -/
def isSocB (u : B) : Bool :=
  (u.val.1.val + u.val.2.1.val == 4) && (u.val.2.2.val == u.val.2.1.val)

def phiOpt : Option B → Bool
  | some u => isSocB u
  | none => false

lemma mulB_eq_some_iff (u v w : B) :
    mulB u v = some w ↔
      v.val.2.1 = u.val.1 ∧ w.val.1 = v.val.1 ∧ w.val.2.1 = u.val.2.1 ∧
      w.val.2.2.val = u.val.2.2.val + v.val.2.2.val := by
  unfold mulB
  constructor
  · intro h
    by_cases h1 : v.val.2.1 = u.val.1
    · rw [if_pos h1] at h
      by_cases hs : u.val.2.2.val + v.val.2.2.val < 5
      · rw [dif_pos hs] at h
        by_cases hv : isValidBasis (v.val.1, u.val.2.1, ⟨u.val.2.2.val + v.val.2.2.val, hs⟩) = true
        · rw [dif_pos hv] at h
          have hw := Option.some.inj h
          refine ⟨h1, ?_, ?_, ?_⟩
          · exact (congrArg (fun z : B => z.val.1) hw).symm
          · exact (congrArg (fun z : B => z.val.2.1) hw).symm
          · exact (congrArg (fun z : B => z.val.2.2.val) hw).symm
        · rw [dif_neg hv] at h; cases h
      · rw [dif_neg hs] at h; cases h
    · rw [if_neg h1] at h; cases h
  · rintro ⟨h1, h2, h3, h4⟩
    have hs : u.val.2.2.val + v.val.2.2.val < 5 := by omega
    have hv : isValidBasis (v.val.1, u.val.2.1, ⟨u.val.2.2.val + v.val.2.2.val, hs⟩) = true := by
      have hw := B_bounds w
      rw [valid_iff]; dsimp
      simp only [h2, h3, h4] at hw
      exact hw
    rw [if_pos h1, dif_pos hs, dif_pos hv]
    congr 1; apply Subtype.ext; ext <;> simp [h2, h3, h4]

lemma mulB_assoc (a b c : B) :
    (mulB a b).bind (fun ab => mulB ab c) = (mulB b c).bind (fun bc => mulB a bc) := by
  have ha := B_bounds a
  have hb := B_bounds b
  have hc := B_bounds c
  rcases h1 : mulB a b with _ | ab <;> rcases h2 : mulB b c with _ | bc
  · rfl
  · simp only [Option.bind_none, Option.bind_some]
    rw [mulB_eq_some_iff] at h2
    rcases h3 : mulB a bc with _ | w
    · rfl
    · rw [mulB_eq_some_iff] at h3
      have hba : b.val.2.1 = a.val.1 := by rw [← h2.2.2.1]; exact h3.1
      have hs : a.val.2.2.val + b.val.2.2.val < 5 := by omega
      have hv : isValidBasis (b.val.1, a.val.2.1, ⟨a.val.2.2.val + b.val.2.2.val, hs⟩) = true := by
        have hw := B_bounds w; rw [valid_iff]; dsimp
        simp only [h3.2.1, h3.2.2.1, h3.2.2.2, h2.2.1, h2.2.2.2] at hw
        omega
      have hab : mulB a b = some ⟨(b.val.1, a.val.2.1, ⟨a.val.2.2.val + b.val.2.2.val, hs⟩), hv⟩ := by
        rw [mulB_eq_some_iff]; exact ⟨hba, rfl, rfl, rfl⟩
      rw [h1] at hab; cases hab
  · simp only [Option.bind_none, Option.bind_some]
    rw [mulB_eq_some_iff] at h1
    rcases h3 : mulB ab c with _ | w
    · rfl
    · rw [mulB_eq_some_iff] at h3
      have hcb : c.val.2.1 = b.val.1 := by rw [← h1.2.1]; exact h3.1
      have hs : b.val.2.2.val + c.val.2.2.val < 5 := by omega
      have hv : isValidBasis (c.val.1, b.val.2.1, ⟨b.val.2.2.val + c.val.2.2.val, hs⟩) = true := by
        have hw := B_bounds w; rw [valid_iff]; dsimp
        simp only [h3.2.1, h3.2.2.1, h3.2.2.2, h1.2.2.1, h1.2.2.2] at hw
        omega
      have hbc : mulB b c = some ⟨(c.val.1, b.val.2.1, ⟨b.val.2.2.val + c.val.2.2.val, hs⟩), hv⟩ := by
        rw [mulB_eq_some_iff]; exact ⟨hcb, rfl, rfl, rfl⟩
      rw [h2] at hbc; cases hbc
  · simp only [Option.bind_some]
    rw [mulB_eq_some_iff] at h1 h2
    rcases h3 : mulB ab c with _ | w1 <;> rcases h4 : mulB a bc with _ | w2
    · rfl
    · rw [mulB_eq_some_iff] at h4
      have hw1 : mulB ab c = some w2 := by
        rw [mulB_eq_some_iff]
        refine ⟨by rw [h1.2.1]; exact h2.1, by rw [h4.2.1, h2.2.1], by rw [h4.2.2.1, h1.2.2.1], ?_⟩
        omega
      rw [h3] at hw1; cases hw1
    · rw [mulB_eq_some_iff] at h3
      have hw2 : mulB a bc = some w1 := by
        rw [mulB_eq_some_iff]
        refine ⟨by rw [h2.2.2.1]; exact h1.1, by rw [h3.2.1, h2.2.1], by rw [h3.2.2.1, h1.2.2.1], ?_⟩
        omega
      rw [h4] at hw2; cases hw2
    · rw [mulB_eq_some_iff] at h3 h4
      congr 1; apply Subtype.ext; ext
      · rw [h3.2.1, h4.2.1, h2.2.1]
      · rw [h3.2.2.1, h4.2.2.1, h1.2.2.1]
      · omega

lemma nuB_invol (u : B) : nuB (nuB u) = u := by
  have := B_bounds u
  apply Subtype.ext; ext <;> simp [nuB] <;> omega

lemma nuB_mulB (u v : B) : (mulB u v).map nuB = mulB (nuB u) (nuB v) := by
  have hu := B_bounds u; have hv := B_bounds v
  rcases h : mulB u v with _ | w
  · simp only [Option.map_none]
    rcases h2 : mulB (nuB u) (nuB v) with _ | w2
    · rfl
    · rw [mulB_eq_some_iff] at h2
      have h1_val : v.val.2.1.val = u.val.1.val := by
        have := congrArg Fin.val h2.1; simp [nuB] at this; omega
      have h1 : v.val.2.1 = u.val.1 := Fin.ext h1_val
      have hw2 := B_bounds w2
      have h2_1 := congrArg Fin.val h2.2.1
      have h2_2 := congrArg Fin.val h2.2.2.1
      have h2_3 := h2.2.2.2
      simp [nuB] at h2_1 h2_2 h2_3
      have h3 : mulB u v = some (nuB w2) := by
        rw [mulB_eq_some_iff]
        refine ⟨h1, ?_, ?_, ?_⟩
        · ext; simp [nuB]; omega
        · ext; simp [nuB]; omega
        · simp [nuB]; omega
      rw [h] at h3; cases h3
  · simp only [Option.map_some]
    rw [mulB_eq_some_iff] at h
    symm; rw [mulB_eq_some_iff]
    refine ⟨?_, ?_, ?_, ?_⟩
    · ext; simp [nuB, h.1]
    · ext; simp [nuB, h.2.1]
    · ext; simp [nuB, h.2.2.1]
    · simp only [nuB, h.1, h.2.1, h.2.2.1, h.2.2.2]; omega

lemma phi_mulB_iff (u v : B) : phiOpt (mulB u v) = true ↔ v = dualB u := by
  have hu := B_bounds u; have hv := B_bounds v
  constructor
  · intro h
    rcases hm : mulB u v with _ | w
    · simp [hm, phiOpt] at h
    · simp only [hm, phiOpt, isSocB, Bool.and_eq_true, beq_iff_eq] at h
      rw [mulB_eq_some_iff] at hm
      apply Subtype.ext; ext
      · simp [dualB]; omega
      · simp [dualB, hm.1]
      · simp [dualB]; omega
  · rintro rfl
    have hw_s : u.val.2.2.val + (u.val.2.1.val - u.val.2.2.val) < 5 := by omega
    have hw_v : isValidBasis (⟨4 - u.val.2.1.val, by omega⟩, u.val.2.1,
        ⟨u.val.2.2.val + (u.val.2.1.val - u.val.2.2.val), hw_s⟩) = true := by
      rw [valid_iff]; dsimp; omega
    have hm : mulB u (dualB u) = some ⟨(⟨4 - u.val.2.1.val, by omega⟩, u.val.2.1,
        ⟨u.val.2.2.val + (u.val.2.1.val - u.val.2.2.val), hw_s⟩), hw_v⟩ := by
      rw [mulB_eq_some_iff]; exact ⟨rfl, rfl, rfl, rfl⟩
    rw [hm]; simp [phiOpt, isSocB]; omega

lemma phi_nakayama (u v : B) : phiOpt (mulB u v) = phiOpt (mulB v (nuB u)) := by
  have hu := B_bounds u; have hv := B_bounds v
  rw [Bool.eq_iff_iff, phi_mulB_iff, phi_mulB_iff]
  constructor <;> intro h
  · subst h; apply Subtype.ext; refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> (apply Fin.ext; simp [dualB, nuB]; try omega)
  · have h1 := congrArg (fun x : B => x.val.1.val) h
    have h2 := congrArg (fun x : B => x.val.2.1.val) h
    have h3 := congrArg (fun x : B => x.val.2.2.val) h
    simp [dualB, nuB] at h1 h2 h3
    apply Subtype.ext; ext <;> (simp [dualB]; omega)

lemma mulB_idemp_left (u : B) : mulB (idempB u.val.2.1) u = some u := by
  rw [mulB_eq_some_iff]; simp [idempB]

lemma mulB_idemp_right (u : B) : mulB u (idempB u.val.1) = some u := by
  rw [mulB_eq_some_iff]; simp [idempB]

lemma mulB_idemp_left_ne (i : Fin 5) (u : B) (h : i ≠ u.val.2.1) : mulB (idempB i) u = none := by
  rcases hm : mulB (idempB i) u with _ | w
  · rfl
  · rw [mulB_eq_some_iff] at hm; exact absurd hm.1.symm h

lemma mulB_idemp_right_ne (i : Fin 5) (u : B) (h : i ≠ u.val.1) : mulB u (idempB i) = none := by
  rcases hm : mulB u (idempB i) with _ | w
  · rfl
  · rw [mulB_eq_some_iff] at hm; exact absurd hm.1 h

/-- The 35-dimensional $\mathbb{F}_2$-algebra $\Lambda = \Pi(A_5)$, wrapped as a structure
so its convolution `Ring` instance does not clash with pointwise `Pi.ring`. -/
structure Λ where
  coeff : B → ZMod 2
  deriving DecidableEq

lemma Λ.ext {a b : Λ} (h : a.coeff = b.coeff) : a = b := by cases a; cases b; congr

instance : Zero Λ := ⟨⟨0⟩⟩
instance : Add Λ := ⟨fun a b => ⟨a.coeff + b.coeff⟩⟩
instance : Neg Λ := ⟨fun a => ⟨-a.coeff⟩⟩
instance : Sub Λ := ⟨fun a b => ⟨a.coeff - b.coeff⟩⟩
instance : SMul (ZMod 2) Λ := ⟨fun c a => ⟨c • a.coeff⟩⟩

@[simp] lemma zero_coeff (w : B) : (0 : Λ).coeff w = 0 := rfl
@[simp] lemma add_coeff (a b : Λ) (w : B) : (a + b).coeff w = a.coeff w + b.coeff w := rfl
@[simp] lemma neg_coeff (a : Λ) (w : B) : (-a).coeff w = -a.coeff w := rfl
@[simp] lemma sub_coeff (a b : Λ) (w : B) : (a - b).coeff w = a.coeff w - b.coeff w := rfl
@[simp] lemma smul_coeff (c : ZMod 2) (a : Λ) (w : B) : (c • a).coeff w = c * a.coeff w := rfl

instance : AddCommGroup Λ where
  add_assoc a b c := by apply Λ.ext; funext w; simp [add_assoc]
  zero_add a := by apply Λ.ext; funext w; simp
  add_zero a := by apply Λ.ext; funext w; simp
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel a := by apply Λ.ext; funext w; exact neg_add_cancel (a.coeff w)
  add_comm a b := by apply Λ.ext; funext w; simp [add_comm]
  sub_eq_add_neg a b := by apply Λ.ext; funext w; simp [sub_eq_add_neg]

@[simp] lemma sum_coeff {ι : Type*} (s : Finset ι) (f : ι → Λ) (w : B) :
    (∑ i ∈ s, f i).coeff w = ∑ i ∈ s, (f i).coeff w := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, add_coeff, ih]

instance : Module (ZMod 2) Λ where
  one_smul a := by apply Λ.ext; funext w; simp
  mul_smul r s a := by apply Λ.ext; funext w; simp [mul_assoc]
  smul_zero r := by apply Λ.ext; funext w; simp
  smul_add r a b := by apply Λ.ext; funext w; simp [mul_add]
  add_smul r s a := by apply Λ.ext; funext w; simp [add_mul]
  zero_smul a := by apply Λ.ext; funext w; simp

def basisVec (u : B) : Λ := ⟨fun x => if x = u then 1 else 0⟩

def mulΛ (a b : Λ) : Λ :=
  ⟨fun w => ∑ u : B, ∑ v : B, if mulB u v = some w then a.coeff u * b.coeff v else 0⟩

def oneΛ : Λ := ⟨fun w => if ∃ i : Fin 5, w = idempB i then 1 else 0⟩

lemma mulΛ_assoc (a b c : Λ) : mulΛ (mulΛ a b) c = mulΛ a (mulΛ b c) := by
  apply Λ.ext; funext w
  simp only [mulΛ]
  trans (∑ u : B, ∑ v : B, ∑ z : B,
      if (mulB u v).bind (fun uv => mulB uv z) = some w then a.coeff u * b.coeff v * c.coeff z else 0)
  · trans (∑ x : B, ∑ z : B, ∑ u : B, ∑ v : B,
        if mulB x z = some w ∧ mulB u v = some x then a.coeff u * b.coeff v * c.coeff z else 0)
    · refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun z _ => ?_
      split_ifs with hxz
      · simp_rw [Finset.sum_mul, ite_mul, zero_mul, hxz, true_and]
      · simp [hxz]
    · rw [Finset.sum_comm]
      trans (∑ z : B, ∑ u : B, ∑ v : B, ∑ x : B,
          if mulB x z = some w ∧ mulB u v = some x then a.coeff u * b.coeff v * c.coeff z else 0)
      · refine Finset.sum_congr rfl fun z _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [Finset.sum_comm]
      · rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun v _ => ?_
        refine Finset.sum_congr rfl fun z _ => ?_
        cases h : mulB u v with
        | none => simp
        | some uv =>
          simp only [Option.bind_some]
          rw [Finset.sum_eq_single uv]
          · simp
          · intro x _ hx; simp [hx.symm]
          · intro hx; exact absurd (Finset.mem_univ uv) hx
  · trans (∑ u : B, ∑ v : B, ∑ z : B,
        if (mulB v z).bind (fun vz => mulB u vz) = some w then a.coeff u * (b.coeff v * c.coeff z) else 0)
    · refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ =>
        Finset.sum_congr rfl fun z _ => ?_
      rw [mulB_assoc, mul_assoc]
    · symm
      refine Finset.sum_congr rfl fun u _ => ?_
      trans (∑ x : B, ∑ v : B, ∑ z : B,
          if mulB u x = some w ∧ mulB v z = some x then a.coeff u * (b.coeff v * c.coeff z) else 0)
      · refine Finset.sum_congr rfl fun x _ => ?_
        split_ifs with hux
        · simp_rw [Finset.mul_sum, mul_ite, mul_zero, hux, true_and]
        · simp [hux]
      · rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun z _ => ?_
        cases h : mulB v z with
        | none => simp
        | some vz =>
          simp only [Option.bind_some]
          rw [Finset.sum_eq_single vz]
          · simp
          · intro x _ hx; simp [hx.symm]
          · intro hx; exact absurd (Finset.mem_univ vz) hx

lemma oneΛ_mulΛ (a : Λ) : mulΛ oneΛ a = a := by
  apply Λ.ext; funext w
  simp only [mulΛ, oneΛ]
  rw [Finset.sum_eq_single (idempB w.val.2.1)]
  · rw [Finset.sum_eq_single w]
    · simp [mulB_idemp_left]
    · intro v _ hvw
      by_cases hv : v.val.2.1 = w.val.2.1
      · rw [← hv, mulB_idemp_left]; simp [hvw]
      · rw [mulB_idemp_left_ne _ _ (Ne.symm hv)]; simp
    · intro h; exact absurd (Finset.mem_univ w) h
  · intro u _ hu
    refine Finset.sum_eq_zero fun v _ => ?_
    by_cases h1 : ∃ i : Fin 5, u = idempB i
    · obtain ⟨i, rfl⟩ := h1
      by_cases hi : i = v.val.2.1
      · subst hi
        rw [mulB_idemp_left]
        have : v ≠ w := fun h => hu (by subst h; rfl)
        simp [this]
      · rw [mulB_idemp_left_ne _ _ hi]; simp
    · simp [h1]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma mulΛ_oneΛ (a : Λ) : mulΛ a oneΛ = a := by
  apply Λ.ext; funext w
  simp only [mulΛ, oneΛ]
  rw [Finset.sum_eq_single w]
  · rw [Finset.sum_eq_single (idempB w.val.1)]
    · simp [mulB_idemp_right]
    · intro v _ hv
      by_cases h1 : ∃ i : Fin 5, v = idempB i
      · obtain ⟨i, rfl⟩ := h1
        have hi : i ≠ w.val.1 := fun h => hv (by subst h; rfl)
        rw [mulB_idemp_right_ne _ _ hi]; simp
      · simp [h1]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro u _ huw
    refine Finset.sum_eq_zero fun v _ => ?_
    by_cases h1 : ∃ i : Fin 5, v = idempB i
    · obtain ⟨i, rfl⟩ := h1
      by_cases hi : i = u.val.1
      · subst hi
        rw [mulB_idemp_right]; simp [huw]
      · rw [mulB_idemp_right_ne _ _ hi]; simp
    · simp [h1]
  · intro h; exact absurd (Finset.mem_univ w) h

instance : Ring Λ where
  mul := mulΛ
  one := oneΛ
  mul_assoc := mulΛ_assoc
  one_mul := oneΛ_mulΛ
  mul_one := mulΛ_oneΛ
  left_distrib a b c := by
    apply Λ.ext; funext w
    change (mulΛ a (b + c)).coeff w = (mulΛ a b).coeff w + (mulΛ a c).coeff w
    simp only [mulΛ, add_coeff, mul_add, ite_add_zero, Finset.sum_add_distrib]
  right_distrib a b c := by
    apply Λ.ext; funext w
    change (mulΛ (a + b) c).coeff w = (mulΛ a c).coeff w + (mulΛ b c).coeff w
    simp only [mulΛ, add_coeff, add_mul, ite_add_zero, Finset.sum_add_distrib]
  zero_mul a := by apply Λ.ext; funext w; change (mulΛ 0 a).coeff w = 0; simp [mulΛ]
  mul_zero a := by apply Λ.ext; funext w; change (mulΛ a 0).coeff w = 0; simp [mulΛ]

@[simp] lemma mul_coeff (a b : Λ) (w : B) :
    (a * b).coeff w = ∑ u : B, ∑ v : B, if mulB u v = some w then a.coeff u * b.coeff v else 0 := rfl

instance : Algebra (ZMod 2) Λ :=
  Algebra.ofModule
    (fun r a b => by apply Λ.ext; funext w; simp [mul_coeff, Finset.mul_sum, mul_ite, mul_assoc])
    (fun r a b => by
      apply Λ.ext; funext w; simp only [mul_coeff, smul_coeff, Finset.mul_sum, mul_ite, mul_zero]
      refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
      split_ifs <;> ring)

lemma basisVec_mul (u v : B) :
    basisVec u * basisVec v = match mulB u v with | some w => basisVec w | none => 0 := by
  apply Λ.ext; funext w
  simp only [mul_coeff, basisVec]
  rw [Finset.sum_eq_single u]
  · rw [Finset.sum_eq_single v]
    · cases mulB u v with
      | none => simp
      | some z => simp [eq_comm]
    · intro x _ hx; simp [hx]
    · intro h; exact absurd (Finset.mem_univ v) h
  · intro x _ hx
    refine Finset.sum_eq_zero fun y _ => ?_; simp [hx]
  · intro h; exact absurd (Finset.mem_univ u) h

lemma eq_sum_basisVec (a : Λ) : a = ∑ u : B, a.coeff u • basisVec u := by
  apply Λ.ext; funext w
  rw [sum_coeff, Finset.sum_eq_single w]
  · simp [basisVec]
  · intro x _ hxw; simp [basisVec, hxw.symm]
  · intro hw; exact absurd (Finset.mem_univ w) hw

/-- The Frobenius trace form `φ : Λ →ₗ[ZMod 2] ZMod 2`. -/
def phiΛ : Λ →ₗ[ZMod 2] ZMod 2 where
  toFun a := ∑ w : B, if isSocB w then a.coeff w else 0
  map_add' a b := by simp [ite_add_zero, Finset.sum_add_distrib]
  map_smul' c a := by simp [Finset.mul_sum, mul_ite]

lemma phiΛ_mul_dual (a : Λ) (u : B) : phiΛ (a * basisVec (dualB u)) = a.coeff u := by
  simp only [phiΛ, LinearMap.coe_mk, AddHom.coe_mk, mul_coeff, basisVec]
  trans (∑ w : B, ∑ x : B, if isSocB w ∧ mulB x (dualB u) = some w then a.coeff x else 0)
  · refine Finset.sum_congr rfl fun w _ => ?_
    split_ifs with hs
    · refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.sum_eq_single (dualB u)]
      · simp [hs]
      · intro y _ hy; simp [hy]
      · intro h; exact absurd (Finset.mem_univ _) h
    · simp [hs]
  · rw [Finset.sum_comm, Finset.sum_eq_single u]
    · have h1 : phiOpt (mulB u (dualB u)) = true := (phi_mulB_iff u (dualB u)).mpr rfl
      rcases hm : mulB u (dualB u) with _ | w0
      · simp [hm, phiOpt] at h1
      · simp only [hm, phiOpt] at h1
        rw [Finset.sum_eq_single w0]
        · simp [h1]
        · intro w _ hww0; simp [Ne.symm hww0]
        · intro h; exact absurd (Finset.mem_univ w0) h
    · intro x _ hxu
      refine Finset.sum_eq_zero fun w _ => ?_
      split_ifs with h
      · exfalso
        have hp : phiOpt (mulB x (dualB u)) = true := by rw [h.2]; exact h.1
        have heq := (phi_mulB_iff x (dualB u)).mp hp
        have hd : Function.Injective dualB := by
          intro p q hpq
          have bp := B_bounds p; have bq := B_bounds q
          have e1 := congrArg (fun z : B => z.val.1.val) hpq
          have e2 := congrArg (fun z : B => z.val.2.1.val) hpq
          have e3 := congrArg (fun z : B => z.val.2.2.val) hpq
          simp [dualB] at e1 e2 e3
          apply Subtype.ext; ext <;> omega
        exact hxu (hd heq.symm)
      · rfl
    · intro h; exact absurd (Finset.mem_univ u) h

/-- The Nakayama ring involution `ν : Λ ≃+* Λ`. -/
def nuΛ : Λ ≃+* Λ where
  toFun a := ⟨fun w => a.coeff (nuB w)⟩
  invFun a := ⟨fun w => a.coeff (nuB w)⟩
  left_inv a := by apply Λ.ext; funext w; simp [nuB_invol]
  right_inv a := by apply Λ.ext; funext w; simp [nuB_invol]
  map_add' a b := by apply Λ.ext; funext w; rfl
  map_mul' a b := by
    apply Λ.ext; funext w
    simp only [mul_coeff]
    refine Equiv.sum_comp (Equiv.mk nuB nuB nuB_invol nuB_invol) _ |>.symm.trans ?_
    refine Finset.sum_congr rfl fun u _ => ?_
    refine Equiv.sum_comp (Equiv.mk nuB nuB nuB_invol nuB_invol) _ |>.symm.trans ?_
    refine Finset.sum_congr rfl fun v _ => ?_
    simp only [Equiv.coe_fn_mk]
    have hiff : mulB (nuB u) (nuB v) = some (nuB w) ↔ mulB u v = some w := by
      rw [← nuB_mulB]
      cases mulB u v with
      | none => simp
      | some z =>
        simp only [Option.map_some, Option.some.injEq]
        exact ⟨fun h => by simpa [nuB_invol] using congrArg nuB h, fun h => by rw [h]⟩
    simp [hiff]

lemma nuΛ_basisVec (u : B) : nuΛ (basisVec u) = basisVec (nuB u) := by
  apply Λ.ext; funext w; simp only [nuΛ, RingEquiv.coe_mk, Equiv.coe_fn_mk, basisVec]
  exact if_congr ⟨fun h => by simpa [nuB_invol] using congrArg nuB h, fun h => by rw [h, nuB_invol]⟩ rfl rfl

lemma phiΛ_comm (a b : Λ) : phiΛ (a * b) = phiΛ (b * nuΛ a) := by
  have hL : ∀ p q : Λ, phiΛ (p * q) =
      ∑ u : B, ∑ v : B, if phiOpt (mulB u v) then p.coeff u * q.coeff v else 0 := by
    intro p q
    simp only [phiΛ, LinearMap.coe_mk, AddHom.coe_mk, mul_coeff]
    trans (∑ w : B, ∑ u : B, ∑ v : B, if isSocB w ∧ mulB u v = some w then p.coeff u * q.coeff v else 0)
    · refine Finset.sum_congr rfl fun w _ => ?_
      split_ifs with hs <;> simp [hs]
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun v _ => ?_
      rcases hm : mulB u v with _ | w0
      · simp [phiOpt]
      · rw [Finset.sum_eq_single w0]
        · simp [phiOpt]; rfl
        · intro w _ hww0; simp [Ne.symm hww0]
        · intro h; exact absurd (Finset.mem_univ w0) h
  rw [hL a b, hL b (nuΛ a), Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  refine Equiv.sum_comp (Equiv.mk nuB nuB nuB_invol nuB_invol) _ |>.symm.trans ?_
  refine Finset.sum_congr rfl fun u _ => ?_
  simp only [Equiv.coe_fn_mk, nuΛ, RingEquiv.coe_mk]
  rw [phi_nakayama (nuB u) v, nuB_invol, mul_comm]

lemma smul_mulΛ (c : ZMod 2) (a b : Λ) : (c • a) * b = c • (a * b) := by
  apply Λ.ext; funext w; simp [mul_coeff, Finset.mul_sum, mul_ite]

/-- Self-injectivity of $\Lambda$: every $\Lambda$-linear map $X \to \Lambda$ extends along any
$\Lambda$-linear injection $X \hookrightarrow Y$. -/
lemma self_injective {X Y : Type*} [AddCommGroup X] [Module Λ X] [AddCommGroup Y] [Module Λ Y]
    [Module (ZMod 2) X] [IsScalarTower (ZMod 2) Λ X]
    [Module (ZMod 2) Y] [IsScalarTower (ZMod 2) Λ Y]
    (i : X →ₗ[Λ] Y) (hi : Function.Injective i) (f : X →ₗ[Λ] Λ) :
    ∃ g : Y →ₗ[Λ] Λ, g.comp i = f := by
  classical
  let i2 : X →ₗ[ZMod 2] Y := i.restrictScalars (ZMod 2)
  obtain ⟨r, hr⟩ := i2.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hi)
  let lam : Y →ₗ[ZMod 2] ZMod 2 := (phiΛ.comp (f.restrictScalars (ZMod 2))).comp r
  let gFun : Y → Λ := fun y => ⟨fun u => lam (basisVec (nuB (dualB u)) • y)⟩
  have hbg : ∀ (b : Λ) (y : Y), phiΛ (b * gFun y) = lam (b • y) := by
    intro b y
    have hb := eq_sum_basisVec b
    conv_lhs => rw [hb]
    conv_rhs => rw [hb]
    rw [Finset.sum_mul, map_sum]
    have hsm : (∑ u : B, b.coeff u • basisVec u) • y = ∑ u : B, (b.coeff u • basisVec u) • y :=
      Finset.sum_smul ..
    rw [hsm, map_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [smul_mulΛ, smul_assoc, map_smul, map_smul]
    refine congrArg (b.coeff v • ·) ?_
    rw [phiΛ_comm, nuΛ_basisVec]
    have hex : ∃ u0 : B, dualB u0 = nuB v := by
      have bv := B_bounds v
      refine ⟨⟨(⟨4 - v.val.2.1.val, by omega⟩, v.val.1,
        ⟨v.val.2.1.val - v.val.2.2.val, by omega⟩), by rw [valid_iff]; dsimp; omega⟩, ?_⟩
      apply Subtype.ext; refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> (apply Fin.ext; simp [dualB, nuB]; try omega)
    obtain ⟨u0, hu0⟩ := hex
    rw [← hu0, phiΛ_mul_dual]
    show lam (basisVec (nuB (dualB u0)) • y) = lam (basisVec v • y)
    rw [hu0, nuB_invol]
  have hmul : ∀ (a : Λ) (y : Y), gFun (a • y) = a * gFun y := by
    intro a y
    apply Λ.ext; funext u
    have hstep : (a * gFun y).coeff u = phiΛ (basisVec (nuB (dualB u)) * (a * gFun y)) := by
      rw [← phiΛ_mul_dual (a * gFun y) u, phiΛ_comm (basisVec (nuB (dualB u))) (a * gFun y),
        nuΛ_basisVec, nuB_invol]
    rw [hstep, ← mul_assoc, hbg (basisVec (nuB (dualB u)) * a) y, mul_smul]
  refine ⟨{ toFun := gFun,
            map_add' := fun y1 y2 => by
              apply Λ.ext; funext u
              change lam (basisVec (nuB (dualB u)) • (y1 + y2)) =
                lam (basisVec (nuB (dualB u)) • y1) + lam (basisVec (nuB (dualB u)) • y2)
              rw [smul_add, map_add],
            map_smul' := hmul }, ?_⟩
  apply LinearMap.ext; intro x; apply Λ.ext; funext u
  simp only [LinearMap.comp_apply, LinearMap.coe_mk, AddHom.coe_mk, gFun, lam]
  have hri : ∀ z : X, r (i z) = z := fun z => by simpa [i2] using LinearMap.congr_fun hr z
  have h1 : r (basisVec (nuB (dualB u)) • i x) = basisVec (nuB (dualB u)) • x := by
    rw [← map_smul i, hri]
  rw [h1]
  change phiΛ (f (basisVec (nuB (dualB u)) • x)) = (f x).coeff u
  rw [map_smul f, smul_eq_mul, phiΛ_comm, nuΛ_basisVec, nuB_invol, phiΛ_mul_dual]

def idempΛ (i : Fin 5) : Λ := basisVec (idempB i)

lemma basisVec_mul_basisVec (u v : B) :
    basisVec u * basisVec v = match mulB u v with | some w => basisVec w | none => 0 := by
  apply Λ.ext; funext w
  simp only [mul_coeff, basisVec]
  rw [Finset.sum_eq_single u]
  · rw [Finset.sum_eq_single v]
    · cases hm : mulB u v with
      | none => simp
      | some z =>
        simp only [if_true, mul_one]
        by_cases hzw : z = w
        · subst hzw; simp
        · simp [hzw, Ne.symm hzw]
    · intro v' _ hv'; simp [hv']
    · intro h; exact absurd (Finset.mem_univ v) h
  · intro u' _ hu'; exact Finset.sum_eq_zero fun v' _ => by simp [hu']
  · intro h; exact absurd (Finset.mem_univ u) h

lemma sum_idempΛ : (∑ i : Fin 5, idempΛ i) = 1 := by
  apply Λ.ext; funext w
  rw [sum_coeff]
  change (∑ i : Fin 5, (basisVec (idempB i)).coeff w) = oneΛ.coeff w
  simp only [basisVec, oneΛ]
  by_cases h : ∃ i : Fin 5, w = idempB i
  · obtain ⟨i0, hi0⟩ := h
    rw [if_pos ⟨i0, hi0⟩, Finset.sum_eq_single i0]
    · simp [hi0]
    · intro i _ hi
      have hne : w ≠ idempB i := by
        rw [hi0]; intro heq
        exact hi (congrArg (fun z : B => z.val.1) heq).symm
      simp [hne]
    · intro hm; exact absurd (Finset.mem_univ i0) hm
  · rw [if_neg h]
    exact Finset.sum_eq_zero fun i _ => if_neg (fun hw => h ⟨i, hw⟩)

instance : Fintype Λ :=
  Fintype.ofEquiv (B → ZMod 2)
    { toFun := fun f => ⟨f⟩
      invFun := fun a => a.coeff
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

lemma add_self_zmod2 {N : Type*} [AddCommGroup N] [Module (ZMod 2) N] (x : N) : x + x = 0 := by
  have h : ((1 : ZMod 2) + (1 : ZMod 2)) • x = 0 := by
    have h2 : (1 : ZMod 2) + (1 : ZMod 2) = 0 := by decide
    rw [h2, zero_smul]
  simpa [add_smul, one_smul] using h

lemma neg_eq_self_zmod2 {N : Type*} [AddCommGroup N] [Module (ZMod 2) N] (x : N) : -x = x := by
  have h := add_self_zmod2 x
  exact neg_eq_of_add_eq_zero_right h

end Algebra

section BimoduleResolution

def mkB (i j s : Fin 5) (h : isValidBasis (i, j, s) = true) : B := ⟨(i, j, s), h⟩

def arrowSrc (k : Fin 8) : Fin 5 :=
  if h : k.val < 4 then ⟨k.val + 1, by omega⟩ else ⟨k.val - 4, by omega⟩

def arrowTgt (k : Fin 8) : Fin 5 :=
  if h : k.val < 4 then ⟨k.val, by omega⟩ else ⟨k.val - 3, by omega⟩

def arrowB (k : Fin 8) : B :=
  if h : k.val < 4 then
    ⟨(⟨k.val + 1, by omega⟩, ⟨k.val, by omega⟩, ⟨0, by omega⟩), by
      rw [valid_iff]; dsimp; omega⟩
  else
    ⟨(⟨k.val - 4, by omega⟩, ⟨k.val - 3, by omega⟩, ⟨1, by omega⟩), by
      rw [valid_iff]; dsimp; omega⟩

abbrev B1 := { p : Fin 8 × B // p.2.val.1 = arrowTgt p.1 }

def mkB1 (k : Fin 8) (u : B) (h : u.val.1 = arrowTgt k) : B1 := ⟨(k, u), h⟩

def relPairs (l : Fin 5) : List (Fin 8 × Fin 8) :=
  match l.val with
  | 0 => [(0, 4)]
  | 1 => [(4, 0), (1, 5)]
  | 2 => [(5, 1), (2, 6)]
  | 3 => [(6, 2), (3, 7)]
  | 4 => [(7, 3)]
  | _ => []

def μList (u : B) : List (Unit × B) := [((), u)]

def d1List (p : B1) : List (B × B) :=
  (match mulB p.val.2 (arrowB p.val.1) with
   | some w => [(w, idempB (arrowSrc p.val.1))]
   | none => []) ++ [(p.val.2, arrowB p.val.1)]

def d2List (u : B) : List (B1 × B) :=
  (relPairs u.val.1).flatMap fun (k1, k2) =>
    let t1 : List (B1 × B) :=
      match mulB u (arrowB k1) with
      | some w =>
        if h : w.val.1 = arrowTgt k2 then [(⟨(k2, w), h⟩, idempB u.val.1)] else []
      | none => []
    let t2 : List (B1 × B) :=
      if h : u.val.1 = arrowTgt k1 then [(⟨(k1, u), h⟩, arrowB k2)] else []
    t1 ++ t2

def s0List (_ : Unit) : List (B × B) :=
  [0, 1, 2, 3, 4].map fun i : Fin 5 => (idempB i, idempB i)

def s1List (u : B) : List (B1 × B) :=
  match u.val.1.val, u.val.2.1.val, u.val.2.2.val with
  | 0, 1, 1 => [(mkB1 4 (mkB 1 1 0 rfl) rfl, mkB 0 0 0 rfl)]
  | 0, 2, 2 => [(mkB1 4 (mkB 1 2 1 rfl) rfl, mkB 0 0 0 rfl), (mkB1 5 (mkB 2 2 0 rfl) rfl, mkB 0 1 1 rfl)]
  | 0, 3, 3 => [(mkB1 4 (mkB 1 3 2 rfl) rfl, mkB 0 0 0 rfl), (mkB1 5 (mkB 2 3 1 rfl) rfl, mkB 0 1 1 rfl), (mkB1 6 (mkB 3 3 0 rfl) rfl, mkB 0 2 2 rfl)]
  | 0, 4, 4 => [(mkB1 4 (mkB 1 4 3 rfl) rfl, mkB 0 0 0 rfl), (mkB1 5 (mkB 2 4 2 rfl) rfl, mkB 0 1 1 rfl), (mkB1 6 (mkB 3 4 1 rfl) rfl, mkB 0 2 2 rfl), (mkB1 7 (mkB 4 4 0 rfl) rfl, mkB 0 3 3 rfl)]
  | 1, 0, 0 => [(mkB1 0 (mkB 0 0 0 rfl) rfl, mkB 1 1 0 rfl)]
  | 1, 1, 1 => [(mkB1 0 (mkB 0 1 1 rfl) rfl, mkB 1 1 0 rfl), (mkB1 4 (mkB 1 1 0 rfl) rfl, mkB 1 0 0 rfl)]
  | 1, 2, 1 => [(mkB1 5 (mkB 2 2 0 rfl) rfl, mkB 1 1 0 rfl)]
  | 1, 2, 2 => [(mkB1 0 (mkB 0 2 2 rfl) rfl, mkB 1 1 0 rfl), (mkB1 4 (mkB 1 2 1 rfl) rfl, mkB 1 0 0 rfl), (mkB1 5 (mkB 2 2 0 rfl) rfl, mkB 1 1 1 rfl)]
  | 1, 3, 2 => [(mkB1 5 (mkB 2 3 1 rfl) rfl, mkB 1 1 0 rfl), (mkB1 6 (mkB 3 3 0 rfl) rfl, mkB 1 2 1 rfl)]
  | 1, 3, 3 => [(mkB1 0 (mkB 0 3 3 rfl) rfl, mkB 1 1 0 rfl), (mkB1 4 (mkB 1 3 2 rfl) rfl, mkB 1 0 0 rfl), (mkB1 5 (mkB 2 3 1 rfl) rfl, mkB 1 1 1 rfl), (mkB1 6 (mkB 3 3 0 rfl) rfl, mkB 1 2 2 rfl)]
  | 1, 4, 3 => [(mkB1 5 (mkB 2 4 2 rfl) rfl, mkB 1 1 0 rfl), (mkB1 6 (mkB 3 4 1 rfl) rfl, mkB 1 2 1 rfl), (mkB1 7 (mkB 4 4 0 rfl) rfl, mkB 1 3 2 rfl)]
  | 2, 0, 0 => [(mkB1 0 (mkB 0 0 0 rfl) rfl, mkB 2 1 0 rfl), (mkB1 1 (mkB 1 0 0 rfl) rfl, mkB 2 2 0 rfl)]
  | 2, 1, 0 => [(mkB1 1 (mkB 1 1 0 rfl) rfl, mkB 2 2 0 rfl)]
  | 2, 1, 1 => [(mkB1 0 (mkB 0 1 1 rfl) rfl, mkB 2 1 0 rfl), (mkB1 1 (mkB 1 1 1 rfl) rfl, mkB 2 2 0 rfl), (mkB1 4 (mkB 1 1 0 rfl) rfl, mkB 2 0 0 rfl)]
  | 2, 2, 1 => [(mkB1 1 (mkB 1 2 1 rfl) rfl, mkB 2 2 0 rfl), (mkB1 5 (mkB 2 2 0 rfl) rfl, mkB 2 1 0 rfl)]
  | 2, 2, 2 => [(mkB1 0 (mkB 0 2 2 rfl) rfl, mkB 2 1 0 rfl), (mkB1 1 (mkB 1 2 2 rfl) rfl, mkB 2 2 0 rfl), (mkB1 4 (mkB 1 2 1 rfl) rfl, mkB 2 0 0 rfl), (mkB1 5 (mkB 2 2 0 rfl) rfl, mkB 2 1 1 rfl)]
  | 2, 3, 1 => [(mkB1 6 (mkB 3 3 0 rfl) rfl, mkB 2 2 0 rfl)]
  | 2, 3, 2 => [(mkB1 1 (mkB 1 3 2 rfl) rfl, mkB 2 2 0 rfl), (mkB1 5 (mkB 2 3 1 rfl) rfl, mkB 2 1 0 rfl), (mkB1 6 (mkB 3 3 0 rfl) rfl, mkB 2 2 1 rfl)]
  | 2, 4, 2 => [(mkB1 6 (mkB 3 4 1 rfl) rfl, mkB 2 2 0 rfl), (mkB1 7 (mkB 4 4 0 rfl) rfl, mkB 2 3 1 rfl)]
  | 3, 0, 0 => [(mkB1 0 (mkB 0 0 0 rfl) rfl, mkB 3 1 0 rfl), (mkB1 1 (mkB 1 0 0 rfl) rfl, mkB 3 2 0 rfl), (mkB1 2 (mkB 2 0 0 rfl) rfl, mkB 3 3 0 rfl)]
  | 3, 1, 0 => [(mkB1 1 (mkB 1 1 0 rfl) rfl, mkB 3 2 0 rfl), (mkB1 2 (mkB 2 1 0 rfl) rfl, mkB 3 3 0 rfl)]
  | 3, 1, 1 => [(mkB1 0 (mkB 0 1 1 rfl) rfl, mkB 3 1 0 rfl), (mkB1 1 (mkB 1 1 1 rfl) rfl, mkB 3 2 0 rfl), (mkB1 2 (mkB 2 1 1 rfl) rfl, mkB 3 3 0 rfl), (mkB1 4 (mkB 1 1 0 rfl) rfl, mkB 3 0 0 rfl)]
  | 3, 2, 0 => [(mkB1 2 (mkB 2 2 0 rfl) rfl, mkB 3 3 0 rfl)]
  | 3, 2, 1 => [(mkB1 1 (mkB 1 2 1 rfl) rfl, mkB 3 2 0 rfl), (mkB1 2 (mkB 2 2 1 rfl) rfl, mkB 3 3 0 rfl), (mkB1 5 (mkB 2 2 0 rfl) rfl, mkB 3 1 0 rfl)]
  | 3, 3, 1 => [(mkB1 2 (mkB 2 3 1 rfl) rfl, mkB 3 3 0 rfl), (mkB1 6 (mkB 3 3 0 rfl) rfl, mkB 3 2 0 rfl)]
  | 3, 4, 1 => [(mkB1 7 (mkB 4 4 0 rfl) rfl, mkB 3 3 0 rfl)]
  | 4, 0, 0 => [(mkB1 0 (mkB 0 0 0 rfl) rfl, mkB 4 1 0 rfl), (mkB1 1 (mkB 1 0 0 rfl) rfl, mkB 4 2 0 rfl), (mkB1 2 (mkB 2 0 0 rfl) rfl, mkB 4 3 0 rfl), (mkB1 3 (mkB 3 0 0 rfl) rfl, mkB 4 4 0 rfl)]
  | 4, 1, 0 => [(mkB1 1 (mkB 1 1 0 rfl) rfl, mkB 4 2 0 rfl), (mkB1 2 (mkB 2 1 0 rfl) rfl, mkB 4 3 0 rfl), (mkB1 3 (mkB 3 1 0 rfl) rfl, mkB 4 4 0 rfl)]
  | 4, 2, 0 => [(mkB1 2 (mkB 2 2 0 rfl) rfl, mkB 4 3 0 rfl), (mkB1 3 (mkB 3 2 0 rfl) rfl, mkB 4 4 0 rfl)]
  | 4, 3, 0 => [(mkB1 3 (mkB 3 3 0 rfl) rfl, mkB 4 4 0 rfl)]
  | _, _, _ => []

def s2List (p : B1) : List (B × B) :=
  match p.val.1.val, p.val.2.val.1.val, p.val.2.val.2.1.val, p.val.2.val.2.2.val with
  | 0, 0, 4, 4 => [(mkB 1 4 3 rfl, mkB 1 1 0 rfl), (mkB 2 4 2 rfl, mkB 1 2 1 rfl), (mkB 3 4 1 rfl, mkB 1 3 2 rfl), (mkB 4 4 0 rfl, mkB 1 4 3 rfl)]
  | 1, 1, 3, 3 => [(mkB 1 3 2 rfl, mkB 2 1 0 rfl), (mkB 2 3 1 rfl, mkB 2 2 1 rfl), (mkB 2 3 2 rfl, mkB 2 2 0 rfl), (mkB 3 3 0 rfl, mkB 2 3 2 rfl), (mkB 3 3 1 rfl, mkB 2 3 1 rfl), (mkB 4 3 0 rfl, mkB 2 4 2 rfl)]
  | 1, 1, 4, 3 => [(mkB 2 4 2 rfl, mkB 2 2 0 rfl), (mkB 3 4 1 rfl, mkB 2 3 1 rfl), (mkB 4 4 0 rfl, mkB 2 4 2 rfl)]
  | 2, 2, 2, 2 => [(mkB 1 2 1 rfl, mkB 3 1 0 rfl), (mkB 2 2 0 rfl, mkB 3 2 1 rfl), (mkB 2 2 1 rfl, mkB 3 2 0 rfl), (mkB 3 2 0 rfl, mkB 3 3 1 rfl), (mkB 3 2 1 rfl, mkB 3 3 0 rfl), (mkB 4 2 0 rfl, mkB 3 4 1 rfl)]
  | 2, 2, 3, 2 => [(mkB 2 3 1 rfl, mkB 3 2 0 rfl), (mkB 3 3 0 rfl, mkB 3 3 1 rfl), (mkB 3 3 1 rfl, mkB 3 3 0 rfl), (mkB 4 3 0 rfl, mkB 3 4 1 rfl)]
  | 2, 2, 4, 2 => [(mkB 3 4 1 rfl, mkB 3 3 0 rfl), (mkB 4 4 0 rfl, mkB 3 4 1 rfl)]
  | 3, 3, 1, 1 => [(mkB 1 1 0 rfl, mkB 4 1 0 rfl), (mkB 2 1 0 rfl, mkB 4 2 0 rfl), (mkB 3 1 0 rfl, mkB 4 3 0 rfl), (mkB 4 1 0 rfl, mkB 4 4 0 rfl)]
  | 3, 3, 2, 1 => [(mkB 2 2 0 rfl, mkB 4 2 0 rfl), (mkB 3 2 0 rfl, mkB 4 3 0 rfl), (mkB 4 2 0 rfl, mkB 4 4 0 rfl)]
  | 3, 3, 3, 1 => [(mkB 3 3 0 rfl, mkB 4 3 0 rfl), (mkB 4 3 0 rfl, mkB 4 4 0 rfl)]
  | 3, 3, 4, 1 => [(mkB 4 4 0 rfl, mkB 4 4 0 rfl)]
  | 4, 1, 0, 0 => [(mkB 0 0 0 rfl, mkB 0 0 0 rfl)]
  | 4, 1, 1, 1 => [(mkB 0 1 1 rfl, mkB 0 0 0 rfl)]
  | 4, 1, 2, 2 => [(mkB 0 2 2 rfl, mkB 0 0 0 rfl)]
  | 4, 1, 3, 3 => [(mkB 0 3 3 rfl, mkB 0 0 0 rfl)]
  | 5, 2, 0, 0 => [(mkB 0 0 0 rfl, mkB 1 0 0 rfl), (mkB 1 0 0 rfl, mkB 1 1 0 rfl)]
  | 5, 2, 1, 0 => [(mkB 1 1 0 rfl, mkB 1 1 0 rfl)]
  | 5, 2, 1, 1 => [(mkB 0 1 1 rfl, mkB 1 0 0 rfl), (mkB 1 1 1 rfl, mkB 1 1 0 rfl)]
  | 5, 2, 2, 1 => [(mkB 1 2 1 rfl, mkB 1 1 0 rfl)]
  | 5, 2, 2, 2 => [(mkB 0 2 2 rfl, mkB 1 0 0 rfl), (mkB 1 2 2 rfl, mkB 1 1 0 rfl)]
  | 5, 2, 3, 2 => [(mkB 1 3 2 rfl, mkB 1 1 0 rfl)]
  | 6, 3, 0, 0 => [(mkB 0 0 0 rfl, mkB 2 0 0 rfl), (mkB 1 0 0 rfl, mkB 2 1 0 rfl), (mkB 2 0 0 rfl, mkB 2 2 0 rfl)]
  | 6, 3, 1, 0 => [(mkB 1 1 0 rfl, mkB 2 1 0 rfl), (mkB 2 1 0 rfl, mkB 2 2 0 rfl)]
  | 6, 3, 1, 1 => [(mkB 0 1 1 rfl, mkB 2 0 0 rfl), (mkB 1 1 1 rfl, mkB 2 1 0 rfl), (mkB 2 1 1 rfl, mkB 2 2 0 rfl)]
  | 6, 3, 2, 0 => [(mkB 2 2 0 rfl, mkB 2 2 0 rfl)]
  | 6, 3, 2, 1 => [(mkB 1 2 1 rfl, mkB 2 1 0 rfl), (mkB 2 2 1 rfl, mkB 2 2 0 rfl)]
  | 6, 3, 3, 1 => [(mkB 2 3 1 rfl, mkB 2 2 0 rfl)]
  | 7, 4, 0, 0 => [(mkB 0 0 0 rfl, mkB 3 0 0 rfl), (mkB 1 0 0 rfl, mkB 3 1 0 rfl), (mkB 2 0 0 rfl, mkB 3 2 0 rfl), (mkB 3 0 0 rfl, mkB 3 3 0 rfl)]
  | 7, 4, 1, 0 => [(mkB 1 1 0 rfl, mkB 3 1 0 rfl), (mkB 2 1 0 rfl, mkB 3 2 0 rfl), (mkB 3 1 0 rfl, mkB 3 3 0 rfl)]
  | 7, 4, 2, 0 => [(mkB 2 2 0 rfl, mkB 3 2 0 rfl), (mkB 3 2 0 rfl, mkB 3 3 0 rfl)]
  | 7, 4, 3, 0 => [(mkB 3 3 0 rfl, mkB 3 3 0 rfl)]
  | _, _, _, _ => []

def s3List (u : B) : List (Unit × B) :=
  if isSocB u then [((), idempB u.val.1)] else []

def listParity {β : Type*} [DecidableEq β] (L : List (β × B)) (y : β) (v : B) : Bool :=
  L.foldr (fun p acc => if p.1 = y ∧ p.2 = v then !acc else acc) false

def listsSameParity {β : Type*} [DecidableEq β] (L1 L2 : List (β × B)) : Bool :=
  (L1 ++ L2).all fun p => listParity L1 p.1 p.2 == listParity L2 p.1 p.2

lemma listParity_of_not_mem {β : Type*} [DecidableEq β] {L : List (β × B)} {y : β} {v : B}
    (h : (y, v) ∉ L) : listParity L y v = false := by
  induction L with
  | nil => rfl
  | cons a tl ih =>
    simp only [List.mem_cons, not_or] at h
    have hne : ¬ (a.1 = y ∧ a.2 = v) := fun ⟨h1, h2⟩ => h.1 (Prod.ext h1.symm h2.symm)
    simp only [listParity, List.foldr_cons, if_neg hne]
    exact ih h.2

lemma listsSameParity_iff {β : Type*} [DecidableEq β] (L1 L2 : List (β × B)) :
    listsSameParity L1 L2 = true → ∀ y v, listParity L1 y v = listParity L2 y v := by
  intro h y v
  by_cases hm : (y, v) ∈ L1 ++ L2
  · have h1 := List.all_eq_true.mp h (y, v) hm
    exact beq_iff_eq.mp h1
  · simp only [List.mem_append, not_or] at hm
    rw [listParity_of_not_mem hm.1, listParity_of_not_mem hm.2]

def compKernel {α β γ : Type*} (K2 : β → List (γ × B)) (K1 : α → List (β × B)) (x : α) :
    List (γ × B) :=
  (K1 x).flatMap fun p1 =>
    (K2 p1.1).filterMap fun p2 =>
      (mulB p2.2 p1.2).map fun w => (p2.1, w)

def allBList : List B :=
  (List.finRange 5).flatMap fun i =>
    (List.finRange 5).flatMap fun j =>
      (List.finRange 5).filterMap fun s =>
        if h : isValidBasis (i, j, s) = true then some ⟨(i, j, s), h⟩ else none

def allB1List : List B1 :=
  (List.finRange 8).flatMap fun k =>
    allBList.filterMap fun u =>
      if h : u.val.1 = arrowTgt k then some ⟨(k, u), h⟩ else none

lemma mem_allBList (u : B) : u ∈ allBList := by
  unfold allBList
  simp only [List.mem_flatMap, List.mem_filterMap, List.mem_finRange, true_and]
  refine ⟨u.val.1, u.val.2.1, u.val.2.2, ?_⟩
  simp [u.property]

lemma mem_allB1List (p : B1) : p ∈ allB1List := by
  unfold allB1List
  simp only [List.mem_flatMap, List.mem_filterMap, List.mem_finRange, true_and]
  refine ⟨p.val.1, p.val.2, mem_allBList p.val.2, ?_⟩
  simp [p.property]

def jListFast (_ : Unit) : List (B × B) :=
  allBList.map fun u => (u, dualB u)

lemma check_μ_d1 : allB1List.all (fun p => listsSameParity (compKernel μList d1List p) []) = true := by
  decide

lemma check_d1_d2 : allBList.all (fun u => listsSameParity (compKernel d1List d2List u) []) = true := by
  decide

lemma check_d2_j : listsSameParity (compKernel d2List jListFast ()) [] = true := by
  decide

lemma check_μ_s0 : listsSameParity (compKernel μList s0List ()) ((s0List ()).map fun p => ((), p.2)) = true := by
  decide

lemma check_h0 :
    allBList.all (fun u =>
      listsSameParity (compKernel s0List μList u ++ compKernel d1List s1List u) [(u, idempB u.val.1)]) = true := by
  decide

lemma check_h1 :
    allB1List.all (fun p =>
      listsSameParity (compKernel s1List d1List p ++ compKernel d2List s2List p)
        [(p, idempB (arrowSrc p.val.1))]) = true := by
  decide

lemma check_h2 :
    allBList.all (fun u =>
      listsSameParity (compKernel s2List d2List u ++ compKernel jListFast s3List u)
        [(u, idempB u.val.1)]) = true := by
  decide

lemma check_s3_j :
    listsSameParity (compKernel s3List jListFast ()) ((s0List ()).map fun p => ((), p.2)) = true := by
  decide

def evalList {β N : Type*} [DecidableEq β] [AddCommGroup N] [Module Λ N]
    (L : List (β × B)) (y : β) (n : N) : N :=
  match L with
  | [] => 0
  | a :: tl => (if a.1 = y then basisVec a.2 • n else 0) + evalList tl y n

lemma evalList_eq_sum_parity {β N : Type*} [DecidableEq β] [AddCommGroup N] [Module Λ N]
    [Module (ZMod 2) N] [IsScalarTower (ZMod 2) Λ N]
    (L : List (β × B)) (y : β) (n : N) :
    evalList L y n = ∑ v : B, if listParity L y v = true then basisVec v • n else 0 := by
  induction L with
  | nil => simp [evalList, listParity]
  | cons a tl ih =>
    simp only [evalList]
    by_cases hy : a.1 = y
    · rw [if_pos hy, ih]
      have hsplit : (∑ v : B, if listParity (a :: tl) y v = true then basisVec v • n else 0) =
          (if listParity (a :: tl) y a.2 = true then basisVec a.2 • n else 0) +
          ∑ v ∈ Finset.univ.erase a.2, if listParity (a :: tl) y v = true then basisVec v • n else 0 :=
        (Finset.add_sum_erase _ _ (Finset.mem_univ a.2)).symm
      have hsplit2 : (∑ v : B, if listParity tl y v = true then basisVec v • n else 0) =
          (if listParity tl y a.2 = true then basisVec a.2 • n else 0) +
          ∑ v ∈ Finset.univ.erase a.2, if listParity tl y v = true then basisVec v • n else 0 :=
        (Finset.add_sum_erase _ _ (Finset.mem_univ a.2)).symm
      rw [hsplit, hsplit2]
      have hrest : ∑ v ∈ Finset.univ.erase a.2,
            (if listParity (a :: tl) y v = true then basisVec v • n else 0) =
          ∑ v ∈ Finset.univ.erase a.2,
            (if listParity tl y v = true then basisVec v • n else 0) := by
        refine Finset.sum_congr rfl fun v hv => ?_
        have hne : a.2 ≠ v := (Finset.ne_of_mem_erase hv).symm
        have hp : listParity (a :: tl) y v = listParity tl y v := by
          simp [listParity, hne]
        rw [hp]
      rw [hrest, ← add_assoc]
      refine congrArg (· + _) ?_
      have hp : listParity (a :: tl) y a.2 = !(listParity tl y a.2) := by
        simp [listParity, hy]
      rw [hp]
      cases listParity tl y a.2 with
      | false => simp
      | true => simp [add_self_zmod2]
    · rw [if_neg hy, zero_add, ih]
      refine Finset.sum_congr rfl fun v _ => ?_
      have hp : listParity (a :: tl) y v = listParity tl y v := by
        simp [listParity, hy]
      rw [hp]

lemma evalList_eq_of_sameParity {β N : Type*} [DecidableEq β] [AddCommGroup N] [Module Λ N]
    [Module (ZMod 2) N] [IsScalarTower (ZMod 2) Λ N]
    {L1 L2 : List (β × B)} (h : listsSameParity L1 L2 = true) (y : β) (n : N) :
    evalList L1 y n = evalList L2 y n := by
  rw [evalList_eq_sum_parity, evalList_eq_sum_parity]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [listsSameParity_iff L1 L2 h y v]

lemma evalList_append {β N : Type*} [DecidableEq β] [AddCommGroup N] [Module Λ N]
    (L1 L2 : List (β × B)) (y : β) (n : N) :
    evalList (L1 ++ L2) y n = evalList L1 y n + evalList L2 y n := by
  induction L1 with
  | nil => simp [evalList]
  | cons a tl ih => simp [evalList, ih, add_assoc]

lemma evalList_zero {β N : Type*} [DecidableEq β] [AddCommGroup N] [Module Λ N]
    (L : List (β × B)) (y : β) : evalList L y (0 : N) = 0 := by
  induction L with
  | nil => rfl
  | cons a tl ih => simp [evalList, ih]

lemma evalList_add {β N : Type*} [DecidableEq β] [AddCommGroup N] [Module Λ N]
    (L : List (β × B)) (y : β) (n1 n2 : N) :
    evalList L y (n1 + n2) = evalList L y n1 + evalList L y n2 := by
  induction L with
  | nil => simp [evalList]
  | cons a tl ih =>
    simp only [evalList, ih]
    split_ifs
    · rw [smul_add]; abel
    · simp

lemma evalList_comp {β γ N : Type*} [Fintype β] [DecidableEq β] [DecidableEq γ]
    [AddCommGroup N] [Module Λ N]
    (K2 : β → List (γ × B)) (L1 : List (β × B)) (z : γ) (n : N) :
    (∑ y : β, evalList (K2 y) z (evalList L1 y n)) =
      evalList (L1.flatMap fun p1 =>
        (K2 p1.1).filterMap fun p2 => (mulB p2.2 p1.2).map fun w => (p2.1, w)) z n := by
  induction L1 with
  | nil =>
    simp only [evalList, List.flatMap_nil]
    exact Finset.sum_eq_zero fun y _ => evalList_zero _ _
  | cons a tl ih =>
    simp only [List.flatMap_cons, evalList_append, ← ih]
    have hstep : ∀ y : β, evalList (K2 y) z (evalList (a :: tl) y n) =
        (if a.1 = y then evalList (K2 y) z (basisVec a.2 • n) else 0) +
          evalList (K2 y) z (evalList tl y n) := by
      intro y
      simp only [evalList]
      rw [evalList_add]
      split_ifs <;> simp [evalList_zero]
    simp_rw [hstep, Finset.sum_add_distrib]
    refine congrArg (· + _) ?_
    rw [Finset.sum_eq_single a.1]
    · simp only [if_true]
      clear ih hstep
      induction K2 a.1 with
      | nil => rfl
      | cons b tl2 ih2 =>
        simp only [List.filterMap_cons, evalList]
        cases hm : mulB b.2 a.2 with
        | none =>
          simp only [Option.map_none]
          by_cases hbz : b.1 = z
          · rw [if_pos hbz, ← mul_smul, basisVec_mul_basisVec, hm, zero_smul, zero_add]
            exact ih2
          · rw [if_neg hbz, zero_add]; exact ih2
        | some w =>
          simp only [Option.map_some, evalList]
          by_cases hbz : b.1 = z
          · rw [if_pos hbz, if_pos hbz, ← mul_smul, basisVec_mul_basisVec, hm, ih2]
          · rw [if_neg hbz, if_neg hbz, zero_add, zero_add]; exact ih2
    · intro y _ hy; simp [Ne.symm hy]
    · intro h; exact absurd (Finset.mem_univ a.1) h

def applyKernel {α β N : Type*} [Fintype α] [DecidableEq β] [AddCommGroup N] [Module Λ N]
    (K : α → List (β × B)) (f : α → N) (y : β) : N :=
  ∑ x : α, evalList (K x) y (f x)

lemma applyKernel_comp {α β γ N : Type*} [Fintype α] [Fintype β] [DecidableEq β] [DecidableEq γ]
    [AddCommGroup N] [Module Λ N]
    (K2 : β → List (γ × B)) (K1 : α → List (β × B)) (f : α → N) (z : γ) :
    applyKernel K2 (applyKernel K1 f) z = applyKernel (compKernel K2 K1) f z := by
  unfold applyKernel compKernel
  have h1 : ∀ y : β, evalList (K2 y) z (∑ x : α, evalList (K1 x) y (f x)) =
      ∑ x : α, evalList (K2 y) z (evalList (K1 x) y (f x)) := by
    intro y
    induction (Finset.univ : Finset α) using Finset.cons_induction with
    | empty => simp [evalList_zero]
    | cons a s ha ih => simp [evalList_add, ih]
  simp_rw [h1]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun x _ => evalList_comp K2 (K1 x) z (f x)

/-- The $\nu$-twisted left $\Lambda$-module structure on `N`: `a •_ν n = nuΛ a • n`. -/
structure Twist (N : Type*) where
  val : N

lemma Twist.ext {N : Type*} {a b : Twist N} (h : a.val = b.val) : a = b := by cases a; cases b; congr

namespace Twist

variable {N : Type*}

instance [Zero N] : Zero (Twist N) := ⟨⟨0⟩⟩
instance [Add N] : Add (Twist N) := ⟨fun x y => ⟨x.val + y.val⟩⟩
instance [Neg N] : Neg (Twist N) := ⟨fun x => ⟨-x.val⟩⟩
instance [Sub N] : Sub (Twist N) := ⟨fun x y => ⟨x.val - y.val⟩⟩

instance [AddCommGroup N] : AddCommGroup (Twist N) where
  add_assoc a b c := by apply Twist.ext; exact add_assoc _ _ _
  zero_add a := by apply Twist.ext; exact zero_add _
  add_zero a := by apply Twist.ext; exact add_zero _
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel a := by apply Twist.ext; exact neg_add_cancel _
  add_comm a b := by apply Twist.ext; exact add_comm _ _
  sub_eq_add_neg a b := by apply Twist.ext; exact sub_eq_add_neg _ _

instance [AddCommGroup N] [Module (ZMod 2) N] : Module (ZMod 2) (Twist N) where
  smul c x := ⟨c • x.val⟩
  one_smul x := by apply Twist.ext; exact one_smul _ _
  mul_smul r s x := by apply Twist.ext; exact mul_smul _ _ _
  smul_zero r := by apply Twist.ext; exact smul_zero _
  smul_add r x y := by apply Twist.ext; exact smul_add _ _ _
  add_smul r s x := by apply Twist.ext; exact add_smul _ _ _
  zero_smul x := by apply Twist.ext; exact zero_smul _ _

instance [AddCommGroup N] [Module Λ N] : Module Λ (Twist N) where
  smul a x := ⟨nuΛ a • x.val⟩
  one_smul x := by apply Twist.ext; change nuΛ 1 • x.val = x.val; rw [map_one, one_smul]
  mul_smul a b x := by apply Twist.ext; change nuΛ (a * b) • x.val = nuΛ a • (nuΛ b • x.val); rw [map_mul, mul_smul]
  smul_zero a := by apply Twist.ext; change nuΛ a • (0 : N) = 0; rw [smul_zero]
  smul_add a x y := by apply Twist.ext; change nuΛ a • (x.val + y.val) = nuΛ a • x.val + nuΛ a • y.val; rw [smul_add]
  add_smul a b x := by apply Twist.ext; change nuΛ (a + b) • x.val = nuΛ a • x.val + nuΛ b • x.val; rw [map_add, add_smul]
  zero_smul x := by apply Twist.ext; change nuΛ 0 • x.val = 0; rw [map_zero, zero_smul]

instance [AddCommGroup N] [Module Λ N] [Module (ZMod 2) N] [IsScalarTower (ZMod 2) Λ N] :
    IsScalarTower (ZMod 2) Λ (Twist N) where
  smul_assoc c a x := by
    apply Twist.ext
    change nuΛ (c • a) • x.val = c • (nuΛ a • x.val)
    have hnu : nuΛ (c • a) = c • nuΛ a := by apply Λ.ext; funext w; simp [nuΛ]
    rw [hnu, smul_assoc]

instance [Fintype N] : Fintype (Twist N) :=
  Fintype.ofEquiv N ⟨Twist.mk, Twist.val, fun _ => rfl, fun _ => rfl⟩

/-- `Twist` is a strict involution up to canonical `Λ`-linear equivalence. -/
def involEquiv [AddCommGroup N] [Module Λ N] : Twist (Twist N) ≃ₗ[Λ] N where
  toFun x := x.val.val
  invFun x := ⟨⟨x⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' a x := by
    change (nuΛ (nuΛ a) • x.val.val) = a • x.val.val
    have h : nuΛ (nuΛ a) = a := by apply Λ.ext; funext w; simp [nuΛ, nuB_invol]
    rw [h]

def map [AddCommGroup N] [Module Λ N] {M : Type*} [AddCommGroup M] [Module Λ M]
    (f : N →ₗ[Λ] M) : Twist N →ₗ[Λ] Twist M where
  toFun x := ⟨f x.val⟩
  map_add' x y := by apply Twist.ext; exact map_add f _ _
  map_smul' a x := by apply Twist.ext; exact map_smul f (nuΛ a) x.val

instance [AddCommGroup N] [Module Λ N] [Module.Projective Λ N] :
    Module.Projective Λ (Twist N) := by
  classical
  have hlift : ∀ {X Y : Type _} [AddCommGroup X] [Module Λ X] [AddCommGroup Y] [Module Λ Y]
      (f : X →ₗ[Λ] Y) (g : Twist N →ₗ[Λ] Y), Function.Surjective f →
      ∃ h : Twist N →ₗ[Λ] X, f.comp h = g := by
    intro X Y _ _ _ _ f g hf
    let f' : Twist X →ₗ[Λ] Twist Y := Twist.map f
    let g' : N →ₗ[Λ] Twist Y := (Twist.map g).comp involEquiv.symm.toLinearMap
    have hf' : Function.Surjective f' := fun y =>
      let ⟨x, hx⟩ := hf y.val
      ⟨⟨x⟩, by apply Twist.ext; exact hx⟩
    obtain ⟨h', hh'⟩ := Module.projective_lifting_property f' g' hf'
    refine ⟨(involEquiv (N := X)).toLinearMap.comp (Twist.map h'), ?_⟩
    ext x
    have h1 := LinearMap.congr_fun hh' x.val
    simpa [f', g', involEquiv, Twist.map] using congrArg Twist.val h1
  exact Module.Projective.of_lifting_property hlift

end Twist

/-- Projective module `P0 N = Q_0 ⊗_Λ N ≅ ⊕_i Λ e_i ⊗_{F2} e_i N`. -/
structure P0 (N : Type*) [AddCommGroup N] [Module Λ N] where
  fn : B → N
  compat : ∀ u : B, idempΛ u.val.1 • fn u = fn u

lemma P0.ext {N : Type*} [AddCommGroup N] [Module Λ N] {a b : P0 N} (h : a.fn = b.fn) : a = b := by
  cases a; cases b; congr

/-- Projective module `P1 N = Q_1 ⊗_Λ N ≅ ⊕_x Λ e_{t(x)} ⊗_{F2} e_{s(x)} N`. -/
structure P1 (N : Type*) [AddCommGroup N] [Module Λ N] where
  fn : B1 → N
  compat : ∀ p : B1, idempΛ (arrowSrc p.val.1) • fn p = fn p

lemma P1.ext {N : Type*} [AddCommGroup N] [Module Λ N] {a b : P1 N} (h : a.fn = b.fn) : a = b := by
  cases a; cases b; congr

namespace P0

variable {N : Type*} [AddCommGroup N] [Module Λ N]

instance : Zero (P0 N) := ⟨⟨fun _ => 0, fun _ => smul_zero _⟩⟩
instance : Add (P0 N) := ⟨fun f g => ⟨fun u => f.fn u + g.fn u, fun u => by rw [smul_add, f.compat, g.compat]⟩⟩
instance : Neg (P0 N) := ⟨fun f => ⟨fun u => -f.fn u, fun u => by rw [smul_neg, f.compat]⟩⟩
instance : Sub (P0 N) := ⟨fun f g => ⟨fun u => f.fn u - g.fn u, fun u => by rw [smul_sub, f.compat, g.compat]⟩⟩

instance : AddCommGroup (P0 N) where
  add_assoc a b c := by apply P0.ext; funext u; exact add_assoc _ _ _
  zero_add a := by apply P0.ext; funext u; exact zero_add _
  add_zero a := by apply P0.ext; funext u; exact add_zero _
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel a := by apply P0.ext; funext u; exact neg_add_cancel _
  add_comm a b := by apply P0.ext; funext u; exact add_comm _ _
  sub_eq_add_neg a b := by apply P0.ext; funext u; exact sub_eq_add_neg _ _

instance [Module (ZMod 2) N] [IsScalarTower (ZMod 2) Λ N] : Module (ZMod 2) (P0 N) where
  smul c f := ⟨fun u => c • f.fn u, fun u => by rw [smul_comm, f.compat]⟩
  one_smul f := by apply P0.ext; funext u; exact one_smul _ _
  mul_smul r s f := by apply P0.ext; funext u; exact mul_smul _ _ _
  smul_zero r := by apply P0.ext; funext u; exact smul_zero _
  smul_add r f g := by apply P0.ext; funext u; exact smul_add _ _ _
  add_smul r s f := by apply P0.ext; funext u; exact add_smul _ _ _
  zero_smul f := by apply P0.ext; funext u; exact zero_smul _ _

def smulFn [Module (ZMod 2) N] (a : Λ) (f : P0 N) (w : B) : N :=
  ∑ u : B, ∑ v : B, if mulB u v = some w then a.coeff u • f.fn v else 0

lemma smulFn_compat [Module (ZMod 2) N] [IsScalarTower (ZMod 2) Λ N] (a : Λ) (f : P0 N) (w : B) :
    idempΛ w.val.1 • smulFn a f w = smulFn a f w := by
  unfold smulFn
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  split_ifs with h
  · have hw : w.val.1 = v.val.1 := ((mulB_eq_some_iff u v w).mp h).2.1
    rw [hw, smul_comm, f.compat]
  · exact smul_zero _

instance [Module (ZMod 2) N] [IsScalarTower (ZMod 2) Λ N] : Module Λ (P0 N) where
  smul a f := ⟨smulFn a f, smulFn_compat a f⟩
  one_smul f := by
    apply P0.ext; funext w
    change smulFn 1 f w = f.fn w
    unfold smulFn
    have h1 : ∀ u v : B, (if mulB u v = some w then (1 : Λ).coeff u • f.fn v else (0 : N)) =
        if u = idempB w.val.2.1 ∧ v = w then f.fn w else 0 := by
      intro u v
      by_cases hu : u = idempB w.val.2.1
      · subst hu
        have hc : (1 : Λ).coeff (idempB w.val.2.1) = 1 := by
          change oneΛ.coeff (idempB w.val.2.1) = 1
          simp [oneΛ]
        by_cases hv : v = w
        · subst hv; simp [mulB_idemp_left, hc]
        · have hne : mulB (idempB w.val.2.1) v ≠ some w := by
            intro hm
            have := (mulB_eq_some_iff _ _ _).mp hm
            exact hv (Subtype.ext (Prod.ext this.2.1.symm (Prod.ext this.1 (Fin.ext (by
              have := this.2.2.2; simp [idempB] at this; omega)))))
          simp [hne, hv]
      · by_cases h1u : ∃ i : Fin 5, u = idempB i
        · obtain ⟨i, hi⟩ := h1u; subst hi
          have hne : i ≠ w.val.2.1 := fun h => hu (by rw [h])
          have hm : mulB (idempB i) v ≠ some w := by
            intro h; exact hne ((mulB_eq_some_iff _ _ _).mp h).2.2.1.symm
          simp [hm, hu]
        · have hc : (1 : Λ).coeff u = 0 := by
            change oneΛ.coeff u = 0; simp [oneΛ, h1u]
          simp [hc, hu]
    simp_rw [h1]
    rw [Finset.sum_eq_single (idempB w.val.2.1)]
    · rw [Finset.sum_eq_single w]
      · simp
      · intro v _ hv; simp [hv]
      · intro hm; exact absurd (Finset.mem_univ w) hm
    · intro u _ hu; exact Finset.sum_eq_zero fun v _ => by simp [hu]
    · intro h; exact absurd (Finset.mem_univ _) h
  mul_smul a b f := by
    apply P0.ext; funext w
    change smulFn (a * b) f w = smulFn a ⟨smulFn b f, smulFn_compat b f⟩ w
    unfold smulFn
    trans (∑ u : B, ∑ v : B, ∑ z : B,
        if (mulB u v).bind (fun uv => mulB uv z) = some w then (a.coeff u * b.coeff v) • f.fn z else 0)
    · trans (∑ x : B, ∑ z : B, ∑ u : B, ∑ v : B,
          if mulB x z = some w ∧ mulB u v = some x then (a.coeff u * b.coeff v) • f.fn z else 0)
      · refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun z _ => ?_
        split_ifs with hxz
        · change (∑ u : B, ∑ v : B, if mulB u v = some x then a.coeff u * b.coeff v else 0) • f.fn z = _
          simp_rw [Finset.sum_smul, ite_smul, zero_smul, hxz, true_and]
        · simp [hxz]
      · rw [Finset.sum_comm]
        trans (∑ z : B, ∑ u : B, ∑ v : B, ∑ x : B,
            if mulB x z = some w ∧ mulB u v = some x then (a.coeff u * b.coeff v) • f.fn z else 0)
        · refine Finset.sum_congr rfl fun z _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun u _ => ?_
          rw [Finset.sum_comm]
        · rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun u _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun v _ => ?_
          refine Finset.sum_congr rfl fun z _ => ?_
          cases h : mulB u v with
          | none => simp
          | some uv =>
            rw [Finset.sum_eq_single uv]
            · simp
            · intro x _ hx; simp [Ne.symm hx]
            · intro hm; exact absurd (Finset.mem_univ uv) hm
    · symm
      trans (∑ u : B, ∑ y : B, ∑ v : B, ∑ z : B,
          if mulB u y = some w ∧ mulB v z = some y then (a.coeff u * b.coeff v) • f.fn z else 0)
      · refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun y _ => ?_
        split_ifs with huy
        · simp_rw [Finset.smul_sum, smul_ite, smul_zero, ← mul_smul, huy, true_and]
        · simp [huy]
      · refine Finset.sum_congr rfl fun u _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [mulB_assoc]
        cases h : mulB v z with
        | none => simp
        | some vz =>
          rw [Finset.sum_eq_single vz]
          · simp
          · intro y _ hy; simp [Ne.symm hy]
          · intro hm; exact absurd (Finset.mem_univ vz) hm
  smul_zero a := by
    apply P0.ext; funext w; change smulFn a 0 w = 0
    exact Finset.sum_eq_zero fun u _ => Finset.sum_eq_zero fun v _ => by
      change (if mulB u v = some w then a.coeff u • (0 : N) else 0) = 0; simp
  smul_add a f g := by
    apply P0.ext; funext w; change smulFn a (f + g) w = smulFn a f w + smulFn a g w
    simp only [smulFn, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
    change (if mulB u v = some w then a.coeff u • (f.fn v + g.fn v) else 0) =
      (if mulB u v = some w then a.coeff u • f.fn v else 0) +
      (if mulB u v = some w then a.coeff u • g.fn v else 0)
    split_ifs <;> simp [smul_add]
  add_smul a b f := by
    apply P0.ext; funext w; change smulFn (a + b) f w = smulFn a f w + smulFn b f w
    simp only [smulFn, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
    split_ifs <;> simp [add_smul]
  zero_smul f := by
    apply P0.ext; funext w; change smulFn 0 f w = 0
    exact Finset.sum_eq_zero fun u _ => Finset.sum_eq_zero fun v _ => by simp

instance [Module (ZMod 2) N] [IsScalarTower (ZMod 2) Λ N] :
    IsScalarTower (ZMod 2) Λ (P0 N) where
  smul_assoc c a f := by
    apply P0.ext; funext w
    change smulFn (c • a) f w = c • smulFn a f w
    simp only [smulFn, smul_coeff, Finset.smul_sum]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
    split_ifs <;> simp [mul_smul]

noncomputable instance [Fintype N] : Fintype (P0 N) := by
  classical
  exact Fintype.ofEquiv { f : B → N // ∀ u : B, idempΛ u.val.1 • f u = f u }
    { toFun := fun x => ⟨x.val, x.property⟩
      invFun := fun x => ⟨x.fn, x.compat⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

instance [Module (ZMod 2) N] [IsScalarTower (ZMod 2) Λ N] [Fintype N] :
    Module.Projective Λ (P0 N) := by
  classical
  have : Module.Finite (ZMod 2) N := Module.Finite.of_finite
  let b := Module.finBasis (ZMod 2) N
  let toFree : P0 N →ₗ[Λ] (Fin (Module.finrank (ZMod 2) N) → Λ) :=
    { toFun := fun f k => ⟨fun u => (b.repr (f.fn u)) k⟩
      map_add' := fun f g => by
        funext k; apply Λ.ext; funext u; change (b.repr (f.fn u + g.fn u)) k = (b.repr (f.fn u)) k + (b.repr (g.fn u)) k
        simp
      map_smul' := fun a f => by
        funext k; apply Λ.ext; funext w
        change (b.repr (smulFn a f w)) k = (a * ⟨fun v => (b.repr (f.fn v)) k⟩).coeff w
        simp only [smulFn, mul_coeff, map_sum, Finsupp.coe_finsetSum, Finset.sum_apply]
        refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
        split_ifs <;> simp }
  let fromFree : (Fin (Module.finrank (ZMod 2) N) → Λ) →ₗ[Λ] P0 N :=
    { toFun := fun g =>
        ⟨fun w => ∑ k, (g k).coeff w • (idempΛ w.val.1 • b k), fun w => by
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          have hid : mulB (idempB w.val.1) (idempB w.val.1) = some (idempB w.val.1) :=
            mulB_idemp_left (idempB w.val.1)
          rw [smul_comm, ← mul_smul, idempΛ, basisVec_mul_basisVec, hid]⟩
      map_add' := fun g1 g2 => by
        apply P0.ext; funext w
        change (∑ k, ((g1 k).coeff w + (g2 k).coeff w) • (idempΛ w.val.1 • b k)) =
          (∑ k, (g1 k).coeff w • (idempΛ w.val.1 • b k)) + (∑ k, (g2 k).coeff w • (idempΛ w.val.1 • b k))
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k _ => by rw [add_smul]
      map_smul' := fun a g => by
        apply P0.ext; funext w
        change (∑ k, (a * g k).coeff w • (idempΛ w.val.1 • b k)) =
          ∑ u : B, ∑ v : B, if mulB u v = some w then a.coeff u • (∑ k, (g k).coeff v • (idempΛ v.val.1 • b k)) else 0
        simp only [mul_coeff, Finset.sum_smul, ite_smul, zero_smul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun v _ => ?_
        split_ifs with h
        · have hw : w.val.1 = v.val.1 := ((mulB_eq_some_iff u v w).mp h).2.1
          rw [hw, Finset.smul_sum]
          refine Finset.sum_congr rfl fun k _ => by rw [mul_smul]
        · simp }
  have hsplit : fromFree.comp toFree = LinearMap.id := by
    apply LinearMap.ext; intro f; apply P0.ext; funext w
    change (∑ k, (b.repr (f.fn w)) k • (idempΛ w.val.1 • b k)) = f.fn w
    have hcomm : ∀ k, (b.repr (f.fn w)) k • (idempΛ w.val.1 • b k) =
        idempΛ w.val.1 • ((b.repr (f.fn w)) k • b k) := fun k => smul_comm _ _ _
    simp_rw [hcomm, ← Finset.smul_sum, b.sum_repr, f.compat]
  exact Module.Projective.of_split toFree fromFree hsplit

def map {M : Type*} [AddCommGroup M] [Module Λ M] [Module (ZMod 2) N] [IsScalarTower (ZMod 2) Λ N]
    [Module (ZMod 2) M] [IsScalarTower (ZMod 2) Λ M] (φ : N →ₗ[Λ] M) : P0 N →ₗ[Λ] P0 M where
  toFun f := ⟨fun u => φ (f.fn u), fun u => by rw [← map_smul, f.compat]⟩
  map_add' f g := by apply P0.ext; funext u; exact map_add φ _ _
  map_smul' a f := by
    apply P0.ext; funext w
    change φ (smulFn a f w) = smulFn a ⟨fun u => φ (f.fn u), _⟩ w
    simp only [smulFn, map_sum]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
    split_ifs with h
    · have h2 : φ (a.coeff u • f.fn v) = a.coeff u • φ (f.fn v) := by
        simpa [algebraMap_smul] using map_smul φ (algebraMap (ZMod 2) Λ (a.coeff u)) (f.fn v)
      exact h2
    · exact map_zero φ

end P0

namespace P1

variable {N : Type*} [AddCommGroup N] [Module Λ N]

instance : Zero (P1 N) := ⟨⟨fun _ => 0, fun _ => smul_zero _⟩⟩
instance : Add (P1 N) := ⟨fun f g => ⟨fun p => f.fn p + g.fn p, fun p => by rw [smul_add, f.compat, g.compat]⟩⟩
instance : Neg (P1 N) := ⟨fun f => ⟨fun p => -f.fn p, fun p => by rw [smul_neg, f.compat]⟩⟩
instance : Sub (P1 N) := ⟨fun f g => ⟨fun p => f.fn p - g.fn p, fun p => by rw [smul_sub, f.compat, g.compat]⟩⟩

instance : AddCommGroup (P1 N) where
  add_assoc a b c := by apply P1.ext; funext p; exact add_assoc _ _ _
  zero_add a := by apply P1.ext; funext p; exact zero_add _
  add_zero a := by apply P1.ext; funext p; exact add_zero _
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel a := by apply P1.ext; funext p; exact neg_add_cancel _
  add_comm a b := by apply P1.ext; funext p; exact add_comm _ _
  sub_eq_add_neg a b := by apply P1.ext; funext p; exact sub_eq_add_neg _ _

instance [Module (ZMod 2) N] [IsScalarTower (ZMod 2) Λ N] : Module (ZMod 2) (P1 N) where
  smul c f := ⟨fun p => c • f.fn p, fun p => by rw [smul_comm, f.compat]⟩
  one_smul f := by apply P1.ext; funext p; exact one_smul _ _
  mul_smul r s f := by apply P1.ext; funext p; exact mul_smul _ _ _
  smul_zero r := by apply P1.ext; funext p; exact smul_zero _
  smul_add r f g := by apply P1.ext; funext p; exact smul_add _ _ _
  add_smul r s f := by apply P1.ext; funext p; exact add_smul _ _ _
  zero_smul f := by apply P1.ext; funext p; exact zero_smul _ _

def smulFn [Module (ZMod 2) N] (a : Λ) (f : P1 N) (q : B1) : N :=
  ∑ u : B, ∑ p : B1, if p.val.1 = q.val.1 ∧ mulB u p.val.2 = some q.val.2 then a.coeff u • f.fn p else 0

lemma smulFn_compat [Module (ZMod 2) N] [IsScalarTower (ZMod 2) Λ N] (a : Λ) (f : P1 N) (q : B1) :
    idempΛ (arrowSrc q.val.1) • smulFn a f q = smulFn a f q := by
  unfold smulFn
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  split_ifs with h
  · rw [← h.1, smul_comm, f.compat]
  · exact smul_zero _

instance [Module (ZMod 2) N] [IsScalarTower (ZMod 2) Λ N] : Module Λ (P1 N) where
  smul a f := ⟨smulFn a f, smulFn_compat a f⟩
  one_smul f := by
    apply P1.ext; funext q
    change smulFn 1 f q = f.fn q
    unfold smulFn
    have h1 : ∀ u : B, ∀ p : B1,
        (if p.val.1 = q.val.1 ∧ mulB u p.val.2 = some q.val.2 then (1 : Λ).coeff u • f.fn p else (0 : N)) =
        if u = idempB q.val.2.val.2.1 ∧ p = q then f.fn q else 0 := by
      intro u p
      by_cases hu : u = idempB q.val.2.val.2.1
      · subst hu
        have hc : (1 : Λ).coeff (idempB q.val.2.val.2.1) = 1 := by
          change oneΛ.coeff (idempB q.val.2.val.2.1) = 1; simp [oneΛ]
        by_cases hp : p = q
        · subst hp; simp [mulB_idemp_left, hc]
        · have hne : ¬ (p.val.1 = q.val.1 ∧ mulB (idempB q.val.2.val.2.1) p.val.2 = some q.val.2) := by
            rintro ⟨h1, h2⟩
            have := (mulB_eq_some_iff _ _ _).mp h2
            apply hp; apply Subtype.ext; refine Prod.ext h1 ?_
            exact Subtype.ext (Prod.ext this.2.1.symm (Prod.ext this.1 (Fin.ext (by
              have := this.2.2.2; simp [idempB] at this; omega))))
          simp [hne, hp]
      · by_cases h1u : ∃ i : Fin 5, u = idempB i
        · obtain ⟨i, hi⟩ := h1u; subst hi
          have hne : i ≠ q.val.2.val.2.1 := fun h => hu (by rw [h])
          have hm : ¬ (p.val.1 = q.val.1 ∧ mulB (idempB i) p.val.2 = some q.val.2) := by
            rintro ⟨_, h⟩; exact hne ((mulB_eq_some_iff _ _ _).mp h).2.2.1.symm
          simp [hm, hu]
        · have hc : (1 : Λ).coeff u = 0 := by
            change oneΛ.coeff u = 0; simp [oneΛ, h1u]
          simp [hc, hu]
    simp_rw [h1]
    rw [Finset.sum_eq_single (idempB q.val.2.val.2.1)]
    · rw [Finset.sum_eq_single q]
      · simp
      · intro p _ hp; simp [hp]
      · intro hm; exact absurd (Finset.mem_univ q) hm
    · intro u _ hu; exact Finset.sum_eq_zero fun p _ => by simp [hu]
    · intro h; exact absurd (Finset.mem_univ _) h
  mul_smul a b f := by
    apply P1.ext; funext q
    change smulFn (a * b) f q = smulFn a ⟨smulFn b f, smulFn_compat b f⟩ q
    unfold smulFn
    trans (∑ u : B, ∑ v : B, ∑ p : B1,
        if p.val.1 = q.val.1 ∧ (mulB u v).bind (fun uv => mulB uv p.val.2) = some q.val.2
        then (a.coeff u * b.coeff v) • f.fn p else 0)
    · trans (∑ x : B, ∑ p : B1, ∑ u : B, ∑ v : B,
          if (p.val.1 = q.val.1 ∧ mulB x p.val.2 = some q.val.2) ∧ mulB u v = some x
          then (a.coeff u * b.coeff v) • f.fn p else 0)
      · refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun p _ => ?_
        split_ifs with hxp
        · change (∑ u : B, ∑ v : B, if mulB u v = some x then a.coeff u * b.coeff v else 0) • f.fn p = _
          simp_rw [Finset.sum_smul, ite_smul, zero_smul, hxp, true_and]
        · simp [hxp]
      · rw [Finset.sum_comm]
        trans (∑ p : B1, ∑ u : B, ∑ v : B, ∑ x : B,
            if (p.val.1 = q.val.1 ∧ mulB x p.val.2 = some q.val.2) ∧ mulB u v = some x
            then (a.coeff u * b.coeff v) • f.fn p else 0)
        · refine Finset.sum_congr rfl fun p _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun u _ => ?_
          rw [Finset.sum_comm]
        · rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun u _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun v _ => ?_
          refine Finset.sum_congr rfl fun p _ => ?_
          cases h : mulB u v with
          | none => simp
          | some uv =>
            rw [Finset.sum_eq_single uv]
            · simp
            · intro x _ hx; simp [Ne.symm hx]
            · intro hm; exact absurd (Finset.mem_univ uv) hm
    · symm
      trans (∑ u : B, ∑ r : B1, ∑ v : B, ∑ p : B1,
          if (r.val.1 = q.val.1 ∧ mulB u r.val.2 = some q.val.2) ∧ (p.val.1 = r.val.1 ∧ mulB v p.val.2 = some r.val.2)
          then (a.coeff u * b.coeff v) • f.fn p else 0)
      · refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun r _ => ?_
        split_ifs with hur
        · simp_rw [Finset.smul_sum, smul_ite, smul_zero, ← mul_smul, hur, true_and]
        · simp [hur]
      · refine Finset.sum_congr rfl fun u _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [mulB_assoc]
        cases h : mulB v p.val.2 with
        | none => simp
        | some vp =>
          have hvp : vp.val.1 = arrowTgt p.val.1 := by
            rw [((mulB_eq_some_iff v p.val.2 vp).mp h).2.1]; exact p.property
          let r0 : B1 := ⟨(p.val.1, vp), hvp⟩
          rw [Finset.sum_eq_single r0]
          · simp [r0]
          · intro r _ hr
            have hne : ¬ (p.val.1 = r.val.1 ∧ some vp = some r.val.2) := by
              rintro ⟨h1, h2⟩
              apply hr; apply Subtype.ext; exact Prod.ext h1.symm (Option.some.inj h2).symm
            rw [if_neg (fun h => hne h.2)]
          · intro hm; exact absurd (Finset.mem_univ r0) hm
  smul_zero a := by
    apply P1.ext; funext q; change smulFn a 0 q = 0
    exact Finset.sum_eq_zero fun u _ => Finset.sum_eq_zero fun p _ => by
      change (if p.val.1 = q.val.1 ∧ mulB u p.val.2 = some q.val.2 then a.coeff u • (0 : N) else 0) = 0; simp
  smul_add a f g := by
    apply P1.ext; funext q; change smulFn a (f + g) q = smulFn a f q + smulFn a g q
    simp only [smulFn, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun p _ => ?_
    change (if p.val.1 = q.val.1 ∧ mulB u p.val.2 = some q.val.2 then a.coeff u • (f.fn p + g.fn p) else 0) =
      (if p.val.1 = q.val.1 ∧ mulB u p.val.2 = some q.val.2 then a.coeff u • f.fn p else 0) +
      (if p.val.1 = q.val.1 ∧ mulB u p.val.2 = some q.val.2 then a.coeff u • g.fn p else 0)
    split_ifs <;> simp [smul_add]
  add_smul a b f := by
    apply P1.ext; funext q; change smulFn (a + b) f q = smulFn a f q + smulFn b f q
    simp only [smulFn, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun p _ => ?_
    split_ifs <;> simp [add_smul]
  zero_smul f := by
    apply P1.ext; funext q; change smulFn 0 f q = 0
    exact Finset.sum_eq_zero fun u _ => Finset.sum_eq_zero fun p _ => by simp

instance [Module (ZMod 2) N] [IsScalarTower (ZMod 2) Λ N] :
    IsScalarTower (ZMod 2) Λ (P1 N) where
  smul_assoc c a f := by
    apply P1.ext; funext q
    change smulFn (c • a) f q = c • smulFn a f q
    simp only [smulFn, smul_coeff, Finset.smul_sum]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun p _ => ?_
    split_ifs <;> simp [mul_smul]

noncomputable instance [Fintype N] : Fintype (P1 N) := by
  classical
  exact Fintype.ofEquiv { f : B1 → N // ∀ p : B1, idempΛ (arrowSrc p.val.1) • f p = f p }
    { toFun := fun x => ⟨x.val, x.property⟩
      invFun := fun x => ⟨x.fn, x.compat⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

instance [Module (ZMod 2) N] [IsScalarTower (ZMod 2) Λ N] [Fintype N] :
    Module.Projective Λ (P1 N) := by
  classical
  have : Module.Finite (ZMod 2) N := Module.Finite.of_finite
  let b := Module.finBasis (ZMod 2) N
  let toFree : P1 N →ₗ[Λ] (Fin 8 × Fin (Module.finrank (ZMod 2) N) → Λ) :=
    { toFun := fun f ik => ⟨fun u => if h : u.val.1 = arrowTgt ik.1 then (b.repr (f.fn ⟨(ik.1, u), h⟩)) ik.2 else 0⟩
      map_add' := fun f g => by
        funext ik; apply Λ.ext; funext u
        change (if h : u.val.1 = arrowTgt ik.1 then (b.repr (f.fn ⟨(ik.1, u), h⟩ + g.fn ⟨(ik.1, u), h⟩)) ik.2 else 0) =
          (if h : u.val.1 = arrowTgt ik.1 then (b.repr (f.fn ⟨(ik.1, u), h⟩)) ik.2 else 0) +
          (if h : u.val.1 = arrowTgt ik.1 then (b.repr (g.fn ⟨(ik.1, u), h⟩)) ik.2 else 0)
        split_ifs <;> simp
      map_smul' := fun a f => by
        funext ik; apply Λ.ext; funext w
        change (if h : w.val.1 = arrowTgt ik.1 then (b.repr (smulFn a f ⟨(ik.1, w), h⟩)) ik.2 else 0) =
          (a * ⟨fun v => if hv : v.val.1 = arrowTgt ik.1 then (b.repr (f.fn ⟨(ik.1, v), hv⟩)) ik.2 else 0⟩).coeff w
        simp only [mul_coeff]
        by_cases hw : w.val.1 = arrowTgt ik.1
        · rw [dif_pos hw]
          simp only [smulFn, map_sum, Finsupp.coe_finsetSum, Finset.sum_apply]
          refine Finset.sum_congr rfl fun u _ => ?_
          have hleft : (∑ p : B1, (b.repr (if p.val.1 = ik.1 ∧ mulB u p.val.2 = some w then a.coeff u • f.fn p else 0)) ik.2) =
              ∑ p : B1, if p.val.1 = ik.1 ∧ mulB u p.val.2 = some w then a.coeff u * (b.repr (f.fn p)) ik.2 else 0 :=
            Finset.sum_congr rfl fun p _ => by split_ifs <;> simp
          rw [hleft]
          have hsub : ∀ v : B,
              (if mulB u v = some w then a.coeff u * (if hv : v.val.1 = arrowTgt ik.1 then (b.repr (f.fn ⟨(ik.1, v), hv⟩)) ik.2 else 0) else 0) =
              ∑ p : B1, if p.val.2 = v ∧ p.val.1 = ik.1 ∧ mulB u p.val.2 = some w then a.coeff u * (b.repr (f.fn p)) ik.2 else 0 := by
            intro v
            by_cases hv : v.val.1 = arrowTgt ik.1
            · rw [dif_pos hv]
              let p0 : B1 := ⟨(ik.1, v), hv⟩
              rw [Finset.sum_eq_single p0]
              · simp [p0]
              · intro p _ hp
                have hne : ¬ (p.val.2 = v ∧ p.val.1 = ik.1 ∧ mulB u p.val.2 = some w) := by
                  rintro ⟨h2, h1, _⟩
                  exact hp (Subtype.ext (Prod.ext h1 h2))
                simp [hne]
              · intro hm; exact absurd (Finset.mem_univ p0) hm
            · rw [dif_neg hv, mul_zero, ite_self]
              symm
              refine Finset.sum_eq_zero fun p _ => ?_
              have hne : ¬ (p.val.2 = v ∧ p.val.1 = ik.1 ∧ mulB u p.val.2 = some w) := by
                rintro ⟨h2, h1, _⟩
                exact hv (by rw [← h2, ← h1]; exact p.property)
              simp [hne]
          simp_rw [hsub]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [Finset.sum_eq_single p.val.2]
          · simp
          · intro v _ hv; simp [Ne.symm hv]
          · intro hm; exact absurd (Finset.mem_univ p.val.2) hm
        · rw [dif_neg hw]
          symm
          refine Finset.sum_eq_zero fun u _ => Finset.sum_eq_zero fun v _ => ?_
          split_ifs with hm hv
          · exfalso; exact hw (((mulB_eq_some_iff u v w).mp hm).2.1.trans hv)
          · simp
          · rfl }
  let fromFree : (Fin 8 × Fin (Module.finrank (ZMod 2) N) → Λ) →ₗ[Λ] P1 N :=
    { toFun := fun g =>
        ⟨fun q => ∑ k, (g (q.val.1, k)).coeff q.val.2 • (idempΛ (arrowSrc q.val.1) • b k), fun q => by
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          have hid : mulB (idempB (arrowSrc q.val.1)) (idempB (arrowSrc q.val.1)) = some (idempB (arrowSrc q.val.1)) :=
            mulB_idemp_left (idempB (arrowSrc q.val.1))
          rw [smul_comm, ← mul_smul, idempΛ, basisVec_mul_basisVec, hid]⟩
      map_add' := fun g1 g2 => by
        apply P1.ext; funext q
        change (∑ k, ((g1 (q.val.1, k)).coeff q.val.2 + (g2 (q.val.1, k)).coeff q.val.2) •
          (idempΛ (arrowSrc q.val.1) • b k)) =
          (∑ k, (g1 (q.val.1, k)).coeff q.val.2 • (idempΛ (arrowSrc q.val.1) • b k)) +
          (∑ k, (g2 (q.val.1, k)).coeff q.val.2 • (idempΛ (arrowSrc q.val.1) • b k))
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k _ => by rw [add_smul]
      map_smul' := fun a g => by
        apply P1.ext; funext q
        change (∑ k, (a * g (q.val.1, k)).coeff q.val.2 • (idempΛ (arrowSrc q.val.1) • b k)) =
          smulFn a ⟨fun p => ∑ k, (g (p.val.1, k)).coeff p.val.2 • (idempΛ (arrowSrc p.val.1) • b k), _⟩ q
        simp only [mul_coeff, Finset.sum_smul, ite_smul, zero_smul, smulFn]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [Finset.sum_comm]
        have hstep : ∀ v : B,
            (∑ k, if mulB u v = some q.val.2 then (a.coeff u * (g (q.val.1, k)).coeff v) • (idempΛ (arrowSrc q.val.1) • b k) else 0) =
            ∑ p : B1, if p.val.2 = v ∧ p.val.1 = q.val.1 ∧ mulB u p.val.2 = some q.val.2 then
              a.coeff u • (∑ k, (g (p.val.1, k)).coeff p.val.2 • (idempΛ (arrowSrc p.val.1) • b k)) else 0 := by
          intro v
          by_cases hv : v.val.1 = arrowTgt q.val.1
          · let p0 : B1 := ⟨(q.val.1, v), hv⟩
            rw [Finset.sum_eq_single p0]
            · simp only [p0, true_and]
              split_ifs with hm
              · rw [Finset.smul_sum]
                refine Finset.sum_congr rfl fun k _ => by rw [mul_smul]
              · simp
            · intro p _ hp
              have hne : ¬ (p.val.2 = v ∧ p.val.1 = q.val.1 ∧ mulB u p.val.2 = some q.val.2) := by
                rintro ⟨h2, h1, _⟩; exact hp (Subtype.ext (Prod.ext h1 h2))
              simp [hne]
            · intro hm; exact absurd (Finset.mem_univ p0) hm
          · have hnm : mulB u v ≠ some q.val.2 := by
              intro hm; exact hv (((mulB_eq_some_iff u v q.val.2).mp hm).2.1.symm.trans q.property)
            simp only [hnm, if_false, Finset.sum_const_zero]
            symm
            refine Finset.sum_eq_zero fun p _ => ?_
            have hne : ¬ (p.val.2 = v ∧ p.val.1 = q.val.1 ∧ mulB u p.val.2 = some q.val.2) := by
              rintro ⟨h2, h1, _⟩; exact hv (by rw [← h2, ← h1]; exact p.property)
            simp [hne]
        simp_rw [hstep]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [Finset.sum_eq_single p.val.2]
        · simp
        · intro v _ hv; simp [Ne.symm hv]
        · intro hm; exact absurd (Finset.mem_univ p.val.2) hm }
  have hsplit : fromFree.comp toFree = LinearMap.id := by
    apply LinearMap.ext; intro f; apply P1.ext; funext q
    change (∑ k, (if h : q.val.2.val.1 = arrowTgt q.val.1 then (b.repr (f.fn ⟨(q.val.1, q.val.2), h⟩)) k else 0) •
      (idempΛ (arrowSrc q.val.1) • b k)) = f.fn q
    have hq : q.val.2.val.1 = arrowTgt q.val.1 := q.property
    simp_rw [dif_pos hq, smul_comm _ (idempΛ (arrowSrc q.val.1)), ← Finset.smul_sum, b.sum_repr, f.compat]
  exact Module.Projective.of_split toFree fromFree hsplit

def map {M : Type*} [AddCommGroup M] [Module Λ M] [Module (ZMod 2) N] [IsScalarTower (ZMod 2) Λ N]
    [Module (ZMod 2) M] [IsScalarTower (ZMod 2) Λ M] (φ : N →ₗ[Λ] M) : P1 N →ₗ[Λ] P1 M where
  toFun f := ⟨fun p => φ (f.fn p), fun p => by rw [← map_smul, f.compat]⟩
  map_add' f g := by apply P1.ext; funext p; exact map_add φ _ _
  map_smul' a f := by
    apply P1.ext; funext q
    change φ (smulFn a f q) = smulFn a ⟨fun p => φ (f.fn p), _⟩ q
    simp only [smulFn, map_sum]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun p _ => ?_
    split_ifs with h
    · have h2 := map_smul φ (algebraMap (ZMod 2) Λ (a.coeff u)) (f.fn p)
      simp only [algebraMap_smul] at h2
      exact h2
    · exact map_zero φ

end P1

section ResolutionMaps

variable {N : Type*} [AddCommGroup N] [Module Λ N] [Module (ZMod 2) N] [IsScalarTower (ZMod 2) Λ N]

lemma evalList_eq_sum_mem {β : Type*} [DecidableEq β] (L : List (β × B)) (y : β) (n : N) :
    evalList L y n = L.foldr (fun p acc => if p.1 = y then basisVec p.2 • n + acc else acc) 0 := by
  induction L with
  | nil => rfl
  | cons a tl ih =>
    simp only [evalList, List.foldr_cons, ih]
    split_ifs <;> simp

lemma idemp_evalList_d1 (p : B1) (w : B) (n : N) (_hn : idempΛ (arrowSrc p.val.1) • n = n) :
    idempΛ w.val.1 • evalList (d1List p) w n = evalList (d1List p) w n := by
  unfold d1List
  rw [evalList_append, smul_add]
  congr 1
  · cases hm : mulB p.val.2 (arrowB p.val.1) with
    | none => simp [evalList]
    | some z =>
      simp only [evalList, add_zero]
      split_ifs with hzw
      · subst hzw
        have hz1 : z.val.1 = arrowSrc p.val.1 := by
          have := ((mulB_eq_some_iff p.val.2 (arrowB p.val.1) z).mp hm).2.1
          rw [this]; unfold arrowB arrowSrc; split_ifs <;> rfl
        have hid : mulB (idempB (arrowSrc p.val.1)) (idempB (arrowSrc p.val.1)) = some (idempB (arrowSrc p.val.1)) :=
          mulB_idemp_left (idempB (arrowSrc p.val.1))
        rw [hz1, ← mul_smul, idempΛ, basisVec_mul_basisVec, hid]
      · simp
  · simp only [evalList, add_zero]
    split_ifs with hpw
    · subst hpw
      have ha : mulB (idempB p.val.2.val.1) (arrowB p.val.1) = some (arrowB p.val.1) := by
        rw [p.property]
        have ht : (arrowB p.val.1).val.2.1 = arrowTgt p.val.1 := by
          unfold arrowB arrowTgt; split_ifs <;> rfl
        rw [← ht]; exact mulB_idemp_left _
      rw [← mul_smul, idempΛ, basisVec_mul_basisVec, ha]
    · simp

lemma idemp_evalList_d2 (u : B) (q : B1) (n : N) (_hn : idempΛ u.val.1 • n = n) :
    idempΛ (arrowSrc q.val.1) • evalList (d2List u) q n = evalList (d2List u) q n := by
  have hall : allBList.all (fun u => (d2List u).all fun pair => pair.2.val.2.1 == arrowSrc pair.1.val.1) = true := by
    decide
  have h1 : ∀ (L : List (B1 × B)),
      L.all (fun pair => pair.2.val.2.1 == arrowSrc pair.1.val.1) = true →
      idempΛ (arrowSrc q.val.1) • evalList L q n = evalList L q n := by
    intro L hL
    induction L with
    | nil => simp [evalList]
    | cons a tl ih =>
      simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq] at hL
      simp only [evalList, smul_add]
      congr 1
      · split_ifs with haq
        · rw [← haq, ← hL.1, ← mul_smul, idempΛ, basisVec_mul_basisVec, mulB_idemp_left]
        · exact smul_zero _
      · exact ih hL.2
  exact h1 (d2List u) (List.all_eq_true.mp hall u (mem_allBList u))

def resμ (N : Type*) [AddCommGroup N] [Module Λ N] [Module (ZMod 2) N] [IsScalarTower (ZMod 2) Λ N] :
    P0 N →ₗ[Λ] N where
  toFun f := applyKernel μList f.fn ()
  map_add' f g := by
    unfold applyKernel
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun u _ => evalList_add _ _ _ _
  map_smul' a f := by
    change (∑ w : B, evalList (μList w) () (P0.smulFn a f w)) = a • (∑ v : B, evalList (μList v) () (f.fn v))
    have hev : ∀ (x : B) (n : N), evalList (μList x) () n = basisVec x • n := fun x n => by
      simp [μList, evalList]
    simp_rw [hev]
    conv_rhs => rw [eq_sum_basisVec a, Finset.sum_smul]
    simp_rw [Finset.smul_sum]
    trans (∑ u : B, ∑ v : B, (a.coeff u • basisVec u) • (basisVec v • f.fn v))
    · simp only [P0.smulFn]
      have h1 : ∀ w : B, basisVec w • (∑ u : B, ∑ v : B, if mulB u v = some w then a.coeff u • f.fn v else 0) =
          ∑ u : B, ∑ v : B, if mulB u v = some w then (a.coeff u • basisVec w) • f.fn v else 0 := by
        intro w
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun v _ => ?_
        split_ifs
        · rw [smul_assoc, smul_comm (basisVec w)]
        · exact smul_zero _
      simp_rw [h1]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [← mul_smul, smul_mulΛ, basisVec_mul_basisVec]
      cases hm : mulB u v with
      | none => simp
      | some w0 =>
        rw [Finset.sum_eq_single w0]
        · simp
        · intro w _ hw; simp [Ne.symm hw]
        · intro h; exact absurd (Finset.mem_univ w0) h
    · rfl

def leftMulB (a : B) (u : B) : List (B × B) :=
  match mulB a u with | some w => [(w, idempB u.val.1)] | none => []

def leftMulB1 (a : B) (p : B1) : List (B1 × B) :=
  match mulB a p.val.2 with
  | some w =>
    if h : w.val.1 = arrowTgt p.val.1 then [(⟨(p.val.1, w), h⟩, idempB (arrowSrc p.val.1))] else []
  | none => []

lemma check_d1_lin :
    allBList.all (fun a =>
      allB1List.all (fun p =>
        listsSameParity (compKernel (leftMulB a) d1List p) (compKernel d1List (leftMulB1 a) p))) = true := by
  decide

lemma check_d2_lin :
    allBList.all (fun a =>
      allBList.all (fun u =>
        listsSameParity (compKernel (leftMulB1 a) d2List u) (compKernel d2List (leftMulB a) u))) = true := by
  decide

lemma applyKernel_leftMulB (a : B) (f : P0 N) (w : B) :
    applyKernel (leftMulB a) f.fn w = (basisVec a • f).fn w := by
  symm
  change P0.smulFn (basisVec a) f w = ∑ v : B, evalList (leftMulB a v) w (f.fn v)
  unfold P0.smulFn
  rw [Finset.sum_eq_single a]
  · refine Finset.sum_congr rfl fun v _ => ?_
    unfold leftMulB
    cases hm : mulB a v with
    | none => simp [evalList]
    | some z =>
      simp only [evalList, add_zero, basisVec, if_true, one_smul]
      by_cases hzw : z = w
      · subst hzw; simp only [if_true]; exact (f.compat v).symm
      · simp [hzw]
  · intro u _ hu; exact Finset.sum_eq_zero fun v _ => by simp [basisVec, hu]
  · intro hm; exact absurd (Finset.mem_univ a) hm

lemma applyKernel_leftMulB1 (a : B) (f : P1 N) (q : B1) :
    applyKernel (leftMulB1 a) f.fn q = (basisVec a • f).fn q := by
  symm
  change P1.smulFn (basisVec a) f q = ∑ p : B1, evalList (leftMulB1 a p) q (f.fn p)
  unfold P1.smulFn
  rw [Finset.sum_eq_single a]
  · refine Finset.sum_congr rfl fun p _ => ?_
    unfold leftMulB1
    cases hm : mulB a p.val.2 with
    | none => simp [evalList]
    | some z =>
      have hz : z.val.1 = arrowTgt p.val.1 := by
        rw [((mulB_eq_some_iff a p.val.2 z).mp hm).2.1]; exact p.property
      simp only [dif_pos hz, evalList, add_zero, basisVec, if_true, one_smul]
      by_cases hpq : (⟨(p.val.1, z), hz⟩ : B1) = q
      · subst hpq
        simp only [if_true, and_self]
        exact (f.compat p).symm
      · have hne : ¬ (p.val.1 = q.val.1 ∧ some z = some q.val.2) := by
          rintro ⟨h1, h2⟩
          apply hpq; apply Subtype.ext; exact Prod.ext h1 (Option.some.inj h2)
        rw [if_neg hpq, if_neg hne]
  · intro u _ hu; exact Finset.sum_eq_zero fun p _ => by simp [basisVec, hu]
  · intro hm; exact absurd (Finset.mem_univ a) hm

def resD1 (N : Type*) [AddCommGroup N] [Module Λ N] [Module (ZMod 2) N] [IsScalarTower (ZMod 2) Λ N] :
    P1 N →ₗ[Λ] P0 N where
  toFun f := ⟨applyKernel d1List f.fn, fun w => by
    unfold applyKernel; rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun p _ => idemp_evalList_d1 p w (f.fn p) (f.compat p)⟩
  map_add' f g := by
    apply P0.ext; funext w; change applyKernel d1List (fun p => f.fn p + g.fn p) w =
      applyKernel d1List f.fn w + applyKernel d1List g.fn w
    unfold applyKernel; rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun p _ => evalList_add _ _ _ _
  map_smul' a f := by
    let D1add : P1 N →ₗ[ZMod 2] P0 N :=
      { toFun := fun x => ⟨applyKernel d1List x.fn, fun w => by
          unfold applyKernel; rw [Finset.smul_sum]
          exact Finset.sum_congr rfl fun p _ => idemp_evalList_d1 p w (x.fn p) (x.compat p)⟩
        map_add' := fun x y => by
          apply P0.ext; funext w
          change applyKernel d1List (fun p => x.fn p + y.fn p) w =
            applyKernel d1List x.fn w + applyKernel d1List y.fn w
          unfold applyKernel; rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun p _ => evalList_add _ _ _ _
        map_smul' := fun c x => by
          apply P0.ext; funext w; change applyKernel d1List (fun p => c • x.fn p) w = c • applyKernel d1List x.fn w
          unfold applyKernel; rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun p _ => ?_
          induction d1List p with
          | nil => simp [evalList]
          | cons hd tl ih =>
            simp only [evalList, smul_add, ih]
            congr 1; split_ifs
            · exact (smul_comm _ _ _).symm
            · exact (smul_zero c).symm }
    have hbasis : ∀ u : B, D1add (basisVec u • f) = basisVec u • D1add f := by
      intro u; apply P0.ext; funext w
      change applyKernel d1List (basisVec u • f).fn w = (basisVec u • D1add f).fn w
      rw [← applyKernel_leftMulB u]
      have harg : (basisVec u • f).fn = applyKernel (leftMulB1 u) f.fn := funext fun q => (applyKernel_leftMulB1 u f q).symm
      change applyKernel d1List (basisVec u • f).fn w = applyKernel (leftMulB u) (applyKernel d1List f.fn) w
      rw [harg, applyKernel_comp, applyKernel_comp]
      refine Finset.sum_congr rfl fun p _ => ?_
      have hchk := List.all_eq_true.mp (List.all_eq_true.mp check_d1_lin u (mem_allBList u)) p (mem_allB1List p)
      exact (evalList_eq_of_sameParity hchk w (f.fn p)).symm
    change D1add (a • f) = a • D1add f
    rw [eq_sum_basisVec a, Finset.sum_smul, Finset.sum_smul, map_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [smul_assoc, smul_assoc, map_smul]
    exact congrArg (a.coeff u • ·) (hbasis u)

def resD2 (N : Type*) [AddCommGroup N] [Module Λ N] [Module (ZMod 2) N] [IsScalarTower (ZMod 2) Λ N] :
    P0 N →ₗ[Λ] P1 N where
  toFun f := ⟨applyKernel d2List f.fn, fun q => by
    unfold applyKernel; rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun u _ => idemp_evalList_d2 u q (f.fn u) (f.compat u)⟩
  map_add' f g := by
    apply P1.ext; funext q; change applyKernel d2List (fun u => f.fn u + g.fn u) q =
      applyKernel d2List f.fn q + applyKernel d2List g.fn q
    unfold applyKernel; rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun u _ => evalList_add _ _ _ _
  map_smul' a f := by
    let D2add : P0 N →ₗ[ZMod 2] P1 N :=
      { toFun := fun x => ⟨applyKernel d2List x.fn, fun q => by
          unfold applyKernel; rw [Finset.smul_sum]
          exact Finset.sum_congr rfl fun v _ => idemp_evalList_d2 v q (x.fn v) (x.compat v)⟩
        map_add' := fun x y => by
          apply P1.ext; funext q
          change applyKernel d2List (fun v => x.fn v + y.fn v) q =
            applyKernel d2List x.fn q + applyKernel d2List y.fn q
          unfold applyKernel; rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun v _ => evalList_add _ _ _ _
        map_smul' := fun c x => by
          apply P1.ext; funext q; change applyKernel d2List (fun v => c • x.fn v) q = c • applyKernel d2List x.fn q
          unfold applyKernel; rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun v _ => ?_
          induction d2List v with
          | nil => simp [evalList]
          | cons hd tl ih =>
            simp only [evalList, smul_add, ih]
            congr 1; split_ifs
            · exact (smul_comm _ _ _).symm
            · exact (smul_zero c).symm }
    have hbasis : ∀ u : B, D2add (basisVec u • f) = basisVec u • D2add f := by
      intro u; apply P1.ext; funext q
      change applyKernel d2List (basisVec u • f).fn q = (basisVec u • D2add f).fn q
      rw [← applyKernel_leftMulB1 u]
      have harg : (basisVec u • f).fn = applyKernel (leftMulB u) f.fn := funext fun w => (applyKernel_leftMulB u f w).symm
      change applyKernel d2List (basisVec u • f).fn q = applyKernel (leftMulB1 u) (applyKernel d2List f.fn) q
      rw [harg, applyKernel_comp, applyKernel_comp]
      refine Finset.sum_congr rfl fun v _ => ?_
      have hchk := List.all_eq_true.mp (List.all_eq_true.mp check_d2_lin u (mem_allBList u)) v (mem_allBList v)
      exact (evalList_eq_of_sameParity hchk q (f.fn v)).symm
    change D2add (a • f) = a • D2add f
    rw [eq_sum_basisVec a, Finset.sum_smul, Finset.sum_smul, map_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [smul_assoc, smul_assoc, map_smul]
    exact congrArg (a.coeff u • ·) (hbasis u)

lemma check_j_lin :
    allBList.all (fun a =>
      listsSameParity (compKernel (leftMulB a) jListFast ())
        ((jListFast ()).filterMap fun p => (mulB p.2 (nuB a)).map fun w => (p.1, w))) = true := by
  decide

def resJ (N : Type*) [AddCommGroup N] [Module Λ N] [Module (ZMod 2) N] [IsScalarTower (ZMod 2) Λ N] :
    Twist N →ₗ[Λ] P0 N where
  toFun x := ⟨fun u => basisVec (dualB u) • x.val, fun u => by
    have h : mulB (idempB u.val.1) (dualB u) = some (dualB u) := by
      have ht : (dualB u).val.2.1 = u.val.1 := rfl
      rw [← ht]; exact mulB_idemp_left _
    rw [← mul_smul, idempΛ, basisVec_mul_basisVec, h]⟩
  map_add' x y := by apply P0.ext; funext u; exact smul_add _ _ _
  map_smul' a x := by
    have hjeval : ∀ (n : N) (w : B), evalList (jListFast ()) w n = basisVec (dualB w) • n := by
      intro n w
      rw [evalList_eq_sum_parity]
      have hpar : ∀ v : B, listParity (jListFast ()) w v = decide (v = dualB w) := by
        have h : allBList.all (fun w => allBList.all (fun v => listParity (jListFast ()) w v == decide (v = dualB w))) = true := by
          decide
        intro v
        exact beq_iff_eq.mp (List.all_eq_true.mp (List.all_eq_true.mp h w (mem_allBList w)) v (mem_allBList v))
      simp_rw [hpar]
      rw [Finset.sum_eq_single (dualB w)]
      · simp
      · intro v _ hv; simp [hv]
      · intro hm; exact absurd (Finset.mem_univ _) hm
    let Jadd : Twist N →ₗ[ZMod 2] P0 N :=
      { toFun := fun y => ⟨fun w => basisVec (dualB w) • y.val, fun w => by
          have h : mulB (idempB w.val.1) (dualB w) = some (dualB w) := by
            have ht : (dualB w).val.2.1 = w.val.1 := rfl
            rw [← ht]; exact mulB_idemp_left _
          rw [← mul_smul, idempΛ, basisVec_mul_basisVec, h]⟩
        map_add' := fun y1 y2 => by apply P0.ext; funext w; exact smul_add _ _ _
        map_smul' := fun c y => by apply P0.ext; funext w; exact (smul_comm _ _ _).symm }
    have hbasis : ∀ u : B, Jadd (basisVec u • x) = basisVec u • Jadd x := by
      intro u; apply P0.ext; funext w
      have hnu : (basisVec u • x : Twist N).val = basisVec (nuB u) • x.val := by
        change nuΛ (basisVec u) • x.val = _; rw [nuΛ_basisVec]
      change basisVec (dualB w) • (basisVec u • x : Twist N).val = (basisVec u • Jadd x).fn w
      rw [hnu, ← applyKernel_leftMulB u]
      have hfn : (Jadd x).fn = applyKernel jListFast (fun _ : Unit => x.val) := by
        funext v
        simp only [applyKernel, Finset.univ_unique, PUnit.default_eq_unit, Finset.sum_singleton]
        exact (hjeval x.val v).symm
      rw [hfn, applyKernel_comp]
      simp only [applyKernel, Finset.univ_unique, PUnit.default_eq_unit, Finset.sum_singleton]
      change basisVec (dualB w) • (basisVec (nuB u) • x.val) = evalList (compKernel (leftMulB u) jListFast ()) w x.val
      have hchk := List.all_eq_true.mp check_j_lin u (mem_allBList u)
      rw [evalList_eq_of_sameParity hchk w x.val, ← hjeval (basisVec (nuB u) • x.val) w]
      clear hjeval hchk hfn hnu
      induction jListFast () with
      | nil => rfl
      | cons hd tl ih =>
        simp only [List.filterMap_cons, evalList]
        cases hm : mulB hd.2 (nuB u) with
        | none =>
          simp only [Option.map_none]
          by_cases hw : hd.1 = w
          · rw [if_pos hw, ← mul_smul, basisVec_mul_basisVec, hm, zero_smul, zero_add]; exact ih
          · rw [if_neg hw, zero_add]; exact ih
        | some z =>
          simp only [Option.map_some, evalList]
          by_cases hw : hd.1 = w
          · rw [if_pos hw, if_pos hw, ← mul_smul, basisVec_mul_basisVec, hm, ih]
          · rw [if_neg hw, if_neg hw, zero_add, zero_add]; exact ih
    change Jadd (a • x) = a • Jadd x
    rw [eq_sum_basisVec a, Finset.sum_smul, Finset.sum_smul, map_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [smul_assoc, smul_assoc, map_smul]
    exact congrArg (a.coeff u • ·) (hbasis u)

lemma evalList_idemp_sum (n : N) :
    evalList ((s0List ()).map fun p => ((), p.2)) () n = n := by
  have h : evalList ((s0List ()).map fun p => ((), p.2)) () n =
      (∑ i : Fin 5, idempΛ i) • n := by
    simp [s0List, evalList, idempΛ, Fin.sum_univ_five, add_smul, add_assoc]
  rw [h, sum_idempΛ, one_smul]

lemma resμ_comp_resD1 (f : P1 N) : resμ N (resD1 N f) = 0 := by
  change applyKernel μList (applyKernel d1List f.fn) () = 0
  rw [applyKernel_comp]
  exact Finset.sum_eq_zero fun p _ =>
    evalList_eq_of_sameParity (List.all_eq_true.mp check_μ_d1 p (mem_allB1List p)) () (f.fn p)

lemma resD1_comp_resD2 (f : P0 N) : resD1 N (resD2 N f) = 0 := by
  apply P0.ext; funext w
  change applyKernel d1List (applyKernel d2List f.fn) w = 0
  rw [applyKernel_comp]
  exact Finset.sum_eq_zero fun u _ =>
    evalList_eq_of_sameParity (List.all_eq_true.mp check_d1_d2 u (mem_allBList u)) w (f.fn u)

lemma resJ_fn_eq (x : Twist N) (w : B) :
    (resJ N x).fn w = applyKernel jListFast (fun _ : Unit => x.val) w := by
  simp only [applyKernel, Finset.univ_unique, PUnit.default_eq_unit, Finset.sum_singleton]
  change basisVec (dualB w) • x.val = evalList (jListFast ()) w x.val
  rw [evalList_eq_sum_parity]
  have hpar : ∀ v : B, listParity (jListFast ()) w v = decide (v = dualB w) := by
    have h : allBList.all (fun w => allBList.all (fun v => listParity (jListFast ()) w v == decide (v = dualB w))) = true := by
      decide
    intro v
    exact beq_iff_eq.mp (List.all_eq_true.mp (List.all_eq_true.mp h w (mem_allBList w)) v (mem_allBList v))
  simp_rw [hpar]
  rw [Finset.sum_eq_single (dualB w)]
  · simp
  · intro v _ hv; simp [hv]
  · intro hm; exact absurd (Finset.mem_univ _) hm

lemma resD2_comp_resJ (x : Twist N) : resD2 N (resJ N x) = 0 := by
  apply P1.ext; funext q
  have hfn : (resJ N x).fn = applyKernel jListFast (fun _ : Unit => x.val) := funext (resJ_fn_eq x)
  change applyKernel d2List (resJ N x).fn q = 0
  rw [hfn, applyKernel_comp]
  simp only [applyKernel, Finset.univ_unique, PUnit.default_eq_unit, Finset.sum_singleton]
  exact evalList_eq_of_sameParity check_d2_j q x.val

lemma idemp_evalList_s1 (u : B) (q : B1) (n : N) :
    idempΛ (arrowSrc q.val.1) • evalList (s1List u) q n = evalList (s1List u) q n := by
  have hall : allBList.all (fun u => (s1List u).all fun p => p.2.val.2.1 == arrowSrc p.1.val.1) = true := by
    decide
  have h1 : ∀ (L : List (B1 × B)),
      L.all (fun p => p.2.val.2.1 == arrowSrc p.1.val.1) = true →
      idempΛ (arrowSrc q.val.1) • evalList L q n = evalList L q n := by
    intro L hL
    induction L with
    | nil => simp [evalList]
    | cons a tl ih =>
      simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq] at hL
      simp only [evalList, smul_add]
      congr 1
      · split_ifs with haq
        · rw [← haq, ← hL.1, ← mul_smul, idempΛ, basisVec_mul_basisVec, mulB_idemp_left]
        · exact smul_zero _
      · exact ih hL.2
  exact h1 (s1List u) (List.all_eq_true.mp hall u (mem_allBList u))

lemma idemp_evalList_s2 (p : B1) (w : B) (n : N) :
    idempΛ w.val.1 • evalList (s2List p) w n = evalList (s2List p) w n := by
  have hall : allB1List.all (fun p => (s2List p).all fun pair => pair.2.val.2.1 == pair.1.val.1) = true := by
    decide
  have h1 : ∀ (L : List (B × B)),
      L.all (fun pair => pair.2.val.2.1 == pair.1.val.1) = true →
      idempΛ w.val.1 • evalList L w n = evalList L w n := by
    intro L hL
    induction L with
    | nil => simp [evalList]
    | cons a tl ih =>
      simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq] at hL
      simp only [evalList, smul_add]
      congr 1
      · split_ifs with haw
        · rw [← haw, ← hL.1, ← mul_smul, idempΛ, basisVec_mul_basisVec, mulB_idemp_left]
        · exact smul_zero _
      · exact ih hL.2
  exact h1 (s2List p) (List.all_eq_true.mp hall p (mem_allB1List p))

lemma resμ_surj : Function.Surjective (resμ N) := by
  intro n
  refine ⟨⟨applyKernel s0List (fun _ : Unit => n), fun w => by
    simp only [applyKernel, Finset.univ_unique, PUnit.default_eq_unit, Finset.sum_singleton]
    have h1 : ∀ (L : List (B × B)),
        L.all (fun pair => pair.2.val.2.1 == pair.1.val.1) = true →
        idempΛ w.val.1 • evalList L w n = evalList L w n := by
      intro L hL
      induction L with
      | nil => simp [evalList]
      | cons a tl ih =>
        simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq] at hL
        simp only [evalList, smul_add]
        congr 1
        · split_ifs with haw
          · rw [← haw, ← hL.1, ← mul_smul, idempΛ, basisVec_mul_basisVec, mulB_idemp_left]
          · exact smul_zero _
        · exact ih hL.2
    exact h1 (s0List ()) (by decide)⟩, ?_⟩
  change applyKernel μList (applyKernel s0List (fun _ : Unit => n)) () = n
  rw [applyKernel_comp]
  simp only [applyKernel, Finset.univ_unique, PUnit.default_eq_unit, Finset.sum_singleton]
  rw [evalList_eq_of_sameParity check_μ_s0 () n, evalList_idemp_sum]

lemma resJ_inj : Function.Injective (resJ N) := by
  have hleft : ∀ x : Twist N, applyKernel s3List (resJ N x).fn () = x.val := by
    intro x
    have hfn : (resJ N x).fn = applyKernel jListFast (fun _ : Unit => x.val) := funext (resJ_fn_eq x)
    rw [hfn, applyKernel_comp]
    simp only [applyKernel, Finset.univ_unique, PUnit.default_eq_unit, Finset.sum_singleton]
    rw [evalList_eq_of_sameParity check_s3_j () x.val, evalList_idemp_sum]
  intro x y hxy
  apply Twist.ext
  rw [← hleft x, ← hleft y, hxy]

lemma ker_resμ_eq_range_resD1 : LinearMap.ker (resμ N) = LinearMap.range (resD1 N) := by
  ext f
  simp only [LinearMap.mem_ker, LinearMap.mem_range]
  constructor
  · intro hf
    refine ⟨⟨applyKernel s1List f.fn, fun q => by
      unfold applyKernel; rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun u _ => idemp_evalList_s1 u q (f.fn u)⟩, ?_⟩
    apply P0.ext; funext w
    have hsum : applyKernel s0List (fun _ : Unit => resμ N f) w +
        applyKernel d1List (applyKernel s1List f.fn) w = f.fn w := by
      have h1 : applyKernel s0List (fun _ : Unit => resμ N f) w =
          applyKernel (compKernel s0List μList) f.fn w := by
        have hfun : (fun _ : Unit => resμ N f) = applyKernel μList f.fn := funext fun _ => rfl
        rw [hfun, applyKernel_comp]
      rw [h1, applyKernel_comp]
      unfold applyKernel
      rw [← Finset.sum_add_distrib]
      trans (∑ u : B, evalList [(u, idempB u.val.1)] w (f.fn u))
      · refine Finset.sum_congr rfl fun u _ => ?_
        rw [← evalList_append]
        exact evalList_eq_of_sameParity (List.all_eq_true.mp check_h0 u (mem_allBList u)) w (f.fn u)
      · rw [Finset.sum_eq_single w]
        · simp only [evalList, if_true, add_zero]; exact f.compat w
        · intro u _ hu; simp [evalList, hu]
        · intro hm; exact absurd (Finset.mem_univ w) hm
    rw [hf] at hsum
    have hz : applyKernel s0List (fun _ : Unit => (0 : N)) w = 0 := by
      simp [applyKernel, evalList_zero]
    rw [hz, zero_add] at hsum
    exact hsum
  · rintro ⟨g, rfl⟩
    exact resμ_comp_resD1 g

lemma ker_resD1_eq_range_resD2 : LinearMap.ker (resD1 N) = LinearMap.range (resD2 N) := by
  ext f
  simp only [LinearMap.mem_ker, LinearMap.mem_range]
  constructor
  · intro hf
    refine ⟨⟨applyKernel s2List f.fn, fun w => by
      unfold applyKernel; rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun p _ => idemp_evalList_s2 p w (f.fn p)⟩, ?_⟩
    apply P1.ext; funext q
    have hsum : applyKernel s1List (resD1 N f).fn q +
        applyKernel d2List (applyKernel s2List f.fn) q = f.fn q := by
      change applyKernel s1List (applyKernel d1List f.fn) q +
          applyKernel d2List (applyKernel s2List f.fn) q = f.fn q
      rw [applyKernel_comp, applyKernel_comp]
      unfold applyKernel
      rw [← Finset.sum_add_distrib]
      trans (∑ p : B1, evalList [(p, idempB (arrowSrc p.val.1))] q (f.fn p))
      · refine Finset.sum_congr rfl fun p _ => ?_
        rw [← evalList_append]
        exact evalList_eq_of_sameParity (List.all_eq_true.mp check_h1 p (mem_allB1List p)) q (f.fn p)
      · rw [Finset.sum_eq_single q]
        · simp only [evalList, if_true, add_zero]; exact f.compat q
        · intro p _ hp; simp [evalList, hp]
        · intro hm; exact absurd (Finset.mem_univ q) hm
    rw [hf] at hsum
    have hz : applyKernel s1List (0 : P0 N).fn q = 0 :=
      Finset.sum_eq_zero fun u _ => evalList_zero _ _
    rw [hz, zero_add] at hsum
    exact hsum
  · rintro ⟨g, rfl⟩
    exact resD1_comp_resD2 g

lemma ker_resD2_eq_range_resJ : LinearMap.ker (resD2 N) = LinearMap.range (resJ N) := by
  ext f
  simp only [LinearMap.mem_ker, LinearMap.mem_range]
  constructor
  · intro hf
    refine ⟨⟨applyKernel s3List f.fn ()⟩, ?_⟩
    apply P0.ext; funext w
    have hfn : (resJ N ⟨applyKernel s3List f.fn ()⟩).fn w =
        applyKernel jListFast (applyKernel s3List f.fn) w := by
      rw [resJ_fn_eq]
    have hsum : applyKernel s2List (resD2 N f).fn w +
        applyKernel jListFast (applyKernel s3List f.fn) w = f.fn w := by
      change applyKernel s2List (applyKernel d2List f.fn) w +
          applyKernel jListFast (applyKernel s3List f.fn) w = f.fn w
      rw [applyKernel_comp, applyKernel_comp]
      unfold applyKernel
      rw [← Finset.sum_add_distrib]
      trans (∑ u : B, evalList [(u, idempB u.val.1)] w (f.fn u))
      · refine Finset.sum_congr rfl fun u _ => ?_
        rw [← evalList_append]
        exact evalList_eq_of_sameParity (List.all_eq_true.mp check_h2 u (mem_allBList u)) w (f.fn u)
      · rw [Finset.sum_eq_single w]
        · simp only [evalList, if_true, add_zero]; exact f.compat w
        · intro u _ hu; simp [evalList, hu]
        · intro hm; exact absurd (Finset.mem_univ w) hm
    rw [hf] at hsum
    have hz : applyKernel s2List (0 : P1 N).fn w = 0 :=
      Finset.sum_eq_zero fun p _ => evalList_zero _ _
    rw [hz, zero_add] at hsum
    rw [hfn]; exact hsum
  · rintro ⟨x, rfl⟩
    exact resD2_comp_resJ x

lemma evalList_map {β M : Type*} [DecidableEq β] [AddCommGroup M] [Module Λ M]
    (φ : N →ₗ[Λ] M) (L : List (β × B)) (y : β) (n : N) :
    φ (evalList L y n) = evalList L y (φ n) := by
  induction L with
  | nil => exact map_zero φ
  | cons a tl ih =>
    simp only [evalList, map_add, ih]
    congr 1; split_ifs
    · exact map_smul φ _ _
    · exact map_zero φ

lemma resμ_nat {M : Type*} [AddCommGroup M] [Module Λ M] [Module (ZMod 2) M] [IsScalarTower (ZMod 2) Λ M]
    (φ : N →ₗ[Λ] M) : φ.comp (resμ N) = (resμ M).comp (P0.map φ) := by
  ext f; change φ (applyKernel μList f.fn ()) = applyKernel μList (fun u => φ (f.fn u)) ()
  unfold applyKernel; rw [map_sum]
  exact Finset.sum_congr rfl fun u _ => evalList_map φ _ _ _

lemma resD1_nat {M : Type*} [AddCommGroup M] [Module Λ M] [Module (ZMod 2) M] [IsScalarTower (ZMod 2) Λ M]
    (φ : N →ₗ[Λ] M) : (P0.map φ).comp (resD1 N) = (resD1 M).comp (P1.map φ) := by
  apply LinearMap.ext; intro f; apply P0.ext; funext w; change φ (applyKernel d1List f.fn w) = applyKernel d1List (fun p => φ (f.fn p)) w
  unfold applyKernel; rw [map_sum]
  exact Finset.sum_congr rfl fun p _ => evalList_map φ _ _ _

lemma resD2_nat {M : Type*} [AddCommGroup M] [Module Λ M] [Module (ZMod 2) M] [IsScalarTower (ZMod 2) Λ M]
    (φ : N →ₗ[Λ] M) : (P1.map φ).comp (resD2 N) = (resD2 M).comp (P0.map φ) := by
  apply LinearMap.ext; intro f; apply P1.ext; funext q; change φ (applyKernel d2List f.fn q) = applyKernel d2List (fun u => φ (f.fn u)) q
  unfold applyKernel; rw [map_sum]
  exact Finset.sum_congr rfl fun u _ => evalList_map φ _ _ _

lemma resJ_nat {M : Type*} [AddCommGroup M] [Module Λ M] [Module (ZMod 2) M] [IsScalarTower (ZMod 2) Λ M]
    (φ : N →ₗ[Λ] M) : (P0.map φ).comp (resJ N) = (resJ M).comp (Twist.map φ) := by
  apply LinearMap.ext; intro x; apply P0.ext; funext u; change φ (basisVec (dualB u) • x.val) = basisVec (dualB u) • φ x.val
  exact map_smul φ _ _

end ResolutionMaps

end BimoduleResolution

section CategoryProj

/-- The category $\mathcal{P}(\Lambda)$ of finite-dimensional projective left $\Lambda$-modules. -/
structure ProjΛ where
  carrier : Type
  [addCommGroup : AddCommGroup carrier]
  [moduleΛ : Module Λ carrier]
  [moduleZ2 : Module (ZMod 2) carrier]
  [tower : IsScalarTower (ZMod 2) Λ carrier]
  [fintype : Fintype carrier]
  [proj : Module.Projective Λ carrier]

instance (P : ProjΛ) : AddCommGroup P.carrier := P.addCommGroup
instance (P : ProjΛ) : Module Λ P.carrier := P.moduleΛ
instance (P : ProjΛ) : Module (ZMod 2) P.carrier := P.moduleZ2
instance (P : ProjΛ) : IsScalarTower (ZMod 2) Λ P.carrier := P.tower
instance (P : ProjΛ) : Fintype P.carrier := P.fintype
instance (P : ProjΛ) : Module.Projective Λ P.carrier := P.proj

namespace ProjΛ

instance : Category.{0} ProjΛ where
  Hom P Q := P.carrier →ₗ[Λ] Q.carrier
  id _ := LinearMap.id
  comp f g := g.comp f
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

def toLin {P Q : ProjΛ} (f : P ⟶ Q) : P.carrier →ₗ[Λ] Q.carrier := f

lemma hom_ext {P Q : ProjΛ} {f g : P ⟶ Q} (h : ∀ x : P.carrier, toLin f x = toLin g x) : f = g :=
  LinearMap.ext h

instance : Preadditive ProjΛ where
  homGroup P Q := inferInstanceAs (AddCommGroup (P.carrier →ₗ[Λ] Q.carrier))
  add_comp P Q R f f' g := hom_ext fun x => map_add (toLin g) (toLin f x) (toLin f' x)
  comp_add P Q R f g g' := hom_ext fun _ => rfl

/-- Zero object of `ProjΛ`. -/
def zeroObj : ProjΛ where
  carrier := PUnit
  addCommGroup := inferInstance
  moduleΛ := inferInstance
  moduleZ2 := inferInstance
  tower := ⟨fun _ _ _ => rfl⟩
  fintype := inferInstance
  proj := Module.Projective.of_lifting_property fun f g _ => ⟨0,
    LinearMap.ext fun x => by
      cases x
      change f (0 : _) = g (0 : PUnit)
      rw [map_zero, map_zero]⟩

instance : HasZeroObject ProjΛ := by
  refine ⟨⟨zeroObj, ?_, ?_⟩⟩
  · intro Q; exact ⟨⟨⟨0⟩, fun f => hom_ext fun x => by cases x; exact map_zero (toLin f)⟩⟩
  · intro Q; exact ⟨⟨⟨0⟩, fun f => hom_ext fun _ => rfl⟩⟩

/-- Every object of `ProjΛ` is injective in the category of left `Λ`-modules. -/
lemma injective (P : ProjΛ) {X Y : Type*} [AddCommGroup X] [Module Λ X] [AddCommGroup Y] [Module Λ Y]
    [Module (ZMod 2) X] [IsScalarTower (ZMod 2) Λ X]
    [Module (ZMod 2) Y] [IsScalarTower (ZMod 2) Λ Y]
    (i : X →ₗ[Λ] Y) (hi : Function.Injective i) (f : X →ₗ[Λ] P.carrier) :
    ∃ g : Y →ₗ[Λ] P.carrier, g.comp i = f := by
  classical
  let π : (P.carrier → Λ) →ₗ[Λ] P.carrier :=
    { toFun := fun c => ∑ p : P.carrier, c p • p
      map_add' := fun c1 c2 => by
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := fun a c => by
        simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply] }
  have hsurj : Function.Surjective π := fun p =>
    ⟨fun q => if q = p then 1 else 0, by
      change (∑ q : P.carrier, (if q = p then (1 : Λ) else 0) • q) = p
      rw [Finset.sum_eq_single p]
      · simp
      · intro q _ hq; simp [hq]
      · intro hm; exact absurd (Finset.mem_univ p) hm⟩
  obtain ⟨s, hs⟩ := Module.projective_lifting_property π LinearMap.id hsurj
  have hcomp : ∀ p : P.carrier, ∃ gp : Y →ₗ[Λ] Λ,
      gp.comp i = (LinearMap.proj p).comp (s.comp f) := fun p =>
    self_injective i hi ((LinearMap.proj p).comp (s.comp f))
  choose gfam hgfam using hcomp
  let G : Y →ₗ[Λ] (P.carrier → Λ) := LinearMap.pi gfam
  refine ⟨π.comp G, ?_⟩
  ext x
  have hGx : G (i x) = s (f x) := by
    funext p
    exact LinearMap.congr_fun (hgfam p) x
  change π (G (i x)) = f x
  rw [hGx]
  exact LinearMap.congr_fun hs (f x)

/-- The Nakayama twist functor `(-)_\nu` on `ProjΛ`. -/
def nuObj (P : ProjΛ) : ProjΛ where
  carrier := Twist P.carrier

def nuFunctor : ProjΛ ⥤ ProjΛ where
  obj P := nuObj P
  map f := Twist.map f
  map_id _ := LinearMap.ext fun _ => rfl
  map_comp _ _ := LinearMap.ext fun _ => rfl

def nuNuIso : nuFunctor ⋙ nuFunctor ≅ 𝟭 ProjΛ :=
  NatIso.ofComponents (fun P =>
    { hom := (Twist.involEquiv (N := P.carrier)).toLinearMap
      inv := (Twist.involEquiv (N := P.carrier)).symm.toLinearMap
      hom_inv_id := LinearMap.ext fun _ => rfl
      inv_hom_id := LinearMap.ext fun _ => rfl })
    (fun _ => LinearMap.ext fun _ => rfl)

/-- `ℤ`-shift on `ProjΛ`: even shifts are identity, odd shifts are `nuFunctor`. -/
def isOddInt (n : ℤ) : Bool := decide (n % 2 ≠ 0)

lemma isOddInt_zero : isOddInt 0 = false := rfl

lemma isOddInt_add (m n : ℤ) : isOddInt (m + n) = xor (isOddInt m) (isOddInt n) := by
  unfold isOddInt
  by_cases hm : m % 2 = 0 <;> by_cases hn : n % 2 = 0
  · have : (m + n) % 2 = 0 := by omega
    simp [hm, hn, this]
  · have : (m + n) % 2 ≠ 0 := by omega
    simp [hm, hn, this]
  · have : (m + n) % 2 ≠ 0 := by omega
    simp [hm, hn, this]
  · have : (m + n) % 2 = 0 := by omega
    simp [hm, hn, this]

def shiftBool : Bool → (ProjΛ ⥤ ProjΛ)
  | false => 𝟭 ProjΛ
  | true => nuFunctor

def shiftAddBool : ∀ (a b : Bool), shiftBool (xor a b) ≅ shiftBool a ⋙ shiftBool b
  | false, false => (Functor.leftUnitor (𝟭 ProjΛ)).symm
  | false, true => (Functor.leftUnitor nuFunctor).symm
  | true, false => (Functor.rightUnitor nuFunctor).symm
  | true, true => nuNuIso.symm

def shiftF (n : ℤ) : ProjΛ ⥤ ProjΛ := shiftBool (isOddInt n)

def shiftAddIso (m n : ℤ) : shiftF (m + n) ≅ shiftF m ⋙ shiftF n :=
  eqToIso (congrArg shiftBool (isOddInt_add m n)) ≪≫ shiftAddBool (isOddInt m) (isOddInt n)

private lemma shiftAddIso_assoc_aux (a b c ab bc abc1 abc2 : Bool)
    (hab : ab = xor a b) (hbc : bc = xor b c) (h1 : abc1 = xor ab c) (h2 : abc2 = xor a bc)
    (h12 : abc1 = abc2) (X : ProjΛ) :
    CategoryStruct.comp
      ((eqToIso (congrArg shiftBool h1) ≪≫ shiftAddBool ab c).hom.app X)
      ((shiftBool c).map ((eqToIso (congrArg shiftBool hab) ≪≫ shiftAddBool a b).hom.app X)) =
    CategoryStruct.comp
      (eqToHom (congrArg (fun d => (shiftBool d).obj X) h12))
      (CategoryStruct.comp
        ((eqToIso (congrArg shiftBool h2) ≪≫ shiftAddBool a bc).hom.app X)
        ((eqToIso (congrArg shiftBool hbc) ≪≫ shiftAddBool b c).hom.app ((shiftBool a).obj X))) := by
  subst hab; subst hbc; subst h1; subst h2
  cases a <;> cases b <;> cases c <;> exact LinearMap.ext fun _ => rfl

private lemma shiftAddIso_zero_add_aux (b0 b z : Bool) (hz : z = false)
    (hb : b0 = b) (h : b0 = xor z b) (X : ProjΛ) :
    (eqToIso (congrArg shiftBool h) ≪≫ shiftAddBool z b).hom.app X =
      CategoryStruct.comp
        (eqToHom (congrArg (fun d => (shiftBool d).obj X) hb))
        ((shiftBool b).map ((eqToIso (congrArg shiftBool hz)).inv.app X)) := by
  subst hz; subst hb
  cases b0 <;> exact LinearMap.ext fun _ => rfl

private lemma shiftAddIso_add_zero_aux (b0 b z : Bool) (hz : z = false)
    (hb : b0 = b) (h : b0 = xor b z) (X : ProjΛ) :
    (eqToIso (congrArg shiftBool h) ≪≫ shiftAddBool b z).hom.app X =
      CategoryStruct.comp
        (eqToHom (congrArg (fun d => (shiftBool d).obj X) hb))
        ((eqToIso (congrArg shiftBool hz)).inv.app ((shiftBool b).obj X)) := by
  subst hz; subst hb
  cases b0 <;> exact LinearMap.ext fun _ => rfl

def shiftMkCore : ShiftMkCore ProjΛ ℤ where
  F := shiftF
  zero := eqToIso (congrArg shiftBool isOddInt_zero)
  add := shiftAddIso
  assoc_hom_app m₁ m₂ m₃ X :=
    shiftAddIso_assoc_aux (isOddInt m₁) (isOddInt m₂) (isOddInt m₃)
      (isOddInt (m₁ + m₂)) (isOddInt (m₂ + m₃)) (isOddInt (m₁ + m₂ + m₃)) (isOddInt (m₁ + (m₂ + m₃)))
      (isOddInt_add m₁ m₂) (isOddInt_add m₂ m₃) (isOddInt_add (m₁ + m₂) m₃) (isOddInt_add m₁ (m₂ + m₃))
      (congrArg isOddInt (add_assoc m₁ m₂ m₃)) X
  zero_add_hom_app n X :=
    shiftAddIso_zero_add_aux (isOddInt (0 + n)) (isOddInt n) (isOddInt 0) isOddInt_zero
      (congrArg isOddInt (zero_add n)) (isOddInt_add 0 n) X
  add_zero_hom_app n X :=
    shiftAddIso_add_zero_aux (isOddInt (n + 0)) (isOddInt n) (isOddInt 0) isOddInt_zero
      (congrArg isOddInt (add_zero n)) (isOddInt_add n 0) X

instance : HasShift ProjΛ ℤ := hasShiftMk ProjΛ ℤ shiftMkCore

instance (n : ℤ) : (shiftFunctor ProjΛ n).Additive where
  map_add {P Q} f g := by
    change (shiftBool (isOddInt n)).map (f + g) =
      (shiftBool (isOddInt n)).map f + (shiftBool (isOddInt n)).map g
    cases isOddInt n <;> exact LinearMap.ext fun _ => rfl

end ProjΛ

end CategoryProj

section ModuleM

lemma mulB_idemp_self (l : Fin 5) : mulB (idempB l) (idempB l) = some (idempB l) :=
  mulB_idemp_left (idempB l)

/-- Indecomposable left projective `Λ e_l`. -/
structure LProj (l : Fin 5) where
  val : Λ
  right_idemp : val * idempΛ l = val

namespace LProj

variable {l : Fin 5}

lemma ext {x y : LProj l} (h : x.val = y.val) : x = y := by
  cases x; cases y; congr

instance : Zero (LProj l) := ⟨⟨0, zero_mul _⟩⟩
instance : Add (LProj l) := ⟨fun x y => ⟨x.val + y.val, by rw [add_mul, x.right_idemp, y.right_idemp]⟩⟩
instance : Neg (LProj l) := ⟨fun x => ⟨-x.val, by rw [neg_mul, x.right_idemp]⟩⟩
instance : Sub (LProj l) := ⟨fun x y => ⟨x.val - y.val, by rw [sub_mul, x.right_idemp, y.right_idemp]⟩⟩

@[simp] lemma val_zero : (0 : LProj l).val = 0 := rfl
@[simp] lemma val_add (x y : LProj l) : (x + y).val = x.val + y.val := rfl

instance : AddCommGroup (LProj l) where
  add_assoc a b c := LProj.ext (add_assoc _ _ _)
  zero_add a := LProj.ext (zero_add _)
  add_zero a := LProj.ext (add_zero _)
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel a := LProj.ext (neg_add_cancel _)
  add_comm a b := LProj.ext (add_comm _ _)
  sub_eq_add_neg a b := LProj.ext (sub_eq_add_neg _ _)

instance : Module (ZMod 2) (LProj l) where
  smul c x := ⟨c • x.val, by rw [smul_mulΛ, x.right_idemp]⟩
  one_smul x := LProj.ext (one_smul _ _)
  mul_smul r s x := LProj.ext (mul_smul _ _ _)
  smul_zero r := LProj.ext (smul_zero _)
  smul_add r x y := LProj.ext (smul_add _ _ _)
  add_smul r s x := LProj.ext (add_smul _ _ _)
  zero_smul x := LProj.ext (zero_smul _ _)

instance : Module Λ (LProj l) where
  smul a x := ⟨a * x.val, by rw [mul_assoc, x.right_idemp]⟩
  one_smul x := LProj.ext (one_mul _)
  mul_smul a b x := LProj.ext (mul_assoc _ _ _)
  smul_zero a := LProj.ext (mul_zero _)
  smul_add a x y := LProj.ext (mul_add _ _ _)
  add_smul a b x := LProj.ext (add_mul _ _ _)
  zero_smul x := LProj.ext (zero_mul _)

instance : IsScalarTower (ZMod 2) Λ (LProj l) where
  smul_assoc c a x := LProj.ext (smul_mulΛ c a x.val)

noncomputable instance : Fintype (LProj l) := by
  classical
  exact Fintype.ofEquiv { a : Λ // a * idempΛ l = a }
    ⟨fun x => ⟨x.1, x.2⟩, fun x => ⟨x.val, x.right_idemp⟩, fun _ => rfl, fun _ => rfl⟩

instance : Module.Projective Λ (LProj l) := by
  let i : LProj l →ₗ[Λ] Λ :=
    { toFun := LProj.val, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  let r : Λ →ₗ[Λ] LProj l :=
    { toFun := fun a => ⟨a * idempΛ l, by
        rw [mul_assoc, idempΛ, basisVec_mul_basisVec, mulB_idemp_self l]⟩
      map_add' := fun a b => LProj.ext (add_mul a b _)
      map_smul' := fun a b => LProj.ext (mul_assoc a b _) }
  exact Module.Projective.of_split i r (LinearMap.ext fun x => LProj.ext x.right_idemp)

def gen (l : Fin 5) : LProj l :=
  ⟨idempΛ l, by rw [idempΛ, basisVec_mul_basisVec, mulB_idemp_self l]⟩

def ofBasis (u : B) (h : u.val.1 = l) : LProj l :=
  ⟨basisVec u, by
    rw [idempΛ, basisVec_mul_basisVec]
    have hm : mulB u (idempB l) = some u := by rw [← h]; exact mulB_idemp_right u
    rw [hm]⟩

lemma smul_gen (x : LProj l) : x.val • gen l = x := LProj.ext x.right_idemp

end LProj

abbrev P02 := LProj 0 × LProj 2
abbrev P42 := LProj 4 × LProj 2

noncomputable abbrev P02Obj : ProjΛ := ⟨P02⟩
noncomputable abbrev P42Obj : ProjΛ := ⟨P42⟩

lemma nuΛ_idemp (l : Fin 5) : nuΛ (idempΛ l) = idempΛ ⟨4 - l.val, by omega⟩ := by
  rw [idempΛ, nuΛ_basisVec, idempΛ]
  congr 1; apply Subtype.ext; refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> (apply Fin.ext; simp [nuB, idempB])

def nuP02 : Twist P02 ≃ₗ[Λ] P42 where
  toFun x :=
    (⟨nuΛ x.val.1.val, by
      have h := congrArg nuΛ x.val.1.right_idemp
      rw [map_mul, nuΛ_idemp] at h; exact h⟩,
     ⟨nuΛ x.val.2.val, by
      have h := congrArg nuΛ x.val.2.right_idemp
      rw [map_mul, nuΛ_idemp] at h; exact h⟩)
  invFun y :=
    ⟨(⟨nuΛ y.1.val, by
      have h := congrArg nuΛ y.1.right_idemp
      rw [map_mul, nuΛ_idemp] at h; exact h⟩,
      ⟨nuΛ y.2.val, by
      have h := congrArg nuΛ y.2.right_idemp
      rw [map_mul, nuΛ_idemp] at h; exact h⟩)⟩
  left_inv x := by
    apply Twist.ext
    exact Prod.ext (LProj.ext (by change nuΛ (nuΛ x.val.1.val) = x.val.1.val; apply Λ.ext; funext w; simp [nuΛ, nuB_invol]))
      (LProj.ext (by change nuΛ (nuΛ x.val.2.val) = x.val.2.val; apply Λ.ext; funext w; simp [nuΛ, nuB_invol]))
  right_inv y := Prod.ext
    (LProj.ext (by change nuΛ (nuΛ y.1.val) = y.1.val; apply Λ.ext; funext w; simp [nuΛ, nuB_invol]))
    (LProj.ext (by change nuΛ (nuΛ y.2.val) = y.2.val; apply Λ.ext; funext w; simp [nuΛ, nuB_invol]))
  map_add' x y := Prod.ext (LProj.ext (map_add nuΛ _ _)) (LProj.ext (map_add nuΛ _ _))
  map_smul' a x := Prod.ext
    (LProj.ext (by
      change nuΛ (nuΛ a * x.val.1.val) = a * nuΛ x.val.1.val
      rw [map_mul]; have h : nuΛ (nuΛ a) = a := by apply Λ.ext; funext w; simp [nuΛ, nuB_invol]
      rw [h]))
    (LProj.ext (by
      change nuΛ (nuΛ a * x.val.2.val) = a * nuΛ x.val.2.val
      rw [map_mul]; have h : nuΛ (nuΛ a) = a := by apply Λ.ext; funext w; simp [nuΛ, nuB_invol]
      rw [h]))

def nuP42 : Twist P42 ≃ₗ[Λ] P02 where
  toFun y :=
    (⟨nuΛ y.val.1.val, by
      have h := congrArg nuΛ y.val.1.right_idemp
      rw [map_mul, nuΛ_idemp] at h; exact h⟩,
     ⟨nuΛ y.val.2.val, by
      have h := congrArg nuΛ y.val.2.right_idemp
      rw [map_mul, nuΛ_idemp] at h; exact h⟩)
  invFun x :=
    ⟨(⟨nuΛ x.1.val, by
      have h := congrArg nuΛ x.1.right_idemp
      rw [map_mul, nuΛ_idemp] at h; exact h⟩,
      ⟨nuΛ x.2.val, by
      have h := congrArg nuΛ x.2.right_idemp
      rw [map_mul, nuΛ_idemp] at h; exact h⟩)⟩
  left_inv y := by
    apply Twist.ext
    exact Prod.ext (LProj.ext (by change nuΛ (nuΛ y.val.1.val) = y.val.1.val; apply Λ.ext; funext w; simp [nuΛ, nuB_invol]))
      (LProj.ext (by change nuΛ (nuΛ y.val.2.val) = y.val.2.val; apply Λ.ext; funext w; simp [nuΛ, nuB_invol]))
  right_inv x := Prod.ext
    (LProj.ext (by change nuΛ (nuΛ x.1.val) = x.1.val; apply Λ.ext; funext w; simp [nuΛ, nuB_invol]))
    (LProj.ext (by change nuΛ (nuΛ x.2.val) = x.2.val; apply Λ.ext; funext w; simp [nuΛ, nuB_invol]))
  map_add' x y := Prod.ext (LProj.ext (map_add nuΛ _ _)) (LProj.ext (map_add nuΛ _ _))
  map_smul' a x := Prod.ext
    (LProj.ext (by
      change nuΛ (nuΛ a * x.val.1.val) = a * nuΛ x.val.1.val
      rw [map_mul]; have h : nuΛ (nuΛ a) = a := by apply Λ.ext; funext w; simp [nuΛ, nuB_invol]
      rw [h]))
    (LProj.ext (by
      change nuΛ (nuΛ a * x.val.2.val) = a * nuΛ x.val.2.val
      rw [map_mul]; have h : nuΛ (nuΛ a) = a := by apply Λ.ext; funext w; simp [nuΛ, nuB_invol]
      rw [h]))

/-- Frobenius trace on `Hom_Λ(P02, P42)` and `Hom_Λ(P42, P02)`. -/
def trPhiP02 (T : P02 →ₗ[Λ] P42) : ZMod 2 :=
  phiΛ (T (LProj.gen 0, 0)).1.val + phiΛ (T (0, LProj.gen 2)).2.val

def trPhiP42 (T : P42 →ₗ[Λ] P02) : ZMod 2 :=
  phiΛ (T (LProj.gen 4, 0)).1.val + phiΛ (T (0, LProj.gen 2)).2.val

lemma trPhiP02_add (T1 T2 : P02 →ₗ[Λ] P42) : trPhiP02 (T1 + T2) = trPhiP02 T1 + trPhiP02 T2 := by
  unfold trPhiP02; simp only [LinearMap.add_apply, Prod.fst_add, Prod.snd_add, LProj.val_add, map_add]; ring

lemma trPhiP42_add (T1 T2 : P42 →ₗ[Λ] P02) : trPhiP42 (T1 + T2) = trPhiP42 T1 + trPhiP42 T2 := by
  unfold trPhiP42; simp only [LinearMap.add_apply, Prod.fst_add, Prod.snd_add, LProj.val_add, map_add]; ring

lemma trPhiP02_zero : trPhiP02 0 = 0 := by
  unfold trPhiP02; simp only [LinearMap.zero_apply, Prod.fst_zero, Prod.snd_zero, LProj.val_zero, map_zero, add_zero]
lemma trPhiP42_zero : trPhiP42 0 = 0 := by
  unfold trPhiP42; simp only [LinearMap.zero_apply, Prod.fst_zero, Prod.snd_zero, LProj.val_zero, map_zero, add_zero]

private lemma p42_decomp (x : P42) :
    x = x.1.val • (LProj.gen 4, (0 : LProj 2)) + x.2.val • ((0 : LProj 4), LProj.gen 2) := by
  refine Prod.ext ?_ ?_
  · apply LProj.ext
    change x.1.val = x.1.val * idempΛ 4 + x.2.val * 0
    rw [mul_zero, add_zero, x.1.right_idemp]
  · apply LProj.ext
    change x.2.val = x.1.val * 0 + x.2.val * idempΛ 2
    rw [mul_zero, zero_add, x.2.right_idemp]

private lemma p02_decomp (x : P02) :
    x = x.1.val • (LProj.gen 0, (0 : LProj 2)) + x.2.val • ((0 : LProj 0), LProj.gen 2) := by
  refine Prod.ext ?_ ?_
  · apply LProj.ext
    change x.1.val = x.1.val * idempΛ 0 + x.2.val * 0
    rw [mul_zero, add_zero, x.1.right_idemp]
  · apply LProj.ext
    change x.2.val = x.1.val * 0 + x.2.val * idempΛ 2
    rw [mul_zero, zero_add, x.2.right_idemp]

lemma trPhi_adj_02 {Y : Type*} [AddCommGroup Y] [Module Λ Y]
    (α : P02 →ₗ[Λ] P42) (u : P42 →ₗ[Λ] Y) (g : Y →ₗ[Λ] P42) :
    let β : P42 →ₗ[Λ] P02 := nuP42.toLinearMap.comp ((Twist.map α).comp nuP02.symm.toLinearMap)
    trPhiP02 (g.comp (u.comp α)) = trPhiP42 (β.comp (g.comp u)) := by
  intro β
  let T : P42 →ₗ[Λ] P42 := g.comp u
  have hα0 := p42_decomp (α (LProj.gen 0, 0))
  have hα2 := p42_decomp (α (0, LProj.gen 2))
  have hT4 := p42_decomp (T (LProj.gen 4, 0))
  have hT2 := p42_decomp (T (0, LProj.gen 2))
  have hβ4 : (β (LProj.gen 4, 0)).1.val = nuΛ (α (LProj.gen 0, 0)).1.val ∧
      (β (LProj.gen 4, 0)).2.val = nuΛ (α (LProj.gen 0, 0)).2.val := by
    have h0 : nuP02.symm (LProj.gen 4, 0) = ⟨(LProj.gen 0, 0)⟩ :=
      Twist.ext (Prod.ext (LProj.ext (nuΛ_idemp 4)) (LProj.ext (map_zero nuΛ)))
    simp only [β, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, h0, Twist.map, nuP42]
    exact ⟨rfl, rfl⟩
  have hβ2 : (β (0, LProj.gen 2)).1.val = nuΛ (α (0, LProj.gen 2)).1.val ∧
      (β (0, LProj.gen 2)).2.val = nuΛ (α (0, LProj.gen 2)).2.val := by
    have h0 : nuP02.symm (0, LProj.gen 2) = ⟨(0, LProj.gen 2)⟩ :=
      Twist.ext (Prod.ext (LProj.ext (map_zero nuΛ)) (LProj.ext (nuΛ_idemp 2)))
    simp only [β, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, h0, Twist.map, nuP42]
    exact ⟨rfl, rfl⟩
  have hTa0 : T (α (LProj.gen 0, 0)) =
      (α (LProj.gen 0, 0)).1.val • T (LProj.gen 4, 0) + (α (LProj.gen 0, 0)).2.val • T (0, LProj.gen 2) := by
    conv_lhs => rw [hα0]
    rw [map_add, map_smul, map_smul]
  have hTa2 : T (α (0, LProj.gen 2)) =
      (α (0, LProj.gen 2)).1.val • T (LProj.gen 4, 0) + (α (0, LProj.gen 2)).2.val • T (0, LProj.gen 2) := by
    conv_lhs => rw [hα2]
    rw [map_add, map_smul, map_smul]
  have hbT4 : β (T (LProj.gen 4, 0)) =
      (T (LProj.gen 4, 0)).1.val • β (LProj.gen 4, 0) + (T (LProj.gen 4, 0)).2.val • β (0, LProj.gen 2) := by
    conv_lhs => rw [hT4]
    rw [map_add, map_smul, map_smul]
  have hbT2 : β (T (0, LProj.gen 2)) =
      (T (0, LProj.gen 2)).1.val • β (LProj.gen 4, 0) + (T (0, LProj.gen 2)).2.val • β (0, LProj.gen 2) := by
    conv_lhs => rw [hT2]
    rw [map_add, map_smul, map_smul]
  change phiΛ (T (α (LProj.gen 0, 0))).1.val + phiΛ (T (α (0, LProj.gen 2))).2.val =
    phiΛ (β (T (LProj.gen 4, 0))).1.val + phiΛ (β (T (0, LProj.gen 2))).2.val
  rw [hTa0, hTa2, hbT4, hbT2]
  change phiΛ ((α (LProj.gen 0, 0)).1.val * (T (LProj.gen 4, 0)).1.val +
      (α (LProj.gen 0, 0)).2.val * (T (0, LProj.gen 2)).1.val) +
    phiΛ ((α (0, LProj.gen 2)).1.val * (T (LProj.gen 4, 0)).2.val +
      (α (0, LProj.gen 2)).2.val * (T (0, LProj.gen 2)).2.val) =
    phiΛ ((T (LProj.gen 4, 0)).1.val * (β (LProj.gen 4, 0)).1.val +
      (T (LProj.gen 4, 0)).2.val * (β (0, LProj.gen 2)).1.val) +
    phiΛ ((T (0, LProj.gen 2)).1.val * (β (LProj.gen 4, 0)).2.val +
      (T (0, LProj.gen 2)).2.val * (β (0, LProj.gen 2)).2.val)
  rw [hβ4.1, hβ4.2, hβ2.1, hβ2.2]
  simp only [map_add]
  rw [phiΛ_comm (α (LProj.gen 0, 0)).1.val (T (LProj.gen 4, 0)).1.val,
      phiΛ_comm (α (LProj.gen 0, 0)).2.val (T (0, LProj.gen 2)).1.val,
      phiΛ_comm (α (0, LProj.gen 2)).1.val (T (LProj.gen 4, 0)).2.val,
      phiΛ_comm (α (0, LProj.gen 2)).2.val (T (0, LProj.gen 2)).2.val]
  ring

/-- Non-degeneracy of the Frobenius pairing `Hom_Λ(P02, Y) × Hom_Λ(Y, P42) → ZMod 2`. -/
lemma trPhiP02_nondeg_left {Y : Type*} [AddCommGroup Y] [Module Λ Y]
    [Module (ZMod 2) Y] [IsScalarTower (ZMod 2) Λ Y]
    (u : P02 →ₗ[Λ] Y) (hu : ∀ v : Y →ₗ[Λ] P42, trPhiP02 (v.comp u) = 0) : u = 0 := by
  classical
  have hzero : ∀ (y : Y) (l : Fin 5), idempΛ l • y = y →
      (∀ f : Y →ₗ[Λ] LProj ⟨4 - l.val, by omega⟩, phiΛ (f y).val = 0) → y = 0 := by
    intro y l hyl hf
    by_contra hne
    let incl : (ZMod 2) →ₗ[ZMod 2] Y :=
      { toFun := fun c => c • y, map_add' := fun a b => add_smul a b y, map_smul' := fun a b => mul_smul a b y }
    have hinj : Function.Injective incl := by
      intro a b hab
      have hsub : (a - b) • y = 0 := by simpa [incl, sub_smul] using sub_eq_zero.mpr hab
      by_contra hneab
      have h1 : a - b = 1 := by
        have := sub_ne_zero.mpr hneab
        fin_cases a <;> fin_cases b <;> simp_all
      rw [h1, one_smul] at hsub
      exact hne hsub
    obtain ⟨lam, hlam⟩ := incl.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hinj)
    have hlamy : lam y = 1 := by
      have := LinearMap.congr_fun hlam 1
      simpa [incl] using this
    let gFun : Y → Λ := fun z => ⟨fun w => lam (basisVec (nuB (dualB w)) • z)⟩
    have hbg : ∀ (b : Λ) (z : Y), phiΛ (b * gFun z) = lam (b • z) := by
      intro b z
      have hb := eq_sum_basisVec b
      conv_lhs => rw [hb]
      conv_rhs => rw [hb]
      rw [Finset.sum_mul, map_sum]
      have hsm : (∑ w : B, b.coeff w • basisVec w) • z = ∑ w : B, (b.coeff w • basisVec w) • z :=
        Finset.sum_smul ..
      rw [hsm, map_sum]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [smul_mulΛ, smul_assoc, map_smul, map_smul]
      refine congrArg (b.coeff v • ·) ?_
      rw [phiΛ_comm, nuΛ_basisVec]
      have hex : ∃ u0 : B, dualB u0 = nuB v := by
        have bv := B_bounds v
        refine ⟨⟨(⟨4 - v.val.2.1.val, by omega⟩, v.val.1,
          ⟨v.val.2.1.val - v.val.2.2.val, by omega⟩), by rw [valid_iff]; dsimp; omega⟩, ?_⟩
        apply Subtype.ext; refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> (apply Fin.ext; simp [dualB, nuB]; try omega)
      obtain ⟨u0, hu0⟩ := hex
      rw [← hu0, phiΛ_mul_dual]
      show lam (basisVec (nuB (dualB u0)) • z) = lam (basisVec v • z)
      rw [hu0, nuB_invol]
    let gLin : Y →ₗ[Λ] Λ :=
      { toFun := gFun
        map_add' := fun z1 z2 => by
          apply Λ.ext; funext w; change lam (basisVec (nuB (dualB w)) • (z1 + z2)) = _
          rw [smul_add, map_add]; rfl
        map_smul' := fun a z => by
          apply Λ.ext; funext w
          change (gFun (a • z)).coeff w = (a * gFun z).coeff w
          have hstep : (a * gFun z).coeff w = phiΛ (basisVec (nuB (dualB w)) * (a * gFun z)) := by
            rw [← phiΛ_mul_dual (a * gFun z) w, phiΛ_comm (basisVec (nuB (dualB w))) (a * gFun z),
              nuΛ_basisVec, nuB_invol]
          rw [hstep, ← mul_assoc, hbg (basisVec (nuB (dualB w)) * a) z, mul_smul] }
    let fProj : Y →ₗ[Λ] LProj ⟨4 - l.val, by omega⟩ :=
      { toFun := fun z => ⟨gLin z * idempΛ ⟨4 - l.val, by omega⟩, by
          rw [mul_assoc, idempΛ, basisVec_mul_basisVec, mulB_idemp_self]⟩
        map_add' := fun z1 z2 => LProj.ext (by
          change gLin (z1 + z2) * idempΛ _ = gLin z1 * idempΛ _ + gLin z2 * idempΛ _
          rw [map_add, add_mul])
        map_smul' := fun a z => LProj.ext (by
          change gLin (a • z) * idempΛ _ = a * (gLin z * idempΛ _)
          rw [map_smul, smul_eq_mul, mul_assoc]) }
    have h0 := hf fProj
    have hphi : phiΛ (fProj y).val = 1 := by
      change phiΛ (gFun y * idempΛ ⟨4 - l.val, by omega⟩) = 1
      rw [← nuΛ_idemp l, ← phiΛ_comm (idempΛ l) (gFun y), hbg (idempΛ l) y, hyl, hlamy]
    rw [hphi] at h0
    exact one_ne_zero h0
  have h1 : u (LProj.gen 0, 0) = 0 := by
    apply hzero (u (LProj.gen 0, 0)) 0
    · have hs : idempΛ 0 • (LProj.gen 0, (0 : LProj 2)) = (LProj.gen 0, 0) := by
        rw [Prod.smul_mk, smul_zero]
        refine Prod.ext (LProj.ext ?_) rfl
        change idempΛ 0 * idempΛ 0 = idempΛ 0
        rw [idempΛ, basisVec_mul_basisVec, mulB_idemp_self]
      rw [← map_smul, hs]
    · intro f
      let v : Y →ₗ[Λ] P42 :=
        { toFun := fun z => (f z, 0)
          map_add' := fun z1 z2 => Prod.ext (map_add f z1 z2) (add_zero 0).symm
          map_smul' := fun a z => Prod.ext (map_smul f a z) (smul_zero a).symm }
      have htr := hu v
      change phiΛ (f (u (LProj.gen 0, 0))).val + phiΛ (0 : LProj 2).val = 0 at htr
      rw [LProj.val_zero, map_zero, add_zero] at htr
      exact htr
  have h2 : u (0, LProj.gen 2) = 0 := by
    apply hzero (u (0, LProj.gen 2)) 2
    · have hs : idempΛ 2 • ((0 : LProj 0), LProj.gen 2) = (0, LProj.gen 2) := by
        rw [Prod.smul_mk, smul_zero]
        refine Prod.ext rfl (LProj.ext ?_)
        change idempΛ 2 * idempΛ 2 = idempΛ 2
        rw [idempΛ, basisVec_mul_basisVec, mulB_idemp_self]
      rw [← map_smul, hs]
    · intro f
      let v : Y →ₗ[Λ] P42 :=
        { toFun := fun z => (0, f z)
          map_add' := fun z1 z2 => Prod.ext (add_zero 0).symm (map_add f z1 z2)
          map_smul' := fun a z => Prod.ext (smul_zero a).symm (map_smul f a z) }
      have htr := hu v
      change phiΛ (0 : LProj 4).val + phiΛ (f (u (0, LProj.gen 2))).val = 0 at htr
      rw [LProj.val_zero, map_zero, zero_add] at htr
      exact htr
  apply LinearMap.ext; rintro ⟨a, b⟩
  rw [p02_decomp (a, b), map_add, map_smul, map_smul, h1, h2, smul_zero, smul_zero, add_zero]
  rfl

/-- Explicit 7-dimensional 2-periodic left `Λ`-module `M`. -/
structure ModM where
  vec : Fin 7 → ZMod 2
  deriving DecidableEq

lemma ModM.ext {a b : ModM} (h : a.vec = b.vec) : a = b := by cases a; cases b; congr

namespace ModM

instance : Zero ModM := ⟨⟨0⟩⟩
instance : Add ModM := ⟨fun x y => ⟨x.vec + y.vec⟩⟩
instance : Neg ModM := ⟨fun x => ⟨-x.vec⟩⟩
instance : Sub ModM := ⟨fun x y => ⟨x.vec - y.vec⟩⟩
instance : SMul (ZMod 2) ModM := ⟨fun c x => ⟨c • x.vec⟩⟩

@[simp] lemma vec_zero (i : Fin 7) : (0 : ModM).vec i = 0 := rfl
@[simp] lemma vec_add (x y : ModM) (i : Fin 7) : (x + y).vec i = x.vec i + y.vec i := rfl
@[simp] lemma vec_sub (x y : ModM) (i : Fin 7) : (x - y).vec i = x.vec i - y.vec i := rfl
@[simp] lemma vec_smul (c : ZMod 2) (x : ModM) (i : Fin 7) : (c • x).vec i = c * x.vec i := rfl

instance : AddCommGroup ModM where
  add_assoc a b c := by apply ModM.ext; funext i; exact add_assoc _ _ _
  zero_add a := by apply ModM.ext; funext i; exact zero_add _
  add_zero a := by apply ModM.ext; funext i; exact add_zero _
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel a := by apply ModM.ext; funext i; exact neg_add_cancel (a.vec i)
  add_comm a b := by apply ModM.ext; funext i; exact add_comm _ _
  sub_eq_add_neg a b := by apply ModM.ext; funext i; exact sub_eq_add_neg _ _

instance : Module (ZMod 2) ModM where
  one_smul x := by apply ModM.ext; funext i; exact one_mul (x.vec i)
  mul_smul r s x := by apply ModM.ext; funext i; exact mul_assoc r s (x.vec i)
  smul_zero r := by apply ModM.ext; funext i; exact mul_zero r
  smul_add r x y := by apply ModM.ext; funext i; exact mul_add r (x.vec i) (y.vec i)
  add_smul r s x := by apply ModM.ext; funext i; exact add_mul r s (x.vec i)
  zero_smul x := by apply ModM.ext; funext i; exact zero_mul (x.vec i)

instance : Fintype ModM :=
  Fintype.ofEquiv (Fin 7 → ZMod 2) ⟨ModM.mk, ModM.vec, fun _ => rfl, fun _ => rfl⟩

def actList (u : B) : List (Fin 7 × Fin 7) :=
  match u.val.1.val, u.val.2.1.val, u.val.2.2.val with
  | 0, 0, 0 => [(0, 0), (1, 1)]
  | 0, 1, 1 => [(2, 0), (3, 0)]
  | 0, 2, 2 => [(5, 0)]
  | 1, 0, 0 => [(1, 2), (1, 3)]
  | 1, 1, 0 => [(2, 2), (3, 3)]
  | 1, 2, 1 => [(5, 2)]
  | 2, 0, 0 => [(1, 4)]
  | 2, 1, 0 => [(2, 4)]
  | 2, 2, 0 => [(4, 4), (5, 5)]
  | 2, 2, 1 => [(5, 4)]
  | 2, 3, 1 => [(6, 4)]
  | 3, 2, 0 => [(5, 6)]
  | 3, 3, 0 => [(6, 6)]
  | _, _, _ => []

def matParity (L : List (Fin 7 × Fin 7)) (r c : Fin 7) : Bool :=
  L.foldr (fun p acc => if p.1 = r ∧ p.2 = c then !acc else acc) false

def actMatBool (u : B) (r c : Fin 7) : Bool := matParity (actList u) r c

def actMat (u : B) (r c : Fin 7) : ZMod 2 := if actMatBool u r c then 1 else 0

def actMB (u : B) (v : Fin 7 → ZMod 2) (r : Fin 7) : ZMod 2 :=
  ∑ c : Fin 7, actMat u r c * v c

lemma actMB_eq_sum (u : B) (v : Fin 7 → ZMod 2) (r : Fin 7) :
    actMB u v r = ∑ c : Fin 7, actMat u r c * v c := rfl

def compActList (L1 L2 : List (Fin 7 × Fin 7)) : List (Fin 7 × Fin 7) :=
  L1.flatMap fun p1 => L2.filterMap fun p2 => if p1.2 = p2.1 then some (p1.1, p2.2) else none

def sameMatParity (L1 L2 : List (Fin 7 × Fin 7)) : Bool :=
  (L1 ++ L2).all fun p => matParity L1 p.1 p.2 == matParity L2 p.1 p.2

lemma actList_mul_check :
    allBList.all (fun u => allBList.all (fun v =>
      sameMatParity (compActList (actList u) (actList v))
        (match mulB u v with | some w => actList w | none => []))) = true := by
  decide

lemma matParity_of_not_mem {L : List (Fin 7 × Fin 7)} {r c : Fin 7} (h : (r, c) ∉ L) :
    matParity L r c = false := by
  induction L with
  | nil => rfl
  | cons a tl ih =>
    simp only [List.mem_cons, not_or] at h
    have hne : ¬ (a.1 = r ∧ a.2 = c) := fun ⟨h1, h2⟩ => h.1 (Prod.ext h1.symm h2.symm)
    simp only [matParity, List.foldr_cons, if_neg hne]
    exact ih h.2

lemma sameMatParity_iff (L1 L2 : List (Fin 7 × Fin 7)) :
    sameMatParity L1 L2 = true → ∀ r c, matParity L1 r c = matParity L2 r c := by
  intro h r c
  by_cases hm : (r, c) ∈ L1 ++ L2
  · exact beq_iff_eq.mp (List.all_eq_true.mp h (r, c) hm)
  · simp only [List.mem_append, not_or] at hm
    rw [matParity_of_not_mem hm.1, matParity_of_not_mem hm.2]

lemma zmod2_matParity_eq_sum (L : List (Fin 7 × Fin 7)) (r c : Fin 7) :
    (if matParity L r c then (1 : ZMod 2) else 0) =
      (L.map fun p => if p.1 = r ∧ p.2 = c then (1 : ZMod 2) else 0).sum := by
  induction L with
  | nil => rfl
  | cons a tl ih =>
    simp only [List.map_cons, List.sum_cons, ← ih]
    by_cases h : a.1 = r ∧ a.2 = c
    · have hp : matParity (a :: tl) r c = !(matParity tl r c) := by simp [matParity, h]
      rw [hp, if_pos h]
      cases matParity tl r c <;> decide
    · have hp : matParity (a :: tl) r c = matParity tl r c := by simp [matParity, h]
      rw [hp, if_neg h, zero_add]

lemma list_sum_compActList (L1 L2 : List (Fin 7 × Fin 7)) (r c : Fin 7) :
    ((compActList L1 L2).map fun p => if p.1 = r ∧ p.2 = c then (1 : ZMod 2) else 0).sum =
      ∑ k : Fin 7, (if matParity L1 r k then (1 : ZMod 2) else 0) *
        (if matParity L2 k c then (1 : ZMod 2) else 0) := by
  simp_rw [zmod2_matParity_eq_sum]
  induction L1 with
  | nil => simp [compActList]
  | cons a tl ih =>
    simp only [compActList, List.flatMap_cons, List.map_append, List.sum_append,
      List.map_cons, List.sum_cons, add_mul, Finset.sum_add_distrib]
    change ((L2.filterMap fun p2 => if a.2 = p2.1 then some (a.1, p2.2) else none).map
      fun p => if p.1 = r ∧ p.2 = c then (1 : ZMod 2) else 0).sum +
      ((compActList tl L2).map fun p => if p.1 = r ∧ p.2 = c then (1 : ZMod 2) else 0).sum = _
    rw [ih]
    refine congrArg (· + _) ?_
    rw [Finset.sum_eq_single a.2]
    · by_cases har : a.1 = r
      · subst har; simp only [true_and, if_true, one_mul]
        clear ih
        induction L2 with
        | nil => rfl
        | cons b tl2 ih2 =>
          simp only [List.filterMap_cons, List.map_cons, List.sum_cons]
          by_cases hab : a.2 = b.1
          · rw [if_pos hab, List.map_cons, List.sum_cons, ih2]
            simp [hab.symm]
          · rw [if_neg hab, ih2]
            have hne : ¬ (b.1 = a.2 ∧ b.2 = c) := fun h => hab h.1.symm
            simp [hne]
      · simp only [har, false_and, if_false, zero_mul]
        clear ih
        induction L2 with
        | nil => rfl
        | cons b tl2 ih2 =>
          simp only [List.filterMap_cons]
          by_cases hab : a.2 = b.1
          · rw [if_pos hab, List.map_cons, List.sum_cons, ih2]; simp [har]
          · rw [if_neg hab, ih2]
    · intro k _ hk; simp [Ne.symm hk]
    · intro hm; exact absurd (Finset.mem_univ a.2) hm

lemma actMat_mul (u v : B) (r c : Fin 7) :
    (∑ k : Fin 7, actMat u r k * actMat v k c) =
      match mulB u v with | some w => actMat w r c | none => 0 := by
  unfold actMat actMatBool
  rw [← list_sum_compActList, ← zmod2_matParity_eq_sum]
  have hchk := sameMatParity_iff _ _ (List.all_eq_true.mp (List.all_eq_true.mp actList_mul_check u (mem_allBList u)) v (mem_allBList v)) r c
  rw [hchk]
  cases mulB u v with
  | none => rfl
  | some w => rfl

lemma actMat_one :
    (List.finRange 7).all (fun r => (List.finRange 7).all (fun c =>
      (∑ i : Fin 5, actMat (idempB i) r c) == (if r = c then (1 : ZMod 2) else 0))) = true := by
  decide

def smulM (a : Λ) (x : ModM) : ModM :=
  ⟨fun r => ∑ u : B, a.coeff u * actMB u x.vec r⟩

instance : Module Λ ModM where
  smul := smulM
  one_smul x := by
    apply ModM.ext; funext r
    change (∑ u : B, oneΛ.coeff u * actMB u x.vec r) = x.vec r
    have h1 : (∑ u : B, oneΛ.coeff u * actMB u x.vec r) =
        ∑ i : Fin 5, actMB (idempB i) x.vec r := by
      have hsplit : ∀ u : B, oneΛ.coeff u * actMB u x.vec r =
          ∑ i : Fin 5, if u = idempB i then actMB (idempB i) x.vec r else 0 := by
        intro u; simp only [oneΛ]
        by_cases h : ∃ i : Fin 5, u = idempB i
        · obtain ⟨i0, hi0⟩ := h
          rw [if_pos ⟨i0, hi0⟩, one_mul, Finset.sum_eq_single i0]
          · simp [hi0]
          · intro i _ hi
            have hne : u ≠ idempB i := by rw [hi0]; intro heq; exact hi (congrArg (fun z : B => z.val.1) heq).symm
            simp [hne]
          · intro hm; exact absurd (Finset.mem_univ i0) hm
        · rw [if_neg h, zero_mul]; symm
          exact Finset.sum_eq_zero fun i _ => if_neg (fun heq => h ⟨i, heq⟩)
      simp_rw [hsplit]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_eq_single (idempB i)]
      · simp
      · intro u _ hu; simp [hu]
      · intro hm; exact absurd (Finset.mem_univ _) hm
    rw [h1]
    simp_rw [actMB_eq_sum]
    rw [Finset.sum_comm]
    have hchk : ∀ c : Fin 7, (∑ i : Fin 5, actMat (idempB i) r c) = if r = c then 1 else 0 := fun c =>
      beq_iff_eq.mp (List.all_eq_true.mp (List.all_eq_true.mp actMat_one r (List.mem_finRange r)) c (List.mem_finRange c))
    trans (∑ c : Fin 7, (∑ i : Fin 5, actMat (idempB i) r c) * x.vec c)
    · exact Finset.sum_congr rfl fun c _ => (Finset.sum_mul ..).symm
    · simp_rw [hchk]
      rw [Finset.sum_eq_single r]
      · simp
      · intro c _ hc; simp [Ne.symm hc]
      · intro hm; exact absurd (Finset.mem_univ r) hm
  mul_smul a b x := by
    apply ModM.ext; funext r
    change (∑ w : B, (a * b).coeff w * actMB w x.vec r) =
      ∑ u : B, a.coeff u * actMB u (fun k => ∑ v : B, b.coeff v * actMB v x.vec k) r
    have hL : (∑ w : B, (a * b).coeff w * actMB w x.vec r) =
        ∑ u : B, ∑ v : B, ∑ c : Fin 7,
          a.coeff u * b.coeff v * ((match mulB u v with | some w => actMat w r c | none => 0) * x.vec c) := by
      trans (∑ w : B, ∑ c : Fin 7, ∑ u : B, ∑ v : B,
          if mulB u v = some w then a.coeff u * b.coeff v * (actMat w r c * x.vec c) else 0)
      · refine Finset.sum_congr rfl fun w _ => ?_
        rw [actMB_eq_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [mul_coeff, Finset.sum_mul]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun v _ => ?_
        split_ifs <;> simp
      · rw [Finset.sum_comm]
        trans (∑ c : Fin 7, ∑ u : B, ∑ v : B, ∑ w : B,
            if mulB u v = some w then a.coeff u * b.coeff v * (actMat w r c * x.vec c) else 0)
        · refine Finset.sum_congr rfl fun c _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun u _ => ?_
          rw [Finset.sum_comm]
        · rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun u _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun v _ => ?_
          refine Finset.sum_congr rfl fun c _ => ?_
          cases hm : mulB u v with
          | none => simp
          | some w0 =>
            rw [Finset.sum_eq_single w0]
            · simp
            · intro w _ hw; simp [Ne.symm hw]
            · intro h; exact absurd (Finset.mem_univ w0) h
    have hR : (∑ u : B, a.coeff u * actMB u (fun k => ∑ v : B, b.coeff v * actMB v x.vec k) r) =
        ∑ u : B, ∑ v : B, ∑ c : Fin 7,
          a.coeff u * b.coeff v * ((∑ k : Fin 7, actMat u r k * actMat v k c) * x.vec c) := by
      refine Finset.sum_congr rfl fun u _ => ?_
      simp_rw [actMB_eq_sum, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => by ring
    rw [hL, hR]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun c _ => ?_
    rw [actMat_mul]
  smul_zero a := by
    apply ModM.ext; funext r; change (∑ u : B, a.coeff u * actMB u 0 r) = 0
    exact Finset.sum_eq_zero fun u _ => by rw [actMB_eq_sum]; simp
  smul_add a x y := by
    apply ModM.ext; funext r
    change (∑ u : B, a.coeff u * actMB u (x.vec + y.vec) r) =
      (∑ u : B, a.coeff u * actMB u x.vec r) + (∑ u : B, a.coeff u * actMB u y.vec r)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    simp_rw [actMB_eq_sum, Pi.add_apply, mul_add, Finset.sum_add_distrib, mul_add]
  add_smul a b x := by
    apply ModM.ext; funext r
    change (∑ u : B, (a.coeff u + b.coeff u) * actMB u x.vec r) =
      (∑ u : B, a.coeff u * actMB u x.vec r) + (∑ u : B, b.coeff u * actMB u x.vec r)
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun u _ => add_mul _ _ _
  zero_smul x := by
    apply ModM.ext; funext r; change (∑ u : B, (0 : ZMod 2) * actMB u x.vec r) = 0; simp

instance : IsScalarTower (ZMod 2) Λ ModM where
  smul_assoc c a x := by
    apply ModM.ext; funext r
    change (∑ u : B, c * a.coeff u * actMB u x.vec r) = c * ∑ u : B, a.coeff u * actMB u x.vec r
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun u _ => mul_assoc _ _ _

def eVec (j : Fin 7) : ModM := ⟨fun i => if i = j then 1 else 0⟩

lemma basisVec_smul_M (u : B) (x : ModM) : basisVec u • x = ⟨actMB u x.vec⟩ := by
  apply ModM.ext; funext r; change (∑ v : B, (basisVec u).coeff v * actMB v x.vec r) = actMB u x.vec r
  rw [Finset.sum_eq_single u]
  · simp [basisVec]
  · intro v _ hv; simp [basisVec, hv]
  · intro hm; exact absurd (Finset.mem_univ u) hm

lemma eq_sum_eVec (x : ModM) : x = ∑ j : Fin 7, x.vec j • eVec j := by
  apply ModM.ext; funext i
  have hsum : (∑ j : Fin 7, x.vec j • eVec j).vec i = ∑ j : Fin 7, x.vec j * (eVec j).vec i := by
    induction (Finset.univ : Finset (Fin 7)) using Finset.cons_induction with
    | empty => rfl
    | cons a s ha ih =>
      rw [Finset.sum_cons, Finset.sum_cons]
      change (x.vec a • eVec a).vec i + (∑ j ∈ s, x.vec j • eVec j).vec i = _
      rw [ih]; rfl
  rw [hsum, Finset.sum_eq_single i]
  · simp [eVec]
  · intro j _ hj; simp [eVec, Ne.symm hj]
  · intro hm; exact absurd (Finset.mem_univ i) hm

/-- Projective cover `πM : P02 ↠ ModM` sending `(a, b) ↦ a • e_0 + b • e_4`. -/
def πM : P02 →ₗ[Λ] ModM where
  toFun p := p.1.val • eVec 0 + p.2.val • eVec 4
  map_add' p q := by
    change (p.1.val + q.1.val) • eVec 0 + (p.2.val + q.2.val) • eVec 4 =
      (p.1.val • eVec 0 + p.2.val • eVec 4) + (q.1.val • eVec 0 + q.2.val • eVec 4)
    rw [add_smul, add_smul]; abel
  map_smul' a p := by
    change (a * p.1.val) • eVec 0 + (a * p.2.val) • eVec 4 =
      a • (p.1.val • eVec 0 + p.2.val • eVec 4)
    rw [smul_add, mul_smul, mul_smul]

/-- Helper: `Λ`-linear map `ModM →ₗ[Λ] P02` or `Twist ModM →ₗ[Λ] P02` from images of `e_0..e_6`. -/
def κMCol (j : Fin 7) : P02 :=
  match j.val with
  | 0 => (0, LProj.ofBasis (mkB 2 4 2 rfl) rfl)
  | 1 => (LProj.ofBasis (mkB 0 4 4 rfl) rfl, 0)
  | 2 => (LProj.ofBasis (mkB 0 3 3 rfl) rfl, LProj.ofBasis (mkB 2 3 2 rfl) rfl)
  | 3 => (LProj.ofBasis (mkB 0 3 3 rfl) rfl, 0)
  | 4 => (LProj.ofBasis (mkB 0 2 2 rfl) rfl, LProj.ofBasis (mkB 2 2 1 rfl) rfl)
  | 5 => (0, LProj.ofBasis (mkB 2 2 2 rfl) rfl)
  | 6 => (0, LProj.ofBasis (mkB 2 1 1 rfl) rfl)
  | _ => 0

def κMFun (x : Twist ModM) : P02 :=
  ∑ j : Fin 7, x.val.vec j • κMCol j

def κMColSpec (j : Fin 7) : List (Bool × B) :=
  match j.val with
  | 0 => [(true, mkB 2 4 2 rfl)]
  | 1 => [(false, mkB 0 4 4 rfl)]
  | 2 => [(false, mkB 0 3 3 rfl), (true, mkB 2 3 2 rfl)]
  | 3 => [(false, mkB 0 3 3 rfl)]
  | 4 => [(false, mkB 0 2 2 rfl), (true, mkB 2 2 1 rfl)]
  | 5 => [(true, mkB 2 2 2 rfl)]
  | 6 => [(true, mkB 2 1 1 rfl)]
  | _ => []

def pairListParity (l : List (Bool × B)) (p : Bool × B) : ZMod 2 :=
  l.foldl (fun acc x => if x == p then acc + 1 else acc) 0

lemma pairListParity_nil (p : Bool × B) : pairListParity [] p = 0 := rfl

lemma pairListParity_cons (x : Bool × B) (l : List (Bool × B)) (p : Bool × B) :
    pairListParity (x :: l) p = (if x = p then 1 else 0) + pairListParity l p := by
  have hgen : ∀ (l : List (Bool × B)) (a : ZMod 2),
      l.foldl (fun acc y => if y == p then acc + 1 else acc) a = a + pairListParity l p := by
    intro l; induction l with
    | nil => intro a; simp [pairListParity]
    | cons y ys ih =>
      intro a
      simp only [pairListParity, List.foldl_cons]
      rw [ih, ih (if y == p then 0 + 1 else 0)]
      by_cases hy : y = p
      · subst hy; simp only [beq_self_eq_true, ↓reduceIte, zero_add, add_assoc]
      · have hbf : (y == p) = false := beq_false_of_ne hy
        simp only [hbf, Bool.false_eq_true, ↓reduceIte, zero_add]
  unfold pairListParity
  rw [List.foldl_cons, hgen]
  by_cases h : x = p
  · subst h; simp only [beq_self_eq_true, ↓reduceIte, zero_add]; rfl
  · have hbf : (x == p) = false := beq_false_of_ne h
    simp only [h, hbf, Bool.false_eq_true, ↓reduceIte]; rfl

lemma pairListParity_append (l1 l2 : List (Bool × B)) (p : Bool × B) :
    pairListParity (l1 ++ l2) p = pairListParity l1 p + pairListParity l2 p := by
  induction l1 with
  | nil => simp [pairListParity_nil]
  | cons x xs ih => simp [pairListParity_cons, ih, add_assoc]

lemma pairListParity_of_not_mem {l : List (Bool × B)} {p : Bool × B} (h : p ∉ l) :
    pairListParity l p = 0 := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    rw [pairListParity_cons, ih (fun hm => h (List.mem_cons_of_mem x hm))]
    have hne : x ≠ p := fun heq => h (heq ▸ List.mem_cons_self ..)
    simp [hne]

def κMLhsList (u : B) (j : Fin 7) : List (Bool × B) :=
  (actList (nuB u)).flatMap fun rc => if rc.2 == j then κMColSpec rc.1 else []

def κMRhsList (u : B) (j : Fin 7) : List (Bool × B) :=
  (κMColSpec j).filterMap fun sw => (mulB u sw.2).map fun w => (sw.1, w)

lemma κM_basis_compat_fast :
    allBList.all (fun u => (List.finRange 7).all (fun j =>
      let l1 := κMLhsList u j
      let l2 := κMRhsList u j
      (l1 ++ l2).all fun p => pairListParity l1 p == pairListParity l2 p)) = true := by
  decide

lemma matParity_cons_eq (rc : Fin 7 × Fin 7) (rest : List (Fin 7 × Fin 7)) (r : Fin 7) :
    (if matParity (rc :: rest) r rc.2 then (1 : ZMod 2) else 0) =
    (if r = rc.1 then 1 else 0) + (if matParity rest r rc.2 then (1 : ZMod 2) else 0) := by
  unfold matParity
  simp only [List.foldr_cons]
  by_cases hr : r = rc.1
  · subst hr
    simp only [and_self, ↓reduceIte]
    cases List.foldr (fun p acc => if p.1 = rc.1 ∧ p.2 = rc.2 then !acc else acc) false rest <;> decide
  · simp [hr, Ne.symm hr]

lemma κMCol_fst_coeff (j : Fin 7) (w : B) :
    (κMCol j).1.val.coeff w = pairListParity (κMColSpec j) (false, w) := by
  fin_cases j <;>
    (simp [κMCol, κMColSpec, pairListParity_cons, pairListParity_nil, LProj.ofBasis, basisVec, mkB, eq_comm]; try rfl)

lemma κMCol_snd_coeff (j : Fin 7) (w : B) :
    (κMCol j).2.val.coeff w = pairListParity (κMColSpec j) (true, w) := by
  fin_cases j <;>
    (simp [κMCol, κMColSpec, pairListParity_cons, pairListParity_nil, LProj.ofBasis, basisVec, mkB, eq_comm]; try rfl)

lemma κMFun_smul_basis (u : B) (x : Twist ModM) :
    κMFun (basisVec u • x) = basisVec u • κMFun x := by
  have hlhs : ∀ (j : Fin 7) (p : Bool × B),
      pairListParity (κMLhsList u j) p = ∑ r : Fin 7, actMat (nuB u) r j * pairListParity (κMColSpec r) p := by
    intro j p
    have hflat : ∀ (l : List (Fin 7 × Fin 7)),
        pairListParity (l.flatMap fun rc => if rc.2 == j then κMColSpec rc.1 else []) p =
        ∑ r : Fin 7, (if matParity l r j then (1 : ZMod 2) else 0) * pairListParity (κMColSpec r) p := by
      intro l; induction l with
      | nil => simp [pairListParity_nil, matParity]
      | cons rc rest ih =>
        simp only [List.flatMap_cons, pairListParity_append, ih]
        by_cases h2 : rc.2 = j
        · subst h2
          simp only [beq_self_eq_true, ↓reduceIte]
          simp_rw [matParity_cons_eq, add_mul, Finset.sum_add_distrib]
          congr 1
          rw [Finset.sum_eq_single rc.1]
          · simp
          · intro r _ hr; simp [hr]
          · intro hm; exact absurd (Finset.mem_univ _) hm
        · have h2f : (rc.2 == j) = false := beq_false_of_ne h2
          simp only [h2f, Bool.false_eq_true, ↓reduceIte, pairListParity_nil, zero_add]
          refine Finset.sum_congr rfl fun r _ => ?_
          have hmp : matParity (rc :: rest) r j = matParity rest r j := by
            unfold matParity; simp only [List.foldr_cons]
            have hne : ¬ (rc.1 = r ∧ rc.2 = j) := fun h => h2 h.2
            simp [hne]
          rw [hmp]
    exact hflat (actList (nuB u))
  have hrhs1 : ∀ (j : Fin 7) (w : B),
      (basisVec u • κMCol j).1.val.coeff w = pairListParity (κMRhsList u j) (false, w) := by
    intro j w
    fin_cases j
    · change (basisVec u * 0).coeff w = _; rw [mul_zero]
      simp only [κMRhsList, κMColSpec, List.filterMap_cons, List.filterMap_nil]
      cases mulB u (mkB 2 4 2 rfl) <;> simp [pairListParity_cons, pairListParity_nil]
    · change (basisVec u * basisVec (mkB 0 4 4 rfl)).coeff w = _
      rw [basisVec_mul_basisVec]; simp only [κMRhsList, κMColSpec, List.filterMap_cons, List.filterMap_nil]
      cases hm : mulB u (mkB 0 4 4 rfl) <;> simp [basisVec, pairListParity_cons, pairListParity_nil, eq_comm]
    · change (basisVec u * basisVec (mkB 0 3 3 rfl)).coeff w = _
      rw [basisVec_mul_basisVec]; simp only [κMRhsList, κMColSpec, List.filterMap_cons, List.filterMap_nil]
      cases hm1 : mulB u (mkB 0 3 3 rfl) <;> cases hm2 : mulB u (mkB 2 3 2 rfl) <;>
        simp [basisVec, pairListParity_cons, pairListParity_nil, eq_comm]
    · change (basisVec u * basisVec (mkB 0 3 3 rfl)).coeff w = _
      rw [basisVec_mul_basisVec]; simp only [κMRhsList, κMColSpec, List.filterMap_cons, List.filterMap_nil]
      cases hm : mulB u (mkB 0 3 3 rfl) <;> simp [basisVec, pairListParity_cons, pairListParity_nil, eq_comm]
    · change (basisVec u * basisVec (mkB 0 2 2 rfl)).coeff w = _
      rw [basisVec_mul_basisVec]; simp only [κMRhsList, κMColSpec, List.filterMap_cons, List.filterMap_nil]
      cases hm1 : mulB u (mkB 0 2 2 rfl) <;> cases hm2 : mulB u (mkB 2 2 1 rfl) <;>
        simp [basisVec, pairListParity_cons, pairListParity_nil, eq_comm]
    · change (basisVec u * 0).coeff w = _; rw [mul_zero]
      simp only [κMRhsList, κMColSpec, List.filterMap_cons, List.filterMap_nil]
      cases mulB u (mkB 2 2 2 rfl) <;> simp [pairListParity_cons, pairListParity_nil]
    · change (basisVec u * 0).coeff w = _; rw [mul_zero]
      simp only [κMRhsList, κMColSpec, List.filterMap_cons, List.filterMap_nil]
      cases mulB u (mkB 2 1 1 rfl) <;> simp [pairListParity_cons, pairListParity_nil]
  have hrhs2 : ∀ (j : Fin 7) (w : B),
      (basisVec u • κMCol j).2.val.coeff w = pairListParity (κMRhsList u j) (true, w) := by
    intro j w
    fin_cases j
    · change (basisVec u * basisVec (mkB 2 4 2 rfl)).coeff w = _
      rw [basisVec_mul_basisVec]; simp only [κMRhsList, κMColSpec, List.filterMap_cons, List.filterMap_nil]
      cases hm : mulB u (mkB 2 4 2 rfl) <;> simp [basisVec, pairListParity_cons, pairListParity_nil, eq_comm]
    · change (basisVec u * 0).coeff w = _; rw [mul_zero]
      simp only [κMRhsList, κMColSpec, List.filterMap_cons, List.filterMap_nil]
      cases mulB u (mkB 0 4 4 rfl) <;> simp [pairListParity_cons, pairListParity_nil]
    · change (basisVec u * basisVec (mkB 2 3 2 rfl)).coeff w = _
      rw [basisVec_mul_basisVec]; simp only [κMRhsList, κMColSpec, List.filterMap_cons, List.filterMap_nil]
      cases hm1 : mulB u (mkB 0 3 3 rfl) <;> cases hm2 : mulB u (mkB 2 3 2 rfl) <;>
        simp [basisVec, pairListParity_cons, pairListParity_nil, eq_comm]
    · change (basisVec u * 0).coeff w = _; rw [mul_zero]
      simp only [κMRhsList, κMColSpec, List.filterMap_cons, List.filterMap_nil]
      cases mulB u (mkB 0 3 3 rfl) <;> simp [pairListParity_cons, pairListParity_nil]
    · change (basisVec u * basisVec (mkB 2 2 1 rfl)).coeff w = _
      rw [basisVec_mul_basisVec]; simp only [κMRhsList, κMColSpec, List.filterMap_cons, List.filterMap_nil]
      cases hm1 : mulB u (mkB 0 2 2 rfl) <;> cases hm2 : mulB u (mkB 2 2 1 rfl) <;>
        simp [basisVec, pairListParity_cons, pairListParity_nil, eq_comm]
    · change (basisVec u * basisVec (mkB 2 2 2 rfl)).coeff w = _
      rw [basisVec_mul_basisVec]; simp only [κMRhsList, κMColSpec, List.filterMap_cons, List.filterMap_nil]
      cases hm : mulB u (mkB 2 2 2 rfl) <;> simp [basisVec, pairListParity_cons, pairListParity_nil, eq_comm]
    · change (basisVec u * basisVec (mkB 2 1 1 rfl)).coeff w = _
      rw [basisVec_mul_basisVec]; simp only [κMRhsList, κMColSpec, List.filterMap_cons, List.filterMap_nil]
      cases hm : mulB u (mkB 2 1 1 rfl) <;> simp [basisVec, pairListParity_cons, pairListParity_nil, eq_comm]
  have h1 : ∀ j : Fin 7, (∑ r : Fin 7, actMat (nuB u) r j • κMCol r) = basisVec u • κMCol j := by
    intro j
    have hchk := List.all_eq_true.mp (List.all_eq_true.mp κM_basis_compat_fast u (mem_allBList u)) j (List.mem_finRange j)
    have hpar : ∀ p : Bool × B, pairListParity (κMLhsList u j) p = pairListParity (κMRhsList u j) p := by
      intro p
      by_cases hm : p ∈ κMLhsList u j ++ κMRhsList u j
      · exact beq_iff_eq.mp (List.all_eq_true.mp hchk p hm)
      · rw [pairListParity_of_not_mem (fun h => hm (List.mem_append_left _ h)),
            pairListParity_of_not_mem (fun h => hm (List.mem_append_right _ h))]
    have hfst : ∀ (s : Finset (Fin 7)) (w : B),
        (∑ r ∈ s, actMat (nuB u) r j • κMCol r).1.val.coeff w =
        ∑ r ∈ s, actMat (nuB u) r j * (κMCol r).1.val.coeff w := by
      intro s w; induction s using Finset.cons_induction with
      | empty => rfl
      | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, Prod.fst_add, LProj.val_add, add_coeff, ih]; rfl
    have hsnd : ∀ (s : Finset (Fin 7)) (w : B),
        (∑ r ∈ s, actMat (nuB u) r j • κMCol r).2.val.coeff w =
        ∑ r ∈ s, actMat (nuB u) r j * (κMCol r).2.val.coeff w := by
      intro s w; induction s using Finset.cons_induction with
      | empty => rfl
      | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, Prod.snd_add, LProj.val_add, add_coeff, ih]; rfl
    refine Prod.ext (LProj.ext ?_) (LProj.ext ?_)
    · apply Λ.ext; funext w; rw [hfst, hrhs1]; simp_rw [κMCol_fst_coeff]; rw [← hlhs, hpar]
    · apply Λ.ext; funext w; rw [hsnd, hrhs2]; simp_rw [κMCol_snd_coeff]; rw [← hlhs, hpar]
  unfold κMFun
  have hval : (basisVec u • x : Twist ModM).val = ⟨actMB (nuB u) x.val.vec⟩ := by
    change nuΛ (basisVec u) • x.val = _
    rw [nuΛ_basisVec, basisVec_smul_M]
  rw [hval]
  simp only [actMB_eq_sum]
  trans (∑ j : Fin 7, x.val.vec j • (∑ r : Fin 7, actMat (nuB u) r j • κMCol r))
  · trans (∑ r : Fin 7, ∑ j : Fin 7, (actMat (nuB u) r j * x.val.vec j) • κMCol r)
    · refine Finset.sum_congr rfl fun r _ => Finset.sum_smul ..
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun r _ => by rw [mul_comm, mul_smul]
  · simp_rw [h1, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => smul_comm _ _ _

/-- Embedding `κM : Twist ModM ↪ P02` with `im(κM) = ker(πM)`. -/
def κM : Twist ModM →ₗ[Λ] P02 where
  toFun := κMFun
  map_add' x y := by
    unfold κMFun; rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => add_smul _ _ _
  map_smul' a x := by
    have hsmul2 : ∀ (c : ZMod 2) (y : Twist ModM), κMFun (c • y) = c • κMFun y := by
      intro c y; unfold κMFun; rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun j _ => mul_smul _ _ _
    let fZ2 : Twist ModM →ₗ[ZMod 2] P02 :=
      { toFun := κMFun
        map_add' := fun x1 x2 => by
          unfold κMFun; rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun j _ => add_smul _ _ _
        map_smul' := hsmul2 }
    change fZ2 (a • x) = a • fZ2 x
    rw [eq_sum_basisVec a, Finset.sum_smul, Finset.sum_smul, map_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [smul_assoc, smul_assoc, map_smul]
    exact congrArg (a.coeff u • ·) (κMFun_smul_basis u x)

lemma πM_comp_κM : πM.comp κM = 0 := by
  have hcol : ∀ j : Fin 7, πM (κMCol j) = 0 := by
    have h : (List.finRange 7).all (fun j => (List.finRange 7).all fun r => (πM (κMCol j)).vec r == 0) = true := by
      decide
    intro j; apply ModM.ext; funext r
    exact beq_iff_eq.mp (List.all_eq_true.mp (List.all_eq_true.mp h j (List.mem_finRange j)) r (List.mem_finRange r))
  apply LinearMap.ext; intro x; apply ModM.ext; funext r
  change (πM (∑ j : Fin 7, x.val.vec j • κMCol j)).vec r = 0
  rw [map_sum]
  have h0 : (∑ j : Fin 7, πM (x.val.vec j • κMCol j)) = 0 :=
    Finset.sum_eq_zero fun j _ => by
      have hs : πM (x.val.vec j • κMCol j) = x.val.vec j • πM (κMCol j) := by
        have := map_smul πM (algebraMap (ZMod 2) Λ (x.val.vec j)) (κMCol j)
        simpa [algebraMap_smul] using this
      rw [hs, hcol j, smul_zero]
  rw [h0]; rfl

lemma κM_pivot_coeffs (z : Twist ModM) :
    (κM z).1.val.coeff (mkB 0 4 4 rfl) = z.val.vec 1 ∧
    (κM z).1.val.coeff (mkB 0 3 3 rfl) = z.val.vec 2 + z.val.vec 3 ∧
    (κM z).1.val.coeff (mkB 0 2 2 rfl) = z.val.vec 4 ∧
    (κM z).2.val.coeff (mkB 2 4 2 rfl) = z.val.vec 0 ∧
    (κM z).2.val.coeff (mkB 2 3 2 rfl) = z.val.vec 2 ∧
    (κM z).2.val.coeff (mkB 2 2 2 rfl) = z.val.vec 5 ∧
    (κM z).2.val.coeff (mkB 2 1 1 rfl) = z.val.vec 6 := by
  have h1 : ∀ (w : B), (κM z).1.val.coeff w = ∑ j : Fin 7, z.val.vec j * (κMCol j).1.val.coeff w := by
    intro w; change (∑ j : Fin 7, z.val.vec j • κMCol j).1.val.coeff w = _
    have hfst : ∀ (s : Finset (Fin 7)), (∑ j ∈ s, z.val.vec j • κMCol j).1.val.coeff w =
        ∑ j ∈ s, z.val.vec j * (κMCol j).1.val.coeff w := by
      intro s; induction s using Finset.cons_induction with
      | empty => rfl
      | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, Prod.fst_add, LProj.val_add, add_coeff, ih]; rfl
    exact hfst Finset.univ
  have h2 : ∀ (w : B), (κM z).2.val.coeff w = ∑ j : Fin 7, z.val.vec j * (κMCol j).2.val.coeff w := by
    intro w; change (∑ j : Fin 7, z.val.vec j • κMCol j).2.val.coeff w = _
    have hsnd : ∀ (s : Finset (Fin 7)), (∑ j ∈ s, z.val.vec j • κMCol j).2.val.coeff w =
        ∑ j ∈ s, z.val.vec j * (κMCol j).2.val.coeff w := by
      intro s; induction s using Finset.cons_induction with
      | empty => rfl
      | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, Prod.snd_add, LProj.val_add, add_coeff, ih]; rfl
    exact hsnd Finset.univ
  have hc1 : ∀ j : Fin 7, (κMCol j).1.val.coeff (mkB 0 4 4 rfl) = if j = 1 then 1 else 0 := by decide
  have hc2 : ∀ j : Fin 7, (κMCol j).1.val.coeff (mkB 0 3 3 rfl) = if j = 2 ∨ j = 3 then 1 else 0 := by decide
  have hc3 : ∀ j : Fin 7, (κMCol j).1.val.coeff (mkB 0 2 2 rfl) = if j = 4 then 1 else 0 := by decide
  have hc4 : ∀ j : Fin 7, (κMCol j).2.val.coeff (mkB 2 4 2 rfl) = if j = 0 then 1 else 0 := by decide
  have hc5 : ∀ j : Fin 7, (κMCol j).2.val.coeff (mkB 2 3 2 rfl) = if j = 2 then 1 else 0 := by decide
  have hc6 : ∀ j : Fin 7, (κMCol j).2.val.coeff (mkB 2 2 2 rfl) = if j = 5 then 1 else 0 := by decide
  have hc7 : ∀ j : Fin 7, (κMCol j).2.val.coeff (mkB 2 1 1 rfl) = if j = 6 then 1 else 0 := by decide
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h1]; simp_rw [hc1]; rw [Fin.sum_univ_seven]; simp
  · rw [h1]; simp_rw [hc2]; rw [Fin.sum_univ_seven]; simp
  · rw [h1]; simp_rw [hc3]; rw [Fin.sum_univ_seven]; simp
  · rw [h2]; simp_rw [hc4]; rw [Fin.sum_univ_seven]; simp
  · rw [h2]; simp_rw [hc5]; rw [Fin.sum_univ_seven]; simp
  · rw [h2]; simp_rw [hc6]; rw [Fin.sum_univ_seven]; simp
  · rw [h2]; simp_rw [hc7]; rw [Fin.sum_univ_seven]; simp

lemma κM_inj : Function.Injective κM := by
  intro x y hxy
  have hrec : ∀ z : Twist ModM,
      z.val.vec 0 = (κM z).2.val.coeff (mkB 2 4 2 rfl) ∧
      z.val.vec 1 = (κM z).1.val.coeff (mkB 0 4 4 rfl) ∧
      z.val.vec 2 = (κM z).2.val.coeff (mkB 2 3 2 rfl) ∧
      z.val.vec 3 = (κM z).1.val.coeff (mkB 0 3 3 rfl) + (κM z).2.val.coeff (mkB 2 3 2 rfl) ∧
      z.val.vec 4 = (κM z).1.val.coeff (mkB 0 2 2 rfl) ∧
      z.val.vec 5 = (κM z).2.val.coeff (mkB 2 2 2 rfl) ∧
      z.val.vec 6 = (κM z).2.val.coeff (mkB 2 1 1 rfl) := by
    intro z
    obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := κM_pivot_coeffs z
    refine ⟨c4.symm, c1.symm, c5.symm, ?_, c3.symm, c6.symm, c7.symm⟩
    rw [c2, c5, add_assoc, add_comm (z.val.vec 3), ← add_assoc, add_self_zmod2, zero_add]
  have hx := hrec x; have hy := hrec y
  apply Twist.ext; apply ModM.ext; funext i
  fin_cases i
  · exact hx.1.trans (by rw [hxy]; exact hy.1.symm)
  · exact hx.2.1.trans (by rw [hxy]; exact hy.2.1.symm)
  · exact hx.2.2.1.trans (by rw [hxy]; exact hy.2.2.1.symm)
  · exact hx.2.2.2.1.trans (by rw [hxy]; exact hy.2.2.2.1.symm)
  · exact hx.2.2.2.2.1.trans (by rw [hxy]; exact hy.2.2.2.2.1.symm)
  · exact hx.2.2.2.2.2.1.trans (by rw [hxy]; exact hy.2.2.2.2.2.1.symm)
  · exact hx.2.2.2.2.2.2.trans (by rw [hxy]; exact hy.2.2.2.2.2.2.symm)

lemma πM_surj : Function.Surjective πM := by
  intro y
  let pre : Fin 7 → P02 := fun j =>
    match j.val with
    | 0 => (LProj.ofBasis (mkB 0 0 0 rfl) rfl, 0)
    | 1 => (0, LProj.ofBasis (mkB 2 0 0 rfl) rfl)
    | 2 => (0, LProj.ofBasis (mkB 2 1 0 rfl) rfl)
    | 3 => (LProj.ofBasis (mkB 0 1 1 rfl) rfl, LProj.ofBasis (mkB 2 1 0 rfl) rfl)
    | 4 => (0, LProj.ofBasis (mkB 2 2 0 rfl) rfl)
    | 5 => (0, LProj.ofBasis (mkB 2 2 1 rfl) rfl)
    | 6 => (0, LProj.ofBasis (mkB 2 3 1 rfl) rfl)
    | _ => 0
  have hpre : ∀ j : Fin 7, πM (pre j) = eVec j := by
    have h : (List.finRange 7).all (fun j => (List.finRange 7).all fun r => (πM (pre j)).vec r == (eVec j).vec r) = true := by
      decide
    intro j; apply ModM.ext; funext r
    exact beq_iff_eq.mp (List.all_eq_true.mp (List.all_eq_true.mp h j (List.mem_finRange j)) r (List.mem_finRange r))
  refine ⟨∑ j : Fin 7, y.vec j • pre j, ?_⟩
  rw [map_sum]
  trans (∑ j : Fin 7, y.vec j • eVec j)
  · refine Finset.sum_congr rfl fun j _ => ?_
    have hs : πM (y.vec j • pre j) = y.vec j • πM (pre j) := by
      have := map_smul πM (algebraMap (ZMod 2) Λ (y.vec j)) (pre j)
      simpa [algebraMap_smul] using this
    rw [hs, hpre j]
  · exact (eq_sum_eVec y).symm

lemma ker_πM_eq_range_κM : LinearMap.ker πM = LinearMap.range κM := by
  apply le_antisymm
  · -- Explicit check: given `p ∈ ker πM`, reconstruct `x : Twist ModM` with `κM x = p`!
    intro p hp
    simp only [LinearMap.mem_ker] at hp
    let x : Twist ModM := ⟨⟨fun j =>
      match j.val with
      | 0 => p.2.val.coeff (mkB 2 4 2 rfl)
      | 1 => p.1.val.coeff (mkB 0 4 4 rfl)
      | 2 => p.2.val.coeff (mkB 2 3 2 rfl)
      | 3 => p.1.val.coeff (mkB 0 3 3 rfl) + p.2.val.coeff (mkB 2 3 2 rfl)
      | 4 => p.1.val.coeff (mkB 0 2 2 rfl)
      | 5 => p.2.val.coeff (mkB 2 2 2 rfl)
      | 6 => p.2.val.coeff (mkB 2 1 1 rfl)
      | _ => 0⟩⟩
    refine ⟨x, ?_⟩
    have hqker : πM (p - κM x) = 0 := by
      have hκ : πM (κM x) = 0 := LinearMap.congr_fun πM_comp_κM x
      rw [map_sub, hp, hκ, sub_zero]
    have hzero : ∀ (q : P02), πM q = 0 →
        q.2.val.coeff (mkB 2 4 2 rfl) = 0 →
        q.1.val.coeff (mkB 0 4 4 rfl) = 0 →
        q.2.val.coeff (mkB 2 3 2 rfl) = 0 →
        q.1.val.coeff (mkB 0 3 3 rfl) = 0 →
        q.1.val.coeff (mkB 0 2 2 rfl) = 0 →
        q.2.val.coeff (mkB 2 2 2 rfl) = 0 →
        q.2.val.coeff (mkB 2 1 1 rfl) = 0 → q = 0 := by
      intro q hq h0 h1 h2 h3 h4 h5 h6
      have hq1_zero : ∀ w : B, w.val.1 ≠ 0 → q.1.val.coeff w = 0 := by
        intro w hw
        have := congrArg (fun a : Λ => a.coeff w) q.1.right_idemp
        rw [← this, mul_coeff]
        exact Finset.sum_eq_zero fun u _ => Finset.sum_eq_zero fun v _ => by
          split_ifs with hm
          · have hv1 : w.val.1 = v.val.1 := ((mulB_eq_some_iff u v w).mp hm).2.1
            have hne : v ≠ idempB 0 := fun h => hw (hv1.trans (by rw [h]; rfl))
            simp [idempΛ, basisVec, hne]
          · rfl
      have hq2_zero : ∀ w : B, w.val.1 ≠ 2 → q.2.val.coeff w = 0 := by
        intro w hw
        have := congrArg (fun a : Λ => a.coeff w) q.2.right_idemp
        rw [← this, mul_coeff]
        exact Finset.sum_eq_zero fun u _ => Finset.sum_eq_zero fun v _ => by
          split_ifs with hm
          · have hv1 : w.val.1 = v.val.1 := ((mulB_eq_some_iff u v w).mp hm).2.1
            have hne : v ≠ idempB 2 := fun h => hw (hv1.trans (by rw [h]; rfl))
            simp [idempΛ, basisVec, hne]
          · rfl
      have hπ : ∀ r : Fin 7, (πM q).vec r =
          (∑ u : B, q.1.val.coeff u * actMat u r 0) + (∑ u : B, q.2.val.coeff u * actMat u r 4) := by
        intro r
        change (∑ u : B, q.1.val.coeff u * actMB u (eVec 0).vec r) +
          (∑ u : B, q.2.val.coeff u * actMB u (eVec 4).vec r) = _
        refine congrArg₂ (· + ·) ?_ ?_
        · refine Finset.sum_congr rfl fun u _ => congrArg (q.1.val.coeff u * ·) ?_
          rw [actMB_eq_sum, Finset.sum_eq_single (0 : Fin 7)]
          · simp [eVec]
          · intro c _ hc; simp [eVec, hc]
          · intro hm; exact absurd (Finset.mem_univ _) hm
        · refine Finset.sum_congr rfl fun u _ => congrArg (q.2.val.coeff u * ·) ?_
          rw [actMB_eq_sum, Finset.sum_eq_single (4 : Fin 7)]
          · simp [eVec]
          · intro c _ hc; simp [eVec, hc]
          · intro hm; exact absurd (Finset.mem_univ _) hm
      have hvec : ∀ r : Fin 7, (πM q).vec r = 0 := fun r => by rw [hq]; rfl
      have hc000 : q.1.val.coeff (mkB 0 0 0 rfl) = 0 := by
        have h := hvec 0; rw [hπ 0] at h
        have hs1 : (∑ u : B, q.1.val.coeff u * actMat u 0 0) = q.1.val.coeff (mkB 0 0 0 rfl) := by
          rw [Finset.sum_eq_single (mkB 0 0 0 rfl)]
          · simp [actMat, actMatBool, actList, matParity, mkB]
          · intro u _ hu; have hz : actMat u 0 0 = 0 := by
              have hc : allBList.all (fun u => (u == mkB 0 0 0 rfl) || (actMat u 0 0 == 0)) = true := by decide
              rcases Bool.or_eq_true _ _ |>.mp (List.all_eq_true.mp hc u (mem_allBList u)) with h1 | h2
              · exact absurd (beq_iff_eq.mp h1) hu
              · exact beq_iff_eq.mp h2
            rw [hz, mul_zero]
          · intro hm; exact absurd (Finset.mem_univ _) hm
        have hs2 : (∑ u : B, q.2.val.coeff u * actMat u 0 4) = 0 :=
          Finset.sum_eq_zero fun u _ => by
            have hz : actMat u 0 4 = 0 := by
              have hc : allBList.all (fun u => actMat u 0 4 == 0) = true := by decide
              exact beq_iff_eq.mp (List.all_eq_true.mp hc u (mem_allBList u))
            rw [hz, mul_zero]
        rw [hs1, hs2, add_zero] at h; exact h
      have hc200 : q.2.val.coeff (mkB 2 0 0 rfl) = 0 := by
        have h := hvec 1; rw [hπ 1] at h
        have hs1 : (∑ u : B, q.1.val.coeff u * actMat u 1 0) = 0 :=
          Finset.sum_eq_zero fun u _ => by
            have hz : actMat u 1 0 = 0 := by
              have hc : allBList.all (fun u => actMat u 1 0 == 0) = true := by decide
              exact beq_iff_eq.mp (List.all_eq_true.mp hc u (mem_allBList u))
            rw [hz, mul_zero]
        have hs2 : (∑ u : B, q.2.val.coeff u * actMat u 1 4) = q.2.val.coeff (mkB 2 0 0 rfl) := by
          rw [Finset.sum_eq_single (mkB 2 0 0 rfl)]
          · simp [actMat, actMatBool, actList, matParity, mkB]
          · intro u _ hu; have hz : actMat u 1 4 = 0 := by
              have hc : allBList.all (fun u => (u == mkB 2 0 0 rfl) || (actMat u 1 4 == 0)) = true := by decide
              rcases Bool.or_eq_true _ _ |>.mp (List.all_eq_true.mp hc u (mem_allBList u)) with h1 | h2
              · exact absurd (beq_iff_eq.mp h1) hu
              · exact beq_iff_eq.mp h2
            rw [hz, mul_zero]
          · intro hm; exact absurd (Finset.mem_univ _) hm
        rw [hs1, hs2, zero_add] at h; exact h
      have hc011 : q.1.val.coeff (mkB 0 1 1 rfl) = 0 := by
        have h := hvec 3; rw [hπ 3] at h
        have hs1 : (∑ u : B, q.1.val.coeff u * actMat u 3 0) = q.1.val.coeff (mkB 0 1 1 rfl) := by
          rw [Finset.sum_eq_single (mkB 0 1 1 rfl)]
          · simp [actMat, actMatBool, actList, matParity, mkB]
          · intro u _ hu; have hz : actMat u 3 0 = 0 := by
              have hc : allBList.all (fun u => (u == mkB 0 1 1 rfl) || (actMat u 3 0 == 0)) = true := by decide
              rcases Bool.or_eq_true _ _ |>.mp (List.all_eq_true.mp hc u (mem_allBList u)) with h1 | h2
              · exact absurd (beq_iff_eq.mp h1) hu
              · exact beq_iff_eq.mp h2
            rw [hz, mul_zero]
          · intro hm; exact absurd (Finset.mem_univ _) hm
        have hs2 : (∑ u : B, q.2.val.coeff u * actMat u 3 4) = 0 :=
          Finset.sum_eq_zero fun u _ => by
            have hz : actMat u 3 4 = 0 := by
              have hc : allBList.all (fun u => actMat u 3 4 == 0) = true := by decide
              exact beq_iff_eq.mp (List.all_eq_true.mp hc u (mem_allBList u))
            rw [hz, mul_zero]
        rw [hs1, hs2, add_zero] at h; exact h
      have hc210 : q.2.val.coeff (mkB 2 1 0 rfl) = 0 := by
        have h := hvec 2; rw [hπ 2] at h
        have hs1 : (∑ u : B, q.1.val.coeff u * actMat u 2 0) = q.1.val.coeff (mkB 0 1 1 rfl) := by
          rw [Finset.sum_eq_single (mkB 0 1 1 rfl)]
          · simp [actMat, actMatBool, actList, matParity, mkB]
          · intro u _ hu; have hz : actMat u 2 0 = 0 := by
              have hc : allBList.all (fun u => (u == mkB 0 1 1 rfl) || (actMat u 2 0 == 0)) = true := by decide
              rcases Bool.or_eq_true _ _ |>.mp (List.all_eq_true.mp hc u (mem_allBList u)) with h1 | h2
              · exact absurd (beq_iff_eq.mp h1) hu
              · exact beq_iff_eq.mp h2
            rw [hz, mul_zero]
          · intro hm; exact absurd (Finset.mem_univ _) hm
        have hs2 : (∑ u : B, q.2.val.coeff u * actMat u 2 4) = q.2.val.coeff (mkB 2 1 0 rfl) := by
          rw [Finset.sum_eq_single (mkB 2 1 0 rfl)]
          · simp [actMat, actMatBool, actList, matParity, mkB]
          · intro u _ hu; have hz : actMat u 2 4 = 0 := by
              have hc : allBList.all (fun u => (u == mkB 2 1 0 rfl) || (actMat u 2 4 == 0)) = true := by decide
              rcases Bool.or_eq_true _ _ |>.mp (List.all_eq_true.mp hc u (mem_allBList u)) with h1 | h2
              · exact absurd (beq_iff_eq.mp h1) hu
              · exact beq_iff_eq.mp h2
            rw [hz, mul_zero]
          · intro hm; exact absurd (Finset.mem_univ _) hm
        rw [hs1, hs2, hc011, zero_add] at h; exact h
      have hc220 : q.2.val.coeff (mkB 2 2 0 rfl) = 0 := by
        have h := hvec 4; rw [hπ 4] at h
        have hs1 : (∑ u : B, q.1.val.coeff u * actMat u 4 0) = 0 :=
          Finset.sum_eq_zero fun u _ => by
            have hz : actMat u 4 0 = 0 := by
              have hc : allBList.all (fun u => actMat u 4 0 == 0) = true := by decide
              exact beq_iff_eq.mp (List.all_eq_true.mp hc u (mem_allBList u))
            rw [hz, mul_zero]
        have hs2 : (∑ u : B, q.2.val.coeff u * actMat u 4 4) = q.2.val.coeff (mkB 2 2 0 rfl) := by
          rw [Finset.sum_eq_single (mkB 2 2 0 rfl)]
          · simp [actMat, actMatBool, actList, matParity, mkB]
          · intro u _ hu; have hz : actMat u 4 4 = 0 := by
              have hc : allBList.all (fun u => (u == mkB 2 2 0 rfl) || (actMat u 4 4 == 0)) = true := by decide
              rcases Bool.or_eq_true _ _ |>.mp (List.all_eq_true.mp hc u (mem_allBList u)) with h1 | h2
              · exact absurd (beq_iff_eq.mp h1) hu
              · exact beq_iff_eq.mp h2
            rw [hz, mul_zero]
          · intro hm; exact absurd (Finset.mem_univ _) hm
        rw [hs1, hs2, zero_add] at h; exact h
      have hc221 : q.2.val.coeff (mkB 2 2 1 rfl) = 0 := by
        have h := hvec 5; rw [hπ 5] at h
        have hs1 : (∑ u : B, q.1.val.coeff u * actMat u 5 0) = q.1.val.coeff (mkB 0 2 2 rfl) := by
          rw [Finset.sum_eq_single (mkB 0 2 2 rfl)]
          · simp [actMat, actMatBool, actList, matParity, mkB]
          · intro u _ hu; have hz : actMat u 5 0 = 0 := by
              have hc : allBList.all (fun u => (u == mkB 0 2 2 rfl) || (actMat u 5 0 == 0)) = true := by decide
              rcases Bool.or_eq_true _ _ |>.mp (List.all_eq_true.mp hc u (mem_allBList u)) with h1 | h2
              · exact absurd (beq_iff_eq.mp h1) hu
              · exact beq_iff_eq.mp h2
            rw [hz, mul_zero]
          · intro hm; exact absurd (Finset.mem_univ _) hm
        have hs2 : (∑ u : B, q.2.val.coeff u * actMat u 5 4) = q.2.val.coeff (mkB 2 2 1 rfl) := by
          rw [Finset.sum_eq_single (mkB 2 2 1 rfl)]
          · simp [actMat, actMatBool, actList, matParity, mkB]
          · intro u _ hu; have hz : actMat u 5 4 = 0 := by
              have hc : allBList.all (fun u => (u == mkB 2 2 1 rfl) || (actMat u 5 4 == 0)) = true := by decide
              rcases Bool.or_eq_true _ _ |>.mp (List.all_eq_true.mp hc u (mem_allBList u)) with h1 | h2
              · exact absurd (beq_iff_eq.mp h1) hu
              · exact beq_iff_eq.mp h2
            rw [hz, mul_zero]
          · intro hm; exact absurd (Finset.mem_univ _) hm
        rw [hs1, hs2, h4, zero_add] at h; exact h
      have hc231 : q.2.val.coeff (mkB 2 3 1 rfl) = 0 := by
        have h := hvec 6; rw [hπ 6] at h
        have hs1 : (∑ u : B, q.1.val.coeff u * actMat u 6 0) = 0 :=
          Finset.sum_eq_zero fun u _ => by
            have hz : actMat u 6 0 = 0 := by
              have hc : allBList.all (fun u => actMat u 6 0 == 0) = true := by decide
              exact beq_iff_eq.mp (List.all_eq_true.mp hc u (mem_allBList u))
            rw [hz, mul_zero]
        have hs2 : (∑ u : B, q.2.val.coeff u * actMat u 6 4) = q.2.val.coeff (mkB 2 3 1 rfl) := by
          rw [Finset.sum_eq_single (mkB 2 3 1 rfl)]
          · simp [actMat, actMatBool, actList, matParity, mkB]
          · intro u _ hu; have hz : actMat u 6 4 = 0 := by
              have hc : allBList.all (fun u => (u == mkB 2 3 1 rfl) || (actMat u 6 4 == 0)) = true := by decide
              rcases Bool.or_eq_true _ _ |>.mp (List.all_eq_true.mp hc u (mem_allBList u)) with h1 | h2
              · exact absurd (beq_iff_eq.mp h1) hu
              · exact beq_iff_eq.mp h2
            rw [hz, mul_zero]
          · intro hm; exact absurd (Finset.mem_univ _) hm
        rw [hs1, hs2, zero_add] at h; exact h
      refine Prod.ext (LProj.ext ?_) (LProj.ext ?_)
      · apply Λ.ext; funext w
        by_cases hw : w.val.1 = 0
        · have hall : w = mkB 0 0 0 rfl ∨ w = mkB 0 1 1 rfl ∨ w = mkB 0 2 2 rfl ∨
              w = mkB 0 3 3 rfl ∨ w = mkB 0 4 4 rfl := by
            have hb := B_bounds w
            have h1 := w.val.1.isLt; have h2 := w.val.2.1.isLt; have h3 := w.val.2.2.isLt
            have h0v : w.val.1.val = 0 := by simpa using congrArg Fin.val hw
            have hseq : w.val.2.2.val = w.val.2.1.val := by omega
            have hj : w.val.2.1.val = 0 ∨ w.val.2.1.val = 1 ∨ w.val.2.1.val = 2 ∨ w.val.2.1.val = 3 ∨ w.val.2.1.val = 4 := by omega
            rcases hj with hj | hj | hj | hj | hj
            · left; apply Subtype.ext; refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> (apply Fin.ext; dsimp [mkB]; omega)
            · right; left; apply Subtype.ext; refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> (apply Fin.ext; dsimp [mkB]; omega)
            · right; right; left; apply Subtype.ext; refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> (apply Fin.ext; dsimp [mkB]; omega)
            · right; right; right; left; apply Subtype.ext; refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> (apply Fin.ext; dsimp [mkB]; omega)
            · right; right; right; right; apply Subtype.ext; refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> (apply Fin.ext; dsimp [mkB]; omega)
          rcases hall with rfl | rfl | rfl | rfl | rfl <;> assumption
        · exact hq1_zero w hw
      · apply Λ.ext; funext w
        by_cases hw : w.val.1 = 2
        · have hall : w = mkB 2 0 0 rfl ∨ w = mkB 2 1 0 rfl ∨ w = mkB 2 1 1 rfl ∨
              w = mkB 2 2 0 rfl ∨ w = mkB 2 2 1 rfl ∨ w = mkB 2 2 2 rfl ∨
              w = mkB 2 3 1 rfl ∨ w = mkB 2 3 2 rfl ∨ w = mkB 2 4 2 rfl := by
            have hb := B_bounds w
            have h2v : w.val.1.val = 2 := by simpa using congrArg Fin.val hw
            have hcases : (w.val.2.1.val = 0 ∧ w.val.2.2.val = 0) ∨
                (w.val.2.1.val = 1 ∧ w.val.2.2.val = 0) ∨ (w.val.2.1.val = 1 ∧ w.val.2.2.val = 1) ∨
                (w.val.2.1.val = 2 ∧ w.val.2.2.val = 0) ∨ (w.val.2.1.val = 2 ∧ w.val.2.2.val = 1) ∨
                (w.val.2.1.val = 2 ∧ w.val.2.2.val = 2) ∨ (w.val.2.1.val = 3 ∧ w.val.2.2.val = 1) ∨
                (w.val.2.1.val = 3 ∧ w.val.2.2.val = 2) ∨ (w.val.2.1.val = 4 ∧ w.val.2.2.val = 2) := by omega
            rcases hcases with ⟨hj, hs⟩ | ⟨hj, hs⟩ | ⟨hj, hs⟩ | ⟨hj, hs⟩ | ⟨hj, hs⟩ | ⟨hj, hs⟩ | ⟨hj, hs⟩ | ⟨hj, hs⟩ | ⟨hj, hs⟩
            · left; apply Subtype.ext; refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> (apply Fin.ext; dsimp [mkB]; omega)
            · right; left; apply Subtype.ext; refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> (apply Fin.ext; dsimp [mkB]; omega)
            · right; right; left; apply Subtype.ext; refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> (apply Fin.ext; dsimp [mkB]; omega)
            · right; right; right; left; apply Subtype.ext; refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> (apply Fin.ext; dsimp [mkB]; omega)
            · right; right; right; right; left; apply Subtype.ext; refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> (apply Fin.ext; dsimp [mkB]; omega)
            · right; right; right; right; right; left; apply Subtype.ext; refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> (apply Fin.ext; dsimp [mkB]; omega)
            · right; right; right; right; right; right; left; apply Subtype.ext; refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> (apply Fin.ext; dsimp [mkB]; omega)
            · right; right; right; right; right; right; right; left; apply Subtype.ext; refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> (apply Fin.ext; dsimp [mkB]; omega)
            · right; right; right; right; right; right; right; right; apply Subtype.ext; refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> (apply Fin.ext; dsimp [mkB]; omega)
          rcases hall with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
        · exact hq2_zero w hw
    have hdiff0 : p - κM x = 0 := by
      obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := κM_pivot_coeffs x
      apply hzero (p - κM x) hqker
      · change p.2.val.coeff _ - (κM x).2.val.coeff _ = 0; rw [c4]; exact sub_self _
      · change p.1.val.coeff _ - (κM x).1.val.coeff _ = 0; rw [c1]; exact sub_self _
      · change p.2.val.coeff _ - (κM x).2.val.coeff _ = 0; rw [c5]; exact sub_self _
      · change p.1.val.coeff _ - (κM x).1.val.coeff _ = 0; rw [c2]
        change p.1.val.coeff (mkB 0 3 3 rfl) -
          (p.2.val.coeff (mkB 2 3 2 rfl) + (p.1.val.coeff (mkB 0 3 3 rfl) + p.2.val.coeff (mkB 2 3 2 rfl))) = 0
        rw [add_left_comm, add_self_zmod2, add_zero, sub_self]
      · change p.1.val.coeff _ - (κM x).1.val.coeff _ = 0; rw [c3]; exact sub_self _
      · change p.2.val.coeff _ - (κM x).2.val.coeff _ = 0; rw [c6]; exact sub_self _
      · change p.2.val.coeff _ - (κM x).2.val.coeff _ = 0; rw [c7]; exact sub_self _
    exact (sub_eq_zero.mp hdiff0).symm
  · rintro p ⟨x, rfl⟩
    simp only [LinearMap.mem_ker]
    exact LinearMap.congr_fun πM_comp_κM x

/-- Twisted exact sequence `0 → ModM -κMν→ P42 -πMν→ Twist ModM → 0`. -/
def κMν : ModM →ₗ[Λ] P42 :=
  nuP02.toLinearMap.comp ((Twist.map κM).comp (Twist.involEquiv (N := ModM)).symm.toLinearMap)

def πMν : P42 →ₗ[Λ] Twist ModM :=
  (Twist.map πM).comp nuP02.symm.toLinearMap

lemma πMν_comp_κMν : πMν.comp κMν = 0 := by
  apply LinearMap.ext; intro x
  simp only [LinearMap.comp_apply, πMν, κMν, LinearEquiv.coe_toLinearMap,
    LinearEquiv.symm_apply_apply, LinearMap.zero_apply]
  have h := LinearMap.congr_fun πM_comp_κM ⟨x⟩
  exact congrArg Twist.mk h

lemma κMν_inj : Function.Injective κMν := by
  intro x y h
  have h1 : κM ⟨x⟩ = κM ⟨y⟩ := by
    have := congrArg (Twist.val ∘ nuP02.symm) h
    simpa [κMν, Twist.map, Twist.involEquiv] using this
  exact congrArg Twist.val (κM_inj h1)

lemma πMν_surj : Function.Surjective πMν := by
  intro y
  obtain ⟨p, hp⟩ := πM_surj y.val
  refine ⟨nuP02 ⟨p⟩, ?_⟩
  apply Twist.ext; apply ModM.ext; funext r; simpa [πMν, Twist.map] using congrArg (fun m : ModM => m.vec r) hp

lemma ker_πMν_eq_range_κMν : LinearMap.ker πMν = LinearMap.range κMν := by
  ext q
  simp only [LinearMap.mem_ker, LinearMap.mem_range]
  constructor
  · intro hq
    have hp : (nuP02.symm q).val ∈ LinearMap.ker πM := by
      simp only [LinearMap.mem_ker]
      exact congrArg Twist.val hq
    rw [ker_πM_eq_range_κM] at hp
    obtain ⟨x, hx⟩ := hp
    refine ⟨x.val, ?_⟩
    apply nuP02.symm.injective
    apply Twist.ext
    simpa [κMν, Twist.map, Twist.involEquiv] using hx
  · rintro ⟨x, rfl⟩
    exact LinearMap.congr_fun πMν_comp_κMν x

/-- The nonzero nilpotent radical endomorphism `ρM = E_{1,0}` of `ModM`. -/
def ρM : ModM →ₗ[Λ] ModM where
  toFun x := ⟨fun i => if i = 1 then x.vec 0 else 0⟩
  map_add' x y := by
    apply ModM.ext; funext i; change (if i = 1 then x.vec 0 + y.vec 0 else 0) =
      (if i = 1 then x.vec 0 else 0) + (if i = 1 then y.vec 0 else 0)
    split_ifs <;> simp
  map_smul' a x := by
    have hchk : allBList.all (fun u => (List.finRange 7).all (fun r => (List.finRange 7).all fun c =>
        (if r = 1 then actMat u 0 c else (0 : ZMod 2)) == (if c = 0 then actMat u r 1 else 0))) = true := by
      decide
    apply ModM.ext; funext r
    change (if r = 1 then ∑ u : B, a.coeff u * actMB u x.vec 0 else 0) =
      ∑ u : B, a.coeff u * actMB u (fun i => if i = 1 then x.vec 0 else 0) r
    have hL : (if r = 1 then ∑ u : B, a.coeff u * actMB u x.vec 0 else 0) =
        ∑ u : B, a.coeff u * ∑ c : Fin 7, (if r = 1 then actMat u 0 c else 0) * x.vec c := by
      split_ifs with hr
      · rfl
      · simp
    have hR : (∑ u : B, a.coeff u * actMB u (fun i => if i = 1 then x.vec 0 else 0) r) =
        ∑ u : B, a.coeff u * ∑ c : Fin 7, (if c = 0 then actMat u r 1 else 0) * x.vec c := by
      refine Finset.sum_congr rfl fun u _ => congrArg (a.coeff u * ·) ?_
      rw [actMB_eq_sum, Finset.sum_eq_single (1 : Fin 7), Finset.sum_eq_single (0 : Fin 7)]
      · simp
      · intro c _ hc; simp [hc]
      · intro hm; exact absurd (Finset.mem_univ _) hm
      · intro c _ hc; simp [hc]
      · intro hm; exact absurd (Finset.mem_univ _) hm
    rw [hL, hR]
    refine Finset.sum_congr rfl fun u _ => congrArg (a.coeff u * ·) (Finset.sum_congr rfl fun c _ => ?_)
    have h := beq_iff_eq.mp (List.all_eq_true.mp (List.all_eq_true.mp
      (List.all_eq_true.mp hchk u (mem_allBList u)) r (List.mem_finRange r)) c (List.mem_finRange c))
    rw [h]

lemma ρM_comp_ρM : ρM.comp ρM = 0 := by
  apply LinearMap.ext; intro x; apply ModM.ext; funext i
  change (if i = 1 then (if (0 : Fin 7) = 1 then x.vec 0 else 0) else 0) = 0
  have h01 : (0 : Fin 7) ≠ 1 := by decide
  simp [h01]

lemma trPhiP02_ρM : trPhiP02 (κMν.comp (ρM.comp πM)) = 1 := by
  have h1 : (κMν (ρM (πM (LProj.gen 0, 0)))).1.val = basisVec (mkB 4 0 0 rfl) := by
    have hp : πM (LProj.gen 0, 0) = eVec 0 := by
      apply ModM.ext; funext r
      have h : (List.finRange 7).all (fun r => (πM (LProj.gen 0, 0)).vec r == (eVec 0).vec r) = true := by decide
      exact beq_iff_eq.mp (List.all_eq_true.mp h r (List.mem_finRange r))
    have hr : ρM (eVec 0) = eVec 1 := by
      apply ModM.ext; funext r; change (if r = 1 then (eVec 0).vec 0 else 0) = (eVec 1).vec r
      simp [eVec]
    rw [hp, hr]
    apply Λ.ext; funext w
    have h : allBList.all (fun w => (κMν (eVec 1)).1.val.coeff w == (basisVec (mkB 4 0 0 rfl)).coeff w) = true := by
      decide
    exact beq_iff_eq.mp (List.all_eq_true.mp h w (mem_allBList w))
  have h2 : (κMν (ρM (πM (0, LProj.gen 2)))).2.val = 0 := by
    have hp : πM (0, LProj.gen 2) = eVec 4 := by
      apply ModM.ext; funext r
      have h : (List.finRange 7).all (fun r => (πM (0, LProj.gen 2)).vec r == (eVec 4).vec r) = true := by decide
      exact beq_iff_eq.mp (List.all_eq_true.mp h r (List.mem_finRange r))
    have hr : ρM (eVec 4) = 0 := by
      apply ModM.ext; funext r; change (if r = 1 then (eVec 4).vec 0 else 0) = 0
      simp [eVec]
    rw [hp, hr, map_zero]; rfl
  unfold trPhiP02
  simp only [LinearMap.comp_apply]
  rw [h1, h2, map_zero, add_zero]
  decide

lemma trPhiP02_idM : trPhiP02 (κMν.comp πM) = 0 := by
  have h : trPhiP02 (κMν.comp πM) == 0 := by decide
  exact beq_iff_eq.mp h

end ModM

/-
## Part 3C: Stable Endomorphisms of `M`, Frobenius–Nakayama Duality, and Natural Twist `deltaTotal`
-/
section StableModM

open ModM

/-- Binary product in `ProjΛ`. -/
abbrev ProjΛ.prod (P Q : ProjΛ) : ProjΛ := ⟨P.carrier × Q.carrier⟩

/-- A `Λ`-linear map factors through a finitely generated projective module in `ProjΛ`. -/
def FactorsThroughProj {X Y : Type} [AddCommGroup X] [Module Λ X]
    [AddCommGroup Y] [Module Λ Y] (f : X →ₗ[Λ] Y) : Prop :=
  ∃ (P : ProjΛ) (g : X →ₗ[Λ] P.carrier) (h : P.carrier →ₗ[Λ] Y), f = h.comp g

lemma FactorsThroughProj_zero {X Y : Type} [AddCommGroup X] [Module Λ X]
    [AddCommGroup Y] [Module Λ Y] : FactorsThroughProj (0 : X →ₗ[Λ] Y) :=
  ⟨P02Obj, 0, 0, by simp⟩

lemma FactorsThroughProj_neg {X Y : Type} [AddCommGroup X] [Module Λ X]
    [AddCommGroup Y] [Module Λ Y] {f : X →ₗ[Λ] Y} (hf : FactorsThroughProj f) :
    FactorsThroughProj (-f) := by
  rcases hf with ⟨P, g, h, rfl⟩
  exact ⟨P, g, -h, by ext x; simp⟩

lemma FactorsThroughProj_add {X Y : Type} [AddCommGroup X] [Module Λ X]
    [AddCommGroup Y] [Module Λ Y] {f1 f2 : X →ₗ[Λ] Y}
    (h1 : FactorsThroughProj f1) (h2 : FactorsThroughProj f2) :
    FactorsThroughProj (f1 + f2) := by
  rcases h1 with ⟨P1, g1, k1, rfl⟩
  rcases h2 with ⟨P2, g2, k2, rfl⟩
  exact ⟨ProjΛ.prod P1 P2, g1.prod g2, k1.coprod k2, LinearMap.ext fun _ => rfl⟩

lemma FactorsThroughProj_sub {X Y : Type} [AddCommGroup X] [Module Λ X]
    [AddCommGroup Y] [Module Λ Y] {f1 f2 : X →ₗ[Λ] Y}
    (h1 : FactorsThroughProj f1) (h2 : FactorsThroughProj f2) :
    FactorsThroughProj (f1 - f2) := by
  rw [sub_eq_add_neg]; exact FactorsThroughProj_add h1 (FactorsThroughProj_neg h2)

lemma FactorsThroughProj_sum {ι : Type*} {X Y : Type} [AddCommGroup X] [Module Λ X]
    [AddCommGroup Y] [Module Λ Y] (s : Finset ι) (f : ι → (X →ₗ[Λ] Y))
    (hf : ∀ i ∈ s, FactorsThroughProj (f i)) :
    FactorsThroughProj (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [FactorsThroughProj_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact FactorsThroughProj_add (hf a (Finset.mem_insert_self a s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

lemma FactorsThroughProj_smul {X Y : Type} [AddCommGroup X] [Module Λ X]
    [Module (ZMod 2) X] [IsScalarTower (ZMod 2) Λ X]
    [AddCommGroup Y] [Module Λ Y] [Module (ZMod 2) Y] [IsScalarTower (ZMod 2) Λ Y]
    (c : ZMod 2) {f : X →ₗ[Λ] Y} (hf : FactorsThroughProj f) :
    FactorsThroughProj (c • f) := by
  rcases hf with ⟨P, g, h, rfl⟩
  refine ⟨P, g, c • h, ?_⟩
  ext x; rfl

lemma FactorsThroughProj_comp_left {X Y Z : Type} [AddCommGroup X] [Module Λ X]
    [AddCommGroup Y] [Module Λ Y] [AddCommGroup Z] [Module Λ Z]
    (u : Y →ₗ[Λ] Z) {f : X →ₗ[Λ] Y} (hf : FactorsThroughProj f) :
    FactorsThroughProj (u.comp f) := by
  rcases hf with ⟨P, g, h, rfl⟩
  exact ⟨P, g, u.comp h, rfl⟩

lemma FactorsThroughProj_comp_right {X Y Z : Type} [AddCommGroup X] [Module Λ X]
    [AddCommGroup Y] [Module Λ Y] [AddCommGroup Z] [Module Λ Z]
    {f : Y →ₗ[Λ] Z} (hf : FactorsThroughProj f) (v : X →ₗ[Λ] Y) :
    FactorsThroughProj (f.comp v) := by
  rcases hf with ⟨P, g, h, rfl⟩
  exact ⟨P, g.comp v, h, rfl⟩

lemma FactorsThroughProj_of_proj_dom (P : ProjΛ) {Y : Type} [AddCommGroup Y] [Module Λ Y]
    (f : P.carrier →ₗ[Λ] Y) : FactorsThroughProj f :=
  ⟨P, LinearMap.id, f, by ext x; rfl⟩

lemma FactorsThroughProj_of_proj_cod {X : Type} [AddCommGroup X] [Module Λ X]
    (P : ProjΛ) (f : X →ₗ[Λ] P.carrier) : FactorsThroughProj f :=
  ⟨P, f, LinearMap.id, by ext x; rfl⟩

lemma FactorsThroughProj_twist {X Y : Type} [AddCommGroup X] [Module Λ X]
    [AddCommGroup Y] [Module Λ Y] {f : X →ₗ[Λ] Y} (hf : FactorsThroughProj f) :
    FactorsThroughProj (Twist.map f) := by
  rcases hf with ⟨P, g, h, rfl⟩
  exact ⟨ProjΛ.nuFunctor.obj P, Twist.map g, Twist.map h, by ext x; rfl⟩

lemma FactorsThroughProj_iff_twist {X Y : Type} [AddCommGroup X] [Module Λ X]
    [AddCommGroup Y] [Module Λ Y] (f : X →ₗ[Λ] Y) :
    FactorsThroughProj (Twist.map f) ↔ FactorsThroughProj f := by
  constructor
  · intro h
    have h2 := FactorsThroughProj_twist h
    have heq : f = (Twist.involEquiv (N := Y)).toLinearMap.comp
        ((Twist.map (Twist.map f)).comp (Twist.involEquiv (N := X)).symm.toLinearMap) := by
      ext x; rfl
    rw [heq]
    exact FactorsThroughProj_comp_left _ (FactorsThroughProj_comp_right h2 _)
  · exact FactorsThroughProj_twist

lemma FactorsThroughProj_iff_exists_epi {X Y : Type} [AddCommGroup X] [Module Λ X]
    [AddCommGroup Y] [Module Λ Y] (P : ProjΛ) (π : P.carrier →ₗ[Λ] Y)
    (hπ : Function.Surjective π) (f : X →ₗ[Λ] Y) :
    FactorsThroughProj f ↔ ∃ g : X →ₗ[Λ] P.carrier, f = π.comp g := by
  constructor
  · rintro ⟨Q, g, h, rfl⟩
    haveI := Q.proj
    obtain ⟨h', hh'⟩ := Module.projective_lifting_property π h hπ
    exact ⟨h'.comp g, by rw [← LinearMap.comp_assoc, hh']⟩
  · rintro ⟨g, rfl⟩
    exact ⟨P, g, π, rfl⟩

lemma FactorsThroughProj_iff_exists_mono {X Y : Type} [AddCommGroup X] [Module Λ X]
    [Module (ZMod 2) X] [IsScalarTower (ZMod 2) Λ X]
    [AddCommGroup Y] [Module Λ Y] [Module (ZMod 2) Y] [IsScalarTower (ZMod 2) Λ Y]
    (P : ProjΛ) (κ : X →ₗ[Λ] P.carrier)
    (hκ : Function.Injective κ) (f : X →ₗ[Λ] Y) :
    FactorsThroughProj f ↔ ∃ h : P.carrier →ₗ[Λ] Y, f = h.comp κ := by
  constructor
  · rintro ⟨Q, g, h, rfl⟩
    obtain ⟨g', hg'⟩ := ProjΛ.injective Q κ hκ g
    exact ⟨h.comp g', by rw [LinearMap.comp_assoc, hg']⟩
  · rintro ⟨h, rfl⟩
    exact ⟨P, κ, h, rfl⟩

lemma FactorsThroughProj_to_ModM {X : Type} [AddCommGroup X] [Module Λ X] (f : X →ₗ[Λ] ModM) :
    FactorsThroughProj f ↔ ∃ g : X →ₗ[Λ] P02, f = πM.comp g :=
  FactorsThroughProj_iff_exists_epi P02Obj πM πM_surj f

lemma FactorsThroughProj_from_ModM {Y : Type} [AddCommGroup Y] [Module Λ Y]
    [Module (ZMod 2) Y] [IsScalarTower (ZMod 2) Λ Y] (f : ModM →ₗ[Λ] Y) :
    FactorsThroughProj f ↔ ∃ h : P42 →ₗ[Λ] Y, f = h.comp κMν :=
  FactorsThroughProj_iff_exists_mono P42Obj κMν κMν_inj f

lemma FactorsThroughProj_to_TwistModM {X : Type} [AddCommGroup X] [Module Λ X]
    (f : X →ₗ[Λ] Twist ModM) :
    FactorsThroughProj f ↔ ∃ g : X →ₗ[Λ] P42, f = πMν.comp g :=
  FactorsThroughProj_iff_exists_epi P42Obj πMν πMν_surj f

lemma FactorsThroughProj_from_TwistModM {Y : Type} [AddCommGroup Y] [Module Λ Y]
    [Module (ZMod 2) Y] [IsScalarTower (ZMod 2) Λ Y] (f : Twist ModM →ₗ[Λ] Y) :
    FactorsThroughProj f ↔ ∃ h : P02 →ₗ[Λ] Y, f = h.comp κM :=
  FactorsThroughProj_iff_exists_mono P02Obj κM κM_inj f

/-- Explicit map `gM : ModM →ₗ[Λ] P02` such that `pM := πM ∘ gM = E_{1,0} + E_{5,4}`. -/
def gMCol (j : Fin 7) : P02 :=
  match j.val with
  | 0 => (0, LProj.ofBasis (mkB 2 0 0 rfl) rfl)
  | 2 => (0, LProj.ofBasis (mkB 2 1 1 rfl) rfl)
  | 4 => (0, LProj.ofBasis (mkB 2 2 1 rfl) rfl)
  | 5 => (0, LProj.ofBasis (mkB 2 2 2 rfl) rfl)
  | 6 => (0, LProj.ofBasis (mkB 2 3 2 rfl) rfl)
  | _ => 0

def gMColSpec (j : Fin 7) : List (Bool × B) :=
  match j.val with
  | 0 => [(true, mkB 2 0 0 rfl)]
  | 2 => [(true, mkB 2 1 1 rfl)]
  | 4 => [(true, mkB 2 2 1 rfl)]
  | 5 => [(true, mkB 2 2 2 rfl)]
  | 6 => [(true, mkB 2 3 2 rfl)]
  | _ => []

def gMLhsList (u : B) (j : Fin 7) : List (Bool × B) :=
  (actList u).flatMap fun rc => if rc.2 == j then gMColSpec rc.1 else []

def gMRhsList (u : B) (j : Fin 7) : List (Bool × B) :=
  (gMColSpec j).filterMap fun sw => (mulB u sw.2).map fun w => (sw.1, w)

lemma gM_basis_compat_fast :
    allBList.all (fun u => (List.finRange 7).all (fun j =>
      let l1 := gMLhsList u j
      let l2 := gMRhsList u j
      (l1 ++ l2).all fun p => pairListParity l1 p == pairListParity l2 p)) = true := by
  decide

def gMFun (x : ModM) : P02 := ∑ j : Fin 7, x.vec j • gMCol j

lemma gMCol_fst_zero (j : Fin 7) : (gMCol j).1 = 0 := by fin_cases j <;> rfl

lemma gMCol_snd_coeff (j : Fin 7) (w : B) :
    (gMCol j).2.val.coeff w = pairListParity (gMColSpec j) (true, w) := by
  fin_cases j <;>
    (simp [gMCol, gMColSpec, pairListParity_cons, pairListParity_nil, LProj.ofBasis, basisVec, mkB, eq_comm]; try rfl)

lemma gMFun_smul_basis (u : B) (x : ModM) :
    gMFun (basisVec u • x) = basisVec u • gMFun x := by
  have hlhs : ∀ (j : Fin 7) (p : Bool × B),
      pairListParity (gMLhsList u j) p = ∑ r : Fin 7, actMat u r j * pairListParity (gMColSpec r) p := by
    intro j p
    have hflat : ∀ (l : List (Fin 7 × Fin 7)),
        pairListParity (l.flatMap fun rc => if rc.2 == j then gMColSpec rc.1 else []) p =
        ∑ r : Fin 7, (if matParity l r j then (1 : ZMod 2) else 0) * pairListParity (gMColSpec r) p := by
      intro l; induction l with
      | nil => simp [pairListParity_nil, matParity]
      | cons rc rest ih =>
        simp only [List.flatMap_cons, pairListParity_append, ih]
        by_cases h2 : rc.2 = j
        · subst h2; simp only [beq_self_eq_true, ↓reduceIte]
          simp_rw [matParity_cons_eq, add_mul, Finset.sum_add_distrib]
          congr 1; rw [Finset.sum_eq_single rc.1]
          · simp
          · intro r _ hr; simp [hr]
          · intro hm; exact absurd (Finset.mem_univ _) hm
        · have h2f : (rc.2 == j) = false := beq_false_of_ne h2
          simp only [h2f, Bool.false_eq_true, ↓reduceIte, pairListParity_nil, zero_add]
          refine Finset.sum_congr rfl fun r _ => ?_
          have hmp : matParity (rc :: rest) r j = matParity rest r j := by
            unfold matParity; simp only [List.foldr_cons]
            have hne : ¬ (rc.1 = r ∧ rc.2 = j) := fun h => h2 h.2
            simp [hne]
          rw [hmp]
    exact hflat (actList u)
  have hrhs2 : ∀ (j : Fin 7) (w : B),
      (basisVec u • gMCol j).2.val.coeff w = pairListParity (gMRhsList u j) (true, w) := by
    intro j w
    fin_cases j
    · change (basisVec u * basisVec (mkB 2 0 0 rfl)).coeff w = _
      rw [basisVec_mul_basisVec]; simp only [gMRhsList, gMColSpec, List.filterMap_cons, List.filterMap_nil]
      cases hm : mulB u (mkB 2 0 0 rfl) <;> simp [basisVec, pairListParity_cons, pairListParity_nil, eq_comm]
    · change (basisVec u * 0).coeff w = _; rw [mul_zero]; rfl
    · change (basisVec u * basisVec (mkB 2 1 1 rfl)).coeff w = _
      rw [basisVec_mul_basisVec]; simp only [gMRhsList, gMColSpec, List.filterMap_cons, List.filterMap_nil]
      cases hm : mulB u (mkB 2 1 1 rfl) <;> simp [basisVec, pairListParity_cons, pairListParity_nil, eq_comm]
    · change (basisVec u * 0).coeff w = _; rw [mul_zero]; rfl
    · change (basisVec u * basisVec (mkB 2 2 1 rfl)).coeff w = _
      rw [basisVec_mul_basisVec]; simp only [gMRhsList, gMColSpec, List.filterMap_cons, List.filterMap_nil]
      cases hm : mulB u (mkB 2 2 1 rfl) <;> simp [basisVec, pairListParity_cons, pairListParity_nil, eq_comm]
    · change (basisVec u * basisVec (mkB 2 2 2 rfl)).coeff w = _
      rw [basisVec_mul_basisVec]; simp only [gMRhsList, gMColSpec, List.filterMap_cons, List.filterMap_nil]
      cases hm : mulB u (mkB 2 2 2 rfl) <;> simp [basisVec, pairListParity_cons, pairListParity_nil, eq_comm]
    · change (basisVec u * basisVec (mkB 2 3 2 rfl)).coeff w = _
      rw [basisVec_mul_basisVec]; simp only [gMRhsList, gMColSpec, List.filterMap_cons, List.filterMap_nil]
      cases hm : mulB u (mkB 2 3 2 rfl) <;> simp [basisVec, pairListParity_cons, pairListParity_nil, eq_comm]
  have h1 : ∀ j : Fin 7, (∑ r : Fin 7, actMat u r j • gMCol r) = basisVec u • gMCol j := by
    intro j
    have hchk := List.all_eq_true.mp (List.all_eq_true.mp gM_basis_compat_fast u (mem_allBList u)) j (List.mem_finRange j)
    have hpar : ∀ p : Bool × B, pairListParity (gMLhsList u j) p = pairListParity (gMRhsList u j) p := by
      intro p
      by_cases hm : p ∈ gMLhsList u j ++ gMRhsList u j
      · exact beq_iff_eq.mp (List.all_eq_true.mp hchk p hm)
      · rw [pairListParity_of_not_mem (fun h => hm (List.mem_append_left _ h)),
            pairListParity_of_not_mem (fun h => hm (List.mem_append_right _ h))]
    have hfst : ∀ (s : Finset (Fin 7)), (∑ r ∈ s, actMat u r j • gMCol r).1 = 0 := by
      intro s; induction s using Finset.cons_induction with
      | empty => rfl
      | cons a s ha ih =>
        rw [Finset.sum_cons, Prod.fst_add, ih, add_zero]
        change actMat u a j • (gMCol a).1 = 0
        rw [gMCol_fst_zero, smul_zero]
    have hsnd : ∀ (s : Finset (Fin 7)) (w : B),
        (∑ r ∈ s, actMat u r j • gMCol r).2.val.coeff w =
        ∑ r ∈ s, actMat u r j * (gMCol r).2.val.coeff w := by
      intro s w; induction s using Finset.cons_induction with
      | empty => rfl
      | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, Prod.snd_add, LProj.val_add, add_coeff, ih]; rfl
    refine Prod.ext ?_ (LProj.ext ?_)
    · rw [hfst]; change (0 : LProj 0) = basisVec u • (gMCol j).1; rw [gMCol_fst_zero, smul_zero]
    · apply Λ.ext; funext w; rw [hsnd, hrhs2]; simp_rw [gMCol_snd_coeff]; rw [← hlhs, hpar]
  unfold gMFun
  rw [basisVec_smul_M]
  simp only [actMB_eq_sum]
  trans (∑ j : Fin 7, x.vec j • (∑ r : Fin 7, actMat u r j • gMCol r))
  · trans (∑ r : Fin 7, ∑ j : Fin 7, (actMat u r j * x.vec j) • gMCol r)
    · refine Finset.sum_congr rfl fun r _ => Finset.sum_smul ..
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun r _ => by rw [mul_comm, mul_smul]
  · simp_rw [h1, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => smul_comm _ _ _

def gM : ModM →ₗ[Λ] P02 where
  toFun := gMFun
  map_add' x y := by
    unfold gMFun; rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => add_smul _ _ _
  map_smul' a x := by
    let fZ2 : ModM →ₗ[ZMod 2] P02 :=
      { toFun := gMFun
        map_add' := fun x1 x2 => by
          unfold gMFun; rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun j _ => add_smul _ _ _
        map_smul' := fun c y => by
          unfold gMFun; rw [Finset.smul_sum]
          exact Finset.sum_congr rfl fun j _ => mul_smul _ _ _ }
    change fZ2 (a • x) = a • fZ2 x
    rw [eq_sum_basisVec a, Finset.sum_smul, Finset.sum_smul, map_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [smul_assoc, smul_assoc, map_smul]
    exact congrArg (a.coeff u • ·) (gMFun_smul_basis u x)

/-- The projective-factoring endomorphism `pM = πM ∘ gM = E_{1,0} + E_{5,4}` of `ModM`. -/
def pM : ModM →ₗ[Λ] ModM := πM.comp gM

lemma FactorsThroughProj_pM : FactorsThroughProj pM := ⟨P02Obj, gM, πM, rfl⟩

lemma pM_apply (x : ModM) :
    pM x = ⟨fun i => if i = 1 then x.vec 0 else if i = 5 then x.vec 4 else 0⟩ := by
  have hcol : ∀ j : Fin 7, πM (gMCol j) = (if j = 0 then eVec 1 else if j = 4 then eVec 5 else 0) := by
    have h : (List.finRange 7).all (fun j => (List.finRange 7).all fun r =>
      (πM (gMCol j)).vec r == (if j = 0 then eVec 1 else if j = 4 then eVec 5 else (0 : ModM)).vec r) = true := by
      decide
    intro j; apply ModM.ext; funext r
    exact beq_iff_eq.mp (List.all_eq_true.mp (List.all_eq_true.mp h j (List.mem_finRange j)) r (List.mem_finRange r))
  change πM (∑ j : Fin 7, x.vec j • gMCol j) = _
  rw [map_sum]
  have hsum : (∑ j : Fin 7, πM (x.vec j • gMCol j)) = x.vec 0 • eVec 1 + x.vec 4 • eVec 5 := by
    have hterm : ∀ j : Fin 7, πM (x.vec j • gMCol j) =
        x.vec j • (if j = 0 then eVec 1 else if j = 4 then eVec 5 else 0) := by
      intro j
      have hs : πM (x.vec j • gMCol j) = x.vec j • πM (gMCol j) := by
        have := map_smul πM (algebraMap (ZMod 2) Λ (x.vec j)) (gMCol j)
        simp only [algebraMap_smul] at this; exact this
      rw [hs, hcol j]
    simp_rw [hterm, Fin.sum_univ_seven]
    simp
  rw [hsum]
  apply ModM.ext; funext i
  fin_cases i <;> simp [eVec]

lemma pM_comp_ρM : pM.comp ρM = 0 := by
  apply LinearMap.ext; intro x; apply ModM.ext; funext i; rw [LinearMap.comp_apply, pM_apply]; simp [ρM]

lemma ρM_comp_pM : ρM.comp pM = 0 := by
  apply LinearMap.ext; intro x; apply ModM.ext; funext i; rw [LinearMap.comp_apply]; change (if i = 1 then (pM x).vec 0 else 0) = 0
  rw [pM_apply]; simp

lemma pM_comp_pM : pM.comp pM = 0 := by
  apply LinearMap.ext; intro x; apply ModM.ext; funext i; rw [LinearMap.comp_apply, pM_apply, pM_apply]; simp

/-- Helper: a `Λ`-linear map from `ModM` is determined by its values on `eVec 0` and `eVec 4`. -/
lemma modM_hom_ext {Y : Type} [AddCommGroup Y] [Module Λ Y] {f g : ModM →ₗ[Λ] Y}
    (h0 : f (eVec 0) = g (eVec 0)) (h4 : f (eVec 4) = g (eVec 4)) : f = g := by
  apply LinearMap.ext; intro x
  obtain ⟨p, rfl⟩ := πM_surj x
  change f (p.1.val • eVec 0 + p.2.val • eVec 4) = g (p.1.val • eVec 0 + p.2.val • eVec 4)
  rw [map_add, map_add, map_smul, map_smul, map_smul, map_smul, h0, h4]

/-- Classification of `End_Λ(ModM)`: 3-dimensional, spanned by `id`, `ρM`, `pM`. -/
lemma endM_decomp (h : ModM →ₗ[Λ] ModM) :
    h = (h (eVec 0)).vec 0 • LinearMap.id +
        ((h (eVec 0)).vec 1 + (h (eVec 4)).vec 5) • ρM +
        (h (eVec 4)).vec 5 • pM := by
  have h0_idemp : idempΛ 0 • eVec 0 = eVec 0 := by
    apply ModM.ext; funext r
    have hc : (List.finRange 7).all (fun r => (idempΛ 0 • eVec 0).vec r == (eVec 0).vec r) = true := by decide
    exact beq_iff_eq.mp (List.all_eq_true.mp hc r (List.mem_finRange r))
  have h4_idemp : idempΛ 2 • eVec 4 = eVec 4 := by
    apply ModM.ext; funext r
    have hc : (List.finRange 7).all (fun r => (idempΛ 2 • eVec 4).vec r == (eVec 4).vec r) = true := by decide
    exact beq_iff_eq.mp (List.all_eq_true.mp hc r (List.mem_finRange r))
  have hrel : basisVec (mkB 0 2 2 rfl) • eVec 0 = basisVec (mkB 2 2 1 rfl) • eVec 4 := by
    apply ModM.ext; funext r
    have hc : (List.finRange 7).all (fun r =>
      (basisVec (mkB 0 2 2 rfl) • eVec 0).vec r == (basisVec (mkB 2 2 1 rfl) • eVec 4).vec r) = true := by decide
    exact beq_iff_eq.mp (List.all_eq_true.mp hc r (List.mem_finRange r))
  have h0_wt : ∀ x : ModM, idempΛ 0 • x = ⟨fun i => if i = 0 ∨ i = 1 then x.vec i else 0⟩ := by
    intro x; rw [idempΛ, basisVec_smul_M]; apply ModM.ext; funext i
    fin_cases i <;>
      (change actMB (idempB 0) x.vec _ = _; rw [actMB_eq_sum, Fin.sum_univ_seven];
       simp [actMat, actMatBool, actList, matParity, idempB, mkB])
  have h2_wt : ∀ x : ModM, idempΛ 2 • x = ⟨fun i => if i = 4 ∨ i = 5 then x.vec i else 0⟩ := by
    intro x; rw [idempΛ, basisVec_smul_M]; apply ModM.ext; funext i
    fin_cases i <;>
      (change actMB (idempB 2) x.vec _ = _; rw [actMB_eq_sum, Fin.sum_univ_seven];
       simp [actMat, actMatBool, actList, matParity, idempB, mkB])
  have he0 : h (eVec 0) = (h (eVec 0)).vec 0 • eVec 0 + (h (eVec 0)).vec 1 • eVec 1 := by
    have hfix : idempΛ 0 • h (eVec 0) = h (eVec 0) := by rw [← map_smul, h0_idemp]
    rw [← hfix, h0_wt]; apply ModM.ext; funext i; fin_cases i <;> simp [eVec]
  have he4 : h (eVec 4) = (h (eVec 4)).vec 4 • eVec 4 + (h (eVec 4)).vec 5 • eVec 5 := by
    have hfix : idempΛ 2 • h (eVec 4) = h (eVec 4) := by rw [← map_smul, h4_idemp]
    rw [← hfix, h2_wt]; apply ModM.ext; funext i; fin_cases i <;> simp [eVec]
  have ha0_eq_b4 : (h (eVec 0)).vec 0 = (h (eVec 4)).vec 4 := by
    have h1 := congrArg (fun m : ModM => (h m).vec 5) hrel
    rw [map_smul, map_smul, he0, he4, smul_add, smul_add] at h1
    have hact : ∀ (u : B) (k : Fin 7) (c : ZMod 2),
        (basisVec u • (c • eVec k)).vec 5 = c * actMat u 5 k := by
      intro u k c
      rw [smul_comm, basisVec_smul_M]
      change c * actMB u (eVec k).vec 5 = _
      rw [actMB_eq_sum, Finset.sum_eq_single k]
      · simp [eVec]
      · intro j _ hj; simp [eVec, hj]
      · intro hm; exact absurd (Finset.mem_univ _) hm
    change (basisVec (mkB 0 2 2 rfl) • ((h (eVec 0)).vec 0 • eVec 0)).vec 5 +
        (basisVec (mkB 0 2 2 rfl) • ((h (eVec 0)).vec 1 • eVec 1)).vec 5 =
        (basisVec (mkB 2 2 1 rfl) • ((h (eVec 4)).vec 4 • eVec 4)).vec 5 +
        (basisVec (mkB 2 2 1 rfl) • ((h (eVec 4)).vec 5 • eVec 5)).vec 5 at h1
    rw [hact, hact, hact, hact] at h1
    have c1 : actMat (mkB 0 2 2 rfl) 5 0 = 1 := by decide
    have c2 : actMat (mkB 0 2 2 rfl) 5 1 = 0 := by decide
    have c3 : actMat (mkB 2 2 1 rfl) 5 4 = 1 := by decide
    have c4 : actMat (mkB 2 2 1 rfl) 5 5 = 0 := by decide
    rw [c1, c2, c3, c4, mul_one, mul_zero, mul_one, mul_zero, add_zero, add_zero] at h1
    exact h1
  apply modM_hom_ext
  · rw [he0]; apply ModM.ext; funext i
    simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply, pM_apply]
    fin_cases i <;> simp [ρM, eVec, add_assoc, add_self_zmod2]
  · rw [he4, ← ha0_eq_b4]; apply ModM.ext; funext i
    simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply, pM_apply]
    fin_cases i <;> simp [ρM, eVec]

private lemma idemp0_smul_eVec0 : idempΛ 0 • eVec 0 = eVec 0 := by
  apply ModM.ext; funext r
  have hc : (List.finRange 7).all (fun r => (idempΛ 0 • eVec 0).vec r == (eVec 0).vec r) = true := by decide
  exact beq_iff_eq.mp (List.all_eq_true.mp hc r (List.mem_finRange r))

private lemma idemp2_smul_eVec4 : idempΛ 2 • eVec 4 = eVec 4 := by
  apply ModM.ext; funext r
  have hc : (List.finRange 7).all (fun r => (idempΛ 2 • eVec 4).vec r == (eVec 4).vec r) = true := by decide
  exact beq_iff_eq.mp (List.all_eq_true.mp hc r (List.mem_finRange r))

private lemma modM_gen_rel : basisVec (mkB 0 2 2 rfl) • eVec 0 = basisVec (mkB 2 2 1 rfl) • eVec 4 := by
  apply ModM.ext; funext r
  have hc : (List.finRange 7).all (fun r =>
    (basisVec (mkB 0 2 2 rfl) • eVec 0).vec r == (basisVec (mkB 2 2 1 rfl) • eVec 4).vec r) = true := by decide
  exact beq_iff_eq.mp (List.all_eq_true.mp hc r (List.mem_finRange r))

private lemma idemp4_smul_modM_zero (x : ModM) : idempΛ 4 • x = 0 := by
  apply ModM.ext; funext r; rw [idempΛ, basisVec_smul_M]
  change actMB (idempB 4) x.vec r = 0
  rw [actMB_eq_sum]
  exact Finset.sum_eq_zero fun c _ => by
    have hz : actMat (idempB 4) r c = 0 := by
      have hc : (List.finRange 7).all (fun r => (List.finRange 7).all fun c =>
          actMat (idempB 4) r c == 0) = true := by decide
      exact beq_iff_eq.mp (List.all_eq_true.mp (List.all_eq_true.mp hc r (List.mem_finRange r)) c (List.mem_finRange c))
    rw [hz, zero_mul]

private lemma idemp0_smul_twistModM_zero (x : Twist ModM) : idempΛ 0 • x = 0 := by
  apply Twist.ext
  change nuΛ (idempΛ 0) • x.val = 0
  rw [nuΛ_idemp]
  exact idemp4_smul_modM_zero x.val

private def q2Tw : P02 →ₗ[Λ] Twist ModM where
  toFun p := p.2.val • ⟨eVec 4⟩
  map_add' p q := by change (p.2.val + q.2.val) • _ = _; rw [add_smul]
  map_smul' a p := by
    simp only [RingHom.id_apply]
    change (a * p.2.val) • (⟨eVec 4⟩ : Twist ModM) = a • (p.2.val • ⟨eVec 4⟩)
    rw [mul_smul]

private lemma q2Tw_gM_e0 : q2Tw (gM (eVec 0)) = 0 := by
  have hg0 : gM (eVec 0) = gMCol 0 := by
    change ∑ j : Fin 7, (eVec 0).vec j • gMCol j = gMCol 0
    rw [Finset.sum_eq_single (0 : Fin 7)]
    · simp [eVec]
    · intro j _ hj; simp [eVec, hj]
    · intro hm; exact absurd (Finset.mem_univ _) hm
  rw [hg0]; apply Twist.ext; apply ModM.ext; funext r
  have hnu0 : nuB (mkB 2 0 0 rfl) = mkB 2 4 2 rfl := by decide
  change (nuΛ (basisVec (mkB 2 0 0 rfl)) • eVec 4).vec r = 0
  rw [nuΛ_basisVec, hnu0, basisVec_smul_M]
  change actMB (mkB 2 4 2 rfl) (eVec 4).vec r = 0
  have hc : (List.finRange 7).all (fun r => actMB (mkB 2 4 2 rfl) (eVec 4).vec r == 0) = true := by decide
  exact beq_iff_eq.mp (List.all_eq_true.mp hc r (List.mem_finRange r))

private lemma q2Tw_gM_e4 : q2Tw (gM (eVec 4)) = ⟨eVec 5⟩ := by
  have hg4 : gM (eVec 4) = gMCol 4 := by
    change ∑ j : Fin 7, (eVec 4).vec j • gMCol j = gMCol 4
    rw [Finset.sum_eq_single (4 : Fin 7)]
    · simp [eVec]
    · intro j _ hj; simp [eVec, hj]
    · intro hm; exact absurd (Finset.mem_univ _) hm
  rw [hg4]; apply Twist.ext; apply ModM.ext; funext r
  have hnu4 : nuB (mkB 2 2 1 rfl) = mkB 2 2 1 rfl := by decide
  change (nuΛ (basisVec (mkB 2 2 1 rfl)) • eVec 4).vec r = (eVec 5).vec r
  rw [nuΛ_basisVec, hnu4, basisVec_smul_M]
  change actMB (mkB 2 2 1 rfl) (eVec 4).vec r = (eVec 5).vec r
  have hc : (List.finRange 7).all (fun r => actMB (mkB 2 2 1 rfl) (eVec 4).vec r == (eVec 5).vec r) = true := by decide
  exact beq_iff_eq.mp (List.all_eq_true.mp hc r (List.mem_finRange r))

/-- Every `Λ`-linear map `ModM → Twist ModM` factors through `P02` (hence through a projective). -/
lemma hom_ModM_Twist_factors (h : ModM →ₗ[Λ] Twist ModM) : FactorsThroughProj h := by
  have h2_wt_tw : ∀ x : Twist ModM, idempΛ 2 • x = ⟨⟨fun i => if i = 4 ∨ i = 5 then x.val.vec i else 0⟩⟩ := by
    intro x; apply Twist.ext; apply ModM.ext; funext i
    change (nuΛ (idempΛ 2) • x.val).vec i = _
    rw [nuΛ_idemp, idempΛ, basisVec_smul_M]
    fin_cases i <;>
      (change actMB (idempB 2) x.val.vec _ = _; rw [actMB_eq_sum, Fin.sum_univ_seven];
       simp [actMat, actMatBool, actList, matParity, idempB])
  have he0 : h (eVec 0) = 0 := by rw [← idemp0_smul_eVec0, map_smul, idemp0_smul_twistModM_zero]
  have he4 : h (eVec 4) = (h (eVec 4)).val.vec 4 • ⟨eVec 4⟩ + (h (eVec 4)).val.vec 5 • ⟨eVec 5⟩ := by
    have hfix : idempΛ 2 • h (eVec 4) = h (eVec 4) := by rw [← map_smul, idemp2_smul_eVec4]
    rw [← hfix, h2_wt_tw]
    apply Twist.ext; apply ModM.ext; funext i
    change (if i = 4 ∨ i = 5 then (h (eVec 4)).val.vec i else 0) =
      (h (eVec 4)).val.vec 4 * (eVec 4).vec i + (h (eVec 4)).val.vec 5 * (eVec 5).vec i
    fin_cases i <;> simp [eVec]
  have hb4_zero : (h (eVec 4)).val.vec 4 = 0 := by
    have h1 := congrArg (fun m : ModM => (h m).val.vec 5) modM_gen_rel
    rw [map_smul, map_smul, he0, smul_zero, he4, smul_add] at h1
    have hnu : nuB (mkB 2 2 1 rfl) = mkB 2 2 1 rfl := by decide
    have hact : ∀ (k : Fin 7) (c : ZMod 2),
        (basisVec (mkB 2 2 1 rfl) • (c • (⟨eVec k⟩ : Twist ModM))).val.vec 5 =
        c * actMat (mkB 2 2 1 rfl) 5 k := by
      intro k c
      change (nuΛ (basisVec (mkB 2 2 1 rfl)) • (c • eVec k)).vec 5 = _
      rw [nuΛ_basisVec, hnu, smul_comm, basisVec_smul_M]
      change c * actMB (mkB 2 2 1 rfl) (eVec k).vec 5 = _
      rw [actMB_eq_sum, Finset.sum_eq_single k]
      · simp [eVec]
      · intro j _ hj; simp [eVec, hj]
      · intro hm; exact absurd (Finset.mem_univ _) hm
    change (0 : ZMod 2) =
        (basisVec (mkB 2 2 1 rfl) • ((h (eVec 4)).val.vec 4 • (⟨eVec 4⟩ : Twist ModM))).val.vec 5 +
        (basisVec (mkB 2 2 1 rfl) • ((h (eVec 4)).val.vec 5 • (⟨eVec 5⟩ : Twist ModM))).val.vec 5 at h1
    rw [hact, hact] at h1
    have c3 : actMat (mkB 2 2 1 rfl) 5 4 = 1 := by decide
    have c4 : actMat (mkB 2 2 1 rfl) 5 5 = 0 := by decide
    rw [c3, c4, mul_one, mul_zero, add_zero] at h1
    exact h1.symm
  have hfact : h = ((h (eVec 4)).val.vec 5 • q2Tw).comp gM := by
    apply modM_hom_ext
    · rw [he0, LinearMap.comp_apply, LinearMap.smul_apply, q2Tw_gM_e0, smul_zero]
    · rw [LinearMap.comp_apply, LinearMap.smul_apply, q2Tw_gM_e4]
      conv_lhs => rw [he4, hb4_zero, zero_smul, zero_add]
  exact ⟨P02Obj, gM, (h (eVec 4)).val.vec 5 • q2Tw, hfact⟩

/-- Weight-space killing: any `ModM → Twist ModM` kills `ρM`, and any `Twist ModM → ModM` kills `Twist.map ρM`. -/
lemma hom_ModM_Twist_comp_ρM (h : ModM →ₗ[Λ] Twist ModM) : h.comp ρM = 0 := by
  apply LinearMap.ext; intro x
  have hfix : idempΛ 0 • ρM x = ρM x := by
    rw [idempΛ, basisVec_smul_M]; apply ModM.ext; funext i
    change actMB (idempB 0) (ρM x).vec i = (ρM x).vec i
    rw [actMB_eq_sum, Fin.sum_univ_seven]
    fin_cases i <;> simp [ρM, actMat, actMatBool, actList, matParity, idempB]
  change h (ρM x) = 0
  rw [← hfix, map_smul, idemp0_smul_twistModM_zero]

lemma hom_Twist_ModM_comp_twistρM (h : Twist ModM →ₗ[Λ] ModM) : h.comp (Twist.map ρM) = 0 := by
  apply LinearMap.ext; intro x
  have hfix : idempΛ 4 • Twist.map ρM x = Twist.map ρM x := by
    apply Twist.ext
    change nuΛ (idempΛ 4) • ρM x.val = ρM x.val
    rw [nuΛ_idemp, idempΛ, basisVec_smul_M]; apply ModM.ext; funext i
    change actMB (idempB 0) (ρM x.val).vec i = (ρM x.val).vec i
    rw [actMB_eq_sum, Fin.sum_univ_seven]
    fin_cases i <;> simp [ρM, actMat, actMatBool, actList, matParity, idempB]
  change h (Twist.map ρM x) = 0
  rw [← hfix, map_smul, idemp4_smul_modM_zero]

/-- Every `Λ`-linear map `Twist ModM → ModM` factors through a projective. -/
lemma hom_Twist_ModM_factors (h : Twist ModM →ₗ[Λ] ModM) : FactorsThroughProj h := by
  have htw : FactorsThroughProj ((Twist.map h).comp (Twist.involEquiv (N := ModM)).symm.toLinearMap) :=
    hom_ModM_Twist_factors _
  have h1 : FactorsThroughProj (Twist.map h) := by
    have heq : Twist.map h =
        ((Twist.map h).comp (Twist.involEquiv (N := ModM)).symm.toLinearMap).comp
          (Twist.involEquiv (N := ModM)).toLinearMap := by
      ext x; rfl
    rw [heq]; exact FactorsThroughProj_comp_right htw _
  exact (FactorsThroughProj_iff_twist h).mp h1

/-- Explicit 1-line lift `liftρM : P02 →ₗ[Λ] P02` of `ρM` realizing `Ω(ρM) = Twist.map (ρM + pM)`. -/
def liftρM : P02 →ₗ[Λ] P02 where
  toFun p := (0, ⟨p.1.val * basisVec (mkB 2 0 0 rfl), by
    rw [mul_assoc, idempΛ, basisVec_mul_basisVec]
    have h : mulB (mkB 2 0 0 rfl) (idempB 2) = some (mkB 2 0 0 rfl) := by decide
    rw [h]⟩)
  map_add' p q := Prod.ext (add_zero 0).symm (LProj.ext (add_mul p.1.val q.1.val _))
  map_smul' a p := Prod.ext (smul_zero a).symm (LProj.ext (mul_assoc a p.1.val _))

lemma πM_comp_liftρM : πM.comp liftρM = ρM.comp πM := by
  have h0 : πM (liftρM (LProj.gen 0, 0)) = ρM (πM (LProj.gen 0, 0)) := by
    have hl : liftρM (LProj.gen 0, 0) = (0, LProj.ofBasis (mkB 2 0 0 rfl) rfl) := by
      refine Prod.ext rfl (LProj.ext ?_)
      change idempΛ 0 * basisVec (mkB 2 0 0 rfl) = basisVec (mkB 2 0 0 rfl)
      rw [idempΛ, basisVec_mul_basisVec]
      have hm : mulB (idempB 0) (mkB 2 0 0 rfl) = some (mkB 2 0 0 rfl) := by decide
      rw [hm]
    rw [hl]; apply ModM.ext; funext r
    have hc : (List.finRange 7).all (fun r =>
      (πM (0, LProj.ofBasis (mkB 2 0 0 rfl) rfl)).vec r == (ρM (πM (LProj.gen 0, 0))).vec r) = true := by decide
    exact beq_iff_eq.mp (List.all_eq_true.mp hc r (List.mem_finRange r))
  have h2 : πM (liftρM (0, LProj.gen 2)) = ρM (πM (0, LProj.gen 2)) := by
    have hl : liftρM (0, LProj.gen 2) = 0 := Prod.ext rfl (LProj.ext (zero_mul _))
    rw [hl, map_zero]; apply ModM.ext; funext r
    have hc : (List.finRange 7).all (fun r =>
      (0 : ModM).vec r == (ρM (πM (0, LProj.gen 2))).vec r) = true := by decide
    exact beq_iff_eq.mp (List.all_eq_true.mp hc r (List.mem_finRange r))
  apply LinearMap.ext; intro p
  rw [p02_decomp p]
  simp only [LinearMap.comp_apply, map_add, map_smul]
  rw [show πM (liftρM (LProj.gen 0, 0)) = ρM (πM (LProj.gen 0, 0)) from h0,
      show πM (liftρM (0, LProj.gen 2)) = ρM (πM (0, LProj.gen 2)) from h2]

lemma liftρM_comp_κM : liftρM.comp κM = κM.comp (Twist.map (ρM + pM)) := by
  have hcol : ∀ j : Fin 7, liftρM (κMCol j) = if j = 4 then κMCol 5 else 0 := by
    intro j
    fin_cases j
    · exact Prod.ext rfl (LProj.ext (zero_mul _))
    · refine Prod.ext rfl (LProj.ext ?_)
      change basisVec (mkB 0 4 4 rfl) * basisVec (mkB 2 0 0 rfl) = 0
      rw [basisVec_mul_basisVec]; have hm : mulB (mkB 0 4 4 rfl) (mkB 2 0 0 rfl) = none := by decide
      rw [hm]
    · refine Prod.ext rfl (LProj.ext ?_)
      change basisVec (mkB 0 3 3 rfl) * basisVec (mkB 2 0 0 rfl) = 0
      rw [basisVec_mul_basisVec]; have hm : mulB (mkB 0 3 3 rfl) (mkB 2 0 0 rfl) = none := by decide
      rw [hm]
    · refine Prod.ext rfl (LProj.ext ?_)
      change basisVec (mkB 0 3 3 rfl) * basisVec (mkB 2 0 0 rfl) = 0
      rw [basisVec_mul_basisVec]; have hm : mulB (mkB 0 3 3 rfl) (mkB 2 0 0 rfl) = none := by decide
      rw [hm]
    · refine Prod.ext rfl (LProj.ext ?_)
      change basisVec (mkB 0 2 2 rfl) * basisVec (mkB 2 0 0 rfl) = basisVec (mkB 2 2 2 rfl)
      rw [basisVec_mul_basisVec]; have hm : mulB (mkB 0 2 2 rfl) (mkB 2 0 0 rfl) = some (mkB 2 2 2 rfl) := by decide
      rw [hm]
    · exact Prod.ext rfl (LProj.ext (zero_mul _))
    · exact Prod.ext rfl (LProj.ext (zero_mul _))
  apply LinearMap.ext; intro x
  have hL : liftρM (κM x) = x.val.vec 4 • κMCol 5 := by
    change liftρM (∑ j : Fin 7, x.val.vec j • κMCol j) = _
    rw [map_sum]
    have hterm : ∀ j : Fin 7, liftρM (x.val.vec j • κMCol j) =
        x.val.vec j • (if j = 4 then κMCol 5 else 0) := by
      intro j
      have hs : liftρM (x.val.vec j • κMCol j) = x.val.vec j • liftρM (κMCol j) := by
        have := map_smul liftρM (algebraMap (ZMod 2) Λ (x.val.vec j)) (κMCol j)
        simp only [algebraMap_smul] at this; exact this
      rw [hs, hcol j]
    simp_rw [hterm, Fin.sum_univ_seven]; simp
  have hR : κM (Twist.map (ρM + pM) x) = x.val.vec 4 • κMCol 5 := by
    have hv : (Twist.map (ρM + pM) x).val = x.val.vec 4 • eVec 5 := by
      apply ModM.ext; funext r; change (ρM x.val).vec r + (pM x.val).vec r = (x.val.vec 4 • eVec 5).vec r
      rw [pM_apply]
      fin_cases r <;> simp [ρM, eVec, add_self_zmod2]
    change ∑ j : Fin 7, (Twist.map (ρM + pM) x).val.vec j • κMCol j = _
    rw [hv, Fin.sum_univ_seven]; simp [eVec]
  exact hL.trans hR.symm

/-- `phiΛ` is invariant under `nuΛ`, so `trPhiP02` and `trPhiP42` are related by `nu`. -/
lemma phiΛ_nuΛ (a : Λ) : phiΛ (nuΛ a) = phiΛ a := by
  change (∑ u : B, if isSocB u then a.coeff (nuB u) else 0) =
    ∑ u : B, if isSocB u then a.coeff u else 0
  let e : B ≃ B := ⟨nuB, nuB, nuB_invol, nuB_invol⟩
  refine Finset.sum_equiv e (fun _ => by simp) fun u _ => ?_
  have hsoc : isSocB (nuB u) = isSocB u := by
    have hc : allBList.all (fun u => isSocB (nuB u) == isSocB u) = true := by decide
    exact beq_iff_eq.mp (List.all_eq_true.mp hc u (mem_allBList u))
  change (if isSocB u then a.coeff (nuB u) else 0) = if isSocB (nuB u) then a.coeff (nuB u) else 0
  rw [hsoc]

lemma trPhiP02_eq_trPhiP42_nu (T : P02 →ₗ[Λ] P42) :
    trPhiP02 T = trPhiP42 (nuP42.toLinearMap.comp ((Twist.map T).comp nuP02.symm.toLinearMap)) := by
  unfold trPhiP02 trPhiP42
  have h0 : nuP02.symm (LProj.gen 4, 0) = ⟨(LProj.gen 0, 0)⟩ :=
    Twist.ext (Prod.ext (LProj.ext (nuΛ_idemp 4)) (LProj.ext (map_zero nuΛ)))
  have h2 : nuP02.symm (0, LProj.gen 2) = ⟨(0, LProj.gen 2)⟩ :=
    Twist.ext (Prod.ext (LProj.ext (map_zero nuΛ)) (LProj.ext (nuΛ_idemp 2)))
  simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, h0, h2, Twist.map, nuP42]
  change phiΛ (T (LProj.gen 0, 0)).1.val + phiΛ (T (0, LProj.gen 2)).2.val =
    phiΛ (nuΛ (T (LProj.gen 0, 0)).1.val) + phiΛ (nuΛ (T (0, LProj.gen 2)).2.val)
  rw [phiΛ_nuΛ, phiΛ_nuΛ]

lemma trPhiP42_eq_trPhiP02_nu (T : P42 →ₗ[Λ] P02) :
    trPhiP42 T = trPhiP02 (nuP02.toLinearMap.comp ((Twist.map T).comp nuP42.symm.toLinearMap)) := by
  unfold trPhiP42 trPhiP02
  have h0 : nuP42.symm (LProj.gen 0, 0) = ⟨(LProj.gen 4, 0)⟩ :=
    Twist.ext (Prod.ext (LProj.ext (nuΛ_idemp 0)) (LProj.ext (map_zero nuΛ)))
  have h2 : nuP42.symm (0, LProj.gen 2) = ⟨(0, LProj.gen 2)⟩ :=
    Twist.ext (Prod.ext (LProj.ext (map_zero nuΛ)) (LProj.ext (nuΛ_idemp 2)))
  simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, h0, h2, Twist.map, nuP02]
  change phiΛ (T (LProj.gen 4, 0)).1.val + phiΛ (T (0, LProj.gen 2)).2.val =
    phiΛ (nuΛ (T (LProj.gen 4, 0)).1.val) + phiΛ (nuΛ (T (0, LProj.gen 2)).2.val)
  rw [phiΛ_nuΛ, phiΛ_nuΛ]

lemma trPhi_adj_02_right {Y : Type*} [AddCommGroup Y] [Module Λ Y]
    (α : P02 →ₗ[Λ] P42) (v : P02 →ₗ[Λ] Y) (g : Y →ₗ[Λ] P02) :
    let β : P42 →ₗ[Λ] P02 := nuP42.toLinearMap.comp ((Twist.map α).comp nuP02.symm.toLinearMap)
    trPhiP02 (α.comp (g.comp v)) = trPhiP42 (g.comp (v.comp β)) := by
  intro β
  let S : P02 →ₗ[Λ] P02 := g.comp v
  have hS0 := p02_decomp (S (LProj.gen 0, 0))
  have hS2 := p02_decomp (S (0, LProj.gen 2))
  have hβ4 := p02_decomp (β (LProj.gen 4, 0))
  have hβ2 := p02_decomp (β (0, LProj.gen 2))
  have hβ4_val : (β (LProj.gen 4, 0)).1.val = nuΛ (α (LProj.gen 0, 0)).1.val ∧
      (β (LProj.gen 4, 0)).2.val = nuΛ (α (LProj.gen 0, 0)).2.val := by
    have h0 : nuP02.symm (LProj.gen 4, 0) = ⟨(LProj.gen 0, 0)⟩ :=
      Twist.ext (Prod.ext (LProj.ext (nuΛ_idemp 4)) (LProj.ext (map_zero nuΛ)))
    simp only [β, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, h0, Twist.map, nuP42]
    exact ⟨rfl, rfl⟩
  have hβ2_val : (β (0, LProj.gen 2)).1.val = nuΛ (α (0, LProj.gen 2)).1.val ∧
      (β (0, LProj.gen 2)).2.val = nuΛ (α (0, LProj.gen 2)).2.val := by
    have h0 : nuP02.symm (0, LProj.gen 2) = ⟨(0, LProj.gen 2)⟩ :=
      Twist.ext (Prod.ext (LProj.ext (map_zero nuΛ)) (LProj.ext (nuΛ_idemp 2)))
    simp only [β, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, h0, Twist.map, nuP42]
    exact ⟨rfl, rfl⟩
  have hαS0 : α (S (LProj.gen 0, 0)) =
      (S (LProj.gen 0, 0)).1.val • α (LProj.gen 0, 0) + (S (LProj.gen 0, 0)).2.val • α (0, LProj.gen 2) := by
    conv_lhs => rw [hS0]
    rw [map_add, map_smul, map_smul]
  have hαS2 : α (S (0, LProj.gen 2)) =
      (S (0, LProj.gen 2)).1.val • α (LProj.gen 0, 0) + (S (0, LProj.gen 2)).2.val • α (0, LProj.gen 2) := by
    conv_lhs => rw [hS2]
    rw [map_add, map_smul, map_smul]
  have hSβ4 : S (β (LProj.gen 4, 0)) =
      (β (LProj.gen 4, 0)).1.val • S (LProj.gen 0, 0) + (β (LProj.gen 4, 0)).2.val • S (0, LProj.gen 2) := by
    conv_lhs => rw [hβ4]
    rw [map_add, map_smul, map_smul]
  have hSβ2 : S (β (0, LProj.gen 2)) =
      (β (0, LProj.gen 2)).1.val • S (LProj.gen 0, 0) + (β (0, LProj.gen 2)).2.val • S (0, LProj.gen 2) := by
    conv_lhs => rw [hβ2]
    rw [map_add, map_smul, map_smul]
  have hswap : ∀ a b : Λ, phiΛ (a * b) = phiΛ (nuΛ b * a) := by
    intro a b
    rw [phiΛ_comm a b, ← phiΛ_nuΛ (b * nuΛ a), map_mul]
    have hinv : nuΛ (nuΛ a) = a := by apply Λ.ext; funext w; simp [nuΛ, nuB_invol]
    rw [hinv]
  change phiΛ (α (S (LProj.gen 0, 0))).1.val + phiΛ (α (S (0, LProj.gen 2))).2.val =
    phiΛ (S (β (LProj.gen 4, 0))).1.val + phiΛ (S (β (0, LProj.gen 2))).2.val
  rw [hαS0, hαS2, hSβ4, hSβ2]
  simp only [Prod.fst_add, Prod.snd_add, LProj.val_add, map_add]
  change phiΛ ((S (LProj.gen 0, 0)).1.val * (α (LProj.gen 0, 0)).1.val) +
      phiΛ ((S (LProj.gen 0, 0)).2.val * (α (0, LProj.gen 2)).1.val) +
      (phiΛ ((S (0, LProj.gen 2)).1.val * (α (LProj.gen 0, 0)).2.val) +
      phiΛ ((S (0, LProj.gen 2)).2.val * (α (0, LProj.gen 2)).2.val)) =
    phiΛ ((β (LProj.gen 4, 0)).1.val * (S (LProj.gen 0, 0)).1.val) +
      phiΛ ((β (LProj.gen 4, 0)).2.val * (S (0, LProj.gen 2)).1.val) +
      (phiΛ ((β (0, LProj.gen 2)).1.val * (S (LProj.gen 0, 0)).2.val) +
      phiΛ ((β (0, LProj.gen 2)).2.val * (S (0, LProj.gen 2)).2.val))
  rw [hβ4_val.1, hβ4_val.2, hβ2_val.1, hβ2_val.2,
    hswap (S (LProj.gen 0, 0)).1.val (α (LProj.gen 0, 0)).1.val,
    hswap (S (LProj.gen 0, 0)).2.val (α (0, LProj.gen 2)).1.val,
    hswap (S (0, LProj.gen 2)).1.val (α (LProj.gen 0, 0)).2.val,
    hswap (S (0, LProj.gen 2)).2.val (α (0, LProj.gen 2)).2.val]
  ring

/-- The twisted image of `κMν ∘ πM` is `κM ∘ πMν`. -/
lemma nu_κMν_comp_πM :
    nuP42.toLinearMap.comp ((Twist.map (κMν.comp πM)).comp nuP02.symm.toLinearMap) =
    κM.comp πMν := by
  apply LinearMap.ext; intro p
  refine Prod.ext (LProj.ext ?_) (LProj.ext ?_)
  · change nuΛ (κMν (πM (nuP02.symm p).val)).1.val = (κM (πMν p)).1.val
    have h1 : κMν (πM (nuP02.symm p).val) = nuP02 ⟨κM (πMν p)⟩ := rfl
    rw [h1]; apply Λ.ext; funext w; simp [nuP02, nuΛ, nuB_invol]
  · change nuΛ (κMν (πM (nuP02.symm p).val)).2.val = (κM (πMν p)).2.val
    have h1 : κMν (πM (nuP02.symm p).val) = nuP02 ⟨κM (πMν p)⟩ := rfl
    rw [h1]; apply Λ.ext; funext w; simp [nuP02, nuΛ, nuB_invol]

/-- Any projective-factoring endomorphism of `ModM` has zero `trPhiP02`. -/
lemma trPhiP02_factors_eq_zero {h : ModM →ₗ[Λ] ModM} (hh : FactorsThroughProj h) :
    trPhiP02 (κMν.comp (h.comp πM)) = 0 := by
  obtain ⟨g, rfl⟩ := (FactorsThroughProj_to_ModM h).mp hh
  have hadj := trPhi_adj_02_right (κMν.comp πM) πM g
  dsimp only at hadj
  rw [nu_κMν_comp_πM] at hadj
  have heq : κMν.comp ((πM.comp g).comp πM) = (κMν.comp πM).comp (g.comp πM) := rfl
  rw [heq, hadj]
  have hzero : g.comp (πM.comp (κM.comp πMν)) = 0 := by
    apply LinearMap.ext; intro p
    simp only [LinearMap.comp_apply, LinearMap.zero_apply]
    have hk : πM (κM (πMν p)) = 0 := LinearMap.congr_fun πM_comp_κM (πMν p)
    rw [hk, map_zero]
  rw [hzero, trPhiP42_zero]

lemma not_factors_ρM : ¬ FactorsThroughProj ρM := by
  intro h
  have h0 := trPhiP02_factors_eq_zero h
  rw [trPhiP02_ρM] at h0
  exact one_ne_zero h0

lemma trPhiP02_endM (h : ModM →ₗ[Λ] ModM) :
    trPhiP02 (κMν.comp (h.comp πM)) = (h (eVec 0)).vec 1 + (h (eVec 4)).vec 5 := by
  conv_lhs => rw [endM_decomp h]
  have h1 : κMν.comp (((h (eVec 0)).vec 0 • LinearMap.id +
      ((h (eVec 0)).vec 1 + (h (eVec 4)).vec 5) • ρM + (h (eVec 4)).vec 5 • pM).comp πM) =
      (h (eVec 0)).vec 0 • (κMν.comp πM) +
      ((h (eVec 0)).vec 1 + (h (eVec 4)).vec 5) • (κMν.comp (ρM.comp πM)) +
      (h (eVec 4)).vec 5 • (κMν.comp (pM.comp πM)) := by
    apply LinearMap.ext; intro p
    simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply]
    have hsc : ∀ (c : ZMod 2) (m : ModM), κMν (c • m) = c • κMν m := fun c m => by
      have := map_smul κMν (algebraMap (ZMod 2) Λ c) m
      simp only [algebraMap_smul] at this; exact this
    rw [map_add, map_add, hsc, hsc, hsc]
  have hsmul : ∀ (c : ZMod 2) (T : P02 →ₗ[Λ] P42), trPhiP02 (c • T) = c * trPhiP02 T := by
    intro c T; unfold trPhiP02
    have hφ : ∀ (a : Λ), phiΛ (c • a) = c * phiΛ a := by
      intro a; exact map_smul phiΛ c a
    change phiΛ (c • (T (LProj.gen 0, 0)).1.val) + phiΛ (c • (T (0, LProj.gen 2)).2.val) = _
    rw [hφ, hφ, mul_add]
  rw [h1, trPhiP02_add, trPhiP02_add, hsmul, hsmul, hsmul, trPhiP02_idM, trPhiP02_ρM,
    trPhiP02_factors_eq_zero FactorsThroughProj_pM]
  ring

/-- Right nondegeneracy of `trPhiP02`, plus left/right nondegeneracy of `trPhiP42`. -/
lemma trPhiP02_nondeg_right {Y : Type*} [AddCommGroup Y] [Module Λ Y]
    (v : Y →ₗ[Λ] P42) (hv : ∀ u : P02 →ₗ[Λ] Y, trPhiP02 (v.comp u) = 0) : v = 0 := by
  by_contra hne
  have hex : ∃ y : Y, v y ≠ 0 := by
    by_contra hall; push_neg at hall; exact hne (LinearMap.ext hall)
  obtain ⟨y, hy⟩ := hex
  have hpair : ∀ (a : Λ), a ≠ 0 → ∃ b : Λ, phiΛ (b * a) = 1 := by
    intro a ha
    have hexw : ∃ w : B, a.coeff w ≠ 0 := by
      by_contra hall; push_neg at hall; exact ha (by apply Λ.ext; funext w; exact hall w)
    obtain ⟨w, hw⟩ := hexw
    have hw1 : a.coeff w = 1 := by
      have h01 : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
      exact (h01 (a.coeff w)).resolve_left hw
    refine ⟨basisVec (nuB (dualB w)), ?_⟩
    rw [phiΛ_comm, nuΛ_basisVec, nuB_invol, phiΛ_mul_dual, hw1]
  by_cases h1 : (v y).1.val ≠ 0
  · obtain ⟨b, hb⟩ := hpair (v y).1.val h1
    let u : P02 →ₗ[Λ] Y :=
      { toFun := fun p => p.1.val • (b • y)
        map_add' := fun p q => by change (p.1.val + q.1.val) • _ = _; rw [add_smul]
        map_smul' := fun r p => by
          simp only [RingHom.id_apply]; change (r * p.1.val) • _ = _; rw [mul_smul] }
    have htr := hv u
    change phiΛ (v (idempΛ 0 • (b • y))).1.val + phiΛ (v ((0 : Λ) • (b • y))).2.val = 0 at htr
    rw [zero_smul, map_zero, Prod.snd_zero, LProj.val_zero, map_zero, add_zero] at htr
    have hval : (v (idempΛ 0 • (b • y))).1.val = idempΛ 0 * (b * (v y).1.val) := by
      rw [map_smul, map_smul]; rfl
    rw [hval] at htr
    have hphi : phiΛ (idempΛ 0 * (b * (v y).1.val)) = phiΛ (b * (v y).1.val) := by
      have hnu0 : nuΛ (idempΛ 0) = idempΛ 4 := nuΛ_idemp 0
      rw [← mul_assoc, phiΛ_comm (idempΛ 0 * b) (v y).1.val, nuΛ.map_mul, hnu0,
        ← mul_assoc, (v y).1.right_idemp, ← phiΛ_comm b (v y).1.val]
    rw [hphi, hb] at htr
    exact one_ne_zero htr
  · push_neg at h1
    have h2 : (v y).2.val ≠ 0 := fun h2 => hy (Prod.ext (LProj.ext h1) (LProj.ext h2))
    obtain ⟨b, hb⟩ := hpair (v y).2.val h2
    let u : P02 →ₗ[Λ] Y :=
      { toFun := fun p => p.2.val • (b • y)
        map_add' := fun p q => by change (p.2.val + q.2.val) • _ = _; rw [add_smul]
        map_smul' := fun r p => by
          simp only [RingHom.id_apply]; change (r * p.2.val) • _ = _; rw [mul_smul] }
    have htr := hv u
    change phiΛ (v ((0 : Λ) • (b • y))).1.val + phiΛ (v (idempΛ 2 • (b • y))).2.val = 0 at htr
    rw [zero_smul, map_zero, Prod.fst_zero, LProj.val_zero, map_zero, zero_add] at htr
    have hval : (v (idempΛ 2 • (b • y))).2.val = idempΛ 2 * (b * (v y).2.val) := by
      rw [map_smul, map_smul]; rfl
    rw [hval] at htr
    have hphi : phiΛ (idempΛ 2 * (b * (v y).2.val)) = phiΛ (b * (v y).2.val) := by
      have hnu2 : nuΛ (idempΛ 2) = idempΛ 2 := nuΛ_idemp 2
      rw [← mul_assoc, phiΛ_comm (idempΛ 2 * b) (v y).2.val, nuΛ.map_mul, hnu2,
        ← mul_assoc, (v y).2.right_idemp, ← phiΛ_comm b (v y).2.val]
    rw [hphi, hb] at htr
    exact one_ne_zero htr

lemma trPhiP42_nondeg_left {Y : Type*} [AddCommGroup Y] [Module Λ Y]
    [Module (ZMod 2) Y] [IsScalarTower (ZMod 2) Λ Y]
    (u : P42 →ₗ[Λ] Y) (hu : ∀ v : Y →ₗ[Λ] P02, trPhiP42 (v.comp u) = 0) : u = 0 := by
  let u' : P02 →ₗ[Λ] Twist Y := (Twist.map u).comp nuP42.symm.toLinearMap
  have hu' : u' = 0 := trPhiP02_nondeg_left u' fun v' => by
    let v : Y →ₗ[Λ] P02 := (Twist.involEquiv (N := P02)).toLinearMap.comp
      ((Twist.map (nuP02.symm.toLinearMap.comp v')).comp (Twist.involEquiv (N := Y)).symm.toLinearMap)
    have htr := hu v
    rw [trPhiP42_eq_trPhiP02_nu] at htr
    have heq : nuP02.toLinearMap.comp ((Twist.map (v.comp u)).comp nuP42.symm.toLinearMap) = v'.comp u' := by
      apply LinearMap.ext; intro p
      simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, u', v]
      exact nuP02.apply_symm_apply _
    rw [heq] at htr; exact htr
  apply LinearMap.ext; intro p
  have h1 := LinearMap.congr_fun hu' (nuP42 ⟨p⟩)
  have h2 := congrArg Twist.val h1
  have hp : nuP42.symm (nuP42 ⟨p⟩) = ⟨p⟩ := nuP42.symm_apply_apply ⟨p⟩
  change u (nuP42.symm (nuP42 ⟨p⟩)).val = 0 at h2
  rw [hp] at h2; exact h2

lemma trPhiP42_nondeg_right {Y : Type*} [AddCommGroup Y] [Module Λ Y]
    [Module (ZMod 2) Y] [IsScalarTower (ZMod 2) Λ Y]
    (v : Y →ₗ[Λ] P02) (hv : ∀ u : P42 →ₗ[Λ] Y, trPhiP42 (v.comp u) = 0) : v = 0 := by
  let v' : Twist Y →ₗ[Λ] P42 := nuP02.toLinearMap.comp (Twist.map v)
  have hv' : v' = 0 := trPhiP02_nondeg_right v' fun u' => by
    let u : P42 →ₗ[Λ] Y := (Twist.involEquiv (N := Y)).toLinearMap.comp
      ((Twist.map (u'.comp nuP42.toLinearMap)).comp (Twist.involEquiv (N := P42)).symm.toLinearMap)
    have htr := hv u
    rw [trPhiP42_eq_trPhiP02_nu] at htr
    have heq : nuP02.toLinearMap.comp ((Twist.map (v.comp u)).comp nuP42.symm.toLinearMap) = v'.comp u' := by
      apply LinearMap.ext; intro p
      simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, v', u]
      have hp : nuP42 ⟨(nuP42.symm p).val⟩ = p := nuP42.apply_symm_apply p
      change nuP02 ⟨v (u' (nuP42 ⟨(nuP42.symm p).val⟩)).val⟩ = nuP02 ⟨v (u' p).val⟩
      rw [hp]
    rw [heq] at htr; exact htr
  apply LinearMap.ext; intro y
  have := LinearMap.congr_fun hv' ⟨y⟩
  have h1 := congrArg nuP02.symm this
  simp only [v', LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, LinearEquiv.symm_apply_apply,
    LinearMap.zero_apply, map_zero] at h1
  exact congrArg Twist.val h1

lemma dualMap_subtype_surj {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (S : Submodule (ZMod 2) V) : Function.Surjective S.subtype.dualMap := by
  intro φ
  obtain ⟨Q, hQ⟩ := Submodule.exists_isCompl S
  refine ⟨φ.comp (Submodule.projectionOnto S Q hQ), ?_⟩
  ext ⟨x, hx⟩
  change φ (Submodule.projectionOnto S Q hQ x) = φ ⟨x, hx⟩
  rw [Submodule.projectionOnto_apply_left hQ ⟨x, hx⟩]

instance instFiniteLinearMap {X Y : Type*} [AddCommGroup X] [Module Λ X]
    [AddCommGroup Y] [Module Λ Y] [Finite X] [Finite Y] : Finite (X →ₗ[Λ] Y) :=
  Finite.of_injective DFunLike.coe DFunLike.coe_injective

/-- Finite-dimensional adjoint range theorem: `u ∈ range A ↔ ∀ v ∈ ker A*, P2 u v = 0`. -/
lemma mem_range_iff_ortho_ker_adj
    {U1 U2 V1 V2 : Type*}
    [AddCommGroup U1] [Module (ZMod 2) U1] [FiniteDimensional (ZMod 2) U1]
    [AddCommGroup U2] [Module (ZMod 2) U2] [FiniteDimensional (ZMod 2) U2]
    [AddCommGroup V1] [Module (ZMod 2) V1] [FiniteDimensional (ZMod 2) V1]
    [AddCommGroup V2] [Module (ZMod 2) V2] [FiniteDimensional (ZMod 2) V2]
    (P1 : U1 →ₗ[ZMod 2] (V1 →ₗ[ZMod 2] ZMod 2))
    (P2 : U2 →ₗ[ZMod 2] (V2 →ₗ[ZMod 2] ZMod 2))
    (hP1L : Function.Injective P1) (hP1R : Function.Injective P1.flip)
    (hP2L : Function.Injective P2) (hP2R : Function.Injective P2.flip)
    (A : U1 →ₗ[ZMod 2] U2) (Astar : V2 →ₗ[ZMod 2] V1)
    (hadj : ∀ u v, P2 (A u) v = P1 u (Astar v)) (u : U2) :
    u ∈ LinearMap.range A ↔ ∀ v ∈ LinearMap.ker Astar, P2 u v = 0 := by
  have hdim1 : Module.finrank (ZMod 2) U1 = Module.finrank (ZMod 2) V1 := by
    apply le_antisymm
    · calc Module.finrank (ZMod 2) U1 ≤ Module.finrank (ZMod 2) (V1 →ₗ[ZMod 2] ZMod 2) :=
            LinearMap.finrank_le_finrank_of_injective hP1L
        _ = Module.finrank (ZMod 2) V1 := Subspace.dual_finrank_eq
    · calc Module.finrank (ZMod 2) V1 ≤ Module.finrank (ZMod 2) (U1 →ₗ[ZMod 2] ZMod 2) :=
            LinearMap.finrank_le_finrank_of_injective hP1R
        _ = Module.finrank (ZMod 2) U1 := Subspace.dual_finrank_eq
  have hdim2 : Module.finrank (ZMod 2) U2 = Module.finrank (ZMod 2) V2 := by
    apply le_antisymm
    · calc Module.finrank (ZMod 2) U2 ≤ Module.finrank (ZMod 2) (V2 →ₗ[ZMod 2] ZMod 2) :=
            LinearMap.finrank_le_finrank_of_injective hP2L
        _ = Module.finrank (ZMod 2) V2 := Subspace.dual_finrank_eq
    · calc Module.finrank (ZMod 2) V2 ≤ Module.finrank (ZMod 2) (U2 →ₗ[ZMod 2] ZMod 2) :=
            LinearMap.finrank_le_finrank_of_injective hP2R
        _ = Module.finrank (ZMod 2) U2 := Subspace.dual_finrank_eq
  have hP1_bij : Function.Bijective P1 :=
    ⟨hP1L, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (hdim1.trans Subspace.dual_finrank_eq.symm)).mp hP1L⟩
  have hP2_bij : Function.Bijective P2 :=
    ⟨hP2L, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (hdim2.trans Subspace.dual_finrank_eq.symm)).mp hP2L⟩
  let W : Submodule (ZMod 2) U2 :=
    LinearMap.ker ((LinearMap.ker Astar).subtype.dualMap.comp P2)
  have hW_mem : ∀ x : U2, x ∈ W ↔ ∀ v ∈ LinearMap.ker Astar, P2 x v = 0 := by
    intro x; simp only [W, LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.dualMap_apply,
      LinearMap.ext_iff, LinearMap.zero_apply, Submodule.coe_subtype, Subtype.forall]
  have hle : LinearMap.range A ≤ W := by
    rintro _ ⟨x, rfl⟩
    rw [hW_mem]; intro v hv
    rw [hadj, LinearMap.mem_ker.mp hv, map_zero]
  have hsurjW : Function.Surjective ((LinearMap.ker Astar).subtype.dualMap.comp P2) :=
    (dualMap_subtype_surj (LinearMap.ker Astar)).comp hP2_bij.2
  have hrankW : Module.finrank (ZMod 2) W + Module.finrank (ZMod 2) (LinearMap.ker Astar) =
      Module.finrank (ZMod 2) U2 := by
    have h1 := LinearMap.finrank_range_add_finrank_ker ((LinearMap.ker Astar).subtype.dualMap.comp P2)
    rw [LinearMap.range_eq_top.mpr hsurjW, finrank_top, Subspace.dual_finrank_eq] at h1
    change Module.finrank (ZMod 2) (LinearMap.ker Astar) + Module.finrank (ZMod 2) W = _ at h1
    omega
  let R : Submodule (ZMod 2) V1 := LinearMap.range Astar
  have hkerA : LinearMap.ker A = LinearMap.ker (R.subtype.dualMap.comp P1) := by
    ext x
    simp only [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.dualMap_apply,
      LinearMap.ext_iff, LinearMap.zero_apply, Submodule.coe_subtype, Subtype.forall, R, LinearMap.mem_range]
    constructor
    · rintro hx _ ⟨v, rfl⟩; rw [← hadj, hx, map_zero, LinearMap.zero_apply]
    · intro hx
      apply hP2L; ext v
      rw [hadj, map_zero, LinearMap.zero_apply]
      exact hx (Astar v) ⟨v, rfl⟩
  have hsurjR : Function.Surjective (R.subtype.dualMap.comp P1) :=
    (dualMap_subtype_surj R).comp hP1_bij.2
  have hrankKerA : Module.finrank (ZMod 2) (LinearMap.ker A) + Module.finrank (ZMod 2) R =
      Module.finrank (ZMod 2) U1 := by
    have h1 := LinearMap.finrank_range_add_finrank_ker (R.subtype.dualMap.comp P1)
    rw [LinearMap.range_eq_top.mpr hsurjR, finrank_top, Subspace.dual_finrank_eq, ← hkerA] at h1
    omega
  have hrankA := LinearMap.finrank_range_add_finrank_ker A
  have hrankAstar := LinearMap.finrank_range_add_finrank_ker Astar
  have hfeq : Module.finrank (ZMod 2) (LinearMap.range A) = Module.finrank (ZMod 2) W := by
    change Module.finrank (ZMod 2) R + Module.finrank (ZMod 2) (LinearMap.ker Astar) =
      Module.finrank (ZMod 2) V2 at hrankAstar
    omega
  have hEq : LinearMap.range A = W := Submodule.eq_of_le_of_finrank_eq hle hfeq
  rw [hEq, hW_mem]

/-- Frobenius–Nakayama duality (left): `h : ModM → X` factors through a projective iff
`trPhiP02 (κMν ∘ f ∘ h ∘ πM) = 0` for all `f : X → ModM`. -/
lemma frobenius_nakayama_left {X : Type} [AddCommGroup X] [Module Λ X]
    [Module (ZMod 2) X] [IsScalarTower (ZMod 2) Λ X] [Fintype X]
    (h : ModM →ₗ[Λ] X) :
    FactorsThroughProj h ↔ ∀ f : X →ₗ[Λ] ModM, trPhiP02 (κMν.comp (f.comp (h.comp πM))) = 0 := by
  constructor
  · intro hh f
    have heq : κMν.comp (f.comp (h.comp πM)) = κMν.comp ((f.comp h).comp πM) :=
      LinearMap.ext fun _ => rfl
    rw [heq]
    exact trPhiP02_factors_eq_zero (FactorsThroughProj_comp_left f hh)
  · intro hortho
    haveI : FiniteDimensional (ZMod 2) (P42 →ₗ[Λ] X) := Module.Finite.of_finite
    haveI : FiniteDimensional (ZMod 2) (P02 →ₗ[Λ] X) := Module.Finite.of_finite
    haveI : FiniteDimensional (ZMod 2) (X →ₗ[Λ] P02) := Module.Finite.of_finite
    haveI : FiniteDimensional (ZMod 2) (X →ₗ[Λ] P42) := Module.Finite.of_finite
    let P1 : (P42 →ₗ[Λ] X) →ₗ[ZMod 2] ((X →ₗ[Λ] P02) →ₗ[ZMod 2] ZMod 2) :=
      { toFun := fun u =>
          { toFun := fun v => trPhiP42 (v.comp u)
            map_add' := fun v1 v2 => by
              have : (v1 + v2).comp u = v1.comp u + v2.comp u := LinearMap.add_comp ..
              rw [this, trPhiP42_add]
            map_smul' := fun c v => by
              have hsc : (c • v).comp u = c • (v.comp u) := LinearMap.ext fun _ => rfl
              rw [hsc]; unfold trPhiP42
              have hφ : ∀ a : Λ, phiΛ (c • a) = c * phiΛ a := map_smul phiΛ c
              simp only [RingHom.id_apply, smul_eq_mul]
              change phiΛ (c • _) + phiΛ (c • _) = _
              rw [hφ, hφ, mul_add] }
        map_add' := fun u1 u2 => by
          ext v; change trPhiP42 (v.comp (u1 + u2)) = trPhiP42 (v.comp u1) + trPhiP42 (v.comp u2)
          rw [LinearMap.comp_add, trPhiP42_add]
        map_smul' := fun c u => by
          ext v; change trPhiP42 (v.comp (c • u)) = c * trPhiP42 (v.comp u)
          have hsc : v.comp (c • u) = c • (v.comp u) := by
            apply LinearMap.ext; intro p
            have := map_smul v (algebraMap (ZMod 2) Λ c) (u p)
            simp only [algebraMap_smul] at this; exact this
          rw [hsc]; unfold trPhiP42
          have hφ : ∀ a : Λ, phiΛ (c • a) = c * phiΛ a := map_smul phiΛ c
          change phiΛ (c • _) + phiΛ (c • _) = _
          rw [hφ, hφ, mul_add] }
    let P2 : (P02 →ₗ[Λ] X) →ₗ[ZMod 2] ((X →ₗ[Λ] P42) →ₗ[ZMod 2] ZMod 2) :=
      { toFun := fun u =>
          { toFun := fun v => trPhiP02 (v.comp u)
            map_add' := fun v1 v2 => by
              have : (v1 + v2).comp u = v1.comp u + v2.comp u := LinearMap.add_comp ..
              rw [this, trPhiP02_add]
            map_smul' := fun c v => by
              have hsc : (c • v).comp u = c • (v.comp u) := LinearMap.ext fun _ => rfl
              rw [hsc]; unfold trPhiP02
              have hφ : ∀ a : Λ, phiΛ (c • a) = c * phiΛ a := map_smul phiΛ c
              simp only [RingHom.id_apply, smul_eq_mul]
              change phiΛ (c • _) + phiΛ (c • _) = _
              rw [hφ, hφ, mul_add] }
        map_add' := fun u1 u2 => by
          ext v; change trPhiP02 (v.comp (u1 + u2)) = trPhiP02 (v.comp u1) + trPhiP02 (v.comp u2)
          rw [LinearMap.comp_add, trPhiP02_add]
        map_smul' := fun c u => by
          ext v; change trPhiP02 (v.comp (c • u)) = c * trPhiP02 (v.comp u)
          have hsc : v.comp (c • u) = c • (v.comp u) := by
            apply LinearMap.ext; intro p
            have := map_smul v (algebraMap (ZMod 2) Λ c) (u p)
            simp only [algebraMap_smul] at this; exact this
          rw [hsc]; unfold trPhiP02
          have hφ : ∀ a : Λ, phiΛ (c • a) = c * phiΛ a := map_smul phiΛ c
          change phiΛ (c • _) + phiΛ (c • _) = _
          rw [hφ, hφ, mul_add] }
    let A : (P42 →ₗ[Λ] X) →ₗ[ZMod 2] (P02 →ₗ[Λ] X) :=
      { toFun := fun u => u.comp (κMν.comp πM)
        map_add' := fun _ _ => LinearMap.add_comp ..
        map_smul' := fun _ _ => LinearMap.ext fun _ => rfl }
    let Astar : (X →ₗ[Λ] P42) →ₗ[ZMod 2] (X →ₗ[Λ] P02) :=
      { toFun := fun v => (κM.comp πMν).comp v
        map_add' := fun _ _ => LinearMap.comp_add ..
        map_smul' := fun c v => by
          apply LinearMap.ext; intro x
          have := map_smul (κM.comp πMν) (algebraMap (ZMod 2) Λ c) (v x)
          simp only [algebraMap_smul] at this; exact this }
    have hP1L : Function.Injective P1 := (injective_iff_map_eq_zero P1).mpr fun u hu =>
      trPhiP42_nondeg_left u fun v => LinearMap.congr_fun hu v
    have hP1R : Function.Injective P1.flip := (injective_iff_map_eq_zero P1.flip).mpr fun v hv =>
      trPhiP42_nondeg_right v fun u => LinearMap.congr_fun hv u
    have hP2L : Function.Injective P2 := (injective_iff_map_eq_zero P2).mpr fun u hu =>
      trPhiP02_nondeg_left u fun v => LinearMap.congr_fun hu v
    have hP2R : Function.Injective P2.flip := (injective_iff_map_eq_zero P2.flip).mpr fun v hv =>
      trPhiP02_nondeg_right v fun u => LinearMap.congr_fun hv u
    have hadj : ∀ u v, P2 (A u) v = P1 u (Astar v) := fun u v => by
      have h := trPhi_adj_02 (κMν.comp πM) u v
      dsimp only at h
      rw [nu_κMν_comp_πM] at h
      exact h
    have hmem : h.comp πM ∈ LinearMap.range A := by
      rw [mem_range_iff_ortho_ker_adj P1 P2 hP1L hP1R hP2L hP2R A Astar hadj]
      intro v hv
      have hπv : πMν.comp v = 0 := by
        apply LinearMap.ext; intro x; apply κM_inj
        have h0 := LinearMap.congr_fun (LinearMap.mem_ker.mp hv) x
        simpa [Astar] using h0
      have hsub : ∀ x : X, ∃ m : ModM, κMν m = v x := fun x => by
        have hm : v x ∈ LinearMap.ker πMν := by
          simp only [LinearMap.mem_ker]
          exact LinearMap.congr_fun hπv x
        rw [ker_πMν_eq_range_κMν] at hm; exact hm
      choose fFun hfFun using hsub
      let f : X →ₗ[Λ] ModM :=
        { toFun := fFun
          map_add' := fun x1 x2 => κMν_inj (by rw [map_add, hfFun, hfFun, hfFun, map_add])
          map_smul' := fun a x => κMν_inj (by
            simp only [RingHom.id_apply]
            rw [map_smul, hfFun, hfFun, map_smul]) }
      have hv_eq : v = κMν.comp f := LinearMap.ext fun x => (hfFun x).symm
      rw [hv_eq]
      exact hortho f
    obtain ⟨h', hh'⟩ := hmem
    rw [FactorsThroughProj_from_ModM]
    refine ⟨h', ?_⟩
    apply LinearMap.ext; intro m
    obtain ⟨p, rfl⟩ := πM_surj m
    exact (LinearMap.congr_fun hh' p).symm

/-- Frobenius–Nakayama duality (right): `f : X → ModM` factors through a projective iff
`trPhiP02 (κMν ∘ f ∘ h ∘ πM) = 0` for all `h : ModM → X`. -/
lemma frobenius_nakayama_right {X : Type} [AddCommGroup X] [Module Λ X]
    [Module (ZMod 2) X] [IsScalarTower (ZMod 2) Λ X] [Fintype X]
    (f : X →ₗ[Λ] ModM) :
    FactorsThroughProj f ↔ ∀ h : ModM →ₗ[Λ] X, trPhiP02 (κMν.comp (f.comp (h.comp πM))) = 0 := by
  constructor
  · intro hf h
    have heq : κMν.comp (f.comp (h.comp πM)) = κMν.comp ((f.comp h).comp πM) :=
      LinearMap.ext fun _ => rfl
    rw [heq]
    exact trPhiP02_factors_eq_zero (FactorsThroughProj_comp_right hf h)
  · intro hortho
    haveI : FiniteDimensional (ZMod 2) (X →ₗ[Λ] P02) := Module.Finite.of_finite
    haveI : FiniteDimensional (ZMod 2) (X →ₗ[Λ] P42) := Module.Finite.of_finite
    haveI : FiniteDimensional (ZMod 2) (P42 →ₗ[Λ] X) := Module.Finite.of_finite
    haveI : FiniteDimensional (ZMod 2) (P02 →ₗ[Λ] X) := Module.Finite.of_finite
    let P1 : (X →ₗ[Λ] P02) →ₗ[ZMod 2] ((P42 →ₗ[Λ] X) →ₗ[ZMod 2] ZMod 2) :=
      { toFun := fun g =>
          { toFun := fun w => trPhiP42 (g.comp w)
            map_add' := fun w1 w2 => by rw [LinearMap.comp_add, trPhiP42_add]
            map_smul' := fun c w => by
              have hsc : g.comp (c • w) = c • (g.comp w) := by
                apply LinearMap.ext; intro p
                have := map_smul g (algebraMap (ZMod 2) Λ c) (w p)
                simp only [algebraMap_smul] at this; exact this
              rw [hsc]; unfold trPhiP42
              have hφ : ∀ a : Λ, phiΛ (c • a) = c * phiΛ a := map_smul phiΛ c
              simp only [RingHom.id_apply, smul_eq_mul]
              change phiΛ (c • _) + phiΛ (c • _) = _
              rw [hφ, hφ, mul_add] }
        map_add' := fun g1 g2 => by
          ext w; change trPhiP42 ((g1 + g2).comp w) = trPhiP42 (g1.comp w) + trPhiP42 (g2.comp w)
          rw [LinearMap.add_comp, trPhiP42_add]
        map_smul' := fun c g => by
          ext w; change trPhiP42 ((c • g).comp w) = c * trPhiP42 (g.comp w)
          have hsc : (c • g).comp w = c • (g.comp w) := LinearMap.ext fun _ => rfl
          rw [hsc]; unfold trPhiP42
          have hφ : ∀ a : Λ, phiΛ (c • a) = c * phiΛ a := map_smul phiΛ c
          change phiΛ (c • _) + phiΛ (c • _) = _
          rw [hφ, hφ, mul_add] }
    let P2 : (X →ₗ[Λ] P42) →ₗ[ZMod 2] ((P02 →ₗ[Λ] X) →ₗ[ZMod 2] ZMod 2) :=
      { toFun := fun u =>
          { toFun := fun v => trPhiP02 (u.comp v)
            map_add' := fun v1 v2 => by rw [LinearMap.comp_add, trPhiP02_add]
            map_smul' := fun c v => by
              have hsc : u.comp (c • v) = c • (u.comp v) := by
                apply LinearMap.ext; intro p
                have := map_smul u (algebraMap (ZMod 2) Λ c) (v p)
                simp only [algebraMap_smul] at this; exact this
              rw [hsc]; unfold trPhiP02
              have hφ : ∀ a : Λ, phiΛ (c • a) = c * phiΛ a := map_smul phiΛ c
              simp only [RingHom.id_apply, smul_eq_mul]
              change phiΛ (c • _) + phiΛ (c • _) = _
              rw [hφ, hφ, mul_add] }
        map_add' := fun u1 u2 => by
          ext v; change trPhiP02 ((u1 + u2).comp v) = trPhiP02 (u1.comp v) + trPhiP02 (u2.comp v)
          rw [LinearMap.add_comp, trPhiP02_add]
        map_smul' := fun c u => by
          ext v; change trPhiP02 ((c • u).comp v) = c * trPhiP02 (u.comp v)
          have hsc : (c • u).comp v = c • (u.comp v) := LinearMap.ext fun _ => rfl
          rw [hsc]; unfold trPhiP02
          have hφ : ∀ a : Λ, phiΛ (c • a) = c * phiΛ a := map_smul phiΛ c
          change phiΛ (c • _) + phiΛ (c • _) = _
          rw [hφ, hφ, mul_add] }
    let Bmap : (X →ₗ[Λ] P02) →ₗ[ZMod 2] (X →ₗ[Λ] P42) :=
      { toFun := fun g => (κMν.comp πM).comp g
        map_add' := fun _ _ => LinearMap.comp_add ..
        map_smul' := fun c g => by
          apply LinearMap.ext; intro x
          have := map_smul (κMν.comp πM) (algebraMap (ZMod 2) Λ c) (g x)
          simp only [algebraMap_smul] at this; exact this }
    let Bstar : (P02 →ₗ[Λ] X) →ₗ[ZMod 2] (P42 →ₗ[Λ] X) :=
      { toFun := fun v => v.comp (κM.comp πMν)
        map_add' := fun _ _ => LinearMap.add_comp ..
        map_smul' := fun _ _ => LinearMap.ext fun _ => rfl }
    have hP1L : Function.Injective P1 := (injective_iff_map_eq_zero P1).mpr fun g hg =>
      trPhiP42_nondeg_right g fun w => LinearMap.congr_fun hg w
    have hP1R : Function.Injective P1.flip := (injective_iff_map_eq_zero P1.flip).mpr fun w hw =>
      trPhiP42_nondeg_left w fun g => LinearMap.congr_fun hw g
    have hP2L : Function.Injective P2 := (injective_iff_map_eq_zero P2).mpr fun u hu =>
      trPhiP02_nondeg_right u fun v => LinearMap.congr_fun hu v
    have hP2R : Function.Injective P2.flip := (injective_iff_map_eq_zero P2.flip).mpr fun v hv =>
      trPhiP02_nondeg_left v fun u => LinearMap.congr_fun hv u
    have hadj : ∀ g v, P2 (Bmap g) v = P1 g (Bstar v) := fun g v => by
      have h := trPhi_adj_02_right (κMν.comp πM) v g
      dsimp only at h
      rw [nu_κMν_comp_πM] at h
      exact h
    have hmem : κMν.comp f ∈ LinearMap.range Bmap := by
      rw [mem_range_iff_ortho_ker_adj P1 P2 hP1L hP1R hP2L hP2R Bmap Bstar hadj]
      intro v hv
      have hvκ : v.comp κM = 0 := by
        apply LinearMap.ext; intro z; obtain ⟨q, rfl⟩ := πMν_surj z
        exact LinearMap.congr_fun (LinearMap.mem_ker.mp hv) q
      have hker : LinearMap.ker πM ≤ LinearMap.ker v := by
        rw [ker_πM_eq_range_κM]; rintro _ ⟨z, rfl⟩
        exact LinearMap.congr_fun hvκ z
      choose sec hsec using πM_surj
      have hwd : ∀ p : P02, v (sec (πM p)) = v p := fun p => by
        have hdiff : sec (πM p) - p ∈ LinearMap.ker πM := by
          simp only [LinearMap.mem_ker, map_sub, hsec, sub_self]
        exact sub_eq_zero.mp (by rw [← map_sub]; exact LinearMap.mem_ker.mp (hker hdiff))
      let h : ModM →ₗ[Λ] X :=
        { toFun := fun m => v (sec m)
          map_add' := fun m1 m2 => by
            have := hwd (sec m1 + sec m2)
            rw [map_add, hsec, hsec] at this; rw [this, map_add]
          map_smul' := fun a m => by
            simp only [RingHom.id_apply]
            have := hwd (a • sec m)
            rw [map_smul, hsec] at this; rw [this, map_smul] }
      have hv_eq : v = h.comp πM := LinearMap.ext fun p => (hwd p).symm
      rw [hv_eq]
      exact hortho h
    obtain ⟨g, hg⟩ := hmem
    rw [FactorsThroughProj_to_ModM]
    refine ⟨g, ?_⟩
    apply LinearMap.ext; intro x; apply κMν_inj
    exact (LinearMap.congr_fun hg x).symm

/-- Almost-vanishing of `ρM`: if `f ∘ ρM` does not factor through a projective, then `f` is a split
monomorphism modulo projectives (in fact `∃ g, g ∘ f ≡ id mod rad`). -/
lemma almost_vanish_ρM_left {X : Type} [AddCommGroup X] [Module Λ X]
    [Module (ZMod 2) X] [IsScalarTower (ZMod 2) Λ X] [Fintype X]
    (h : ModM →ₗ[Λ] X) (hnot : ¬ FactorsThroughProj (h.comp ρM)) :
    ∃ f : X →ₗ[Λ] ModM, trPhiP02 (κMν.comp (f.comp (h.comp (ρM.comp πM)))) = 1 := by
  have hex : ∃ f : X →ₗ[Λ] ModM, trPhiP02 (κMν.comp (f.comp ((h.comp ρM).comp πM))) ≠ 0 := by
    by_contra hall; push_neg at hall
    exact hnot ((frobenius_nakayama_left (h.comp ρM)).mpr hall)
  obtain ⟨f, hf⟩ := hex
  refine ⟨f, ?_⟩
  have h01 : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  exact (h01 _).resolve_left hf

/-- The canonical bilinear form `qForm W : Hom_Λ(W, M) × Hom_Λ(M, W) → ZMod 2` measuring the
coefficient of `id_M` in `f ∘ g ∈ End_Λ(M)`. -/
def qForm (W : Type) [AddCommGroup W] [Module Λ W]
    [Module (ZMod 2) W] [IsScalarTower (ZMod 2) Λ W] :
    (W →ₗ[Λ] ModM) →ₗ[ZMod 2] ((ModM →ₗ[Λ] W) →ₗ[ZMod 2] ZMod 2) where
  toFun f :=
    { toFun := fun g => trPhiP02 (κMν.comp (f.comp (g.comp (ρM.comp πM))))
      map_add' := fun g1 g2 => by
        have h : κMν.comp (f.comp ((g1 + g2).comp (ρM.comp πM))) =
            κMν.comp (f.comp (g1.comp (ρM.comp πM))) + κMν.comp (f.comp (g2.comp (ρM.comp πM))) := by
          apply LinearMap.ext; intro p
          simp only [LinearMap.comp_apply, LinearMap.add_apply, map_add]
        exact (congrArg trPhiP02 h).trans (trPhiP02_add _ _)
      map_smul' := fun c g => by
        have h : κMν.comp (f.comp ((c • g).comp (ρM.comp πM))) =
            c • κMν.comp (f.comp (g.comp (ρM.comp πM))) := by
          apply LinearMap.ext; intro p
          have h1 : f (c • g (ρM (πM p))) = c • f (g (ρM (πM p))) := by
            have := map_smul f (algebraMap (ZMod 2) Λ c) (g (ρM (πM p)))
            simp only [algebraMap_smul] at this; exact this
          have h2 : κMν (c • f (g (ρM (πM p)))) = c • κMν (f (g (ρM (πM p)))) := by
            have := map_smul κMν (algebraMap (ZMod 2) Λ c) (f (g (ρM (πM p))))
            simp only [algebraMap_smul] at this; exact this
          exact (congrArg κMν h1).trans h2
        rw [h]; unfold trPhiP02
        have hφ : ∀ a : Λ, phiΛ (c • a) = c * phiΛ a := map_smul phiΛ c
        simp only [RingHom.id_apply, smul_eq_mul]
        change phiΛ (c • _) + phiΛ (c • _) = _
        rw [hφ, hφ, mul_add] }
  map_add' f1 f2 := by
    ext g
    have h : κMν.comp ((f1 + f2).comp (g.comp (ρM.comp πM))) =
        κMν.comp (f1.comp (g.comp (ρM.comp πM))) + κMν.comp (f2.comp (g.comp (ρM.comp πM))) := by
      apply LinearMap.ext; intro p
      simp only [LinearMap.comp_apply, LinearMap.add_apply, map_add]
    exact (congrArg trPhiP02 h).trans (trPhiP02_add _ _)
  map_smul' c f := by
    ext g
    have h : κMν.comp ((c • f).comp (g.comp (ρM.comp πM))) =
        c • κMν.comp (f.comp (g.comp (ρM.comp πM))) := by
      apply LinearMap.ext; intro p
      have := map_smul κMν (algebraMap (ZMod 2) Λ c) (f (g (ρM (πM p))))
      simp only [algebraMap_smul] at this; exact this
    change trPhiP02 (κMν.comp ((c • f).comp (g.comp (ρM.comp πM)))) = c * _
    rw [h]; unfold trPhiP02
    have hφ : ∀ a : Λ, phiΛ (c • a) = c * phiΛ a := map_smul phiΛ c
    change phiΛ (c • _) + phiΛ (c • _) = c * (_ + _)
    rw [hφ, hφ, mul_add]

lemma qForm_eq_comm {W : Type} [AddCommGroup W] [Module Λ W]
    [Module (ZMod 2) W] [IsScalarTower (ZMod 2) Λ W]
    (f : W →ₗ[Λ] ModM) (g : ModM →ₗ[Λ] W) :
    qForm W f g = trPhiP02 (κMν.comp (ρM.comp (f.comp (g.comp πM)))) := by
  have hcomm : FactorsThroughProj ((f.comp g).comp ρM - ρM.comp (f.comp g)) := by
    have hd := endM_decomp (f.comp g)
    have heq : (f.comp g).comp ρM - ρM.comp (f.comp g) = 0 := by
      conv_lhs => rw [hd]
      apply LinearMap.ext; intro x; apply ModM.ext; funext i
      simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.add_apply,
        LinearMap.smul_apply, LinearMap.id_apply, LinearMap.zero_apply]
      have h1 : pM (ρM x) = 0 := LinearMap.congr_fun pM_comp_ρM x
      have h2 : ρM (pM x) = 0 := LinearMap.congr_fun ρM_comp_pM x
      have h3 : ρM (ρM x) = 0 := LinearMap.congr_fun ρM_comp_ρM x
      have h4 : ∀ (c : ZMod 2) (m : ModM), ρM (c • m) = c • ρM m := fun c m => by
        have := map_smul ρM (algebraMap (ZMod 2) Λ c) m
        simp only [algebraMap_smul] at this; exact this
      rw [map_add, map_add, h4, h4, h4, h1, h2, h3]
      simp [sub_self]
    rw [heq]; exact FactorsThroughProj_zero
  have h0 := trPhiP02_factors_eq_zero hcomm
  have hsub : κMν.comp (((f.comp g).comp ρM - ρM.comp (f.comp g)).comp πM) =
      κMν.comp (f.comp (g.comp (ρM.comp πM))) + κMν.comp (ρM.comp (f.comp (g.comp πM))) := by
    apply LinearMap.ext; intro p
    have hneg : ∀ z : ModM, -z = z := fun z => by apply ModM.ext; funext i; exact CharTwo.neg_eq _
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.add_apply, sub_eq_add_neg,
      LinearMap.neg_apply, hneg, map_add]
  rw [hsub, trPhiP02_add] at h0
  exact (CharTwo.add_eq_zero.mp h0)

lemma qForm_eq_id_coeff {W : Type} [AddCommGroup W] [Module Λ W]
    [Module (ZMod 2) W] [IsScalarTower (ZMod 2) Λ W]
    (f : W →ₗ[Λ] ModM) (g : ModM →ₗ[Λ] W) :
    qForm W f g = ((f.comp g) (eVec 0)).vec 0 := by
  have heq : κMν.comp (f.comp (g.comp (ρM.comp πM))) = κMν.comp (((f.comp g).comp ρM).comp πM) :=
    LinearMap.ext fun _ => rfl
  change trPhiP02 (κMν.comp (f.comp (g.comp (ρM.comp πM)))) = _
  rw [heq, trPhiP02_endM]
  have h1 : (f.comp g) (ρM (eVec 0)) = (f.comp g) (eVec 1) := by
    have hρ0 : ρM (eVec 0) = eVec 1 := by
      apply ModM.ext; funext r; change (if r = 1 then (eVec 0).vec 0 else 0) = (eVec 1).vec r; fin_cases r <;> decide
    rw [hρ0]
  have h4 : (f.comp g) (ρM (eVec 4)) = 0 := by
    have hρ4 : ρM (eVec 4) = 0 := by
      apply ModM.ext; funext r; change (if r = 1 then (eVec 4).vec 0 else 0) = 0; fin_cases r <;> decide
    rw [hρ4, map_zero]
  have hL : (((f.comp g).comp ρM) (eVec 0)).vec 1 + (((f.comp g).comp ρM) (eVec 4)).vec 5 =
      ((f.comp g) (eVec 1)).vec 1 := by
    change ((f.comp g) (ρM (eVec 0))).vec 1 + ((f.comp g) (ρM (eVec 4))).vec 5 = _
    rw [h1, h4, vec_zero, add_zero]
  rw [hL]
  conv_lhs => rw [endM_decomp (f.comp g)]
  simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply, pM_apply]
  simp [ρM, eVec]

/-- Existence of a dual basis `(g_i, f_i)` for the nondegenerate quotient of `qForm W`. -/
lemma exists_qForm_dual_basis (W : Type) [AddCommGroup W] [Module Λ W]
    [Module (ZMod 2) W] [IsScalarTower (ZMod 2) Λ W] [Fintype W] :
    ∃ (k : ℕ) (g : Fin k → (ModM →ₗ[Λ] W)) (f : Fin k → (W →ₗ[Λ] ModM)),
      (∀ i j, qForm W (f i) (g j) = if i = j then 1 else 0) ∧
      (∀ u : ModM →ₗ[Λ] W, (∀ i, qForm W (f i) u = 0) → FactorsThroughProj (u.comp ρM)) ∧
      (∀ v : W →ₗ[Λ] ModM, (∀ i, qForm W v (g i) = 0) → FactorsThroughProj (ρM.comp v)) := by
  haveI : FiniteDimensional (ZMod 2) (W →ₗ[Λ] ModM) := Module.Finite.of_finite
  haveI : FiniteDimensional (ZMod 2) (ModM →ₗ[Λ] W) := Module.Finite.of_finite
  let Q := qForm W
  let K : Submodule (ZMod 2) (W →ₗ[Λ] ModM) := LinearMap.ker Q
  let R : Submodule (ZMod 2) ((ModM →ₗ[Λ] W) →ₗ[ZMod 2] ZMod 2) := LinearMap.range Q
  haveI : FiniteDimensional (ZMod 2) R := inferInstance
  let k := Module.finrank (ZMod 2) R
  let bR : Module.Basis (Fin k) (ZMod 2) R := Module.finBasis (ZMod 2) R
  have hlift : ∀ i : Fin k, ∃ fi : W →ₗ[Λ] ModM, Q fi = (bR i).1 := fun i => (bR i).2
  choose f hf using hlift
  let ev : (ModM →ₗ[Λ] W) →ₗ[ZMod 2] (Fin k → ZMod 2) :=
    { toFun := fun u i => Q (f i) u
      map_add' := fun u1 u2 => by ext i; exact map_add (Q (f i)) u1 u2
      map_smul' := fun c u => by ext i; exact map_smul (Q (f i)) c u }
  have hev_surj : Function.Surjective ev := by
    have hlin : LinearIndependent (ZMod 2) (fun i : Fin k => Q (f i)) := by
      have hfun : (fun i : Fin k => Q (f i)) = R.subtype ∘ bR := funext fun i => hf i
      rw [hfun]
      exact bR.linearIndependent.map' R.subtype (Submodule.ker_subtype R)
    by_contra hns
    have hlt : LinearMap.range ev < ⊤ := lt_top_iff_ne_top.mpr fun htop =>
      hns (LinearMap.range_eq_top.mp htop)
    obtain ⟨φ, hφ0, hφ_ker⟩ := Submodule.exists_le_ker_of_lt_top (LinearMap.range ev) hlt
    let c : Fin k → ZMod 2 := fun i => φ (Pi.single i 1)
    have hsum0 : ∑ i : Fin k, c i • Q (f i) = 0 := by
      ext u
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, LinearMap.zero_apply]
      have hu : ev u = ∑ i : Fin k, ev u i • Pi.single i (1 : ZMod 2) := by
        ext j; simp [Finset.sum_apply, Pi.single_apply]
      have h0 : φ (ev u) = 0 := LinearMap.mem_ker.mp (hφ_ker (LinearMap.mem_range_self ev u))
      rw [hu, map_sum] at h0
      simp only [map_smul, smul_eq_mul] at h0
      simpa [c, ev, mul_comm] using h0
    have hc0 : ∀ i, c i = 0 := fun i => Fintype.linearIndependent_iff.mp hlin c hsum0 i
    apply hφ0; apply LinearMap.ext; intro v
    have hv : v = ∑ i : Fin k, v i • Pi.single i (1 : ZMod 2) := by
      ext j; simp [Finset.sum_apply, Pi.single_apply]
    rw [hv, map_sum]; simp [c, hc0]
  choose g hg using fun j : Fin k => hev_surj (Pi.single j 1)
  refine ⟨k, g, f, ?_, ?_, ?_⟩
  · intro i j
    have h := congrFun (hg j) i
    simpa [ev, Pi.single_apply, eq_comm] using h
  · intro u hu
    rw [frobenius_nakayama_left]
    intro v
    have hmem : (⟨Q v, ⟨v, rfl⟩⟩ : R) = ∑ i : Fin k, bR.repr ⟨Q v, ⟨v, rfl⟩⟩ i • bR i :=
      (bR.sum_repr ⟨Q v, ⟨v, rfl⟩⟩).symm
    have hQv : Q v = ∑ i : Fin k, bR.repr ⟨Q v, ⟨v, rfl⟩⟩ i • Q (f i) := by
      have hval := congrArg Subtype.val hmem
      simp only [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul] at hval
      simpa [hf] using hval
    have h0 : Q v u = 0 := by rw [hQv]; simp [Q, hu]
    exact h0
  · intro v hv
    rw [frobenius_nakayama_right]
    intro u
    have hmem : (⟨Q v, ⟨v, rfl⟩⟩ : R) = ∑ i : Fin k, bR.repr ⟨Q v, ⟨v, rfl⟩⟩ i • bR i :=
      (bR.sum_repr ⟨Q v, ⟨v, rfl⟩⟩).symm
    have hQv : Q v = ∑ i : Fin k, bR.repr ⟨Q v, ⟨v, rfl⟩⟩ i • Q (f i) := by
      have hval := congrArg Subtype.val hmem
      simp only [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul] at hval
      simpa [hf] using hval
    have hc0 : ∀ j : Fin k, bR.repr ⟨Q v, ⟨v, rfl⟩⟩ j = 0 := by
      intro j
      have hj := hv j
      rw [hQv] at hj
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] at hj
      have hterm : ∀ i : Fin k, Q (f i) (g j) = if i = j then 1 else 0 := fun i => by
        have := congrFun (hg j) i; simpa [ev, Pi.single_apply, eq_comm] using this
      simp_rw [hterm] at hj
      simpa using hj
    have hQv0 : Q v = 0 := by rw [hQv]; simp [hc0]
    have h0 : Q v u = 0 := by rw [hQv0]; rfl
    rw [qForm_eq_comm] at h0
    exact h0

/-- The canonical natural endomorphism `deltaM W : W →ₗ[Λ] W` (independent of basis mod proj!). -/
noncomputable def deltaM (W : Type) [AddCommGroup W] [Module Λ W]
    [Module (ZMod 2) W] [IsScalarTower (ZMod 2) Λ W] [Fintype W] : W →ₗ[Λ] W :=
  let h := exists_qForm_dual_basis W
  ∑ i : Fin h.choose, (h.choose_spec.choose i).comp (ρM.comp (h.choose_spec.choose_spec.choose i))

lemma deltaM_natural {W1 W2 : Type}
    [AddCommGroup W1] [Module Λ W1] [Module (ZMod 2) W1] [IsScalarTower (ZMod 2) Λ W1] [Fintype W1]
    [AddCommGroup W2] [Module Λ W2] [Module (ZMod 2) W2] [IsScalarTower (ZMod 2) Λ W2] [Fintype W2]
    (φ : W1 →ₗ[Λ] W2) :
    FactorsThroughProj (φ.comp (deltaM W1) - (deltaM W2).comp φ) := by
  unfold deltaM
  set h1 := exists_qForm_dual_basis W1
  set k1 := h1.choose
  set g1 := h1.choose_spec.choose
  set f1 := h1.choose_spec.choose_spec.choose
  obtain ⟨hd1, hr1, hl1⟩ := h1.choose_spec.choose_spec.choose_spec
  change ∀ i j, qForm W1 (f1 i) (g1 j) = if i = j then 1 else 0 at hd1
  set h2 := exists_qForm_dual_basis W2
  set k2 := h2.choose
  set g2 := h2.choose_spec.choose
  set f2 := h2.choose_spec.choose_spec.choose
  obtain ⟨hd2, hr2, hl2⟩ := h2.choose_spec.choose_spec.choose_spec
  change ∀ i j, qForm W2 (f2 i) (g2 j) = if i = j then 1 else 0 at hd2
  let c : Fin k2 → Fin k1 → ZMod 2 := fun j i => qForm W2 (f2 j) (φ.comp (g1 i))
  let mid : W1 →ₗ[Λ] W2 := ∑ i : Fin k1, ∑ j : Fin k2, c j i • ((g2 j).comp (ρM.comp (f1 i)))
  have hL : FactorsThroughProj (φ.comp (∑ i : Fin k1, (g1 i).comp (ρM.comp (f1 i))) - mid) := by
    have heq : φ.comp (∑ i : Fin k1, (g1 i).comp (ρM.comp (f1 i))) - mid =
        ∑ i : Fin k1, ((φ.comp (g1 i) - ∑ j : Fin k2, c j i • g2 j).comp ρM).comp (f1 i) := by
      ext x
      simp only [mid, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.sum_apply,
        LinearMap.smul_apply, map_sum, Finset.sum_sub_distrib]
    rw [heq]
    refine FactorsThroughProj_sum Finset.univ _ fun i _ => FactorsThroughProj_comp_right (hr2 _ ?_) _
    intro j0
    change qForm W2 (f2 j0) (φ.comp (g1 i) - ∑ j : Fin k2, c j i • g2 j) = 0
    rw [map_sub, map_sum]
    simp only [map_smul, smul_eq_mul, hd2]
    simp [c, sub_self]
  have hR : FactorsThroughProj ((∑ j : Fin k2, (g2 j).comp (ρM.comp (f2 j))).comp φ - mid) := by
    have heq : (∑ j : Fin k2, (g2 j).comp (ρM.comp (f2 j))).comp φ - mid =
        ∑ j : Fin k2, (g2 j).comp (ρM.comp ((f2 j).comp φ - ∑ i : Fin k1, c j i • f1 i)) := by
      ext x
      simp only [mid, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.sum_apply,
        LinearMap.smul_apply, map_sum, map_sub]
      rw [Finset.sum_comm, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      have h1s : ρM (c j i • f1 i x) = c j i • ρM (f1 i x) := by
        have := map_smul ρM (algebraMap (ZMod 2) Λ (c j i)) (f1 i x)
        simp only [algebraMap_smul] at this; exact this
      have h2s : g2 j (c j i • ρM (f1 i x)) = c j i • g2 j (ρM (f1 i x)) := by
        have := map_smul (g2 j) (algebraMap (ZMod 2) Λ (c j i)) (ρM (f1 i x))
        simp only [algebraMap_smul] at this; exact this
      rw [h1s, h2s]
    rw [heq]
    refine FactorsThroughProj_sum Finset.univ _ fun j _ => FactorsThroughProj_comp_left _ (hl1 _ ?_)
    intro i0
    change qForm W1 ((f2 j).comp φ - ∑ i : Fin k1, c j i • f1 i) (g1 i0) = 0
    rw [map_sub, map_sum]
    simp only [LinearMap.sub_apply, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
      smul_eq_mul, hd1]
    have hqeq : qForm W1 ((f2 j).comp φ) (g1 i0) = c j i0 := rfl
    rw [hqeq]; simp [sub_self]
  have hdiff : φ.comp (∑ i : Fin k1, (g1 i).comp (ρM.comp (f1 i))) -
      (∑ j : Fin k2, (g2 j).comp (ρM.comp (f2 j))).comp φ =
      (φ.comp (∑ i : Fin k1, (g1 i).comp (ρM.comp (f1 i))) - mid) -
      ((∑ j : Fin k2, (g2 j).comp (ρM.comp (f2 j))).comp φ - mid) := by abel
  rw [hdiff]
  exact FactorsThroughProj_sub hL hR

/-- `deltaM W` is strictly square-zero on the nose! -/
lemma ρM_comp_endM_comp_ρM (u : ModM →ₗ[Λ] ModM) : ρM.comp (u.comp ρM) = 0 := by
  have hd := endM_decomp u
  apply LinearMap.ext; intro x
  simp only [LinearMap.comp_apply, LinearMap.zero_apply]
  rw [hd]
  simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply]
  have h1 : pM (ρM x) = 0 := LinearMap.congr_fun pM_comp_ρM x
  have h2 : ρM (ρM x) = 0 := LinearMap.congr_fun ρM_comp_ρM x
  have hsc : ∀ (c : ZMod 2) (m : ModM), ρM (c • m) = c • ρM m := fun c m => by
    have := map_smul ρM (algebraMap (ZMod 2) Λ c) m
    simp only [algebraMap_smul] at this; exact this
  rw [h1, h2, smul_zero, smul_zero, add_zero, add_zero, hsc, h2, smul_zero]

lemma deltaM_comp_deltaM (W : Type) [AddCommGroup W] [Module Λ W]
    [Module (ZMod 2) W] [IsScalarTower (ZMod 2) Λ W] [Fintype W] :
    (deltaM W).comp (deltaM W) = 0 := by
  unfold deltaM
  set h := exists_qForm_dual_basis W
  set k := h.choose
  set g := h.choose_spec.choose
  set f := h.choose_spec.choose_spec.choose
  apply LinearMap.ext; intro x
  simp only [LinearMap.comp_apply, LinearMap.sum_apply, map_sum, LinearMap.zero_apply]
  refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun i _ => ?_
  have hmid := LinearMap.congr_fun (ρM_comp_endM_comp_ρM ((f i).comp (g j))) (f j x)
  simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hmid
  rw [hmid, map_zero]

/-- Twisted component `deltaMν W` and total natural twist `deltaTotal W = deltaM W + deltaMν W`. -/
noncomputable def deltaMν (W : Type) [AddCommGroup W] [Module Λ W]
    [Module (ZMod 2) W] [IsScalarTower (ZMod 2) Λ W] [Fintype W] : W →ₗ[Λ] W :=
  (Twist.involEquiv (N := W)).toLinearMap.comp
    ((Twist.map (deltaM (Twist W))).comp (Twist.involEquiv (N := W)).symm.toLinearMap)

noncomputable def deltaTotal (W : Type) [AddCommGroup W] [Module Λ W]
    [Module (ZMod 2) W] [IsScalarTower (ZMod 2) Λ W] [Fintype W] : W →ₗ[Λ] W :=
  deltaM W + deltaMν W

lemma deltaMν_natural {W1 W2 : Type}
    [AddCommGroup W1] [Module Λ W1] [Module (ZMod 2) W1] [IsScalarTower (ZMod 2) Λ W1] [Fintype W1]
    [AddCommGroup W2] [Module Λ W2] [Module (ZMod 2) W2] [IsScalarTower (ZMod 2) Λ W2] [Fintype W2]
    (φ : W1 →ₗ[Λ] W2) :
    FactorsThroughProj (φ.comp (deltaMν W1) - (deltaMν W2).comp φ) := by
  have htw := FactorsThroughProj_twist (deltaM_natural (Twist.map φ))
  have heq : φ.comp (deltaMν W1) - (deltaMν W2).comp φ =
      (Twist.involEquiv (N := W2)).toLinearMap.comp
        ((Twist.map ((Twist.map φ).comp (deltaM (Twist W1)) - (deltaM (Twist W2)).comp (Twist.map φ))).comp
          (Twist.involEquiv (N := W1)).symm.toLinearMap) := by
    ext x; rfl
  rw [heq]
  exact FactorsThroughProj_comp_left _ (FactorsThroughProj_comp_right htw _)

lemma deltaTotal_natural {W1 W2 : Type}
    [AddCommGroup W1] [Module Λ W1] [Module (ZMod 2) W1] [IsScalarTower (ZMod 2) Λ W1] [Fintype W1]
    [AddCommGroup W2] [Module Λ W2] [Module (ZMod 2) W2] [IsScalarTower (ZMod 2) Λ W2] [Fintype W2]
    (φ : W1 →ₗ[Λ] W2) :
    FactorsThroughProj (φ.comp (deltaTotal W1) - (deltaTotal W2).comp φ) := by
  have heq : φ.comp (deltaTotal W1) - (deltaTotal W2).comp φ =
      (φ.comp (deltaM W1) - (deltaM W2).comp φ) + (φ.comp (deltaMν W1) - (deltaMν W2).comp φ) := by
    ext x; simp only [deltaTotal, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply, map_add]; abel
  rw [heq]
  exact FactorsThroughProj_add (deltaM_natural φ) (deltaMν_natural φ)

/-- `deltaTotal W` is strictly square-zero on the nose! -/
lemma deltaTotal_comp_deltaTotal (W : Type) [AddCommGroup W] [Module Λ W]
    [Module (ZMod 2) W] [IsScalarTower (ZMod 2) Λ W] [Fintype W] :
    (deltaTotal W).comp (deltaTotal W) = 0 := by
  have h1 : (deltaM W).comp (deltaM W) = 0 := deltaM_comp_deltaM W
  have h4 : (deltaMν W).comp (deltaMν W) = 0 := by
    apply LinearMap.ext; intro x
    have ht := LinearMap.congr_fun (deltaM_comp_deltaM (Twist W)) ⟨x⟩
    exact congrArg Twist.val ht
  have h2 : (deltaM W).comp (deltaMν W) = 0 := by
    apply LinearMap.ext; intro x
    have hd1 : deltaM W = ∑ i : Fin (exists_qForm_dual_basis W).choose,
        ((exists_qForm_dual_basis W).choose_spec.choose i).comp
          (ρM.comp ((exists_qForm_dual_basis W).choose_spec.choose_spec.choose i)) := rfl
    have hd2 : deltaM (Twist W) = ∑ j : Fin (exists_qForm_dual_basis (Twist W)).choose,
        ((exists_qForm_dual_basis (Twist W)).choose_spec.choose j).comp
          (ρM.comp ((exists_qForm_dual_basis (Twist W)).choose_spec.choose_spec.choose j)) := rfl
    have hval : deltaMν W x = ∑ j : Fin (exists_qForm_dual_basis (Twist W)).choose,
        ((exists_qForm_dual_basis (Twist W)).choose_spec.choose j
          (ρM ((exists_qForm_dual_basis (Twist W)).choose_spec.choose_spec.choose j ⟨x⟩))).val := by
      change (deltaM (Twist W) ⟨x⟩).val = _
      rw [hd2, LinearMap.sum_apply]
      induction (Finset.univ : Finset (Fin (exists_qForm_dual_basis (Twist W)).choose)) using Finset.cons_induction with
      | empty => rfl
      | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons]; exact congrArg (_ + ·) ih
    simp only [LinearMap.comp_apply, LinearMap.zero_apply]
    rw [hval, hd1, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    simp only [LinearMap.comp_apply, map_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    let g := (exists_qForm_dual_basis W).choose_spec.choose
    let f := (exists_qForm_dual_basis W).choose_spec.choose_spec.choose
    let gt := (exists_qForm_dual_basis (Twist W)).choose_spec.choose
    let ft := (exists_qForm_dual_basis (Twist W)).choose_spec.choose_spec.choose
    let kmap : Twist ModM →ₗ[Λ] ModM := (f i).comp ((Twist.involEquiv (N := W)).toLinearMap.comp (Twist.map (gt j)))
    have hkill := LinearMap.congr_fun (hom_Twist_ModM_comp_twistρM kmap) ⟨ft j ⟨x⟩⟩
    simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hkill
    change g i (ρM (kmap (Twist.map ρM ⟨ft j ⟨x⟩⟩))) = 0
    rw [hkill, map_zero, map_zero]
  have h3 : (deltaMν W).comp (deltaM W) = 0 := by
    apply LinearMap.ext; intro x
    have hd1 : deltaM W = ∑ i : Fin (exists_qForm_dual_basis W).choose,
        ((exists_qForm_dual_basis W).choose_spec.choose i).comp
          (ρM.comp ((exists_qForm_dual_basis W).choose_spec.choose_spec.choose i)) := rfl
    have hd2 : deltaM (Twist W) = ∑ j : Fin (exists_qForm_dual_basis (Twist W)).choose,
        ((exists_qForm_dual_basis (Twist W)).choose_spec.choose j).comp
          (ρM.comp ((exists_qForm_dual_basis (Twist W)).choose_spec.choose_spec.choose j)) := rfl
    change (deltaM (Twist W) ⟨deltaM W x⟩).val = 0
    have hsum : deltaM (Twist W) ⟨deltaM W x⟩ = 0 := by
      rw [hd2, LinearMap.sum_apply]
      refine Finset.sum_eq_zero fun j _ => ?_
      let g := (exists_qForm_dual_basis W).choose_spec.choose
      let f := (exists_qForm_dual_basis W).choose_spec.choose_spec.choose
      let gt := (exists_qForm_dual_basis (Twist W)).choose_spec.choose
      let ft := (exists_qForm_dual_basis (Twist W)).choose_spec.choose_spec.choose
      have harg : (⟨deltaM W x⟩ : Twist W) =
          ∑ i : Fin (exists_qForm_dual_basis W).choose, ⟨g i (ρM (f i x))⟩ := by
        apply Twist.ext
        rw [hd1, LinearMap.sum_apply]
        induction (Finset.univ : Finset (Fin (exists_qForm_dual_basis W).choose)) using Finset.cons_induction with
        | empty => rfl
        | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons]; exact congrArg (_ + ·) ih
      change gt j (ρM (ft j ⟨deltaM W x⟩)) = 0
      rw [harg, map_sum, map_sum, map_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      let kmap : ModM →ₗ[Λ] Twist ModM := (Twist.map (ft j)).comp ((Twist.involEquiv (N := W)).symm.toLinearMap.comp (g i))
      have hkill := LinearMap.congr_fun (hom_ModM_Twist_comp_ρM kmap) (f i x)
      have hval : ft j ⟨g i (ρM (f i x))⟩ = 0 := congrArg Twist.val hkill
      rw [hval, map_zero, map_zero]
    rw [hsum]; rfl
  apply LinearMap.ext; intro x
  simp only [deltaTotal, LinearMap.comp_apply, LinearMap.add_apply, map_add, LinearMap.zero_apply]
  have e1 := LinearMap.congr_fun h1 x
  have e2 := LinearMap.congr_fun h2 x
  have e3 := LinearMap.congr_fun h3 x
  have e4 := LinearMap.congr_fun h4 x
  simp only [LinearMap.comp_apply, LinearMap.zero_apply] at e1 e2 e3 e4
  simp [e1, e2, e3, e4]

/-- Exact `Λ`-linear involution `epsEquiv W = id + deltaTotal W` on every finite `Λ`-module `W`! -/
noncomputable def epsEquiv (W : Type) [AddCommGroup W] [Module Λ W]
    [Module (ZMod 2) W] [IsScalarTower (ZMod 2) Λ W] [Fintype W] : W ≃ₗ[Λ] W where
  toFun x := x + deltaTotal W x
  invFun x := x + deltaTotal W x
  left_inv x := by
    dsimp only
    have hsq := LinearMap.congr_fun (deltaTotal_comp_deltaTotal W) x
    simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hsq
    rw [map_add, hsq, add_zero, add_assoc]
    have h2 : deltaTotal W x + deltaTotal W x = 0 := by
      have h1 : (1 + 1 : ZMod 2) • deltaTotal W x = 0 := by
        have : (1 + 1 : ZMod 2) = 0 := by decide
        rw [this, zero_smul]
      rwa [add_smul, one_smul] at h1
    rw [h2, add_zero]
  right_inv x := by
    dsimp only
    have hsq := LinearMap.congr_fun (deltaTotal_comp_deltaTotal W) x
    simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hsq
    rw [map_add, hsq, add_zero, add_assoc]
    have h2 : deltaTotal W x + deltaTotal W x = 0 := by
      have h1 : (1 + 1 : ZMod 2) • deltaTotal W x = 0 := by
        have : (1 + 1 : ZMod 2) = 0 := by decide
        rw [this, zero_smul]
      rwa [add_smul, one_smul] at h1
    rw [h2, add_zero]
  map_add' x y := by rw [map_add]; abel
  map_smul' a x := by simp only [RingHom.id_apply, smul_add, map_smul]

lemma deltaTotal_twist (W : Type) [AddCommGroup W] [Module Λ W]
    [Module (ZMod 2) W] [IsScalarTower (ZMod 2) Λ W] [Fintype W] :
    FactorsThroughProj (Twist.map (deltaTotal W) - deltaTotal (Twist W)) := by
  have h1 : FactorsThroughProj (Twist.map (deltaM W) - deltaMν (Twist W)) := by
    have hnat := deltaM_natural (Twist.involEquiv (N := W)).symm.toLinearMap
    have htw := FactorsThroughProj_twist hnat
    have heq : Twist.map (deltaM W) - deltaMν (Twist W) =
        (Twist.involEquiv (N := Twist W)).toLinearMap.comp
          (Twist.map ((Twist.involEquiv (N := W)).symm.toLinearMap.comp (deltaM W) -
            (deltaM (Twist (Twist W))).comp (Twist.involEquiv (N := W)).symm.toLinearMap)) := by
      ext x; rfl
    rw [heq]; exact FactorsThroughProj_comp_left _ htw
  have heq : Twist.map (deltaTotal W) - deltaTotal (Twist W) =
      Twist.map (deltaM W) - deltaMν (Twist W) := by
    apply LinearMap.ext; intro x; apply Twist.ext
    simp only [deltaTotal, LinearMap.sub_apply, LinearMap.add_apply, Twist.map]
    change (deltaM W x.val + deltaMν W x.val) - ((deltaM (Twist W) x).val + (deltaMν (Twist W) x).val) =
      deltaM W x.val - (deltaMν (Twist W) x).val
    have hx : (deltaM (Twist W) x).val = deltaMν W x.val := rfl
    rw [hx]; abel
  rw [heq]; exact h1

lemma deltaTotal_ModM : FactorsThroughProj (deltaTotal ModM - ρM) := by
  have h1 : FactorsThroughProj (deltaM ModM - ρM) := by
    unfold deltaM
    set h := exists_qForm_dual_basis ModM
    set k := h.choose; set g := h.choose_spec.choose; set f := h.choose_spec.choose_spec.choose
    obtain ⟨hd, hr, _⟩ := h.choose_spec.choose_spec.choose_spec
    change ∀ i j, qForm ModM (f i) (g j) = if i = j then 1 else 0 at hd
    let c : Fin k → ZMod 2 := fun i => qForm ModM (f i) LinearMap.id
    have hrad : FactorsThroughProj ((LinearMap.id - ∑ i : Fin k, c i • g i).comp ρM) := by
      apply hr; intro j
      change qForm ModM (f j) (LinearMap.id - ∑ i : Fin k, c i • g i) = 0
      rw [map_sub, map_sum]; simp only [map_smul, smul_eq_mul, hd]; simp [c, sub_self]
    have heq : (∑ i : Fin k, (g i).comp (ρM.comp (f i))) - ρM =
        (∑ i : Fin k, (g i).comp (ρM.comp (f i) - c i • ρM)) -
        ((LinearMap.id - ∑ i : Fin k, c i • g i).comp ρM) := by
      ext x
      simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.sum_apply,
        LinearMap.smul_apply, LinearMap.id_apply, map_sub, Finset.sum_sub_distrib]
      have hsc : ∀ (i : Fin k), g i (c i • ρM x) = c i • g i (ρM x) := fun i => by
        have := map_smul (g i) (algebraMap (ZMod 2) Λ (c i)) (ρM x)
        simp only [algebraMap_smul] at this; exact this
      simp_rw [hsc]; abel
    rw [heq]
    refine FactorsThroughProj_sub (FactorsThroughProj_sum Finset.univ _ fun i _ => ?_) hrad
    apply FactorsThroughProj_comp_left
    have hfi : ρM.comp (f i) - c i • ρM = 0 := by
      have hc : c i = (f i (eVec 0)).vec 0 := qForm_eq_id_coeff (f i) LinearMap.id
      conv_lhs => rw [endM_decomp (f i), hc]
      apply LinearMap.ext; intro x; apply ModM.ext; funext r
      simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.add_apply,
        LinearMap.smul_apply, LinearMap.id_apply, LinearMap.zero_apply]
      have hsc : ∀ (a : ZMod 2) (m : ModM), ρM (a • m) = a • ρM m := fun a m => by
        have := map_smul ρM (algebraMap (ZMod 2) Λ a) m
        simp only [algebraMap_smul] at this; exact this
      have h2 : ρM (ρM x) = 0 := LinearMap.congr_fun ρM_comp_ρM x
      have h3 : ρM (pM x) = 0 := LinearMap.congr_fun ρM_comp_pM x
      rw [map_add, map_add, hsc, hsc, hsc, h2, h3, smul_zero, smul_zero, add_zero, add_zero, sub_self]
    rw [hfi]; exact FactorsThroughProj_zero
  have h2 : FactorsThroughProj (deltaMν ModM) := by
    have hzero : FactorsThroughProj (deltaM (Twist ModM)) := by
      unfold deltaM
      set h := exists_qForm_dual_basis (Twist ModM)
      set k := h.choose; set g := h.choose_spec.choose; set f := h.choose_spec.choose_spec.choose
      exact FactorsThroughProj_sum Finset.univ _ fun i _ =>
        FactorsThroughProj_comp_left _ (FactorsThroughProj_comp_left _ (hom_Twist_ModM_factors (f i)))
    have htw := FactorsThroughProj_twist hzero
    exact FactorsThroughProj_comp_left _ (FactorsThroughProj_comp_right htw _)
  have hdiff : deltaTotal ModM - ρM = (deltaM ModM - ρM) + deltaMν ModM := by
    ext x; simp only [deltaTotal, LinearMap.sub_apply, LinearMap.add_apply]; abel
  rw [hdiff]
  exact FactorsThroughProj_add h1 h2

lemma deltaM_eq_zero_of_qForm_zero (W : Type) [AddCommGroup W] [Module Λ W]
    [Module (ZMod 2) W] [IsScalarTower (ZMod 2) Λ W] [Fintype W]
    (h0 : ∀ f g, qForm W f g = 0) : deltaM W = 0 := by
  unfold deltaM
  set h := exists_qForm_dual_basis W
  set k := h.choose; set g := h.choose_spec.choose; set f := h.choose_spec.choose_spec.choose
  obtain ⟨hd, _, _⟩ := h.choose_spec.choose_spec.choose_spec
  have hk0 : IsEmpty (Fin k) := ⟨fun i => by
    have hi := hd i i
    rw [if_pos rfl, h0] at hi
    exact zero_ne_one hi⟩
  exact Finset.sum_eq_zero fun i _ => (hk0.false i).elim

lemma deltaTotal_eq_zero_of_qForm_zero (W : Type) [AddCommGroup W] [Module Λ W]
    [Module (ZMod 2) W] [IsScalarTower (ZMod 2) Λ W] [Fintype W]
    (h1 : ∀ f g, qForm W f g = 0)
    (h2 : ∀ f g, qForm (Twist W) f g = 0) : deltaTotal W = 0 := by
  unfold deltaTotal deltaMν
  rw [deltaM_eq_zero_of_qForm_zero W h1, deltaM_eq_zero_of_qForm_zero (Twist W) h2]
  apply LinearMap.ext; intro x
  simp only [LinearMap.add_apply, LinearMap.zero_apply, zero_add, LinearMap.comp_apply,
    LinearEquiv.coe_toLinearMap, Twist.map, Twist.involEquiv]
  rfl

end StableModM

end ModuleM

/-
## Part 4: Syzygy Compatibility `deltaTotal_omega` and `Pretriangulated ProjΛ`
-/
section PretriangulatedProj

open ModM CategoryTheory.Pretriangulated

noncomputable abbrev P0Obj (N : Type) [AddCommGroup N] [Module Λ N]
    [Module (ZMod 2) N] [IsScalarTower (ZMod 2) Λ N] [Fintype N] : ProjΛ := ⟨P0 N⟩

noncomputable abbrev P1Obj (N : Type) [AddCommGroup N] [Module Λ N]
    [Module (ZMod 2) N] [IsScalarTower (ZMod 2) Λ N] [Fintype N] : ProjΛ := ⟨P1 N⟩

noncomputable instance instFintypeSubmodule {X : Type} [AddCommGroup X] [Module Λ X]
    [Fintype X] (S : Submodule Λ X) : Fintype S := by
  classical exact inferInstance

lemma neg_eq_self_mod {X : Type*} [AddCommGroup X] [Module (ZMod 2) X] (x : X) : -x = x := by
  have h : (1 + 1 : ZMod 2) • x = 0 := by
    have h2 : (1 + 1 : ZMod 2) = 0 := by decide
    rw [h2, zero_smul]
  rw [add_smul, one_smul] at h
  exact (eq_neg_of_add_eq_zero_left h).symm

lemma add_self_zmod2_mod {X : Type*} [AddCommGroup X] [Module (ZMod 2) X] (x : X) : x + x = 0 := by
  have h : (1 + 1 : ZMod 2) • x = 0 := by
    have h2 : (1 + 1 : ZMod 2) = 0 := by decide
    rw [h2, zero_smul]
  rwa [add_smul, one_smul] at h

lemma neg_hom_eq_self {P Q : ProjΛ} (f : P ⟶ Q) : -f = f :=
  ProjΛ.hom_ext fun x => neg_eq_self_mod (ProjΛ.toLin f x)

lemma shift1_obj_carrier (P : ProjΛ) : (P⟦(1 : ℤ)⟧).carrier = Twist P.carrier := rfl

lemma shift1_map_toLin {P Q : ProjΛ} (f : P ⟶ Q) :
    ProjΛ.toLin (f⟦(1 : ℤ)⟧') = Twist.map (ProjΛ.toLin f) := rfl

/-- Exactness factorization into an injective kernel inclusion. -/
lemma lift_of_ker_eq_range {X K P W : Type*}
    [AddCommGroup X] [Module Λ X] [AddCommGroup K] [Module Λ K]
    [AddCommGroup P] [Module Λ P] [AddCommGroup W] [Module Λ W]
    {ι : K →ₗ[Λ] P} {π : P →ₗ[Λ] W}
    (hι : Function.Injective ι) (hex : LinearMap.ker π = LinearMap.range ι)
    {f : X →ₗ[Λ] P} (hf : π.comp f = 0) :
    ∃ g : X →ₗ[Λ] K, ι.comp g = f := by
  have hmem : ∀ x : X, ∃ k : K, ι k = f x := fun x => by
    have hx : f x ∈ LinearMap.ker π := LinearMap.congr_fun hf x
    rw [hex] at hx
    exact hx
  choose gFun hgFun using hmem
  refine ⟨{
    toFun := gFun
    map_add' := fun x y => hι (by rw [map_add, hgFun, hgFun, hgFun, map_add])
    map_smul' := fun a x => hι (by simp only [RingHom.id_apply, map_smul, hgFun])
  }, LinearMap.ext fun x => hgFun x⟩

/-- Exactness descent from a surjective quotient projection. -/
lemma desc_of_ker_eq_range {K P W Y : Type*}
    [AddCommGroup K] [Module Λ K] [AddCommGroup P] [Module Λ P]
    [AddCommGroup W] [Module Λ W] [AddCommGroup Y] [Module Λ Y]
    {ι : K →ₗ[Λ] P} {π : P →ₗ[Λ] W}
    (hπ : Function.Surjective π) (hex : LinearMap.ker π = LinearMap.range ι)
    {f : P →ₗ[Λ] Y} (hf : f.comp ι = 0) :
    ∃ g : W →ₗ[Λ] Y, g.comp π = f := by
  choose sec hsec using hπ
  have hwd : ∀ p1 p2 : P, π p1 = π p2 → f p1 = f p2 := by
    intro p1 p2 hp
    have hker : p1 - p2 ∈ LinearMap.ker π := by
      simp only [LinearMap.mem_ker, map_sub, hp, sub_self]
    rw [hex] at hker
    obtain ⟨k, hk⟩ := hker
    have hfk : f (p1 - p2) = 0 := by rw [← hk]; exact LinearMap.congr_fun hf k
    rw [map_sub] at hfk
    exact sub_eq_zero.mp hfk
  refine ⟨{
    toFun := fun w => f (sec w)
    map_add' := fun w1 w2 => by
      rw [← map_add]
      exact hwd (sec (w1 + w2)) (sec w1 + sec w2) (by rw [map_add, hsec, hsec, hsec])
    map_smul' := fun a w => by
      simp only [RingHom.id_apply, ← map_smul]
      exact hwd (sec (a • w)) (a • sec w) (by rw [map_smul, hsec, hsec])
  }, LinearMap.ext fun p => hwd (sec (π p)) p (hsec (π p))⟩

/-- Syzygy existence along a pair of short exact sequences with projective middle terms. -/
lemma syzygy_exists {K1 W1 K2 W2 : Type}
    [AddCommGroup K1] [Module Λ K1] [AddCommGroup W1] [Module Λ W1]
    [AddCommGroup K2] [Module Λ K2] [AddCommGroup W2] [Module Λ W2]
    {P1 P2 : ProjΛ}
    {ι1 : K1 →ₗ[Λ] P1.carrier} {π1 : P1.carrier →ₗ[Λ] W1}
    {ι2 : K2 →ₗ[Λ] P2.carrier} {π2 : P2.carrier →ₗ[Λ] W2}
    (h10 : π1.comp ι1 = 0)
    (hι2 : Function.Injective ι2) (hπ2 : Function.Surjective π2)
    (hex2 : LinearMap.ker π2 = LinearMap.range ι2)
    (φ : W1 →ₗ[Λ] W2) :
    ∃ (L : P1.carrier →ₗ[Λ] P2.carrier) (ψ : K1 →ₗ[Λ] K2),
      π2.comp L = φ.comp π1 ∧ ι2.comp ψ = L.comp ι1 := by
  haveI := P1.proj
  obtain ⟨L, hL⟩ := Module.projective_lifting_property π2 (φ.comp π1) hπ2
  have hcomp : π2.comp (L.comp ι1) = 0 := by
    rw [← LinearMap.comp_assoc, hL, LinearMap.comp_assoc, h10, LinearMap.comp_zero]
  obtain ⟨ψ, hψ⟩ := lift_of_ker_eq_range hι2 hex2 hcomp
  exact ⟨L, ψ, hL, hψ⟩

/-- Cosyzygy existence along a pair of short exact sequences with projective (= injective) middle terms. -/
lemma cosyzygy_exists {K1 W1 K2 W2 : Type}
    [AddCommGroup K1] [Module Λ K1] [Module (ZMod 2) K1] [IsScalarTower (ZMod 2) Λ K1]
    [AddCommGroup W1] [Module Λ W1] [Module (ZMod 2) W1] [IsScalarTower (ZMod 2) Λ W1]
    [AddCommGroup K2] [Module Λ K2] [Module (ZMod 2) K2] [IsScalarTower (ZMod 2) Λ K2]
    [AddCommGroup W2] [Module Λ W2] [Module (ZMod 2) W2] [IsScalarTower (ZMod 2) Λ W2]
    {P1 P2 : ProjΛ}
    {ι1 : K1 →ₗ[Λ] P1.carrier} {π1 : P1.carrier →ₗ[Λ] W1}
    {ι2 : K2 →ₗ[Λ] P2.carrier} {π2 : P2.carrier →ₗ[Λ] W2}
    (hι1 : Function.Injective ι1) (hπ1 : Function.Surjective π1)
    (hex1 : LinearMap.ker π1 = LinearMap.range ι1)
    (h20 : π2.comp ι2 = 0)
    (ψ : K1 →ₗ[Λ] K2) :
    ∃ (L : P1.carrier →ₗ[Λ] P2.carrier) (φ : W1 →ₗ[Λ] W2),
      L.comp ι1 = ι2.comp ψ ∧ φ.comp π1 = π2.comp L := by
  obtain ⟨L, hL⟩ := ProjΛ.injective P2 ι1 hι1 (ι2.comp ψ)
  have hcomp : (π2.comp L).comp ι1 = 0 := by
    rw [LinearMap.comp_assoc, hL, ← LinearMap.comp_assoc, h20, LinearMap.zero_comp]
  obtain ⟨φ, hφ⟩ := desc_of_ker_eq_range hπ1 hex1 hcomp
  exact ⟨L, φ, hL, hφ⟩

/-- Uniqueness of syzygies modulo maps factoring through projectives. -/
lemma syzygy_unique_mod_proj {K1 W1 K2 W2 : Type}
    [AddCommGroup K1] [Module Λ K1] [AddCommGroup W1] [Module Λ W1]
    [AddCommGroup K2] [Module Λ K2] [AddCommGroup W2] [Module Λ W2]
    {P1 P2 : ProjΛ}
    {ι1 : K1 →ₗ[Λ] P1.carrier} {π1 : P1.carrier →ₗ[Λ] W1}
    {ι2 : K2 →ₗ[Λ] P2.carrier} {π2 : P2.carrier →ₗ[Λ] W2}
    (hι2 : Function.Injective ι2) (hex2 : LinearMap.ker π2 = LinearMap.range ι2)
    {φ : W1 →ₗ[Λ] W2}
    {L1 L2 : P1.carrier →ₗ[Λ] P2.carrier} {ψ1 ψ2 : K1 →ₗ[Λ] K2}
    (hL1 : π2.comp L1 = φ.comp π1) (hL2 : π2.comp L2 = φ.comp π1)
    (hψ1 : ι2.comp ψ1 = L1.comp ι1) (hψ2 : ι2.comp ψ2 = L2.comp ι1) :
    FactorsThroughProj (ψ1 - ψ2) := by
  have hker : π2.comp (L1 - L2) = 0 := by
    rw [LinearMap.comp_sub, hL1, hL2, sub_self]
  obtain ⟨s, hs⟩ := lift_of_ker_eq_range hι2 hex2 hker
  have heq : ψ1 - ψ2 = s.comp ι1 := by
    apply LinearMap.ext; intro k; apply hι2
    have h1 := LinearMap.congr_fun hψ1 k
    have h2 := LinearMap.congr_fun hψ2 k
    have h3 := LinearMap.congr_fun hs (ι1 k)
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, map_sub] at h1 h2 h3 ⊢
    rw [h1, h2, ← h3]
  rw [heq]
  exact ⟨P1, ι1, s, rfl⟩

/-- Uniqueness of cosyzygies modulo maps factoring through projectives. -/
lemma cosyzygy_unique_mod_proj {K1 W1 K2 W2 : Type}
    [AddCommGroup K1] [Module Λ K1] [AddCommGroup W1] [Module Λ W1]
    [AddCommGroup K2] [Module Λ K2] [AddCommGroup W2] [Module Λ W2]
    {P1 P2 : ProjΛ}
    {ι1 : K1 →ₗ[Λ] P1.carrier} {π1 : P1.carrier →ₗ[Λ] W1}
    {ι2 : K2 →ₗ[Λ] P2.carrier} {π2 : P2.carrier →ₗ[Λ] W2}
    (hπ1 : Function.Surjective π1) (hex1 : LinearMap.ker π1 = LinearMap.range ι1)
    {ψ : K1 →ₗ[Λ] K2}
    {L1 L2 : P1.carrier →ₗ[Λ] P2.carrier} {φ1 φ2 : W1 →ₗ[Λ] W2}
    (hL1 : L1.comp ι1 = ι2.comp ψ) (hL2 : L2.comp ι1 = ι2.comp ψ)
    (hφ1 : φ1.comp π1 = π2.comp L1) (hφ2 : φ2.comp π1 = π2.comp L2) :
    FactorsThroughProj (φ1 - φ2) := by
  have hker : (L1 - L2).comp ι1 = 0 := by
    rw [LinearMap.sub_comp, hL1, hL2, sub_self]
  obtain ⟨s, hs⟩ := desc_of_ker_eq_range hπ1 hex1 hker
  have heq : φ1 - φ2 = π2.comp s := by
    apply LinearMap.ext; intro w
    obtain ⟨p, rfl⟩ := hπ1 w
    have h1 := LinearMap.congr_fun hφ1 p
    have h2 := LinearMap.congr_fun hφ2 p
    have h3 := LinearMap.congr_fun hs p
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, map_sub] at h1 h2 h3 ⊢
    rw [h1, h2, ← map_sub, ← h3]
  rw [heq]
  exact ⟨P2, s, π2, rfl⟩

/-- Syzygy of a map factoring through projectives also factors through projectives. -/
lemma syzygy_of_factors {K1 W1 K2 W2 : Type}
    [AddCommGroup K1] [Module Λ K1] [AddCommGroup W1] [Module Λ W1]
    [AddCommGroup K2] [Module Λ K2] [AddCommGroup W2] [Module Λ W2]
    {P1 P2 : ProjΛ}
    {ι1 : K1 →ₗ[Λ] P1.carrier} {π1 : P1.carrier →ₗ[Λ] W1}
    {ι2 : K2 →ₗ[Λ] P2.carrier} {π2 : P2.carrier →ₗ[Λ] W2}
    (h10 : π1.comp ι1 = 0)
    (hι2 : Function.Injective ι2) (hπ2 : Function.Surjective π2)
    (hex2 : LinearMap.ker π2 = LinearMap.range ι2)
    {φ : W1 →ₗ[Λ] W2} (hφ : FactorsThroughProj φ)
    {L : P1.carrier →ₗ[Λ] P2.carrier} {ψ : K1 →ₗ[Λ] K2}
    (hL : π2.comp L = φ.comp π1) (hψ : ι2.comp ψ = L.comp ι1) :
    FactorsThroughProj ψ := by
  rcases hφ with ⟨Q, g, h, rfl⟩
  haveI := Q.proj
  obtain ⟨h', hh'⟩ := Module.projective_lifting_property π2 h hπ2
  let L0 : P1.carrier →ₗ[Λ] P2.carrier := h'.comp (g.comp π1)
  have hL0 : π2.comp L0 = (h.comp g).comp π1 := by
    ext p; change π2 (h' (g (π1 p))) = h (g (π1 p))
    exact LinearMap.congr_fun hh' (g (π1 p))
  have hψ0 : ι2.comp (0 : K1 →ₗ[Λ] K2) = L0.comp ι1 := by
    ext k; change ι2 0 = h' (g (π1 (ι1 k)))
    have hk : π1 (ι1 k) = 0 := LinearMap.congr_fun h10 k
    rw [hk, map_zero, map_zero, map_zero]
  have hdiff := syzygy_unique_mod_proj hι2 hex2 hL hL0 hψ hψ0
  simpa using hdiff

/-- Cosyzygy of a map factoring through projectives also factors through projectives. -/
lemma cosyzygy_of_factors {K1 W1 K2 W2 : Type}
    [AddCommGroup K1] [Module Λ K1] [Module (ZMod 2) K1] [IsScalarTower (ZMod 2) Λ K1]
    [AddCommGroup W1] [Module Λ W1] [Module (ZMod 2) W1] [IsScalarTower (ZMod 2) Λ W1]
    [AddCommGroup K2] [Module Λ K2] [Module (ZMod 2) K2] [IsScalarTower (ZMod 2) Λ K2]
    [AddCommGroup W2] [Module Λ W2] [Module (ZMod 2) W2] [IsScalarTower (ZMod 2) Λ W2]
    {P1 P2 : ProjΛ}
    {ι1 : K1 →ₗ[Λ] P1.carrier} {π1 : P1.carrier →ₗ[Λ] W1}
    {ι2 : K2 →ₗ[Λ] P2.carrier} {π2 : P2.carrier →ₗ[Λ] W2}
    (hι1 : Function.Injective ι1) (hπ1 : Function.Surjective π1)
    (hex1 : LinearMap.ker π1 = LinearMap.range ι1)
    (h20 : π2.comp ι2 = 0)
    {ψ : K1 →ₗ[Λ] K2} (hψ : FactorsThroughProj ψ)
    {L : P1.carrier →ₗ[Λ] P2.carrier} {φ : W1 →ₗ[Λ] W2}
    (hL : L.comp ι1 = ι2.comp ψ) (hφ : φ.comp π1 = π2.comp L) :
    FactorsThroughProj φ := by
  rcases hψ with ⟨Q, g, h, rfl⟩
  obtain ⟨g', hg'⟩ := ProjΛ.injective Q ι1 hι1 g
  let L0 : P1.carrier →ₗ[Λ] P2.carrier := (ι2.comp h).comp g'
  have hL0 : L0.comp ι1 = ι2.comp (h.comp g) := by
    apply LinearMap.ext; intro k; change ι2 (h (g' (ι1 k))) = ι2 (h (g k))
    exact congrArg (fun x => ι2 (h x)) (LinearMap.congr_fun hg' k)
  have hφ0 : (0 : W1 →ₗ[Λ] W2).comp π1 = π2.comp L0 := by
    apply LinearMap.ext; intro p; change 0 = π2 (ι2 (h (g' p)))
    exact (LinearMap.congr_fun h20 (h (g' p))).symm
  have hdiff := cosyzygy_unique_mod_proj hπ1 hex1 hL hL0 hφ hφ0
  simpa using hdiff

/-- Syzygy invariance of `qForm`: the bilinear form `qForm` is preserved under taking syzygies! -/
lemma qForm_syzygy_eq {K W : Type}
    [AddCommGroup K] [Module Λ K] [Module (ZMod 2) K] [IsScalarTower (ZMod 2) Λ K]
    [AddCommGroup W] [Module Λ W] [Module (ZMod 2) W] [IsScalarTower (ZMod 2) Λ W]
    {P : ProjΛ} {ι : K →ₗ[Λ] P.carrier} {π : P.carrier →ₗ[Λ] W}
    (_hπ_comp_ι : π.comp ι = 0)
    (f : W →ₗ[Λ] ModM) (g : ModM →ₗ[Λ] W)
    {Lf : P.carrier →ₗ[Λ] P02} {f' : K →ₗ[Λ] Twist ModM}
    (hLf : πM.comp Lf = f.comp π) (hf' : κM.comp f' = Lf.comp ι)
    {Lg : P02 →ₗ[Λ] P.carrier} {g' : Twist ModM →ₗ[Λ] K}
    (hLg : π.comp Lg = g.comp πM) (hg' : ι.comp g' = Lg.comp κM) :
    qForm W f g =
      qForm (Twist K)
        ((Twist.involEquiv (N := ModM)).toLinearMap.comp (Twist.map f'))
        ((Twist.map g').comp (Twist.involEquiv (N := ModM)).symm.toLinearMap) := by
  have hc0 : qForm W f g = ((f.comp g) (eVec 0)).vec 0 := qForm_eq_id_coeff f g
  generalize hu_def : f.comp g = u
  rw [hu_def] at hc0
  have hu := endM_decomp u
  let c : ZMod 2 := (u (eVec 0)).vec 0
  let b : ZMod 2 := (u (eVec 0)).vec 1 + (u (eVec 4)).vec 5
  let d : ZMod 2 := (u (eVec 4)).vec 5
  have hc : qForm W f g = c := hc0
  let L0 : P02 →ₗ[Λ] P02 := c • LinearMap.id + b • liftρM
  let ψ0 : Twist ModM →ₗ[Λ] Twist ModM := c • LinearMap.id + b • Twist.map (ρM + pM)
  have hL0 : πM.comp L0 = (c • LinearMap.id + b • ρM).comp πM := by
    apply LinearMap.ext; intro p
    have hsc : ∀ (a : ZMod 2) (q : P02), πM (a • q) = a • πM q := fun a q => by
      have := map_smul πM (algebraMap (ZMod 2) Λ a) q
      simp only [algebraMap_smul] at this; exact this
    simp only [L0, LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply,
      LinearMap.id_apply, map_add, hsc]
    rw [show πM (liftρM p) = ρM (πM p) from LinearMap.congr_fun πM_comp_liftρM p]
  have hψ0 : κM.comp ψ0 = L0.comp κM := by
    apply LinearMap.ext; intro x
    have hsc : ∀ (a : ZMod 2) (z : Twist ModM), κM (a • z) = a • κM z := fun a z => by
      have := map_smul κM (algebraMap (ZMod 2) Λ a) z
      simp only [algebraMap_smul] at this; exact this
    simp only [L0, ψ0, LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply,
      LinearMap.id_apply, map_add, hsc]
    rw [show liftρM (κM x) = κM (Twist.map (ρM + pM) x) from LinearMap.congr_fun liftρM_comp_κM x]
  have hLfg : πM.comp (Lf.comp Lg) = u.comp πM := by
    rw [← hu_def, ← LinearMap.comp_assoc, hLf, LinearMap.comp_assoc, hLg, ← LinearMap.comp_assoc]
  have hψfg : κM.comp (f'.comp g') = (Lf.comp Lg).comp κM := by
    rw [← LinearMap.comp_assoc, hf', LinearMap.comp_assoc, hg', ← LinearMap.comp_assoc]
  have hdiffL : πM.comp (Lf.comp Lg - L0) = (d • pM).comp πM := by
    rw [LinearMap.comp_sub, hLfg, hL0, hu]
    apply LinearMap.ext; intro p; apply ModM.ext; funext r
    simp only [c, b, d, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.add_apply,
      LinearMap.smul_apply, LinearMap.id_apply, vec_add, vec_sub, vec_smul]
    ring
  have hdiffψ : κM.comp (f'.comp g' - ψ0) = (Lf.comp Lg - L0).comp κM := by
    rw [LinearMap.comp_sub, LinearMap.sub_comp, hψfg, hψ0]
  have hfac1 : FactorsThroughProj (f'.comp g' - ψ0) :=
    syzygy_of_factors (P1 := P02Obj) (P2 := P02Obj) πM_comp_κM κM_inj πM_surj ker_πM_eq_range_κM
      (FactorsThroughProj_smul d FactorsThroughProj_pM) hdiffL hdiffψ
  have hfac_pM : FactorsThroughProj (b • Twist.map pM) :=
    FactorsThroughProj_smul b (FactorsThroughProj_twist FactorsThroughProj_pM)
  have hfac2 : FactorsThroughProj (f'.comp g' - (c • LinearMap.id + b • Twist.map ρM)) := by
    have heq : f'.comp g' - (c • LinearMap.id + b • Twist.map ρM) =
        (f'.comp g' - ψ0) + b • Twist.map pM := by
      apply LinearMap.ext; intro x; apply Twist.ext; apply ModM.ext; funext r
      simp only [ψ0, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
        LinearMap.smul_apply, LinearMap.id_apply, Twist.map]
      change (f' (g' x)).val.vec r - (c * x.val.vec r + b * (ρM x.val).vec r) =
        ((f' (g' x)).val.vec r - (c * x.val.vec r + b * ((ρM x.val).vec r + (pM x.val).vec r))) +
          b * (pM x.val).vec r
      ring
    rw [heq]; exact FactorsThroughProj_add hfac1 hfac_pM
  let ftw : Twist K →ₗ[Λ] ModM := (Twist.involEquiv (N := ModM)).toLinearMap.comp (Twist.map f')
  let gtw : ModM →ₗ[Λ] Twist K := (Twist.map g').comp (Twist.involEquiv (N := ModM)).symm.toLinearMap
  have hfac3 : FactorsThroughProj (ftw.comp gtw - (c • LinearMap.id + b • ρM)) := by
    have htw := FactorsThroughProj_twist hfac2
    have heq : ftw.comp gtw - (c • LinearMap.id + b • ρM) =
        (Twist.involEquiv (N := ModM)).toLinearMap.comp
          ((Twist.map (f'.comp g' - (c • LinearMap.id + b • Twist.map ρM))).comp
            (Twist.involEquiv (N := ModM)).symm.toLinearMap) := by
      apply LinearMap.ext; intro x; apply ModM.ext; funext r; rfl
    rw [heq]; exact FactorsThroughProj_comp_left _ (FactorsThroughProj_comp_right htw _)
  have hfac4 : FactorsThroughProj ((ftw.comp gtw).comp ρM - c • ρM) := by
    have hr := FactorsThroughProj_comp_right hfac3 ρM
    have heq : (ftw.comp gtw - (c • LinearMap.id + b • ρM)).comp ρM = (ftw.comp gtw).comp ρM - c • ρM := by
      apply LinearMap.ext; intro x; apply ModM.ext; funext r
      simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.add_apply,
        LinearMap.smul_apply, LinearMap.id_apply]
      have h2 : ρM (ρM x) = 0 := LinearMap.congr_fun ρM_comp_ρM x
      rw [h2, smul_zero, add_zero]
    rwa [heq] at hr
  have htr0 := trPhiP02_factors_eq_zero hfac4
  have hsplit : κMν.comp (((ftw.comp gtw).comp ρM - c • ρM).comp πM) =
      κMν.comp (ftw.comp (gtw.comp (ρM.comp πM))) + c • (κMν.comp (ρM.comp πM)) := by
    apply LinearMap.ext; intro p
    have hsc : ∀ (a : ZMod 2) (m : ModM), κMν (a • m) = a • κMν m := fun a m => by
      have := map_smul κMν (algebraMap (ZMod 2) Λ a) m
      simp only [algebraMap_smul] at this; exact this
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.add_apply,
      LinearMap.smul_apply, sub_eq_add_neg, neg_eq_self_mod, map_add, hsc]
  rw [hsplit, trPhiP02_add] at htr0
  have htrc : trPhiP02 (c • (κMν.comp (ρM.comp πM))) = c := by
    have hsm : ∀ (a : ZMod 2) (T : P02 →ₗ[Λ] P42), trPhiP02 (a • T) = a * trPhiP02 T := fun a T => by
      unfold trPhiP02
      have hφ : ∀ x : Λ, phiΛ (a • x) = a * phiΛ x := map_smul phiΛ a
      change phiΛ (a • _) + phiΛ (a • _) = a * (_ + _)
      rw [hφ, hφ, mul_add]
    rw [hsm, trPhiP02_ρM, mul_one]
  rw [htrc] at htr0
  have hq : qForm (Twist K) ftw gtw = c := CharTwo.add_eq_zero.mp htr0
  rw [hc, hq]

/-- Helper for `deltaM_omega`: right-hand cancellation via cosyzygies and `qForm_syzygy_eq`. -/
private lemma deltaM_omega_right_part {K W : Type}
    [AddCommGroup K] [Module Λ K] [Module (ZMod 2) K] [IsScalarTower (ZMod 2) Λ K] [Fintype K]
    [AddCommGroup W] [Module Λ W] [Module (ZMod 2) W] [IsScalarTower (ZMod 2) Λ W] [Fintype W]
    {P : ProjΛ} {ι : K →ₗ[Λ] P.carrier} {π : P.carrier →ₗ[Λ] W}
    (hι : Function.Injective ι) (hπ : Function.Surjective π)
    (hex : LinearMap.ker π = LinearMap.range ι) (hπ_comp_ι : π.comp ι = 0)
    {k1 : ℕ} {g1 : Fin k1 → (ModM →ₗ[Λ] W)} {f1 : Fin k1 → (W →ₗ[Λ] ModM)}
    (hd1 : ∀ i j, qForm W (f1 i) (g1 j) = if i = j then 1 else 0)
    (hl1 : ∀ f : W →ₗ[Λ] ModM, (∀ i, qForm W f (g1 i) = 0) → FactorsThroughProj (ρM.comp f))
    {Lf : Fin k1 → (P.carrier →ₗ[Λ] P02)} {f1' : Fin k1 → (K →ₗ[Λ] Twist ModM)}
    (hLf : ∀ i, πM.comp (Lf i) = (f1 i).comp π) (hf1' : ∀ i, κM.comp (f1' i) = (Lf i).comp ι)
    {Lg : Fin k1 → (P02 →ₗ[Λ] P.carrier)} {g1' : Fin k1 → (Twist ModM →ₗ[Λ] K)}
    (hLg : ∀ i, π.comp (Lg i) = (g1 i).comp πM) (hg1' : ∀ i, ι.comp (g1' i) = (Lg i).comp κM)
    (f2j : Twist K →ₗ[Λ] ModM) (u : ModM →ₗ[Λ] Twist K) :
    let g1tw : Fin k1 → (ModM →ₗ[Λ] Twist K) := fun i =>
      (Twist.map (g1' i)).comp (Twist.involEquiv (N := ModM)).symm.toLinearMap
    let f1tw : Fin k1 → (Twist K →ₗ[Λ] ModM) := fun i =>
      (Twist.involEquiv (N := ModM)).toLinearMap.comp (Twist.map (f1' i))
    qForm (Twist K) (f2j - ∑ i : Fin k1, qForm (Twist K) f2j (g1tw i) • f1tw i) u = 0 := by
  intro g1tw f1tw
  let c : Fin k1 → ZMod 2 := fun i => qForm (Twist K) f2j (g1tw i)
  let f2un : K →ₗ[Λ] Twist ModM := (Twist.map f2j).comp (Twist.involEquiv (N := K)).symm.toLinearMap
  let uun : Twist ModM →ₗ[Λ] K := (Twist.involEquiv (N := K)).toLinearMap.comp (Twist.map u)
  obtain ⟨Lv, vW, hLv1, hLv2⟩ :=
    cosyzygy_exists (P1 := P) (P2 := P02Obj) hι hπ hex πM_comp_κM f2un
  obtain ⟨Lu, uW, hLu1, hLu2⟩ :=
    cosyzygy_exists (P1 := P02Obj) (P2 := P) κM_inj πM_surj ker_πM_eq_range_κM hπ_comp_ι uun
  have hf2eq : (Twist.involEquiv (N := ModM)).toLinearMap.comp (Twist.map f2un) = f2j :=
    LinearMap.ext fun _ => rfl
  have hueq : (Twist.map uun).comp (Twist.involEquiv (N := ModM)).symm.toLinearMap = u :=
    LinearMap.ext fun _ => rfl
  have hq_vW_uW : qForm (Twist K) f2j u = qForm W vW uW := by
    rw [← hf2eq, ← hueq]
    exact (qForm_syzygy_eq hπ_comp_ι vW uW hLv2.symm hLv1.symm hLu2.symm hLu1.symm).symm
  have hq_f1_uW : ∀ i : Fin k1, qForm (Twist K) (f1tw i) u = qForm W (f1 i) uW := fun i => by
    rw [← hueq]
    exact (qForm_syzygy_eq hπ_comp_ι (f1 i) uW (hLf i) (hf1' i) hLu2.symm hLu1.symm).symm
  have hc_eq : ∀ i : Fin k1, c i = qForm W vW (g1 i) := fun i => by
    change qForm (Twist K) f2j (g1tw i) = qForm W vW (g1 i)
    rw [← hf2eq]
    exact (qForm_syzygy_eq hπ_comp_ι vW (g1 i) hLv2.symm hLv1.symm (hLg i) (hg1' i)).symm
  have hradW : FactorsThroughProj (ρM.comp (vW - ∑ i : Fin k1, c i • f1 i)) := by
    apply hl1; intro i0
    change qForm W (vW - ∑ i : Fin k1, c i • f1 i) (g1 i0) = 0
    rw [map_sub, map_sum]
    simp only [LinearMap.sub_apply, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
      smul_eq_mul, hd1]
    simp [hc_eq i0, sub_self]
  have hq0 : qForm W (vW - ∑ i : Fin k1, c i • f1 i) uW = 0 := by
    rw [qForm_eq_comm]
    have heq : κMν.comp (ρM.comp ((vW - ∑ i : Fin k1, c i • f1 i).comp (uW.comp πM))) =
        κMν.comp (((ρM.comp (vW - ∑ i : Fin k1, c i • f1 i)).comp uW).comp πM) :=
      LinearMap.ext fun _ => rfl
    rw [heq]
    exact trPhiP02_factors_eq_zero (FactorsThroughProj_comp_right hradW uW)
  have hL1 : qForm (Twist K) (f2j - ∑ i : Fin k1, c i • f1tw i) u =
      qForm (Twist K) f2j u - ∑ i : Fin k1, c i * qForm (Twist K) (f1tw i) u := by
    have := LinearMap.congr_fun (map_sub (qForm (Twist K)) f2j (∑ i : Fin k1, c i • f1tw i)) u
    simp only [LinearMap.sub_apply, map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
      smul_eq_mul] at this
    exact this
  have hR1 : qForm W (vW - ∑ i : Fin k1, c i • f1 i) uW =
      qForm W vW uW - ∑ i : Fin k1, c i * qForm W (f1 i) uW := by
    have := LinearMap.congr_fun (map_sub (qForm W) vW (∑ i : Fin k1, c i • f1 i)) uW
    simp only [LinearMap.sub_apply, map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
      smul_eq_mul] at this
    exact this
  rw [hL1, hq_vW_uW]
  have hsum : ∑ i : Fin k1, c i * qForm (Twist K) (f1tw i) u = ∑ i : Fin k1, c i * qForm W (f1 i) uW :=
    Finset.sum_congr rfl fun i _ => congrArg (c i * ·) (hq_f1_uW i)
  rw [hsum, ← hR1, hq0]

/-- Syzygy compatibility of `deltaM`: syzygy of `deltaM W` agrees with `deltaMν K` modulo projectives. -/
lemma deltaM_omega {K W : Type}
    [AddCommGroup K] [Module Λ K] [Module (ZMod 2) K] [IsScalarTower (ZMod 2) Λ K] [Fintype K]
    [AddCommGroup W] [Module Λ W] [Module (ZMod 2) W] [IsScalarTower (ZMod 2) Λ W] [Fintype W]
    {P : ProjΛ} {ι : K →ₗ[Λ] P.carrier} {π : P.carrier →ₗ[Λ] W}
    (hι : Function.Injective ι) (hπ : Function.Surjective π)
    (hex : LinearMap.ker π = LinearMap.range ι)
    {L : P.carrier →ₗ[Λ] P.carrier} {dK : K →ₗ[Λ] K}
    (hL : π.comp L = (deltaM W).comp π) (hdK : ι.comp dK = L.comp ι) :
    FactorsThroughProj (dK - deltaMν K) := by
  have hπ_comp_ι : π.comp ι = 0 := by
    apply LinearMap.ext; intro k; change π (ι k) = 0
    exact LinearMap.mem_ker.mp (hex.symm ▸ LinearMap.mem_range_self ι k)
  set h1 := exists_qForm_dual_basis W
  set k1 := h1.choose
  set g1 := h1.choose_spec.choose
  set f1 := h1.choose_spec.choose_spec.choose
  obtain ⟨hd1, hr1, hl1⟩ := h1.choose_spec.choose_spec.choose_spec
  change ∀ i j, qForm W (f1 i) (g1 j) = if i = j then 1 else 0 at hd1
  have hsf : ∀ i : Fin k1, ∃ (Lf : P.carrier →ₗ[Λ] P02) (f' : K →ₗ[Λ] Twist ModM),
      πM.comp Lf = (f1 i).comp π ∧ κM.comp f' = Lf.comp ι := fun i =>
    syzygy_exists (P1 := P) (P2 := P02Obj) hπ_comp_ι κM_inj πM_surj ker_πM_eq_range_κM (f1 i)
  choose Lf f1' hLf hf1' using hsf
  have hsg : ∀ i : Fin k1, ∃ (Lg : P02 →ₗ[Λ] P.carrier) (g' : Twist ModM →ₗ[Λ] K),
      π.comp Lg = (g1 i).comp πM ∧ ι.comp g' = Lg.comp κM := fun i =>
    syzygy_exists (P1 := P02Obj) (P2 := P) πM_comp_κM hι hπ hex (g1 i)
  choose Lg g1' hLg hg1' using hsg
  let Lsum : P.carrier →ₗ[Λ] P.carrier := ∑ i : Fin k1, (Lg i).comp (liftρM.comp (Lf i))
  let dKsum : K →ₗ[Λ] K := ∑ i : Fin k1, (g1' i).comp ((Twist.map (ρM + pM)).comp (f1' i))
  have hdM1 : deltaM W = ∑ i : Fin k1, (g1 i).comp (ρM.comp (f1 i)) := rfl
  have hLsum : π.comp Lsum = (deltaM W).comp π := by
    apply LinearMap.ext; intro p
    rw [hdM1]
    simp only [Lsum, LinearMap.comp_apply, LinearMap.sum_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 := LinearMap.congr_fun (hLg i) (liftρM (Lf i p))
    have h2 := LinearMap.congr_fun πM_comp_liftρM (Lf i p)
    have h3 := LinearMap.congr_fun (hLf i) p
    simp only [LinearMap.comp_apply] at h1 h2 h3
    rw [h1, h2, h3]
  have hdKsum : ι.comp dKsum = Lsum.comp ι := by
    apply LinearMap.ext; intro k
    simp only [dKsum, Lsum, LinearMap.comp_apply, LinearMap.sum_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 := LinearMap.congr_fun (hg1' i) (Twist.map (ρM + pM) (f1' i k))
    have h2 := LinearMap.congr_fun liftρM_comp_κM (f1' i k)
    have h3 := LinearMap.congr_fun (hf1' i) k
    simp only [LinearMap.comp_apply] at h1 h2 h3
    rw [h1, ← h2, h3]
  have hstep1 : FactorsThroughProj (dK - dKsum) :=
    syzygy_unique_mod_proj hι hex hL hLsum hdK hdKsum
  let dKρ : K →ₗ[Λ] K := ∑ i : Fin k1, (g1' i).comp ((Twist.map ρM).comp (f1' i))
  have hstep1b : FactorsThroughProj (dKsum - dKρ) := by
    have heq : dKsum - dKρ = ∑ i : Fin k1, (g1' i).comp ((Twist.map pM).comp (f1' i)) := by
      apply LinearMap.ext; intro k
      simp only [dKsum, dKρ, LinearMap.sub_apply, LinearMap.sum_apply, LinearMap.comp_apply,
        ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← map_sub]
      refine congrArg (g1' i) (Twist.ext ?_)
      change (ρM (f1' i k).val + pM (f1' i k).val) - ρM (f1' i k).val = pM (f1' i k).val
      abel
    rw [heq]
    exact FactorsThroughProj_sum Finset.univ _ fun i _ =>
      FactorsThroughProj_comp_left _ (FactorsThroughProj_comp_right (FactorsThroughProj_twist FactorsThroughProj_pM) _)
  have hstep2 : FactorsThroughProj (Twist.map dKρ - deltaM (Twist K)) := by
    set h2 := exists_qForm_dual_basis (Twist K)
    set k2 := h2.choose
    set g2 := h2.choose_spec.choose
    set f2 := h2.choose_spec.choose_spec.choose
    obtain ⟨hd2, hr2, _⟩ := h2.choose_spec.choose_spec.choose_spec
    change ∀ i j, qForm (Twist K) (f2 i) (g2 j) = if i = j then 1 else 0 at hd2
    let g1tw : Fin k1 → (ModM →ₗ[Λ] Twist K) := fun i =>
      (Twist.map (g1' i)).comp (Twist.involEquiv (N := ModM)).symm.toLinearMap
    let f1tw : Fin k1 → (Twist K →ₗ[Λ] ModM) := fun i =>
      (Twist.involEquiv (N := ModM)).toLinearMap.comp (Twist.map (f1' i))
    have htw_dKρ : Twist.map dKρ = ∑ i : Fin k1, (g1tw i).comp (ρM.comp (f1tw i)) := by
      apply LinearMap.ext; intro x; apply Twist.ext
      simp only [dKρ, Twist.map, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.sum_apply, LinearMap.comp_apply]
      induction (Finset.univ : Finset (Fin k1)) using Finset.cons_induction with
      | empty => rfl
      | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons]; exact congrArg (_ + ·) ih
    have hdM2 : deltaM (Twist K) = ∑ j : Fin k2, (g2 j).comp (ρM.comp (f2 j)) := rfl
    rw [htw_dKρ, hdM2]
    let c : Fin k2 → Fin k1 → ZMod 2 := fun j i => qForm (Twist K) (f2 j) (g1tw i)
    let mid : Twist K →ₗ[Λ] Twist K := ∑ i : Fin k1, ∑ j : Fin k2, c j i • ((g2 j).comp (ρM.comp (f1tw i)))
    have hLpart : FactorsThroughProj ((∑ i : Fin k1, (g1tw i).comp (ρM.comp (f1tw i))) - mid) := by
      have heq : (∑ i : Fin k1, (g1tw i).comp (ρM.comp (f1tw i))) - mid =
          ∑ i : Fin k1, ((g1tw i - ∑ j : Fin k2, c j i • g2 j).comp ρM).comp (f1tw i) := by
        apply LinearMap.ext; intro x
        simp only [mid, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.sum_apply,
          LinearMap.smul_apply, Finset.sum_sub_distrib]
      rw [heq]
      refine FactorsThroughProj_sum Finset.univ _ fun i _ => FactorsThroughProj_comp_right (hr2 _ ?_) _
      intro j0
      change qForm (Twist K) (f2 j0) (g1tw i - ∑ j : Fin k2, c j i • g2 j) = 0
      rw [map_sub, map_sum]; simp only [map_smul, smul_eq_mul, hd2]; simp [c, sub_self]
    have hRpart : FactorsThroughProj ((∑ j : Fin k2, (g2 j).comp (ρM.comp (f2 j))) - mid) := by
      have heq : (∑ j : Fin k2, (g2 j).comp (ρM.comp (f2 j))) - mid =
          ∑ j : Fin k2, (g2 j).comp (ρM.comp (f2 j - ∑ i : Fin k1, c j i • f1tw i)) := by
        apply LinearMap.ext; intro x
        simp only [mid, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.sum_apply,
          LinearMap.smul_apply, map_sum, map_sub]
        rw [Finset.sum_comm, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        have h1s : ρM (c j i • f1tw i x) = c j i • ρM (f1tw i x) := by
          have := map_smul ρM (algebraMap (ZMod 2) Λ (c j i)) (f1tw i x)
          simp only [algebraMap_smul] at this; exact this
        have h2s : g2 j (c j i • ρM (f1tw i x)) = c j i • g2 j (ρM (f1tw i x)) := by
          have := map_smul (g2 j) (algebraMap (ZMod 2) Λ (c j i)) (ρM (f1tw i x))
          simp only [algebraMap_smul] at this; exact this
        rw [h1s, h2s]
      rw [heq]
      refine FactorsThroughProj_sum Finset.univ _ fun j _ => FactorsThroughProj_comp_left _ ?_
      rw [frobenius_nakayama_right]
      intro u
      have h0 := deltaM_omega_right_part hι hπ hex hπ_comp_ι hd1 hl1 hLf hf1' hLg hg1' (f2 j) u
      dsimp only at h0
      rwa [qForm_eq_comm] at h0
    have hdiff : (∑ i : Fin k1, (g1tw i).comp (ρM.comp (f1tw i))) -
        (∑ j : Fin k2, (g2 j).comp (ρM.comp (f2 j))) =
        ((∑ i : Fin k1, (g1tw i).comp (ρM.comp (f1tw i))) - mid) -
        ((∑ j : Fin k2, (g2 j).comp (ρM.comp (f2 j))) - mid) := by abel
    rw [hdiff]; exact FactorsThroughProj_sub hLpart hRpart
  have hstep2_un : FactorsThroughProj (dKρ - deltaMν K) := by
    rw [← FactorsThroughProj_iff_twist]
    have heq : Twist.map (dKρ - deltaMν K) = Twist.map dKρ - deltaM (Twist K) := by
      ext x; rfl
    rw [heq]; exact hstep2
  have hcomb : dK - deltaMν K = (dK - dKsum) + (dKsum - dKρ) + (dKρ - deltaMν K) := by abel
  rw [hcomb]
  exact FactorsThroughProj_add (FactorsThroughProj_add hstep1 hstep1b) hstep2_un

/-- Syzygy compatibility of `deltaMν`: syzygy of `deltaMν W` agrees with `deltaM K` modulo projectives. -/
lemma deltaMν_omega {K W : Type}
    [AddCommGroup K] [Module Λ K] [Module (ZMod 2) K] [IsScalarTower (ZMod 2) Λ K] [Fintype K]
    [AddCommGroup W] [Module Λ W] [Module (ZMod 2) W] [IsScalarTower (ZMod 2) Λ W] [Fintype W]
    {P : ProjΛ} {ι : K →ₗ[Λ] P.carrier} {π : P.carrier →ₗ[Λ] W}
    (hι : Function.Injective ι) (hπ : Function.Surjective π)
    (hex : LinearMap.ker π = LinearMap.range ι)
    {L : P.carrier →ₗ[Λ] P.carrier} {dK : K →ₗ[Λ] K}
    (hL : π.comp L = (deltaMν W).comp π) (hdK : ι.comp dK = L.comp ι) :
    FactorsThroughProj (dK - deltaM K) := by
  have hιt : Function.Injective (Twist.map ι) := fun x y hxy =>
    Twist.ext (hι (congrArg Twist.val hxy))
  have hπt : Function.Surjective (Twist.map π) := fun w => by
    obtain ⟨p, hp⟩ := hπ w.val
    exact ⟨⟨p⟩, Twist.ext hp⟩
  have hext : LinearMap.ker (Twist.map π) = LinearMap.range (Twist.map ι) := by
    ext p; simp only [LinearMap.mem_ker, LinearMap.mem_range]
    constructor
    · intro hp
      have hp' : p.val ∈ LinearMap.ker π := congrArg Twist.val hp
      rw [hex] at hp'
      obtain ⟨k, hk⟩ := hp'
      exact ⟨⟨k⟩, Twist.ext hk⟩
    · rintro ⟨k, rfl⟩
      apply Twist.ext
      exact LinearMap.mem_ker.mp (hex.symm ▸ LinearMap.mem_range_self ι k.val)
  have hLt : (Twist.map π).comp (Twist.map L) = (deltaM (Twist W)).comp (Twist.map π) := by
    apply LinearMap.ext; intro p; apply Twist.ext
    exact LinearMap.congr_fun hL p.val
  have hdKt : (Twist.map ι).comp (Twist.map dK) = (Twist.map L).comp (Twist.map ι) := by
    apply LinearMap.ext; intro k; apply Twist.ext
    exact LinearMap.congr_fun hdK k.val
  have h1 := deltaM_omega (P := ProjΛ.nuObj P) hιt hπt hext hLt hdKt
  have htw : FactorsThroughProj (Twist.map (deltaM K) - deltaMν (Twist K)) := by
    have hnat := deltaM_natural (Twist.involEquiv (N := K)).symm.toLinearMap
    have h2 := FactorsThroughProj_twist hnat
    have heq : Twist.map (deltaM K) - deltaMν (Twist K) =
        (Twist.involEquiv (N := Twist K)).toLinearMap.comp
          (Twist.map ((Twist.involEquiv (N := K)).symm.toLinearMap.comp (deltaM K) -
            (deltaM (Twist (Twist K))).comp (Twist.involEquiv (N := K)).symm.toLinearMap)) := by
      ext x; rfl
    rw [heq]; exact FactorsThroughProj_comp_left _ h2
  rw [← FactorsThroughProj_iff_twist]
  have heq : Twist.map (dK - deltaM K) =
      (Twist.map dK - deltaMν (Twist K)) - (Twist.map (deltaM K) - deltaMν (Twist K)) := by
    apply LinearMap.ext; intro x; apply Twist.ext
    simp only [LinearMap.sub_apply, Twist.map]
    change dK x.val - deltaM K x.val = (dK x.val - (deltaMν (Twist K) x).val) - (deltaM K x.val - (deltaMν (Twist K) x).val)
    abel
  rw [heq]; exact FactorsThroughProj_sub h1 htw

/-- Full Heller syzygy compatibility: syzygy of `deltaTotal W` agrees with `deltaTotal K` modulo projectives! -/
lemma deltaTotal_omega {K W : Type}
    [AddCommGroup K] [Module Λ K] [Module (ZMod 2) K] [IsScalarTower (ZMod 2) Λ K] [Fintype K]
    [AddCommGroup W] [Module Λ W] [Module (ZMod 2) W] [IsScalarTower (ZMod 2) Λ W] [Fintype W]
    {P : ProjΛ} {ι : K →ₗ[Λ] P.carrier} {π : P.carrier →ₗ[Λ] W}
    (hι : Function.Injective ι) (hπ : Function.Surjective π)
    (hex : LinearMap.ker π = LinearMap.range ι)
    {L : P.carrier →ₗ[Λ] P.carrier} {dK : K →ₗ[Λ] K}
    (hL : π.comp L = (deltaTotal W).comp π) (hdK : ι.comp dK = L.comp ι) :
    FactorsThroughProj (dK - deltaTotal K) := by
  have hπ_comp_ι : π.comp ι = 0 := by
    apply LinearMap.ext; intro k; change π (ι k) = 0
    exact LinearMap.mem_ker.mp (hex.symm ▸ LinearMap.mem_range_self ι k)
  obtain ⟨L1, dK1, hL1, hdK1⟩ := syzygy_exists hπ_comp_ι hι hπ hex (deltaM W)
  obtain ⟨L2, dK2, hL2, hdK2⟩ := syzygy_exists hπ_comp_ι hι hπ hex (deltaMν W)
  have hL12 : π.comp (L1 + L2) = (deltaTotal W).comp π := by
    rw [LinearMap.comp_add, hL1, hL2]; ext p; rfl
  have hdK12 : ι.comp (dK1 + dK2) = (L1 + L2).comp ι := by
    rw [LinearMap.comp_add, LinearMap.add_comp, hdK1, hdK2]
  have hu := syzygy_unique_mod_proj hι hex hL hL12 hdK hdK12
  have h1 := deltaM_omega hι hπ hex hL1 hdK1
  have h2 := deltaMν_omega hι hπ hex hL2 hdK2
  have heq : dK - deltaTotal K = (dK - (dK1 + dK2)) + (dK1 - deltaMν K) + (dK2 - deltaM K) := by
    ext k; simp only [deltaTotal, LinearMap.sub_apply, LinearMap.add_apply]; abel
  rw [heq]; exact FactorsThroughProj_add (FactorsThroughProj_add hu h1) h2

/-- Canonical embedding `K ↪ P0 (Twist K)` from the 3-term bimodule resolution. -/
def resJK (K : Type*) [AddCommGroup K] [Module Λ K]
    [Module (ZMod 2) K] [IsScalarTower (ZMod 2) Λ K] :
    K →ₗ[Λ] P0 (Twist K) :=
  (resJ (Twist K)).comp (Twist.involEquiv (N := K)).symm.toLinearMap

lemma resJK_inj {K : Type*} [AddCommGroup K] [Module Λ K]
    [Module (ZMod 2) K] [IsScalarTower (ZMod 2) Λ K] :
    Function.Injective (resJK K) :=
  resJ_inj.comp (Twist.involEquiv (N := K)).symm.injective

lemma resD2_comp_resJK {K : Type*} [AddCommGroup K] [Module Λ K]
    [Module (ZMod 2) K] [IsScalarTower (ZMod 2) Λ K] :
    (resD2 (Twist K)).comp (resJK K) = 0 :=
  LinearMap.ext fun k => resD2_comp_resJ (N := Twist K) ⟨⟨k⟩⟩

lemma ker_resD2_eq_range_resJK {K : Type*} [AddCommGroup K] [Module Λ K]
    [Module (ZMod 2) K] [IsScalarTower (ZMod 2) Λ K] :
    LinearMap.ker (resD2 (Twist K)) = LinearMap.range (resJK K) := by
  rw [ker_resD2_eq_range_resJ]
  ext f; simp only [LinearMap.mem_range, resJK, LinearMap.comp_apply]
  constructor
  · rintro ⟨x, rfl⟩; exact ⟨x.val.val, rfl⟩
  · rintro ⟨k, rfl⟩; exact ⟨⟨⟨k⟩⟩, rfl⟩

lemma resJK_nat {K1 K2 : Type*} [AddCommGroup K1] [Module Λ K1]
    [Module (ZMod 2) K1] [IsScalarTower (ZMod 2) Λ K1]
    [AddCommGroup K2] [Module Λ K2] [Module (ZMod 2) K2] [IsScalarTower (ZMod 2) Λ K2]
    (φ : K1 →ₗ[Λ] K2) :
    (P0.map (Twist.map φ)).comp (resJK K1) = (resJK K2).comp φ := by
  apply LinearMap.ext; intro k; apply P0.ext; funext u
  exact congrFun (congrArg P0.fn (LinearMap.congr_fun (resJ_nat (Twist.map φ)) ⟨⟨k⟩⟩)) u

/-- Exactness predicate for a triangle `X -f→ Y -g→ Z -h→ Twist X` in `ProjΛ`. -/
def IsExact3 (T : Triangle ProjΛ) : Prop :=
  LinearMap.ker (ProjΛ.toLin T.mor₂) = LinearMap.range (ProjΛ.toLin T.mor₁) ∧
  LinearMap.ker (ProjΛ.toLin T.mor₃) = LinearMap.range (ProjΛ.toLin T.mor₂) ∧
  LinearMap.ker (Twist.map (ProjΛ.toLin T.mor₁)) = LinearMap.range (ProjΛ.toLin T.mor₃)

/-- Kernel module `K = ker(T.mor₁)` of a triangle in `ProjΛ`. -/
abbrev kerT (T : Triangle ProjΛ) : Submodule Λ T.obj₁.carrier :=
  LinearMap.ker (ProjΛ.toLin T.mor₁)

/-- Canonical inclusion `kerT T ↪ T.obj₁`. -/
def inclKerT (T : Triangle ProjΛ) : kerT T →ₗ[Λ] T.obj₁.carrier :=
  (kerT T).subtype

lemma inclKerT_inj (T : Triangle ProjΛ) : Function.Injective (inclKerT T) :=
  Submodule.injective_subtype _

/-- Surjective factorization `T.obj₃ ↠ Twist (kerT T)` of `T.mor₃` for an exact triangle `T`. -/
def surjMor3 (T : Triangle ProjΛ) (hT : IsExact3 T) :
    T.obj₃.carrier →ₗ[Λ] Twist (kerT T) where
  toFun z := ⟨⟨(ProjΛ.toLin T.mor₃ z).val, by
    have hmem : ProjΛ.toLin T.mor₃ z ∈ LinearMap.ker (Twist.map (ProjΛ.toLin T.mor₁)) := by
      rw [hT.2.2]; exact LinearMap.mem_range_self _ z
    exact congrArg Twist.val hmem⟩⟩
  map_add' z1 z2 := by
    apply Twist.ext; apply Subtype.ext
    exact congrArg Twist.val (map_add (ProjΛ.toLin T.mor₃) z1 z2)
  map_smul' a z := by
    apply Twist.ext; apply Subtype.ext
    exact congrArg Twist.val (map_smul (ProjΛ.toLin T.mor₃) a z)

lemma twist_incl_comp_surjMor3 (T : Triangle ProjΛ) (hT : IsExact3 T) :
    (Twist.map (inclKerT T)).comp (surjMor3 T hT) = ProjΛ.toLin T.mor₃ := by
  apply LinearMap.ext; intro z; rfl

lemma surjMor3_surj (T : Triangle ProjΛ) (hT : IsExact3 T) :
    Function.Surjective (surjMor3 T hT) := by
  intro ⟨⟨x, hx⟩⟩
  have hmem : (⟨x⟩ : Twist T.obj₁.carrier) ∈ LinearMap.range (ProjΛ.toLin T.mor₃) := by
    rw [← hT.2.2]; exact Twist.ext hx
  obtain ⟨z, hz⟩ := hmem
  exact ⟨z, Twist.ext (Subtype.ext (congrArg Twist.val hz))⟩

lemma ker_surjMor3_eq_range_mor2 (T : Triangle ProjΛ) (hT : IsExact3 T) :
    LinearMap.ker (surjMor3 T hT) = LinearMap.range (ProjΛ.toLin T.mor₂) := by
  rw [← hT.2.1]; ext z; simp only [LinearMap.mem_ker]
  constructor
  · intro hz; apply Twist.ext; exact congrArg (fun t => t.val.val) hz
  · intro hz; apply Twist.ext; apply Subtype.ext; exact congrArg Twist.val hz

lemma surjMor3_comp_mor2 (T : Triangle ProjΛ) (hT : IsExact3 T) :
    (surjMor3 T hT).comp (ProjΛ.toLin T.mor₂) = 0 := by
  apply LinearMap.ext; intro y
  change surjMor3 T hT (ProjΛ.toLin T.mor₂ y) = 0
  exact LinearMap.mem_ker.mp ((ker_surjMor3_eq_range_mor2 T hT).symm ▸ LinearMap.mem_range_self _ y)

lemma mor2_comp_mor1 (T : Triangle ProjΛ) (hT : IsExact3 T) :
    (ProjΛ.toLin T.mor₂).comp (ProjΛ.toLin T.mor₁) = 0 := by
  apply LinearMap.ext; intro x
  change ProjΛ.toLin T.mor₂ (ProjΛ.toLin T.mor₁ x) = 0
  exact LinearMap.mem_ker.mp (hT.1.symm ▸ LinearMap.mem_range_self _ x)

lemma mor1_comp_inclKerT (T : Triangle ProjΛ) :
    (ProjΛ.toLin T.mor₁).comp (inclKerT T) = 0 := by
  ext ⟨x, hx⟩; exact hx

/-- A chain-map lift from the canonical 3-term resolution `P_•(Twist K1)` to an exact triangle `T2`
along `ψ : Twist K1 → Twist (kerT T2)` realizing `α : K1 → kerT T2`. -/
def HasGenLift {K1 : Type} [AddCommGroup K1] [Module Λ K1]
    [Module (ZMod 2) K1] [IsScalarTower (ZMod 2) Λ K1]
    (T2 : Triangle ProjΛ) (hT2 : IsExact3 T2)
    (ψ : Twist K1 →ₗ[Λ] Twist (kerT T2)) (α : K1 →ₗ[Λ] kerT T2) : Prop :=
  ∃ (u0 : P0 (Twist K1) →ₗ[Λ] T2.obj₁.carrier)
    (u1 : P1 (Twist K1) →ₗ[Λ] T2.obj₂.carrier)
    (u2 : P0 (Twist K1) →ₗ[Λ] T2.obj₃.carrier),
    (surjMor3 T2 hT2).comp u2 = ψ.comp (resμ (Twist K1)) ∧
    (ProjΛ.toLin T2.mor₂).comp u1 = u2.comp (resD1 (Twist K1)) ∧
    (ProjΛ.toLin T2.mor₁).comp u0 = u1.comp (resD2 (Twist K1)) ∧
    (inclKerT T2).comp α = u0.comp (resJK K1)

/-- Existence of a comparison lift for any `ψ : Twist K1 → Twist (kerT T2)` (with `K1` finite). -/
lemma exists_genLift {K1 : Type} [AddCommGroup K1] [Module Λ K1]
    [Module (ZMod 2) K1] [IsScalarTower (ZMod 2) Λ K1] [Fintype K1]
    (T2 : Triangle ProjΛ) (hT2 : IsExact3 T2)
    (ψ : Twist K1 →ₗ[Λ] Twist (kerT T2)) :
    ∃ α : K1 →ₗ[Λ] kerT T2, HasGenLift T2 hT2 ψ α := by
  haveI : Module.Projective Λ (P0 (Twist K1)) := (P0Obj (Twist K1)).proj
  haveI : Module.Projective Λ (P1 (Twist K1)) := (P1Obj (Twist K1)).proj
  obtain ⟨u2, hu2⟩ := Module.projective_lifting_property (surjMor3 T2 hT2)
    (ψ.comp (resμ (Twist K1))) (surjMor3_surj T2 hT2)
  have h1mem : ∀ p : P1 (Twist K1), u2 (resD1 (Twist K1) p) ∈ LinearMap.range (ProjΛ.toLin T2.mor₂) := by
    intro p; rw [← ker_surjMor3_eq_range_mor2 T2 hT2, LinearMap.mem_ker]
    have := LinearMap.congr_fun hu2 (resD1 (Twist K1) p)
    simp only [LinearMap.comp_apply] at this
    rw [this, resμ_comp_resD1, map_zero]
  let g2R : T2.obj₂.carrier →ₗ[Λ] LinearMap.range (ProjΛ.toLin T2.mor₂) := (ProjΛ.toLin T2.mor₂).rangeRestrict
  let u2d1R : P1 (Twist K1) →ₗ[Λ] LinearMap.range (ProjΛ.toLin T2.mor₂) :=
    (u2.comp (resD1 (Twist K1))).codRestrict _ h1mem
  obtain ⟨u1, hu1R⟩ := Module.projective_lifting_property g2R u2d1R (LinearMap.surjective_rangeRestrict _)
  have hu1 : (ProjΛ.toLin T2.mor₂).comp u1 = u2.comp (resD1 (Twist K1)) := by
    ext p; exact congrArg Subtype.val (LinearMap.congr_fun hu1R p)
  have h0mem : ∀ p : P0 (Twist K1), u1 (resD2 (Twist K1) p) ∈ LinearMap.range (ProjΛ.toLin T2.mor₁) := by
    intro p; rw [← hT2.1, LinearMap.mem_ker]
    have := LinearMap.congr_fun hu1 (resD2 (Twist K1) p)
    simp only [LinearMap.comp_apply] at this
    rw [this, resD1_comp_resD2, map_zero]
  let f2R : T2.obj₁.carrier →ₗ[Λ] LinearMap.range (ProjΛ.toLin T2.mor₁) := (ProjΛ.toLin T2.mor₁).rangeRestrict
  let u1d2R : P0 (Twist K1) →ₗ[Λ] LinearMap.range (ProjΛ.toLin T2.mor₁) :=
    (u1.comp (resD2 (Twist K1))).codRestrict _ h0mem
  obtain ⟨u0, hu0R⟩ := Module.projective_lifting_property f2R u1d2R (LinearMap.surjective_rangeRestrict _)
  have hu0 : (ProjΛ.toLin T2.mor₁).comp u0 = u1.comp (resD2 (Twist K1)) := by
    ext p; exact congrArg Subtype.val (LinearMap.congr_fun hu0R p)
  have hker0 : (ProjΛ.toLin T2.mor₁).comp (u0.comp (resJK K1)) = 0 := by
    rw [← LinearMap.comp_assoc, hu0, LinearMap.comp_assoc, resD2_comp_resJK, LinearMap.comp_zero]
  let α : K1 →ₗ[Λ] kerT T2 := (u0.comp (resJK K1)).codRestrict (kerT T2) (fun k => LinearMap.congr_fun hker0 k)
  exact ⟨α, u0, u1, u2, hu2, hu1, hu0, LinearMap.ext fun _ => rfl⟩

/-- Uniqueness of comparison maps modulo projectives! -/
lemma genLift_unique_mod_proj {K1 : Type} [AddCommGroup K1] [Module Λ K1]
    [Module (ZMod 2) K1] [IsScalarTower (ZMod 2) Λ K1] [Fintype K1]
    (T2 : Triangle ProjΛ) (hT2 : IsExact3 T2)
    (ψ : Twist K1 →ₗ[Λ] Twist (kerT T2)) {α α' : K1 →ₗ[Λ] kerT T2}
    (h1 : HasGenLift T2 hT2 ψ α) (h2 : HasGenLift T2 hT2 ψ α') :
    FactorsThroughProj (α - α') := by
  haveI : Module.Projective Λ (P0 (Twist K1)) := (P0Obj (Twist K1)).proj
  haveI : Module.Projective Λ (P1 (Twist K1)) := (P1Obj (Twist K1)).proj
  rcases h1 with ⟨u0, u1, u2, hu2, hu1, hu0, hα⟩
  rcases h2 with ⟨v0, v1, v2, hv2, hv1, hv0, hα'⟩
  have hd2_mem : ∀ p : P0 (Twist K1), (u2 - v2) p ∈ LinearMap.range (ProjΛ.toLin T2.mor₂) := by
    intro p; rw [← ker_surjMor3_eq_range_mor2 T2 hT2, LinearMap.mem_ker]
    have h1p := LinearMap.congr_fun hu2 p; have h2p := LinearMap.congr_fun hv2 p
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, map_sub] at h1p h2p ⊢
    rw [h1p, h2p, sub_self]
  obtain ⟨s2, hs2R⟩ := Module.projective_lifting_property (ProjΛ.toLin T2.mor₂).rangeRestrict
    ((u2 - v2).codRestrict _ hd2_mem) (LinearMap.surjective_rangeRestrict _)
  have hs2 : (ProjΛ.toLin T2.mor₂).comp s2 = u2 - v2 := by
    ext p; exact congrArg Subtype.val (LinearMap.congr_fun hs2R p)
  let w1 : P1 (Twist K1) →ₗ[Λ] T2.obj₂.carrier := (u1 - v1) - s2.comp (resD1 (Twist K1))
  have hw1_mem : ∀ p : P1 (Twist K1), w1 p ∈ LinearMap.range (ProjΛ.toLin T2.mor₁) := by
    intro p; rw [← hT2.1, LinearMap.mem_ker]
    have h1p := LinearMap.congr_fun hu1 p; have h2p := LinearMap.congr_fun hv1 p
    have hsp := LinearMap.congr_fun hs2 (resD1 (Twist K1) p)
    simp only [w1, LinearMap.comp_apply, LinearMap.sub_apply, map_sub] at h1p h2p hsp ⊢
    rw [h1p, h2p, hsp, sub_self]
  obtain ⟨s1, hs1R⟩ := Module.projective_lifting_property (ProjΛ.toLin T2.mor₁).rangeRestrict
    (w1.codRestrict _ hw1_mem) (LinearMap.surjective_rangeRestrict _)
  have hs1 : (ProjΛ.toLin T2.mor₁).comp s1 = w1 := by
    ext p; exact congrArg Subtype.val (LinearMap.congr_fun hs1R p)
  let w0 : P0 (Twist K1) →ₗ[Λ] T2.obj₁.carrier := (u0 - v0) - s1.comp (resD2 (Twist K1))
  have hw0_ker : ∀ p : P0 (Twist K1), ProjΛ.toLin T2.mor₁ (w0 p) = 0 := by
    intro p
    have h1p := LinearMap.congr_fun hu0 p; have h2p := LinearMap.congr_fun hv0 p
    have hsp := LinearMap.congr_fun hs1 (resD2 (Twist K1) p)
    simp only [w0, w1, LinearMap.comp_apply, LinearMap.sub_apply, map_sub] at h1p h2p hsp ⊢
    rw [h1p, h2p, hsp, resD1_comp_resD2, map_zero, sub_zero, sub_self]
  let s0 : P0 (Twist K1) →ₗ[Λ] kerT T2 := w0.codRestrict (kerT T2) hw0_ker
  have heq : α - α' = s0.comp (resJK K1) := by
    apply LinearMap.ext; intro k; apply Subtype.ext
    have h1k := LinearMap.congr_fun hα k; have h2k := LinearMap.congr_fun hα' k
    simp only [s0, w0, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.codRestrict_apply] at h1k h2k ⊢
    change (inclKerT T2 (α k) - inclKerT T2 (α' k)) = (u0 (resJK K1 k) - v0 (resJK K1 k)) - s1 (resD2 (Twist K1) (resJK K1 k))
    rw [h1k, h2k, show resD2 (Twist K1) (resJK K1 k) = 0 from LinearMap.congr_fun resD2_comp_resJK k,
        map_zero, sub_zero]
  rw [heq]
  exact ⟨P0Obj (Twist K1), resJK K1, s0, rfl⟩

/-- Standard lift for a single exact triangle `T`: `HasGenLift T hT LinearMap.id α`. -/
abbrev HasLiftWith (T : Triangle ProjΛ) (hT : IsExact3 T) (α : kerT T →ₗ[Λ] kerT T) : Prop :=
  HasGenLift T hT LinearMap.id α

/-- The twisted distinguished triangles `Δ_{θ_ε}` in `ProjΛ`! -/
def IsDistinguishedε (T : Triangle ProjΛ) : Prop :=
  ∃ (hT : IsExact3 T) (α : kerT T →ₗ[Λ] kerT T),
    HasLiftWith T hT α ∧ FactorsThroughProj (α - (LinearMap.id + deltaTotal (kerT T)))

lemma isDistinguishedε_iff_of_lift (T : Triangle ProjΛ) (hT : IsExact3 T)
    {α : kerT T →ₗ[Λ] kerT T} (hL : HasLiftWith T hT α) :
    IsDistinguishedε T ↔ FactorsThroughProj (α - (LinearMap.id + deltaTotal (kerT T))) := by
  constructor
  · rintro ⟨hT', α', hL', hF'⟩
    have hU := genLift_unique_mod_proj T hT LinearMap.id hL hL'
    have heq : α - (LinearMap.id + deltaTotal (kerT T)) =
        (α - α') + (α' - (LinearMap.id + deltaTotal (kerT T))) := by abel
    rw [heq]; exact FactorsThroughProj_add hU hF'
  · intro hF; exact ⟨hT, α, hL, hF⟩

/-- Naturality of comparison maps along any morphism of exact triangles `(a, b, c) : T1 ⟶ T2`! -/
lemma comparison_nat_of_triangle_morphism {T1 T2 : Triangle ProjΛ}
    (hT1 : IsExact3 T1) (hT2 : IsExact3 T2) (m : T1 ⟶ T2)
    {α1 : kerT T1 →ₗ[Λ] kerT T1} {α2 : kerT T2 →ₗ[Λ] kerT T2}
    (hL1 : HasLiftWith T1 hT1 α1) (hL2 : HasLiftWith T2 hT2 α2) :
    let φ : kerT T1 →ₗ[Λ] kerT T2 :=
      ((ProjΛ.toLin m.hom₁).comp (inclKerT T1)).codRestrict (kerT T2) (fun k => by
        have hc := LinearMap.congr_fun m.comm₁ k.1
        change ProjΛ.toLin T2.mor₁ (ProjΛ.toLin m.hom₁ k.1) = 0
        have h1 : ProjΛ.toLin m.hom₂ (ProjΛ.toLin T1.mor₁ k.1) = ProjΛ.toLin T2.mor₁ (ProjΛ.toLin m.hom₁ k.1) := hc
        rw [← h1, k.2, map_zero])
    FactorsThroughProj (φ.comp α1 - α2.comp φ) := by
  intro φ
  rcases hL1 with ⟨u0, u1, u2, hu2, hu1, hu0, hα1⟩
  rcases hL2 with ⟨v0, v1, v2, hv2, hv1, hv0, hα2⟩
  have h1_lift : HasGenLift T2 hT2 (Twist.map φ) (φ.comp α1) := by
    refine ⟨(ProjΛ.toLin m.hom₁).comp u0, (ProjΛ.toLin m.hom₂).comp u1, (ProjΛ.toLin m.hom₃).comp u2,
      ?_, ?_, ?_, ?_⟩
    · apply LinearMap.ext; intro p; apply Twist.ext; apply Subtype.ext
      have hc3 := LinearMap.congr_fun m.comm₃ (u2 p)
      have h3 : (Twist.map (ProjΛ.toLin m.hom₁)) (ProjΛ.toLin T1.mor₃ (u2 p)) =
          ProjΛ.toLin T2.mor₃ (ProjΛ.toLin m.hom₃ (u2 p)) := hc3
      have h2p := congrArg (fun t => t.val.val) (LinearMap.congr_fun hu2 p)
      change (ProjΛ.toLin T2.mor₃ (ProjΛ.toLin m.hom₃ (u2 p))).val = ProjΛ.toLin m.hom₁ (resμ (Twist (kerT T1)) p).val.val
      rw [← h3]; change ProjΛ.toLin m.hom₁ (ProjΛ.toLin T1.mor₃ (u2 p)).val = _
      exact congrArg (ProjΛ.toLin m.hom₁) h2p
    · ext p
      have hc2 := LinearMap.congr_fun m.comm₂ (u1 p)
      have h1p := LinearMap.congr_fun hu1 p
      exact hc2.symm.trans (congrArg (ProjΛ.toLin m.hom₃) h1p)
    · ext p
      have hc1 := LinearMap.congr_fun m.comm₁ (u0 p)
      have h0p := LinearMap.congr_fun hu0 p
      exact hc1.symm.trans (congrArg (ProjΛ.toLin m.hom₂) h0p)
    · ext k
      have hk := LinearMap.congr_fun hα1 k
      exact congrArg (ProjΛ.toLin m.hom₁) hk
  have h2_lift : HasGenLift T2 hT2 (Twist.map φ) (α2.comp φ) := by
    refine ⟨v0.comp (P0.map (Twist.map φ)), v1.comp (P1.map (Twist.map φ)),
      v2.comp (P0.map (Twist.map φ)), ?_, ?_, ?_, ?_⟩
    · rw [← LinearMap.comp_assoc, hv2, LinearMap.id_comp, ← resμ_nat]
    · rw [← LinearMap.comp_assoc, hv1, LinearMap.comp_assoc, ← resD1_nat, LinearMap.comp_assoc]
    · rw [← LinearMap.comp_assoc, hv0, LinearMap.comp_assoc, ← resD2_nat, LinearMap.comp_assoc]
    · rw [← LinearMap.comp_assoc, hα2, LinearMap.comp_assoc, ← resJK_nat, LinearMap.comp_assoc]
  exact genLift_unique_mod_proj T2 hT2 (Twist.map φ) h1_lift h2_lift

lemma tri_comm₁ {T1 T2 : Triangle ProjΛ} (m : T1 ⟶ T2) (x : T1.obj₁.carrier) :
    ProjΛ.toLin m.hom₂ (ProjΛ.toLin T1.mor₁ x) = ProjΛ.toLin T2.mor₁ (ProjΛ.toLin m.hom₁ x) :=
  LinearMap.congr_fun m.comm₁ x

lemma tri_comm₂ {T1 T2 : Triangle ProjΛ} (m : T1 ⟶ T2) (y : T1.obj₂.carrier) :
    ProjΛ.toLin m.hom₃ (ProjΛ.toLin T1.mor₂ y) = ProjΛ.toLin T2.mor₂ (ProjΛ.toLin m.hom₂ y) :=
  LinearMap.congr_fun m.comm₂ y

lemma tri_comm₃ {T1 T2 : Triangle ProjΛ} (m : T1 ⟶ T2) (z : T1.obj₃.carrier) :
    Twist.map (ProjΛ.toLin m.hom₁) (ProjΛ.toLin T1.mor₃ z) = ProjΛ.toLin T2.mor₃ (ProjΛ.toLin m.hom₃ z) :=
  LinearMap.congr_fun m.comm₃ z

/- ### Axiom 1: `isomorphic_distinguished` -/
lemma isDistinguishedε_of_iso (T1 : Triangle ProjΛ) (h1 : IsDistinguishedε T1)
    (T2 : Triangle ProjΛ) (e : T2 ≅ T1) : IsDistinguishedε T2 := by
  rcases h1 with ⟨hT1, α1, hL1, hF1⟩
  have h1_inv_l : ∀ x : T2.obj₁.carrier, ProjΛ.toLin e.inv.hom₁ (ProjΛ.toLin e.hom.hom₁ x) = x :=
    fun x => LinearMap.congr_fun (Iso.hom_inv_id_triangle_hom₁ e) x
  have h1_inv_r : ∀ y : T1.obj₁.carrier, ProjΛ.toLin e.hom.hom₁ (ProjΛ.toLin e.inv.hom₁ y) = y :=
    fun y => LinearMap.congr_fun (Iso.inv_hom_id_triangle_hom₁ e) y
  have h2_inv_l : ∀ x : T2.obj₂.carrier, ProjΛ.toLin e.inv.hom₂ (ProjΛ.toLin e.hom.hom₂ x) = x :=
    fun x => LinearMap.congr_fun (Iso.hom_inv_id_triangle_hom₂ e) x
  have h2_inv_r : ∀ y : T1.obj₂.carrier, ProjΛ.toLin e.hom.hom₂ (ProjΛ.toLin e.inv.hom₂ y) = y :=
    fun y => LinearMap.congr_fun (Iso.inv_hom_id_triangle_hom₂ e) y
  have h3_inv_l : ∀ x : T2.obj₃.carrier, ProjΛ.toLin e.inv.hom₃ (ProjΛ.toLin e.hom.hom₃ x) = x :=
    fun x => LinearMap.congr_fun (Iso.hom_inv_id_triangle_hom₃ e) x
  have h3_inv_r : ∀ y : T1.obj₃.carrier, ProjΛ.toLin e.hom.hom₃ (ProjΛ.toLin e.inv.hom₃ y) = y :=
    fun y => LinearMap.congr_fun (Iso.inv_hom_id_triangle_hom₃ e) y
  have hbij1 : Function.Bijective (ProjΛ.toLin e.hom.hom₁) :=
    ⟨fun x y hxy => (h1_inv_l x).symm.trans ((congrArg _ hxy).trans (h1_inv_l y)),
     fun y => ⟨ProjΛ.toLin e.inv.hom₁ y, h1_inv_r y⟩⟩
  have hbij2 : Function.Bijective (ProjΛ.toLin e.hom.hom₂) :=
    ⟨fun x y hxy => (h2_inv_l x).symm.trans ((congrArg _ hxy).trans (h2_inv_l y)),
     fun y => ⟨ProjΛ.toLin e.inv.hom₂ y, h2_inv_r y⟩⟩
  have hbij3 : Function.Bijective (ProjΛ.toLin e.hom.hom₃) :=
    ⟨fun x y hxy => (h3_inv_l x).symm.trans ((congrArg _ hxy).trans (h3_inv_l y)),
     fun y => ⟨ProjΛ.toLin e.inv.hom₃ y, h3_inv_r y⟩⟩
  have hT2 : IsExact3 T2 := by
    refine ⟨?_, ?_, ?_⟩
    · ext y; simp only [LinearMap.mem_ker, LinearMap.mem_range]
      constructor
      · intro hy
        have h1y : ProjΛ.toLin e.hom.hom₂ y ∈ LinearMap.ker (ProjΛ.toLin T1.mor₂) := by
          change ProjΛ.toLin T1.mor₂ (ProjΛ.toLin e.hom.hom₂ y) = 0
          rw [← tri_comm₂ e.hom y, hy, map_zero]
        rw [hT1.1] at h1y
        obtain ⟨x1, hx1⟩ := h1y
        obtain ⟨x2, rfl⟩ := hbij1.2 x1
        refine ⟨x2, hbij2.1 ?_⟩
        exact (tri_comm₁ e.hom x2).trans hx1
      · rintro ⟨x, rfl⟩
        apply hbij3.1
        rw [map_zero, tri_comm₂ e.hom, tri_comm₁ e.hom]
        exact LinearMap.congr_fun (mor2_comp_mor1 T1 hT1) _
    · ext z; simp only [LinearMap.mem_ker, LinearMap.mem_range]
      constructor
      · intro hz
        have h1z : ProjΛ.toLin e.hom.hom₃ z ∈ LinearMap.ker (ProjΛ.toLin T1.mor₃) := by
          change ProjΛ.toLin T1.mor₃ (ProjΛ.toLin e.hom.hom₃ z) = 0
          rw [← tri_comm₃ e.hom z]
          have hzt : (ProjΛ.toLin T2.mor₃ z : Twist T2.obj₁.carrier) = 0 := hz
          rw [hzt]; exact map_zero _
        rw [hT1.2.1] at h1z
        obtain ⟨y1, hy1⟩ := h1z
        obtain ⟨y2, rfl⟩ := hbij2.2 y1
        refine ⟨y2, hbij3.1 ?_⟩
        exact (tri_comm₂ e.hom y2).trans hy1
      · rintro ⟨y, rfl⟩
        apply Twist.ext; apply hbij1.1
        have h3 := congrArg Twist.val (tri_comm₃ e.hom (ProjΛ.toLin T2.mor₂ y))
        have h2 := tri_comm₂ e.hom y
        have hzero : ProjΛ.toLin T1.mor₃ (ProjΛ.toLin T1.mor₂ (ProjΛ.toLin e.hom.hom₂ y)) = 0 :=
          LinearMap.mem_ker.mp (hT1.2.1.symm ▸ LinearMap.mem_range_self _ _)
        change ProjΛ.toLin e.hom.hom₁ (ProjΛ.toLin T2.mor₃ (ProjΛ.toLin T2.mor₂ y)).val =
          ProjΛ.toLin e.hom.hom₁ (0 : T2.obj₁.carrier)
        rw [map_zero]
        exact (h3.trans (congrArg (fun a => (ProjΛ.toLin T1.mor₃ a).val) h2)).trans (congrArg Twist.val hzero)
    · ext x; simp only [LinearMap.mem_ker, LinearMap.mem_range]
      constructor
      · intro hx
        have h1x : Twist.map (ProjΛ.toLin e.hom.hom₁) x ∈ LinearMap.ker (Twist.map (ProjΛ.toLin T1.mor₁)) := by
          apply Twist.ext
          change ProjΛ.toLin T1.mor₁ (ProjΛ.toLin e.hom.hom₁ x.val) = 0
          rw [← tri_comm₁ e.hom x.val]
          have hxv : ProjΛ.toLin T2.mor₁ x.val = 0 := congrArg Twist.val hx
          rw [hxv, map_zero]
        rw [hT1.2.2] at h1x
        obtain ⟨z1, hz1⟩ := h1x
        obtain ⟨z2, rfl⟩ := hbij3.2 z1
        refine ⟨z2, Twist.ext (hbij1.1 ?_)⟩
        exact congrArg Twist.val ((tri_comm₃ e.hom z2).trans hz1)
      · rintro ⟨z, rfl⟩
        apply Twist.ext; apply hbij2.1
        have hc1 := tri_comm₁ e.hom (ProjΛ.toLin T2.mor₃ z).val
        have hc3 : ProjΛ.toLin e.hom.hom₁ (ProjΛ.toLin T2.mor₃ z).val =
            (ProjΛ.toLin T1.mor₃ (ProjΛ.toLin e.hom.hom₃ z)).val :=
          congrArg Twist.val (tri_comm₃ e.hom z)
        have hzero : Twist.map (ProjΛ.toLin T1.mor₁) (ProjΛ.toLin T1.mor₃ (ProjΛ.toLin e.hom.hom₃ z)) = 0 :=
          LinearMap.mem_ker.mp (hT1.2.2.symm ▸ LinearMap.mem_range_self (ProjΛ.toLin T1.mor₃) (ProjΛ.toLin e.hom.hom₃ z))
        change ProjΛ.toLin e.hom.hom₂ (ProjΛ.toLin T2.mor₁ (ProjΛ.toLin T2.mor₃ z).val) =
          ProjΛ.toLin e.hom.hom₂ (0 : T2.obj₂.carrier)
        rw [map_zero, hc1, hc3]
        exact congrArg Twist.val hzero
  obtain ⟨α2, hL2⟩ := exists_genLift T2 hT2 LinearMap.id
  rw [isDistinguishedε_iff_of_lift T2 hT2 hL2]
  have hcomp := comparison_nat_of_triangle_morphism hT2 hT1 e.hom hL2 hL1
  dsimp only at hcomp
  let φ : kerT T2 →ₗ[Λ] kerT T1 :=
    ((ProjΛ.toLin e.hom.hom₁).comp (inclKerT T2)).codRestrict (kerT T1) (fun k => by
      change ProjΛ.toLin T1.mor₁ (ProjΛ.toLin e.hom.hom₁ k.1) = 0
      rw [← tri_comm₁ e.hom k.1, k.2, map_zero])
  let φinv : kerT T1 →ₗ[Λ] kerT T2 :=
    ((ProjΛ.toLin e.inv.hom₁).comp (inclKerT T1)).codRestrict (kerT T2) (fun k => by
      change ProjΛ.toLin T2.mor₁ (ProjΛ.toLin e.inv.hom₁ k.1) = 0
      rw [← tri_comm₁ e.inv k.1, k.2, map_zero])
  have hinvL : φinv.comp φ = LinearMap.id := by
    apply LinearMap.ext; intro k; apply Subtype.ext; exact h1_inv_l k.1
  have hnat := deltaTotal_natural φ
  have h1' : FactorsThroughProj (φinv.comp (φ.comp α2 - α1.comp φ)) :=
    FactorsThroughProj_comp_left φinv hcomp
  have h2' : FactorsThroughProj (φinv.comp ((α1 - (LinearMap.id + deltaTotal (kerT T1))).comp φ)) :=
    FactorsThroughProj_comp_left φinv (FactorsThroughProj_comp_right hF1 φ)
  have h3' : FactorsThroughProj (φinv.comp (φ.comp (deltaTotal (kerT T2)) - (deltaTotal (kerT T1)).comp φ)) :=
    FactorsThroughProj_comp_left φinv hnat
  have heq : α2 - (LinearMap.id + deltaTotal (kerT T2)) =
      φinv.comp (φ.comp α2 - α1.comp φ) +
      φinv.comp ((α1 - (LinearMap.id + deltaTotal (kerT T1))).comp φ) -
      φinv.comp (φ.comp (deltaTotal (kerT T2)) - (deltaTotal (kerT T1)).comp φ) := by
    ext k
    have hL : ∀ z : kerT T2, φinv (φ z) = z := fun z => LinearMap.congr_fun hinvL z
    simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply,
      map_sub, map_add, hL]
    abel
  rw [heq]
  exact FactorsThroughProj_sub (FactorsThroughProj_add h1' h2') h3'

/- ### Axiom 2: `contractible_distinguished` -/
lemma subsingleton_of_isZero_proj (Z : ProjΛ) (hz : Limits.IsZero Z) : Subsingleton Z.carrier := by
  have hid0 : (𝟙 Z) = 0 := hz.eq_of_src _ _
  refine ⟨fun x y => ?_⟩
  have hx : x = 0 := LinearMap.congr_fun hid0 x
  have hy : y = 0 := LinearMap.congr_fun hid0 y
  rw [hx, hy]

lemma isDistinguishedε_contractible (X : ProjΛ) :
    IsDistinguishedε (contractibleTriangle X) := by
  haveI : Subsingleton (contractibleTriangle X).obj₃.carrier :=
    subsingleton_of_isZero_proj _ (Limits.isZero_zero ProjΛ)
  have hT : IsExact3 (contractibleTriangle X) := by
    refine ⟨?_, ?_, ?_⟩
    · ext x; simp only [LinearMap.mem_ker, LinearMap.mem_range]
      exact ⟨fun _ => ⟨x, rfl⟩, fun _ => Subsingleton.elim _ _⟩
    · ext z; simp only [LinearMap.mem_ker, LinearMap.mem_range]
      exact ⟨fun _ => ⟨0, Subsingleton.elim _ _⟩, fun _ => rfl⟩
    · ext x; simp only [LinearMap.mem_ker, LinearMap.mem_range]
      constructor
      · intro hx; refine ⟨0, ?_⟩
        change (0 : Twist X.carrier) = x
        exact (Twist.ext (congrArg Twist.val hx)).symm
      · rintro ⟨_, rfl⟩
        change Twist.map (LinearMap.id : X.carrier →ₗ[Λ] X.carrier) (0 : Twist X.carrier) = 0
        rfl
  obtain ⟨α, hL⟩ := exists_genLift (contractibleTriangle X) hT LinearMap.id
  rw [isDistinguishedε_iff_of_lift _ hT hL]
  have hsub : Subsingleton (kerT (contractibleTriangle X)) :=
    ⟨fun a b => Subtype.ext (a.2.trans b.2.symm)⟩
  have hzero : α - (LinearMap.id + deltaTotal (kerT (contractibleTriangle X))) = 0 :=
    LinearMap.ext fun _ => Subsingleton.elim _ _
  rw [hzero]; exact FactorsThroughProj_zero

/- ### Axiom 3: `distinguished_cocone_triangle` -/
/-- Helper for `isDistinguishedε_cocone`: builds comparison maps and homotopies `(φ, ψ, t, b)`. -/
private lemma isDistinguishedε_cocone_homotopy {X Y : ProjΛ} (f : X ⟶ Y) :
    let fl : X.carrier →ₗ[Λ] Y.carrier := ProjΛ.toLin f
    let K : Submodule Λ X.carrier := LinearMap.ker fl
    let I : Submodule Λ Y.carrier := LinearMap.range fl
    let C := Y.carrier ⧸ I
    let Q : ProjΛ := P0Obj (Twist C)
    let g0 : Y.carrier →ₗ[Λ] Q.carrier := (resJK C).comp I.mkQ
    let W : Submodule Λ (P1 (Twist C)) := LinearMap.range (resD2 (Twist C))
    let pQ : Q.carrier →ₗ[Λ] W := (resD2 (Twist C)).rangeRestrict
    ∃ (u0 : P0 (Twist K) →ₗ[Λ] X.carrier) (u1 : P1 (Twist K) →ₗ[Λ] Y.carrier)
      (u2 : P0 (Twist K) →ₗ[Λ] Q.carrier) (φ : Twist K →ₗ[Λ] W) (ψ : W →ₗ[Λ] Twist K)
      (t : Twist K →ₗ[Λ] P0 (Twist K)) (b : W →ₗ[Λ] Q.carrier),
      u0.comp (resJK K) = K.subtype ∧ u1.comp (resD2 (Twist K)) = fl.comp u0 ∧
      u2.comp (resD1 (Twist K)) = g0.comp u1 ∧ φ.comp (resμ (Twist K)) = pQ.comp u2 ∧
      ψ.comp φ + (resμ (Twist K)).comp t = LinearMap.id ∧ φ.comp ψ + pQ.comp b = LinearMap.id := by
  classical
  intro fl K I C Q g0 W pQ
  let ι : K →ₗ[Λ] X.carrier := K.subtype
  have hι : Function.Injective ι := Submodule.injective_subtype K
  let q : Y.carrier →ₗ[Λ] C := I.mkQ
  have hq_surj : Function.Surjective q := Submodule.mkQ_surjective I
  let jC : C →ₗ[Λ] Q.carrier := resJK C
  have hjC : Function.Injective jC := resJK_inj
  have hker_g0 : LinearMap.ker g0 = LinearMap.range fl := by
    ext y; simp only [g0, LinearMap.mem_ker, LinearMap.comp_apply]
    constructor
    · intro hy
      have hqy : q y = 0 := hjC (hy.trans (map_zero jC).symm)
      exact (Submodule.Quotient.mk_eq_zero I).mp hqy
    · intro hy
      have hqy : q y = 0 := (Submodule.Quotient.mk_eq_zero I).mpr hy
      rw [hqy, map_zero]
  have hpQ_surj : Function.Surjective pQ := LinearMap.surjective_rangeRestrict _
  have hker_pQ : LinearMap.ker pQ = LinearMap.range g0 := by
    have hrg : LinearMap.range g0 = LinearMap.range (resJK C) := by
      ext z; simp only [g0, LinearMap.mem_range, LinearMap.comp_apply]
      constructor
      · rintro ⟨y, rfl⟩; exact ⟨q y, rfl⟩
      · rintro ⟨c, rfl⟩; obtain ⟨y, rfl⟩ := hq_surj c; exact ⟨y, rfl⟩
    rw [LinearMap.ker_rangeRestrict, hrg, ker_resD2_eq_range_resJK]
  have hpQ_g0 : pQ.comp g0 = 0 := by
    apply LinearMap.ext; intro y; change pQ (g0 y) = 0
    exact LinearMap.mem_ker.mp (hker_pQ.symm ▸ LinearMap.mem_range_self g0 y)
  have hg0_fl : g0.comp fl = 0 := by
    apply LinearMap.ext; intro x; change g0 (fl x) = 0
    exact LinearMap.mem_ker.mp (hker_g0.symm ▸ LinearMap.mem_range_self fl x)
  obtain ⟨u0, hu0⟩ := ProjΛ.injective X (resJK K) resJK_inj ι
  have hfu0_ker : (fl.comp u0).comp (resJK K) = 0 := by
    rw [LinearMap.comp_assoc, hu0]; apply LinearMap.ext; intro ⟨x, hx⟩; exact hx
  obtain ⟨v1, hv1⟩ := desc_of_ker_eq_range (LinearMap.surjective_rangeRestrict (resD2 (Twist K)))
    (by rw [LinearMap.ker_rangeRestrict]; exact ker_resD2_eq_range_resJK) hfu0_ker
  obtain ⟨u1, hu1_sub⟩ := ProjΛ.injective Y (LinearMap.range (resD2 (Twist K))).subtype
    (Submodule.injective_subtype _) v1
  have hu1 : u1.comp (resD2 (Twist K)) = fl.comp u0 := by
    apply LinearMap.ext; intro p
    exact (LinearMap.congr_fun hu1_sub ⟨resD2 (Twist K) p, ⟨p, rfl⟩⟩).trans (LinearMap.congr_fun hv1 p)
  have hgu1_ker : (g0.comp u1).comp (resD2 (Twist K)) = 0 := by
    rw [LinearMap.comp_assoc, hu1, ← LinearMap.comp_assoc, hg0_fl, LinearMap.zero_comp]
  obtain ⟨v2, hv2⟩ := desc_of_ker_eq_range (LinearMap.surjective_rangeRestrict (resD1 (Twist K)))
    (by rw [LinearMap.ker_rangeRestrict]; exact ker_resD1_eq_range_resD2) hgu1_ker
  obtain ⟨u2, hu2_sub⟩ := ProjΛ.injective Q (LinearMap.range (resD1 (Twist K))).subtype
    (Submodule.injective_subtype _) v2
  have hu2 : u2.comp (resD1 (Twist K)) = g0.comp u1 := by
    apply LinearMap.ext; intro p
    exact (LinearMap.congr_fun hu2_sub ⟨resD1 (Twist K) p, ⟨p, rfl⟩⟩).trans (LinearMap.congr_fun hv2 p)
  have hpu2_ker : (pQ.comp u2).comp (resD1 (Twist K)) = 0 := by
    rw [LinearMap.comp_assoc, hu2, ← LinearMap.comp_assoc, hpQ_g0, LinearMap.zero_comp]
  obtain ⟨φ, hφ⟩ := desc_of_ker_eq_range resμ_surj ker_resμ_eq_range_resD1 hpu2_ker
  obtain ⟨w0, hw0⟩ := ProjΛ.injective (P0Obj (Twist K)) ι hι (resJK K)
  have hdw0_ker : ((resD2 (Twist K)).comp w0).comp ι = 0 := by
    rw [LinearMap.comp_assoc, hw0, resD2_comp_resJK]
  obtain ⟨z1, hz1⟩ := desc_of_ker_eq_range (LinearMap.surjective_rangeRestrict fl)
    (by rw [LinearMap.ker_rangeRestrict]; exact (Submodule.range_subtype K).symm) hdw0_ker
  obtain ⟨w1, hw1_sub⟩ := ProjΛ.injective (P1Obj (Twist K)) I.subtype (Submodule.injective_subtype _) z1
  have hw1 : w1.comp fl = (resD2 (Twist K)).comp w0 := by
    apply LinearMap.ext; intro x
    exact (LinearMap.congr_fun hw1_sub ⟨fl x, ⟨x, rfl⟩⟩).trans (LinearMap.congr_fun hz1 x)
  have hdw1_ker : ((resD1 (Twist K)).comp w1).comp fl = 0 := by
    rw [LinearMap.comp_assoc, hw1, ← LinearMap.comp_assoc]
    exact LinearMap.ext fun x => resD1_comp_resD2 (w0 x)
  obtain ⟨z2, hz2⟩ := desc_of_ker_eq_range (LinearMap.surjective_rangeRestrict g0)
    (by rw [LinearMap.ker_rangeRestrict]; exact hker_g0) hdw1_ker
  obtain ⟨w2, hw2_sub⟩ := ProjΛ.injective (P0Obj (Twist K)) (LinearMap.range g0).subtype
    (Submodule.injective_subtype _) z2
  have hw2 : w2.comp g0 = (resD1 (Twist K)).comp w1 := by
    apply LinearMap.ext; intro y
    exact (LinearMap.congr_fun hw2_sub ⟨g0 y, ⟨y, rfl⟩⟩).trans (LinearMap.congr_fun hz2 y)
  have hμw2_ker : ((resμ (Twist K)).comp w2).comp g0 = 0 := by
    apply LinearMap.ext; intro y
    simp only [LinearMap.comp_apply, LinearMap.zero_apply]
    rw [show w2 (g0 y) = resD1 (Twist K) (w1 y) from LinearMap.congr_fun hw2 y]
    exact resμ_comp_resD1 (w1 y)
  obtain ⟨ψ, hψ⟩ := desc_of_ker_eq_range hpQ_surj hker_pQ hμw2_ker
  have hψφ : ∃ t : Twist K →ₗ[Λ] P0 (Twist K), ψ.comp φ + (resμ (Twist K)).comp t = LinearMap.id := by
    have hd0 : (w0.comp u0 - LinearMap.id).comp (resJK K) = 0 := by
      apply LinearMap.ext; intro k
      simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.zero_apply]
      rw [show u0 (resJK K k) = ι k from LinearMap.congr_fun hu0 k,
          show w0 (ι k) = resJK K k from LinearMap.congr_fun hw0 k, sub_self]
    obtain ⟨s0R, hs0R⟩ := desc_of_ker_eq_range (LinearMap.surjective_rangeRestrict (resD2 (Twist K)))
      (by rw [LinearMap.ker_rangeRestrict]; exact ker_resD2_eq_range_resJK) hd0
    obtain ⟨s0, hs0_sub⟩ := ProjΛ.injective (P0Obj (Twist K)) (LinearMap.range (resD2 (Twist K))).subtype
      (Submodule.injective_subtype _) s0R
    have hs0 : s0.comp (resD2 (Twist K)) = w0.comp u0 - LinearMap.id := by
      apply LinearMap.ext; intro p
      exact (LinearMap.congr_fun hs0_sub ⟨resD2 (Twist K) p, ⟨p, rfl⟩⟩).trans (LinearMap.congr_fun hs0R p)
    have hd1 : ((w1.comp u1 - LinearMap.id) - (resD2 (Twist K)).comp s0).comp (resD2 (Twist K)) = 0 := by
      apply LinearMap.ext; intro p
      simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.zero_apply]
      rw [show u1 (resD2 (Twist K) p) = fl (u0 p) from LinearMap.congr_fun hu1 p,
          show w1 (fl (u0 p)) = resD2 (Twist K) (w0 (u0 p)) from LinearMap.congr_fun hw1 (u0 p),
          show s0 (resD2 (Twist K) p) = w0 (u0 p) - p from LinearMap.congr_fun hs0 p,
          map_sub, sub_self]
    obtain ⟨s1R, hs1R⟩ := desc_of_ker_eq_range (LinearMap.surjective_rangeRestrict (resD1 (Twist K)))
      (by rw [LinearMap.ker_rangeRestrict]; exact ker_resD1_eq_range_resD2) hd1
    obtain ⟨s1, hs1_sub⟩ := ProjΛ.injective (P1Obj (Twist K)) (LinearMap.range (resD1 (Twist K))).subtype
      (Submodule.injective_subtype _) s1R
    have hs1 : s1.comp (resD1 (Twist K)) = (w1.comp u1 - LinearMap.id) - (resD2 (Twist K)).comp s0 := by
      apply LinearMap.ext; intro p
      exact (LinearMap.congr_fun hs1_sub ⟨resD1 (Twist K) p, ⟨p, rfl⟩⟩).trans (LinearMap.congr_fun hs1R p)
    have hd2 : ((w2.comp u2 - LinearMap.id) - (resD1 (Twist K)).comp s1).comp (resD1 (Twist K)) = 0 := by
      apply LinearMap.ext; intro p
      simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.zero_apply]
      rw [show u2 (resD1 (Twist K) p) = g0 (u1 p) from LinearMap.congr_fun hu2 p,
          show w2 (g0 (u1 p)) = resD1 (Twist K) (w1 (u1 p)) from LinearMap.congr_fun hw2 (u1 p),
          show s1 (resD1 (Twist K) p) = (w1 (u1 p) - p) - resD2 (Twist K) (s0 p) from LinearMap.congr_fun hs1 p,
          map_sub, map_sub, resD1_comp_resD2, sub_zero, sub_self]
    obtain ⟨t, ht⟩ := desc_of_ker_eq_range resμ_surj ker_resμ_eq_range_resD1 hd2
    refine ⟨t, LinearMap.ext fun x => ?_⟩
    obtain ⟨p, rfl⟩ := resμ_surj x
    have h1 := LinearMap.congr_fun ht p
    have h2 : (resμ (Twist K)) ((w2 (u2 p) - p) - resD1 (Twist K) (s1 p)) =
        ψ (φ (resμ (Twist K) p)) - resμ (Twist K) p := by
      rw [map_sub, resμ_comp_resD1, sub_zero, map_sub]
      rw [show resμ (Twist K) (w2 (u2 p)) = ψ (pQ (u2 p)) from (LinearMap.congr_fun hψ (u2 p)).symm,
          show pQ (u2 p) = φ (resμ (Twist K) p) from (LinearMap.congr_fun hφ p).symm]
    have h3 : resμ (Twist K) (t (resμ (Twist K) p)) = ψ (φ (resμ (Twist K) p)) - resμ (Twist K) p :=
      (congrArg (resμ (Twist K)) h1).trans h2
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply]
    rw [h3, sub_eq_add_neg, neg_eq_self_mod, ← add_assoc, add_self_zmod2_mod, zero_add]
  obtain ⟨t, ht⟩ := hψφ
  have hφψ : ∃ b : W →ₗ[Λ] Q.carrier, φ.comp ψ + pQ.comp b = LinearMap.id := by
    have hd0 : (u0.comp w0 - LinearMap.id).comp ι = 0 := by
      rw [LinearMap.sub_comp, LinearMap.comp_assoc, hw0, hu0, LinearMap.id_comp, sub_self]
    obtain ⟨s0R, hs0R⟩ := desc_of_ker_eq_range (LinearMap.surjective_rangeRestrict fl)
      (by rw [LinearMap.ker_rangeRestrict]; exact (Submodule.range_subtype K).symm) hd0
    obtain ⟨s0, hs0_sub⟩ := ProjΛ.injective X I.subtype (Submodule.injective_subtype _) s0R
    have hs0 : s0.comp fl = u0.comp w0 - LinearMap.id := by
      apply LinearMap.ext; intro x
      exact (LinearMap.congr_fun hs0_sub ⟨fl x, ⟨x, rfl⟩⟩).trans (LinearMap.congr_fun hs0R x)
    have hd1 : ((u1.comp w1 - LinearMap.id) - fl.comp s0).comp fl = 0 := by
      apply LinearMap.ext; intro x
      simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.zero_apply]
      rw [show w1 (fl x) = resD2 (Twist K) (w0 x) from LinearMap.congr_fun hw1 x,
          show u1 (resD2 (Twist K) (w0 x)) = fl (u0 (w0 x)) from LinearMap.congr_fun hu1 (w0 x),
          show s0 (fl x) = u0 (w0 x) - x from LinearMap.congr_fun hs0 x,
          map_sub, sub_self]
    obtain ⟨s1R, hs1R⟩ := desc_of_ker_eq_range (LinearMap.surjective_rangeRestrict g0)
      (by rw [LinearMap.ker_rangeRestrict]; exact hker_g0) hd1
    obtain ⟨s1, hs1_sub⟩ := ProjΛ.injective Y (LinearMap.range g0).subtype (Submodule.injective_subtype _) s1R
    have hs1 : s1.comp g0 = (u1.comp w1 - LinearMap.id) - fl.comp s0 := by
      apply LinearMap.ext; intro y
      exact (LinearMap.congr_fun hs1_sub ⟨g0 y, ⟨y, rfl⟩⟩).trans (LinearMap.congr_fun hs1R y)
    have hd2 : ((u2.comp w2 - LinearMap.id) - g0.comp s1).comp g0 = 0 := by
      apply LinearMap.ext; intro y
      simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.zero_apply]
      rw [show w2 (g0 y) = resD1 (Twist K) (w1 y) from LinearMap.congr_fun hw2 y,
          show u2 (resD1 (Twist K) (w1 y)) = g0 (u1 (w1 y)) from LinearMap.congr_fun hu2 (w1 y),
          show s1 (g0 y) = (u1 (w1 y) - y) - fl (s0 y) from LinearMap.congr_fun hs1 y,
          map_sub, map_sub, show g0 (fl (s0 y)) = 0 from LinearMap.congr_fun hg0_fl _, sub_zero, sub_self]
    obtain ⟨b, hb⟩ := desc_of_ker_eq_range hpQ_surj hker_pQ hd2
    refine ⟨b, LinearMap.ext fun w => ?_⟩
    obtain ⟨q0, rfl⟩ := hpQ_surj w
    have h1 := LinearMap.congr_fun hb q0
    have h2 : pQ ((u2 (w2 q0) - q0) - g0 (s1 q0)) = φ (ψ (pQ q0)) - pQ q0 := by
      rw [map_sub, show pQ (g0 (s1 q0)) = 0 from LinearMap.congr_fun hpQ_g0 _, sub_zero, map_sub]
      rw [show pQ (u2 (w2 q0)) = φ (resμ (Twist K) (w2 q0)) from (LinearMap.congr_fun hφ (w2 q0)).symm,
          show resμ (Twist K) (w2 q0) = ψ (pQ q0) from (LinearMap.congr_fun hψ q0).symm]
    have h3 : pQ (b (pQ q0)) = φ (ψ (pQ q0)) - pQ q0 := (congrArg pQ h1).trans h2
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply]
    rw [h3, sub_eq_add_neg, neg_eq_self_mod, ← add_assoc, add_self_zmod2_mod, zero_add]
  obtain ⟨b, hb⟩ := hφψ
  exact ⟨u0, u1, u2, φ, ψ, t, b, hu0, hu1, hu2, hφ, ht, hb⟩

set_option maxHeartbeats 800000 in
lemma isDistinguishedε_cocone {X Y : ProjΛ} (f : X ⟶ Y) :
    ∃ (Z : ProjΛ) (g : Y ⟶ Z) (h : Z ⟶ X⟦(1 : ℤ)⟧),
      IsDistinguishedε (Triangle.mk f g h) := by
  classical
  let fl : X.carrier →ₗ[Λ] Y.carrier := ProjΛ.toLin f
  let K : Submodule Λ X.carrier := LinearMap.ker fl
  let ι : K →ₗ[Λ] X.carrier := K.subtype
  have hι : Function.Injective ι := Submodule.injective_subtype K
  let I : Submodule Λ Y.carrier := LinearMap.range fl
  let C := Y.carrier ⧸ I
  let q : Y.carrier →ₗ[Λ] C := I.mkQ
  have hq_surj : Function.Surjective q := Submodule.mkQ_surjective I
  let Q : ProjΛ := P0Obj (Twist C)
  let jC : C →ₗ[Λ] Q.carrier := resJK C
  have hjC : Function.Injective jC := resJK_inj
  let g0 : Y.carrier →ₗ[Λ] Q.carrier := jC.comp q
  have hker_g0 : LinearMap.ker g0 = LinearMap.range fl := by
    ext y; simp only [g0, LinearMap.mem_ker, LinearMap.comp_apply]
    constructor
    · intro hy
      have hqy : q y = 0 := hjC (hy.trans (map_zero jC).symm)
      exact (Submodule.Quotient.mk_eq_zero I).mp hqy
    · intro hy
      have hqy : q y = 0 := (Submodule.Quotient.mk_eq_zero I).mpr hy
      rw [hqy, map_zero]
  let W : Submodule Λ (P1 (Twist C)) := LinearMap.range (resD2 (Twist C))
  let pQ : Q.carrier →ₗ[Λ] W := (resD2 (Twist C)).rangeRestrict
  have hpQ_surj : Function.Surjective pQ := LinearMap.surjective_rangeRestrict _
  have hker_pQ : LinearMap.ker pQ = LinearMap.range g0 := by
    have hrg : LinearMap.range g0 = LinearMap.range (resJK C) := by
      ext z; simp only [g0, jC, LinearMap.mem_range, LinearMap.comp_apply]
      constructor
      · rintro ⟨y, rfl⟩; exact ⟨q y, rfl⟩
      · rintro ⟨c, rfl⟩; obtain ⟨y, rfl⟩ := hq_surj c; exact ⟨y, rfl⟩
    rw [LinearMap.ker_rangeRestrict, hrg, ker_resD2_eq_range_resJK]
  have hpQ_g0 : pQ.comp g0 = 0 := by
    apply LinearMap.ext; intro y; change pQ (g0 y) = 0
    exact LinearMap.mem_ker.mp (hker_pQ.symm ▸ LinearMap.mem_range_self g0 y)
  obtain ⟨u0, u1, u2, φ, ψ, t, b, hu0, hu1, hu2, hφ, ht, hb⟩ := isDistinguishedε_cocone_homotopy f
  let piW : W × P0 (Twist K) →ₗ[Λ] Twist K := ψ.coprod (resμ (Twist K))
  let secPiW : Twist K →ₗ[Λ] W × P0 (Twist K) := φ.prod t
  have hPiWsec : piW.comp secPiW = LinearMap.id :=
    LinearMap.ext fun x => LinearMap.congr_fun ht x
  let Pex : Submodule Λ (W × P0 (Twist K)) := LinearMap.ker piW
  have hPex_proj : Module.Projective Λ Pex := by
    let toF : Pex →ₗ[Λ] P0 (Twist K) × Q.carrier :=
      { toFun := fun z => (z.1.2, b z.1.1)
        map_add' := fun x y => Prod.ext rfl (map_add b _ _)
        map_smul' := fun a x => Prod.ext rfl (map_smul b a _) }
    let rawFrom : P0 (Twist K) × Q.carrier →ₗ[Λ] W × P0 (Twist K) :=
      { toFun := fun rq => (φ (resμ (Twist K) rq.1) + pQ rq.2, rq.1)
        map_add' := fun x y => by ext <;> simp [map_add]; abel
        map_smul' := fun a x => by ext <;> simp [map_smul, smul_add] }
    let projPex : W × P0 (Twist K) →ₗ[Λ] Pex :=
      (LinearMap.id + secPiW.comp piW).codRestrict Pex (fun z => by
        simp only [Pex, LinearMap.mem_ker, LinearMap.add_apply, LinearMap.id_apply,
          LinearMap.comp_apply, map_add]
        rw [show piW (secPiW (piW z)) = piW z from LinearMap.congr_fun hPiWsec (piW z), add_self_zmod2_mod])
    let fromF : P0 (Twist K) × Q.carrier →ₗ[Λ] Pex := projPex.comp rawFrom
    have hsplit : fromF.comp toF = LinearMap.id := by
      apply LinearMap.ext; intro ⟨⟨w, r⟩, hwr⟩; apply Subtype.ext
      have hPi0 : ψ w + resμ (Twist K) r = 0 := hwr
      have hψw : ψ w = resμ (Twist K) r := by
        have h := congrArg (· + resμ (Twist K) r) hPi0
        simpa [add_assoc, add_self_zmod2_mod] using h
      have hw : φ (resμ (Twist K) r) + pQ (b w) = w := by
        rw [← hψw]; exact LinearMap.congr_fun hb w
      have hraw : rawFrom (r, b w) = (w, r) := Prod.ext hw rfl
      change rawFrom (r, b w) + secPiW (piW (rawFrom (r, b w))) = (w, r)
      rw [hraw, hwr, map_zero, add_zero]
    exact Module.Projective.of_split toF fromF hsplit
  haveI : Module.Projective Λ Pex := hPex_proj
  let PexObj : ProjΛ := ⟨Pex⟩
  let ρ : Q.carrier × P0 (Twist K) →ₗ[Λ] W × P0 (Twist K) := LinearMap.prodMap pQ LinearMap.id
  have hρ_surj : Function.Surjective ρ := fun ⟨w, r⟩ => by
    obtain ⟨q0, rfl⟩ := hpQ_surj w; exact ⟨(q0, r), rfl⟩
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property ρ Pex.subtype hρ_surj
  have hσ_inj : Function.Injective σ := fun x y hxy =>
    Submodule.injective_subtype Pex ((LinearMap.congr_fun hσ x).symm.trans ((congrArg ρ hxy).trans (LinearMap.congr_fun hσ y)))
  obtain ⟨τ, hτ⟩ := ProjΛ.injective PexObj σ hσ_inj LinearMap.id
  let Z0Sub : Submodule Λ (Q.carrier × P0 (Twist K)) := LinearMap.ker τ
  let projZ0 : Q.carrier × P0 (Twist K) →ₗ[Λ] Z0Sub :=
    (LinearMap.id + σ.comp τ).codRestrict Z0Sub (fun z => by
      simp only [Z0Sub, LinearMap.mem_ker, LinearMap.add_apply, LinearMap.id_apply,
        LinearMap.comp_apply, map_add]
      rw [show τ (σ (τ z)) = τ z from LinearMap.congr_fun hτ (τ z), add_self_zmod2_mod])
  haveI : Module.Projective Λ Z0Sub :=
    Module.Projective.of_split Z0Sub.subtype projZ0 (LinearMap.ext fun ⟨z, hz⟩ => Subtype.ext (by
      change z + σ (τ z) = z; rw [hz, map_zero, add_zero]))
  let Z0 : ProjΛ := ⟨Z0Sub⟩
  let g_final : Y ⟶ Z0 := projZ0.comp (g0.prod 0)
  let h0_surj : Z0.carrier →ₗ[Λ] Twist K := (piW.comp ρ).comp Z0Sub.subtype
  have hPiρσ : (piW.comp ρ).comp σ = 0 := by
    apply LinearMap.ext; intro z; change piW (ρ (σ z)) = 0
    rw [show ρ (σ z) = z.1 from LinearMap.congr_fun hσ z]
    exact z.2
  have hPiρ_projZ0 : h0_surj.comp projZ0 = piW.comp ρ := by
    apply LinearMap.ext; intro z; change piW (ρ (z + σ (τ z))) = piW (ρ z)
    rw [map_add, map_add, show piW (ρ (σ (τ z))) = 0 from LinearMap.congr_fun hPiρσ (τ z), add_zero]
  let β : Twist K ≃ₗ[Λ] Twist K := epsEquiv (Twist K)
  let h_surj : Z0.carrier →ₗ[Λ] Twist K := β.toLinearMap.comp h0_surj
  let h_final : Z0 ⟶ X⟦(1 : ℤ)⟧ := (Twist.map ι).comp h_surj
  have hker_gf : LinearMap.ker (ProjΛ.toLin g_final) = LinearMap.range fl := by
    rw [← hker_g0]; ext y; simp only [LinearMap.mem_ker]
    constructor
    · intro hy
      have h0 : (g0 y, (0 : P0 (Twist K))) + σ (τ (g0 y, 0)) = 0 := congrArg Subtype.val hy
      have hρ0 : ρ (g0 y, (0 : P0 (Twist K))) = 0 :=
        Prod.ext (LinearMap.congr_fun hpQ_g0 y) rfl
      have hτ0 : (τ (g0 y, (0 : P0 (Twist K)))).1 = 0 := by
        have := congrArg ρ h0
        rw [map_add, map_zero, hρ0, zero_add] at this
        rwa [show ρ (σ (τ (g0 y, 0))) = (τ (g0 y, 0)).1 from LinearMap.congr_fun hσ _] at this
      have hτz : τ (g0 y, (0 : P0 (Twist K))) = 0 := Subtype.ext hτ0
      rw [hτz, map_zero, add_zero] at h0
      exact congrArg Prod.fst h0
    · intro hy
      apply Subtype.ext
      have hpair : (g0 y, (0 : P0 (Twist K))) = 0 := Prod.ext hy rfl
      change (g0 y, (0 : P0 (Twist K))) + σ (τ (g0 y, 0)) = 0
      rw [hpair, map_zero, map_zero, add_zero]
  have hker_h0 : LinearMap.ker h0_surj = LinearMap.range (ProjΛ.toLin g_final) := by
    ext ⟨z, hz⟩; simp only [LinearMap.mem_ker, LinearMap.mem_range]
    constructor
    · intro h0
      have hρz : ρ z ∈ Pex := h0
      let z' : Q.carrier × P0 (Twist K) := z + σ ⟨ρ z, hρz⟩
      have hρz' : ρ z' = 0 := by
        simp only [z', map_add, show ρ (σ ⟨ρ z, hρz⟩) = ρ z from LinearMap.congr_fun hσ ⟨ρ z, hρz⟩,
          add_self_zmod2_mod]
      have hz'2 : z'.2 = 0 := congrArg Prod.snd hρz'
      have hz'1 : z'.1 ∈ LinearMap.range g0 := by
        rw [← hker_pQ, LinearMap.mem_ker]; exact congrArg Prod.fst hρz'
      obtain ⟨y, hy⟩ := hz'1
      have hz'_eq : z' = (g0 y, 0) := Prod.ext hy.symm hz'2
      refine ⟨y, Subtype.ext ?_⟩
      change (g0 y, (0 : P0 (Twist K))) + σ (τ (g0 y, 0)) = z
      rw [← hz'_eq]
      have hτz' : τ z' = ⟨ρ z, hρz⟩ := by
        have h1 : τ (z + σ ⟨ρ z, hρz⟩) = τ z + τ (σ ⟨ρ z, hρz⟩) := map_add τ _ _
        have h2 : τ (σ ⟨ρ z, hρz⟩) = ⟨ρ z, hρz⟩ := LinearMap.congr_fun hτ ⟨ρ z, hρz⟩
        rw [h1, hz, zero_add, h2]
      rw [hτz']
      change (z + σ ⟨ρ z, hρz⟩) + σ ⟨ρ z, hρz⟩ = z
      rw [add_assoc, add_self_zmod2_mod, add_zero]
    · rintro ⟨y, hy⟩
      rw [← hy]
      have h1 := LinearMap.congr_fun hPiρ_projZ0 (g0 y, 0)
      simp only [LinearMap.comp_apply] at h1
      change h0_surj (projZ0 (g0 y, 0)) = 0
      rw [h1]
      simp only [piW, ρ, LinearMap.coprod_apply, LinearMap.prodMap_apply, LinearMap.id_apply,
        show pQ (g0 y) = 0 from LinearMap.congr_fun hpQ_g0 y, map_zero, add_zero]
  have h0_surj_surj : Function.Surjective h0_surj := fun x => by
    obtain ⟨z, hz⟩ := hρ_surj (secPiW x)
    refine ⟨projZ0 z, ?_⟩
    rw [show h0_surj (projZ0 z) = piW (ρ z) from LinearMap.congr_fun hPiρ_projZ0 z]
    change piW (ρ z) = x
    rw [hz]; exact LinearMap.congr_fun hPiWsec x
  have hT : IsExact3 (Triangle.mk f g_final h_final) := by
    refine ⟨hker_gf, ?_, ?_⟩
    · change LinearMap.ker ((Twist.map ι).comp (β.toLinearMap.comp h0_surj)) = LinearMap.range (ProjΛ.toLin g_final)
      rw [← hker_h0]; ext z; simp only [LinearMap.mem_ker, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
      constructor
      · intro hz; exact β.injective (by
          rw [map_zero]; exact Twist.ext (hι (congrArg Twist.val hz)))
      · intro hz; rw [hz, map_zero, map_zero]
    · ext x; simp only [Triangle.mk_mor₁, Triangle.mk_mor₃, LinearMap.mem_ker, LinearMap.mem_range]
      constructor
      · intro hx
        have hxk : x.val ∈ K := congrArg Twist.val hx
        obtain ⟨z, hz⟩ := h0_surj_surj (β.symm ⟨⟨x.val, hxk⟩⟩)
        refine ⟨z, ?_⟩
        change Twist.map ι (β (h0_surj z)) = x
        rw [hz, β.apply_symm_apply]; rfl
      · rintro ⟨z, rfl⟩
        apply Twist.ext
        exact (β (h0_surj z)).val.2
  let u2_0 : P0 (Twist K) →ₗ[Λ] Z0.carrier := projZ0.comp (u2.prod (t.comp (resμ (Twist K))))
  have hu2_0_h0 : h0_surj.comp u2_0 = resμ (Twist K) := by
    apply LinearMap.ext; intro p
    have h1 := LinearMap.congr_fun hPiρ_projZ0 (u2 p, t (resμ (Twist K) p))
    simp only [u2_0, LinearMap.comp_apply, LinearMap.prod_apply, Function.prod_apply] at h1 ⊢
    rw [h1]
    simp only [piW, ρ, LinearMap.coprod_apply, LinearMap.prodMap_apply, LinearMap.id_apply]
    rw [show pQ (u2 p) = φ (resμ (Twist K) p) from (LinearMap.congr_fun hφ p).symm]
    exact LinearMap.congr_fun ht (resμ (Twist K) p)
  have hu2_0_d1 : u2_0.comp (resD1 (Twist K)) = (ProjΛ.toLin g_final).comp u1 := by
    apply LinearMap.ext; intro p
    change projZ0 (u2 (resD1 (Twist K) p), t (resμ (Twist K) (resD1 (Twist K) p))) =
      projZ0 (g0 (u1 p), 0)
    rw [show u2 (resD1 (Twist K) p) = g0 (u1 p) from LinearMap.congr_fun hu2 p,
        resμ_comp_resD1, map_zero]
  let α_final : K →ₗ[Λ] K :=
    (Twist.involEquiv (N := K)).toLinearMap.comp
      ((Twist.map β.toLinearMap).comp (Twist.involEquiv (N := K)).symm.toLinearMap)
  have hL : HasLiftWith (Triangle.mk f g_final h_final) hT α_final := by
    refine ⟨u0.comp (P0.map β.toLinearMap), u1.comp (P1.map β.toLinearMap),
      u2_0.comp (P0.map β.toLinearMap), ?_, ?_, ?_, ?_⟩
    · have hsurj : surjMor3 (Triangle.mk f g_final h_final) hT = h_surj := LinearMap.ext fun _ => rfl
      rw [hsurj]
      apply LinearMap.ext; intro p
      have h1 : h0_surj (u2_0 (P0.map β.toLinearMap p)) = resμ (Twist K) (P0.map β.toLinearMap p) :=
        LinearMap.congr_fun hu2_0_h0 (P0.map β.toLinearMap p)
      have h2 : resμ (Twist K) (P0.map β.toLinearMap p) = β.toLinearMap (resμ (Twist K) p) :=
        (LinearMap.congr_fun (resμ_nat β.toLinearMap) p).symm
      change β (h0_surj (u2_0 (P0.map β.toLinearMap p))) = resμ (Twist K) p
      rw [h1, h2]
      exact β.left_inv (resμ (Twist K) p)
    · change (ProjΛ.toLin g_final).comp (u1.comp (P1.map β.toLinearMap)) =
        (u2_0.comp (P0.map β.toLinearMap)).comp (resD1 (Twist K))
      rw [← LinearMap.comp_assoc, ← hu2_0_d1, LinearMap.comp_assoc, LinearMap.comp_assoc]
      exact congrArg (u2_0.comp ·) (resD1_nat β.toLinearMap).symm
    · change fl.comp (u0.comp (P0.map β.toLinearMap)) =
        (u1.comp (P1.map β.toLinearMap)).comp (resD2 (Twist K))
      rw [← LinearMap.comp_assoc, ← hu1, LinearMap.comp_assoc, LinearMap.comp_assoc]
      exact congrArg (u1.comp ·) (resD2_nat β.toLinearMap).symm
    · apply LinearMap.ext; intro k
      have hrj : P0.map β.toLinearMap (resJK K k) = resJK K (α_final k) :=
        LinearMap.congr_fun (resJ_nat β.toLinearMap) ⟨⟨k⟩⟩
      change ι (α_final k) = u0 (P0.map β.toLinearMap (resJK K k))
      rw [hrj, show u0 (resJK K (α_final k)) = ι (α_final k) from LinearMap.congr_fun hu0 (α_final k)]
  refine ⟨Z0, g_final, h_final, hT, α_final, hL, ?_⟩
  have htw := deltaTotal_twist K
  have heq : α_final - (LinearMap.id + deltaTotal K) =
      (Twist.involEquiv (N := K)).toLinearMap.comp
        ((Twist.map (deltaTotal (Twist K) - Twist.map (deltaTotal K))).comp
          (Twist.involEquiv (N := K)).symm.toLinearMap) := by
    apply LinearMap.ext; intro k
    change (β ⟨k⟩).val - (k + deltaTotal K k) = (deltaTotal (Twist K) ⟨k⟩).val - deltaTotal K k
    change (k + (deltaTotal (Twist K) ⟨k⟩).val) - (k + deltaTotal K k) = _
    abel
  suffices FactorsThroughProj (α_final - ((LinearMap.id : K →ₗ[Λ] K) + deltaTotal K)) from this
  rw [heq]
  have hneg : deltaTotal (Twist K) - Twist.map (deltaTotal K) = -(Twist.map (deltaTotal K) - deltaTotal (Twist K)) := by
    abel
  rw [hneg]
  exact FactorsThroughProj_comp_left _ (FactorsThroughProj_comp_right (FactorsThroughProj_twist (FactorsThroughProj_neg htw)) _)

/- ### Axiom 4: `rotate_distinguished_triangle` -/
/-- Exactness of `P0.map` and `P1.map` on short exact sequences (used for Axiom 4 and Part 5). -/
lemma P0_map_comp_eq_zero {A B C : Type*}
    [AddCommGroup A] [Module Λ A] [Module (ZMod 2) A] [IsScalarTower (ZMod 2) Λ A]
    [AddCommGroup B] [Module Λ B] [Module (ZMod 2) B] [IsScalarTower (ZMod 2) Λ B]
    [AddCommGroup C] [Module Λ C] [Module (ZMod 2) C] [IsScalarTower (ZMod 2) Λ C]
    {u : A →ₗ[Λ] B} {p : B →ₗ[Λ] C} (h : p.comp u = 0) :
    (P0.map p).comp (P0.map u) = 0 := by
  apply LinearMap.ext; intro f; apply P0.ext; funext w; exact LinearMap.congr_fun h (f.fn w)

lemma P1_map_comp_eq_zero {A B C : Type*}
    [AddCommGroup A] [Module Λ A] [Module (ZMod 2) A] [IsScalarTower (ZMod 2) Λ A]
    [AddCommGroup B] [Module Λ B] [Module (ZMod 2) B] [IsScalarTower (ZMod 2) Λ B]
    [AddCommGroup C] [Module Λ C] [Module (ZMod 2) C] [IsScalarTower (ZMod 2) Λ C]
    {u : A →ₗ[Λ] B} {p : B →ₗ[Λ] C} (h : p.comp u = 0) :
    (P1.map p).comp (P1.map u) = 0 := by
  apply LinearMap.ext; intro f; apply P1.ext; funext q; exact LinearMap.congr_fun h (f.fn q)

/-- Exactness is invariant under rotation in `ProjΛ`. -/
lemma isExact3_rotate_iff (T : Triangle ProjΛ) :
    IsExact3 T ↔ IsExact3 T.rotate := by
  have hneg : ProjΛ.toLin T.rotate.mor₃ = Twist.map (ProjΛ.toLin T.mor₁) := by
    change ProjΛ.toLin (-(T.mor₁⟦(1 : ℤ)⟧')) = _
    rw [neg_hom_eq_self]; rfl
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h2, ?_, ?_⟩
    · rw [hneg]; exact h3
    · rw [hneg]; ext y; simp only [LinearMap.mem_ker, LinearMap.mem_range]
      constructor
      · intro hy
        have hy' : y.val ∈ LinearMap.ker (ProjΛ.toLin T.mor₂) := congrArg Twist.val hy
        rw [h1] at hy'
        obtain ⟨x, hx⟩ := hy'
        exact ⟨⟨x⟩, Twist.ext hx⟩
      · rintro ⟨x, rfl⟩
        apply Twist.ext
        exact LinearMap.mem_ker.mp (h1.symm ▸ LinearMap.mem_range_self (ProjΛ.toLin T.mor₁) x.val)
  · rintro ⟨h2, h3, h1t⟩
    dsimp only [Triangle.rotate, Triangle.mk_obj₁, Triangle.mk_obj₂, Triangle.mk_obj₃,
      Triangle.mk_mor₁, Triangle.mk_mor₂, Triangle.mk_mor₃] at h2 h3 h1t
    have h3' : LinearMap.ker (Twist.map (ProjΛ.toLin T.mor₁)) = LinearMap.range (ProjΛ.toLin T.mor₃) := by
      rw [← hneg]; exact h3
    have h1t' : LinearMap.ker (Twist.map (ProjΛ.toLin T.mor₂)) = LinearMap.range (Twist.map (ProjΛ.toLin T.mor₁)) := by
      rw [← hneg]; exact h1t
    refine ⟨?_, h2, h3'⟩
    ext y; simp only [LinearMap.mem_ker, LinearMap.mem_range]
    constructor
    · intro hy
      have hy' : (⟨y⟩ : Twist T.obj₂.carrier) ∈ LinearMap.ker (Twist.map (ProjΛ.toLin T.mor₂)) :=
        Twist.ext hy
      rw [h1t'] at hy'
      obtain ⟨x, hx⟩ := hy'
      exact ⟨x.val, congrArg Twist.val hx⟩
    · rintro ⟨x, rfl⟩
      have hmem : (⟨ProjΛ.toLin T.mor₁ x⟩ : Twist T.obj₂.carrier) ∈ LinearMap.range (Twist.map (ProjΛ.toLin T.mor₁)) :=
        ⟨⟨x⟩, rfl⟩
      rw [← h1t'] at hmem
      exact congrArg Twist.val hmem

/-- Surjection `T.obj₁ ↠ kerT T.rotate` induced by `T.mor₁` for an exact triangle `T`. -/
def fSurjRot (T : Triangle ProjΛ) (hT : IsExact3 T) :
    T.obj₁.carrier →ₗ[Λ] kerT T.rotate :=
  (ProjΛ.toLin T.mor₁).codRestrict (kerT T.rotate) (fun x => LinearMap.congr_fun (mor2_comp_mor1 T hT) x)

/-- Key syzygy relation between comparison maps of `T` and `T.rotate`! -/
lemma rotate_comparison_syzygy (T : Triangle ProjΛ) (hT : IsExact3 T)
    {α : kerT T →ₗ[Λ] kerT T} {β : kerT T.rotate →ₗ[Λ] kerT T.rotate}
    (hL : HasLiftWith T hT α) (hL' : HasLiftWith T.rotate ((isExact3_rotate_iff T).mp hT) β) :
    ∃ (L : T.obj₁.carrier →ₗ[Λ] T.obj₁.carrier) (αL : kerT T →ₗ[Λ] kerT T),
      (fSurjRot T hT).comp L = β.comp (fSurjRot T hT) ∧ (inclKerT T).comp αL = L.comp (inclKerT T) ∧
      FactorsThroughProj (αL - α) := by
  let f_surj := fSurjRot T hT
  have hTr := (isExact3_rotate_iff T).mp hT
  have hneg : ProjΛ.toLin T.rotate.mor₃ = Twist.map (ProjΛ.toLin T.mor₁) := by
    change ProjΛ.toLin (-(T.mor₁⟦(1 : ℤ)⟧')) = _
    rw [neg_hom_eq_self]; rfl
  let K := kerT T
  let I := kerT T.rotate
  let ι : K →ₗ[Λ] T.obj₁.carrier := inclKerT T
  let ιI : I →ₗ[Λ] T.obj₂.carrier := inclKerT T.rotate
  have hf_eq : ιI.comp f_surj = ProjΛ.toLin T.mor₁ := LinearMap.ext fun _ => rfl
  have hf_surj_comp_ι : f_surj.comp ι = 0 :=
    LinearMap.ext fun k => Subtype.ext k.2
  have hf_surj_surj : Function.Surjective f_surj := fun ⟨y, hy⟩ => by
    have hy' : y ∈ LinearMap.range (ProjΛ.toLin T.mor₁) := hT.1 ▸ hy
    obtain ⟨x, hx⟩ := hy'; exact ⟨x, Subtype.ext hx⟩
  rcases hL' with ⟨v0, v1, v2, hv2, hv1, hv0, hβ⟩
  let i_tw : Twist K →ₗ[Λ] Twist T.obj₁.carrier := Twist.map ι
  let p_tw : Twist T.obj₁.carrier →ₗ[Λ] Twist I := Twist.map f_surj
  have hi_tw_inj : Function.Injective i_tw := fun a b hab => Twist.ext (inclKerT_inj T (congrArg Twist.val hab))
  have hp_tw_comp_i : p_tw.comp i_tw = 0 := by
    apply LinearMap.ext; intro k; apply Twist.ext
    exact LinearMap.congr_fun hf_surj_comp_ι k.val
  have hker_ptw : LinearMap.ker p_tw = LinearMap.range i_tw := by
    ext x; simp only [LinearMap.mem_ker, LinearMap.mem_range]
    constructor
    · intro hx
      have hx' : x.val ∈ K := congrArg (fun t : Twist I => t.val.1) hx
      exact ⟨⟨⟨x.val, hx'⟩⟩, rfl⟩
    · rintro ⟨k, rfl⟩; exact LinearMap.congr_fun hp_tw_comp_i k
  let i0 : P0 (Twist K) →ₗ[Λ] P0 (Twist T.obj₁.carrier) := P0.map i_tw
  let p0 : P0 (Twist T.obj₁.carrier) →ₗ[Λ] P0 (Twist I) := P0.map p_tw
  let i1 : P1 (Twist K) →ₗ[Λ] P1 (Twist T.obj₁.carrier) := P1.map i_tw
  let p1 : P1 (Twist T.obj₁.carrier) →ₗ[Λ] P1 (Twist I) := P1.map p_tw
  haveI : Module.Projective Λ (P0 (Twist T.obj₁.carrier)) := (P0Obj (Twist T.obj₁.carrier)).proj
  haveI : Module.Projective Λ (P1 (Twist T.obj₁.carrier)) := (P1Obj (Twist T.obj₁.carrier)).proj
  let v0' : P0 (Twist I) →ₗ[Λ] T.obj₂.carrier := v0
  let v1' : P1 (Twist I) →ₗ[Λ] T.obj₃.carrier := v1
  let v2' : P0 (Twist I) →ₗ[Λ] Twist T.obj₁.carrier := v2
  have hv2_eq : p_tw.comp v2' = resμ (Twist I) := by
    apply LinearMap.ext; intro p; apply Twist.ext; apply Subtype.ext
    have h1 := LinearMap.congr_fun hv2 p
    have h2 : (ProjΛ.toLin T.rotate.mor₃ (v2 p)).val = (resμ (Twist I) p).val.1 :=
      congrArg (fun t : Twist I => t.val.1) h1
    have h3 : (ProjΛ.toLin T.rotate.mor₃ (v2 p)).val = ProjΛ.toLin T.mor₁ (v2' p).val :=
      congrArg Twist.val (LinearMap.congr_fun hneg (v2 p))
    exact h3.symm.trans h2
  have hd2_ker : p_tw.comp (v2'.comp p0 - resμ (Twist T.obj₁.carrier)) = 0 := by
    rw [LinearMap.comp_sub, ← LinearMap.comp_assoc, hv2_eq, resμ_nat p_tw, sub_self]
  obtain ⟨w2', hw2'⟩ := lift_of_ker_eq_range hi_tw_inj hker_ptw hd2_ker
  obtain ⟨w2, hw2_surj⟩ := Module.projective_lifting_property (surjMor3 T hT) w2' (surjMor3_surj T hT)
  have hw2 : (ProjΛ.toLin T.mor₃).comp w2 = v2'.comp p0 - resμ (Twist T.obj₁.carrier) := by
    apply LinearMap.ext; intro p
    have h1 : i_tw (surjMor3 T hT (w2 p)) = (ProjΛ.toLin T.mor₃) (w2 p) :=
      LinearMap.congr_fun (twist_incl_comp_surjMor3 T hT) (w2 p)
    have h2 : surjMor3 T hT (w2 p) = w2' p := LinearMap.congr_fun hw2_surj p
    have h3 : i_tw (w2' p) = (v2'.comp p0 - resμ (Twist T.obj₁.carrier)) p := LinearMap.congr_fun hw2' p
    exact h1.symm.trans ((congrArg i_tw h2).trans h3)
  have hw1_mem : ∀ p : P1 (Twist T.obj₁.carrier),
      (v1'.comp p1 - w2.comp (resD1 (Twist T.obj₁.carrier))) p ∈ LinearMap.range (ProjΛ.toLin T.mor₂) := by
    intro p; rw [← hT.2.1, LinearMap.mem_ker]
    have h1p : ProjΛ.toLin T.mor₃ (v1' (p1 p)) = v2' (resD1 (Twist I) (p1 p)) :=
      LinearMap.congr_fun hv1 (p1 p)
    have h2p : ProjΛ.toLin T.mor₃ (w2 (resD1 (Twist T.obj₁.carrier) p)) =
        v2' (p0 (resD1 (Twist T.obj₁.carrier) p)) - resμ (Twist T.obj₁.carrier) (resD1 (Twist T.obj₁.carrier) p) :=
      LinearMap.congr_fun hw2 (resD1 (Twist T.obj₁.carrier) p)
    change ProjΛ.toLin T.mor₃ (v1' (p1 p) - w2 (resD1 (Twist T.obj₁.carrier) p)) = 0
    rw [map_sub, h1p, h2p, resμ_comp_resD1, sub_zero,
        show p0 (resD1 (Twist T.obj₁.carrier) p) = resD1 (Twist I) (p1 p) from LinearMap.congr_fun (resD1_nat p_tw) p]
    exact sub_self _
  obtain ⟨w1, hw1R⟩ := Module.projective_lifting_property (ProjΛ.toLin T.mor₂).rangeRestrict
    ((v1'.comp p1 - w2.comp (resD1 (Twist T.obj₁.carrier))).codRestrict _ hw1_mem)
    (LinearMap.surjective_rangeRestrict _)
  have hw1 : (ProjΛ.toLin T.mor₂).comp w1 = v1'.comp p1 - w2.comp (resD1 (Twist T.obj₁.carrier)) := by
    ext p; exact congrArg Subtype.val (LinearMap.congr_fun hw1R p)
  have hw0_mem : ∀ p : P0 (Twist T.obj₁.carrier),
      (v0'.comp p0 - w1.comp (resD2 (Twist T.obj₁.carrier))) p ∈ LinearMap.range (ProjΛ.toLin T.mor₁) := by
    intro p; rw [← hT.1, LinearMap.mem_ker]
    have h1p : ProjΛ.toLin T.mor₂ (v0' (p0 p)) = v1' (resD2 (Twist I) (p0 p)) :=
      LinearMap.congr_fun hv0 (p0 p)
    have h2p : ProjΛ.toLin T.mor₂ (w1 (resD2 (Twist T.obj₁.carrier) p)) =
        v1' (p1 (resD2 (Twist T.obj₁.carrier) p)) - w2 (resD1 (Twist T.obj₁.carrier) (resD2 (Twist T.obj₁.carrier) p)) :=
      LinearMap.congr_fun hw1 (resD2 (Twist T.obj₁.carrier) p)
    change ProjΛ.toLin T.mor₂ (v0' (p0 p) - w1 (resD2 (Twist T.obj₁.carrier) p)) = 0
    rw [map_sub, h1p, h2p, resD1_comp_resD2, map_zero, sub_zero,
        show p1 (resD2 (Twist T.obj₁.carrier) p) = resD2 (Twist I) (p0 p) from LinearMap.congr_fun (resD2_nat p_tw) p,
        sub_self]
  obtain ⟨w0, hw0R⟩ := Module.projective_lifting_property (ProjΛ.toLin T.mor₁).rangeRestrict
    ((v0'.comp p0 - w1.comp (resD2 (Twist T.obj₁.carrier))).codRestrict _ hw0_mem)
    (LinearMap.surjective_rangeRestrict _)
  have hw0 : (ProjΛ.toLin T.mor₁).comp w0 = v0'.comp p0 - w1.comp (resD2 (Twist T.obj₁.carrier)) := by
    ext p; exact congrArg Subtype.val (LinearMap.congr_fun hw0R p)
  let L : T.obj₁.carrier →ₗ[Λ] T.obj₁.carrier := w0.comp (resJK T.obj₁.carrier)
  have hfL : f_surj.comp L = β.comp f_surj := by
    apply LinearMap.ext; intro x; apply Subtype.ext
    change ProjΛ.toLin T.mor₁ (w0 (resJK T.obj₁.carrier x)) = ιI (β (f_surj x))
    rw [show ProjΛ.toLin T.mor₁ (w0 (resJK T.obj₁.carrier x)) =
          v0' (p0 (resJK T.obj₁.carrier x)) - w1 (resD2 (Twist T.obj₁.carrier) (resJK T.obj₁.carrier x))
          from LinearMap.congr_fun hw0 (resJK T.obj₁.carrier x)]
    rw [show resD2 (Twist T.obj₁.carrier) (resJK T.obj₁.carrier x) = 0 from LinearMap.congr_fun resD2_comp_resJK x,
        map_zero, sub_zero,
        show p0 (resJK T.obj₁.carrier x) = resJK I (f_surj x) from LinearMap.congr_fun (resJK_nat f_surj) x]
    exact (LinearMap.congr_fun hβ (f_surj x)).symm
  have hL_ker : (ProjΛ.toLin T.mor₁).comp (L.comp ι) = 0 := by
    apply LinearMap.ext; intro k
    simp only [LinearMap.comp_apply, LinearMap.zero_apply]
    change ιI (f_surj (L (ι k))) = 0
    rw [show f_surj (L (ι k)) = β (f_surj (ι k)) from LinearMap.congr_fun hfL (ι k),
        show f_surj (ι k) = 0 from LinearMap.congr_fun hf_surj_comp_ι k, map_zero, map_zero]
  let αL : K →ₗ[Λ] K := (L.comp ι).codRestrict K (fun k => LinearMap.congr_fun hL_ker k)
  have hαL_eq : ι.comp αL = L.comp ι := LinearMap.ext fun _ => rfl
  have hL_new : HasLiftWith T hT αL := by
    refine ⟨w0.comp i0, w1.comp i1, w2.comp i0, ?_, ?_, ?_, ?_⟩
    · apply LinearMap.ext; intro p; apply hi_tw_inj
      have h1 : (ProjΛ.toLin T.mor₃) (w2 (i0 p)) = v2' (p0 (i0 p)) - resμ (Twist T.obj₁.carrier) (i0 p) :=
        LinearMap.congr_fun hw2 (i0 p)
      have hp0i0 : p0 (i0 p) = 0 := LinearMap.congr_fun (P0_map_comp_eq_zero hp_tw_comp_i) p
      have hnat : resμ (Twist T.obj₁.carrier) (i0 p) = i_tw (resμ (Twist K) p) :=
        (LinearMap.congr_fun (resμ_nat i_tw) p).symm
      change i_tw (surjMor3 T hT (w2 (i0 p))) = i_tw (resμ (Twist K) p)
      have hmor : i_tw (surjMor3 T hT (w2 (i0 p))) = (ProjΛ.toLin T.mor₃) (w2 (i0 p)) := rfl
      rw [hmor, h1, hp0i0, map_zero, zero_sub, neg_eq_self_mod, hnat]
    · apply LinearMap.ext; intro p
      have h1 := LinearMap.congr_fun hw1 (i1 p)
      have hp1i1 : p1 (i1 p) = 0 := LinearMap.congr_fun (P1_map_comp_eq_zero hp_tw_comp_i) p
      have hnat := LinearMap.congr_fun (resD1_nat i_tw) p
      simp only [LinearMap.comp_apply, LinearMap.sub_apply] at h1 hnat ⊢
      rw [h1, hp1i1, map_zero, zero_sub, neg_eq_self_mod, hnat]
    · apply LinearMap.ext; intro p
      have h1 := LinearMap.congr_fun hw0 (i0 p)
      have hp0i0 : p0 (i0 p) = 0 := LinearMap.congr_fun (P0_map_comp_eq_zero hp_tw_comp_i) p
      have hnat := LinearMap.congr_fun (resD2_nat i_tw) p
      simp only [LinearMap.comp_apply, LinearMap.sub_apply] at h1 hnat ⊢
      rw [h1, hp0i0, map_zero, zero_sub, neg_eq_self_mod, hnat]
    · apply LinearMap.ext; intro k
      change ι (αL k) = w0 (i0 (resJK K k))
      rw [show ι (αL k) = L (ι k) from LinearMap.congr_fun hαL_eq k,
          show i0 (resJK K k) = resJK T.obj₁.carrier (ι k) from LinearMap.congr_fun (resJK_nat ι) k]
      rfl
  exact ⟨L, αL, hfL, hαL_eq, genLift_unique_mod_proj T hT LinearMap.id hL_new hL⟩

lemma isDistinguishedε_rotate_iff (T : Triangle ProjΛ) :
    IsDistinguishedε T ↔ IsDistinguishedε T.rotate := by
  constructor
  · rintro ⟨hT, α, hL, hF⟩
    have hTr := (isExact3_rotate_iff T).mp hT
    obtain ⟨β, hL'⟩ := exists_genLift T.rotate hTr LinearMap.id
    rw [isDistinguishedε_iff_of_lift T.rotate hTr hL']
    let f_surj := fSurjRot T hT
    have hf_surj : Function.Surjective f_surj := fun ⟨y, hy⟩ => by
      obtain ⟨x, hx⟩ := (hT.1 ▸ hy : y ∈ LinearMap.range (ProjΛ.toLin T.mor₁))
      exact ⟨x, Subtype.ext hx⟩
    have hker_f : LinearMap.ker f_surj = LinearMap.range (inclKerT T) := by
      ext x
      constructor
      · intro h; exact ⟨⟨x, congrArg Subtype.val h⟩, rfl⟩
      · rintro ⟨k, rfl⟩; exact Subtype.ext k.2
    have hcomp0 : f_surj.comp (inclKerT T) = 0 := LinearMap.ext fun k => Subtype.ext k.2
    obtain ⟨L, αL, hfL, hαL, hU⟩ := rotate_comparison_syzygy T hT hL hL'
    obtain ⟨L', α', hfL', hα'⟩ := syzygy_exists hcomp0 (inclKerT_inj T) hf_surj hker_f
      (LinearMap.id + deltaTotal (kerT T.rotate))
    have hα'_eq : FactorsThroughProj (α' - (LinearMap.id + deltaTotal (kerT T))) := by
      have hL_d : f_surj.comp (L' - LinearMap.id) = (deltaTotal (kerT T.rotate)).comp f_surj := by
        apply LinearMap.ext; intro x
        have hx := LinearMap.congr_fun hfL' x
        simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.add_apply,
          LinearMap.id_apply, map_sub] at hx ⊢
        rw [hx]; abel
      have hα_d : (inclKerT T).comp (α' - LinearMap.id) = (L' - LinearMap.id).comp (inclKerT T) := by
        rw [LinearMap.comp_sub, LinearMap.sub_comp, hα', LinearMap.comp_id, LinearMap.id_comp]
      have hd := deltaTotal_omega (inclKerT_inj T) hf_surj hker_f hL_d hα_d
      have heq : α' - (LinearMap.id + deltaTotal (kerT T)) = (α' - LinearMap.id) - deltaTotal (kerT T) := by abel
      rw [heq]; exact hd
    have hdiff_α : FactorsThroughProj (αL - α') := by
      have heq : αL - α' = (αL - α) + (α - (LinearMap.id + deltaTotal (kerT T))) -
          (α' - (LinearMap.id + deltaTotal (kerT T))) := by abel
      rw [heq]; exact FactorsThroughProj_sub (FactorsThroughProj_add hU hF) hα'_eq
    have hLdiff : (L - L').comp (inclKerT T) = (inclKerT T).comp (αL - α') := by
      rw [LinearMap.sub_comp, LinearMap.comp_sub, hαL, hα']
    have hfdiff : (β - (LinearMap.id + deltaTotal (kerT T.rotate))).comp f_surj = f_surj.comp (L - L') := by
      apply LinearMap.ext; intro x
      have h1 := LinearMap.congr_fun hfL x
      have h2 := LinearMap.congr_fun hfL' x
      simp only [LinearMap.comp_apply, LinearMap.sub_apply, map_sub] at h1 h2 ⊢
      rw [h1, h2]
    exact cosyzygy_of_factors (inclKerT_inj T) hf_surj hker_f hcomp0 hdiff_α hLdiff hfdiff
  · rintro ⟨hTr, β, hL', hF'⟩
    have hT := (isExact3_rotate_iff T).mpr hTr
    obtain ⟨α, hL⟩ := exists_genLift T hT LinearMap.id
    rw [isDistinguishedε_iff_of_lift T hT hL]
    let f_surj := fSurjRot T hT
    have hf_surj : Function.Surjective f_surj := fun ⟨y, hy⟩ => by
      obtain ⟨x, hx⟩ := (hT.1 ▸ hy : y ∈ LinearMap.range (ProjΛ.toLin T.mor₁))
      exact ⟨x, Subtype.ext hx⟩
    have hker_f : LinearMap.ker f_surj = LinearMap.range (inclKerT T) := by
      ext x
      constructor
      · intro h; exact ⟨⟨x, congrArg Subtype.val h⟩, rfl⟩
      · rintro ⟨k, rfl⟩; exact Subtype.ext k.2
    have hcomp0 : f_surj.comp (inclKerT T) = 0 := LinearMap.ext fun k => Subtype.ext k.2
    obtain ⟨L, αL, hfL, hαL, hU⟩ := rotate_comparison_syzygy T hT hL hL'
    obtain ⟨L', α', hfL', hα'⟩ := syzygy_exists hcomp0 (inclKerT_inj T) hf_surj hker_f
      (LinearMap.id + deltaTotal (kerT T.rotate))
    have hα'_eq : FactorsThroughProj (α' - (LinearMap.id + deltaTotal (kerT T))) := by
      have hL_d : f_surj.comp (L' - LinearMap.id) = (deltaTotal (kerT T.rotate)).comp f_surj := by
        apply LinearMap.ext; intro x
        have hx := LinearMap.congr_fun hfL' x
        simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.add_apply,
          LinearMap.id_apply, map_sub] at hx ⊢
        rw [hx]; abel
      have hα_d : (inclKerT T).comp (α' - LinearMap.id) = (L' - LinearMap.id).comp (inclKerT T) := by
        rw [LinearMap.comp_sub, LinearMap.sub_comp, hα', LinearMap.comp_id, LinearMap.id_comp]
      have hd := deltaTotal_omega (inclKerT_inj T) hf_surj hker_f hL_d hα_d
      have heq : α' - (LinearMap.id + deltaTotal (kerT T)) = (α' - LinearMap.id) - deltaTotal (kerT T) := by abel
      rw [heq]; exact hd
    have hdiff_α : FactorsThroughProj (αL - α') :=
      syzygy_of_factors (L := L - L') (ψ := αL - α') hcomp0 (inclKerT_inj T) hf_surj hker_f hF'
        (by
          apply LinearMap.ext; intro x
          have h1 := LinearMap.congr_fun hfL x
          have h2 := LinearMap.congr_fun hfL' x
          simp only [LinearMap.comp_apply, LinearMap.sub_apply, map_sub] at h1 h2 ⊢
          rw [h1, h2])
        (by rw [LinearMap.comp_sub, hαL, hα', LinearMap.sub_comp])
    have heq : α - (LinearMap.id + deltaTotal (kerT T)) =
        -(αL - α) + (αL - α') + (α' - (LinearMap.id + deltaTotal (kerT T))) := by abel
    rw [heq]
    exact FactorsThroughProj_add (FactorsThroughProj_add (FactorsThroughProj_neg hU) hdiff_α) hα'_eq

/- ### Axiom 5: `complete_distinguished_triangle_morphism` -/
lemma isDistinguishedε_complete (T1 T2 : Triangle ProjΛ)
    (h1 : IsDistinguishedε T1) (h2 : IsDistinguishedε T2)
    (a : T1.obj₁ ⟶ T2.obj₁) (b : T1.obj₂ ⟶ T2.obj₂)
    (hab : CategoryStruct.comp T1.mor₁ b = CategoryStruct.comp a T2.mor₁) :
    ∃ c : T1.obj₃ ⟶ T2.obj₃,
      CategoryStruct.comp T1.mor₂ c = CategoryStruct.comp b T2.mor₂ ∧
      CategoryStruct.comp T1.mor₃ (a⟦(1 : ℤ)⟧') = CategoryStruct.comp c T2.mor₃ := by
  rcases h1 with ⟨hT1, α1, hL1, hF1⟩
  rcases h2 with ⟨hT2, α2, hL2, hF2⟩
  have hab_apply : ∀ x : T1.obj₁.carrier,
      ProjΛ.toLin b (ProjΛ.toLin T1.mor₁ x) = ProjΛ.toLin T2.mor₁ (ProjΛ.toLin a x) :=
    fun x => LinearMap.congr_fun hab x
  let φ : kerT T1 →ₗ[Λ] kerT T2 :=
    ((ProjΛ.toLin a).comp (inclKerT T1)).codRestrict (kerT T2) (fun k => by
      change ProjΛ.toLin T2.mor₁ (ProjΛ.toLin a k.1) = 0
      rw [← hab_apply k.1, k.2, map_zero])
  have hgb_ker : ((ProjΛ.toLin T2.mor₂).comp (ProjΛ.toLin b)).comp (ProjΛ.toLin T1.mor₁) = 0 := by
    apply LinearMap.ext; intro x
    change ProjΛ.toLin T2.mor₂ (ProjΛ.toLin b (ProjΛ.toLin T1.mor₁ x)) = 0
    rw [hab_apply x]; exact LinearMap.congr_fun (mor2_comp_mor1 T2 hT2) _
  obtain ⟨c0R, hc0R⟩ := desc_of_ker_eq_range (LinearMap.surjective_rangeRestrict (ProjΛ.toLin T1.mor₂))
    (by rw [LinearMap.ker_rangeRestrict]; exact hT1.1) hgb_ker
  obtain ⟨c0, hc0_sub⟩ := ProjΛ.injective T2.obj₃ (LinearMap.range (ProjΛ.toLin T1.mor₂)).subtype
    (Submodule.injective_subtype _) c0R
  have hc0 : c0.comp (ProjΛ.toLin T1.mor₂) = (ProjΛ.toLin T2.mor₂).comp (ProjΛ.toLin b) := by
    ext y; exact (LinearMap.congr_fun hc0_sub ⟨ProjΛ.toLin T1.mor₂ y, ⟨y, rfl⟩⟩).trans (LinearMap.congr_fun hc0R y)
  have hhc0_ker : ((surjMor3 T2 hT2).comp c0).comp (ProjΛ.toLin T1.mor₂) = 0 := by
    rw [LinearMap.comp_assoc, hc0, ← LinearMap.comp_assoc, surjMor3_comp_mor2 T2 hT2, LinearMap.zero_comp]
  obtain ⟨ψ, hψ⟩ := desc_of_ker_eq_range (surjMor3_surj T1 hT1) (ker_surjMor3_eq_range_mor2 T1 hT1) hhc0_ker
  let ψun : kerT T1 →ₗ[Λ] kerT T2 :=
    (Twist.involEquiv (N := kerT T2)).toLinearMap.comp
      ((Twist.map ψ).comp (Twist.involEquiv (N := kerT T1)).symm.toLinearMap)
  have hψun_tw : Twist.map ψun = ψ := by ext x; rfl
  rcases hL1 with ⟨u0, u1, u2, hu2, hu1, hu0, hα1⟩
  rcases hL2 with ⟨v0, v1, v2, hv2, hv1, hv0, hα2⟩
  have hL_a : HasGenLift T2 hT2 ψ (φ.comp α1) := by
    refine ⟨(ProjΛ.toLin a).comp u0, (ProjΛ.toLin b).comp u1, c0.comp u2, ?_, ?_, ?_, ?_⟩
    · rw [← LinearMap.comp_assoc, ← hψ, LinearMap.comp_assoc, hu2, LinearMap.id_comp]
    · rw [← LinearMap.comp_assoc, ← hc0, LinearMap.comp_assoc, hu1, LinearMap.comp_assoc]
    · apply LinearMap.ext; intro p
      exact (hab_apply (u0 p)).symm.trans (congrArg (ProjΛ.toLin b) (LinearMap.congr_fun hu0 p))
    · apply LinearMap.ext; intro k; exact congrArg (ProjΛ.toLin a) (LinearMap.congr_fun hα1 k)
  have hL_b : HasGenLift T2 hT2 ψ (α2.comp ψun) := by
    refine ⟨v0.comp (P0.map ψ), v1.comp (P1.map ψ), v2.comp (P0.map ψ), ?_, ?_, ?_, ?_⟩
    · rw [← LinearMap.comp_assoc, hv2, LinearMap.id_comp, ← resμ_nat]
    · rw [← LinearMap.comp_assoc, hv1, LinearMap.comp_assoc, ← resD1_nat, LinearMap.comp_assoc]
    · rw [← LinearMap.comp_assoc, hv0, LinearMap.comp_assoc, ← resD2_nat, LinearMap.comp_assoc]
    · rw [← LinearMap.comp_assoc, hα2, LinearMap.comp_assoc, ← hψun_tw, ← resJK_nat, LinearMap.comp_assoc]
  have hU := genLift_unique_mod_proj T2 hT2 ψ hL_a hL_b
  have hnat := deltaTotal_natural φ
  have hprod : FactorsThroughProj ((LinearMap.id + deltaTotal (kerT T2)).comp (φ - ψun)) := by
    have heq : (LinearMap.id + deltaTotal (kerT T2)).comp (φ - ψun) =
        (φ.comp α1 - α2.comp ψun) - φ.comp (α1 - (LinearMap.id + deltaTotal (kerT T1))) +
        (α2 - (LinearMap.id + deltaTotal (kerT T2))).comp ψun -
        (φ.comp (deltaTotal (kerT T1)) - (deltaTotal (kerT T2)).comp φ) := by
      apply LinearMap.ext; intro k
      simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sub_apply,
        LinearMap.id_apply, map_sub, map_add]
      abel
    rw [heq]
    exact FactorsThroughProj_sub
      (FactorsThroughProj_add
        (FactorsThroughProj_sub hU (FactorsThroughProj_comp_left φ hF1))
        (FactorsThroughProj_comp_right hF2 ψun))
      hnat
  have hfac_un : FactorsThroughProj (φ - ψun) := by
    have hmul := FactorsThroughProj_comp_left (epsEquiv (kerT T2)).toLinearMap hprod
    have heq : (epsEquiv (kerT T2)).toLinearMap.comp ((LinearMap.id + deltaTotal (kerT T2)).comp (φ - ψun)) =
        φ - ψun := by
      apply LinearMap.ext; intro k; exact (epsEquiv (kerT T2)).left_inv ((φ - ψun) k)
    rwa [heq] at hmul
  have hfac_ψ : FactorsThroughProj (Twist.map φ - ψ) := by
    have htw := FactorsThroughProj_twist hfac_un
    have heq : Twist.map (φ - ψun) = Twist.map φ - ψ := by ext x; rfl
    rwa [heq] at htw
  obtain ⟨d, hd⟩ := (FactorsThroughProj_iff_exists_epi T2.obj₃ (surjMor3 T2 hT2) (surjMor3_surj T2 hT2) _).mp hfac_ψ
  let c : T1.obj₃ ⟶ T2.obj₃ := c0 + d.comp (surjMor3 T1 hT1)
  refine ⟨c, ?_, ?_⟩
  · apply ProjΛ.hom_ext; intro y
    change c0 (ProjΛ.toLin T1.mor₂ y) + d (surjMor3 T1 hT1 (ProjΛ.toLin T1.mor₂ y)) =
      ProjΛ.toLin T2.mor₂ (ProjΛ.toLin b y)
    rw [show surjMor3 T1 hT1 (ProjΛ.toLin T1.mor₂ y) = 0 from LinearMap.congr_fun (surjMor3_comp_mor2 T1 hT1) y,
        map_zero, add_zero]
    exact LinearMap.congr_fun hc0 y
  · apply ProjΛ.hom_ext; intro z; apply Twist.ext
    have h1 : (surjMor3 T2 hT2 (c0 z)).val.1 = (ψ (surjMor3 T1 hT1 z)).val.1 :=
      congrArg (fun t : Twist (kerT T2) => t.val.1) (LinearMap.congr_fun hψ z).symm
    have h2 : (surjMor3 T2 hT2 (d (surjMor3 T1 hT1 z))).val.1 =
        (Twist.map φ (surjMor3 T1 hT1 z) - ψ (surjMor3 T1 hT1 z)).val.1 :=
      congrArg (fun t : Twist (kerT T2) => t.val.1) (LinearMap.congr_fun hd (surjMor3 T1 hT1 z)).symm
    change ProjΛ.toLin a (ProjΛ.toLin T1.mor₃ z).val =
      (ProjΛ.toLin T2.mor₃ (c0 z + d (surjMor3 T1 hT1 z))).val
    rw [map_add]
    change ProjΛ.toLin a (ProjΛ.toLin T1.mor₃ z).val =
      (surjMor3 T2 hT2 (c0 z)).val.1 + (surjMor3 T2 hT2 (d (surjMor3 T1 hT1 z))).val.1
    rw [h1, h2]
    change ProjΛ.toLin a (ProjΛ.toLin T1.mor₃ z).val =
      (ψ (surjMor3 T1 hT1 z)).val.1 + (ProjΛ.toLin a (ProjΛ.toLin T1.mor₃ z).val - (ψ (surjMor3 T1 hT1 z)).val.1)
    abel

/-- The twisted pretriangulated structure `(ProjΛ, (-)_\nu, Δ_{θ_ε})`! -/
instance instPretriangulatedProjΛ : Pretriangulated ProjΛ where
  distinguishedTriangles := { T | IsDistinguishedε T }
  isomorphic_distinguished := isDistinguishedε_of_iso
  contractible_distinguished := isDistinguishedε_contractible
  distinguished_cocone_triangle := isDistinguishedε_cocone
  rotate_distinguished_triangle := isDistinguishedε_rotate_iff
  complete_distinguished_triangle_morphism := isDistinguishedε_complete

end PretriangulatedProj

/-
## Part 5: Pushouts `ModA`, `ModB`, Relative Filler, 3-Octahedron Contradiction, and Universe Lift
-/
section OctahedralFailure

open ModM CategoryTheory.Pretriangulated

noncomputable instance instFintypeQuotient {X : Type} [AddCommGroup X] [Module Λ X]
    [Fintype X] (S : Submodule Λ X) : Fintype (X ⧸ S) := by
  classical exact inferInstance

lemma zmod2_eq_one_of_ne_zero {x : ZMod 2} (hx : x ≠ 0) : x = 1 := by
  fin_cases x
  · exact absurd rfl hx
  · rfl

lemma add_self_Λ {X : Type*} [AddCommGroup X] [Module Λ X] (x : X) : x + x = 0 := by
  have h2 : (1 : Λ) + (1 : Λ) = 0 := by
    apply Λ.ext; funext b; change (1 : Λ).coeff b + (1 : Λ).coeff b = 0; exact CharTwo.add_self_eq_zero _
  calc x + x = (1 : Λ) • x + (1 : Λ) • x := by rw [one_smul]
    _ = ((1 : Λ) + (1 : Λ)) • x := (add_smul 1 1 x).symm
    _ = 0 := by rw [h2, zero_smul]

lemma neg_eq_self_Λ {X : Type*} [AddCommGroup X] [Module Λ X] (x : X) : -x = x :=
  eq_of_sub_eq_zero (by rw [sub_eq_add_neg]; exact add_self_Λ (-x))

lemma eq_of_add_eq_zero_Λ {X : Type*} [AddCommGroup X] [Module Λ X] {x y : X}
    (h : x + y = 0) : x = y := by
  rw [eq_neg_of_add_eq_zero_left h, neg_eq_self_Λ]

lemma qForm_eq_zero_of_factors {N : Type} [AddCommGroup N] [Module Λ N]
    [Module (ZMod 2) N] [IsScalarTower (ZMod 2) Λ N] [Fintype N]
    (f : N →ₗ[Λ] ModM) (g : ModM →ₗ[Λ] N)
    (h : FactorsThroughProj ((f.comp g).comp ρM)) :
    qForm N f g = 0 := by
  have heq : κMν.comp (f.comp (g.comp (ρM.comp πM))) = κMν.comp (((f.comp g).comp ρM).comp πM) :=
    LinearMap.ext fun _ => rfl
  change trPhiP02 (κMν.comp (f.comp (g.comp (ρM.comp πM)))) = 0
  rw [heq]; exact trPhiP02_factors_eq_zero h

lemma qForm_eq_of_sub_factors {N : Type} [AddCommGroup N] [Module Λ N]
    [Module (ZMod 2) N] [IsScalarTower (ZMod 2) Λ N] [Fintype N]
    (f : N →ₗ[Λ] ModM) (g g1 : ModM →ₗ[Λ] N)
    (h : FactorsThroughProj ((f.comp (g - g1)).comp ρM)) :
    qForm N f g = qForm N f g1 := by
  apply sub_eq_zero.mp
  rw [← map_sub]
  exact qForm_eq_zero_of_factors f (g - g1) h

lemma basisVec_200_smul_vec_zero (x : ModM) :
    (basisVec (mkB 2 0 0 rfl) • x).vec 0 = 0 := by
  rw [basisVec_smul_M]
  change ∑ c : Fin 7, actMat (mkB 2 0 0 rfl) 0 c * x.vec c = 0
  have hc : ∀ c : Fin 7, actMat (mkB 2 0 0 rfl) 0 c = 0 := fun c => by fin_cases c <;> decide
  simp [hc]

lemma liftρM_comp_liftρM : liftρM.comp liftρM = 0 := by
  apply LinearMap.ext; intro p
  exact Prod.ext rfl (LProj.ext (zero_mul _))

/-- Twisted lift `liftρMν : P42 →ₗ[Λ] P42` of `Twist.map ρM` realizing `Ω(Twist.map ρM) = ρM + pM`. -/
def liftρMν : P42 →ₗ[Λ] P42 :=
  nuP02.toLinearMap.comp ((Twist.map liftρM).comp nuP02.symm.toLinearMap)

lemma πMν_comp_liftρMν : πMν.comp liftρMν = (Twist.map ρM).comp πMν := by
  apply LinearMap.ext; intro p; apply Twist.ext
  simp only [πMν, liftρMν, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearEquiv.symm_apply_apply]
  exact LinearMap.congr_fun πM_comp_liftρM (nuP02.symm p).val

lemma liftρMν_comp_κMν : liftρMν.comp κMν = κMν.comp (ρM + pM) := by
  apply LinearMap.ext; intro m
  simp only [liftρMν, κMν, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearEquiv.symm_apply_apply]
  exact congrArg (fun p : P02 => nuP02 ⟨p⟩) (LinearMap.congr_fun liftρM_comp_κM ⟨m⟩)

/-- Helper: syzygy of an endomorphism `w : ModM →ₗ[Λ] ModM` along `πM : P02 ↠ ModM`. -/
lemma syzygy_endM_mod_proj (w : ModM →ₗ[Λ] ModM)
    {L : P02 →ₗ[Λ] P02} {s : Twist ModM →ₗ[Λ] Twist ModM}
    (hL : πM.comp L = w.comp πM) (hs : κM.comp s = L.comp κM) :
    FactorsThroughProj (s - (((w (eVec 0)).vec 0) • LinearMap.id +
      ((w (eVec 0)).vec 1 + (w (eVec 4)).vec 5) • Twist.map ρM)) := by
  have hw := endM_decomp w
  let c : ZMod 2 := (w (eVec 0)).vec 0
  let b : ZMod 2 := (w (eVec 0)).vec 1 + (w (eVec 4)).vec 5
  let d : ZMod 2 := (w (eVec 4)).vec 5
  let L0 : P02 →ₗ[Λ] P02 := c • LinearMap.id + b • liftρM
  let ψ0 : Twist ModM →ₗ[Λ] Twist ModM := c • LinearMap.id + b • Twist.map (ρM + pM)
  have hL0 : πM.comp L0 = (c • LinearMap.id + b • ρM).comp πM := by
    apply LinearMap.ext; intro p
    have hsc : ∀ (a : ZMod 2) (q : P02), πM (a • q) = a • πM q := fun a q => by
      have := map_smul πM (algebraMap (ZMod 2) Λ a) q
      simp only [algebraMap_smul] at this; exact this
    simp only [L0, LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply,
      LinearMap.id_apply, map_add, hsc]
    rw [show πM (liftρM p) = ρM (πM p) from LinearMap.congr_fun πM_comp_liftρM p]
  have hψ0 : κM.comp ψ0 = L0.comp κM := by
    apply LinearMap.ext; intro x
    have hsc : ∀ (a : ZMod 2) (z : Twist ModM), κM (a • z) = a • κM z := fun a z => by
      have := map_smul κM (algebraMap (ZMod 2) Λ a) z
      simp only [algebraMap_smul] at this; exact this
    simp only [L0, ψ0, LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply,
      LinearMap.id_apply, map_add, hsc]
    rw [show liftρM (κM x) = κM (Twist.map (ρM + pM) x) from LinearMap.congr_fun liftρM_comp_κM x]
  have hdiffL : πM.comp (L - L0) = (d • pM).comp πM := by
    rw [LinearMap.comp_sub, hL, hL0, hw]
    apply LinearMap.ext; intro p; apply ModM.ext; funext r
    simp only [c, b, d, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.add_apply,
      LinearMap.smul_apply, LinearMap.id_apply, vec_add, vec_sub, vec_smul]
    ring
  have hdiffψ : κM.comp (s - ψ0) = (L - L0).comp κM := by
    rw [LinearMap.comp_sub, LinearMap.sub_comp, hs, hψ0]
  have hfac1 := syzygy_of_factors (P1 := P02Obj) (P2 := P02Obj) πM_comp_κM κM_inj πM_surj
    ker_πM_eq_range_κM (FactorsThroughProj_smul d FactorsThroughProj_pM) hdiffL hdiffψ
  have hfac2 : FactorsThroughProj (b • Twist.map pM) :=
    FactorsThroughProj_smul b (FactorsThroughProj_twist FactorsThroughProj_pM)
  have heq : s - (c • LinearMap.id + b • Twist.map ρM) = (s - ψ0) + b • Twist.map pM := by
    apply LinearMap.ext; intro x; apply Twist.ext; apply ModM.ext; funext r
    change (s x).val.vec r - (c * x.val.vec r + b * (ρM x.val).vec r) =
      ((s x).val.vec r - (c * x.val.vec r + b * ((ρM x.val).vec r + (pM x.val).vec r))) +
        b * (pM x.val).vec r
    ring
  rw [heq]; exact FactorsThroughProj_add hfac1 hfac2

/-- Helper: syzygy of an endomorphism `w : Twist ModM →ₗ[Λ] Twist ModM` along `πMν : P42 ↠ Twist ModM`. -/
lemma syzygy_endMν_mod_proj (w : Twist ModM →ₗ[Λ] Twist ModM)
    {L : P42 →ₗ[Λ] P42} {s : ModM →ₗ[Λ] ModM}
    (hL : πMν.comp L = w.comp πMν) (hs : κMν.comp s = L.comp κMν) :
    let wu : ModM →ₗ[Λ] ModM :=
      (Twist.involEquiv (N := ModM)).toLinearMap.comp
        ((Twist.map w).comp (Twist.involEquiv (N := ModM)).symm.toLinearMap)
    FactorsThroughProj (s - (((wu (eVec 0)).vec 0) • LinearMap.id +
      ((wu (eVec 0)).vec 1 + (wu (eVec 4)).vec 5) • ρM)) := by
  intro wu
  let L0 : P02 →ₗ[Λ] P02 := nuP42.toLinearMap.comp ((Twist.map L).comp nuP42.symm.toLinearMap)
  have hL0 : πM.comp L0 = wu.comp πM := by
    apply LinearMap.ext; intro p
    have h1 := congrArg Twist.val (LinearMap.congr_fun hL (nuP02 ⟨p⟩))
    simp only [πMν, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      LinearEquiv.symm_apply_apply] at h1
    exact h1
  have hs0 : κM.comp (Twist.map s) = L0.comp κM := by
    apply LinearMap.ext; intro x
    have h1 := congrArg (fun q : P42 => (nuP02.symm q).val) (LinearMap.congr_fun hs x.val)
    simp only [κMν, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      LinearEquiv.symm_apply_apply] at h1
    exact h1
  have htw := syzygy_endM_mod_proj wu hL0 hs0
  rw [← FactorsThroughProj_iff_twist]
  have heq : Twist.map (s - (((wu (eVec 0)).vec 0) • LinearMap.id +
        ((wu (eVec 0)).vec 1 + (wu (eVec 4)).vec 5) • ρM)) =
      Twist.map s - (((wu (eVec 0)).vec 0) • LinearMap.id +
        ((wu (eVec 0)).vec 1 + (wu (eVec 4)).vec 5) • Twist.map ρM) := by
    apply LinearMap.ext; intro x; apply Twist.ext; rfl
  rw [heq]; exact htw

/- ### 5A. Pushouts `ModA` and `ModB` and Vanishing of `qForm` -/

/-- Pushout submodule defining `ModA`: `0 → ModM -iA→ ModA -qA→ Twist ModM → 0`. -/
def subA : Submodule Λ (ModM × P42) := LinearMap.range (ρM.prod κMν)

def ModA : Type := (ModM × P42) ⧸ subA

instance : AddCommGroup ModA := Submodule.Quotient.addCommGroup subA
instance : Module Λ ModA := Submodule.Quotient.module subA
instance : Module (ZMod 2) ModA := Submodule.Quotient.module' subA
instance : IsScalarTower (ZMod 2) Λ ModA :=
  ⟨fun c a x => by
    obtain ⟨p, rfl⟩ := Submodule.mkQ_surjective subA x
    change subA.mkQ ((c • a) • p) = subA.mkQ (c • (a • p))
    rw [smul_assoc]⟩
noncomputable instance : Fintype ModA := instFintypeQuotient subA

def mkA : ModM × P42 →ₗ[Λ] ModA := subA.mkQ

lemma mkA_surj : Function.Surjective mkA := Submodule.mkQ_surjective subA

lemma mkA_eq_zero {p : ModM × P42} : mkA p = 0 ↔ p ∈ subA := Submodule.Quotient.mk_eq_zero subA

def iA : ModM →ₗ[Λ] ModA := mkA.comp (LinearMap.inl Λ ModM P42)

def jA : P42 →ₗ[Λ] ModA := mkA.comp (LinearMap.inr Λ ModM P42)

def qA : ModA →ₗ[Λ] Twist ModM :=
  subA.liftQ ((0 : ModM →ₗ[Λ] Twist ModM).coprod πMν) (by
    rintro _ ⟨m, rfl⟩
    simp only [LinearMap.mem_ker, LinearMap.coprod_apply, LinearMap.prod_apply, LinearMap.zero_apply,
      zero_add]
    exact LinearMap.congr_fun πMν_comp_κMν m)

lemma iA_inj : Function.Injective iA := by
  intro m1 m2 h
  have hsub : (m1 - m2, (0 : P42)) ∈ subA := by
    rw [← mkA_eq_zero]
    change iA (m1 - m2) = 0
    rw [map_sub, h, sub_self]
  rcases hsub with ⟨x, hx⟩
  have hx2 : κMν x = 0 := congrArg Prod.snd hx
  have hx0 : x = 0 := κMν_inj (hx2.trans (map_zero κMν).symm)
  have hx1 : ρM x = m1 - m2 := congrArg Prod.fst hx
  rw [hx0, map_zero] at hx1
  exact sub_eq_zero.mp hx1.symm

lemma qA_surj : Function.Surjective qA := fun x => by
  obtain ⟨p, rfl⟩ := πMν_surj x
  exact ⟨jA p, by change 0 + πMν p = πMν p; exact zero_add _⟩

lemma qA_comp_iA : qA.comp iA = 0 := by
  apply LinearMap.ext; intro m; change 0 + πMν 0 = 0; rw [map_zero, add_zero]

lemma qA_comp_jA : qA.comp jA = πMν := by
  apply LinearMap.ext; intro p; change 0 + πMν p = πMν p; exact zero_add _

lemma iA_comp_ρM : iA.comp ρM = jA.comp κMν := by
  apply LinearMap.ext; intro m
  have h0 : mkA (ρM m, κMν m) = 0 := mkA_eq_zero.mpr ⟨m, rfl⟩
  have hsum : iA (ρM m) + jA (κMν m) = 0 := by
    change mkA (ρM m, 0) + mkA (0, κMν m) = 0
    rw [← map_add, show (ρM m, (0 : P42)) + (0, κMν m) = (ρM m, κMν m) from
      Prod.ext (add_zero _) (zero_add _), h0]
  exact eq_of_add_eq_zero_Λ hsum

lemma ker_qA_eq_range_iA : LinearMap.ker qA = LinearMap.range iA := by
  ext a; simp only [LinearMap.mem_ker, LinearMap.mem_range]
  obtain ⟨⟨m, p⟩, rfl⟩ := mkA_surj a
  constructor
  · intro h
    have hp : πMν p = 0 := by change 0 + πMν p = 0 at h; rwa [zero_add] at h
    have hmem : p ∈ LinearMap.range κMν := ker_πMν_eq_range_κMν ▸ hp
    obtain ⟨x, hx⟩ := hmem
    refine ⟨m - ρM x, ?_⟩
    rw [← sub_eq_zero]; change mkA (m - ρM x, 0) - mkA (m, p) = 0
    rw [← map_sub, mkA_eq_zero]
    refine ⟨x, Prod.ext ?_ ?_⟩
    · change ρM x = (m - ρM x) - m
      rw [sub_sub_cancel_left, neg_eq_self_Λ]
    · change κMν x = 0 - p
      rw [hx, zero_sub, neg_eq_self_Λ]
  · rintro ⟨m0, hm0⟩
    rw [← hm0]; exact LinearMap.congr_fun qA_comp_iA m0

/-- Descent `f0 : Twist ModM →ₗ[Λ] ModA` satisfying `qA ∘ f0 = Twist.map ρM` on the nose! -/
lemma jA_comp_liftρMν_comp_κMν : (jA.comp liftρMν).comp κMν = 0 := by
  apply LinearMap.ext; intro m
  change jA (liftρMν (κMν m)) = 0
  rw [show liftρMν (κMν m) = κMν (ρM m + pM m) from LinearMap.congr_fun liftρMν_comp_κMν m,
      show jA (κMν (ρM m + pM m)) = iA (ρM (ρM m + pM m)) from (LinearMap.congr_fun iA_comp_ρM _).symm,
      map_add, show ρM (ρM m) = 0 from LinearMap.congr_fun ρM_comp_ρM m,
      show ρM (pM m) = 0 from LinearMap.congr_fun ρM_comp_pM m, add_zero, map_zero]

noncomputable def f0 : Twist ModM →ₗ[Λ] ModA :=
  (desc_of_ker_eq_range πMν_surj ker_πMν_eq_range_κMν jA_comp_liftρMν_comp_κMν).choose

lemma f0_comp_πMν : f0.comp πMν = jA.comp liftρMν :=
  (desc_of_ker_eq_range πMν_surj ker_πMν_eq_range_κMν jA_comp_liftρMν_comp_κMν).choose_spec

lemma qA_comp_f0 : qA.comp f0 = Twist.map ρM := by
  apply LinearMap.ext; intro x
  obtain ⟨p, rfl⟩ := πMν_surj x
  change qA (f0 (πMν p)) = Twist.map ρM (πMν p)
  rw [show f0 (πMν p) = jA (liftρMν p) from LinearMap.congr_fun f0_comp_πMν p,
      show qA (jA (liftρMν p)) = πMν (liftρMν p) from LinearMap.congr_fun qA_comp_jA _]
  exact LinearMap.congr_fun πMν_comp_liftρMν p

/-- Pushout submodule defining `ModB`: `0 → ModA -uB→ ModB -pB→ ModM → 0`. -/
noncomputable def subB : Submodule Λ (ModA × P02) := LinearMap.range (f0.prod κM)

def ModB : Type := (ModA × P02) ⧸ subB

noncomputable instance : AddCommGroup ModB := Submodule.Quotient.addCommGroup subB
noncomputable instance : Module Λ ModB := Submodule.Quotient.module subB
noncomputable instance : Module (ZMod 2) ModB := Submodule.Quotient.module' subB
noncomputable instance : IsScalarTower (ZMod 2) Λ ModB :=
  ⟨fun c a x => by
    obtain ⟨p, rfl⟩ := Submodule.mkQ_surjective subB x
    change subB.mkQ ((c • a) • p) = subB.mkQ (c • (a • p))
    rw [smul_assoc]⟩
noncomputable instance : Fintype ModB := instFintypeQuotient subB

noncomputable def mkModB : ModA × P02 →ₗ[Λ] ModB := subB.mkQ

lemma mkModB_surj : Function.Surjective mkModB := Submodule.mkQ_surjective subB

lemma mkModB_eq_zero {p : ModA × P02} : mkModB p = 0 ↔ p ∈ subB := Submodule.Quotient.mk_eq_zero subB

noncomputable def uB : ModA →ₗ[Λ] ModB := mkModB.comp (LinearMap.inl Λ ModA P02)

noncomputable def vB : P02 →ₗ[Λ] ModB := mkModB.comp (LinearMap.inr Λ ModA P02)

noncomputable def pB : ModB →ₗ[Λ] ModM :=
  subB.liftQ ((0 : ModA →ₗ[Λ] ModM).coprod πM) (by
    rintro _ ⟨x, rfl⟩
    simp only [LinearMap.mem_ker, LinearMap.coprod_apply, LinearMap.prod_apply, LinearMap.zero_apply,
      zero_add]
    exact LinearMap.congr_fun πM_comp_κM x)

lemma uB_inj : Function.Injective uB := by
  intro a1 a2 h
  have hsub : (a1 - a2, (0 : P02)) ∈ subB := by
    rw [← mkModB_eq_zero]
    change uB (a1 - a2) = 0
    rw [map_sub, h, sub_self]
  rcases hsub with ⟨x, hx⟩
  have hx2 : κM x = 0 := congrArg Prod.snd hx
  have hx0 : x = 0 := κM_inj (hx2.trans (map_zero κM).symm)
  have hx1 : f0 x = a1 - a2 := congrArg Prod.fst hx
  rw [hx0, map_zero] at hx1
  exact sub_eq_zero.mp hx1.symm

lemma pB_surj : Function.Surjective pB := fun m => by
  obtain ⟨p, rfl⟩ := πM_surj m
  exact ⟨vB p, by change 0 + πM p = πM p; exact zero_add _⟩

lemma pB_comp_uB : pB.comp uB = 0 := by
  apply LinearMap.ext; intro a; change 0 + πM 0 = 0; rw [map_zero, add_zero]

lemma pB_comp_vB : pB.comp vB = πM := by
  apply LinearMap.ext; intro p; change 0 + πM p = πM p; exact zero_add _

lemma uB_comp_f0 : uB.comp f0 = vB.comp κM := by
  apply LinearMap.ext; intro x
  have h0 : mkModB (f0 x, κM x) = 0 := mkModB_eq_zero.mpr ⟨x, rfl⟩
  have hsum : uB (f0 x) + vB (κM x) = 0 := by
    change mkModB (f0 x, 0) + mkModB (0, κM x) = 0
    rw [← map_add, show (f0 x, (0 : P02)) + (0, κM x) = (f0 x, κM x) from
      Prod.ext (add_zero _) (zero_add _), h0]
  exact eq_of_add_eq_zero_Λ hsum

lemma ker_pB_eq_range_uB : LinearMap.ker pB = LinearMap.range uB := by
  ext b; simp only [LinearMap.mem_ker, LinearMap.mem_range]
  obtain ⟨⟨a, p⟩, rfl⟩ := mkModB_surj b
  constructor
  · intro h
    have hp : πM p = 0 := by change 0 + πM p = 0 at h; rwa [zero_add] at h
    have hmem : p ∈ LinearMap.range κM := ker_πM_eq_range_κM ▸ hp
    obtain ⟨x, hx⟩ := hmem
    refine ⟨a - f0 x, ?_⟩
    rw [← sub_eq_zero]; change mkModB (a - f0 x, 0) - mkModB (a, p) = 0
    rw [← map_sub, mkModB_eq_zero]
    refine ⟨x, Prod.ext ?_ ?_⟩
    · change f0 x = (a - f0 x) - a
      rw [sub_sub_cancel_left, neg_eq_self_Λ]
    · change κM x = 0 - p
      rw [hx, zero_sub, neg_eq_self_Λ]
  · rintro ⟨a0, ha0⟩
    rw [← ha0]; exact LinearMap.congr_fun pB_comp_uB a0

/-- Every `f : ModA →ₗ[Λ] ModM` satisfies `(f ∘ iA) (eVec 0) .vec 0 = 0`, hence `f ∘ iA = b • ρM + d • pM`. -/
lemma hom_ModA_ModM_comp_iA_coeff0 (f : ModA →ₗ[Λ] ModM) :
    ((f.comp iA) (eVec 0)).vec 0 = 0 := by
  have hfac : FactorsThroughProj ((f.comp iA).comp ρM) := by
    rw [LinearMap.comp_assoc, iA_comp_ρM, ← LinearMap.comp_assoc]
    exact ⟨P42Obj, κMν, f.comp jA, rfl⟩
  have hd := endM_decomp (f.comp iA)
  have heq : (f.comp iA).comp ρM = ((f.comp iA) (eVec 0)).vec 0 • ρM := by
    conv_lhs => rw [hd]
    apply LinearMap.ext; intro m
    simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply]
    rw [show ρM (ρM m) = 0 from LinearMap.congr_fun ρM_comp_ρM m,
        show pM (ρM m) = 0 from LinearMap.congr_fun pM_comp_ρM m, smul_zero, smul_zero, add_zero, add_zero]
  rw [heq] at hfac
  by_contra hc
  rw [zmod2_eq_one_of_ne_zero hc, one_smul] at hfac
  exact not_factors_ρM hfac

lemma qForm_ModA_zero (f : ModA →ₗ[Λ] ModM) (g : ModM →ₗ[Λ] ModA) :
    qForm ModA f g = 0 := by
  obtain ⟨h, hh⟩ := (FactorsThroughProj_to_TwistModM (qA.comp g)).mp (hom_ModM_Twist_factors (qA.comp g))
  have hker : qA.comp (g - jA.comp h) = 0 := by
    rw [LinearMap.comp_sub, ← LinearMap.comp_assoc, qA_comp_jA, hh, sub_self]
  obtain ⟨u, hu⟩ := lift_of_ker_eq_range iA_inj ker_qA_eq_range_iA hker
  have hg : g = iA.comp u + jA.comp h := by
    apply LinearMap.ext; intro m
    have h1 := LinearMap.congr_fun hu m
    simp only [LinearMap.comp_apply, LinearMap.sub_apply] at h1
    change g m = iA (u m) + jA (h m)
    rw [h1]; abel
  have hfi : f.comp iA = (((f.comp iA) (eVec 0)).vec 1 + ((f.comp iA) (eVec 4)).vec 5) • ρM +
      ((f.comp iA) (eVec 4)).vec 5 • pM := by
    have hd := endM_decomp (f.comp iA)
    rw [hom_ModA_ModM_comp_iA_coeff0 f, zero_smul, zero_add] at hd
    exact hd
  have hfac : FactorsThroughProj ((f.comp g).comp ρM) := by
    have heq : (f.comp g).comp ρM =
        ((f.comp iA) (eVec 4)).vec 5 • (pM.comp (u.comp ρM)) + ((f.comp jA).comp h).comp ρM := by
      apply LinearMap.ext; intro m
      have hgm : g (ρM m) = iA (u (ρM m)) + jA (h (ρM m)) := LinearMap.congr_fun hg (ρM m)
      have hfim := LinearMap.congr_fun hfi (u (ρM m))
      simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply] at hfim ⊢
      rw [hgm, map_add, hfim,
          show ρM (u (ρM m)) = 0 from LinearMap.congr_fun (ρM_comp_endM_comp_ρM u) m,
          smul_zero, zero_add]
    rw [heq]
    exact FactorsThroughProj_add
      (FactorsThroughProj_smul _ (FactorsThroughProj_comp_right FactorsThroughProj_pM _))
      (FactorsThroughProj_comp_right ⟨P42Obj, h, f.comp jA, rfl⟩ ρM)
  exact qForm_eq_zero_of_factors f g hfac

/-- Every `g' : Twist ModM →ₗ[Λ] ModA` has `qA ∘ g'` with zero identity coefficient! -/
lemma qA_comp_hom_TwistModM_decomp (g' : Twist ModM →ₗ[Λ] ModA) :
    let w : ModM →ₗ[Λ] ModM :=
      (Twist.involEquiv (N := ModM)).toLinearMap.comp
        ((Twist.map (qA.comp g')).comp (Twist.involEquiv (N := ModM)).symm.toLinearMap)
    qA.comp g' = ((w (eVec 0)).vec 1 + (w (eVec 4)).vec 5) • Twist.map ρM +
      ((w (eVec 4)).vec 5) • Twist.map pM := by
  intro w
  haveI : Module.Projective Λ P42 := P42Obj.proj
  obtain ⟨pair, hpair⟩ := Module.projective_lifting_property mkA (g'.comp πMν) mkA_surj
  let a : P42 →ₗ[Λ] ModM := (LinearMap.fst Λ ModM P42).comp pair
  let L : P42 →ₗ[Λ] P42 := (LinearMap.snd Λ ModM P42).comp pair
  have hdecomp : g'.comp πMν = iA.comp a + jA.comp L := by
    apply LinearMap.ext; intro p
    have hp := LinearMap.congr_fun hpair p
    simp only [LinearMap.comp_apply] at hp
    change g' (πMν p) = mkA (a p, 0) + mkA (0, L p)
    rw [← map_add, ← hp]; congr 1; exact Prod.ext (add_zero _).symm (zero_add _).symm
  have hL : πMν.comp L = (qA.comp g').comp πMν := by
    apply LinearMap.ext; intro p
    have hp := LinearMap.congr_fun hdecomp p
    simp only [LinearMap.comp_apply, LinearMap.add_apply] at hp
    change πMν (L p) = qA (g' (πMν p))
    rw [hp, map_add, show qA (iA (a p)) = 0 from LinearMap.congr_fun qA_comp_iA (a p), zero_add]
    exact (LinearMap.congr_fun qA_comp_jA (L p)).symm
  have hLκ_ker : πMν.comp (L.comp κMν) = 0 := by
    rw [← LinearMap.comp_assoc, hL, LinearMap.comp_assoc, πMν_comp_κMν, LinearMap.comp_zero]
  obtain ⟨s, hs⟩ := lift_of_ker_eq_range κMν_inj ker_πMν_eq_range_κMν hLκ_ker
  have hρs_fac : FactorsThroughProj (ρM.comp s) := by
    have heq : ρM.comp s = a.comp κMν := by
      apply LinearMap.ext; intro m; apply iA_inj
      have h0 : g' (πMν (κMν m)) = 0 := by
        rw [show πMν (κMν m) = 0 from LinearMap.congr_fun πMν_comp_κMν m, map_zero]
      have h1 := LinearMap.congr_fun hdecomp (κMν m)
      simp only [LinearMap.comp_apply, LinearMap.add_apply] at h1
      rw [h0] at h1
      have h2 := LinearMap.congr_fun hs m
      simp only [LinearMap.comp_apply] at h2
      rw [← h2, show jA (κMν (s m)) = iA (ρM (s m)) from (LinearMap.congr_fun iA_comp_ρM (s m)).symm] at h1
      exact (eq_of_add_eq_zero_Λ h1.symm).symm
    rw [heq]; exact ⟨P42Obj, κMν, a, rfl⟩
  have hsyz := syzygy_endMν_mod_proj (qA.comp g') hL hs
  have hρsyz := FactorsThroughProj_comp_left ρM hsyz
  have hρ_c : FactorsThroughProj (((w (eVec 0)).vec 0) • ρM) := by
    have heq : ((w (eVec 0)).vec 0) • ρM = ρM.comp s -
        ρM.comp (s - (((w (eVec 0)).vec 0) • LinearMap.id +
          ((w (eVec 0)).vec 1 + (w (eVec 4)).vec 5) • ρM)) := by
      apply LinearMap.ext; intro m
      have hsc : ∀ (c : ZMod 2) (x : ModM), ρM (c • x) = c • ρM x := fun c x => by
        have := map_smul ρM (algebraMap (ZMod 2) Λ c) x
        simp only [algebraMap_smul] at this; exact this
      simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.add_apply,
        LinearMap.smul_apply, LinearMap.id_apply, map_sub, map_add, hsc]
      rw [show ρM (ρM m) = 0 from LinearMap.congr_fun ρM_comp_ρM m, smul_zero, add_zero]
      abel
    rw [heq]; exact FactorsThroughProj_sub hρs_fac hρsyz
  have hc0 : (w (eVec 0)).vec 0 = 0 := by
    by_contra hc
    rw [zmod2_eq_one_of_ne_zero hc, one_smul] at hρ_c
    exact not_factors_ρM hρ_c
  have hwd := endM_decomp w
  rw [hc0, zero_smul, zero_add] at hwd
  apply LinearMap.ext; intro x; apply Twist.ext
  have hx := LinearMap.congr_fun hwd x.val
  exact hx

lemma qForm_TwistModA_zero (f : Twist ModA →ₗ[Λ] ModM) (g : ModM →ₗ[Λ] Twist ModA) :
    qForm (Twist ModA) f g = 0 := by
  let f' : ModA →ₗ[Λ] Twist ModM := (Twist.map f).comp (Twist.involEquiv (N := ModA)).symm.toLinearMap
  let g' : Twist ModM →ₗ[Λ] ModA := (Twist.involEquiv (N := ModA)).toLinearMap.comp (Twist.map g)
  have hfj_ker : (f'.comp jA).comp κMν = 0 := by
    rw [LinearMap.comp_assoc, ← iA_comp_ρM, ← LinearMap.comp_assoc]
    exact hom_ModM_Twist_comp_ρM (f'.comp iA)
  obtain ⟨v, hv⟩ := desc_of_ker_eq_range πMν_surj ker_πMν_eq_range_κMν hfj_ker
  let r : ModA →ₗ[Λ] Twist ModM := f' - v.comp qA
  have hqg_ρ : (qA.comp g').comp (Twist.map ρM) = 0 := by
    rw [qA_comp_hom_TwistModM_decomp g']
    apply LinearMap.ext; intro x; apply Twist.ext
    simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.zero_apply]
    change _ • (ρM (ρM x.val)) + _ • (pM (ρM x.val)) = 0
    rw [show ρM (ρM x.val) = 0 from LinearMap.congr_fun ρM_comp_ρM x.val,
        show pM (ρM x.val) = 0 from LinearMap.congr_fun pM_comp_ρM x.val, smul_zero, smul_zero, add_zero]
  have hker_gρ : qA.comp (g'.comp (Twist.map ρM)) = 0 := by
    rw [← LinearMap.comp_assoc]; exact hqg_ρ
  obtain ⟨u, hu⟩ := lift_of_ker_eq_range iA_inj ker_qA_eq_range_iA hker_gρ
  have hfac_tw : FactorsThroughProj ((f'.comp g').comp (Twist.map ρM)) := by
    have heq : (f'.comp g').comp (Twist.map ρM) = (r.comp iA).comp u := by
      apply LinearMap.ext; intro x
      have h1 : g' (Twist.map ρM x) = iA (u x) := (LinearMap.congr_fun hu x).symm
      have h2 : qA (g' (Twist.map ρM x)) = 0 := LinearMap.congr_fun hker_gρ x
      change f' (g' (Twist.map ρM x)) = (f' (iA (u x)) - v (qA (iA (u x))))
      rw [← h1, h2, map_zero, sub_zero]
    rw [heq]; exact FactorsThroughProj_comp_left (r.comp iA) (hom_Twist_ModM_factors u)
  have hfac : FactorsThroughProj ((f.comp g).comp ρM) := by
    rw [← FactorsThroughProj_iff_twist]
    have heq : Twist.map ((f.comp g).comp ρM) = (f'.comp g').comp (Twist.map ρM) := by
      apply LinearMap.ext; intro x; rfl
    rw [heq]; exact hfac_tw
  exact qForm_eq_zero_of_factors f g hfac

lemma deltaTotal_ModA : deltaTotal ModA = 0 :=
  deltaTotal_eq_zero_of_qForm_zero ModA qForm_ModA_zero qForm_TwistModA_zero

/-- Crucial vanishing: EVERY `h : Twist ModM →ₗ[Λ] ModB` factors through projectives! -/
lemma hom_TwistModM_ModB_factors (h : Twist ModM →ₗ[Λ] ModB) : FactorsThroughProj h := by
  obtain ⟨k, hk⟩ := (FactorsThroughProj_to_ModM (pB.comp h)).mp (hom_Twist_ModM_factors (pB.comp h))
  have hker : pB.comp (h - vB.comp k) = 0 := by
    rw [LinearMap.comp_sub, ← LinearMap.comp_assoc, pB_comp_vB, hk, sub_self]
  obtain ⟨g', hg'⟩ := lift_of_ker_eq_range uB_inj ker_pB_eq_range_uB hker
  have hq := qA_comp_hom_TwistModM_decomp g'
  dsimp only at hq
  obtain ⟨l, hl⟩ := (FactorsThroughProj_to_TwistModM (Twist.map pM)).mp
    (FactorsThroughProj_twist FactorsThroughProj_pM)
  let b : ZMod 2 := (((Twist.involEquiv (N := ModM)).toLinearMap.comp
    ((Twist.map (qA.comp g')).comp (Twist.involEquiv (N := ModM)).symm.toLinearMap)) (eVec 0)).vec 1 +
    (((Twist.involEquiv (N := ModM)).toLinearMap.comp
    ((Twist.map (qA.comp g')).comp (Twist.involEquiv (N := ModM)).symm.toLinearMap)) (eVec 4)).vec 5
  let d : ZMod 2 := (((Twist.involEquiv (N := ModM)).toLinearMap.comp
    ((Twist.map (qA.comp g')).comp (Twist.involEquiv (N := ModM)).symm.toLinearMap)) (eVec 4)).vec 5
  have hkerA : qA.comp (g' - (b • f0 + d • jA.comp l)) = 0 := by
    apply LinearMap.ext; intro x
    have hsc : ∀ (c : ZMod 2) (a : ModA), qA (c • a) = c • qA a := fun c a => by
      have := map_smul qA (algebraMap (ZMod 2) Λ c) a
      simp only [algebraMap_smul] at this; exact this
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply,
      map_sub, map_add, hsc, LinearMap.zero_apply]
    rw [show qA (g' x) = b • Twist.map ρM x + d • Twist.map pM x from LinearMap.congr_fun hq x,
        show qA (f0 x) = Twist.map ρM x from LinearMap.congr_fun qA_comp_f0 x,
        show qA (jA (l x)) = πMν (l x) from LinearMap.congr_fun qA_comp_jA (l x),
        show πMν (l x) = Twist.map pM x from (LinearMap.congr_fun hl x).symm, sub_self]
  obtain ⟨w, hw⟩ := lift_of_ker_eq_range iA_inj ker_qA_eq_range_iA hkerA
  have hdecomp : h = vB.comp k + b • (vB.comp κM) + d • ((uB.comp jA).comp l) + (uB.comp iA).comp w := by
    apply LinearMap.ext; intro x
    have h1 := LinearMap.congr_fun hg' x
    have h2 := LinearMap.congr_fun hw x
    have hsc : ∀ (c : ZMod 2) (a : ModA), uB (c • a) = c • uB a := fun c a => by
      have := map_smul uB (algebraMap (ZMod 2) Λ c) a
      simp only [algebraMap_smul] at this; exact this
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply] at h1 h2 ⊢
    have h3 : g' x = iA (w x) + b • f0 x + d • jA (l x) := by
      have := congrArg (· + (b • f0 x + d • jA (l x))) h2
      simpa [add_assoc] using this.symm
    have h4 : uB (g' x) = uB (iA (w x)) + b • vB (κM x) + d • uB (jA (l x)) := by
      rw [h3, map_add, map_add, hsc, hsc, show uB (f0 x) = vB (κM x) from LinearMap.congr_fun uB_comp_f0 x]
    have h5 := congrArg (· + vB (k x)) h1
    simp only [sub_add_cancel] at h5
    rw [← h5, h4]; abel
  rw [hdecomp]
  exact FactorsThroughProj_add
    (FactorsThroughProj_add
      (FactorsThroughProj_add ⟨P02Obj, k, vB, rfl⟩
        (FactorsThroughProj_smul b ⟨P02Obj, κM, vB, rfl⟩))
      (FactorsThroughProj_smul d ⟨P42Obj, l, uB.comp jA, rfl⟩))
    (FactorsThroughProj_comp_left (uB.comp iA) (hom_Twist_ModM_factors w))

lemma qForm_TwistModB_zero (f : Twist ModB →ₗ[Λ] ModM) (g : ModM →ₗ[Λ] Twist ModB) :
    qForm (Twist ModB) f g = 0 := by
  let g' : Twist ModM →ₗ[Λ] ModB := (Twist.involEquiv (N := ModB)).toLinearMap.comp (Twist.map g)
  have hg_fac : FactorsThroughProj g := by
    rw [← FactorsThroughProj_iff_twist]
    have htw := FactorsThroughProj_twist (hom_TwistModM_ModB_factors g')
    have heq : Twist.map g = (Twist.involEquiv (N := ModB)).symm.toLinearMap.comp g' := by
      apply LinearMap.ext; intro x; rfl
    rw [heq]; exact FactorsThroughProj_comp_left _ (hom_TwistModM_ModB_factors g')
  exact qForm_eq_zero_of_factors f g (FactorsThroughProj_comp_right (FactorsThroughProj_comp_left f hg_fac) ρM)

/-- Every `g : ModM →ₗ[Λ] ModB` has `pB ∘ g = b • ρM + d • pM` (zero identity coefficient). -/
lemma pB_comp_hom_ModM_decomp (g : ModM →ₗ[Λ] ModB) :
    pB.comp g = (((pB.comp g) (eVec 0)).vec 1 + ((pB.comp g) (eVec 4)).vec 5) • ρM +
      (((pB.comp g) (eVec 4)).vec 5) • pM := by
  haveI : Module.Projective Λ P02 := P02Obj.proj
  obtain ⟨pair, hpair⟩ := Module.projective_lifting_property mkModB (g.comp πM) mkModB_surj
  let a : P02 →ₗ[Λ] ModA := (LinearMap.fst Λ ModA P02).comp pair
  let L : P02 →ₗ[Λ] P02 := (LinearMap.snd Λ ModA P02).comp pair
  have hdecomp : g.comp πM = uB.comp a + vB.comp L := by
    apply LinearMap.ext; intro p
    have hp := LinearMap.congr_fun hpair p
    simp only [LinearMap.comp_apply] at hp
    change g (πM p) = mkModB (a p, 0) + mkModB (0, L p)
    rw [← map_add, ← hp]; congr 1; exact Prod.ext (add_zero _).symm (zero_add _).symm
  have hL : πM.comp L = (pB.comp g).comp πM := by
    apply LinearMap.ext; intro p
    have hp := LinearMap.congr_fun hdecomp p
    simp only [LinearMap.comp_apply, LinearMap.add_apply] at hp
    change πM (L p) = pB (g (πM p))
    rw [hp, map_add, show pB (uB (a p)) = 0 from LinearMap.congr_fun pB_comp_uB (a p), zero_add]
    exact (LinearMap.congr_fun pB_comp_vB (L p)).symm
  have hLκ_ker : πM.comp (L.comp κM) = 0 := by
    rw [← LinearMap.comp_assoc, hL, LinearMap.comp_assoc, πM_comp_κM, LinearMap.comp_zero]
  obtain ⟨s, hs⟩ := lift_of_ker_eq_range κM_inj ker_πM_eq_range_κM hLκ_ker
  have hf0s : f0.comp s = a.comp κM := by
    apply LinearMap.ext; intro x; apply uB_inj
    have h0 : g (πM (κM x)) = 0 := by
      rw [show πM (κM x) = 0 from LinearMap.congr_fun πM_comp_κM x, map_zero]
    have h1 := LinearMap.congr_fun hdecomp (κM x)
    simp only [LinearMap.comp_apply, LinearMap.add_apply] at h1
    rw [h0] at h1
    have h2 := LinearMap.congr_fun hs x
    simp only [LinearMap.comp_apply] at h2
    rw [← h2, show vB (κM (s x)) = uB (f0 (s x)) from (LinearMap.congr_fun uB_comp_f0 (s x)).symm] at h1
    exact (eq_of_add_eq_zero_Λ h1.symm).symm
  have hρs_fac : FactorsThroughProj ((Twist.map ρM).comp s) := by
    rw [← qA_comp_f0, LinearMap.comp_assoc, hf0s, ← LinearMap.comp_assoc]
    exact ⟨P02Obj, κM, qA.comp a, rfl⟩
  have hsyz := syzygy_endM_mod_proj (pB.comp g) hL hs
  have hρsyz := FactorsThroughProj_comp_left (Twist.map ρM) hsyz
  have hρ_c : FactorsThroughProj ((((pB.comp g) (eVec 0)).vec 0) • Twist.map ρM) := by
    have heq : (((pB.comp g) (eVec 0)).vec 0) • Twist.map ρM = (Twist.map ρM).comp s -
        (Twist.map ρM).comp (s - ((((pB.comp g) (eVec 0)).vec 0) • LinearMap.id +
          (((pB.comp g) (eVec 0)).vec 1 + ((pB.comp g) (eVec 4)).vec 5) • Twist.map ρM)) := by
      apply LinearMap.ext; intro x; apply Twist.ext
      have hsc : ∀ (c : ZMod 2) (m : ModM), ρM (c • m) = c • ρM m := fun c m => by
        have := map_smul ρM (algebraMap (ZMod 2) Λ c) m
        simp only [algebraMap_smul] at this; exact this
      change ((pB.comp g) (eVec 0)).vec 0 • ρM x.val =
        ρM (s x).val - ρM ((s x).val - (((pB.comp g) (eVec 0)).vec 0 • x.val +
          (((pB.comp g) (eVec 0)).vec 1 + ((pB.comp g) (eVec 4)).vec 5) • ρM x.val))
      rw [map_sub, map_add, hsc, hsc,
          show ρM (ρM x.val) = 0 from LinearMap.congr_fun ρM_comp_ρM x.val, smul_zero, add_zero]
      abel
    rw [heq]; exact FactorsThroughProj_sub hρs_fac hρsyz
  have hc0 : ((pB.comp g) (eVec 0)).vec 0 = 0 := by
    by_contra hc
    rw [zmod2_eq_one_of_ne_zero hc, one_smul] at hρ_c
    exact not_factors_ρM ((FactorsThroughProj_iff_twist ρM).mp hρ_c)
  have hd := endM_decomp (pB.comp g)
  rw [hc0, zero_smul, zero_add] at hd
  exact hd

lemma qForm_ModB_zero (f : ModB →ₗ[Λ] ModM) (g : ModM →ₗ[Λ] ModB) :
    qForm ModB f g = 0 := by
  have hp := pB_comp_hom_ModM_decomp g
  let b : ZMod 2 := ((pB.comp g) (eVec 0)).vec 1 + ((pB.comp g) (eVec 4)).vec 5
  let d : ZMod 2 := ((pB.comp g) (eVec 4)).vec 5
  obtain ⟨k, hk⟩ := (FactorsThroughProj_to_ModM (d • pM)).mp (FactorsThroughProj_smul d FactorsThroughProj_pM)
  let g1 : ModM →ₗ[Λ] ModB := g - vB.comp k
  have hqg : qForm ModB f g = qForm ModB f g1 :=
    qForm_eq_of_sub_factors f g g1 (by
      have hsub : g - g1 = vB.comp k := by simp [g1]
      rw [hsub]
      exact FactorsThroughProj_comp_right ⟨P02Obj, k, f.comp vB, rfl⟩ ρM)
  rw [hqg]
  have hp1 : pB.comp g1 = b • ρM := by
    apply LinearMap.ext; intro m
    change pB (g m - vB (k m)) = b • ρM m
    rw [map_sub, show pB (vB (k m)) = πM (k m) from LinearMap.congr_fun pB_comp_vB (k m),
        show πM (k m) = d • pM m from (LinearMap.congr_fun hk m).symm,
        show pB (g m) = b • ρM m + d • pM m from LinearMap.congr_fun hp m]
    abel
  have hkerB : pB.comp (g1.comp πM - b • (vB.comp liftρM)) = 0 := by
    apply LinearMap.ext; intro p
    have hsc : ∀ (c : ZMod 2) (x : ModB), pB (c • x) = c • pB x := fun c x => by
      have := map_smul pB (algebraMap (ZMod 2) Λ c) x
      simp only [algebraMap_smul] at this; exact this
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply, map_sub, hsc,
      LinearMap.zero_apply]
    rw [show pB (g1 (πM p)) = b • ρM (πM p) from LinearMap.congr_fun hp1 (πM p),
        show pB (vB (liftρM p)) = πM (liftρM p) from LinearMap.congr_fun pB_comp_vB _,
        show πM (liftρM p) = ρM (πM p) from LinearMap.congr_fun πM_comp_liftρM p, sub_self]
  obtain ⟨a, ha⟩ := lift_of_ker_eq_range uB_inj ker_pB_eq_range_uB hkerB
  have haκ : a.comp κM = b • (f0.comp (Twist.map (ρM + pM))) := by
    apply LinearMap.ext; intro x; apply uB_inj
    have h1 := LinearMap.congr_fun ha (κM x)
    have hsc : ∀ (c : ZMod 2) (z : ModA), uB (c • z) = c • uB z := fun c z => by
      have := map_smul uB (algebraMap (ZMod 2) Λ c) z
      simp only [algebraMap_smul] at this; exact this
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply] at h1 ⊢
    rw [show πM (κM x) = 0 from LinearMap.congr_fun πM_comp_κM x, map_zero, zero_sub,
        neg_eq_self_Λ, show liftρM (κM x) = κM (Twist.map (ρM + pM) x) from LinearMap.congr_fun liftρM_comp_κM x,
        show vB (κM (Twist.map (ρM + pM) x)) = uB (f0 (Twist.map (ρM + pM) x)) from (LinearMap.congr_fun uB_comp_f0 _).symm] at h1
    rw [h1, hsc]
  have hqa_κ : (qA.comp a).comp κM = 0 := by
    rw [LinearMap.comp_assoc, haκ]
    apply LinearMap.ext; intro x
    have hsc : ∀ (c : ZMod 2) (z : ModA), qA (c • z) = c • qA z := fun c z => by
      have := map_smul qA (algebraMap (ZMod 2) Λ c) z
      simp only [algebraMap_smul] at this; exact this
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, hsc, LinearMap.zero_apply]
    rw [show qA (f0 (Twist.map (ρM + pM) x)) = Twist.map ρM (Twist.map (ρM + pM) x) from LinearMap.congr_fun qA_comp_f0 _]
    have h0 : Twist.map ρM (Twist.map (ρM + pM) x) = 0 := by
      apply Twist.ext; change ρM (ρM x.val + pM x.val) = 0
      rw [map_add, show ρM (ρM x.val) = 0 from LinearMap.congr_fun ρM_comp_ρM x.val,
          show ρM (pM x.val) = 0 from LinearMap.congr_fun ρM_comp_pM x.val, add_zero]
    rw [h0, smul_zero]
  obtain ⟨r, hr⟩ := desc_of_ker_eq_range πM_surj ker_πM_eq_range_κM hqa_κ
  have hqa_alift : qA.comp (a.comp liftρM) = 0 := by
    rw [← LinearMap.comp_assoc, ← hr, LinearMap.comp_assoc, πM_comp_liftρM, ← LinearMap.comp_assoc,
        hom_ModM_Twist_comp_ρM r, LinearMap.zero_comp]
  obtain ⟨m, hm⟩ := lift_of_ker_eq_range iA_inj ker_qA_eq_range_iA hqa_alift
  have hmκ : m.comp κM = 0 := by
    apply LinearMap.ext; intro x; apply iA_inj
    change iA (m (κM x)) = iA 0
    rw [map_zero]
    rw [show iA (m (κM x)) = a (liftρM (κM x)) from LinearMap.congr_fun hm (κM x),
        show liftρM (κM x) = κM (Twist.map (ρM + pM) x) from LinearMap.congr_fun liftρM_comp_κM x,
        show a (κM (Twist.map (ρM + pM) x)) = b • f0 (Twist.map (ρM + pM) (Twist.map (ρM + pM) x)) from LinearMap.congr_fun haκ _]
    have hsq : Twist.map (ρM + pM) (Twist.map (ρM + pM) x) = 0 := by
      apply Twist.ext
      change (ρM + pM) (ρM x.val + pM x.val) = 0
      simp only [LinearMap.add_apply, map_add,
        show ρM (ρM x.val) = 0 from LinearMap.congr_fun ρM_comp_ρM x.val,
        show ρM (pM x.val) = 0 from LinearMap.congr_fun ρM_comp_pM x.val,
        show pM (ρM x.val) = 0 from LinearMap.congr_fun pM_comp_ρM x.val,
        show pM (pM x.val) = 0 from LinearMap.congr_fun pM_comp_pM x.val, add_zero]
    rw [hsq, map_zero, smul_zero]
  obtain ⟨m0, hm0⟩ := desc_of_ker_eq_range πM_surj ker_πM_eq_range_κM hmκ
  have hm0_0 : (m0 (eVec 0)).vec 0 = 0 := by
    have hgen : πM (LProj.gen 0, 0) = eVec 0 := by
      apply ModM.ext; funext i; fin_cases i <;> decide
    have hlift_gen : liftρM (LProj.gen 0, 0) = basisVec (mkB 2 0 0 rfl) • ((0, LProj.gen 2) : P02) := by
      refine Prod.ext (by change (0 : LProj 0) = basisVec (mkB 2 0 0 rfl) • 0; rw [smul_zero]) (LProj.ext ?_)
      change idempΛ 0 * basisVec (mkB 2 0 0 rfl) = basisVec (mkB 2 0 0 rfl) * idempΛ 2
      rw [idempΛ, idempΛ, basisVec_mul_basisVec, basisVec_mul_basisVec]
      have h1 : mulB (idempB 0) (mkB 2 0 0 rfl) = some (mkB 2 0 0 rfl) := by decide
      have h2 : mulB (mkB 2 0 0 rfl) (idempB 2) = some (mkB 2 0 0 rfl) := by decide
      rw [h1, h2]
    have hia : iA (m0 (eVec 0)) = basisVec (mkB 2 0 0 rfl) • a (0, LProj.gen 2) := by
      rw [← hgen, show m0 (πM (LProj.gen 0, 0)) = m (LProj.gen 0, 0) from LinearMap.congr_fun hm0 _,
          show iA (m (LProj.gen 0, 0)) = a (liftρM (LProj.gen 0, 0)) from LinearMap.congr_fun hm _,
          hlift_gen, map_smul]
    obtain ⟨⟨x, y⟩, hxy⟩ := mkA_surj (a (0, LProj.gen 2))
    rw [← hxy, ← map_smul] at hia
    have hsub : (m0 (eVec 0) - basisVec (mkB 2 0 0 rfl) • x, -(basisVec (mkB 2 0 0 rfl) • y)) ∈ subA := by
      rw [← mkA_eq_zero]
      have heq : ((m0 (eVec 0) - basisVec (mkB 2 0 0 rfl) • x, -(basisVec (mkB 2 0 0 rfl) • y)) : ModM × P42) =
          (m0 (eVec 0), 0) - (basisVec (mkB 2 0 0 rfl) • x, basisVec (mkB 2 0 0 rfl) • y) :=
        Prod.ext rfl (zero_sub _).symm
      rw [heq, map_sub]
      exact sub_eq_zero.mpr hia
    rcases hsub with ⟨z, hz⟩
    have hz1 : m0 (eVec 0) - basisVec (mkB 2 0 0 rfl) • x = ρM z := (congrArg Prod.fst hz).symm
    have hvec := congrArg (fun v : ModM => v.vec 0) hz1
    simp only [vec_sub, basisVec_200_smul_vec_zero, sub_zero] at hvec
    have hρ0 : (ρM z).vec 0 = 0 := rfl
    exact hvec.trans hρ0
  have hg1_ρπ : g1.comp (ρM.comp πM) = (uB.comp (iA.comp m0)).comp πM := by
    apply LinearMap.ext; intro p
    have h1 := LinearMap.congr_fun ha (liftρM p)
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      show liftρM (liftρM p) = 0 from LinearMap.congr_fun liftρM_comp_liftρM p,
      map_zero, smul_zero, sub_zero,
      show πM (liftρM p) = ρM (πM p) from LinearMap.congr_fun πM_comp_liftρM p] at h1
    change g1 (ρM (πM p)) = uB (iA (m0 (πM p)))
    rw [← h1, show m0 (πM p) = m p from LinearMap.congr_fun hm0 p,
        show iA (m p) = a (liftρM p) from LinearMap.congr_fun hm p]
  have hfu_iA : (f.comp uB).comp iA =
      ((((f.comp uB).comp iA) (eVec 0)).vec 1 + (((f.comp uB).comp iA) (eVec 4)).vec 5) • ρM +
      (((f.comp uB).comp iA) (eVec 4)).vec 5 • pM := by
    have hd := endM_decomp ((f.comp uB).comp iA)
    rw [hom_ModA_ModM_comp_iA_coeff0 (f.comp uB), zero_smul, zero_add] at hd
    exact hd
  change trPhiP02 (κMν.comp (f.comp (g1.comp (ρM.comp πM)))) = 0
  rw [hg1_ρπ]
  have hcomp : κMν.comp (f.comp ((uB.comp (iA.comp m0)).comp πM)) =
      ((((f.comp uB).comp iA) (eVec 0)).vec 1 + (((f.comp uB).comp iA) (eVec 4)).vec 5) •
        (κMν.comp (ρM.comp (m0.comp πM))) +
      (((f.comp uB).comp iA) (eVec 4)).vec 5 • (κMν.comp (pM.comp (m0.comp πM))) := by
    apply LinearMap.ext; intro p
    have hsc : ∀ (c : ZMod 2) (x : ModM), κMν (c • x) = c • κMν x := fun c x => by
      have := map_smul κMν (algebraMap (ZMod 2) Λ c) x
      simp only [algebraMap_smul] at this; exact this
    have h1 := LinearMap.congr_fun hfu_iA (m0 (πM p))
    simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply] at h1 ⊢
    rw [h1, map_add, hsc, hsc]
  rw [hcomp, trPhiP02_add]
  have hsm : ∀ (c : ZMod 2) (T : P02 →ₗ[Λ] P42), trPhiP02 (c • T) = c * trPhiP02 T := fun c T => by
    unfold trPhiP02
    have hφ : ∀ x : Λ, phiΛ (c • x) = c * phiΛ x := map_smul phiΛ c
    change phiΛ (c • _) + phiΛ (c • _) = c * (_ + _)
    rw [hφ, hφ, mul_add]
  rw [hsm, hsm]
  have htr1 : trPhiP02 (κMν.comp (ρM.comp (m0.comp πM))) = 0 := by
    have hq1 : qForm ModM LinearMap.id m0 = trPhiP02 (κMν.comp (ρM.comp (m0.comp πM))) :=
      qForm_eq_comm LinearMap.id m0
    rw [← hq1, qForm_eq_id_coeff LinearMap.id m0]
    exact hm0_0
  have htr2 : trPhiP02 (κMν.comp (pM.comp (m0.comp πM))) = 0 := by
    have heq : κMν.comp (pM.comp (m0.comp πM)) = κMν.comp ((pM.comp m0).comp πM) :=
      LinearMap.ext fun _ => rfl
    rw [heq]
    exact trPhiP02_factors_eq_zero (FactorsThroughProj_comp_right FactorsThroughProj_pM m0)
  rw [htr1, htr2, mul_zero, mul_zero, add_zero]

lemma deltaTotal_ModB : deltaTotal ModB = 0 :=
  deltaTotal_eq_zero_of_qForm_zero ModB qForm_ModB_zero qForm_TwistModB_zero

/- ### 5B. Canonical Resolution Triangles `resTri`, `relative_filler`, and 3-Octahedron Contradiction -/

/-- The canonical 3-term resolution triangle `P0(Twist N) → P1(Twist N) → P0(Twist N) → Twist P0(Twist N)`. -/
noncomputable abbrev resTri (N : Type) [AddCommGroup N] [Module Λ N]
    [Module (ZMod 2) N] [IsScalarTower (ZMod 2) Λ N] [Fintype N] : Triangle ProjΛ :=
  Triangle.mk (X := P0Obj (Twist N)) (Y := P1Obj (Twist N)) (Z := P0Obj (Twist N))
    (resD2 (Twist N)) (resD1 (Twist N)) ((Twist.map (resJK N)).comp (resμ (Twist N)))

lemma resTri_isExact3 (N : Type) [AddCommGroup N] [Module Λ N]
    [Module (ZMod 2) N] [IsScalarTower (ZMod 2) Λ N] [Fintype N] :
    IsExact3 (resTri N) := by
  refine ⟨ker_resD1_eq_range_resD2, ?_, ?_⟩
  · change LinearMap.ker ((Twist.map (resJK N)).comp (resμ (Twist N))) = LinearMap.range (resD1 (Twist N))
    rw [← ker_resμ_eq_range_resD1]
    ext f; simp only [LinearMap.mem_ker, LinearMap.comp_apply]
    constructor
    · intro hf; exact Twist.ext (resJK_inj ((congrArg Twist.val hf).trans (map_zero (resJK N)).symm))
    · intro hf; rw [hf, map_zero]
  · ext x; simp only [resTri, Triangle.mk_mor₁, Triangle.mk_mor₃, LinearMap.mem_ker, LinearMap.mem_range,
      LinearMap.comp_apply]
    constructor
    · intro hx
      have hx' : x.val ∈ LinearMap.ker (resD2 (Twist N)) := congrArg Twist.val hx
      rw [ker_resD2_eq_range_resJK (K := N)] at hx'
      obtain ⟨n, hn⟩ := hx'
      obtain ⟨p, hp⟩ := resμ_surj (N := Twist N) ⟨n⟩
      refine ⟨p, Twist.ext ?_⟩
      change resJK N (resμ (Twist N) p).val = x.val
      rw [hp]; exact hn
    · rintro ⟨p, rfl⟩
      apply Twist.ext
      exact LinearMap.congr_fun resD2_comp_resJK _

lemma resTri_distinguished_iff (N : Type) [AddCommGroup N] [Module Λ N]
    [Module (ZMod 2) N] [IsScalarTower (ZMod 2) Λ N] [Fintype N] :
    IsDistinguishedε (resTri N) ↔ FactorsThroughProj (deltaTotal N) := by
  have hEx := resTri_isExact3 N
  have hmem : ∀ n : N, resJK N n ∈ kerT (resTri N) := fun n => LinearMap.congr_fun resD2_comp_resJK n
  let toK : N →ₗ[Λ] kerT (resTri N) := (resJK N).codRestrict (kerT (resTri N)) hmem
  have htoK_bij : Function.Bijective toK := by
    refine ⟨fun a b hab => resJK_inj (congrArg Subtype.val hab), fun ⟨p, hp⟩ => ?_⟩
    have hp' : p ∈ LinearMap.range (resJK N) := (ker_resD2_eq_range_resJK (K := N)) ▸ hp
    obtain ⟨n, hn⟩ := hp'
    exact ⟨n, Subtype.ext hn⟩
  let eN : N ≃ₗ[Λ] kerT (resTri N) := LinearEquiv.ofBijective toK htoK_bij
  have hLift : HasLiftWith (resTri N) hEx LinearMap.id := by
    refine ⟨P0.map (Twist.map eN.symm.toLinearMap), P1.map (Twist.map eN.symm.toLinearMap),
      P0.map (Twist.map eN.symm.toLinearMap), ?_, ?_, ?_, ?_⟩
    · apply LinearMap.ext; intro p; apply Twist.ext; apply Subtype.ext
      change resJK N (resμ (Twist N) (P0.map (Twist.map eN.symm.toLinearMap) p)).val = (resμ (Twist (kerT (resTri N))) p).val.1
      have hnat := congrArg Twist.val (LinearMap.congr_fun (resμ_nat (Twist.map eN.symm.toLinearMap)) p)
      simp only [LinearMap.comp_apply] at hnat
      rw [← hnat]
      exact congrArg Subtype.val (eN.apply_symm_apply (resμ (Twist (kerT (resTri N))) p).val)
    · exact (resD1_nat (Twist.map eN.symm.toLinearMap)).symm
    · exact (resD2_nat (Twist.map eN.symm.toLinearMap)).symm
    · apply LinearMap.ext; intro k
      change k.1 = P0.map (Twist.map eN.symm.toLinearMap) (resJK (kerT (resTri N)) k)
      have hnat := LinearMap.congr_fun (resJK_nat eN.symm.toLinearMap) k
      simp only [LinearMap.comp_apply] at hnat
      rw [hnat]
      exact (congrArg Subtype.val (eN.apply_symm_apply k)).symm
  rw [isDistinguishedε_iff_of_lift (resTri N) hEx hLift]
  have hsub : (LinearMap.id - (LinearMap.id + deltaTotal (kerT (resTri N)))) = -(deltaTotal (kerT (resTri N))) := by
    abel
  rw [hsub]
  have hnat := deltaTotal_natural eN.toLinearMap
  constructor
  · intro hK
    have hK' := FactorsThroughProj_neg hK
    rw [neg_neg] at hK'
    have h1 := FactorsThroughProj_comp_left eN.symm.toLinearMap hnat
    have h2 := FactorsThroughProj_comp_left eN.symm.toLinearMap (FactorsThroughProj_comp_right hK' eN.toLinearMap)
    have heq : deltaTotal N =
        eN.symm.toLinearMap.comp (eN.toLinearMap.comp (deltaTotal N) - (deltaTotal (kerT (resTri N))).comp eN.toLinearMap) +
        eN.symm.toLinearMap.comp ((deltaTotal (kerT (resTri N))).comp eN.toLinearMap) := by
      apply LinearMap.ext; intro n
      simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply,
        LinearEquiv.coe_toLinearMap, map_sub, LinearEquiv.symm_apply_apply]
      abel
    rw [heq]; exact FactorsThroughProj_add h1 h2
  · intro hN
    apply FactorsThroughProj_neg
    have h1 := FactorsThroughProj_comp_right hnat eN.symm.toLinearMap
    have h2 := FactorsThroughProj_comp_left eN.toLinearMap (FactorsThroughProj_comp_right hN eN.symm.toLinearMap)
    have heq : deltaTotal (kerT (resTri N)) =
        eN.toLinearMap.comp ((deltaTotal N).comp eN.symm.toLinearMap) -
        (eN.toLinearMap.comp (deltaTotal N) - (deltaTotal (kerT (resTri N))).comp eN.toLinearMap).comp eN.symm.toLinearMap := by
      apply LinearMap.ext; intro k
      simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
        LinearEquiv.apply_symm_apply]
      abel
    rw [heq]; exact FactorsThroughProj_sub h2 h1

lemma resTri_ModA_distinguished : resTri ModA ∈ distTriang ProjΛ := by
  change IsDistinguishedε (resTri ModA)
  rw [resTri_distinguished_iff, deltaTotal_ModA]
  exact FactorsThroughProj_zero

lemma resTri_ModB_distinguished : resTri ModB ∈ distTriang ProjΛ := by
  change IsDistinguishedε (resTri ModB)
  rw [resTri_distinguished_iff, deltaTotal_ModB]
  exact FactorsThroughProj_zero

lemma resTri_ModM_not_distinguished : resTri ModM ∉ distTriang ProjΛ := by
  intro h
  have hd : FactorsThroughProj (deltaTotal ModM) := (resTri_distinguished_iff ModM).mp h
  have hρ : FactorsThroughProj ρM := by
    have heq : ρM = deltaTotal ModM - (deltaTotal ModM - ρM) := by abel
    rw [heq]; exact FactorsThroughProj_sub hd deltaTotal_ModM
  exact not_factors_ρM hρ

/-- Exactness of `P0.map` and `P1.map` on short exact sequences. -/
lemma P0_map_inj {A B : Type*}
    [AddCommGroup A] [Module Λ A] [Module (ZMod 2) A] [IsScalarTower (ZMod 2) Λ A]
    [AddCommGroup B] [Module Λ B] [Module (ZMod 2) B] [IsScalarTower (ZMod 2) Λ B]
    {u : A →ₗ[Λ] B} (hu : Function.Injective u) : Function.Injective (P0.map u) :=
  fun _ _ h => P0.ext (funext fun w => hu (congrFun (congrArg P0.fn h) w))

lemma P0_map_surj {B C : Type*}
    [AddCommGroup B] [Module Λ B] [Module (ZMod 2) B] [IsScalarTower (ZMod 2) Λ B]
    [AddCommGroup C] [Module Λ C] [Module (ZMod 2) C] [IsScalarTower (ZMod 2) Λ C]
    {p : B →ₗ[Λ] C} (hp : Function.Surjective p) : Function.Surjective (P0.map p) := by
  intro g
  choose sec hsec using hp
  refine ⟨⟨fun w => idempΛ w.val.1 • sec (g.fn w), fun w => by
    rw [← mul_smul, idempΛ, basisVec_mul_basisVec, mulB_idemp_self]⟩, P0.ext (funext fun w => ?_)⟩
  change p (idempΛ w.val.1 • sec (g.fn w)) = g.fn w
  rw [map_smul, hsec, g.compat]

lemma P0_map_exact {A B C : Type*}
    [AddCommGroup A] [Module Λ A] [Module (ZMod 2) A] [IsScalarTower (ZMod 2) Λ A]
    [AddCommGroup B] [Module Λ B] [Module (ZMod 2) B] [IsScalarTower (ZMod 2) Λ B]
    [AddCommGroup C] [Module Λ C] [Module (ZMod 2) C] [IsScalarTower (ZMod 2) Λ C]
    {u : A →ₗ[Λ] B} {p : B →ₗ[Λ] C} (hu : Function.Injective u)
    (hex : LinearMap.ker p = LinearMap.range u) :
    LinearMap.ker (P0.map p) = LinearMap.range (P0.map u) := by
  ext f; simp only [LinearMap.mem_ker, LinearMap.mem_range]
  constructor
  · intro hf
    have hmem : ∀ w : OMA.MO31809.B, ∃ a : A, u a = f.fn w := fun w => by
      have hw : f.fn w ∈ LinearMap.ker p := congrFun (congrArg P0.fn hf) w
      rw [hex] at hw; exact hw
    choose a ha using hmem
    refine ⟨⟨a, fun w => hu (by rw [map_smul, ha, f.compat])⟩, P0.ext (funext ha)⟩
  · rintro ⟨g, rfl⟩
    apply P0.ext; funext w
    have hmem : u (g.fn w) ∈ LinearMap.range u := LinearMap.mem_range_self u (g.fn w)
    rw [← hex] at hmem; exact hmem

lemma P1_map_inj {A B : Type*}
    [AddCommGroup A] [Module Λ A] [Module (ZMod 2) A] [IsScalarTower (ZMod 2) Λ A]
    [AddCommGroup B] [Module Λ B] [Module (ZMod 2) B] [IsScalarTower (ZMod 2) Λ B]
    {u : A →ₗ[Λ] B} (hu : Function.Injective u) : Function.Injective (P1.map u) :=
  fun _ _ h => P1.ext (funext fun q => hu (congrFun (congrArg P1.fn h) q))

lemma P1_map_surj {B C : Type*}
    [AddCommGroup B] [Module Λ B] [Module (ZMod 2) B] [IsScalarTower (ZMod 2) Λ B]
    [AddCommGroup C] [Module Λ C] [Module (ZMod 2) C] [IsScalarTower (ZMod 2) Λ C]
    {p : B →ₗ[Λ] C} (hp : Function.Surjective p) : Function.Surjective (P1.map p) := by
  intro g
  choose sec hsec using hp
  refine ⟨⟨fun q => idempΛ (arrowSrc q.val.1) • sec (g.fn q), fun q => by
    rw [← mul_smul, idempΛ, basisVec_mul_basisVec, mulB_idemp_self]⟩, P1.ext (funext fun q => ?_)⟩
  change p (idempΛ (arrowSrc q.val.1) • sec (g.fn q)) = g.fn q
  rw [map_smul, hsec, g.compat]

lemma P1_map_exact {A B C : Type*}
    [AddCommGroup A] [Module Λ A] [Module (ZMod 2) A] [IsScalarTower (ZMod 2) Λ A]
    [AddCommGroup B] [Module Λ B] [Module (ZMod 2) B] [IsScalarTower (ZMod 2) Λ B]
    [AddCommGroup C] [Module Λ C] [Module (ZMod 2) C] [IsScalarTower (ZMod 2) Λ C]
    {u : A →ₗ[Λ] B} {p : B →ₗ[Λ] C} (hu : Function.Injective u)
    (hex : LinearMap.ker p = LinearMap.range u) :
    LinearMap.ker (P1.map p) = LinearMap.range (P1.map u) := by
  ext f; simp only [LinearMap.mem_ker, LinearMap.mem_range]
  constructor
  · intro hf
    have hmem : ∀ q : B1, ∃ a : A, u a = f.fn q := fun q => by
      have hq : f.fn q ∈ LinearMap.ker p := congrFun (congrArg P1.fn hf) q
      rw [hex] at hq; exact hq
    choose a ha using hmem
    refine ⟨⟨a, fun q => hu (by rw [map_smul, ha, f.compat])⟩, P1.ext (funext ha)⟩
  · rintro ⟨g, rfl⟩
    apply P1.ext; funext q
    have hmem : u (g.fn q) ∈ LinearMap.range u := LinearMap.mem_range_self u (g.fn q)
    rw [← hex] at hmem; exact hmem

/-- Any short exact sequence `0 → X -f→ Y -g→ Z → 0` in `ProjΛ` gives a distinguished triangle `(f, g, 0)`. -/
lemma split_exact_distinguished {X Y Z : ProjΛ} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : Function.Injective (ProjΛ.toLin f))
    (hg : Function.Surjective (ProjΛ.toLin g))
    (hex : LinearMap.ker (ProjΛ.toLin g) = LinearMap.range (ProjΛ.toLin f)) :
    Triangle.mk f g (0 : Z ⟶ X⟦(1 : ℤ)⟧) ∈ distTriang ProjΛ := by
  change IsDistinguishedε (Triangle.mk f g 0)
  have hT : IsExact3 (Triangle.mk f g 0) := by
    refine ⟨hex, ?_, ?_⟩
    · ext z; simp only [Triangle.mk_mor₃, LinearMap.mem_ker, LinearMap.mem_range]
      exact ⟨fun _ => hg z, fun _ => rfl⟩
    · ext x; simp only [Triangle.mk_mor₁, Triangle.mk_mor₃, LinearMap.mem_ker, LinearMap.mem_range]
      constructor
      · intro hx; exact ⟨0, (Twist.ext (hf ((congrArg Twist.val hx).trans (map_zero _).symm))).symm⟩
      · rintro ⟨_, rfl⟩; exact map_zero _
  obtain ⟨α, hL⟩ := exists_genLift (Triangle.mk f g 0) hT LinearMap.id
  rw [isDistinguishedε_iff_of_lift _ hT hL]
  have hsub : Subsingleton (kerT (Triangle.mk f g 0)) :=
    ⟨fun a b => Subtype.ext (hf (a.2.trans b.2.symm))⟩
  have hzero : α - (LinearMap.id + deltaTotal (kerT (Triangle.mk f g 0))) = 0 :=
    LinearMap.ext fun _ => Subsingleton.elim _ _
  rw [hzero]; exact FactorsThroughProj_zero

/-- Helper module `ModSA` for CLLZ Lemma 3.11: `0 → ModA -eA→ P42 × P02 -πSA→ ModSA → 0`
and `0 → Twist ModM -ιSA→ ModSA -qSA→ ModM → 0`. -/
noncomputable def e1A : ModA →ₗ[Λ] P42 :=
  (ProjΛ.injective P42Obj iA iA_inj κMν).choose

lemma he1A : e1A.comp iA = κMν :=
  (ProjΛ.injective P42Obj iA iA_inj κMν).choose_spec

noncomputable def eA : ModA →ₗ[Λ] P42 × P02 := e1A.prod (κM.comp qA)

lemma heA_inj : Function.Injective eA := by
  intro a1 a2 h
  have h2' : κM (qA a1) = κM (qA a2) := congrArg Prod.snd h
  have hq : qA (a1 - a2) = 0 := by rw [map_sub, κM_inj h2', sub_self]
  have hmem : a1 - a2 ∈ LinearMap.range iA := ker_qA_eq_range_iA ▸ hq
  obtain ⟨m, hm⟩ := hmem
  have h1' : e1A (a1 - a2) = 0 := by rw [map_sub]; exact sub_eq_zero.mpr (congrArg Prod.fst h)
  rw [← hm, show e1A (iA m) = κMν m from LinearMap.congr_fun he1A m] at h1'
  have hm0 : m = 0 := κMν_inj (h1'.trans (map_zero κMν).symm)
  rw [hm0, map_zero] at hm
  exact sub_eq_zero.mp hm.symm

noncomputable def subSA : Submodule Λ (P42 × P02) := LinearMap.range eA

def ModSA : Type := (P42 × P02) ⧸ subSA

noncomputable instance : AddCommGroup ModSA := Submodule.Quotient.addCommGroup subSA
noncomputable instance : Module Λ ModSA := Submodule.Quotient.module subSA
noncomputable instance : Module (ZMod 2) ModSA := Submodule.Quotient.module' subSA
noncomputable instance : IsScalarTower (ZMod 2) Λ ModSA :=
  ⟨fun c a x => by
    obtain ⟨p, rfl⟩ := Submodule.mkQ_surjective subSA x
    change subSA.mkQ ((c • a) • p) = subSA.mkQ (c • (a • p))
    rw [smul_assoc]⟩
noncomputable instance : Fintype ModSA := instFintypeQuotient subSA

noncomputable def πSA : P42 × P02 →ₗ[Λ] ModSA := subSA.mkQ

lemma hπSA_surj : Function.Surjective πSA := Submodule.mkQ_surjective subSA

lemma hker_πSA : LinearMap.ker πSA = LinearMap.range eA := Submodule.ker_mkQ subSA

lemma hπSA_eA : πSA.comp eA = 0 := by
  apply LinearMap.ext; intro a; exact (Submodule.Quotient.mk_eq_zero subSA).mpr ⟨a, rfl⟩

lemma hinl_SA_ker : (πSA.comp (LinearMap.inl Λ P42 P02)).comp κMν = 0 := by
  apply LinearMap.ext; intro m
  change πSA (κMν m, 0) = 0
  have heq : (κMν m, (0 : P02)) = eA (iA m) :=
    Prod.ext (LinearMap.congr_fun he1A m).symm (by
      change 0 = κM (qA (iA m)); rw [show qA (iA m) = 0 from LinearMap.congr_fun qA_comp_iA m, map_zero])
  rw [heq]; exact LinearMap.congr_fun hπSA_eA (iA m)

noncomputable def ιSA : Twist ModM →ₗ[Λ] ModSA :=
  (desc_of_ker_eq_range πMν_surj ker_πMν_eq_range_κMν hinl_SA_ker).choose

lemma hιSA : ιSA.comp πMν = πSA.comp (LinearMap.inl Λ P42 P02) :=
  (desc_of_ker_eq_range πMν_surj ker_πMν_eq_range_κMν hinl_SA_ker).choose_spec

lemma hιSA_inj : Function.Injective ιSA := by
  intro x1 x2 h
  obtain ⟨p1, rfl⟩ := πMν_surj x1
  obtain ⟨p2, rfl⟩ := πMν_surj x2
  have h0 : πSA (p1 - p2, 0) = 0 := by
    have h1' : πSA (p1, 0) = πSA (p2, 0) :=
      (show ιSA (πMν p1) = πSA (p1, 0) from LinearMap.congr_fun hιSA p1).symm.trans
        (h.trans (show ιSA (πMν p2) = πSA (p2, 0) from LinearMap.congr_fun hιSA p2))
    have heq : (p1 - p2, (0 : P02)) = (p1, 0) - (p2, 0) := Prod.ext rfl (sub_self _).symm
    rw [heq, map_sub, h1', sub_self]
  have hmem : (p1 - p2, (0 : P02)) ∈ LinearMap.range eA := hker_πSA ▸ h0
  obtain ⟨a, ha⟩ := hmem
  have hqa : qA a = 0 := κM_inj ((congrArg Prod.snd ha).trans (map_zero κM).symm)
  obtain ⟨m, hm⟩ := (ker_qA_eq_range_iA ▸ hqa : a ∈ LinearMap.range iA)
  have hp : p1 - p2 = κMν m := by
    have hfst : e1A a = p1 - p2 := congrArg Prod.fst ha
    rw [← hfst, ← hm]; exact LinearMap.congr_fun he1A m
  have hπ : πMν (p1 - p2) = 0 := by rw [hp]; exact LinearMap.congr_fun πMν_comp_κMν m
  rw [map_sub] at hπ; exact sub_eq_zero.mp hπ

lemma hsnd_SA_ker : (πM.comp (LinearMap.snd Λ P42 P02)).comp eA = 0 := by
  apply LinearMap.ext; intro a; exact LinearMap.congr_fun πM_comp_κM (qA a)

noncomputable def qSA : ModSA →ₗ[Λ] ModM :=
  (desc_of_ker_eq_range hπSA_surj hker_πSA hsnd_SA_ker).choose

lemma hqSA : qSA.comp πSA = πM.comp (LinearMap.snd Λ P42 P02) :=
  (desc_of_ker_eq_range hπSA_surj hker_πSA hsnd_SA_ker).choose_spec

lemma hqSA_surj : Function.Surjective qSA := fun m => by
  obtain ⟨p, rfl⟩ := πM_surj m
  exact ⟨πSA (0, p), LinearMap.congr_fun hqSA (0, p)⟩

lemma hker_qSA : LinearMap.ker qSA = LinearMap.range ιSA := by
  ext z; simp only [LinearMap.mem_ker, LinearMap.mem_range]
  obtain ⟨⟨p1, p2⟩, rfl⟩ := hπSA_surj z
  constructor
  · intro hz
    have hp2 : πM p2 = 0 := (show qSA (πSA (p1, p2)) = πM p2 from LinearMap.congr_fun hqSA (p1, p2)).symm.trans hz
    obtain ⟨x, hx⟩ := (ker_πM_eq_range_κM ▸ hp2 : p2 ∈ LinearMap.range κM)
    obtain ⟨a, ha⟩ := qA_surj x
    refine ⟨πMν (p1 - e1A a), ?_⟩
    rw [show ιSA (πMν (p1 - e1A a)) = πSA (p1 - e1A a, 0) from LinearMap.congr_fun hιSA (p1 - e1A a)]
    rw [← sub_eq_zero, ← map_sub]
    have hmem : (p1 - e1A a, (0 : P02)) - (p1, p2) = eA (-a) := by
      refine Prod.ext ?_ ?_
      · change (p1 - e1A a) - p1 = e1A (-a); rw [map_neg]; abel
      · change 0 - p2 = κM (qA (-a))
        rw [map_neg, map_neg, ha, hx, zero_sub]
    rw [hmem]; exact LinearMap.congr_fun hπSA_eA (-a)
  · rintro ⟨x, hx⟩
    obtain ⟨p, rfl⟩ := πMν_surj x
    rw [← hx, show ιSA (πMν p) = πSA (p, 0) from LinearMap.congr_fun hιSA p]
    rw [show qSA (πSA (p, 0)) = πM 0 from LinearMap.congr_fun hqSA (p, 0)]; exact map_zero πM

lemma exists_cosyz_f0 : ∃ (Lf0 : P02 →ₗ[Λ] P42 × P02) (η : ModM →ₗ[Λ] ModSA),
    Lf0.comp κM = eA.comp f0 ∧ η.comp πM = πSA.comp Lf0 :=
  cosyzygy_exists (P1 := P02Obj) (P2 := ProjΛ.prod P42Obj P02Obj) κM_inj πM_surj ker_πM_eq_range_κM hπSA_eA f0

noncomputable def Lf0_SA : P02 →ₗ[Λ] P42 × P02 := exists_cosyz_f0.choose
noncomputable def ηSA : ModM →ₗ[Λ] ModSA := exists_cosyz_f0.choose_spec.choose

lemma hLf0_SA : Lf0_SA.comp κM = eA.comp f0 := exists_cosyz_f0.choose_spec.choose_spec.1
lemma hηSA : ηSA.comp πM = πSA.comp Lf0_SA := exists_cosyz_f0.choose_spec.choose_spec.2

noncomputable def φB_SA : ModB →ₗ[Λ] P42 × P02 :=
  subB.liftQ (eA.coprod Lf0_SA) (by
    rintro _ ⟨x, rfl⟩
    simp only [LinearMap.mem_ker, LinearMap.coprod_apply, LinearMap.prod_apply, Function.prod_apply]
    change eA (f0 x) + Lf0_SA (κM x) = 0
    rw [show Lf0_SA (κM x) = eA (f0 x) from LinearMap.congr_fun hLf0_SA x, add_self_Λ])

lemma hφB_uB_SA : φB_SA.comp uB = eA := by
  apply LinearMap.ext; intro a; change eA a + Lf0_SA 0 = eA a; rw [map_zero, add_zero]

lemma hπSA_φB_SA : πSA.comp φB_SA = ηSA.comp pB := by
  apply LinearMap.ext; intro b
  obtain ⟨⟨a, p⟩, rfl⟩ := mkModB_surj b
  change πSA (eA a + Lf0_SA p) = ηSA (0 + πM p)
  rw [map_add, zero_add, show πSA (eA a) = 0 from LinearMap.congr_fun hπSA_eA a, zero_add]
  exact (LinearMap.congr_fun hηSA p).symm

lemma hqSA_ηSA : FactorsThroughProj (qSA.comp ηSA - ρM) := by
  let L1 : P02 →ₗ[Λ] P02 := (LinearMap.snd Λ P42 P02).comp Lf0_SA
  have hL1_κ : L1.comp κM = κM.comp (Twist.map ρM) := by
    apply LinearMap.ext; intro x
    have h1 := congrArg Prod.snd (LinearMap.congr_fun hLf0_SA x)
    simp only [LinearMap.comp_apply] at h1
    change (Lf0_SA (κM x)).2 = κM (Twist.map ρM x)
    rw [h1]; exact congrArg κM (LinearMap.congr_fun qA_comp_f0 x)
  have hL1_π : (qSA.comp ηSA).comp πM = πM.comp L1 := by
    apply LinearMap.ext; intro p
    change qSA (ηSA (πM p)) = πM (Lf0_SA p).2
    rw [show ηSA (πM p) = πSA (Lf0_SA p) from LinearMap.congr_fun hηSA p]
    exact LinearMap.congr_fun hqSA (Lf0_SA p)
  have hL2_κ : liftρM.comp κM = κM.comp (Twist.map (ρM + pM)) := liftρM_comp_κM
  have hL2_π : ρM.comp πM = πM.comp liftρM := πM_comp_liftρM.symm
  have hdiff_κ : (L1 - liftρM).comp κM = κM.comp (Twist.map pM) := by
    rw [LinearMap.sub_comp, hL1_κ, hL2_κ]
    apply LinearMap.ext; intro x
    simp only [LinearMap.sub_apply, LinearMap.comp_apply]
    rw [← map_sub]; apply congrArg κM; apply Twist.ext
    change ρM x.val - (ρM x.val + pM x.val) = pM x.val
    rw [sub_add_cancel_left, neg_eq_self_Λ]
  have hdiff_π : (qSA.comp ηSA - ρM).comp πM = πM.comp (L1 - liftρM) := by
    rw [LinearMap.sub_comp, LinearMap.comp_sub, hL1_π, hL2_π]
  exact cosyzygy_of_factors (P1 := P02Obj) (P2 := P02Obj) κM_inj πM_surj ker_πM_eq_range_κM
    πM_comp_κM (FactorsThroughProj_twist FactorsThroughProj_pM) hdiff_κ hdiff_π

lemma hηSA_vanish (h : ModSA →ₗ[Λ] ModB) : FactorsThroughProj (h.comp ηSA) := by
  obtain ⟨P, k1, k2, hk12⟩ := hom_TwistModM_ModB_factors (h.comp ιSA)
  obtain ⟨k1', hk1'⟩ := ProjΛ.injective P ιSA hιSA_inj k1
  let hproj : ModSA →ₗ[Λ] ModB := k2.comp k1'
  have hsub_ker : (h - hproj).comp ιSA = 0 := by
    apply LinearMap.ext; intro x
    change h (ιSA x) - k2 (k1' (ιSA x)) = 0
    rw [show k1' (ιSA x) = k1 x from LinearMap.congr_fun hk1' x,
        show k2 (k1 x) = h (ιSA x) from (LinearMap.congr_fun hk12 x).symm, sub_self]
  obtain ⟨ℓ, hℓ⟩ := desc_of_ker_eq_range hqSA_surj hker_qSA hsub_ker
  have hℓρ : FactorsThroughProj (ℓ.comp ρM) :=
    (frobenius_nakayama_left (ℓ.comp ρM)).mpr fun f => by
      have heq : κMν.comp (f.comp ((ℓ.comp ρM).comp πM)) = κMν.comp (f.comp (ℓ.comp (ρM.comp πM))) :=
        LinearMap.ext fun _ => rfl
      rw [heq]; exact qForm_ModB_zero f ℓ
  have heq : h.comp ηSA = hproj.comp ηSA + ℓ.comp (qSA.comp ηSA - ρM) + ℓ.comp ρM := by
    apply LinearMap.ext; intro m
    have h1 := LinearMap.congr_fun hℓ (ηSA m)
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.add_apply, map_sub] at h1 ⊢
    rw [h1]; abel
  rw [heq]
  have hproj_fac : FactorsThroughProj (hproj.comp ηSA) :=
    ⟨P, k1'.comp ηSA, k2, LinearMap.ext fun _ => rfl⟩
  exact FactorsThroughProj_add
    (FactorsThroughProj_add hproj_fac (FactorsThroughProj_comp_left ℓ hqSA_ηSA))
    hℓρ

/-- CLLZ Lemma 3.11 (`relative_filler`): any third component `x : E_{A,2} ⟶ E_{B,2}` completing
`(x0, x1)` to a morphism `resTri ModA ⟶ resTri ModB` equals `x2 ≫ s` for a strict involution
automorphism `s` of `resTri ModB`! -/
lemma relative_filler (x : P0Obj (Twist ModA) ⟶ P0Obj (Twist ModB))
    (h1 : CategoryStruct.comp (resTri ModA).mor₂ x =
      CategoryStruct.comp (P1.map (Twist.map uB)) (resTri ModB).mor₂)
    (h2 : CategoryStruct.comp (resTri ModA).mor₃ ((P0.map (Twist.map uB))⟦(1 : ℤ)⟧') =
      CategoryStruct.comp x (resTri ModB).mor₃) :
    ∃ s : P0Obj (Twist ModB) ⟶ P0Obj (Twist ModB),
      CategoryStruct.comp s s = 𝟙 (P0Obj (Twist ModB)) ∧
      CategoryStruct.comp (resTri ModB).mor₂ s = (resTri ModB).mor₂ ∧
      CategoryStruct.comp s (resTri ModB).mor₃ = (resTri ModB).mor₃ ∧
      CategoryStruct.comp (P0.map (Twist.map uB)) s = x := by
  let v : P0 (Twist ModA) →ₗ[Λ] P0 (Twist ModB) := ProjΛ.toLin x - P0.map (Twist.map uB)
  have hv_d1 : v.comp (resD1 (Twist ModA)) = 0 := by
    apply LinearMap.ext; intro p
    have hx1 : ProjΛ.toLin x (resD1 (Twist ModA) p) = resD1 (Twist ModB) (P1.map (Twist.map uB) p) :=
      LinearMap.congr_fun h1 p
    have hnat : P0.map (Twist.map uB) (resD1 (Twist ModA) p) = resD1 (Twist ModB) (P1.map (Twist.map uB) p) :=
      LinearMap.congr_fun (resD1_nat (Twist.map uB)) p
    change ProjΛ.toLin x (resD1 (Twist ModA) p) - P0.map (Twist.map uB) (resD1 (Twist ModA) p) = 0
    rw [hx1, hnat, sub_self]
  obtain ⟨vbar, hvbar⟩ := desc_of_ker_eq_range resμ_surj ker_resμ_eq_range_resD1 hv_d1
  have hμ_vbar : (resμ (Twist ModB)).comp vbar = 0 := by
    apply LinearMap.ext; intro a
    obtain ⟨p, rfl⟩ := resμ_surj a
    apply Twist.ext; apply resJK_inj
    have hx2 : resJK ModB (resμ (Twist ModB) (ProjΛ.toLin x p)).val =
        P0.map (Twist.map uB) (resJK ModA (resμ (Twist ModA) p).val) :=
      (congrArg Twist.val (LinearMap.congr_fun h2 p)).symm
    have hnatμ : (resμ (Twist ModB) (P0.map (Twist.map uB) p)).val = uB (resμ (Twist ModA) p).val :=
      congrArg Twist.val (LinearMap.congr_fun (resμ_nat (Twist.map uB)) p).symm
    have hnatJ : P0.map (Twist.map uB) (resJK ModA (resμ (Twist ModA) p).val) =
        resJK ModB (uB (resμ (Twist ModA) p).val) :=
      LinearMap.congr_fun (resJK_nat uB) (resμ (Twist ModA) p).val
    change resJK ModB (resμ (Twist ModB) (vbar (resμ (Twist ModA) p))).val = resJK ModB (0 : ModB)
    rw [map_zero, show vbar (resμ (Twist ModA) p) = ProjΛ.toLin x p - P0.map (Twist.map uB) p from LinearMap.congr_fun hvbar p]
    rw [map_sub]
    change resJK ModB ((resμ (Twist ModB) (ProjΛ.toLin x p)).val -
      (resμ (Twist ModB) (P0.map (Twist.map uB) p)).val) = 0
    rw [map_sub, hx2, hnatμ, hnatJ, sub_self]
  have heAtw_inj : Function.Injective (Twist.map eA) := fun a1 a2 h =>
    Twist.ext (heA_inj (congrArg Twist.val h))
  obtain ⟨Lv, hLv⟩ := ProjΛ.injective (P0Obj (Twist ModB)) (Twist.map eA) heAtw_inj vbar
  have hμLv_ker : ((resμ (Twist ModB)).comp Lv).comp (Twist.map eA) = 0 := by
    rw [LinearMap.comp_assoc, hLv, hμ_vbar]
  have hπSAtw_surj : Function.Surjective (Twist.map πSA) := fun z => by
    obtain ⟨p, hp⟩ := hπSA_surj z.val; exact ⟨⟨p⟩, Twist.ext hp⟩
  have hker_πSAtw : LinearMap.ker (Twist.map πSA) = LinearMap.range (Twist.map eA) := by
    ext z; simp only [LinearMap.mem_ker, LinearMap.mem_range]
    constructor
    · intro hz
      have h1 : z.val ∈ LinearMap.range eA := hker_πSA ▸ congrArg Twist.val hz
      obtain ⟨a, ha⟩ := h1; exact ⟨⟨a⟩, Twist.ext ha⟩
    · rintro ⟨a, rfl⟩; apply Twist.ext; exact LinearMap.congr_fun hπSA_eA a.val
  obtain ⟨htw, hhtw⟩ := desc_of_ker_eq_range hπSAtw_surj hker_πSAtw hμLv_ker
  let h_un : ModSA →ₗ[Λ] ModB :=
    (Twist.involEquiv (N := ModB)).toLinearMap.comp
      ((Twist.map htw).comp (Twist.involEquiv (N := ModSA)).symm.toLinearMap)
  have hhtw_η_fac : FactorsThroughProj (htw.comp (Twist.map ηSA)) := by
    have hfac := FactorsThroughProj_twist (hηSA_vanish h_un)
    have heq : Twist.map (h_un.comp ηSA) = htw.comp (Twist.map ηSA) := by
      apply LinearMap.ext; intro x; rfl
    rwa [heq] at hfac
  obtain ⟨m0, hm0⟩ := (FactorsThroughProj_iff_exists_epi (P0Obj (Twist ModB))
    (resμ (Twist ModB)) resμ_surj _).mp hhtw_η_fac
  let n_raw : Twist ModB →ₗ[Λ] P0 (Twist ModB) := Lv.comp (Twist.map φB_SA) - m0.comp (Twist.map pB)
  have hμ_nraw : (resμ (Twist ModB)).comp n_raw = 0 := by
    apply LinearMap.ext; intro b
    change resμ (Twist ModB) (Lv (Twist.map φB_SA b) - m0 (Twist.map pB b)) = 0
    rw [map_sub, show resμ (Twist ModB) (Lv (Twist.map φB_SA b)) = htw (Twist.map πSA (Twist.map φB_SA b))
          from (LinearMap.congr_fun hhtw (Twist.map φB_SA b)).symm,
        show Twist.map πSA (Twist.map φB_SA b) = Twist.map ηSA (Twist.map pB b)
          from Twist.ext (LinearMap.congr_fun hπSA_φB_SA b.val),
        show resμ (Twist ModB) (m0 (Twist.map pB b)) = htw (Twist.map ηSA (Twist.map pB b))
          from (LinearMap.congr_fun hm0 (Twist.map pB b)).symm, sub_self]
  have hnraw_uB : n_raw.comp (Twist.map uB) = vbar := by
    apply LinearMap.ext; intro a
    change Lv (Twist.map φB_SA (Twist.map uB a)) - m0 (Twist.map pB (Twist.map uB a)) = vbar a
    have hp0 : Twist.map pB (Twist.map uB a) = 0 := Twist.ext (LinearMap.congr_fun pB_comp_uB a.val)
    have hφa : Twist.map φB_SA (Twist.map uB a) = Twist.map eA a := Twist.ext (LinearMap.congr_fun hφB_uB_SA a.val)
    rw [hp0, map_zero, sub_zero, hφa]
    exact LinearMap.congr_fun hLv a
  let n : P0Obj (Twist ModB) ⟶ P0Obj (Twist ModB) := n_raw.comp (resμ (Twist ModB))
  have hn_sq : CategoryStruct.comp n n = 0 := by
    apply ProjΛ.hom_ext; intro p
    change n_raw (resμ (Twist ModB) (n_raw (resμ (Twist ModB) p))) = 0
    rw [show resμ (Twist ModB) (n_raw (resμ (Twist ModB) p)) = 0 from LinearMap.congr_fun hμ_nraw _, map_zero]
  let s : P0Obj (Twist ModB) ⟶ P0Obj (Twist ModB) := 𝟙 (P0Obj (Twist ModB)) + n
  refine ⟨s, ?_, ?_, ?_, ?_⟩
  · apply ProjΛ.hom_ext; intro p
    change (p + n_raw (resμ (Twist ModB) p)) + n_raw (resμ (Twist ModB) (p + n_raw (resμ (Twist ModB) p))) = p
    rw [map_add, show resμ (Twist ModB) (n_raw (resμ (Twist ModB) p)) = 0 from LinearMap.congr_fun hμ_nraw _,
        add_zero, add_assoc, add_self_Λ, add_zero]
  · apply ProjΛ.hom_ext; intro p
    let p' : P1 (Twist ModB) := p
    change resD1 (Twist ModB) p' + n_raw (resμ (Twist ModB) (resD1 (Twist ModB) p')) = resD1 (Twist ModB) p'
    rw [resμ_comp_resD1 p', map_zero, add_zero]
  · apply ProjΛ.hom_ext; intro p; apply Twist.ext
    change resJK ModB (resμ (Twist ModB) (p + n_raw (resμ (Twist ModB) p))).val = resJK ModB (resμ (Twist ModB) p).val
    rw [map_add, show resμ (Twist ModB) (n_raw (resμ (Twist ModB) p)) = 0 from LinearMap.congr_fun hμ_nraw _,
        add_zero]
  · apply ProjΛ.hom_ext; intro p
    change P0.map (Twist.map uB) p + n_raw (resμ (Twist ModB) (P0.map (Twist.map uB) p)) = ProjΛ.toLin x p
    rw [show resμ (Twist ModB) (P0.map (Twist.map uB) p) = Twist.map uB (resμ (Twist ModA) p)
          from (LinearMap.congr_fun (resμ_nat (Twist.map uB)) p).symm,
        show n_raw (Twist.map uB (resμ (Twist ModA) p)) = vbar (resμ (Twist ModA) p)
          from LinearMap.congr_fun hnraw_uB _,
        show vbar (resμ (Twist ModA) p) = ProjΛ.toLin x p - P0.map (Twist.map uB) p
          from LinearMap.congr_fun hvbar p]
    abel

/-- Verdier's octahedral axiom (TR4) fails in the pretriangulated category `ProjΛ`! -/
lemma not_isTriangulated_ProjΛ : ¬ IsTriangulated ProjΛ := by
  intro hTri
  have huB_tw_inj : Function.Injective (Twist.map uB) := fun a1 a2 h => Twist.ext (uB_inj (congrArg Twist.val h))
  have hpB_tw_surj : Function.Surjective (Twist.map pB) := fun m => by
    obtain ⟨b, hb⟩ := pB_surj m.val; exact ⟨⟨b⟩, Twist.ext hb⟩
  have hker_pB_tw : LinearMap.ker (Twist.map pB) = LinearMap.range (Twist.map uB) := by
    ext b; simp only [LinearMap.mem_ker, LinearMap.mem_range]
    constructor
    · intro hb
      obtain ⟨a, ha⟩ := (ker_pB_eq_range_uB ▸ congrArg Twist.val hb : b.val ∈ LinearMap.range uB)
      exact ⟨⟨a⟩, Twist.ext ha⟩
    · rintro ⟨a, rfl⟩; apply Twist.ext; exact LinearMap.congr_fun pB_comp_uB a.val
  let x0 : P0Obj (Twist ModA) ⟶ P0Obj (Twist ModB) := P0.map (Twist.map uB)
  let q0 : P0Obj (Twist ModB) ⟶ P0Obj (Twist ModM) := P0.map (Twist.map pB)
  let x1 : P1Obj (Twist ModA) ⟶ P1Obj (Twist ModB) := P1.map (Twist.map uB)
  let q1 : P1Obj (Twist ModB) ⟶ P1Obj (Twist ModM) := P1.map (Twist.map pB)
  have hC0 : Triangle.mk x0 q0 0 ∈ distTriang ProjΛ :=
    split_exact_distinguished x0 q0 (P0_map_inj huB_tw_inj) (P0_map_surj hpB_tw_surj) (P0_map_exact huB_tw_inj hker_pB_tw)
  have hC1 : Triangle.mk x1 q1 0 ∈ distTriang ProjΛ :=
    split_exact_distinguished x1 q1 (P1_map_inj huB_tw_inj) (P1_map_surj hpB_tw_surj) (P1_map_exact huB_tw_inj hker_pB_tw)
  obtain ⟨fA, gA, hA, hfA, hgA, hhA, hTA⟩ :
      ∃ (fA : P0Obj (Twist ModA) ⟶ P1Obj (Twist ModA))
        (gA : P1Obj (Twist ModA) ⟶ P0Obj (Twist ModA))
        (hA : P0Obj (Twist ModA) ⟶ (P0Obj (Twist ModA))⟦(1 : ℤ)⟧),
        fA = (resTri ModA).mor₁ ∧ gA = (resTri ModA).mor₂ ∧ hA = (resTri ModA).mor₃ ∧
        Triangle.mk fA gA hA ∈ distTriang ProjΛ :=
    ⟨(resTri ModA).mor₁, (resTri ModA).mor₂, (resTri ModA).mor₃, rfl, rfl, rfl, resTri_ModA_distinguished⟩
  obtain ⟨fB, gB, hB, hfB, hgB, hhB, hTB⟩ :
      ∃ (fB : P0Obj (Twist ModB) ⟶ P1Obj (Twist ModB))
        (gB : P1Obj (Twist ModB) ⟶ P0Obj (Twist ModB))
        (hB : P0Obj (Twist ModB) ⟶ (P0Obj (Twist ModB))⟦(1 : ℤ)⟧),
        fB = (resTri ModB).mor₁ ∧ gB = (resTri ModB).mor₂ ∧ hB = (resTri ModB).mor₃ ∧
        Triangle.mk fB gB hB ∈ distTriang ProjΛ :=
    ⟨(resTri ModB).mor₁, (resTri ModB).mor₂, (resTri ModB).mor₃, rfl, rfl, rfl, resTri_ModB_distinguished⟩
  have hsq : CategoryStruct.comp fA x1 = CategoryStruct.comp x0 fB := by
    rw [hfA, hfB]; exact resD2_nat (Twist.map uB)
  obtain ⟨Z13, v13, w13, hDiag⟩ := distinguished_cocone_triangle (CategoryStruct.comp fA x1)
  have H1 := Triangulated.someOctahedron rfl hTA hC1 hDiag
  have H2 := Triangulated.someOctahedron hsq.symm hC0 hTB hDiag
  let x : P0Obj (Twist ModA) ⟶ P0Obj (Twist ModB) := CategoryStruct.comp H1.m₁ H2.m₃
  have hx1 : CategoryStruct.comp (resTri ModA).mor₂ x =
      CategoryStruct.comp x1 (resTri ModB).mor₂ := by
    rw [← hgA, ← hgB]
    apply ProjΛ.hom_ext; intro z
    change ProjΛ.toLin H2.m₃ (ProjΛ.toLin H1.m₁ (ProjΛ.toLin gA z)) = ProjΛ.toLin gB (ProjΛ.toLin x1 z)
    rw [show ProjΛ.toLin H1.m₁ (ProjΛ.toLin gA z) = ProjΛ.toLin v13 (ProjΛ.toLin x1 z)
          from LinearMap.congr_fun H1.comm₁ z,
        show ProjΛ.toLin H2.m₃ (ProjΛ.toLin v13 (ProjΛ.toLin x1 z)) = ProjΛ.toLin gB (ProjΛ.toLin x1 z)
          from LinearMap.congr_fun H2.comm₃ (ProjΛ.toLin x1 z)]
  have hx2 : CategoryStruct.comp (resTri ModA).mor₃ (x0⟦(1 : ℤ)⟧') =
      CategoryStruct.comp x (resTri ModB).mor₃ := by
    rw [← hhA, ← hhB]
    apply ProjΛ.hom_ext; intro z
    change ProjΛ.toLin (x0⟦(1 : ℤ)⟧') (ProjΛ.toLin hA z) =
      ProjΛ.toLin hB (ProjΛ.toLin H2.m₃ (ProjΛ.toLin H1.m₁ z))
    rw [show ProjΛ.toLin hB (ProjΛ.toLin H2.m₃ (ProjΛ.toLin H1.m₁ z)) =
          ProjΛ.toLin (x0⟦(1 : ℤ)⟧') (ProjΛ.toLin w13 (ProjΛ.toLin H1.m₁ z))
          from (LinearMap.congr_fun H2.comm₄ (ProjΛ.toLin H1.m₁ z)).symm,
        show ProjΛ.toLin w13 (ProjΛ.toLin H1.m₁ z) = ProjΛ.toLin hA z
          from LinearMap.congr_fun H1.comm₂ z]
  obtain ⟨s, hs_inv, hs_d1, hs_d2, hs_x⟩ := relative_filler x hx1 hx2
  have hs_gB : CategoryStruct.comp gB s = gB := by rw [hgB]; exact hs_d1
  have hs_hB : CategoryStruct.comp s hB = hB := by rw [hhB]; exact hs_d2
  let n3' : Z13 ⟶ P0Obj (Twist ModB) := CategoryStruct.comp H2.m₃ s
  have hm1_n3' : CategoryStruct.comp H1.m₁ n3' = x0 := by
    apply ProjΛ.hom_ext; intro z
    change ProjΛ.toLin s (ProjΛ.toLin x z) = ProjΛ.toLin x0 z
    rw [show ProjΛ.toLin x z = ProjΛ.toLin s (ProjΛ.toLin x0 z) from (LinearMap.congr_fun hs_x z).symm,
        show ProjΛ.toLin s (ProjΛ.toLin s (ProjΛ.toLin x0 z)) = ProjΛ.toLin x0 z
          from LinearMap.congr_fun hs_inv (ProjΛ.toLin x0 z)]
  have hv13_n3' : CategoryStruct.comp v13 n3' = gB := by
    apply ProjΛ.hom_ext; intro z
    change ProjΛ.toLin s (ProjΛ.toLin H2.m₃ (ProjΛ.toLin v13 z)) = ProjΛ.toLin gB z
    rw [show ProjΛ.toLin H2.m₃ (ProjΛ.toLin v13 z) = ProjΛ.toLin gB z from LinearMap.congr_fun H2.comm₃ z,
        show ProjΛ.toLin s (ProjΛ.toLin gB z) = ProjΛ.toLin gB z from LinearMap.congr_fun hs_gB z]
  have hn3'_d2 : CategoryStruct.comp n3' hB = CategoryStruct.comp w13 (x0⟦(1 : ℤ)⟧') := by
    apply ProjΛ.hom_ext; intro z
    change ProjΛ.toLin hB (ProjΛ.toLin s (ProjΛ.toLin H2.m₃ z)) = ProjΛ.toLin (x0⟦(1 : ℤ)⟧') (ProjΛ.toLin w13 z)
    rw [show ProjΛ.toLin hB (ProjΛ.toLin s (ProjΛ.toLin H2.m₃ z)) = ProjΛ.toLin hB (ProjΛ.toLin H2.m₃ z)
          from LinearMap.congr_fun hs_hB (ProjΛ.toLin H2.m₃ z),
        show ProjΛ.toLin hB (ProjΛ.toLin H2.m₃ z) = ProjΛ.toLin (x0⟦(1 : ℤ)⟧') (ProjΛ.toLin w13 z)
          from (LinearMap.congr_fun H2.comm₄ z).symm]
  let sIso : P0Obj (Twist ModB) ≅ P0Obj (Twist ModB) := ⟨s, s, hs_inv, hs_inv⟩
  have h2' : Triangle.mk H2.m₁ n3' (CategoryStruct.comp hB (q0⟦(1 : ℤ)⟧')) ∈ distTriang ProjΛ := by
    refine isomorphic_distinguished _ H2.mem _ (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) sIso ?_ ?_ ?_)
    · exact ProjΛ.hom_ext fun _ => rfl
    · apply ProjΛ.hom_ext; intro z
      exact LinearMap.congr_fun hs_inv (ProjΛ.toLin H2.m₃ z)
    · apply ProjΛ.hom_ext; intro z
      change ProjΛ.toLin (q0⟦(1 : ℤ)⟧') (ProjΛ.toLin hB z) =
        ProjΛ.toLin (q0⟦(1 : ℤ)⟧') (ProjΛ.toLin hB (ProjΛ.toLin s z))
      rw [show ProjΛ.toLin hB (ProjΛ.toLin s z) = ProjΛ.toLin hB z from LinearMap.congr_fun hs_hB z]
  have h2'_rot : Triangle.mk n3' (CategoryStruct.comp hB (q0⟦(1 : ℤ)⟧'))
      (-(H2.m₁⟦(1 : ℤ)⟧')) ∈ distTriang ProjΛ :=
    rot_of_distTriang _ h2'
  have H3 := Triangulated.someOctahedron hm1_n3' H1.mem h2'_rot hC0
  have hq0_surj : Function.Surjective (ProjΛ.toLin q0) := P0_map_surj hpB_tw_surj
  have hq1_surj : Function.Surjective (ProjΛ.toLin q1) := P1_map_surj hpB_tw_surj
  have hH3_m1 : H3.m₁ = (resTri ModM).mor₂ := by
    apply ProjΛ.hom_ext; intro z
    obtain ⟨y, rfl⟩ := hq1_surj z
    have hL : ProjΛ.toLin H3.m₁ (ProjΛ.toLin q1 y) = ProjΛ.toLin q0 (ProjΛ.toLin gB y) := by
      have h1 : ProjΛ.toLin H1.m₃ (ProjΛ.toLin v13 y) = ProjΛ.toLin q1 y := LinearMap.congr_fun H1.comm₃ y
      have h2 : ProjΛ.toLin H3.m₁ (ProjΛ.toLin H1.m₃ (ProjΛ.toLin v13 y)) =
          ProjΛ.toLin q0 (ProjΛ.toLin n3' (ProjΛ.toLin v13 y)) := LinearMap.congr_fun H3.comm₁ (ProjΛ.toLin v13 y)
      have h3 : ProjΛ.toLin n3' (ProjΛ.toLin v13 y) = ProjΛ.toLin gB y := LinearMap.congr_fun hv13_n3' y
      rw [← h1, h2, h3]
    have hR : ProjΛ.toLin (resTri ModM).mor₂ (ProjΛ.toLin q1 y) = ProjΛ.toLin q0 (ProjΛ.toLin gB y) := by
      rw [hgB]; exact (LinearMap.congr_fun (resD1_nat (Twist.map pB)) y).symm
    exact hL.trans hR.symm
  have hH3_m3 : H3.m₃ = (resTri ModM).mor₃ := by
    apply ProjΛ.hom_ext; intro z
    obtain ⟨y, rfl⟩ := hq0_surj z
    have hL : ProjΛ.toLin H3.m₃ (ProjΛ.toLin q0 y) = ProjΛ.toLin (q0⟦(1 : ℤ)⟧') (ProjΛ.toLin hB y) :=
      LinearMap.congr_fun H3.comm₃ y
    have hR : ProjΛ.toLin (resTri ModM).mor₃ (ProjΛ.toLin q0 y) = ProjΛ.toLin (q0⟦(1 : ℤ)⟧') (ProjΛ.toLin hB y) := by
      rw [hhB]; apply Twist.ext
      change resJK ModM (resμ (Twist ModM) (P0.map (Twist.map pB) y)).val =
        P0.map (Twist.map pB) (resJK ModB (resμ (Twist ModB) y).val)
      rw [show (resμ (Twist ModM) (P0.map (Twist.map pB) y)).val = pB (resμ (Twist ModB) y).val
            from congrArg Twist.val (LinearMap.congr_fun (resμ_nat (Twist.map pB)) y).symm,
          show P0.map (Twist.map pB) (resJK ModB (resμ (Twist ModB) y).val) =
            resJK ModM (pB (resμ (Twist ModB) y).val)
            from LinearMap.congr_fun (resJK_nat pB) _]
    exact hL.trans hR.symm
  have hH3_w : CategoryStruct.comp (-(H2.m₁⟦(1 : ℤ)⟧')) (H1.m₃⟦(1 : ℤ)⟧') = -((resTri ModM).mor₁⟦(1 : ℤ)⟧') := by
    rw [neg_hom_eq_self, neg_hom_eq_self]
    apply ProjΛ.hom_ext; intro z; apply Twist.ext
    obtain ⟨y, hy⟩ := hq0_surj z.val
    have hL : ProjΛ.toLin H1.m₃ (ProjΛ.toLin H2.m₁ (ProjΛ.toLin q0 y)) = ProjΛ.toLin q1 (ProjΛ.toLin fB y) := by
      rw [show ProjΛ.toLin H2.m₁ (ProjΛ.toLin q0 y) = ProjΛ.toLin v13 (ProjΛ.toLin fB y)
            from LinearMap.congr_fun H2.comm₁ y,
          show ProjΛ.toLin H1.m₃ (ProjΛ.toLin v13 (ProjΛ.toLin fB y)) = ProjΛ.toLin q1 (ProjΛ.toLin fB y)
            from LinearMap.congr_fun H1.comm₃ (ProjΛ.toLin fB y)]
    have hR : ProjΛ.toLin (resTri ModM).mor₁ (ProjΛ.toLin q0 y) = ProjΛ.toLin q1 (ProjΛ.toLin fB y) := by
      rw [hfB]; exact (LinearMap.congr_fun (resD2_nat (Twist.map pB)) y).symm
    change ProjΛ.toLin H1.m₃ (ProjΛ.toLin H2.m₁ z.val) = ProjΛ.toLin (resTri ModM).mor₁ z.val
    rw [← hy]; exact hL.trans hR.symm
  have hRotM : (resTri ModM).rotate ∈ distTriang ProjΛ := by
    have hmem := H3.mem
    rw [hH3_m1, hH3_m3, hH3_w] at hmem
    exact hmem
  exact resTri_ModM_not_distinguished ((rotate_distinguished_triangle (resTri ModM)).mpr hRotM)

/- ### 5C. Universe-Polymorphic Small Model `ULiftProj.{u_1, u_2}` and Final Theorem `OMA.solution` -/

/-- Carrier wrapper for `Fin n` with no pre-existing algebraic instances, avoiding `Fin.instAdd` clashes. -/
structure SmallCarrier (n : ℕ) : Type where
  idx : Fin n

instance (n : ℕ) : Fintype (SmallCarrier n) :=
  Fintype.ofEquiv (Fin n) ⟨SmallCarrier.mk, SmallCarrier.idx, fun _ => rfl, fun _ => rfl⟩

/-- Small (`Type 0`) model of `ProjΛ`: finite projective `Λ`-modules carried on `SmallCarrier n`. -/
structure SmallProj : Type where
  n : ℕ
  addCommGroup : AddCommGroup (SmallCarrier n)
  moduleΛ : Module Λ (SmallCarrier n)
  moduleZ2 : Module (ZMod 2) (SmallCarrier n)
  tower : @IsScalarTower (ZMod 2) Λ (SmallCarrier n) _ moduleΛ.toSMul moduleZ2.toSMul
  proj : @Module.Projective Λ _ (SmallCarrier n) addCommGroup.toAddCommMonoid moduleΛ

namespace SmallProj

def toProj (P : SmallProj) : ProjΛ :=
  @ProjΛ.mk (SmallCarrier P.n) P.addCommGroup P.moduleΛ P.moduleZ2 P.tower inferInstance P.proj

/-- Nakayama twist on `SmallProj`, keeping the exact same `SmallCarrier P.n` carrier! -/
def nuModΛ (P : SmallProj) : @Module Λ (SmallCarrier P.n) _ P.addCommGroup.toAddCommMonoid := by
  letI : AddCommGroup (SmallCarrier P.n) := P.addCommGroup
  letI : Module Λ (SmallCarrier P.n) := P.moduleΛ
  exact
    { smul := fun a x => nuΛ a • x
      one_smul := fun x => by change nuΛ 1 • x = x; rw [nuΛ.map_one, one_smul]
      mul_smul := fun a b x => by change nuΛ (a * b) • x = nuΛ a • (nuΛ b • x); rw [nuΛ.map_mul, mul_smul]
      smul_zero := fun a => by change nuΛ a • (0 : SmallCarrier P.n) = 0; exact smul_zero (nuΛ a)
      smul_add := fun a x y => by change nuΛ a • (x + y) = nuΛ a • x + nuΛ a • y; exact smul_add (nuΛ a) x y
      add_smul := fun a b x => by change nuΛ (a + b) • x = nuΛ a • x + nuΛ b • x; rw [nuΛ.map_add, add_smul]
      zero_smul := fun x => by change nuΛ 0 • x = 0; rw [nuΛ.map_zero, zero_smul] }

def nuObj (P : SmallProj) : SmallProj where
  n := P.n
  addCommGroup := P.addCommGroup
  moduleΛ := nuModΛ P
  moduleZ2 := P.moduleZ2
  tower := by
    letI : AddCommGroup (SmallCarrier P.n) := P.addCommGroup
    letI : Module (ZMod 2) (SmallCarrier P.n) := P.moduleZ2
    have htw := P.tower
    exact @IsScalarTower.mk (ZMod 2) Λ (SmallCarrier P.n) _ (nuModΛ P).toSMul P.moduleZ2.toSMul
      (fun c a x => by
        have hnu : nuΛ (c • a) = c • nuΛ a := by apply Λ.ext; funext w; simp [nuΛ]
        have h1 := @IsScalarTower.smul_assoc (ZMod 2) Λ (SmallCarrier P.n) _ P.moduleΛ.toSMul P.moduleZ2.toSMul htw c (nuΛ a) x
        change @HSMul.hSMul Λ (SmallCarrier P.n) (SmallCarrier P.n) (@instHSMul _ _ P.moduleΛ.toSMul) (nuΛ (c • a)) x =
          c • (@HSMul.hSMul Λ (SmallCarrier P.n) (SmallCarrier P.n) (@instHSMul _ _ P.moduleΛ.toSMul) (nuΛ a) x)
        rw [hnu]; exact h1)
  proj := by
    letI : AddCommGroup (SmallCarrier P.n) := P.addCommGroup
    letI : Module Λ (SmallCarrier P.n) := nuModΛ P
    have hlift : ∀ {X Y : Type _} [AddCommGroup X] [Module Λ X] [AddCommGroup Y] [Module Λ Y]
        (f : X →ₗ[Λ] Y) (g : SmallCarrier P.n →ₗ[Λ] Y), Function.Surjective f →
        ∃ h : SmallCarrier P.n →ₗ[Λ] X, f.comp h = g := by
      intro X Y _ _ _ _ f g hf
      have hinv : ∀ a : Λ, nuΛ (nuΛ a) = a := fun a => by apply Λ.ext; funext w; simp [nuΛ, nuB_invol]
      let f' : Twist X →ₗ[Λ] Twist Y := Twist.map f
      let g' : P.toProj.carrier →ₗ[Λ] Twist Y :=
        { toFun := fun x => ⟨g x⟩
          map_add' := fun x y => Twist.ext (map_add g x y)
          map_smul' := fun a x => Twist.ext (by
            have h1 := g.map_smul (nuΛ a) x
            have h2 : @HSMul.hSMul Λ (SmallCarrier P.n) (SmallCarrier P.n) (@instHSMul _ _ (nuModΛ P).toSMul) (nuΛ a) x =
                @HSMul.hSMul Λ (SmallCarrier P.n) (SmallCarrier P.n) (@instHSMul _ _ P.moduleΛ.toSMul) a x := by
              change @HSMul.hSMul Λ (SmallCarrier P.n) (SmallCarrier P.n) (@instHSMul _ _ P.moduleΛ.toSMul) (nuΛ (nuΛ a)) x = _
              rw [hinv]
            rw [h2] at h1
            exact h1) }
      have hf' : Function.Surjective f' := fun y =>
        let ⟨x, hx⟩ := hf y.val
        ⟨⟨x⟩, Twist.ext hx⟩
      obtain ⟨h', hh'⟩ := Module.projective_lifting_property f' g' hf'
      let h : SmallCarrier P.n →ₗ[Λ] X :=
        { toFun := fun x => (h' x).val
          map_add' := fun x y => congrArg Twist.val (map_add h' x y)
          map_smul' := fun a x => by
            have h1 := congrArg Twist.val (h'.map_smul (nuΛ a) x)
            exact h1.trans (by change nuΛ (nuΛ a) • (h' x).val = a • (h' x).val; rw [hinv]) }
      refine ⟨h, LinearMap.ext fun x => ?_⟩
      exact congrArg Twist.val (LinearMap.congr_fun hh' x)
    exact Module.Projective.of_lifting_property hlift

/-- Every `P : ProjΛ` is isomorphic to a `SmallProj` carried on `SmallCarrier (Fintype.card P.carrier)`. -/
noncomputable def ofProjWithIso (P : ProjΛ) : Σ S : SmallProj, S.toProj ≅ P := by
  let e : P.carrier ≃ SmallCarrier (Fintype.card P.carrier) :=
    (Fintype.equivFin P.carrier).trans ⟨SmallCarrier.mk, SmallCarrier.idx, fun _ => rfl, fun _ => rfl⟩
  letI addG : AddCommGroup (SmallCarrier (Fintype.card P.carrier)) :=
    { add := fun x y => e (e.symm x + e.symm y)
      zero := e 0
      neg := fun x => e (-e.symm x)
      sub := fun x y => e (e.symm x - e.symm y)
      nsmul := fun k x => e (k • e.symm x)
      zsmul := fun k x => e (k • e.symm x)
      add_assoc := fun a b c => by
        change e (e.symm (e (e.symm a + e.symm b)) + e.symm c) = e (e.symm a + e.symm (e (e.symm b + e.symm c)))
        simp [add_assoc]
      zero_add := fun a => by change e (e.symm (e 0) + e.symm a) = a; simp
      add_zero := fun a => by change e (e.symm a + e.symm (e 0)) = a; simp
      nsmul_zero := fun x => by change e ((0 : ℕ) • e.symm x) = e 0; simp
      nsmul_succ := fun n x => by
        change e ((n + 1) • e.symm x) = e (e.symm (e (n • e.symm x)) + e.symm x)
        simp [add_nsmul]
      zsmul_zero' := fun x => by change e ((0 : ℤ) • e.symm x) = e 0; simp
      zsmul_succ' := fun n x => by
        change e (((n.succ : ℕ) : ℤ) • e.symm x) = e (e.symm (e ((n : ℤ) • e.symm x)) + e.symm x)
        simp [Nat.cast_succ, add_zsmul, one_zsmul]
      zsmul_neg' := fun n x => by
        change e ((Int.negSucc n) • e.symm x) = e (-e.symm (e (((n.succ : ℕ) : ℤ) • e.symm x)))
        simp only [Equiv.symm_apply_apply, negSucc_zsmul, natCast_zsmul]
      neg_add_cancel := fun a => by change e (e.symm (e (-e.symm a)) + e.symm a) = e 0; simp
      add_comm := fun a b => by change e (e.symm a + e.symm b) = e (e.symm b + e.symm a); rw [add_comm]
      sub_eq_add_neg := fun a b => by
        change e (e.symm a - e.symm b) = e (e.symm a + e.symm (e (-e.symm b)))
        simp [sub_eq_add_neg] }
  letI modΛ : Module Λ (SmallCarrier (Fintype.card P.carrier)) :=
    { smul := fun a x => e (a • e.symm x)
      one_smul := fun x => by change e ((1 : Λ) • e.symm x) = x; simp
      mul_smul := fun a b x => by change e ((a * b) • e.symm x) = e (a • e.symm (e (b • e.symm x))); simp [mul_smul]
      smul_zero := fun a => by change e (a • e.symm (e 0)) = e 0; simp
      smul_add := fun a x y => by
        change e (a • e.symm (e (e.symm x + e.symm y))) = e (e.symm (e (a • e.symm x)) + e.symm (e (a • e.symm y)))
        simp [smul_add]
      add_smul := fun a b x => by
        change e ((a + b) • e.symm x) = e (e.symm (e (a • e.symm x)) + e.symm (e (b • e.symm x)))
        simp [add_smul]
      zero_smul := fun x => by change e ((0 : Λ) • e.symm x) = e 0; simp }
  letI modZ2 : Module (ZMod 2) (SmallCarrier (Fintype.card P.carrier)) :=
    { smul := fun c x => e (c • e.symm x)
      one_smul := fun x => by change e ((1 : ZMod 2) • e.symm x) = x; simp
      mul_smul := fun a b x => by change e ((a * b) • e.symm x) = e (a • e.symm (e (b • e.symm x))); simp [mul_smul]
      smul_zero := fun a => by change e (a • e.symm (e 0)) = e 0; simp
      smul_add := fun a x y => by
        change e (a • e.symm (e (e.symm x + e.symm y))) = e (e.symm (e (a • e.symm x)) + e.symm (e (a • e.symm y)))
        simp [smul_add]
      add_smul := fun a b x => by
        change e ((a + b) • e.symm x) = e (e.symm (e (a • e.symm x)) + e.symm (e (b • e.symm x)))
        simp [add_smul]
      zero_smul := fun x => by change e ((0 : ZMod 2) • e.symm x) = e 0; simp }
  letI tow : IsScalarTower (ZMod 2) Λ (SmallCarrier (Fintype.card P.carrier)) :=
    ⟨fun c a x => by change e ((c • a) • e.symm x) = e (c • e.symm (e (a • e.symm x))); simp [smul_assoc]⟩
  let toF : P.carrier →ₗ[Λ] SmallCarrier (Fintype.card P.carrier) :=
    { toFun := e
      map_add' := fun x y => by change e (x + y) = e (e.symm (e x) + e.symm (e y)); simp
      map_smul' := fun a x => by change e (a • x) = e (a • e.symm (e x)); simp }
  let fromF : SmallCarrier (Fintype.card P.carrier) →ₗ[Λ] P.carrier :=
    { toFun := e.symm
      map_add' := fun x y => by change e.symm (e (e.symm x + e.symm y)) = e.symm x + e.symm y; simp
      map_smul' := fun a x => by change e.symm (e (a • e.symm x)) = a • e.symm x; simp }
  have hproj : Module.Projective Λ (SmallCarrier (Fintype.card P.carrier)) :=
    Module.Projective.of_split fromF toF (LinearMap.ext fun x => e.apply_symm_apply x)
  let S : SmallProj := ⟨Fintype.card P.carrier, addG, modΛ, modZ2, tow, hproj⟩
  let iso : S.toProj ≅ P :=
    ⟨fromF, toF, ProjΛ.hom_ext fun x => e.apply_symm_apply x, ProjΛ.hom_ext fun x => e.symm_apply_apply x⟩
  exact ⟨S, iso⟩

noncomputable def ofProj (P : ProjΛ) : SmallProj := (ofProjWithIso P).1

noncomputable def isoProj (P : ProjΛ) : (ofProj P).toProj ≅ P := (ofProjWithIso P).2

/-- Iso `(nuObj P).toProj ≅ P.toProj⟦1⟧` in `ProjΛ`. -/
def nuToProjIso (P : SmallProj) : (nuObj P).toProj ≅ P.toProj⟦(1 : ℤ)⟧ where
  hom :=
    { toFun := Twist.mk
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  inv :=
    { toFun := Twist.val
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  hom_inv_id := ProjΛ.hom_ext fun _ => rfl
  inv_hom_id := ProjΛ.hom_ext fun _ => rfl

end SmallProj

universe u_obj u_hom

/-- Universe-lifted small category `ULiftProj.{u_1}` with `Hom` in `Type u_2`, equivalent to `ProjΛ`! -/
structure ULiftProj : Type u_obj where
  down : SmallProj

namespace ULiftProj

instance instCategory : Category.{u_hom, u_obj} ULiftProj.{u_obj} where
  Hom P Q := ULift.{u_hom} (P.down.toProj ⟶ Q.down.toProj)
  id P := ULift.up (𝟙 P.down.toProj)
  comp f g := ULift.up (CategoryStruct.comp f.down g.down)
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

instance : Preadditive ULiftProj.{u_obj} where
  homGroup P Q :=
    { add := fun f g => ULift.up (f.down + g.down)
      zero := ULift.up (0 : P.down.toProj ⟶ Q.down.toProj)
      neg := fun f => ULift.up (-f.down)
      sub := fun f g => ULift.up (f.down - g.down)
      nsmul := fun k f => ULift.up (k • f.down)
      zsmul := fun k f => ULift.up (k • f.down)
      add_assoc := fun a b c => congrArg ULift.up (add_assoc a.down b.down c.down)
      zero_add := fun a => congrArg ULift.up (zero_add a.down)
      add_zero := fun a => congrArg ULift.up (add_zero a.down)
      nsmul_zero := fun a => congrArg ULift.up (zero_nsmul a.down)
      nsmul_succ := fun n a => by
        change ULift.up ((n + 1) • a.down) = ULift.up (n • a.down + a.down)
        rw [add_nsmul, one_nsmul]
      zsmul_zero' := fun a => congrArg ULift.up (zero_zsmul a.down)
      zsmul_succ' := fun n a => by
        change ULift.up (((n.succ : ℕ) : ℤ) • a.down) = ULift.up ((n : ℤ) • a.down + a.down)
        rw [Nat.cast_succ, add_zsmul, one_zsmul]
      zsmul_neg' := fun n a => by
        change ULift.up ((Int.negSucc n) • a.down) = ULift.up (-(((n.succ : ℕ) : ℤ) • a.down))
        rw [negSucc_zsmul, natCast_zsmul]
      neg_add_cancel := fun a => congrArg ULift.up (neg_add_cancel a.down)
      add_comm := fun a b => congrArg ULift.up (add_comm a.down b.down)
      sub_eq_add_neg := fun a b => congrArg ULift.up (sub_eq_add_neg a.down b.down) }
  add_comp _ _ _ f f' g := congrArg ULift.up (Preadditive.add_comp _ _ _ f.down f'.down g.down)
  comp_add _ _ _ f g g' := congrArg ULift.up (Preadditive.comp_add _ _ _ f.down g.down g'.down)

noncomputable def zeroObj : ULiftProj.{u_obj} := ⟨SmallProj.ofProj ProjΛ.zeroObj⟩

lemma subsingleton_zeroObj : Subsingleton zeroObj.{u_obj}.down.toProj.carrier := by
  let e := SmallProj.isoProj ProjΛ.zeroObj
  haveI : Subsingleton ProjΛ.zeroObj.carrier := ⟨fun x y => by cases x; cases y; rfl⟩
  refine ⟨fun x y => ?_⟩
  have h1 : ProjΛ.toLin e.hom x = ProjΛ.toLin e.hom y := Subsingleton.elim _ _
  have h2 := congrArg (ProjΛ.toLin e.inv) h1
  have hx : ProjΛ.toLin e.inv (ProjΛ.toLin e.hom x) = x := LinearMap.congr_fun e.hom_inv_id x
  have hy : ProjΛ.toLin e.inv (ProjΛ.toLin e.hom y) = y := LinearMap.congr_fun e.hom_inv_id y
  exact hx.symm.trans (h2.trans hy)

instance : HasZeroObject ULiftProj.{u_obj} := by
  haveI : Subsingleton zeroObj.{u_obj}.down.toProj.carrier := subsingleton_zeroObj
  refine ⟨⟨zeroObj, ?_, ?_⟩⟩
  · intro Q
    exact ⟨⟨⟨ULift.up (0 : zeroObj.down.toProj ⟶ Q.down.toProj)⟩, fun f => congrArg ULift.up (ProjΛ.hom_ext fun x => by
      have hx : x = 0 := Subsingleton.elim x 0
      rw [hx, map_zero]; rfl)⟩⟩
  · intro Q
    exact ⟨⟨⟨ULift.up (0 : Q.down.toProj ⟶ zeroObj.down.toProj)⟩, fun f => congrArg ULift.up (ProjΛ.hom_ext fun _ => Subsingleton.elim _ _)⟩⟩

def nuFunctor : ULiftProj.{u_obj} ⥤ ULiftProj.{u_obj} where
  obj P := ⟨SmallProj.nuObj P.down⟩
  map {P Q} f := ULift.up
    { toFun := fun (x : P.down.toProj.carrier) => f.down.toFun x
      map_add' := fun (x y : P.down.toProj.carrier) => f.down.map_add' x y
      map_smul' := fun a (x : P.down.toProj.carrier) => f.down.map_smul' (nuΛ a) x }
  map_id _ := congrArg ULift.up (ProjΛ.hom_ext fun _ => rfl)
  map_comp _ _ := congrArg ULift.up (ProjΛ.hom_ext fun _ => rfl)

def nuNuIso : nuFunctor.{u_obj, u_hom} ⋙ nuFunctor.{u_obj, u_hom} ≅ 𝟭 ULiftProj.{u_obj} :=
  NatIso.ofComponents (fun P =>
    { hom := ULift.up
        { toFun := fun (x : P.down.toProj.carrier) => x
          map_add' := fun _ _ => rfl
          map_smul' := fun a (x : P.down.toProj.carrier) => by
            letI : AddCommGroup (SmallCarrier P.down.n) := P.down.addCommGroup
            letI : Module Λ (SmallCarrier P.down.n) := P.down.moduleΛ
            have hinv : nuΛ (nuΛ a) = a := by apply Λ.ext; funext w; simp [nuΛ, nuB_invol]
            change (nuΛ (nuΛ a)) • x = a • x
            rw [hinv] }
      inv := ULift.up
        { toFun := fun (x : P.down.toProj.carrier) => x
          map_add' := fun _ _ => rfl
          map_smul' := fun a (x : P.down.toProj.carrier) => by
            letI : AddCommGroup (SmallCarrier P.down.n) := P.down.addCommGroup
            letI : Module Λ (SmallCarrier P.down.n) := P.down.moduleΛ
            have hinv : nuΛ (nuΛ a) = a := by apply Λ.ext; funext w; simp [nuΛ, nuB_invol]
            change a • x = (nuΛ (nuΛ a)) • x
            rw [hinv] }
      hom_inv_id := congrArg ULift.up (ProjΛ.hom_ext fun _ => rfl)
      inv_hom_id := congrArg ULift.up (ProjΛ.hom_ext fun _ => rfl) })
    (fun _ => congrArg ULift.up (ProjΛ.hom_ext fun _ => rfl))

def shiftBool : Bool → (ULiftProj.{u_obj} ⥤ ULiftProj.{u_obj})
  | false => 𝟭 ULiftProj.{u_obj}
  | true => nuFunctor.{u_obj, u_hom}

def shiftAddBool : ∀ (a b : Bool), shiftBool.{u_obj, u_hom} (xor a b) ≅
    shiftBool.{u_obj, u_hom} a ⋙ shiftBool.{u_obj, u_hom} b
  | false, false => (Functor.leftUnitor (𝟭 ULiftProj.{u_obj})).symm
  | false, true => (Functor.leftUnitor nuFunctor.{u_obj, u_hom}).symm
  | true, false => (Functor.rightUnitor nuFunctor.{u_obj, u_hom}).symm
  | true, true => nuNuIso.{u_obj, u_hom}.symm

def shiftF (n : ℤ) : ULiftProj.{u_obj} ⥤ ULiftProj.{u_obj} := shiftBool (ProjΛ.isOddInt n)

def shiftAddIso (m n : ℤ) : shiftF.{u_obj, u_hom} (m + n) ≅
    shiftF.{u_obj, u_hom} m ⋙ shiftF.{u_obj, u_hom} n :=
  eqToIso (congrArg shiftBool (ProjΛ.isOddInt_add m n)) ≪≫
    shiftAddBool (ProjΛ.isOddInt m) (ProjΛ.isOddInt n)

private lemma shiftAddIso_assoc_aux (a b c ab bc abc1 abc2 : Bool)
    (hab : ab = xor a b) (hbc : bc = xor b c) (h1 : abc1 = xor ab c) (h2 : abc2 = xor a bc)
    (h12 : abc1 = abc2) (X : ULiftProj.{u_obj}) :
    CategoryStruct.comp
      ((eqToIso (congrArg shiftBool.{u_obj, u_hom} h1) ≪≫ shiftAddBool ab c).hom.app X)
      ((shiftBool c).map ((eqToIso (congrArg shiftBool.{u_obj, u_hom} hab) ≪≫ shiftAddBool a b).hom.app X)) =
    CategoryStruct.comp
      (eqToHom (congrArg (fun d => (shiftBool.{u_obj, u_hom} d).obj X) h12))
      (CategoryStruct.comp
        ((eqToIso (congrArg shiftBool.{u_obj, u_hom} h2) ≪≫ shiftAddBool a bc).hom.app X)
        ((eqToIso (congrArg shiftBool.{u_obj, u_hom} hbc) ≪≫ shiftAddBool b c).hom.app ((shiftBool a).obj X))) := by
  subst hab; subst hbc; subst h1; subst h2
  cases a <;> cases b <;> cases c <;> exact congrArg ULift.up (ProjΛ.hom_ext fun _ => rfl)

private lemma shiftAddIso_zero_add_aux (b0 b z : Bool) (hz : z = false)
    (hb : b0 = b) (h : b0 = xor z b) (X : ULiftProj.{u_obj}) :
    (eqToIso (congrArg shiftBool.{u_obj, u_hom} h) ≪≫ shiftAddBool z b).hom.app X =
      CategoryStruct.comp
        (eqToHom (congrArg (fun d => (shiftBool.{u_obj, u_hom} d).obj X) hb))
        ((shiftBool b).map ((eqToIso (congrArg shiftBool.{u_obj, u_hom} hz)).inv.app X)) := by
  subst hz; subst hb
  cases b0 <;> exact congrArg ULift.up (ProjΛ.hom_ext fun _ => rfl)

private lemma shiftAddIso_add_zero_aux (b0 b z : Bool) (hz : z = false)
    (hb : b0 = b) (h : b0 = xor b z) (X : ULiftProj.{u_obj}) :
    (eqToIso (congrArg shiftBool.{u_obj, u_hom} h) ≪≫ shiftAddBool b z).hom.app X =
      CategoryStruct.comp
        (eqToHom (congrArg (fun d => (shiftBool.{u_obj, u_hom} d).obj X) hb))
        ((eqToIso (congrArg shiftBool.{u_obj, u_hom} hz)).inv.app ((shiftBool b).obj X)) := by
  subst hz; subst hb
  cases b0 <;> exact congrArg ULift.up (ProjΛ.hom_ext fun _ => rfl)

def shiftMkCore : ShiftMkCore ULiftProj.{u_obj} ℤ where
  F := shiftF.{u_obj, u_hom}
  zero := eqToIso (congrArg shiftBool ProjΛ.isOddInt_zero)
  add := shiftAddIso
  assoc_hom_app m₁ m₂ m₃ X :=
    shiftAddIso_assoc_aux (ProjΛ.isOddInt m₁) (ProjΛ.isOddInt m₂) (ProjΛ.isOddInt m₃)
      (ProjΛ.isOddInt (m₁ + m₂)) (ProjΛ.isOddInt (m₂ + m₃))
      (ProjΛ.isOddInt (m₁ + m₂ + m₃)) (ProjΛ.isOddInt (m₁ + (m₂ + m₃)))
      (ProjΛ.isOddInt_add m₁ m₂) (ProjΛ.isOddInt_add m₂ m₃)
      (ProjΛ.isOddInt_add (m₁ + m₂) m₃) (ProjΛ.isOddInt_add m₁ (m₂ + m₃))
      (congrArg ProjΛ.isOddInt (add_assoc m₁ m₂ m₃)) X
  zero_add_hom_app n X :=
    shiftAddIso_zero_add_aux (ProjΛ.isOddInt (0 + n)) (ProjΛ.isOddInt n) (ProjΛ.isOddInt 0)
      ProjΛ.isOddInt_zero (congrArg ProjΛ.isOddInt (zero_add n)) (ProjΛ.isOddInt_add 0 n) X
  add_zero_hom_app n X :=
    shiftAddIso_add_zero_aux (ProjΛ.isOddInt (n + 0)) (ProjΛ.isOddInt n) (ProjΛ.isOddInt 0)
      ProjΛ.isOddInt_zero (congrArg ProjΛ.isOddInt (add_zero n)) (ProjΛ.isOddInt_add n 0) X

instance instHasShift : HasShift ULiftProj.{u_obj} ℤ := hasShiftMk ULiftProj.{u_obj} ℤ shiftMkCore.{u_obj, u_hom}

instance (n : ℤ) : (shiftFunctor ULiftProj.{u_obj} n).Additive where
  map_add {P Q} f g := by
    change (shiftBool (ProjΛ.isOddInt n)).map (f + g) =
      (shiftBool (ProjΛ.isOddInt n)).map f +
      (shiftBool (ProjΛ.isOddInt n)).map g
    cases ProjΛ.isOddInt n <;> exact congrArg ULift.up (ProjΛ.hom_ext fun _ => rfl)

/-- Iso `(X⟦1⟧).down.toProj ≅ X.down.toProj⟦1⟧` with exact syntactic domain matching `T.mor₃.down`. -/
def shift1ToProjIso (X : ULiftProj.{u_obj}) :
    ((@shiftFunctor ULiftProj.{u_obj} ℤ instCategory.{u_obj, u_hom} _ instHasShift.{u_obj, u_hom} 1).obj X).down.toProj ≅
      X.down.toProj⟦(1 : ℤ)⟧ :=
  SmallProj.nuToProjIso X.down

/-- Transport triangles from `ULiftProj` to `ProjΛ`. -/
def toProjTri (T : @Triangle ULiftProj.{u_obj} instCategory.{u_obj, u_hom} instHasShift.{u_obj, u_hom}) : Triangle ProjΛ :=
  Triangle.mk T.mor₁.down T.mor₂.down
    (CategoryStruct.comp T.mor₃.down (shift1ToProjIso.{u_obj, u_hom} T.obj₁).hom)

lemma shift1_nat {P Q : ULiftProj.{u_obj}} (f : @Quiver.Hom ULiftProj.{u_obj} instCategory.{u_obj, u_hom}.toQuiver P Q) :
    CategoryStruct.comp ((@shiftFunctor ULiftProj.{u_obj} ℤ instCategory.{u_obj, u_hom} _ instHasShift.{u_obj, u_hom} 1).map f).down
        (shift1ToProjIso.{u_obj, u_hom} Q).hom =
      CategoryStruct.comp (shift1ToProjIso.{u_obj, u_hom} P).hom (f.down⟦(1 : ℤ)⟧') :=
  ProjΛ.hom_ext fun _ => rfl

def toProjTri_iso {T1 T2 : @Triangle ULiftProj.{u_obj} instCategory.{u_obj, u_hom} instHasShift.{u_obj, u_hom}} (e : T2 ≅ T1) :
    toProjTri.{u_obj, u_hom} T2 ≅ toProjTri.{u_obj, u_hom} T1 := by
  let iso1 : T2.obj₁.down.toProj ≅ T1.obj₁.down.toProj :=
    ⟨e.hom.hom₁.down, e.inv.hom₁.down,
      congrArg ULift.down (congrArg TriangleMorphism.hom₁ e.hom_inv_id),
      congrArg ULift.down (congrArg TriangleMorphism.hom₁ e.inv_hom_id)⟩
  let iso2 : T2.obj₂.down.toProj ≅ T1.obj₂.down.toProj :=
    ⟨e.hom.hom₂.down, e.inv.hom₂.down,
      congrArg ULift.down (congrArg TriangleMorphism.hom₂ e.hom_inv_id),
      congrArg ULift.down (congrArg TriangleMorphism.hom₂ e.inv_hom_id)⟩
  let iso3 : T2.obj₃.down.toProj ≅ T1.obj₃.down.toProj :=
    ⟨e.hom.hom₃.down, e.inv.hom₃.down,
      congrArg ULift.down (congrArg TriangleMorphism.hom₃ e.hom_inv_id),
      congrArg ULift.down (congrArg TriangleMorphism.hom₃ e.inv_hom_id)⟩
  refine Triangle.isoMk _ _ iso1 iso2 iso3 ?_ ?_ ?_
  · exact congrArg ULift.down e.hom.comm₁
  · exact congrArg ULift.down e.hom.comm₂
  · apply ProjΛ.hom_ext; intro x; apply Twist.ext
    exact LinearMap.congr_fun (congrArg ULift.down e.hom.comm₃) x

/-- Pretriangulated structure on `ULiftProj.{u_obj}` pulled back from `ProjΛ`! -/
instance instPretriangulatedULift : Pretriangulated ULiftProj.{u_obj} where
  distinguishedTriangles := { T | IsDistinguishedε (toProjTri.{u_obj, u_hom} T) }
  isomorphic_distinguished T1 h1 T2 e := isDistinguishedε_of_iso _ h1 _ (toProjTri_iso.{u_obj, u_hom} e)
  contractible_distinguished X := by
    let ZU : ULiftProj.{u_obj} := (contractibleTriangle X).obj₃
    let ZP : ProjΛ := (contractibleTriangle X.down.toProj).obj₃
    have hz_u : Limits.IsZero ZU := Limits.isZero_zero _
    haveI h0sub : Subsingleton ZU.down.toProj.carrier := by
      have hid0 : (𝟙 ZU) = 0 := hz_u.eq_of_src _ _
      refine ⟨fun x y => ?_⟩
      have hx : x = 0 := LinearMap.congr_fun (congrArg ULift.down hid0) x
      have hy : y = 0 := LinearMap.congr_fun (congrArg ULift.down hid0) y
      rw [hx, hy]
    haveI : Subsingleton ZP.carrier := subsingleton_of_isZero_proj ZP (Limits.isZero_zero ProjΛ)
    let iso0 : ZU.down.toProj ≅ ZP :=
      ⟨0, 0, ProjΛ.hom_ext fun _ => Subsingleton.elim _ _, ProjΛ.hom_ext fun _ => Subsingleton.elim _ _⟩
    refine isDistinguishedε_of_iso (contractibleTriangle X.down.toProj) (isDistinguishedε_contractible _) _
      (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) iso0 ?_ ?_ ?_)
    · exact ProjΛ.hom_ext fun _ => rfl
    · exact ProjΛ.hom_ext fun _ => Subsingleton.elim _ _
    · exact ProjΛ.hom_ext fun z => by
        haveI : Subsingleton (toProjTri.{u_obj, u_hom} (contractibleTriangle X)).obj₃.carrier := h0sub
        have hz0 : z = 0 := Subsingleton.elim z 0
        rw [hz0, map_zero, map_zero]
  distinguished_cocone_triangle {X Y} f := by
    obtain ⟨Z, g, h, hD⟩ := isDistinguishedε_cocone f.down
    let Zs : ULiftProj.{u_obj} := ⟨SmallProj.ofProj Z⟩
    let eZ : Zs.down.toProj ≅ Z := SmallProj.isoProj Z
    let gs : Y ⟶ Zs := ULift.up (CategoryStruct.comp g eZ.inv)
    let hs := ULift.up.{u_hom} (CategoryStruct.comp (CategoryStruct.comp eZ.hom h) (shift1ToProjIso.{u_obj, u_hom} X).inv)
    refine ⟨Zs, gs, hs, isDistinguishedε_of_iso (Triangle.mk f.down g h) hD _
      (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) eZ ?_ ?_ ?_)⟩
    · exact ProjΛ.hom_ext fun _ => rfl
    · apply ProjΛ.hom_ext; intro y
      exact LinearMap.congr_fun eZ.inv_hom_id (ProjΛ.toLin g y)
    · apply ProjΛ.hom_ext; intro z; rfl
  rotate_distinguished_triangle T := by
    have hIso : toProjTri.{u_obj, u_hom} T.rotate ≅ (toProjTri.{u_obj, u_hom} T).rotate := by
      refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (shift1ToProjIso.{u_obj, u_hom} T.obj₁) ?_ ?_ ?_
      · exact ProjΛ.hom_ext fun _ => rfl
      · exact ProjΛ.hom_ext fun _ => rfl
      · exact ProjΛ.hom_ext fun x => Twist.ext rfl
    constructor
    · intro h
      exact isDistinguishedε_of_iso _ ((isDistinguishedε_rotate_iff _).mp h) _ hIso
    · intro h
      exact (isDistinguishedε_rotate_iff _).mpr (isDistinguishedε_of_iso _ h _ hIso.symm)
  complete_distinguished_triangle_morphism T1 T2 h1 h2 a b hab := by
    obtain ⟨c, hc1, hc2⟩ := isDistinguishedε_complete (toProjTri.{u_obj, u_hom} T1) (toProjTri.{u_obj, u_hom} T2) h1 h2
      a.down b.down (congrArg ULift.down hab)
    refine ⟨ULift.up c, congrArg ULift.up hc1, congrArg ULift.up ?_⟩
    apply ProjΛ.hom_ext; intro x
    exact congrArg Twist.val (LinearMap.congr_fun hc2 x)

/-- If `ULiftProj.{u_obj}` satisfies TR4 (`IsTriangulated`), then so does `ProjΛ`! -/
lemma isTriangulated_ProjΛ_of_ULift
    [hU : @IsTriangulated ULiftProj.{u_obj} instCategory.{u_obj, u_hom} _ _ instHasShift.{u_obj, u_hom} _
      instPretriangulatedULift.{u_obj, u_hom}] : IsTriangulated ProjΛ := by
  refine ⟨?_⟩
  intro X1 X2 X3 Z12 Z23 Z13 u12 u23 u13 comm v12 w12 h12 v23 w23 h23 v13 w13 h13
  let liftO : ProjΛ → ULiftProj.{u_obj} := fun P => ⟨SmallProj.ofProj P⟩
  let isoO : ∀ P : ProjΛ, (liftO P).down.toProj ≅ P := fun P => SmallProj.isoProj P
  have hih : ∀ (P : ProjΛ) (x : P.carrier), ProjΛ.toLin (isoO P).hom (ProjΛ.toLin (isoO P).inv x) = x :=
    fun P x => LinearMap.congr_fun (isoO P).inv_hom_id x
  have hhi : ∀ (P : ProjΛ) (x : (liftO P).down.toProj.carrier),
      ProjΛ.toLin (isoO P).inv (ProjΛ.toLin (isoO P).hom x) = x :=
    fun P x => LinearMap.congr_fun (isoO P).hom_inv_id x
  let liftM : ∀ {P Q : ProjΛ}, (P ⟶ Q) →
      (@Quiver.Hom ULiftProj.{u_obj} instCategory.{u_obj, u_hom}.toQuiver (liftO P) (liftO Q)) := fun f =>
    ULift.up (CategoryStruct.comp (CategoryStruct.comp (isoO _).hom f) (isoO _).inv)
  let liftW : ∀ {Z X : ProjΛ}, (Z ⟶ X⟦(1 : ℤ)⟧) →
      (@Quiver.Hom ULiftProj.{u_obj} instCategory.{u_obj, u_hom}.toQuiver (liftO Z)
        ((@shiftFunctor ULiftProj.{u_obj} ℤ instCategory.{u_obj, u_hom} _ instHasShift.{u_obj, u_hom} 1).obj (liftO X))) := fun w =>
    ULift.up (CategoryStruct.comp (CategoryStruct.comp (CategoryStruct.comp (isoO _).hom w)
      ((isoO _).inv⟦(1 : ℤ)⟧')) (shift1ToProjIso.{u_obj, u_hom} (liftO _)).inv)
  have hlift_tri : ∀ {X Y Z : ProjΛ} {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ X⟦(1 : ℤ)⟧},
      Triangle.mk f g h ∈ distTriang ProjΛ →
      IsDistinguishedε (toProjTri.{u_obj, u_hom} (Triangle.mk (liftM f) (liftM g) (liftW h))) := by
    intro X Y Z f g h hT
    refine isDistinguishedε_of_iso (Triangle.mk f g h) hT _
      (Triangle.isoMk _ _ (isoO X) (isoO Y) (isoO Z) ?_ ?_ ?_)
    · apply ProjΛ.hom_ext; intro x; exact hih Y _
    · apply ProjΛ.hom_ext; intro y; exact hih Z _
    · apply ProjΛ.hom_ext; intro z; apply Twist.ext; exact hih X _
  have hcomm' : CategoryStruct.comp (liftM u12) (liftM u23) = liftM u13 := by
    apply congrArg ULift.up; apply ProjΛ.hom_ext; intro x
    change ProjΛ.toLin (isoO X3).inv (ProjΛ.toLin u23 (ProjΛ.toLin (isoO X2).hom
      (ProjΛ.toLin (isoO X2).inv (ProjΛ.toLin u12 (ProjΛ.toLin (isoO X1).hom x))))) =
      ProjΛ.toLin (isoO X3).inv (ProjΛ.toLin u13 (ProjΛ.toLin (isoO X1).hom x))
    rw [hih X2, ← comm]; rfl
  obtain ⟨H⟩ := hU.octahedron_axiom hcomm' (hlift_tri h12) (hlift_tri h23) (hlift_tri h13)
  let m1 : Z12 ⟶ Z13 := CategoryStruct.comp (CategoryStruct.comp (isoO Z12).inv H.m₁.down) (isoO Z13).hom
  let m3 : Z13 ⟶ Z23 := CategoryStruct.comp (CategoryStruct.comp (isoO Z13).inv H.m₃.down) (isoO Z23).hom
  refine ⟨⟨m1, m3, ?_, ?_, ?_, ?_, ?_⟩⟩
  · apply ProjΛ.hom_ext; intro x
    have hc := LinearMap.congr_fun (congrArg ULift.down H.comm₁) (ProjΛ.toLin (isoO X2).inv x)
    have h1 : ProjΛ.toLin (isoO Z13).hom (ProjΛ.toLin H.m₁.down (ProjΛ.toLin (isoO Z12).inv
        (ProjΛ.toLin v12 (ProjΛ.toLin (isoO X2).hom (ProjΛ.toLin (isoO X2).inv x))))) =
        ProjΛ.toLin (isoO Z13).hom (ProjΛ.toLin (isoO Z13).inv (ProjΛ.toLin v13 (ProjΛ.toLin (isoO X3).hom
          (ProjΛ.toLin (isoO X3).inv (ProjΛ.toLin u23 (ProjΛ.toLin (isoO X2).hom (ProjΛ.toLin (isoO X2).inv x))))))) :=
      congrArg (ProjΛ.toLin (isoO Z13).hom) hc
    rw [hih X2, hih X3, hih Z13] at h1
    exact h1
  · apply ProjΛ.hom_ext; intro z; apply Twist.ext
    have hc := LinearMap.congr_fun (congrArg ULift.down H.comm₂) (ProjΛ.toLin (isoO Z12).inv z)
    have h1 : ProjΛ.toLin (isoO X1).hom (ProjΛ.toLin (isoO X1).inv
        (ProjΛ.toLin w13 (ProjΛ.toLin (isoO Z13).hom (ProjΛ.toLin H.m₁.down (ProjΛ.toLin (isoO Z12).inv z)))).val) =
        ProjΛ.toLin (isoO X1).hom (ProjΛ.toLin (isoO X1).inv
          (ProjΛ.toLin w12 (ProjΛ.toLin (isoO Z12).hom (ProjΛ.toLin (isoO Z12).inv z))).val) :=
      congrArg (ProjΛ.toLin (isoO X1).hom) hc
    rw [hih Z12, hih X1, hih X1] at h1
    exact h1
  · apply ProjΛ.hom_ext; intro x
    have hc := LinearMap.congr_fun (congrArg ULift.down H.comm₃) (ProjΛ.toLin (isoO X3).inv x)
    have h1 : ProjΛ.toLin (isoO Z23).hom (ProjΛ.toLin H.m₃.down (ProjΛ.toLin (isoO Z13).inv
        (ProjΛ.toLin v13 (ProjΛ.toLin (isoO X3).hom (ProjΛ.toLin (isoO X3).inv x))))) =
        ProjΛ.toLin (isoO Z23).hom (ProjΛ.toLin (isoO Z23).inv (ProjΛ.toLin v23
          (ProjΛ.toLin (isoO X3).hom (ProjΛ.toLin (isoO X3).inv x)))) :=
      congrArg (ProjΛ.toLin (isoO Z23).hom) hc
    rw [hih X3, hih Z23] at h1
    exact h1
  · apply ProjΛ.hom_ext; intro z; apply Twist.ext
    have hc := LinearMap.congr_fun (congrArg ULift.down H.comm₄) (ProjΛ.toLin (isoO Z13).inv z)
    have h1 : ProjΛ.toLin (isoO X2).hom (ProjΛ.toLin (isoO X2).inv (ProjΛ.toLin u12 (ProjΛ.toLin (isoO X1).hom
        (ProjΛ.toLin (isoO X1).inv (ProjΛ.toLin w13 (ProjΛ.toLin (isoO Z13).hom (ProjΛ.toLin (isoO Z13).inv z))).val)))) =
        ProjΛ.toLin (isoO X2).hom (ProjΛ.toLin (isoO X2).inv
          (ProjΛ.toLin w23 (ProjΛ.toLin (isoO Z23).hom (ProjΛ.toLin H.m₃.down (ProjΛ.toLin (isoO Z13).inv z)))).val) :=
      congrArg (ProjΛ.toLin (isoO X2).hom) hc
    rw [hih Z13, hih X1, hih X2, hih X2] at h1
    exact h1
  · refine isDistinguishedε_of_iso _ H.mem _ (Triangle.isoMk _ _ (isoO Z12).symm (isoO Z13).symm (isoO Z23).symm ?_ ?_ ?_)
    · apply ProjΛ.hom_ext; intro z; exact hhi Z13 _
    · apply ProjΛ.hom_ext; intro z; exact hhi Z23 _
    · apply ProjΛ.hom_ext; intro z; apply Twist.ext
      have hz1 : ProjΛ.toLin (isoO Z23).hom (ProjΛ.toLin (isoO Z23).inv z) = z := hih Z23 z
      have hx2 : ProjΛ.toLin (isoO X2).hom (ProjΛ.toLin (isoO X2).inv (ProjΛ.toLin w23 z).val) =
          (ProjΛ.toLin w23 z).val := hih X2 _
      change ProjΛ.toLin (isoO Z12).inv (ProjΛ.toLin v12 (ProjΛ.toLin w23 z).val) =
        ProjΛ.toLin (isoO Z12).inv (ProjΛ.toLin v12 (ProjΛ.toLin (isoO X2).hom
          (ProjΛ.toLin (isoO X2).inv (ProjΛ.toLin w23 (ProjΛ.toLin (isoO Z23).hom (ProjΛ.toLin (isoO Z23).inv z))).val)))
      rw [hz1, hx2]

end ULiftProj

end OctahedralFailure

end OMA.MO31809

theorem OMA.solution : type_of% @Mathoverflow31809.mathoverflow_31809 := by
  intro h
  haveI : CategoryTheory.IsTriangulated OMA.MO31809.ULiftProj := h OMA.MO31809.ULiftProj
  exact OMA.MO31809.not_isTriangulated_ProjΛ OMA.MO31809.ULiftProj.isTriangulated_ProjΛ_of_ULift
